//! Backward liveness of slots (A:1231-1240; M3 plan d.6; owner 2E): a loan is
//! live where a slot holding it is used later. A use is a local as an operand or as
//! the base of a place; a definition a whole-local assignment. `StorageDead` is
//! never a use; a `Drop` of a slot is one only when a destructor runs on it or on a
//! borrowing value inside it, and some part of it may hold a value there. `Hold(l)` is defined at the end of l's pre-header and
//! used at its head; `Caller(m)` and `_0` (choice: the return reads it, so a loan it
//! holds is live at every `StorageDead` before the `Return`) are used at `Return`.

use std::collections::{BTreeMap, BTreeSet};

use enrang_hir::{Tcx, Ty, TyKind};
use enrang_mir::{
    Body, Callee, DataflowAnalysis, Local, Place, Point, Statement, StatementKind, Terminator,
    TerminatorKind, solve, statement_places, terminator_places,
};

use crate::access::moved_drops;
use crate::cx::BodyCx;
use crate::slots::SlotId;

/// The slots live before and after each point.
#[derive(Clone, Debug, Default)]
pub struct LiveSlots {
    pub before: BTreeMap<Point, BTreeSet<SlotId>>,
    pub after: BTreeMap<Point, BTreeSet<SlotId>>,
}

impl LiveSlots {
    pub fn compute(cx: &BodyCx) -> LiveSlots {
        let res = solve(cx.body, Live(cx, moved_drops(cx)));
        let mut out = LiveSlots::default();
        res.visit(cx.body, |p, before, after| {
            out.before.insert(p, before.clone());
            out.after.insert(p, after.clone());
        });
        out
    }

    pub fn live_before(&self, p: Point) -> &BTreeSet<SlotId> {
        self.before.get(&p).unwrap_or(&EMPTY)
    }

    pub fn live_after(&self, p: Point) -> &BTreeSet<SlotId> {
        self.after.get(&p).unwrap_or(&EMPTY)
    }
}

static EMPTY: BTreeSet<SlotId> = BTreeSet::new();

/// Whether a destructor runs on a value of type `ty` or on a borrowing value inside
/// it (O10, I5), a nullable field's included: `private g: Guard | null` is a
/// reference field as `private g: Guard` is (S:848).
pub(crate) fn drop_runs(tcx: &Tcx, ty: Ty) -> bool {
    match tcx.kind(ty) {
        TyKind::Adt(adt, args) => {
            tcx.adt(adt).is_class()
                && (tcx.class_dtor(adt, args).is_some()
                    || tcx
                        .adt_field_tys(adt, args)
                        .into_iter()
                        .any(|f| crate::slots::bvalue(tcx, f) && drop_runs(tcx, f)))
        }
        TyKind::Tuple(parts) => tcx.list(parts).iter().any(|&p| drop_runs(tcx, p)),
        TyKind::Nullable(t) => drop_runs(tcx, t),
        _ => false,
    }
}

/// The body, and the scope drops that use nothing ([`moved_drops`]).
struct Live<'a, 'b>(&'a BodyCx<'b>, BTreeSet<Point>);

impl Live<'_, '_> {
    fn slot(&self, l: Local) -> Option<SlotId> {
        let s = SlotId::Local(l);
        self.0.slots.has(s).then_some(s)
    }

    fn uses(&self, set: &mut BTreeSet<SlotId>, places: impl IntoIterator<Item = Place>) {
        set.extend(places.into_iter().filter_map(|p| self.slot(p.local)));
    }

    /// A destination: a whole local is defined, a projection uses its base.
    fn dest(&self, set: &mut BTreeSet<SlotId>, p: Place) {
        if let Some(s) = self.slot(p.local) {
            match p.is_local() {
                true => set.remove(&s),
                false => set.insert(s),
            };
        }
    }

    fn block_start(&self, set: &mut BTreeSet<SlotId>, at: Point) {
        if at.index == 0 {
            for lp in self.0.body.meta.loops.iter().filter(|l| l.head == at.block) {
                if self.0.slots.has(SlotId::Hold(lp.id)) {
                    set.insert(SlotId::Hold(lp.id));
                }
            }
        }
    }
}

impl DataflowAnalysis for Live<'_, '_> {
    type Domain = BTreeSet<SlotId>;
    const FORWARD: bool = false;

    fn bottom(&self, _b: &Body) -> Self::Domain {
        BTreeSet::new()
    }

    fn entry(&self, _b: &Body) -> Self::Domain {
        BTreeSet::new()
    }

    fn join(&self, into: &mut Self::Domain, from: &Self::Domain) -> bool {
        let n = into.len();
        into.extend(from.iter().copied());
        into.len() != n
    }

    fn statement(&self, set: &mut Self::Domain, st: &Statement, at: Point) {
        let tcx = self.0.tcx;
        match &st.kind {
            StatementKind::Assign { dest, .. }
            | StatementKind::Intrinsic {
                dest: Some(dest), ..
            }
            | StatementKind::HostCall {
                dest: Some(dest), ..
            } => {
                self.dest(set, *dest);
                let rest = statement_places(&st.kind).into_iter().skip(1);
                let rest: Vec<Place> = match &st.kind {
                    StatementKind::Assign { .. } => rest.collect(),
                    _ => statement_places(&st.kind)
                        .into_iter()
                        .take_while(|p| p != dest)
                        .collect(),
                };
                self.uses(set, rest);
            }
            StatementKind::Drop(p, _) => {
                let ty = self.0.body.locals[p.local].ty;
                if p.is_local() && drop_runs(tcx, ty) && !self.1.contains(&at) {
                    self.uses(set, [*p]);
                }
            }
            StatementKind::StorageDead(_) | StatementKind::StorageLive(_) => {}
            // Building a local in place starts a new value (A:939): the old one,
            // a loan its fields took in the previous turn included, is dead here.
            StatementKind::SetTable { place, .. } if place.is_local() => self.dest(set, *place),
            k => self.uses(set, statement_places(k)),
        }
        self.block_start(set, at);
    }

    fn terminator(&self, set: &mut Self::Domain, t: &Terminator, at: Point) {
        let b = self.0.body;
        for lp in b.meta.loops.iter().filter(|l| l.preheader == at.block) {
            set.remove(&SlotId::Hold(lp.id));
        }
        match &t.kind {
            TerminatorKind::Call { callee, dest, .. } => {
                self.dest(set, *dest);
                let places = terminator_places(&t.kind);
                self.uses(set, places[..places.len() - 1].iter().copied());
                if let Callee::ClosureLocal(l) = callee {
                    self.uses(set, [Place::local(*l)]);
                }
            }
            TerminatorKind::Return => {
                self.uses(set, [Place::local(Local::RETURN)]);
                set.extend(
                    self.0
                        .slots
                        .list
                        .iter()
                        .filter(|(s, _)| matches!(s, SlotId::Caller(_)))
                        .map(|(s, _)| *s),
                );
            }
            k => self.uses(set, terminator_places(k)),
        }
        self.block_start(set, at);
    }
}
