//! Write-liveness N3 and loan modes (A:1026, A:1350-1352; M3 plan d.7; owner 2F):
//! a loan is exclusive when a write through a slot holding it may follow.
//!
//! A wslot is a ref-carrying local's reference part: the local itself for a
//! reference (a nullable one, a closure, an environment), each reference part of
//! a borrowing tuple held directly (its payload looked through when nullable); a
//! borrowing class value has none, since it is never write-live itself. The
//! backward analysis gens rules (a)-(e) of N3 and kills a wslot where it is
//! reassigned. Creating a closure is a write of each capture the arrow writes
//! through, or each hidden argument a local function writes through, so those
//! captures are exclusive and the ones it only reads stay shared (S 5.5: captures
//! are inferred per variable).

use std::collections::{BTreeMap, BTreeSet};

use enrang_base::{BitSet, Idx};
use enrang_hir::{self as hir, AdtId, Perm, RetSources, Tcx, TyKind};
use enrang_mir::{
    AggregateKind, Bodies, Body, BodyOwner, ClosureFn, DataflowAnalysis, ForOfLoop, Local, Operand,
    Place, PlaceTy, Point, Proj, Results, Rvalue, Statement, StatementKind, Terminator,
    TerminatorKind, solve,
};

use crate::cx::{BodyCx, SccState};
use crate::declared::{call_info, operand_ty, perm_slots, ref_parts};
use crate::held::HeldResults;
use crate::loans::{LoanId, LoanKind};

/// Each loan's mode.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Modes {
    exclusive: BitSet<LoanId>,
}

impl Modes {
    pub fn exclusive(&self, l: LoanId) -> bool {
        l.0 < self.exclusive.domain_size() as u32 && self.exclusive.contains(l)
    }
}

/// The modes of `cx.body`'s loans, fixed before the access checks (plan d.7).
pub fn compute_modes(cx: &BodyCx, _held: &HeldResults) -> Modes {
    let w = WLive::compute(cx.tcx, cx.body, cx.bodies, cx.scc, None);
    let b = cx.body;
    let mut exclusive = BitSet::new(cx.loans.table.len());
    for (id, loan) in cx.loans.table.iter_enumerated() {
        let on = match &loan.kind {
            LoanKind::Hold(l) => b.meta.loops.iter().any(|x| x.id == *l && w.binding_live(x)),
            LoanKind::HoldCrossing(_) | LoanKind::Closure => false,
            kind => match b.stmt_at(loan.site).map(|s| &s.kind) {
                Some(StatementKind::Assign { dest, value }) => {
                    // A part loan's part, as the destination holds it.
                    let part = match kind {
                        LoanKind::Part(k) => crate::loans::dest_part(b, loan, k),
                        _ => &[],
                    };
                    let closure_param = matches!(value, Rvalue::Ref { place, .. }
                        if b.place_ty(cx.tcx, *place)
                            .is_some_and(|t| matches!(cx.tcx.kind(t.ty), TyKind::Closure(_))));
                    closure_param || w.dest_live(loan.site, *dest, part)
                }
                _ => false,
            },
        };
        if on {
            exclusive.insert(id);
        }
    }
    Modes { exclusive }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct WSlot(pub u32);

impl Idx for WSlot {
    fn new(i: usize) -> Self {
        WSlot(u32::try_from(i).expect("WSlot exceeds u32"))
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

/// The wslots of one body, by local and part path.
#[derive(Clone, Debug, Default)]
pub struct WSlots {
    index: BTreeMap<(Local, Vec<u32>), WSlot>,
}

impl WSlots {
    fn collect(tcx: &Tcx, b: &Body) -> WSlots {
        let mut index = BTreeMap::new();
        for (l, d) in b.locals.iter_enumerated() {
            let paths = match tcx.kind(d.ty) {
                TyKind::Closure(_) => vec![Vec::new()],
                _ => ref_parts(tcx, d.ty),
            };
            for p in paths {
                let n = index.len();
                index.insert((l, p), WSlot::new(n));
            }
        }
        WSlots { index }
    }

    pub fn get(&self, l: Local, path: &[u32]) -> Option<WSlot> {
        self.index.get(&(l, path.to_vec())).copied()
    }

    /// The wslots of `l` at or below `path`.
    pub fn under(&self, l: Local, path: &[u32]) -> Vec<WSlot> {
        self.index
            .range((l, path.to_vec())..)
            .take_while(|((x, p), _)| *x == l && p.starts_with(path))
            .map(|(_, w)| *w)
            .collect()
    }
}

/// Where a place sits: in a wslot's local at a part path, or behind the
/// reference that wslot holds.
enum At {
    Slot(Local, Vec<u32>),
    Through(Local, Vec<u32>),
}

/// A witness's seed: one point, and at a call one argument (`usize::MAX`: the
/// destination's write-through), or all of the point's direct writes.
pub type Seed = (Point, Option<usize>);

/// The analysis; `seed`, when set, keeps only the direct writes (rules (a), (b),
/// (e) and a writing closure) it names, for witnesses.
pub struct Wl<'a> {
    tcx: &'a Tcx,
    body: &'a Body,
    bodies: &'a Bodies,
    scc: Option<&'a SccState>,
    pub slots: WSlots,
    seed: Option<Seed>,
}

/// Solved write-liveness of one body.
pub struct WLive<'a> {
    pub res: Results<Wl<'a>>,
}

impl<'a> WLive<'a> {
    pub fn compute(
        tcx: &'a Tcx,
        body: &'a Body,
        bodies: &'a Bodies,
        scc: Option<&'a SccState>,
        seed: Option<Seed>,
    ) -> WLive<'a> {
        let slots = WSlots::collect(tcx, body);
        let wl = Wl {
            tcx,
            body,
            bodies,
            scc,
            slots,
            seed,
        };
        WLive {
            res: solve(body, wl),
        }
    }

    pub fn slots(&self) -> &WSlots {
        &self.res.analysis.slots
    }

    pub fn after(&self, p: Point) -> BitSet<WSlot> {
        self.res.after(self.res.analysis.body, p)
    }

    /// The wslots write-live at the body's entry.
    pub fn entry(&self) -> BitSet<WSlot> {
        let b = self.res.analysis.body;
        match b.blocks.is_empty() {
            true => self.res.analysis.bottom(b),
            false => self
                .res
                .before(b, Point::new(enrang_mir::BlockId::ENTRY, 0)),
        }
    }

    /// Whether `l` at `path` (any part below it) is write-live at entry.
    pub fn live_at_entry(&self, l: Local, path: &[u32]) -> bool {
        let e = self.entry();
        self.slots().under(l, path).iter().any(|w| e.contains(*w))
    }

    /// Whether a part of `dest` (below `part`) is write-live just after `p`.
    pub fn dest_live(&self, p: Point, dest: Place, part: &[u32]) -> bool {
        let Some(At::Slot(l, mut path)) = self.res.analysis.resolve(dest) else {
            return false;
        };
        path.extend_from_slice(part);
        let after = self.after(p);
        self.slots()
            .under(l, &path)
            .iter()
            .any(|w| after.contains(*w))
    }

    /// Whether loop `lp`'s binding is write-live anywhere in its body (plan d.7).
    pub fn binding_live(&self, lp: &ForOfLoop) -> bool {
        let b = self.res.analysis.body;
        let Some(w) = self.slots().get(lp.binding, &[]) else {
            return false;
        };
        let mut seen = BTreeSet::new();
        let mut stack = vec![lp.bind.block];
        while let Some(bb) = stack.pop() {
            if (bb == lp.head && bb != lp.bind.block) || !seen.insert(bb) {
                continue;
            }
            let from = if bb == lp.bind.block {
                lp.bind.index
            } else {
                0
            };
            for i in from..=b.blocks[bb].stmts.len() as u32 {
                if self.after(Point::new(bb, i as usize)).contains(w) {
                    return true;
                }
            }
            stack.extend(b.blocks[bb].term.kind.successors());
        }
        false
    }
}

impl Wl<'_> {
    fn event(&self, at: Point) -> bool {
        self.seed.is_none_or(|(p, _)| p == at)
    }

    fn event_arg(&self, at: Point, i: usize) -> bool {
        self.seed
            .is_none_or(|(p, q)| p == at && q.is_none_or(|q| q == i))
    }

    fn flag(&self, adt: AdtId) -> bool {
        match self.scc.and_then(|s| s.flags.get(&adt)) {
            Some(&f) => f,
            None => crate::class_contract(self.tcx, adt).writes_through_fields,
        }
    }

    fn resolve(&self, p: Place) -> Option<At> {
        let tcx = self.tcx;
        let mut pt = PlaceTy::of(self.body.locals[p.local].ty);
        let mut path = Vec::new();
        for &proj in self.body.projs(p) {
            let payload = matches!(tcx.kind(pt.ty), TyKind::Nullable(_));
            match proj {
                Proj::Deref => return Some(At::Through(p.local, path)),
                Proj::Variant(_) if payload => {}
                Proj::Field(_) if payload && pt.variant.is_some() => {}
                Proj::Field(k) if matches!(tcx.kind(pt.ty), TyKind::Tuple(_)) => path.push(k.0),
                _ => return None,
            }
            pt = pt.project(tcx, proj)?;
        }
        Some(At::Slot(p.local, path))
    }

    fn place_at(&self, p: Place, rel: &[u32]) -> Vec<WSlot> {
        match self.resolve(p) {
            Some(At::Slot(l, mut path)) => {
                path.extend_from_slice(rel);
                self.slots.under(l, &path)
            }
            Some(At::Through(l, path)) => self.slots.get(l, &path).into_iter().collect(),
            None => Vec::new(),
        }
    }

    fn operand_at(&self, op: &Operand, rel: &[u32]) -> Vec<WSlot> {
        op.place().map_or_else(Vec::new, |p| self.place_at(p, rel))
    }

    /// What a value takes references from at `rel` below it (rule (c)); `None`
    /// for `rel` takes everything.
    fn value_at(&self, rv: &Rvalue, rel: Option<&[u32]>) -> Vec<WSlot> {
        let all = rel.unwrap_or(&[]);
        match rv {
            Rvalue::Use(op) | Rvalue::Convert(_, op) => self.operand_at(op, all),
            Rvalue::Ref { place, .. } | Rvalue::ClosureReborrow(place) => {
                self.place_at(*place, &[])
            }
            Rvalue::ClosureValue { env, .. } => self.place_at(*env, &[]),
            Rvalue::Aggregate(AggregateKind::Present, ops) => {
                ops.iter().flat_map(|o| self.operand_at(o, all)).collect()
            }
            // An environment's captures are its parts, each write-live alone.
            Rvalue::Aggregate(AggregateKind::Tuple | AggregateKind::ClosureEnv, ops) => match rel {
                Some([k, rest @ ..]) => ops
                    .get(*k as usize)
                    .map_or_else(Vec::new, |o| self.operand_at(o, rest)),
                _ => ops.iter().flat_map(|o| self.operand_at(o, &[])).collect(),
            },
            _ => Vec::new(),
        }
    }

    /// Rule (e): a store into `dest` lands in a borrowing value whose class writes
    /// through its fields (not into a `readonly &` field itself), or in a
    /// borrowing tuple behind a reference.
    pub(crate) fn writes_through(&self, dest: Place) -> bool {
        let tcx = self.tcx;
        let projs = self.body.projs(dest);
        let mut pt = PlaceTy::of(self.body.locals[dest.local].ty);
        // The container: Some(Some(class, into a `readonly &` field)) or Some(None)
        // for a tuple behind a reference.
        let mut owner: Option<Option<(AdtId, bool)>> = None;
        let mut through = false;
        for (i, &proj) in projs.iter().enumerate() {
            match (proj, tcx.kind(pt.ty)) {
                (Proj::Deref, _) => {
                    through = true;
                    owner = None;
                }
                (Proj::Field(f), TyKind::Adt(adt, _))
                    if pt.variant.is_none() && tcx.adt(adt).is_class() =>
                {
                    let ro = tcx
                        .field_def(adt, None, f)
                        .readonly_refs
                        .iter()
                        .any(Vec::is_empty);
                    owner = Some(Some((adt, ro && i + 1 == projs.len())));
                }
                (Proj::Field(_), TyKind::Tuple(_)) if owner.is_none() && through => {
                    owner = Some(None);
                }
                _ => {}
            }
            let Some(next) = pt.project(tcx, proj) else {
                return false;
            };
            pt = next;
        }
        match owner {
            Some(Some((adt, ro))) => !ro && self.flag(adt),
            Some(None) => true,
            None if through && projs.last() == Some(&Proj::Deref) => match tcx.kind(pt.ty) {
                TyKind::Adt(adt, _) => tcx.is_borrowing(pt.ty) && self.flag(adt),
                _ => tcx.is_borrowing(pt.ty),
            },
            None => false,
        }
    }

    /// Whether `arrow` of this body's HIR owner writes through its environment.
    /// The captures, by environment field, that arrow `arrow` writes through:
    /// none when its environment is not write-live at its entry, else each field
    /// written through, or read into a slot that is write-live or stores it; every
    /// field when the environment itself is used so.
    fn arrow_writes(&self, arrow: hir::ArrowId) -> Vec<u32> {
        let parent = match self.body.owner {
            BodyOwner::Fn(d) => hir::BodyOwner::Fn(d),
            BodyOwner::Test(d) => hir::BodyOwner::Test(d),
            BodyOwner::Statements(m) => hir::BodyOwner::Statements(m),
            BodyOwner::Arrow(p, _) => p,
            BodyOwner::Shim(_) => return Vec::new(),
        };
        let Some(ab) = self.bodies.get(&BodyOwner::Arrow(parent, arrow)) else {
            return Vec::new();
        };
        let w = WLive::compute(self.tcx, ab, self.bodies, self.scc, None);
        if !w.live_at_entry(Local(1), &[]) {
            return Vec::new();
        }
        let count = PlaceTy::of(ab.locals[Local(1)].ty)
            .project(self.tcx, Proj::Deref)
            .map_or(0, |env| match self.tcx.kind(env.ty) {
                TyKind::Tuple(parts) => self.tcx.list(parts).len(),
                _ => 0,
            });
        let all = || (0..count as u32).collect::<Vec<u32>>();
        // The environment field a place reaches through `_1`: `Some(Some(k))` for
        // `(*_1).k...`, `Some(None)` for the environment as a whole.
        let field = |p: Place| -> Option<Option<u32>> {
            (p.local == Local(1)).then(|| match ab.projs(p) {
                [Proj::Deref, Proj::Field(k), ..] => Some(k.0),
                _ => None,
            })
        };
        let mut out = BTreeSet::new();
        let mut take = |f: Option<u32>| -> bool {
            match f {
                Some(k) => {
                    out.insert(k);
                    true
                }
                None => false,
            }
        };
        let kept = |p: Point, dest: Place| match w.res.analysis.resolve(dest) {
            Some(At::Slot(..)) => w.dest_live(p, dest, &[]),
            _ => true,
        };
        for (bb, block) in ab.blocks.iter_enumerated() {
            for i in 0..=block.stmts.len() {
                let p = Point::new(bb, i);
                // (a) a write through a capture.
                for dest in crate::init::point_dests(ab, p) {
                    let through = ab.projs(dest).iter().skip(2).any(|q| *q == Proj::Deref);
                    match field(dest) {
                        Some(f) if through && !take(f) => return all(),
                        _ => {}
                    }
                }
                // (b), (c), (e) a capture, or what it points at, read into a slot
                // that is write-live or stores it, or passed to a call.
                let read: Vec<(Place, Option<Place>)> = match ab.stmt_at(p).map(|s| &s.kind) {
                    Some(StatementKind::Assign { dest, value }) => {
                        let mut ps: Vec<Place> = Vec::new();
                        match value {
                            Rvalue::Ref { place, .. } | Rvalue::ClosureReborrow(place) => {
                                ps.push(*place)
                            }
                            Rvalue::ClosureValue { env, .. } => ps.push(*env),
                            Rvalue::Use(op) | Rvalue::Convert(_, op) => ps.extend(op.place()),
                            Rvalue::Aggregate(_, ops) => {
                                ps.extend(ops.iter().filter_map(Operand::place))
                            }
                            _ => {}
                        }
                        ps.into_iter().map(|q| (q, Some(*dest))).collect()
                    }
                    Some(_) => Vec::new(),
                    None => match &block.term.kind {
                        TerminatorKind::Call { args, .. } => (args.iter())
                            .filter_map(Operand::place)
                            .filter(|q| {
                                (ab.place_ty(self.tcx, *q))
                                    .is_none_or(|t| !self.tcx.is_value_type(t.ty))
                            })
                            .map(|q| (q, None))
                            .collect(),
                        _ => Vec::new(),
                    },
                };
                for (q, dest) in read {
                    let Some(f) = field(q) else {
                        continue;
                    };
                    if dest.is_none_or(|d| kept(p, d)) && !take(f) {
                        return all();
                    }
                }
            }
        }
        // The environment is write-live at entry, so the arrow writes through
        // some capture: one the scan cannot name makes every capture written.
        match out.is_empty() {
            true => all(),
            false => out.into_iter().collect(),
        }
    }

    /// The hidden arguments, by environment field, that local function `f`
    /// writes through, by its current contract (A:1360).
    fn named_writes(&self, f: hir::DefId) -> Vec<u32> {
        let Some(fb) = self.bodies.get(&BodyOwner::Fn(f)) else {
            return Vec::new();
        };
        let c = match self.scc.and_then(|s| s.current.get(&f)) {
            Some(c) => c.clone(),
            None => (*crate::contract(self.tcx, f)).clone(),
        };
        let slots = perm_slots(self.tcx, &crate::r3::arg_tys(fb));
        (crate::r3::hidden(self.tcx, f, fb).into_iter().enumerate())
            .filter(|&(_, i)| {
                crate::declared::perm_of(&slots, &c.perms, i as usize) == Some(Perm::Write)
            })
            .map(|(k, _)| k as u32)
            .collect()
    }

    /// The gens of a write of `rv` into `dest` at `at`, against the state after.
    fn write(
        &self,
        after: &BitSet<WSlot>,
        dest: Place,
        rv: Option<&Rvalue>,
        at: Point,
        gens: &mut Vec<WSlot>,
    ) {
        // An arrow's rebinding of a captured reference, `r = x`, is EN0616 alone
        // (A:1270): no write through the environment, so `f(&a)` of such an arrow
        // borrows nothing for writing.
        if crate::rebind::repoints_capture(self.body, dest) {
            return;
        }
        let direct = self.event(at);
        match self.resolve(dest) {
            // (a) a write through the reference `dest` dereferences.
            Some(At::Through(l, path)) if direct => gens.extend(self.slots.get(l, &path)),
            // (c) a flow into a slot write-live just after.
            Some(At::Slot(l, path)) if rv.is_some() => {
                for (k, w) in self.slots.index.range((l, path.clone())..) {
                    if k.0 != l || !k.1.starts_with(&path) {
                        break;
                    }
                    if after.contains(*w) {
                        let rel = &k.1[path.len()..];
                        let rv = rv.expect("a value");
                        let part = match rv {
                            Rvalue::Ref { .. } => None,
                            _ => Some(rel),
                        };
                        gens.extend(self.value_at(rv, part));
                    }
                }
            }
            _ => {}
        }
        let Some(rv) = rv.filter(|_| direct) else {
            return;
        };
        // (e) a store into a value that writes through its fields.
        if self.writes_through(dest) {
            gens.extend(self.value_at(rv, None));
        }
        match rv {
            Rvalue::Aggregate(
                AggregateKind::Adt {
                    adt, variant: None, ..
                },
                ops,
            ) if self.flag(*adt) => {
                for (f, op) in ops.iter().enumerate() {
                    let fd = self.tcx.field_def(*adt, None, hir::FieldIdx(f as u32));
                    if !fd.readonly_refs.iter().any(Vec::is_empty) {
                        gens.extend(self.operand_at(op, &[]));
                    }
                }
            }
            Rvalue::ClosureValue {
                func: ClosureFn::Arrow(a),
                env,
            } => {
                for k in self.arrow_writes(*a) {
                    gens.extend(self.place_at(*env, &[k]));
                }
            }
            // A local function as a closure (C12, c.16): its env's captures are
            // its hidden arguments, each written when it writes through it.
            Rvalue::ClosureValue {
                func: ClosureFn::Named(f),
                env,
            } => {
                for k in self.named_writes(f.def) {
                    gens.extend(self.place_at(*env, &[k]));
                }
            }
            _ => {}
        }
    }

    fn kill(&self, s: &mut BitSet<WSlot>, dest: Place) {
        if let Some(At::Slot(l, path)) = self.resolve(dest) {
            for w in self.slots.under(l, &path) {
                s.remove(w);
            }
        }
    }
}

impl DataflowAnalysis for Wl<'_> {
    type Domain = BitSet<WSlot>;
    const FORWARD: bool = false;

    fn bottom(&self, _b: &Body) -> BitSet<WSlot> {
        BitSet::new(self.slots.index.len())
    }

    fn entry(&self, b: &Body) -> BitSet<WSlot> {
        self.bottom(b)
    }

    fn join(&self, into: &mut BitSet<WSlot>, from: &BitSet<WSlot>) -> bool {
        into.union(from)
    }

    fn statement(&self, s: &mut BitSet<WSlot>, st: &Statement, at: Point) {
        let mut gens = Vec::new();
        match &st.kind {
            StatementKind::Assign { dest, value } => {
                self.write(s, *dest, Some(value), at, &mut gens);
                self.kill(s, *dest);
            }
            StatementKind::FieldInit { field, value } => {
                self.write(s, *field, Some(&Rvalue::Use(value.clone())), at, &mut gens);
            }
            StatementKind::Intrinsic { dest: Some(d), .. }
            | StatementKind::HostCall { dest: Some(d), .. } => {
                self.write(s, *d, None, at, &mut gens);
                self.kill(s, *d);
            }
            _ => {}
        }
        for w in gens {
            s.insert(w);
        }
    }

    fn terminator(&self, s: &mut BitSet<WSlot>, t: &Terminator, at: Point) {
        let TerminatorKind::Call {
            callee, args, dest, ..
        } = &t.kind
        else {
            return;
        };
        let mut gens = Vec::new();
        if let Some(At::Through(l, p)) = self.resolve(*dest)
            && self.event_arg(at, usize::MAX)
        {
            gens.extend(self.slots.get(l, &p));
        }
        let ci = call_info(self.tcx, self.body, self.scc, callee, args);
        // (d) the result, a reference or a reference part of a tuple, write-live.
        let result_live = match self.resolve(*dest) {
            Some(At::Slot(l, p)) => self.slots.under(l, &p).iter().any(|w| s.contains(*w)),
            _ => false,
        };
        let sources = match &ci.sources {
            RetSources::Params(v) => v.as_slice(),
            RetSources::NoLoans => &[],
        };
        for &i in sources.iter().filter(|_| result_live) {
            gens.extend(
                args.get(i as usize)
                    .map_or_else(Vec::new, |a| self.operand_at(a, &[])),
            );
        }
        // (b) a Write `&` argument, or reference part of a by-value tuple.
        let tys: Vec<_> = args
            .iter()
            .map(|a| operand_ty(self.tcx, self.body, a).unwrap_or(self.tcx.common().void))
            .collect();
        for (k, (i, path)) in perm_slots(self.tcx, &tys).into_iter().enumerate() {
            if self.event_arg(at, k) && ci.perms.get(k) == Some(&Perm::Write) {
                gens.extend(self.operand_at(&args[i], &path));
            }
        }
        self.kill(s, *dest);
        for w in gens {
            s.insert(w);
        }
    }
}
