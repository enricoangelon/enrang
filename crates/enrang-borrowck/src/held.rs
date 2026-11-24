//! `held`, `fields`, `rfields`, `wfields`: the forward loan analysis (A:1038-1229;
//! M3 plan d.5; owner 2E), with `store()`, `kill()`, the turn-key renames at a
//! bind and a pre-header, bind marks and covered bits on keys.
//!
//! Every row reads the state before its statement (for a call, before the call,
//! every store included) and applies its unions after. A borrowing value's `fields`
//! is its `held`, never stored apart. The EN0616s of `store` and of a write's
//! read-set check are data (`HeldResults::store_errors`), since inference runs this
//! analysis again; `access::store_errors` applies the one-report rule (A:1265).

use std::cell::RefCell;
use std::collections::BTreeMap;

use enrang_base::Span;
use enrang_hir::{DefId, FieldIdx, LoopId, Perm, RetSources, Ty, TyKind, VariantIdx};
use enrang_mir::{
    AggregateKind, BlockId, Body, BodyOwner, BorrowOrigin, Callee, DataflowAnalysis, ForOfLoop,
    Local, LocalKind, LoopSource, Operand, Place, PlaceTy, Point, Proj, Rvalue, Statement,
    StatementKind, Terminator, TerminatorKind, solve,
};

use crate::cx::{BodyCx, CallInfo, call_info};
use crate::loans::{
    Cross, LoanId, LoanKey, LoanKind, Step, Turn, container, normalize, readonly_field, ref_parts,
    strip_null,
};
use crate::slots::{
    SlotId, SlotKind, Slots, bvalue, closure_ty, fixed_param, own_this, param_index, pointee,
    ref_carrying,
};
use crate::wlive::WLive;

/// What a key carries (plan d.5): the loop whose bind alone gave it, and whether a
/// parameter's key is bare (not covered).
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct KeyBits {
    pub mark: Option<LoopId>,
    pub bare: bool,
}

impl KeyBits {
    const BARE: KeyBits = KeyBits {
        mark: None,
        bare: true,
    };

    /// Two copies of one key meet: plain wins over a mark, two marks give plain,
    /// bare wins (A:1227-1229).
    fn merge(self, o: KeyBits) -> KeyBits {
        KeyBits {
            mark: if self.mark == o.mark { self.mark } else { None },
            bare: self.bare || o.bare,
        }
    }
}

/// A set of keys with their bits.
pub type Set = BTreeMap<LoanKey, KeyBits>;

static EMPTY: Set = BTreeMap::new();

/// `into ∪= from` by the merge rule; whether `into` changed.
fn union(into: &mut Set, from: &Set) -> bool {
    let mut changed = false;
    for (k, b) in from {
        let new = into.get(k).map_or(*b, |x| x.merge(*b));
        changed |= into.insert(*k, new) != Some(new);
    }
    changed
}

fn meets(a: &Set, b: &Set) -> bool {
    a.keys().any(|k| b.contains_key(k))
}

fn key(k: LoanKey) -> (LoanKey, KeyBits) {
    (k, KeyBits::default())
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Map {
    Held,
    Fields,
    RFields,
    WFields,
}

const MAPS: [Map; 4] = [Map::Held, Map::Fields, Map::RFields, Map::WFields];

/// The state at a point: per slot, the four maps.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct State {
    pub held: BTreeMap<SlotId, Set>,
    pub fields: BTreeMap<SlotId, Set>,
    pub rfields: BTreeMap<SlotId, Set>,
    pub wfields: BTreeMap<SlotId, Set>,
}

impl State {
    fn map_mut(&mut self, m: Map) -> &mut BTreeMap<SlotId, Set> {
        match m {
            Map::Held => &mut self.held,
            Map::Fields => &mut self.fields,
            Map::RFields => &mut self.rfields,
            Map::WFields => &mut self.wfields,
        }
    }

    fn get(&self, m: Map, s: SlotId) -> &Set {
        let map = match m {
            Map::Held => &self.held,
            Map::Fields => &self.fields,
            Map::RFields => &self.rfields,
            Map::WFields => &self.wfields,
        };
        map.get(&s).unwrap_or(&EMPTY)
    }

    fn add(&mut self, m: Map, s: SlotId, set: &Set) {
        if !set.is_empty() {
            union(self.map_mut(m).entry(s).or_default(), set);
        }
    }

    fn each_set(&mut self, mut f: impl FnMut(&mut Set)) {
        for m in MAPS {
            self.map_mut(m).values_mut().for_each(&mut f);
        }
    }
}

/// Why `held` reports EN0616 (A:1186-1206).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub enum StoreErrorKind {
    /// The read-set check: a `readonly &` field takes what another field writes
    /// through.
    ReadSet,
    /// A store into a value reached through a capture, inside an arrow.
    Captured,
    /// A store into a value reached through an Own `this` or the by-value borrowing
    /// parameter of this contract index.
    Consumed(u32),
}

/// An EN0616 of `store` or of a write's read-set check, at the write or the call.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub struct StoreError {
    pub at: Point,
    pub span: Span,
    pub kind: StoreErrorKind,
    /// A call's store, which the one-report rule may silence (A:1265).
    pub call: bool,
}

/// The solved analysis of one body: the state before each point, the state before
/// each `Return`, and the stores' EN0616s.
#[derive(Clone, Debug, Default)]
pub struct HeldResults {
    pub slots: Slots,
    pub at: BTreeMap<Point, State>,
    pub returns: Vec<(Point, State)>,
    pub store_errors: Vec<StoreError>,
}

impl HeldResults {
    /// Solves `held` over `cx.body`; `keys_only` skips bind marks (plan g.2).
    pub fn run(cx: &BodyCx, keys_only: bool) -> HeldResults {
        let flow = Flow {
            cx,
            wl: WLive::compute(cx.tcx, cx.body, cx.bodies, cx.scc, None),
            keys_only,
            own: own_this(cx.tcx, cx.body),
            arrow: matches!(cx.body.owner, BodyOwner::Arrow(..)),
            errors: RefCell::new(None),
        };
        let res = solve(cx.body, flow);
        *res.analysis.errors.borrow_mut() = Some(Vec::new());
        let mut out = HeldResults {
            slots: cx.slots.clone(),
            ..HeldResults::default()
        };
        let b = cx.body;
        res.visit(b, |p, before, _| {
            if b.stmt_at(p).is_none() && b.blocks[p.block].term.kind == TerminatorKind::Return {
                out.returns.push((p, before.clone()));
            }
            out.at.insert(p, before.clone());
        });
        let mut errors = res.analysis.errors.take().unwrap_or_default();
        errors.sort();
        errors.dedup();
        out.store_errors = errors;
        out
    }

    fn map(&self, p: Point, s: SlotId, m: Map) -> Set {
        self.at
            .get(&p)
            .map(|st| st.get(m, s).clone())
            .unwrap_or_default()
    }

    /// `held(s)` just before `p` runs.
    pub fn held_at(&self, p: Point, s: SlotId) -> Set {
        self.map(p, s, Map::Held)
    }

    /// `fields(s)` just before `p` (a borrowing value's is its `held`).
    pub fn fields_at(&self, p: Point, s: SlotId) -> Set {
        match self.slots.kind(s) {
            Some(SlotKind::ValueBorrowing) => self.held_at(p, s),
            _ => self.map(p, s, Map::Fields),
        }
    }

    pub fn rfields_at(&self, p: Point, s: SlotId) -> Set {
        self.map(p, s, Map::RFields)
    }

    pub fn wfields_at(&self, p: Point, s: SlotId) -> Set {
        self.map(p, s, Map::WFields)
    }

    /// `held` and `rfields` of `Caller(m)`, joined over every `Return`.
    pub fn caller_at_returns(&self, m: u32) -> (Set, Set) {
        let (mut held, mut rfields) = (Set::new(), Set::new());
        for (_, st) in &self.returns {
            union(&mut held, st.get(Map::Held, SlotId::Caller(m)));
            union(&mut rfields, st.get(Map::RFields, SlotId::Caller(m)));
        }
        (held, rfields)
    }

    /// `held(_0)` at each `Return`.
    pub fn ret_at_returns(&self) -> Vec<(Point, Set)> {
        let ret = SlotId::Local(Local::RETURN);
        self.returns
            .iter()
            .map(|(p, st)| (*p, st.get(Map::Held, ret).clone()))
            .collect()
    }
}

/// A row's result before it lands in a slot; `None` maps take the defaults.
#[derive(Clone, Debug, Default)]
struct Val {
    held: Set,
    fields: Option<Set>,
    rfields: Option<Set>,
    wfields: Option<Set>,
    /// New loans whose keys cover what they cross.
    new: Vec<LoanId>,
}

impl Val {
    fn held(held: Set) -> Val {
        Val {
            fields: Some(held.clone()),
            rfields: Some(held.clone()),
            held,
            ..Val::default()
        }
    }

    /// The four sets with the defaults of A:1040 applied.
    fn resolved(&self) -> (Set, Set, Set, Set) {
        let fields = self.fields.clone().unwrap_or_else(|| self.held.clone());
        let rfields = self.rfields.clone().unwrap_or_else(|| fields.clone());
        let wfields = self.wfields.clone().unwrap_or_else(|| self.held.clone());
        (self.held.clone(), fields, rfields, wfields)
    }
}

/// One store's inputs (A:1181): `ht` is `held(t)`, `class` the type behind `t`.
struct StoreArgs<'s> {
    ht: &'s Set,
    class: Ty,
    main: &'s Set,
    /// The read-set check's T, when it runs.
    check: Option<&'s Set>,
    rset: Option<&'s Set>,
    wset: Option<&'s Set>,
    at: Point,
    span: Span,
    call: bool,
    /// For a call's store of an argument's loans into itself, the callee.
    own: Option<DefId>,
}

type Pending = Vec<(Map, SlotId, Set)>;

struct Flow<'a, 'b> {
    cx: &'a BodyCx<'b>,
    wl: WLive<'b>,
    keys_only: bool,
    own: bool,
    arrow: bool,
    /// Collected only on the final pass.
    errors: RefCell<Option<Vec<StoreError>>>,
}

const PAYLOAD: [Proj; 2] = [Proj::Variant(VariantIdx::PRESENT), Proj::Field(FieldIdx(0))];

impl Flow<'_, '_> {
    fn body(&self) -> &Body {
        self.cx.body
    }

    fn kind(&self, l: Local) -> Option<SlotKind> {
        self.cx.slots.kind(SlotId::Local(l))
    }

    fn ty(&self, l: Local) -> Ty {
        self.body().locals[l].ty
    }

    fn err(&self, at: Point, span: Span, kind: StoreErrorKind, call: bool) {
        if let Some(v) = self.errors.borrow_mut().as_mut() {
            v.push(StoreError {
                at,
                span,
                kind,
                call,
            });
        }
    }

    fn held<'s>(&self, st: &'s State, l: Local) -> &'s Set {
        st.get(Map::Held, SlotId::Local(l))
    }

    /// `fields(l)`; a borrowing value's is its `held`.
    fn fields<'s>(&self, st: &'s State, l: Local) -> &'s Set {
        match self.kind(l) {
            Some(SlotKind::ValueBorrowing) => self.held(st, l),
            _ => st.get(Map::Fields, SlotId::Local(l)),
        }
    }

    fn rfields<'s>(&self, st: &'s State, l: Local) -> &'s Set {
        st.get(Map::RFields, SlotId::Local(l))
    }

    /// `site(t)`: the site loans of `held(t)` that `fields(t)` lacks (A:1040).
    fn site(&self, st: &State, t: Local) -> Set {
        let f = self.fields(st, t);
        self.held(st, t)
            .iter()
            .filter(|(k, _)| matches!(k, LoanKey::Site(..)) && !f.contains_key(k))
            .map(|(k, b)| (*k, *b))
            .collect()
    }

    /// `fields(t) ∪ site(t)`.
    fn through(&self, st: &State, t: Local) -> Set {
        let mut s = self.fields(st, t).clone();
        union(&mut s, &self.site(st, t));
        s
    }

    fn slot_val(&self, st: &State, l: Local) -> Val {
        let s = SlotId::Local(l);
        Val {
            held: self.held(st, l).clone(),
            fields: Some(self.fields(st, l).clone()),
            rfields: Some(self.rfields(st, l).clone()),
            wfields: Some(st.get(Map::WFields, s).clone()).filter(|w| !w.is_empty()),
            new: Vec::new(),
        }
    }

    fn rooted_through(&self, k: &LoanKey, r: Local) -> bool {
        matches!(k, LoanKey::Site(l, _)
            if self.cx.loans.table[*l].path.root == r && self.cx.loans.table[*l].path.through_ref)
    }

    fn flag(&self, ty: Ty) -> bool {
        class_flag(self.cx, ty)
    }

    fn bind_of(&self, at: Point) -> Option<&ForOfLoop> {
        self.body().meta.loops.iter().find(|l| l.bind == at)
    }

    fn bind_loan(&self, lp: &ForOfLoop) -> Option<LoanId> {
        self.cx
            .loans
            .at(lp.bind)
            .find(|(_, l)| l.kind == LoanKind::Site)
            .map(|(id, _)| id)
    }

    /// Whether N4 gives loan `id` at all (A:935): a reborrow copying a reference
    /// local, a nullable reference local's payload and a part of a tuple held
    /// directly in a local take one only when the copy or the source is write-live
    /// just after, and a constant literal view only when the slot it fills is
    /// (A:970: otherwise it becomes a static); every other loan exists.
    fn gives(&self, id: LoanId) -> bool {
        let (b, tcx) = (self.body(), self.cx.tcx);
        let loan = &self.cx.loans.table[id];
        let Some(Statement {
            kind: StatementKind::Assign { dest, value },
            ..
        }) = b.stmt_at(loan.site)
        else {
            return true;
        };
        let src = match (&loan.kind, value) {
            (LoanKind::Payload, _) => loan.path.root,
            (LoanKind::Part(_), _) if loan.path.steps.first() != Some(&Step::Fields) => {
                loan.path.root
            }
            (
                LoanKind::Site,
                Rvalue::Ref {
                    place,
                    origin: BorrowOrigin::Reborrow,
                },
            ) if b.projs(*place) == [Proj::Deref]
                && matches!(tcx.kind(self.ty(place.local)), TyKind::Ref(_))
                && b.locals[place.local].kind != LocalKind::ClosureEnv =>
            {
                place.local
            }
            (
                LoanKind::Site,
                Rvalue::Ref {
                    origin: BorrowOrigin::LiteralView,
                    ..
                },
            ) => dest.local,
            _ => return true,
        };
        // The part in the source, and the same part as the destination holds it.
        let (part, to): (&[u32], &[u32]) = match &loan.kind {
            LoanKind::Part(k) => (k, crate::loans::dest_part(b, loan, k)),
            _ => (&[], &[]),
        };
        let after = self.wl.after(loan.site);
        let live = |l: Local, part: &[u32]| {
            self.wl
                .slots()
                .under(l, part)
                .iter()
                .any(|w| after.contains(*w))
        };
        live(dest.local, to) || live(src, part)
    }

    fn new_loans(&self, at: Point, keep: impl Fn(&LoanKind) -> bool) -> Vec<LoanId> {
        self.cx
            .loans
            .at(at)
            .filter(|(id, l)| keep(&l.kind) && self.gives(*id))
            .map(|(id, _)| id)
            .collect()
    }

    fn keys(ids: &[LoanId]) -> Set {
        ids.iter()
            .map(|l| key(LoanKey::Site(*l, Turn::Any)))
            .collect()
    }

    // ---- rows -----------------------------------------------------------------

    fn value(&self, st: &State, at: Point, dest: Place, rv: &Rvalue) -> Val {
        let (b, tcx) = (self.body(), self.cx.tcx);
        let op_local = |o: &Operand| o.place().filter(|p| p.is_local()).map(|p| p.local);
        let union_of = |ops: &[&Operand]| {
            let mut s = Set::new();
            for l in ops.iter().filter_map(|o| op_local(o)) {
                union(&mut s, self.held(st, l));
            }
            s
        };
        match rv {
            Rvalue::Ref { place, origin } => self.ref_row(st, at, *place, *origin),
            Rvalue::Use(op) => self.use_row(st, at, op),
            Rvalue::Convert(_, op) => match op_local(op) {
                Some(t) => Val {
                    wfields: None,
                    ..self.slot_val(st, t)
                },
                None => Val::default(),
            },
            Rvalue::Aggregate(AggregateKind::Present, ops) => ops
                .first()
                .and_then(op_local)
                .map(|t| self.slot_val(st, t))
                .unwrap_or_default(),
            Rvalue::Aggregate(AggregateKind::ClosureEnv, ops) => {
                Val::held(union_of(&ops.iter().collect::<Vec<_>>()))
            }
            Rvalue::Aggregate(AggregateKind::Tuple | AggregateKind::Adt { .. }, ops) => {
                let Some(dty) = b.place_ty(tcx, dest).map(|p| p.ty) else {
                    return Val::default();
                };
                if !bvalue(tcx, dty) {
                    return Val::default();
                }
                let ro = |i: usize| match tcx.kind(dty) {
                    TyKind::Adt(adt, _) => tcx.adt(adt).as_class().is_some_and(|c| {
                        c.fields
                            .get(i)
                            .is_some_and(|f| f.readonly_refs.iter().any(|p| p.is_empty()))
                    }),
                    _ => false,
                };
                let (r, w): (Vec<_>, Vec<_>) = ops.iter().enumerate().partition(|(i, _)| ro(*i));
                Val {
                    held: union_of(&ops.iter().collect::<Vec<_>>()),
                    fields: None,
                    rfields: Some(union_of(&r.iter().map(|(_, o)| *o).collect::<Vec<_>>())),
                    wfields: Some(union_of(&w.iter().map(|(_, o)| *o).collect::<Vec<_>>())),
                    new: Vec::new(),
                }
            }
            Rvalue::ClosureValue { env, .. } => Val::held(self.held(st, env.local).clone()),
            Rvalue::ClosureReborrow(f) => {
                let new = self.new_loans(at, |k| *k == LoanKind::Site);
                let mut s = Self::keys(&new);
                union(&mut s, self.held(st, f.local));
                Val::held(s)
            }
            _ => Val::default(),
        }
    }

    fn ref_row(&self, st: &State, at: Point, place: Place, origin: BorrowOrigin) -> Val {
        let (b, tcx) = (self.body(), self.cx.tcx);
        let projs = b.projs(place);
        let Some((_, cross, ty_p)) = normalize(tcx, b, place.local, projs) else {
            return Val::default();
        };
        let bind = self.bind_of(at);
        let site = self
            .cx
            .loans
            .at(at)
            .find(|(_, l)| l.kind == LoanKind::Site)
            .map(|(id, _)| id)
            .filter(|id| self.gives(*id));
        let turn = if bind.is_some() {
            Turn::This
        } else {
            Turn::Any
        };
        let own = site.map(|l| LoanKey::Site(l, turn));
        let mut s: Set = own.into_iter().map(key).collect();
        let (mut f, mut r);
        match cross {
            Cross::Env => {
                union(&mut s, self.held(st, place.local));
                (f, r) = (s.clone(), s.clone());
            }
            Cross::LocalField { b: bl, ro } => {
                union(
                    &mut s,
                    if ro {
                        self.rfields(st, bl)
                    } else {
                        self.held(st, bl)
                    },
                );
                (f, r) = (s.clone(), s.clone());
            }
            Cross::PtrField { t, ro } => {
                let base = if ro {
                    self.rfields(st, t).clone()
                } else {
                    self.through(st, t)
                };
                union(&mut s, &base);
                (f, r) = (s.clone(), s.clone());
            }
            Cross::Ref(_) | Cross::None => {
                let t = match cross {
                    Cross::Ref(t) => Some(t),
                    _ => None,
                };
                if let Some(t) = t {
                    let mut a = self.held(st, t).clone();
                    if fixed_param(tcx, b, t) && tcx.is_value_type(ty_p) {
                        a.retain(|k, _| !matches!(k, LoanKey::Fields(_) | LoanKey::RFields(_)));
                    }
                    union(&mut s, &a);
                }
                let root = t.unwrap_or(place.local);
                let borrowing = bvalue(tcx, ty_p);
                f = match (borrowing, t) {
                    (true, Some(t)) => self.fields(st, t).clone(),
                    (true, None) => self.held(st, place.local).clone(),
                    // A reference to a whole closure local, as a capture of `f`
                    // makes, holds what `f`'s captures hold, since calling it
                    // reads through them (S:972, S:975); one to an `R | null` in a
                    // local, a tuple part included, as a form's `[temp-arg]` makes,
                    // holds what the local holds (S:837, A:977).
                    (false, None)
                        if (projs.is_empty() && closure_ty(tcx, ty_p))
                            || (!projs.contains(&Proj::Deref) && ref_carrying(tcx, ty_p)) =>
                    {
                        let mut x = s.clone();
                        union(&mut x, self.held(st, place.local));
                        x
                    }
                    (false, _) => s.clone(),
                };
                let whole = matches!(projs, [] | [Proj::Deref])
                    || projs == PAYLOAD
                    || projs == [PAYLOAD[0], PAYLOAD[1], Proj::Deref]
                    || projs == [Proj::Deref, PAYLOAD[0], PAYLOAD[1]];
                r = match borrowing && whole {
                    true => self.rfields(st, root).clone(),
                    false => f.clone(),
                };
                union(&mut s, &f);
            }
        }
        if origin == BorrowOrigin::ClosureCapture {
            for id in self.new_loans(at, |k| *k == LoanKind::Closure) {
                s.insert(LoanKey::Site(id, Turn::Any), KeyBits::default());
            }
        }
        if let Some(lp) = bind.filter(|_| !self.keys_only) {
            let lb = self.bind_loan(lp);
            for set in [&mut s, &mut f, &mut r] {
                for (k, bits) in set.iter_mut() {
                    let own_site = matches!(k, LoanKey::Site(l, _) if Some(*l) == lb);
                    if !own_site && Some(*k) != own {
                        bits.mark = Some(lp.id);
                    }
                }
            }
        }
        Val {
            held: s,
            fields: Some(f),
            rfields: Some(r),
            wfields: None,
            new: site.into_iter().collect(),
        }
    }

    fn use_row(&self, st: &State, at: Point, op: &Operand) -> Val {
        let (b, tcx) = (self.body(), self.cx.tcx);
        let (Operand::Copy(p) | Operand::Move(p)) = op else {
            return Val::default();
        };
        let copy = matches!(op, Operand::Copy(_));
        let (projs, t) = (b.projs(*p), p.local);
        let ty = self.ty(t);
        let new = self.new_loans(at, |_| true);
        let newset = Self::keys(&new);
        let tuple =
            |ty: Ty| bvalue(tcx, ty) && !matches!(tcx.kind(strip_null(tcx, ty)), TyKind::Adt(..));
        if projs.is_empty() {
            if self.kind(t).is_none() {
                return Val::default();
            }
            let mut v = self.slot_val(st, t);
            if copy && tuple(ty) {
                union(&mut v.held, &newset);
                return Val {
                    fields: Some(v.held.clone()),
                    held: v.held,
                    ..Val::default()
                };
            }
            if copy && matches!(tcx.kind(ty), TyKind::Nullable(_)) && pointee(tcx, ty).is_some() {
                union(&mut v.held, &newset);
                v.new = new;
            }
            return v;
        }
        if b.locals[t].kind == LocalKind::ClosureEnv
            && matches!(projs, [Proj::Deref, Proj::Field(_)])
        {
            let mut s = newset;
            union(&mut s, self.held(st, t));
            return Val {
                new,
                ..Val::held(s)
            };
        }
        if projs == PAYLOAD {
            return self.slot_val(st, t);
        }
        if projs == [Proj::Deref] && self.kind(t) == Some(SlotKind::PtrBorrowing) {
            let class = pointee(tcx, ty).is_some_and(|pt| !tuple(pt));
            return match copy {
                true => {
                    let mut h = self.through(st, t);
                    union(&mut h, &newset);
                    Val {
                        fields: Some(h.clone()),
                        rfields: class.then(|| self.rfields(st, t).clone()),
                        held: h,
                        ..Val::default()
                    }
                }
                false => Val {
                    held: self.fields(st, t).clone(),
                    rfields: Some(self.rfields(st, t).clone()),
                    ..Val::default()
                },
            };
        }
        let Some(through) = container(tcx, b, t, projs) else {
            return Val::default();
        };
        let Some(pty) = b.place_ty(tcx, *p).map(|x| x.ty) else {
            return Val::default();
        };
        let (cty, steps) = match through {
            true => (
                pointee(tcx, ty).unwrap_or(ty),
                crate::loans::after_deref(projs),
            ),
            false => (ty, projs),
        };
        let main = |st: &State| match through {
            true => self.through(st, t),
            false => self.held(st, t).clone(),
        };
        if !ref_parts(tcx, pty).is_empty() {
            let mut h = match readonly_field(tcx, cty, steps) {
                true => self.rfields(st, t).clone(),
                false => main(st),
            };
            union(&mut h, &newset);
            return Val {
                new,
                ..Val::held(h)
            };
        }
        if bvalue(tcx, pty) {
            let h = match (copy, through) {
                (false, true) => self.fields(st, t).clone(),
                _ => main(st),
            };
            return Val::held(h);
        }
        Val::default()
    }

    // ---- definitions, writes, stores ------------------------------------------

    fn assign(&self, st: &mut State, at: Point, dest: Place, v: Val, span: Span) {
        match dest.is_local() {
            true => self.define(st, dest.local, v),
            false => self.write(st, at, dest, v, span),
        }
    }

    /// `kill(d)`, then d's sets from `v` minus the loans rooted at d through a
    /// reference; each new loan that stays covers the keys it crosses (A:1072).
    fn define(&self, st: &mut State, d: Local, v: Val) {
        let s = SlotId::Local(d);
        let Some(kind) = self.kind(d) else {
            return;
        };
        self.kill(st, s);
        // The row that repoints a parameter leaves its keys bare too (A:1208).
        let param = param_index(self.body(), d);
        let strip = |mut set: Set| {
            set.retain(|k, _| !self.rooted_through(k, d));
            if let Some(i) = param {
                for k in [LoanKey::Param(i), LoanKey::Fields(i), LoanKey::RFields(i)] {
                    if let Some(bits) = set.get_mut(&k) {
                        bits.bare = true;
                    }
                }
            }
            set
        };
        let new = v.new.clone();
        let (held, fields, rfields, wfields) = v.resolved();
        let mut held = strip(held);
        for l in new {
            if !held
                .keys()
                .any(|k| matches!(k, LoanKey::Site(x, _) if *x == l))
            {
                continue;
            }
            let path = &self.cx.loans.table[l].path;
            let Some(i) = param_index(self.body(), path.root).filter(|_| path.through_ref) else {
                continue;
            };
            let fields_too = path.steps.first() == Some(&Step::Fields);
            for (k, bits) in held.iter_mut() {
                let crossed = match k {
                    LoanKey::Param(j) => *j == i,
                    LoanKey::Fields(j) | LoanKey::RFields(j) => *j == i && fields_too,
                    _ => false,
                };
                if crossed {
                    bits.bare = false;
                }
            }
        }
        let mut put = |m: Map, set: Set| {
            if !set.is_empty() {
                st.map_mut(m).insert(s, set);
            }
        };
        put(Map::Held, held);
        put(Map::RFields, strip(rfields));
        match kind {
            SlotKind::ValueBorrowing => put(Map::WFields, strip(wfields)),
            _ => put(Map::Fields, strip(fields)),
        }
    }

    /// `kill(s)` (A:1208).
    fn kill(&self, st: &mut State, s: SlotId) {
        if let SlotId::Local(r) = s {
            st.each_set(|set| set.retain(|k, _| !self.rooted_through(k, r)));
        }
        for m in MAPS {
            st.map_mut(m).remove(&s);
        }
        let param = match s {
            SlotId::Local(r) => param_index(self.body(), r),
            _ => None,
        };
        if let Some(i) = param {
            st.each_set(|set| {
                for k in [LoanKey::Param(i), LoanKey::Fields(i), LoanKey::RFields(i)] {
                    if let Some(bits) = set.get_mut(&k) {
                        bits.bare = true;
                    }
                }
            });
        }
        for m in MAPS {
            st.map_mut(m).retain(|_, set| !set.is_empty());
        }
    }

    /// A write of a ref-carrying value inside a local borrowing value or inside a
    /// borrowing value behind a reference (A:1112-1148).
    fn write(&self, st: &mut State, at: Point, dest: Place, u: Val, span: Span) {
        let (b, tcx) = (self.body(), self.cx.tcx);
        let (d, projs) = (dest.local, b.projs(dest));
        let Some(pty) = b.place_ty(tcx, dest).map(|p| p.ty) else {
            return;
        };
        if tcx.is_value_type(pty) {
            return;
        }
        let (uh, _, ur, uw) = u.resolved();
        let dty = self.ty(d);
        // The class of the value a nested `readonly &` field write lands in.
        let nested = |steps: &[Proj]| match steps.split_last() {
            Some((Proj::Field(_), prefix)) if !prefix.is_empty() => {
                let mut pt = PlaceTy::of(dty);
                for &p in &projs[..projs.len() - steps.len() + prefix.len()] {
                    pt = pt.project(tcx, p)?;
                }
                readonly_field(tcx, pt.ty, &steps[prefix.len()..]).then_some(pt.ty)
            }
            _ => None,
        };
        let deref = projs.iter().rposition(|p| *p == Proj::Deref);
        if deref.is_none() && self.kind(d) == Some(SlotKind::ValueBorrowing) {
            let before = st.clone();
            let s = SlotId::Local(d);
            st.add(Map::Held, s, &uh);
            if readonly_field(tcx, dty, projs) {
                if meets(&uh, before.get(Map::WFields, s)) && self.flag(dty) {
                    self.err(at, span, StoreErrorKind::ReadSet, false);
                }
                st.add(Map::RFields, s, &uh);
            } else {
                if let Some(cls) = nested(projs)
                    && meets(&uh, self.held(&before, d))
                    && self.flag(cls)
                {
                    self.err(at, span, StoreErrorKind::ReadSet, false);
                }
                st.add(Map::WFields, s, &uh);
            }
            return;
        }
        let Some(i) = deref else {
            return;
        };
        let (base, rest) = (&projs[..i], &projs[i + 1..]);
        let env = b.locals[d].kind == LocalKind::ClosureEnv;
        if env && !base.is_empty() {
            self.err(at, span, StoreErrorKind::Captured, false);
            return;
        }
        // held of the reference written through: a slot, or a reference field.
        // `*(d as Present).0` of a narrowed reference counts as `*d` (A:1030).
        let narrowed = base == PAYLOAD;
        let ht = match (base.is_empty() || narrowed, container(tcx, b, d, base)) {
            (true, _) if self.kind(d) == Some(SlotKind::PtrBorrowing) => self.held(st, d).clone(),
            (false, Some(true)) => self.through(st, d),
            (false, Some(false)) => self.held(st, d).clone(),
            _ => return,
        };
        let mut pt = PlaceTy::of(dty);
        for &p in base {
            match pt.project(tcx, p) {
                Some(x) => pt = x,
                None => return,
            }
        }
        let Some(class) = pointee(tcx, pt.ty) else {
            return;
        };
        let read = readonly_field(tcx, class, rest);
        let whole = rest.is_empty();
        if self.own && d == Local(1) && base.is_empty() {
            // An Own `this`: a write into a local value, no store (A:1132).
            let t = SlotId::Local(d);
            if read && uh.contains_key(&LoanKey::Fields(0)) && self.flag(class) {
                self.err(at, span, StoreErrorKind::ReadSet, false);
            }
            if let Some(cls) = nested(rest) {
                let local = self
                    .local_roots(&ht)
                    .into_iter()
                    .any(|(bl, _)| meets(&uh, self.held(st, bl)));
                if (meets(&uh, self.fields(st, d)) || local) && self.flag(cls) {
                    self.err(at, span, StoreErrorKind::ReadSet, false);
                }
            }
            st.add(Map::Held, t, &uh);
            st.add(Map::Fields, t, &uh);
            if read {
                st.add(Map::RFields, t, &uh);
            }
            if whole {
                st.add(Map::RFields, t, &ur);
            }
            return;
        }
        let snapshot = st.clone();
        let mut pending = Pending::new();
        let whole_class = whole && matches!(tcx.kind(strip_null(tcx, class)), TyKind::Adt(..));
        let args = match whole_class {
            true => StoreArgs {
                ht: &ht,
                class,
                main: &uh,
                check: Some(&ur),
                rset: Some(&ur),
                wset: Some(&uw),
                at,
                span,
                call: false,
                own: None,
            },
            false => StoreArgs {
                ht: &ht,
                class,
                main: &uh,
                check: read.then_some(&uh),
                rset: read.then_some(&uh),
                wset: (!read).then_some(&uh),
                at,
                span,
                call: false,
                own: None,
            },
        };
        self.store(&snapshot, &mut pending, &args);
        for (m, s, set) in pending {
            st.add(m, s, &set);
        }
    }

    /// The loans of `ht` without `through_ref` rooted at a borrowing local, with
    /// their steps.
    fn local_roots(&self, ht: &Set) -> Vec<(Local, Vec<Step>)> {
        ht.keys()
            .filter_map(|k| match k {
                LoanKey::Site(l, _) => Some(&self.cx.loans.table[*l].path),
                _ => None,
            })
            .filter(|p| !p.through_ref && self.kind(p.root) == Some(SlotKind::ValueBorrowing))
            .map(|p| (p.root, p.steps.clone()))
            .collect()
    }

    /// The declared type of the value at `root` + `steps`.
    fn path_ty(&self, root: Local, steps: &[Step]) -> Option<Ty> {
        let tcx = self.cx.tcx;
        let mut pt = PlaceTy::of(self.ty(root));
        for s in steps {
            let p = match s {
                Step::Field(f) => Proj::Field(*f),
                Step::Variant(v) => Proj::Variant(*v),
                Step::Elem => Proj::ConstIndex(0),
                Step::BoxDeref => Proj::Deref,
                Step::Capture(_) | Step::Fields => return None,
            };
            pt = pt.project(tcx, p)?;
        }
        Some(pt.ty)
    }

    /// `store(t, T, read, wr)` (A:1181-1206) against the snapshot `b`; the unions go
    /// to `out`.
    fn store(&self, b: &State, out: &mut Pending, a: &StoreArgs) {
        let body = self.body();
        if let Some(t) = a.check {
            let param =
                a.ht.keys().any(
                    |k| matches!(k, LoanKey::Param(i) if t.contains_key(&LoanKey::Fields(*i))),
                ) && self.flag(a.class);
            let local = self.local_roots(a.ht).into_iter().any(|(bl, steps)| {
                let s = SlotId::Local(bl);
                match steps.is_empty()
                    || steps == [Step::Variant(VariantIdx::PRESENT), Step::Field(FieldIdx(0))]
                {
                    true => meets(t, b.get(Map::WFields, s)) && self.flag(self.ty(bl)),
                    false => {
                        meets(t, b.get(Map::Held, s))
                            && self.path_ty(bl, &steps).is_some_and(|ty| self.flag(ty))
                    }
                }
            });
            if (param || local) && !a.own.is_some_and(|d| self.callee_rejects(d)) {
                self.err(a.at, a.span, StoreErrorKind::ReadSet, a.call);
            }
        }
        let push = |out: &mut Pending, m: Map, s: SlotId, set: Option<&Set>| {
            if let Some(set) = set {
                out.push((m, s, set.clone()));
            }
        };
        for k in a.ht.keys() {
            let LoanKey::Site(l, _) = k else {
                continue;
            };
            let path = &self.cx.loans.table[*l].path;
            if path.through_ref || self.kind(path.root).is_none() {
                continue;
            }
            let s = SlotId::Local(path.root);
            push(out, Map::Held, s, Some(a.main));
            push(out, Map::RFields, s, a.rset);
            if self.kind(path.root) == Some(SlotKind::ValueBorrowing) {
                push(out, Map::WFields, s, a.wset);
            }
        }
        for (s, kind) in &self.cx.slots.list {
            if *kind == SlotKind::PtrBorrowing && meets(b.get(Map::Held, *s), a.ht) {
                push(out, Map::Held, *s, Some(a.main));
                push(out, Map::Fields, *s, Some(a.main));
                push(out, Map::RFields, *s, a.rset);
            }
        }
        let mut consumed = None;
        for k in a.ht.keys() {
            let (LoanKey::Param(m) | LoanKey::Fields(m) | LoanKey::RFields(m)) = *k else {
                continue;
            };
            let caller = SlotId::Caller(m);
            if self.cx.slots.has(caller) {
                push(out, Map::Held, caller, Some(a.main));
                push(out, Map::RFields, caller, a.rset);
            }
            let by_value = self.kind(Local(m + 1)) == Some(SlotKind::ValueBorrowing)
                && param_index(body, Local(m + 1)) == Some(m);
            if (self.own && m == 0) || by_value {
                consumed.get_or_insert(m);
            }
        }
        if self.arrow
            && a.ht.keys().any(|k| matches!(k, LoanKey::Site(l, _) if self.cx.loans.table[*l].path.root == Local(1)))
        {
            self.err(a.at, a.span, StoreErrorKind::Captured, a.call);
        }
        if let Some(m) = consumed {
            self.err(a.at, a.span, StoreErrorKind::Consumed(m), a.call);
        }
    }

    /// Whether user callee `d`'s own body is rejected, by the read-set check or
    /// a conflict: then a store of an object's loans into that object that its
    /// contract records comes from a body already reported, once (A:1270,
    /// `INF-04-upcast`, `FV-02-copier`), and its callers check it no more. A body
    /// that passes keeps the caller's check, which sees the caller's loans
    /// (`FV-02-skip`'s `nudge`).
    fn callee_rejects(&self, d: DefId) -> bool {
        let cx = self.cx;
        if !cx.probe {
            return false;
        }
        if let Some(&r) = cx.rejects.borrow().get(&d) {
            return r;
        }
        let Some(b) = cx.bodies.get(&BodyOwner::Fn(d)) else {
            return false;
        };
        let mut inner = BodyCx::new(cx.tcx, cx.bodies, b, cx.scc);
        inner.probe = false;
        let held = HeldResults::run(&inner, false);
        let live = crate::liveness::LiveSlots::compute(&inner);
        let modes = crate::wlive::compute_modes(&inner, &held);
        let r = (held.store_errors.iter()).any(|e| e.kind == StoreErrorKind::ReadSet)
            || !crate::access::check(&inner, &held, &live, &modes).is_empty();
        cx.rejects.borrow_mut().insert(d, r);
        r
    }

    /// A call (A:1150-1185): the result from the sources, then every store against
    /// the state before the call, the unions applied after.
    fn call(
        &self,
        st: &mut State,
        at: Point,
        callee: &Callee,
        args: &[Operand],
        dest: Place,
        span: Span,
    ) {
        let (b, tcx) = (self.body(), self.cx.tcx);
        let before = st.clone();
        let mut val = Val::default();
        let mut pending = Pending::new();
        if !matches!(
            callee,
            Callee::NamedFill { .. } | Callee::ImplicitCtor { .. }
        ) {
            let ci = call_info(self.cx, callee, args);
            let ret = b.place_ty(tcx, dest).map(|p| p.ty);
            if ret.is_some_and(|r| ref_carrying(tcx, r))
                && let RetSources::Params(src) = &ci.sources
            {
                for &i in src {
                    let Some(l) = arg_local(&ci, args, i) else {
                        continue;
                    };
                    let set = match (ci.through_read.contains(&i), ci.through_fields.contains(&i)) {
                        (true, _) => self.rfields(&before, l),
                        (_, true) => self.fields(&before, l),
                        _ => self.held(&before, l),
                    };
                    union(&mut val.held, set);
                }
                val = Val::held(val.held);
            }
            for s in &ci.stores {
                let (Some(j), Some(k)) =
                    (arg_local(&ci, args, s.from), arg_local(&ci, args, s.into))
                else {
                    continue;
                };
                let t = match (s.read_set_only, s.fields_only) {
                    (true, _) => self.rfields(&before, j),
                    (_, true) => self.fields(&before, j),
                    _ => self.held(&before, j),
                };
                let wr = !s.read_set_only && !(s.read && read_param(self.cx, &ci, args, s.from));
                let check = s.read && !(s.read_set_only && s.from == s.into);
                let kty = self.ty(k);
                self.store(
                    &before,
                    &mut pending,
                    &StoreArgs {
                        ht: self.held(&before, k),
                        class: pointee(tcx, kty).unwrap_or(kty),
                        main: t,
                        check: check.then_some(t),
                        rset: s.read.then_some(t),
                        wset: wr.then_some(t),
                        at,
                        span,
                        call: true,
                        own: match (callee, s.from == s.into) {
                            (Callee::Fn(f) | Callee::Virtual { method: f, .. }, true) => {
                                Some(f.def)
                            }
                            _ => None,
                        },
                    },
                );
            }
        }
        self.assign(st, at, dest, val, span);
        for (m, s, set) in pending {
            if !(dest.is_local() && s == SlotId::Local(dest.local)) {
                st.add(m, s, &set);
            }
        }
    }

    // ---- loops ----------------------------------------------------------------

    /// A pre-header: this run's and earlier turns' keys become earlier runs', and a
    /// mark via this loop's bind becomes plain (A:1044).
    fn preheader(&self, st: &mut State, block: BlockId) {
        for lp in self
            .body()
            .meta
            .loops
            .iter()
            .filter(|l| l.preheader == block)
        {
            let lb = self.bind_loan(lp);
            st.each_set(|set| {
                if let Some(lb) = lb {
                    rename(
                        set,
                        lb,
                        &[Turn::This, Turn::EarlierThisRun],
                        Turn::EarlierRuns,
                    );
                }
                for bits in set.values_mut() {
                    if bits.mark == Some(lp.id) {
                        bits.mark = None;
                    }
                }
            });
        }
    }

    /// The hold of a loop over a path, at the end of its pre-header (A:1223).
    fn hold(&self, st: &mut State, at: Point) {
        for lp in self
            .body()
            .meta
            .loops
            .iter()
            .filter(|l| l.preheader == at.block)
        {
            if !matches!(lp.source, LoopSource::Path(_)) {
                continue;
            }
            let s = SlotId::Hold(lp.id);
            self.kill(st, s);
            let mut set: Set = [key(LoanKey::Hold(lp.id))].into();
            for (id, l) in self.cx.loans.at(at) {
                if l.kind == LoanKind::HoldCrossing(lp.id) {
                    set.insert(LoanKey::Site(id, Turn::Any), KeyBits::default());
                }
            }
            st.held.insert(s, set);
        }
    }
}

/// Renames `Site(l, from)` keys to `Site(l, to)`, merging with a copy there.
fn rename(set: &mut Set, l: LoanId, from: &[Turn], to: Turn) {
    for t in from {
        if let Some(bits) = set.remove(&LoanKey::Site(l, *t)) {
            let k = LoanKey::Site(l, to);
            let new = set.get(&k).map_or(bits, |x| x.merge(bits));
            set.insert(k, new);
        }
    }
}

impl DataflowAnalysis for Flow<'_, '_> {
    type Domain = State;
    const FORWARD: bool = true;

    fn bottom(&self, _b: &Body) -> State {
        State::default()
    }

    /// Each ref-carrying parameter's keys, bare (A:1038-1040).
    fn entry(&self, b: &Body) -> State {
        let mut st = State::default();
        let bare = |keys: &[LoanKey]| -> Set { keys.iter().map(|k| (*k, KeyBits::BARE)).collect() };
        for l in b.args() {
            let s = SlotId::Local(l);
            let Some(kind) = self.cx.slots.kind(s) else {
                continue;
            };
            let i = l.0 - 1;
            let (p, f, r) = (LoanKey::Param(i), LoanKey::Fields(i), LoanKey::RFields(i));
            if self.arrow && l.0 == 1 {
                st.held.insert(s, bare(&[p]));
                continue;
            }
            match kind {
                SlotKind::PtrBorrowing => {
                    st.held.insert(s, bare(&[p, f, r]));
                    st.fields.insert(s, bare(&[f, r]));
                    st.rfields.insert(s, bare(&[r]));
                }
                SlotKind::ValueBorrowing => {
                    st.held.insert(s, bare(&[p]));
                    st.rfields.insert(s, bare(&[p]));
                    st.wfields.insert(s, bare(&[p]));
                }
                SlotKind::Plain => {
                    st.held.insert(s, bare(&[p]));
                }
            }
        }
        st
    }

    fn join(&self, into: &mut State, from: &State) -> bool {
        let mut changed = false;
        for m in MAPS {
            let src = match m {
                Map::Held => &from.held,
                Map::Fields => &from.fields,
                Map::RFields => &from.rfields,
                Map::WFields => &from.wfields,
            };
            let dst = into.map_mut(m);
            for (s, set) in src {
                changed |= union(dst.entry(*s).or_default(), set);
            }
        }
        changed
    }

    fn statement(&self, st: &mut State, s: &Statement, at: Point) {
        if at.index == 0 {
            self.preheader(st, at.block);
        }
        if let Some(lp) = self.bind_of(at)
            && let Some(lb) = self.bind_loan(lp)
        {
            st.each_set(|set| rename(set, lb, &[Turn::This], Turn::EarlierThisRun));
        }
        match &s.kind {
            StatementKind::Assign { dest, value } => {
                let v = self.value(st, at, *dest, value);
                self.assign(st, at, *dest, v, s.span);
            }
            StatementKind::FieldInit { field, value } => {
                let v = self.use_row(st, at, value);
                self.assign(st, at, *field, v, s.span);
            }
            StatementKind::Intrinsic { dest: Some(d), .. }
            | StatementKind::HostCall { dest: Some(d), .. } => {
                self.assign(st, at, *d, Val::default(), s.span);
            }
            _ => {}
        }
    }

    fn terminator(&self, st: &mut State, t: &Terminator, at: Point) {
        if at.index == 0 {
            self.preheader(st, at.block);
        }
        if let TerminatorKind::Call {
            callee, args, dest, ..
        } = &t.kind
        {
            self.call(st, at, callee, args, *dest, t.span);
        }
        self.hold(st, at);
    }
}

/// A borrowing class's flag: the SCC being inferred first, then the memo; a
/// tuple's is always set (A:1336).
pub(crate) fn class_flag(cx: &BodyCx, ty: Ty) -> bool {
    let tcx = cx.tcx;
    match tcx.kind(strip_null(tcx, ty)) {
        TyKind::Adt(adt, _) => cx
            .scc
            .and_then(|s| s.flags.get(&adt).copied())
            .unwrap_or_else(|| crate::class_contract(tcx, adt).writes_through_fields),
        TyKind::Tuple(_) => true,
        _ => false,
    }
}

/// The local passed for contract index `i`.
pub(crate) fn arg_local(ci: &CallInfo, args: &[Operand], i: u32) -> Option<Local> {
    let op = args.get(*ci.args_map.get(i as usize)?)?;
    op.place().filter(|p| p.is_local()).map(|p| p.local)
}

fn arg_ty(cx: &BodyCx, ci: &CallInfo, args: &[Operand], i: u32) -> Option<Ty> {
    match args.get(*ci.args_map.get(i as usize)?)? {
        Operand::Copy(p) | Operand::Move(p) => cx.body.place_ty(cx.tcx, *p).map(|t| t.ty),
        Operand::Const(c) => Some(c.ty),
    }
}

/// The permission of contract index `j` when it is a `&` parameter: `perms` holds
/// one per `&` parameter, `this` first (A:311).
pub(crate) fn perm_of(cx: &BodyCx, ci: &CallInfo, args: &[Operand], j: u32) -> Option<Perm> {
    let is_ref = |i: u32| arg_ty(cx, ci, args, i).is_some_and(|t| pointee(cx.tcx, t).is_some());
    if !is_ref(j) {
        return None;
    }
    ci.perms.get((0..j).filter(|&i| is_ref(i)).count()).copied()
}

/// `j` is a `&` parameter whose permission is Read, or a by-value borrowing tuple
/// parameter whose reference parts are all Read (A:1158).
fn read_param(cx: &BodyCx, ci: &CallInfo, args: &[Operand], j: u32) -> bool {
    if let Some(p) = perm_of(cx, ci, args, j) {
        return p == Perm::Read;
    }
    let tcx = cx.tcx;
    let n = ci.args_map.len() as u32;
    let is_ref = |i: u32| arg_ty(cx, ci, args, i).is_some_and(|t| pointee(tcx, t).is_some());
    let parts = |i: u32| match arg_ty(cx, ci, args, i) {
        Some(t) if bvalue(tcx, t) && !matches!(tcx.kind(strip_null(tcx, t)), TyKind::Adt(..)) => {
            ref_parts(tcx, t).len()
        }
        _ => 0,
    };
    let start = (0..n).filter(|&i| is_ref(i)).count() + (0..j).map(parts).sum::<usize>();
    let count = parts(j);
    count > 0 && (start..start + count).all(|x| ci.perms.get(x) == Some(&Perm::Read))
}
