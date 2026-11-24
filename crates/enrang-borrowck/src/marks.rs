//! Read-only marks (A:1009, S:773; M3 plan d.3; owner 2D): where a slot's
//! reference comes from something that may not be written, and the reports
//! EN0608, EN0609, EN0614 and EN0616.
//!
//! A forward may-analysis over the reference-carrying locals (`SlotId::Local`):
//! a `Ref` takes the marks of its place, a copy, a `Convert` or an aggregate the
//! marks of its operands, a call result its callee's read-only reason and the
//! marks of its source arguments; repointing replaces, joins union, a store into
//! a borrowing value carries none. Each mark records how it came: made here,
//! through loop l's bind (the pre-header makes it plain), or from a call's marked
//! source argument. A write through a marked slot, or passing one to a Write
//! parameter or into a class that writes through its fields, reports the first
//! origin once: at the write, at loop l's source, or at the call.

use std::collections::{BTreeMap, BTreeSet};

use enrang_base::{BitSet, Span};
use enrang_diag::Code;
use enrang_hir::{
    AdtId, ConstValue, DefId, DefKind, FieldIdx, LoopId, Mark, Reason, ResultPerm, RetSources, Tcx,
    TyKind,
};
use enrang_mir::{
    AggregateKind, BlockId, Body, BorrowOrigin, Callee, ConstKind, DataflowAnalysis, Local,
    LocalKind, Operand, Place, PlaceTy, Point, Proj, Rvalue, Statement, StatementKind, Terminator,
    TerminatorKind, solve,
};

use crate::cx::{BodyCx, call_info};
use crate::held::HeldResults;
use crate::init::{point_dests, unset};
use crate::movepaths::{MoveData, MovePathIdx, def_of, owner_def};
use crate::moves::span_at;
use crate::slots::SlotId;

/// Where a read-only mark comes from (plan d.3).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum MarkOrigin {
    ConstRoot(Local),
    ByValueParam(Local),
    TopConst(DefId),
    StringLiteral,
    ConstLiteral(Span),
    ReadonlyField(AdtId, FieldIdx),
    ReadonlyRef(AdtId, FieldIdx),
    RawDerived(Span),
    ReadOnlyResult(DefId),
    ConstPointing(DefId),
    StringPart(DefId),
}

impl MarkOrigin {
    /// The code a write through it reports (A:1009).
    pub fn code(self) -> Code {
        match self {
            MarkOrigin::ConstRoot(_)
            | MarkOrigin::ByValueParam(_)
            | MarkOrigin::TopConst(_)
            | MarkOrigin::ConstLiteral(_) => Code::EN0608,
            MarkOrigin::ReadonlyField(..) => Code::EN0609,
            _ => Code::EN0616,
        }
    }
}

/// A write through a marked slot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MarkError {
    pub code: Code,
    pub origin: MarkOrigin,
    pub at: Point,
    pub span: Span,
    /// For a marked argument of the call at `at` passed to a Write parameter:
    /// its index among the call's arguments.
    pub arg: Option<usize>,
}

/// How a mark reached a slot.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Via {
    Plain,
    Loop(LoopId),
    /// From a marked source argument of the call at this point.
    Call(Point),
}

type Marks = BTreeMap<MarkOrigin, Via>;
type State = BTreeMap<Local, Marks>;

/// The solved marks of one body: the state before each point.
#[derive(Clone, Debug, Default)]
pub struct MarkResults {
    at: BTreeMap<Point, State>,
}

/// The root a local is frozen by (S 4.11): a `const` local, or a by-value
/// parameter not marked `let`.
pub(crate) fn frozen(tcx: &Tcx, b: &Body, l: Local) -> Option<MarkOrigin> {
    let d = &b.locals[l];
    let by_ref = |t: enrang_hir::Ty| match tcx.kind(t) {
        TyKind::Nullable(t) => matches!(tcx.kind(t), TyKind::Ref(_)),
        k => matches!(k, TyKind::Ref(_)),
    };
    match d.kind {
        LocalKind::User if !d.mutable => Some(MarkOrigin::ConstRoot(l)),
        // An arrow's parameter is a by-value parameter too, frozen unless written
        // `let` (S:444, S:774), which its local keeps; `_1` is the environment.
        LocalKind::Arg if matches!(b.owner, enrang_mir::BodyOwner::Arrow(..)) => {
            (!d.mutable && !by_ref(d.ty)).then_some(MarkOrigin::ByValueParam(l))
        }
        LocalKind::Arg => {
            let def = owner_def(b)?;
            let i = (l.0 as usize - 1).checked_sub(usize::from(tcx.takes_this(def)))?;
            let p = tcx.sig_opt(def)?.params.get(i)?;
            (p.mark != Mark::Let && !by_ref(p.ty)).then_some(MarkOrigin::ByValueParam(l))
        }
        _ => None,
    }
}

fn merge(into: &mut Marks, o: MarkOrigin, v: Via) -> bool {
    match into.get(&o) {
        None => {
            into.insert(o, v);
            true
        }
        Some(&w) if w != v && w != Via::Plain => {
            into.insert(o, Via::Plain);
            true
        }
        _ => false,
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum Mode {
    Ref,
    Copy,
    /// A write; `true` when it initialises the path (a named form's field).
    Write(bool),
}

struct Flow<'a, 'c> {
    cx: &'a BodyCx<'c>,
    /// A local function's hidden parameters whose captured variable is a
    /// `const`: marked at entry, so a write through one is EN0608 at the write
    /// (S:981, T:820).
    const_hidden: BTreeSet<Local>,
    /// An arrow body's env fields that capture a `const` path: a write of
    /// `*(*_1).i` is a write of that `const` (EN0608, EN0614 at the write).
    const_captures: BTreeSet<u32>,
    /// The body is a constructor: its writes of `this`'s `readonly` fields are no
    /// writes through anything.
    ctor: bool,
    /// A `new`'s borrow of its destination initialises it (c.10).
    md: &'a MoveData,
}

impl<'a, 'c> Flow<'a, 'c> {
    fn new(cx: &'a BodyCx<'c>) -> Self {
        let ctor = owner_def(cx.body).is_some_and(|d| cx.tcx.def(d).kind == DefKind::Ctor);
        let md = &cx.moves;
        let const_hidden = match cx.body.owner {
            enrang_mir::BodyOwner::Fn(d) => {
                let hidden = crate::r3::hidden(cx.tcx, d, cx.body);
                (hidden.into_iter())
                    .filter(|&i| captures_const(cx, d, i, &mut BTreeSet::new()))
                    .map(|i| Local(i + 1))
                    .collect()
            }
            _ => BTreeSet::new(),
        };
        let const_captures = match cx.body.owner {
            enrang_mir::BodyOwner::Arrow(top, a) => (0..cx.body.captures.len() as u32)
                .filter(|&i| arrow_captures_const(cx, top, a, i, &mut BTreeSet::new()))
                .collect(),
            _ => BTreeSet::new(),
        };
        Flow {
            cx,
            const_hidden,
            const_captures,
            ctor,
            md,
        }
    }
}

impl Flow<'_, '_> {
    /// The marks of `place` taken by a `Ref`, read by a copy, or written through:
    /// the slot's own when the place reaches through the reference the local
    /// holds (or, for a copy, is part of the local), then `readonly &` parts, then,
    /// for a `Ref` or a write of an owned place, its root and `readonly` fields.
    fn place(&self, s: &State, pl: Place, mode: Mode, span: Span) -> Marks {
        let (tcx, b) = (self.cx.tcx, self.cx.body);
        let slot = s.get(&pl.local).into_iter().flatten();
        let mut m = Marks::new();
        let mut owner = frozen(tcx, b, pl.local).filter(|_| mode != Mode::Write(true));
        let (mut ro_field, mut crossed) = (None, false);
        let mut parts: Option<(AdtId, FieldIdx, &[Vec<u32>], Vec<u32>)> = None;
        let mut ty = PlaceTy::of(b.locals[pl.local].ty);
        let ctor_this = self.ctor && pl.local == Local(1);
        for (k, proj) in b.projs(pl).iter().enumerate() {
            match (*proj, tcx.kind(ty.ty)) {
                (Proj::Deref, TyKind::Raw(_)) => {
                    // Only a reference made through a raw pointer is raw-derived
                    // (plan d.3); `*p = v` and a write of an `unsafe let` are not.
                    if !matches!(mode, Mode::Write(_)) {
                        m.insert(MarkOrigin::RawDerived(span), Via::Plain);
                    }
                    (owner, ro_field, parts, crossed) = (None, None, None, true);
                }
                (Proj::Deref, TyKind::Ref(_)) => {
                    if !crossed {
                        m.extend(slot.clone());
                    }
                    if let Some((adt, f, refs, path)) = &parts
                        && refs.contains(path)
                    {
                        m.insert(MarkOrigin::ReadonlyRef(*adt, *f), Via::Plain);
                    }
                    (owner, ro_field, parts, crossed) = (None, None, None, true);
                    // `*(*_1).i` of an arrow: the captured path itself, a `const`
                    // one as frozen as the variable (its root's mark).
                    if let (2, [Proj::Deref, Proj::Field(i), ..]) = (k, b.projs(pl))
                        && pl.local == Local(1)
                        && self.const_captures.contains(&i.0)
                        && mode != Mode::Write(true)
                    {
                        owner = Some(MarkOrigin::ConstRoot(Local(1)));
                    }
                }
                (Proj::Field(f), TyKind::Adt(adt, _)) if ty.variant.is_none() => {
                    let fd = tcx.field_def(adt, None, f);
                    let exempt = ctor_this && k == 1 && matches!(mode, Mode::Write(_));
                    if fd.readonly && !exempt {
                        ro_field = Some(MarkOrigin::ReadonlyField(adt, f));
                    }
                    parts = (!fd.readonly_refs.is_empty())
                        .then(|| (adt, f, &fd.readonly_refs[..], Vec::new()));
                }
                (Proj::Field(FieldIdx(i)), TyKind::Tuple(_)) => {
                    parts.iter_mut().for_each(|p| p.3.push(i));
                }
                (Proj::ConstIndex(i), TyKind::Tuple(_)) => {
                    parts.iter_mut().for_each(|p| p.3.push(i as u32));
                }
                _ => {}
            }
            ty = ty.project(tcx, *proj).expect("a typed place");
        }
        // A store into the field itself takes no reference through it (A:1009). A
        // copy of the tuple, or of a part holding a `readonly` part, carries it as a
        // reference to it does (S:592).
        let ro = parts.filter(|(_, _, refs, path)| match mode {
            Mode::Copy | Mode::Ref => refs.iter().any(|r| r.starts_with(path)),
            Mode::Write(_) => false,
        });
        m.extend(ro.map(|(adt, f, ..)| (MarkOrigin::ReadonlyRef(adt, f), Via::Plain)));
        match mode {
            Mode::Copy if !crossed => m.extend(slot),
            Mode::Copy => {}
            _ => m.extend(owner.into_iter().chain(ro_field).map(|o| (o, Via::Plain))),
        }
        m
    }

    fn operand(&self, s: &State, op: &Operand, span: Span) -> Marks {
        match op {
            Operand::Copy(p) | Operand::Move(p) => self.place(s, *p, Mode::Copy, span),
            Operand::Const(c) => {
                let by_ref = matches!(self.cx.tcx.kind(c.ty), TyKind::Ref(_));
                let o = match c.kind {
                    ConstKind::Value(ConstValue::Str(_)) if by_ref => MarkOrigin::StringLiteral,
                    ConstKind::Value(ConstValue::StaticAddr(d)) if by_ref => {
                        MarkOrigin::TopConst(d)
                    }
                    _ => return Marks::new(),
                };
                Marks::from([(o, Via::Plain)])
            }
        }
    }

    fn rvalue(&self, s: &State, v: &Rvalue, at: Point, span: Span) -> Marks {
        let b = self.cx.body;
        match v {
            Rvalue::Ref {
                origin: BorrowOrigin::LiteralView,
                ..
            } => Marks::from([(MarkOrigin::ConstLiteral(span), Via::Plain)]),
            Rvalue::Ref { place, .. } => {
                let mode = match self.md.exempt.contains(&at) {
                    true => Mode::Write(true),
                    false => Mode::Ref,
                };
                let mut m = self.place(s, *place, mode, span);
                if let Some(l) = b.meta.loops.iter().find(|l| l.bind == at) {
                    m.values_mut().for_each(|v| *v = Via::Loop(l.id));
                }
                m
            }
            Rvalue::Use(_) | Rvalue::Convert(..) | Rvalue::Aggregate(..) => {
                let mut m = Marks::new();
                for op in crate::init::operands(v) {
                    for (o, v) in self.operand(s, op, span) {
                        merge(&mut m, o, v);
                    }
                }
                m
            }
            _ => Marks::new(),
        }
    }

    /// The marks of a call's result (A:1009).
    fn call(&self, s: &State, callee: &Callee, args: &[Operand], at: Point, span: Span) -> Marks {
        let info = call_info(self.cx, callee, args);
        let mut m = Marks::new();
        if let (ResultPerm::ReadOnly(r), Some(def)) = (&info.result, callee_def(callee)) {
            let o = match r {
                Reason::StringPart => MarkOrigin::StringPart(def),
                Reason::Constant(_) | Reason::Static(_) | Reason::ConstLiteral => {
                    MarkOrigin::ConstPointing(def)
                }
                _ => MarkOrigin::ReadOnlyResult(def),
            };
            m.insert(o, Via::Plain);
        }
        if let RetSources::Params(src) = &info.sources {
            for &i in src {
                let Some(op) = info.args_map.get(i as usize).and_then(|&a| args.get(a)) else {
                    continue;
                };
                for (o, v) in self.operand(s, op, span) {
                    let v = match v {
                        Via::Loop(l) => Via::Loop(l),
                        _ => Via::Call(at),
                    };
                    merge(&mut m, o, v);
                }
                // A result reached from a class passed for an object type or a
                // fields-only interface may point into a `readonly` field the type
                // names, which the callee's body did not see (H42).
                let tcx = self.cx.tcx;
                if let Some(param) = callee_params(tcx, self.cx.body, callee)
                    .and_then(|ps| ps.get(i as usize).map(|p| p.0))
                    && let Some(o) = readonly_shape_field(
                        tcx,
                        param,
                        passed_ty(tcx, self.cx.body, at, op).unwrap_or(tcx.common().error),
                    )
                {
                    merge(&mut m, o, Via::Call(at));
                }
            }
        }
        m
    }

    fn set(&self, s: &mut State, dest: Place, m: Marks) {
        let ty = self.cx.body.locals[dest.local].ty;
        if !dest.is_local() {
            // A store into a part of a borrowing tuple held directly, a nullable
            // one's payload included, leaves the tuple holding what was stored,
            // as the literal `[&k, 0]` would (S:604, S:889): a later write through
            // the part reads it back. A store into a class's field takes no marks;
            // rule (e) checks its source at the store (A:1009).
            if !m.is_empty() && self.tuple_part(dest) {
                let into = s.entry(dest.local).or_default();
                for (o, v) in m {
                    merge(into, o, v);
                }
            }
            return;
        }
        match m.is_empty() || self.cx.tcx.is_value_type(ty) {
            true => s.remove(&dest.local),
            false => s.insert(dest.local, m),
        };
    }
}

impl Flow<'_, '_> {
    /// Whether `dest` is a part of a tuple local, reached through tuple parts and
    /// nullable payloads alone.
    fn tuple_part(&self, dest: Place) -> bool {
        let (tcx, b) = (self.cx.tcx, self.cx.body);
        let mut ty = PlaceTy::of(b.locals[dest.local].ty);
        for proj in b.projs(dest) {
            let ok = match (proj, tcx.kind(ty.ty)) {
                (Proj::Field(_) | Proj::ConstIndex(_), TyKind::Tuple(_)) => true,
                (Proj::Variant(_), TyKind::Nullable(_)) => true,
                (Proj::Field(_), TyKind::Nullable(_)) => ty.variant.is_some(),
                _ => false,
            };
            if !ok {
                return false;
            }
            let Some(next) = ty.project(tcx, *proj) else {
                return false;
            };
            ty = next;
        }
        true
    }
}

/// Whether hidden parameter `i` (a contract index) of local function `f` captures
/// a `const`: some call passes `&x [hidden-arg]` of a `const` `x`, or some
/// `closure(fn f, env(..))` (C12, c.16) holds `&x [closure-capture]` in that
/// argument's env field; or either passes `&*_j`, a hidden parameter of the
/// calling local function that does.
fn captures_const(cx: &BodyCx, f: DefId, i: u32, seen: &mut BTreeSet<(DefId, u32)>) -> bool {
    if !seen.insert((f, i)) {
        return false;
    }
    let tcx = cx.tcx;
    // Where `b` passes hidden argument `i` of `f`: the borrow's place, by origin.
    let passed = |b: &Body| -> Vec<Place> {
        let mut out = Vec::new();
        let borrowed = |op: Option<&Operand>, at: Point, want: BorrowOrigin| {
            let arg = op.and_then(Operand::place).filter(|p| p.is_local())?;
            match def_of(b, at, arg.local)? {
                (_, Rvalue::Ref { place, origin }) if *origin == want => Some(*place),
                _ => None,
            }
        };
        for (bb, block) in b.blocks.iter_enumerated() {
            if let TerminatorKind::Call {
                callee: Callee::Fn(g),
                args,
                ..
            } = &block.term.kind
                && g.def == f
            {
                let at = b.terminator_point(bb);
                out.extend(borrowed(args.get(i as usize), at, BorrowOrigin::HiddenArg));
            }
            for (idx, st) in block.stmts.iter().enumerate() {
                let StatementKind::Assign {
                    value:
                        Rvalue::ClosureValue {
                            func: enrang_mir::ClosureFn::Named(g),
                            env,
                        },
                    ..
                } = &st.kind
                else {
                    continue;
                };
                let at = Point::new(bb, idx);
                let Some(fb) = cx.bodies.get(&enrang_mir::BodyOwner::Fn(f)) else {
                    continue;
                };
                let k = crate::r3::hidden(tcx, f, fb).iter().position(|&h| h == i);
                if g.def != f || !env.is_local() {
                    continue;
                }
                if let (Some(k), Some((q, Rvalue::Aggregate(_, ops)))) =
                    (k, def_of(b, at, env.local))
                {
                    out.extend(borrowed(ops.get(k), q, BorrowOrigin::ClosureCapture));
                }
            }
        }
        out
    };
    for b in cx.bodies.values() {
        for place in passed(b) {
            let captured = match (b.projs(place), b.owner) {
                ([], _) => matches!(frozen(tcx, b, place.local), Some(MarkOrigin::ConstRoot(_))),
                ([Proj::Deref], enrang_mir::BodyOwner::Fn(caller)) => {
                    let j = place.local.0.wrapping_sub(1);
                    crate::r3::hidden(tcx, caller, b).contains(&j)
                        && captures_const(cx, caller, j, seen)
                }
                _ => false,
            };
            if captured {
                return true;
            }
        }
    }
    false
}

/// Whether env field `i` of arrow `a` of `top` captures a `const` path: the
/// `env(..)` its closure value is built from holds `&x [closure-capture]` of a
/// `const` local `x`, or of `*(*_1).j` of an enclosing arrow's field that does.
fn arrow_captures_const(
    cx: &BodyCx,
    top: enrang_hir::BodyOwner,
    a: enrang_hir::ArrowId,
    i: u32,
    seen: &mut BTreeSet<(enrang_hir::ArrowId, u32)>,
) -> bool {
    use enrang_mir::BodyOwner as O;
    if !seen.insert((a, i)) {
        return false;
    }
    let of_top = |o: &O| match (o, top) {
        (O::Arrow(t, _), _) => *t == top,
        (O::Fn(d), enrang_hir::BodyOwner::Fn(e)) => *d == e,
        (O::Test(d), enrang_hir::BodyOwner::Test(e)) => *d == e,
        (O::Statements(m), enrang_hir::BodyOwner::Statements(n)) => *m == n,
        _ => false,
    };
    for b in cx.bodies.values().filter(|b| of_top(&b.owner)) {
        for (bb, block) in b.blocks.iter_enumerated() {
            for (idx, st) in block.stmts.iter().enumerate() {
                let StatementKind::Assign {
                    value:
                        Rvalue::ClosureValue {
                            func: enrang_mir::ClosureFn::Arrow(x),
                            env,
                        },
                    ..
                } = &st.kind
                else {
                    continue;
                };
                let at = Point::new(bb, idx);
                if *x != a || !env.is_local() {
                    continue;
                }
                let Some((q, Rvalue::Aggregate(_, ops))) = def_of(b, at, env.local) else {
                    continue;
                };
                let Some(t) = ops.get(i as usize).and_then(Operand::place) else {
                    continue;
                };
                let Some((_, Rvalue::Ref { place, origin })) = def_of(b, q, t.local) else {
                    continue;
                };
                if *origin != BorrowOrigin::ClosureCapture {
                    continue;
                }
                let captured = match (b.projs(*place), b.owner) {
                    ([], _) => {
                        matches!(
                            frozen(cx.tcx, b, place.local),
                            Some(MarkOrigin::ConstRoot(_))
                        )
                    }
                    ([Proj::Deref, Proj::Field(j), Proj::Deref], O::Arrow(t2, outer))
                        if place.local == Local(1) =>
                    {
                        arrow_captures_const(cx, t2, outer, j.0, seen)
                    }
                    _ => false,
                };
                if captured {
                    return true;
                }
            }
        }
    }
    false
}

fn callee_def(c: &Callee) -> Option<DefId> {
    match c {
        Callee::Fn(f) | Callee::Virtual { method: f, .. } => Some(f.def),
        _ => None,
    }
}

impl DataflowAnalysis for Flow<'_, '_> {
    type Domain = State;
    const FORWARD: bool = true;

    fn bottom(&self, _b: &Body) -> State {
        State::new()
    }

    fn entry(&self, _b: &Body) -> State {
        let hidden = self.const_hidden.iter();
        hidden
            .map(|&l| (l, Marks::from([(MarkOrigin::ConstRoot(l), Via::Plain)])))
            .collect()
    }

    fn join(&self, into: &mut State, from: &State) -> bool {
        let mut changed = false;
        for (l, m) in from {
            let e = into.entry(*l).or_default();
            for (&o, &v) in m {
                changed |= merge(e, o, v);
            }
        }
        changed
    }

    fn statement(&self, s: &mut State, st: &Statement, at: Point) {
        match &st.kind {
            StatementKind::Assign { dest, value } => {
                let m = self.rvalue(s, value, at, st.span);
                self.set(s, *dest, m);
            }
            StatementKind::StorageLive(l) | StatementKind::StorageDead(l) => {
                s.remove(l);
            }
            StatementKind::Intrinsic { dest: Some(d), .. }
            | StatementKind::HostCall { dest: Some(d), .. } => self.set(s, *d, Marks::new()),
            _ => {}
        }
    }

    fn terminator(&self, s: &mut State, t: &Terminator, at: Point) {
        if let TerminatorKind::Call {
            callee, args, dest, ..
        } = &t.kind
        {
            let m = self.call(s, callee, args, at, t.span);
            self.set(s, *dest, m);
        }
    }

    fn edge(&self, s: &mut State, _from: BlockId, to: BlockId) {
        for l in self.cx.body.meta.loops.iter().filter(|l| l.preheader == to) {
            for v in s.values_mut().flat_map(|m| m.values_mut()) {
                if *v == Via::Loop(l.id) {
                    *v = Via::Plain;
                }
            }
        }
    }
}

impl MarkResults {
    /// Solves the marks of `cx.body`. The flows are the locals' own (plan d.3);
    /// `held` is not read yet (see the stage 2D report).
    pub fn run(cx: &BodyCx, _held: &HeldResults) -> MarkResults {
        let res = solve(cx.body, Flow::new(cx));
        let mut at = BTreeMap::new();
        res.visit(cx.body, |p, before, _| {
            at.insert(p, before.clone());
        });
        MarkResults { at }
    }

    pub fn marks_at(&self, p: Point, s: SlotId) -> BTreeMap<MarkOrigin, Option<LoopId>> {
        let SlotId::Local(l) = s else {
            return BTreeMap::new();
        };
        let m = self.at.get(&p).and_then(|st| st.get(&l));
        m.into_iter()
            .flatten()
            .map(|(&o, &v)| {
                let l = match v {
                    Via::Loop(l) => Some(l),
                    _ => None,
                };
                (o, l)
            })
            .collect()
    }
}

/// The loans that the marked arguments of `errors` make, each argument passed to
/// a parameter that writes and reported once (A:1270): a conflict of mode at such
/// a borrow, or with its loan, is a consequence of the same marked argument, whose
/// mark error is the one report, as `const e = &data[0]; new Grower(&data);` over
/// a `const data` is EN0608 alone (`FV-01-ctor`, `FV-05-nested`). A receiver is
/// no such argument.
/// Each loan is mapped to the index in `errors` of its marked argument's error.
pub fn marked_loans(cx: &BodyCx, errors: &[MarkError]) -> BTreeMap<crate::LoanId, usize> {
    let b = cx.body;
    let mut out = BTreeMap::new();
    for (k, e) in errors.iter().enumerate() {
        // A receiver's mark (EN0614) is no marked argument here: its borrow is the
        // method's, and a conflict of it stays a report of its own (T:667).
        let Some(i) = e.arg.filter(|_| e.code != Code::EN0614) else {
            continue;
        };
        let TerminatorKind::Call { args, .. } = &b.blocks[e.at.block].term.kind else {
            continue;
        };
        if b.stmt_at(e.at).is_some() {
            continue;
        }
        let Some(t) = args.get(i).and_then(|o| o.place()).filter(|p| p.is_local()) else {
            continue;
        };
        let Some((q, Rvalue::Ref { .. })) = def_of(b, e.at, t.local) else {
            continue;
        };
        out.extend(
            (cx.loans.table.iter_enumerated())
                .filter_map(|(id, l)| (l.site == q).then_some((id, k))),
        );
    }
    out
}

/// Every write through a marked slot of `cx.body`, one per report site: a
/// statement, a loop, or each marked argument of a call (SPEC 13: each phase
/// reports all its errors).
pub fn check(cx: &BodyCx, marks: &MarkResults) -> Vec<MarkError> {
    let b = cx.body;
    let mut out: BTreeMap<(Point, Option<usize>), MarkError> = BTreeMap::new();
    writes(cx, marks, |p, m, receiver, span, arg| {
        // A loop's report first (it is the only one), then a mark made here, then
        // one from a call's source argument.
        let rank = |v: &Via| match v {
            Via::Loop(_) => 0,
            Via::Plain => 1,
            Via::Call(_) => 2,
        };
        let Some((&o, &v)) = m
            .iter()
            .filter(|(o, _)| !matches!(o, MarkOrigin::ConstLiteral(_)))
            .min_by_key(|(o, v)| (rank(v), **o))
        else {
            return;
        };
        let (at, span) = match v {
            Via::Plain => (p, span),
            Via::Call(q) => (q, span_at(b, q)),
            Via::Loop(l) => {
                let l = b.meta.loops.iter().find(|x| x.id == l).expect("a loop");
                (Point::new(l.preheader, 0), l.span)
            }
        };
        let code = match receiver && v == Via::Plain {
            true => Code::EN0614,
            false => o.code(),
        };
        let arg = arg.filter(|_| v == Via::Plain);
        out.entry((at, arg)).or_insert(MarkError {
            code,
            origin: o,
            at,
            span,
            arg,
        });
    });
    out.into_values().collect()
}

/// Calls `f` with the marks of every write through a slot, every slot passed to
/// a Write parameter (with whether it is a Write `this`) and every value a
/// statement stores into a class that writes through its fields (rule (e)), its
/// span, and for a call's argument its index among the call's arguments. A call
/// that stores an argument into such a value is covered by its Write parameter
/// (A:1359: rule (e) makes the callee's own parameter Write; `D20-core-4`).
fn writes(
    cx: &BodyCx,
    marks: &MarkResults,
    mut f: impl FnMut(Point, Marks, bool, Span, Option<usize>),
) {
    let (tcx, b) = (cx.tcx, cx.body);
    let flow = Flow::new(cx);
    let md = flow.md;
    let init = crate::init::InitResults::compute(b, md);
    let empty = State::new();
    let mut uninit: BTreeMap<Point, BitSet<MovePathIdx>> = BTreeMap::new();
    init.replay(b, &md, |p, _, u| {
        uninit.insert(p, u.clone());
    });
    for (bb, block) in b.blocks.iter_enumerated() {
        for idx in 0..=block.stmts.len() {
            let p = Point::new(bb, idx);
            let s = marks.at.get(&p).unwrap_or(&empty);
            let span = span_at(b, p);
            let stmt = b.stmt_at(p).map(|s| &s.kind);
            for d in point_dests(b, p) {
                if d.is_local() || matches!(stmt, Some(StatementKind::FieldInit { .. })) {
                    continue;
                }
                let initialising = unset(&md, &uninit[&p], md.lookup[&d].0, false).is_some();
                f(
                    p,
                    flow.place(s, d, Mode::Write(initialising), span),
                    false,
                    span,
                    None,
                );
                if let Some(StatementKind::Assign { value, .. }) = stmt
                    && let Some(Proj::Field(field)) = b.projs(d).last()
                    && base_ty(tcx, b, d).is_some_and(|t| writes_through(tcx, t, Some(*field)))
                {
                    for op in crate::init::operands(value) {
                        f(p, flow.operand(s, op, span), false, span, None);
                    }
                }
                // A reference stored into a part of a tuple reached through a
                // reference to it, `p[0] = &k` with `p = &t`: the tuple's own marks
                // can't follow, since the store names no local of this body that
                // holds them, so the source is checked at the store, as rule (e)
                // checks one stored into a class that writes through its fields.
                if let Some(StatementKind::Assign { value, .. }) = stmt
                    && through_ref_tuple_part(tcx, b, d)
                {
                    f(p, flow.rvalue(s, value, p, span), false, span, None);
                }
            }
            let TerminatorKind::Call { callee, args, .. } = &block.term.kind else {
                continue;
            };
            if stmt.is_some() {
                continue;
            }
            let info = call_info(cx, callee, args);
            let this = callee_def(callee).is_some_and(|d| tcx.takes_this(d));
            let index = |i: u32| info.args_map.get(i as usize).copied();
            let arg = |i: u32| index(i).and_then(|a| args.get(a));
            // `perms` holds one permission per `&` parameter, `this` first, then
            // one per reference part of each by-value borrowing tuple parameter
            // (A:311-313), so each is mapped to its argument, and a part to the
            // operand that built it when the tuple is a literal here.
            let tys: Vec<enrang_hir::Ty> = (0..info.args_map.len() as u32)
                .map(|i| {
                    arg(i)
                        .and_then(|op| match op {
                            Operand::Copy(pl) | Operand::Move(pl) => {
                                b.place_ty(tcx, *pl).map(|t| t.ty)
                            }
                            Operand::Const(c) => Some(c.ty),
                        })
                        .unwrap_or(tcx.common().error)
                })
                .collect();
            let slots = crate::declared::perm_slots(tcx, &tys);
            for ((i, path), perm) in slots.iter().zip(info.perms.iter()) {
                let i = *i as u32;
                let Some(op) = arg(i).filter(|_| *perm == enrang_hir::Perm::Write) else {
                    continue;
                };
                if !path.is_empty() {
                    let (state, part, at) = match tuple_part(b, p, op, path) {
                        Some((q, part)) => (marks.at.get(&q).unwrap_or(&empty), part, q),
                        None => (s, op, p),
                    };
                    let at_arg = part
                        .place()
                        .and_then(|pl| def_of(b, at, pl.local))
                        .map_or(span_at(b, at), |(q, _)| span_at(b, q));
                    f(p, flow.operand(state, part, span), false, at_arg, index(i));
                    continue;
                }
                let receiver = i == 0 && this;
                // A local function's hidden argument: the callee reports a
                // `const` written through it at the write.
                let hidden_arg = op
                    .place()
                    .and_then(|pl| def_of(b, p, pl.local))
                    .is_some_and(|(_, v)| {
                        matches!(
                            v,
                            Rvalue::Ref {
                                origin: BorrowOrigin::HiddenArg,
                                ..
                            }
                        )
                    });
                if hidden_arg {
                    continue;
                }
                let at_arg = op
                    .place()
                    .and_then(|pl| def_of(b, p, pl.local))
                    .filter(|_| !receiver)
                    .map_or(span, |(q, _)| span_at(b, q));
                f(p, flow.operand(s, op, span), receiver, at_arg, index(i));
            }
            // A class passed for an object type or a fields-only interface (C20)
            // to a parameter the callee may write: its body is checked once for
            // the shape, which has no `readonly` field (H42, S:774). A function, a
            // method, an `fn` value or a closure, by their parameter types.
            let Some(params) = callee_params(tcx, b, callee) else {
                continue;
            };
            for (i, op) in (0..info.args_map.len() as u32).filter_map(|i| Some((i, arg(i)?))) {
                let Some(&(param, mark)) = params.get(i as usize) else {
                    continue;
                };
                let writable = match tcx.kind(strip_null(tcx, param)) {
                    TyKind::Ref(_) => {
                        crate::declared::perm_of(&slots, &info.perms, i as usize)
                            == Some(enrang_hir::Perm::Write)
                    }
                    _ => mark == Mark::Let,
                };
                let passed = passed_ty(tcx, b, p, op).unwrap_or(tys[i as usize]);
                let Some(m) = writable
                    .then(|| readonly_shape_field(tcx, param, passed))
                    .flatten()
                else {
                    continue;
                };
                let at_arg = op
                    .place()
                    .and_then(|pl| def_of(b, p, pl.local))
                    .map_or(span, |(q, _)| span_at(b, q));
                f(p, Marks::from([(m, Via::Plain)]), false, at_arg, index(i));
            }
        }
    }
}

/// The parameter types and marks of what `callee` calls, by contract index:
/// `this` first for a method (its type left out), then its parameters; an `fn`
/// value's or a closure's from its type.
fn callee_params(tcx: &Tcx, b: &Body, callee: &Callee) -> Option<Vec<(enrang_hir::Ty, Mark)>> {
    match callee {
        Callee::Fn(f) | Callee::Virtual { method: f, .. } => {
            let sig = tcx.sig_opt(f.def)?;
            let receiver = tcx
                .takes_this(f.def)
                .then_some((tcx.common().error, Mark::None));
            Some(
                (receiver.into_iter())
                    .chain(sig.params.iter().map(|p| (p.ty, p.mark)))
                    .collect(),
            )
        }
        Callee::FnPtr(op) => Some(fn_params(tcx, op_ty(tcx, b, op))),
        Callee::ClosureLocal(l) => Some(fn_params(tcx, Some(b.locals[*l].ty))),
        _ => None,
    }
}

/// The type of the value argument `op` passes at `p`: an argument made `T | null`
/// for a nullable parameter is the value `present` wraps.
fn passed_ty(tcx: &Tcx, b: &Body, p: Point, op: &Operand) -> Option<enrang_hir::Ty> {
    let wrapped = op
        .place()
        .filter(|pl| pl.is_local())
        .and_then(|pl| def_of(b, p, pl.local))
        .and_then(|(_, v)| match v {
            Rvalue::Aggregate(AggregateKind::Present, ops) => ops.first(),
            _ => None,
        });
    op_ty(tcx, b, wrapped.unwrap_or(op))
}

/// `t` without one `| null` at its top.
fn strip_null(tcx: &Tcx, t: enrang_hir::Ty) -> enrang_hir::Ty {
    match tcx.kind(t) {
        TyKind::Nullable(inner) => inner,
        _ => t,
    }
}

/// The type of operand `op`.
fn op_ty(tcx: &Tcx, b: &Body, op: &Operand) -> Option<enrang_hir::Ty> {
    match op {
        Operand::Copy(pl) | Operand::Move(pl) => b.place_ty(tcx, *pl).map(|t| t.ty),
        Operand::Const(c) => Some(c.ty),
    }
}

/// The parameters of an `fn` or closure type, through one `| null`.
fn fn_params(tcx: &Tcx, t: Option<enrang_hir::Ty>) -> Vec<(enrang_hir::Ty, Mark)> {
    match t.map(|t| tcx.kind(strip_null(tcx, t))) {
        Some(TyKind::FnPtr(_, s) | TyKind::Closure(s)) => tcx.fn_sig(s).params.clone(),
        _ => Vec::new(),
    }
}

/// The first `readonly` field of the class `arg` that the object type or
/// fields-only interface of `param` names, each looked at through one `&` and one
/// `| null`.
fn readonly_shape_field(
    tcx: &Tcx,
    param: enrang_hir::Ty,
    arg: enrang_hir::Ty,
) -> Option<MarkOrigin> {
    let strip = |t: enrang_hir::Ty| match tcx.kind(strip_null(tcx, t)) {
        TyKind::Ref(p) => strip_null(tcx, p),
        _ => strip_null(tcx, t),
    };
    let shape = match tcx.kind(strip(param)) {
        TyKind::Param(pid) => match tcx.param(pid).implicit {
            Some(enrang_hir::Implicit::Shape(shape)) => shape,
            _ => return None,
        },
        TyKind::Object(shape) => shape,
        _ => return None,
    };
    let TyKind::Adt(adt, _) = tcx.kind(strip(arg)) else {
        return None;
    };
    let enrang_hir::AdtKind::Class(class) = &tcx.adt(adt).kind else {
        return None;
    };
    tcx.shape(shape).fields.iter().find_map(|(name, _)| {
        let (f, fd) = class.field_named(*name)?;
        fd.readonly.then_some(MarkOrigin::ReadonlyField(adt, f))
    })
}

/// The operand that built part `path` of the tuple `op` passed at `p`, with the
/// point of the literal that holds it, when each tuple on the way is a literal of
/// this block; otherwise `None`, and the whole tuple's marks stand for the part.
fn tuple_part<'b>(
    b: &'b Body,
    p: Point,
    op: &'b Operand,
    path: &[u32],
) -> Option<(Point, &'b Operand)> {
    let (mut at, mut cur) = (p, op);
    for &k in path {
        let pl = cur.place().filter(|pl| pl.is_local())?;
        let (q, value) = def_of(b, at, pl.local)?;
        let Rvalue::Aggregate(AggregateKind::Tuple, ops) = value else {
            return None;
        };
        (at, cur) = (q, ops.get(k as usize)?);
    }
    Some((at, cur))
}

/// Whether `p` is a reference part of a tuple reached through a reference: one a
/// reference local points at, `(*_p).0` with `_p: &[&i64[], i32]`, or a tuple
/// field's part, `(*_1).t.0`, of a class that writes through its reference fields
/// (rule (e)), a part declared `readonly` excepted.
fn through_ref_tuple_part(tcx: &Tcx, b: &Body, p: Place) -> bool {
    let projs = b.projs(p);
    if !projs.contains(&Proj::Deref)
        || !matches!(projs.last(), Some(Proj::Field(_) | Proj::ConstIndex(_)))
    {
        return false;
    }
    let mut ty = PlaceTy::of(b.locals[p.local].ty);
    // The class field last crossed, with the tuple path under it.
    let mut field: Option<(AdtId, FieldIdx, Vec<u32>)> = None;
    let mut last_on_tuple = false;
    for q in projs {
        last_on_tuple = false;
        match (q, tcx.kind(ty.ty)) {
            (Proj::Field(f), TyKind::Adt(adt, _)) if ty.variant.is_none() => {
                field = Some((adt, *f, Vec::new()));
            }
            (Proj::Field(FieldIdx(i)), TyKind::Tuple(_)) => {
                field.iter_mut().for_each(|x| x.2.push(*i));
                last_on_tuple = true;
            }
            (Proj::ConstIndex(i), TyKind::Tuple(_)) => {
                field.iter_mut().for_each(|x| x.2.push(*i as u32));
                last_on_tuple = true;
            }
            (Proj::Deref, _) => field = None,
            _ => {}
        }
        let Some(next) = ty.project(tcx, *q) else {
            return false;
        };
        ty = next;
    }
    if !last_on_tuple || !crate::slots::ref_carrying(tcx, ty.ty) {
        return false;
    }
    match field {
        None => true,
        Some((adt, f, path)) => {
            tcx.adt(adt).is_class()
                && crate::class_contract(tcx, adt).writes_through_fields
                && !tcx.field_def(adt, None, f).readonly_refs.contains(&path)
        }
    }
}

/// The type of `p` without its last projection.
fn base_ty(tcx: &Tcx, b: &Body, p: Place) -> Option<enrang_hir::Ty> {
    let projs = b.projs(p);
    let start = PlaceTy::of(b.locals[p.local].ty);
    let base = projs[..projs.len() - 1]
        .iter()
        .try_fold(start, |t, q| t.project(tcx, *q));
    base.map(|t| t.ty)
}

/// Whether `ty` is a borrowing class that writes through its reference fields
/// and, for field `f`, `f` is not declared `readonly &` (rule (e)).
fn writes_through(tcx: &Tcx, ty: enrang_hir::Ty, f: Option<FieldIdx>) -> bool {
    let TyKind::Adt(adt, _) = tcx.kind(ty) else {
        return false;
    };
    tcx.is_borrowing_class(adt)
        && crate::class_contract(tcx, adt).writes_through_fields
        && f.is_none_or(|f| {
            !tcx.field_def(adt, None, f)
                .readonly_refs
                .contains(&Vec::new())
        })
}
