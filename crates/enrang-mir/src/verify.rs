//! The MIR verifier (A:580-582; M3 plan b.7, rules V01-V18).
//!
//! It runs in tests after every pass and in the driver after mirbuild and after
//! elaboration; a failure on compiler-built MIR is an internal error. The `Built`
//! guards (V12-V14) hold only in `Built` MIR, which interface files store. Errors
//! come back in point order, each naming the one rule it breaks. A:584's reruns of
//! phase-2 rules on stored bodies, and EN0316, are M4's read path.

use std::fmt;

use enrang_base::{BitSet, Idx};
use enrang_hir::{
    AdtKind, Bound, CastKind, ClassModifier, ConstValue, ConvKind, DefId, DefKind, FieldIdx, IntTy,
    LangItem, ParamId, Receiver, Tcx, Ty, TyKind, Vis,
};

use crate::body::{
    AggregateKind, BinOp, Body, BodyOwner, BorrowOrigin, Callee, CheckedOp, ClassHolder, ClassOp,
    ClosureFn, ConstKind, DropOrigin, FormCall, LocalKind, MirPhase, Operand, Place, Proj, Rvalue,
    ShimKind, Statement, StatementKind, Terminator, TerminatorKind,
};
use crate::cfg::Cfg;
use crate::dataflow::{DataflowAnalysis, GenKill, GenKillAnalysis, solve};
use crate::ids::{BlockId, Local, Point};
use crate::proj::{PlaceTy, places, statement_places, terminator_places, variant_count};

/// The verifier's rules (plan b.7).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Rule {
    /// V01: `_0` the return slot, `_1.._arg_count` the arguments, every local used
    /// declared.
    LocalOnce,
    /// V02: types agree.
    Types,
    /// V03: `HostCall` only in `os/vm`.
    HostCallPlace,
    /// V04: `SetTable` on a class with a hidden pointer, in a `DropGlue` or
    /// `NamedFill` shim or as the first write to the object a `new` builds.
    SetTable,
    /// V05: regions nest and exist.
    Regions,
    /// V06: `Drop` only when `Built`, `DropGlue` never then.
    NoDropAfterElab,
    /// V07: no `Param` or `Infer` after mono.
    NoParams,
    /// V08: every check in a run that ends directly before its use; only the
    /// compare, the `Switch` and `StorageLive(x)` between a `for...of` head's `Len`
    /// and its `CheckBounds`.
    CheckRuns,
    /// V09: no `Move` of a reference but from a `Temp`, and no operand carrying
    /// loans that is a field or part, but in a `Use`.
    MoveRef,
    /// V10: every `Convert` between the pairs its kind allows.
    ConvertPairs,
    /// V11: `FieldInit` placement.
    FieldInit,
    /// V12: a `CheckBounds` and a `Len` before every index.
    GuardBounds,
    /// V13: a `CheckTag` before every case projection.
    GuardTag,
    /// V14: a `CheckClass` before every exact-class event.
    GuardClass,
    /// V15: an unsafe intrinsic inside a region.
    UnsafeIntrinsic,
    /// V16: a virtual call only where a table can be read, of a method with a slot,
    /// the table read from the receiver.
    Virtual,
    /// V17: blocks in range, distinct switch values, `next` unless `never`.
    Cfg,
    /// V18: `PhaseMeta` names real blocks, points and statements.
    Meta,
}

/// One broken rule, where, and why.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifyError {
    pub rule: Rule,
    pub at: Option<Point>,
    pub message: String,
}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.at {
            Some(p) => write!(f, "{:?} at {p}: {}", self.rule, self.message),
            None => write!(f, "{:?}: {}", self.rule, self.message),
        }
    }
}

/// Checks `b` against every rule (plan b.7).
pub fn verify(tcx: &Tcx, b: &Body) -> Result<(), Vec<VerifyError>> {
    let mut v = Verifier {
        tcx,
        b,
        errors: Vec::new(),
    };
    v.cfg();
    v.locals();
    if v.errors.is_empty() {
        v.regions();
        v.meta();
        v.statements();
        v.set_tables();
        v.forof_heads();
        v.field_inits();
    }
    if v.errors.is_empty() {
        return Ok(());
    }
    let mut errors = v.errors;
    errors.sort_by_key(|e| (e.at, e.rule));
    errors.dedup();
    Err(errors)
}

/// A call's parameter types, the receiver first, and its return type, as the
/// verifier types them: type arguments substituted, an interface member's `Self`
/// the receiver's pointee, and a callee with a defaulted parameter cut to the
/// arguments supplied (A:937); `None` where they are not known.
pub fn callee_types(
    tcx: &Tcx,
    b: &Body,
    callee: &Callee,
    args: &[Operand],
) -> (Option<Vec<Ty>>, Option<Ty>) {
    let v = Verifier {
        tcx,
        b,
        errors: Vec::new(),
    };
    let (mut params, ret) = v.callee_sig(callee, args);
    if let (Some(params), Callee::Fn(f) | Callee::Virtual { method: f, .. }) = (&mut params, callee)
        && let Some(s) = tcx.sig_opt(f.def)
        && s.params.iter().any(|p| p.has_default)
        && let Some(Operand::Const(c)) = args.last()
        && let ConstKind::Value(ConstValue::Int(n, _)) = c.kind
    {
        params.truncate(usize::from(tcx.takes_this(f.def)) + n as usize);
    }
    (params, ret)
}

struct Verifier<'a> {
    tcx: &'a Tcx,
    b: &'a Body,
    errors: Vec<VerifyError>,
}

/// Whether `st` is one of the three guards a run holds.
fn is_check(st: &Statement) -> bool {
    matches!(
        st.kind,
        StatementKind::CheckBounds { .. }
            | StatementKind::CheckTag { .. }
            | StatementKind::CheckClass { .. }
    )
}

impl<'a> Verifier<'a> {
    fn error(&mut self, rule: Rule, at: Option<Point>, message: impl Into<String>) {
        self.errors.push(VerifyError {
            rule,
            at,
            message: message.into(),
        });
    }

    fn ty_str(&self, t: Ty) -> String {
        self.tcx.ty_string(t)
    }

    /// Whether a value of `from` may stand where `to` is declared.
    fn fits(&self, from: Ty, to: Ty) -> bool {
        from == to
            || self.tcx.same_ignoring_rows(from, to)
            || self.tcx.kind(from) == TyKind::Never
            || self.tcx.references_error(from)
            || self.tcx.references_error(to)
            || self.bounded(from, to)
            || self.safe_to_unsafe(from, to)
    }

    /// A safe `fn` value where an `unsafe fn` of the same parameters and result
    /// is expected (C15, `Adjust::FnToUnsafePtr` on a value that is no function
    /// name): the same pointer, callable only in more places.
    fn safe_to_unsafe(&self, from: Ty, to: Ty) -> bool {
        let tcx = self.tcx;
        let (TyKind::FnPtr(a, x), TyKind::FnPtr(b, y)) = (tcx.kind(from), tcx.kind(to)) else {
            return false;
        };
        let (x, y) = (tcx.fn_sig(x), tcx.fn_sig(y));
        a == b
            && !x.unsafety
            && y.unsafety
            && x.params.len() == y.params.len()
            && (x.params.iter().zip(&y.params))
                .all(|((s, _), (t, _))| tcx.same_ignoring_rows(*s, *t))
            && tcx.same_ignoring_rows(x.ret, y.ret)
    }

    /// C20: an object, or a class by its public fields, where an object type with
    /// a subset of its fields is expected, at a parameter or a reference, which
    /// stands for the shape passed as a type parameter does (SPEC 4.3, A:609).
    fn has_shape(&self, from: Ty, shape: enrang_hir::ShapeId) -> bool {
        let tcx = self.tcx;
        let want = tcx.shape(shape);
        match tcx.kind(from) {
            TyKind::Object(have) => {
                let have = tcx.shape(have);
                want.fields.iter().all(|(n, t)| {
                    (have.fields.iter()).any(|(m, s)| m == n && tcx.same_ignoring_rows(*s, *t))
                })
            }
            TyKind::Adt(adt, args) => {
                let Some(class) = tcx.adt(adt).as_class() else {
                    return false;
                };
                want.fields.iter().all(|(n, t)| {
                    class.fields.iter().enumerate().any(|(i, f)| {
                        f.name == *n
                            && f.vis == enrang_hir::Vis::Public
                            && tcx.same_ignoring_rows(
                                tcx.field_ty(adt, None, enrang_hir::FieldIdx::new(i), args),
                                *t,
                            )
                    })
                })
            }
            _ => false,
        }
    }

    /// A type parameter stands for the type mono picks: a callee's own one the call
    /// leaves uninstantiated (an implicit one, D5, included) takes any argument; an
    /// argument fits an interface it satisfies; a parameter fits one of its
    /// bounds, or a base of a bounding class.
    fn bounded(&self, from: Ty, to: Ty) -> bool {
        let tcx = self.tcx;
        match (tcx.kind(from), tcx.kind(to)) {
            (TyKind::Ref(x), TyKind::Ref(y)) => self.bounded(x, y),
            (_, TyKind::Param(p)) => !self.in_scope(p),
            (_, TyKind::Object(s)) if from != to => self.has_shape(from, s),
            (_, TyKind::Adt(i, _)) if tcx.adt(i).is_interface() => {
                self.convert_ok(ConvKind::BoxToInterface, tcx.mk_box(from), tcx.mk_box(to))
            }
            (TyKind::Param(p), _) => tcx.param(p).bounds.iter().any(|&b| {
                let (Bound::Iface { adt, args } | Bound::Class { adt, args }) = *tcx.bound(b);
                let mut cur = Some((adt, args));
                while let Some((a, l)) = cur {
                    if tcx.mk_adt(a, &tcx.list(l)) == to {
                        return true;
                    }
                    cur = tcx.base_of(a, l);
                }
                false
            }),
            _ => false,
        }
    }

    /// Whether `p` is a type parameter of the body's owner (its class's included).
    fn in_scope(&self, p: ParamId) -> bool {
        let def = match self.b.owner {
            BodyOwner::Fn(d) | BodyOwner::Test(d) => Some(d),
            BodyOwner::Arrow(enrang_hir::BodyOwner::Fn(d), _) => Some(d),
            _ => None,
        };
        def.and_then(|d| self.tcx.sig_opt(d))
            .is_some_and(|s| self.tcx.all_params(s.generics).contains(&p))
    }

    /// A float, or a type an earlier error left unknown.
    fn float_or_error(&self, t: Ty) -> bool {
        matches!(self.tcx.kind(t), TyKind::Float(_)) || self.tcx.references_error(t)
    }

    /// V02 on C12's closure of an `fn` value: the env holds one `fn` value whose
    /// parameters and result are the closure's.
    fn fn_value_env(&self, env: Place, closure: enrang_hir::FnSigId) -> Result<(), String> {
        let tcx = self.tcx;
        let Some(et) = self.place_ty(env) else {
            return Ok(());
        };
        let field = match tcx.kind(et) {
            TyKind::Tuple(l) => match &tcx.list(l)[..] {
                [t] => Some(*t),
                _ => None,
            },
            _ => None,
        };
        let (want, got) = match field.map(|t| tcx.kind(t)) {
            Some(TyKind::FnPtr(_, s)) => (tcx.fn_sig(closure), tcx.fn_sig(s)),
            _ => return Err(format!("`{}` holds no `fn` value", self.ty_str(et))),
        };
        let same = |a: Ty, b: Ty| self.fits(a, b) && self.fits(b, a);
        let params = want.params.len() == got.params.len()
            && (want.params.iter().zip(&got.params)).all(|(a, b)| same(a.0, b.0));
        match params && same(want.ret, got.ret) {
            true => Ok(()),
            false => Err(format!("`{}` is not the closure's `fn`", self.ty_str(et))),
        }
    }

    fn int_or_error(&self, t: Ty) -> bool {
        matches!(self.tcx.kind(t), TyKind::Int(_)) || self.tcx.references_error(t)
    }

    /// V02: a shift's value and amount are both integers (b.4).
    fn shifted(&self, a: Ty, c: Ty) -> String {
        format!("`{}` is shifted by `{}`", self.ty_str(a), self.ty_str(c))
    }

    /// V02 on a form's arguments (D19): the text forms take one `&string`
    /// (`FailureMove` one `string`); the others but `IntoFailure` and `Expect`
    /// take shared borrows and `&string` constants, so only references.
    fn form_args(&self, fc: FormCall, args: &[Operand]) -> Option<String> {
        let tcx = self.tcx;
        let text = tcx.common().str;
        let tys: Vec<Ty> = args.iter().filter_map(|a| self.operand_ty(a)).collect();
        let one = |want: Ty| match tys.as_slice() {
            [t] if self.fits(*t, want) => None,
            _ => Some(format!("needs one `{}`", self.ty_str(want))),
        };
        match fc {
            FormCall::FailureText | FormCall::FailureCopy => one(tcx.mk_ref(text)),
            FormCall::FailureMove => one(text),
            FormCall::IntoFailure | FormCall::Expect { .. } => None,
            _ => tys
                .iter()
                .find(|t| !matches!(tcx.kind(**t), TyKind::Ref(_) | TyKind::Error))
                .map(|t| format!("takes `{}`, no reference", self.ty_str(*t))),
        }
    }

    fn place_ty(&self, p: Place) -> Option<Ty> {
        self.b.place_ty(self.tcx, p).map(|t| t.ty)
    }

    fn operand_ty(&self, op: &Operand) -> Option<Ty> {
        match op {
            Operand::Copy(p) | Operand::Move(p) => self.place_ty(*p),
            Operand::Const(c) => Some(c.ty),
        }
    }

    /// The module of the body's owner.
    fn module(&self) -> Option<enrang_hir::ModuleId> {
        let of = |o: enrang_hir::BodyOwner| match o {
            enrang_hir::BodyOwner::Fn(d)
            | enrang_hir::BodyOwner::Const(d)
            | enrang_hir::BodyOwner::Test(d) => self.tcx.def(d).module,
            enrang_hir::BodyOwner::Statements(m) => m,
        };
        match self.b.owner {
            BodyOwner::Fn(d) | BodyOwner::Test(d) => Some(self.tcx.def(d).module),
            BodyOwner::Statements(m) => Some(m),
            BodyOwner::Arrow(o, _) => Some(of(o)),
            BodyOwner::Shim(_) => None,
        }
    }

    // -----------------------------------------------------------------------------
    // V17, V01, V05, V18.

    fn cfg(&mut self) {
        let n = self.b.blocks.len();
        if n == 0 {
            self.error(Rule::Cfg, None, "a body has at least one block");
            return;
        }
        for (id, block) in self.b.blocks.iter_enumerated() {
            let at = Some(self.b.terminator_point(id));
            for s in block.term.kind.successors() {
                if s.index() >= n {
                    self.error(Rule::Cfg, at, format!("{s} is out of range"));
                }
            }
            match &block.term.kind {
                TerminatorKind::Switch { arms, .. } => {
                    let mut values: Vec<u128> = arms.iter().map(|(v, _)| *v).collect();
                    values.sort();
                    if values.windows(2).any(|w| w[0] == w[1]) {
                        self.error(Rule::Cfg, at, "a switch value appears twice");
                    }
                }
                TerminatorKind::Call {
                    callee, next, args, ..
                } => {
                    let never = self
                        .callee_sig(callee, args)
                        .1
                        .is_some_and(|t| self.tcx.kind(t) == TyKind::Never);
                    if next.is_none() && !never && callee.form().is_none() {
                        self.error(
                            Rule::Cfg,
                            at,
                            "a call with no next block must return `never`",
                        );
                    }
                }
                _ => {}
            }
        }
    }

    fn locals(&mut self) {
        let b = self.b;
        let count = b.locals.len();
        if count == 0 || b.locals[Local::RETURN].kind != LocalKind::Return {
            self.error(Rule::LocalOnce, None, "_0 is the return slot");
        }
        if b.arg_count as usize >= count.max(1) {
            self.error(Rule::LocalOnce, None, "more arguments than locals");
            return;
        }
        if b.phase == MirPhase::Mono {
            for (l, decl) in b.locals.iter_enumerated() {
                if self.tcx.has_params(decl.ty) || self.tcx.has_infer(decl.ty) {
                    self.error(
                        Rule::NoParams,
                        None,
                        format!("{l} has a type parameter after mono"),
                    );
                }
            }
        }
        for (l, decl) in b.locals.iter_enumerated() {
            let arg = (1..=b.arg_count).contains(&l.0);
            let env = matches!(b.owner, BodyOwner::Arrow(..)) && l == Local(1);
            let ok = match decl.kind {
                LocalKind::Return => l == Local::RETURN,
                LocalKind::Arg => arg,
                LocalKind::ClosureEnv => env && arg,
                _ => !arg && l != Local::RETURN,
            };
            if !ok {
                self.error(
                    Rule::LocalOnce,
                    None,
                    format!("{l} has the kind {:?}", decl.kind),
                );
            }
        }
        let mut used: Vec<(Option<Point>, Local)> = Vec::new();
        for (block_id, block) in b.blocks.iter_enumerated() {
            for (i, st) in block.stmts.iter().enumerate() {
                if let StatementKind::StorageLive(l) | StatementKind::StorageDead(l) = st.kind {
                    used.push((Some(Point::new(block_id, i)), l));
                }
            }
            if let TerminatorKind::Call {
                callee: Callee::ClosureLocal(l),
                ..
            } = block.term.kind
            {
                used.push((Some(b.terminator_point(block_id)), l));
            }
        }
        for (at, p) in places(b) {
            used.push((at, p.local));
            for proj in b.projs(p) {
                if let Proj::Index(l) = proj {
                    used.push((at, *l));
                }
            }
        }
        for l in &b.meta.loops {
            used.push((None, l.binding));
        }
        for r in &b.meta.records {
            used.push((Some(r.at), r.slot));
        }
        for f in b.meta.facts.iter() {
            used.push((None, f.root));
        }
        used.extend(b.meta.defaults_count.map(|l| (None, l)));
        used.extend(
            b.drop_flags
                .iter()
                .flat_map(|(f, k)| [(None, *f), (None, k.local)]),
        );
        for (at, l) in used {
            if l.index() >= count {
                self.error(Rule::LocalOnce, at, format!("{l} is not declared"));
            }
        }
    }

    fn regions(&mut self) {
        let b = self.b;
        for (r, region) in b.unsafe_regions.iter_enumerated() {
            if let Some(parent) = region.parent {
                match b.unsafe_regions.get(parent) {
                    Some(p) if parent < r => {
                        if !p.span.is_dummy()
                            && !region.span.is_dummy()
                            && (region.span.lo < p.span.lo || region.span.hi > p.span.hi)
                        {
                            self.error(Rule::Regions, None, format!("{r} lies outside {parent}"));
                        }
                    }
                    _ => self.error(
                        Rule::Regions,
                        None,
                        format!("{r}'s parent {parent} does not exist"),
                    ),
                }
            }
        }
        for (id, block) in b.blocks.iter_enumerated() {
            let regions = block
                .stmts
                .iter()
                .enumerate()
                .map(|(i, s)| (Point::new(id, i), s.region))
                .chain([(b.terminator_point(id), block.term.region)]);
            for (at, region) in regions {
                if let Some(r) = region
                    && r.index() >= b.unsafe_regions.len()
                {
                    self.error(Rule::Regions, Some(at), format!("{r} does not exist"));
                }
            }
        }
    }

    fn point_ok(&self, p: Point) -> bool {
        p.block.index() < self.b.blocks.len()
            && p.index as usize <= self.b.blocks[p.block].stmts.len()
    }

    fn meta(&mut self) {
        let b = self.b;
        let n = b.blocks.len();
        for l in &b.meta.loops {
            let bind_ok = self.point_ok(l.bind)
                && matches!(
                    b.stmt_at(l.bind).map(|s| &s.kind),
                    Some(StatementKind::Assign {
                        value: Rvalue::Ref {
                            origin: BorrowOrigin::ForOfElement,
                            ..
                        },
                        ..
                    })
                );
            if l.preheader.index() >= n || l.head.index() >= n || !bind_ok {
                self.error(
                    Rule::Meta,
                    None,
                    format!(
                        "loop l{}: its bind is no `for-of-element` borrow, or a block is missing",
                        l.id.0
                    ),
                );
            }
        }
        let facts = b.meta.facts.len();
        let mut points: Vec<(Point, u32)> =
            b.meta.records.iter().map(|r| (r.at, r.fact.0)).collect();
        points.extend(b.meta.narrowed_uses.iter().map(|(f, p)| (*p, f.0)));
        for (p, f) in points {
            if !self.point_ok(p) || f as usize >= facts {
                self.error(
                    Rule::Meta,
                    None,
                    format!("a record or use of f{f} at {p} names nothing"),
                );
            }
        }
        for (f, bb) in &b.meta.fact_tests {
            if bb.index() >= n || f.index() >= facts {
                self.error(
                    Rule::Meta,
                    None,
                    format!("the test of f{} names nothing", f.0),
                );
            }
        }
        for &p in &b.meta.assign_values {
            let is_move = matches!(
                b.stmt_at(p).map(|s| &s.kind),
                Some(StatementKind::Assign {
                    value: Rvalue::Use(Operand::Move(_)),
                    ..
                })
            );
            if !self.point_ok(p) || !is_move {
                self.error(Rule::Meta, Some(p), "an assignment's value is no `move`");
            }
        }
    }

    // -----------------------------------------------------------------------------
    // Statements and terminators.

    fn statements(&mut self) {
        let b = self.b;
        for (at, p) in places(b) {
            if b.place_ty(self.tcx, p).is_none() {
                self.error(Rule::Types, at, "a projection does not fit its base");
                continue;
            }
            for proj in b.projs(p) {
                if let Proj::Index(l) = proj
                    && self.tcx.kind(b.locals[*l].ty) != TyKind::Int(IntTy::Isize)
                {
                    self.error(Rule::Types, at, format!("the index {l} is no `isize`"));
                }
            }
        }
        if !self.errors.is_empty() {
            return;
        }
        let in_vm = self.module().is_some_and(|m| {
            let path = self.tcx.module(m).path;
            path.as_str() == "os/vm" || path.as_str().starts_with("os/vm/")
        });
        for (id, block) in b.blocks.iter_enumerated() {
            for (i, st) in block.stmts.iter().enumerate() {
                let at = Point::new(id, i);
                operands(Some(&st.kind), None).for_each(|o| self.move_ref(o, at));
                if let StatementKind::Assign { value, .. } = &st.kind {
                    match value {
                        Rvalue::Aggregate(_, ops) => {
                            ops.iter().for_each(|o| self.carrying_operand(o, at))
                        }
                        Rvalue::Convert(_, op) => self.carrying_operand(op, at),
                        _ => {}
                    }
                }
                self.statement(st, at, in_vm);
                self.guards(id, i, st);
            }
            let at = b.terminator_point(id);
            operands(None, Some(&block.term.kind)).for_each(|o| self.move_ref(o, at));
            if let TerminatorKind::Call { args, .. } = &block.term.kind {
                args.iter().for_each(|o| self.carrying_operand(o, at));
            }
            self.terminator(&block.term, at);
            self.class_guards(id, None);
            self.runs(id);
        }
        self.move_this();
    }

    fn statement(&mut self, st: &Statement, at: Point, in_vm: bool) {
        let b = self.b;
        let p = Some(at);
        match &st.kind {
            StatementKind::Assign { dest, value } => {
                let Some(dt) = self.place_ty(*dest) else {
                    return;
                };
                if let Rvalue::Convert(k, op) = value {
                    if let Some(st) = self.operand_ty(op)
                        && !self.convert_ok(*k, st, dt)
                    {
                        self.error(
                            Rule::ConvertPairs,
                            p,
                            format!(
                                "{k:?} does not convert `{}` to `{}`",
                                self.ty_str(st),
                                self.ty_str(dt)
                            ),
                        );
                    }
                    return;
                }
                match self.rvalue_ok(value, dt) {
                    Ok(()) => {}
                    Err(m) => self.error(Rule::Types, p, m),
                }
            }
            StatementKind::CheckBounds { index, len } => {
                for op in [index, len] {
                    if let Some(t) = self.operand_ty(op)
                        && self.tcx.kind(t) != TyKind::Int(IntTy::Isize)
                    {
                        self.error(Rule::Types, p, "a bounds check compares `isize`s");
                    }
                }
            }
            StatementKind::CheckTag { place, variant } => {
                let ok = self
                    .place_ty(*place)
                    .and_then(|t| variant_count(self.tcx, t))
                    .is_some_and(|n| variant.index() < n);
                if !ok {
                    self.error(Rule::Types, p, "a tag check on no such case");
                }
            }
            StatementKind::FieldInit { field, value } => {
                if let (Some(ft), Some(vt)) = (self.place_ty(*field), self.operand_ty(value))
                    && !self.fits(vt, ft)
                {
                    self.error(Rule::Types, p, "a field initialiser of another type");
                }
            }
            StatementKind::Drop(..) if b.phase != MirPhase::Built => {
                self.error(Rule::NoDropAfterElab, p, "`drop` after elaboration");
            }
            StatementKind::DropGlue(_) if b.phase == MirPhase::Built => {
                self.error(Rule::NoDropAfterElab, p, "`drop_glue` before elaboration");
            }
            StatementKind::Intrinsic { kind, .. } => {
                if !kind.is_safe() && st.region.is_none() {
                    self.error(
                        Rule::UnsafeIntrinsic,
                        p,
                        format!("`{}` outside every `unsafe` region", kind.name()),
                    );
                }
            }
            StatementKind::HostCall { .. } => {
                if !in_vm {
                    self.error(Rule::HostCallPlace, p, "a host call outside `os/vm`");
                }
            }
            _ => {}
        }
    }

    /// V09: no `Move` of a reference-typed place unless the place is a `Temp` local.
    fn move_ref(&mut self, op: &Operand, at: Point) {
        if let Operand::Move(p) = op
            && let Some(t) = self.place_ty(*p)
            && matches!(self.tcx.kind(t), TyKind::Ref(_))
            && !(p.is_local() && self.b.locals[p.local].kind == LocalKind::Temp)
        {
            self.error(
                Rule::MoveRef,
                Some(at),
                format!("a move of the reference {}", p.local),
            );
        }
    }

    /// V09 too: an aggregate's, a conversion's or a call's operand whose type
    /// carries loans is a whole local or a constant, since phase 3 reads such an
    /// operand's sets from its local; a reference read out of a field or part, or
    /// a borrowing value moved out of one, goes through a `Use` into a temporary
    /// first (A:935).
    fn carrying_operand(&mut self, op: &Operand, at: Point) {
        if let Some(p) = op.place()
            && !p.is_local()
            && let Some(t) = self.place_ty(p)
            && !self.tcx.is_value_type(t)
        {
            self.error(
                Rule::MoveRef,
                Some(at),
                format!(
                    "a part of {} carrying loans is an operand with no temporary",
                    p.local
                ),
            );
        }
    }

    fn rvalue_ok(&self, rv: &Rvalue, dt: Ty) -> Result<(), String> {
        let tcx = self.tcx;
        let mismatch = |what: String| Err(format!("{what} is assigned to `{}`", self.ty_str(dt)));
        let check = |t: Ty| -> Result<(), String> {
            match self.fits(t, dt) {
                true => Ok(()),
                false => mismatch(format!("`{}`", self.ty_str(t))),
            }
        };
        match rv {
            Rvalue::Use(op) => self.operand_ty(op).map_or(Ok(()), check),
            Rvalue::Ref { place, .. } => self
                .place_ty(*place)
                .map_or(Ok(()), |t| check(tcx.mk_ref(t))),
            Rvalue::AddrOf(place) => self
                .place_ty(*place)
                .map_or(Ok(()), |t| check(tcx.mk_raw(t))),
            Rvalue::Binary(op, x, y) => {
                let (Some(a), Some(c)) = (self.operand_ty(x), self.operand_ty(y)) else {
                    return Ok(());
                };
                let shift = matches!(op, BinOp::Shl | BinOp::Shr | BinOp::Ushr);
                if shift && !(self.int_or_error(a) && self.int_or_error(c)) {
                    return Err(self.shifted(a, c));
                }
                if !shift && !self.fits(a, c) && !self.fits(c, a) {
                    return Err(format!(
                        "`{}` and `{}` are combined",
                        self.ty_str(a),
                        self.ty_str(c)
                    ));
                }
                if matches!(op, BinOp::Div | BinOp::Rem) && !self.float_or_error(a) {
                    return Err(format!(
                        "`{}` of `{}` is `checked`",
                        crate::print::name_of(crate::print::BINOPS, op),
                        self.ty_str(a)
                    ));
                }
                match op.is_comparison() {
                    true => check(tcx.common().bool),
                    false => check(a),
                }
            }
            Rvalue::Checked(op, x, y) => {
                let (Some(a), Some(c)) = (self.operand_ty(x), self.operand_ty(y)) else {
                    return Ok(());
                };
                let shift = matches!(op, CheckedOp::Shl | CheckedOp::Shr | CheckedOp::Ushr);
                if shift && !(self.int_or_error(a) && self.int_or_error(c)) {
                    return Err(self.shifted(a, c));
                }
                if !shift && !self.fits(a, c) {
                    return Err(format!(
                        "`{}` and `{}` are combined",
                        self.ty_str(a),
                        self.ty_str(c)
                    ));
                }
                if matches!(op, CheckedOp::Div | CheckedOp::Rem)
                    && matches!(tcx.kind(a), TyKind::Float(_))
                {
                    return Err(format!(
                        "`checked_{}` of `{}`",
                        crate::print::name_of(crate::print::CHECKED, op),
                        self.ty_str(a)
                    ));
                }
                check(a)
            }
            Rvalue::Unary(_, x) | Rvalue::CheckedNeg(x) => self.operand_ty(x).map_or(Ok(()), check),
            Rvalue::Cast(k, x, t) => {
                check(*t)?;
                let Some(s) = self.operand_ty(x) else {
                    return Ok(());
                };
                let (sk, tk) = (tcx.kind(s), tcx.kind(*t));
                let int = |k: TyKind| matches!(k, TyKind::Int(_));
                let float = |k: TyKind| matches!(k, TyKind::Float(_));
                let raw = |k: TyKind| matches!(k, TyKind::Raw(_));
                let usize_ = |k: TyKind| k == TyKind::Int(IntTy::Usize);
                let ok = match k {
                    CastKind::IntToInt => int(sk) && int(tk),
                    CastKind::IntToFloat => int(sk) && float(tk),
                    CastKind::FloatToFloat => float(sk) && float(tk),
                    CastKind::FloatToInt => float(sk) && int(tk),
                    CastKind::EnumToInt => matches!(sk, TyKind::Adt(..)) && int(tk),
                    CastKind::BoolToInt => sk == TyKind::Bool && int(tk),
                    CastKind::UsizeToRaw => usize_(sk) && raw(tk),
                    CastKind::RawToUsize => raw(sk) && usize_(tk),
                    CastKind::RefToRaw => matches!(sk, TyKind::Ref(_)) && raw(tk),
                    CastKind::RawToRaw => raw(sk) && raw(tk),
                };
                match ok || tcx.references_error(s) {
                    true => Ok(()),
                    false => Err(format!(
                        "{k:?} does not cast `{}` to `{}`",
                        self.ty_str(s),
                        self.ty_str(*t)
                    )),
                }
            }
            Rvalue::Convert(..) => Ok(()),
            Rvalue::Aggregate(kind, ops) => {
                let tys: Vec<Option<Ty>> = ops.iter().map(|o| self.operand_ty(o)).collect();
                let parts = |want: &[Ty]| -> Result<(), String> {
                    if want.len() != tys.len() {
                        return Err(format!("{} operands for {} parts", tys.len(), want.len()));
                    }
                    for (got, &w) in tys.iter().zip(want) {
                        if let Some(g) = got
                            && !self.fits(*g, w)
                        {
                            return Err(format!(
                                "`{}` given for a part of type `{}`",
                                self.ty_str(*g),
                                self.ty_str(w)
                            ));
                        }
                    }
                    Ok(())
                };
                match kind {
                    AggregateKind::Fixed(e) => {
                        check(tcx.mk_fixed(*e, ops.len() as u64))?;
                        parts(&vec![*e; ops.len()])
                    }
                    AggregateKind::Repeat(n) => match tys.first().copied().flatten() {
                        Some(t) if ops.len() == 1 => check(tcx.mk_fixed(t, *n)),
                        _ => Err("`repeat` takes one operand".to_owned()),
                    },
                    AggregateKind::Tuple | AggregateKind::ClosureEnv => match tcx.kind(dt) {
                        TyKind::Tuple(l) => parts(&tcx.list(l)),
                        _ => mismatch("a tuple".to_owned()),
                    },
                    AggregateKind::Adt { adt, variant, args } => {
                        check(tcx.mk_adt(*adt, &tcx.list(*args)))?;
                        let pt = PlaceTy {
                            ty: tcx.mk_adt(*adt, &tcx.list(*args)),
                            variant: *variant,
                        };
                        let want: Vec<Ty> = (0..)
                            .map_while(|i| {
                                pt.project(tcx, Proj::Field(FieldIdx::new(i))).map(|t| t.ty)
                            })
                            .collect();
                        parts(&want)
                    }
                    AggregateKind::Object(shape) => {
                        check(tcx.mk_object_shape((*tcx.shape(*shape)).clone()))?;
                        let want: Vec<Ty> = tcx.shape(*shape).fields.iter().map(|f| f.1).collect();
                        parts(&want)
                    }
                    AggregateKind::Present => match tcx.kind(dt) {
                        TyKind::Nullable(t) => parts(&[t]),
                        _ => mismatch("a present value".to_owned()),
                    },
                    AggregateKind::Null => match tcx.kind(dt) {
                        TyKind::Nullable(_) if ops.is_empty() => Ok(()),
                        _ => mismatch("`null`".to_owned()),
                    },
                }
            }
            Rvalue::Discriminant(p) => {
                let ok = self
                    .place_ty(*p)
                    .and_then(|t| variant_count(tcx, t))
                    .is_some();
                match ok && matches!(tcx.kind(dt), TyKind::Int(_)) {
                    true => Ok(()),
                    false => Err("a discriminant of no enum, or into no integer".to_owned()),
                }
            }
            Rvalue::Len(p) => {
                let ok = self.place_ty(*p).is_some_and(|t| {
                    matches!(
                        tcx.kind(t),
                        TyKind::Array(_) | TyKind::Fixed(..) | TyKind::Slice(_) | TyKind::Str
                    )
                });
                match ok && tcx.kind(dt) == TyKind::Int(IntTy::Isize) {
                    true => Ok(()),
                    false => Err("a length of no array or view, or into no `isize`".to_owned()),
                }
            }
            Rvalue::ClosureValue { func, env } => match tcx.kind(dt) {
                TyKind::Closure(s) if *func == ClosureFn::FnValue => self.fn_value_env(*env, s),
                TyKind::Closure(_) | TyKind::Error => Ok(()),
                _ => mismatch("a closure".to_owned()),
            },
            Rvalue::ClosureReborrow(p) => self.place_ty(*p).map_or(Ok(()), check),
            Rvalue::ArrowFn(_) => match tcx.kind(dt) {
                TyKind::FnPtr(..) | TyKind::Error => Ok(()),
                _ => mismatch("a function".to_owned()),
            },
        }
    }

    /// V10's pairs.
    fn convert_ok(&self, k: ConvKind, from: Ty, to: Ty) -> bool {
        let tcx = self.tcx;
        let (f, t) = (tcx.kind(from), tcx.kind(to));
        let pointee = |k: TyKind| match k {
            TyKind::Ref(x) => Some((ClassHolder::Ref, x)),
            TyKind::Boxed(x) => Some((ClassHolder::Box, x)),
            _ => None,
        };
        match k {
            ConvKind::FixedToSlice | ConvKind::ArrayToSlice => {
                let (TyKind::Ref(a), TyKind::Ref(s)) = (f, t) else {
                    return false;
                };
                let TyKind::Slice(elem) = tcx.kind(s) else {
                    return false;
                };
                match (k, tcx.kind(a)) {
                    // Type identity ignores permission rows (S:682), which
                    // phase 3 compares (`borrowck::rows`).
                    (ConvKind::FixedToSlice, TyKind::Fixed(e, _))
                    | (ConvKind::ArrayToSlice, TyKind::Array(e)) => {
                        e == elem || tcx.same_ignoring_rows(e, elem)
                    }
                    _ => false,
                }
            }
            ConvKind::Upcast => {
                let (Some((hf, d)), Some((ht, a))) = (pointee(f), pointee(t)) else {
                    return false;
                };
                let (TyKind::Adt(dadt, dargs), TyKind::Adt(..)) = (tcx.kind(d), tcx.kind(a)) else {
                    return false;
                };
                let mut cur = tcx.base_of(dadt, dargs);
                while let Some((b, args)) = cur {
                    if tcx.mk_adt(b, &tcx.list(args)) == a {
                        return hf == ht;
                    }
                    cur = tcx.base_of(b, args);
                }
                false
            }
            ConvKind::BoxToInterface | ConvKind::RefToInterface => {
                let holder = match k {
                    ConvKind::BoxToInterface => ClassHolder::Box,
                    _ => ClassHolder::Ref,
                };
                let (Some((hf, c)), Some((ht, i))) = (pointee(f), pointee(t)) else {
                    return false;
                };
                if hf != holder || ht != holder {
                    return false;
                }
                let TyKind::Adt(iadt, _) = tcx.kind(i) else {
                    return false;
                };
                let Some(iface) = tcx.adt(iadt).as_interface() else {
                    return false;
                };
                if matches!(tcx.kind(c), TyKind::Param(_)) {
                    return true;
                }
                let Some(module) = self.module() else {
                    return true;
                };
                iface.methods.iter().all(|&m| {
                    tcx.def(m)
                        .name()
                        .is_some_and(|name| tcx.member(c, name, module).is_some())
                })
            }
        }
    }

    /// A callee's parameter types, the receiver first, and its return type, its
    /// type arguments substituted; an interface member's `Self` is the receiver's
    /// pointee (`&I`, or `Box<I>`, which it then takes), a method of the `@lang`
    /// class behind `string`,
    /// `Slice<T>`, `T[]` or `Box<T>` takes that type (`Tcx::lang_class_of`).
    fn callee_sig(&self, c: &Callee, args: &[Operand]) -> (Option<Vec<Ty>>, Option<Ty>) {
        let tcx = self.tcx;
        let ptr = |t: Option<Ty>| match t.map(|t| tcx.kind(t)) {
            Some(TyKind::FnPtr(_, s) | TyKind::Closure(s)) => {
                let s = tcx.fn_sig(s);
                (Some(s.params.iter().map(|p| p.0).collect()), Some(s.ret))
            }
            _ => (None, None),
        };
        match c {
            Callee::Fn(f) | Callee::Virtual { method: f, .. } => {
                let Some(sig) = tcx.sig_opt(f.def) else {
                    return (None, None);
                };
                let (mut params, mut targs) =
                    (tcx.all_params(sig.generics), tcx.list(f.args).to_vec());
                // Another count is the terminator's arity error, or an interface
                // member's `Self` after its parameters' arguments (sema's
                // `Target`), which is not checked here.
                if params.len() != targs.len() {
                    return (None, None);
                }
                let mut tys = Vec::new();
                if tcx.takes_this(f.def) {
                    let this = builtin(tcx, crate::decls::self_ty(tcx, f.def));
                    let mut recv_ty = tcx.mk_ref(this);
                    if let TyKind::Param(p) = tcx.kind(this)
                        && let Some(recv) = args.first().and_then(|a| self.operand_ty(a))
                        && let TyKind::Ref(x) | TyKind::Boxed(x) = tcx.kind(recv)
                    {
                        params.push(p);
                        targs.push(x);
                        // A `Box<I>` is a two-word `&I` (A:1541), a table V16 reads.
                        if matches!(tcx.kind(recv), TyKind::Boxed(_)) {
                            recv_ty = tcx.mk_box(this);
                        }
                    }
                    tys.push(recv_ty);
                }
                tys.extend(sig.params.iter().map(|p| p.ty));
                let s = |t: Ty| tcx.subst(t, &params, &targs);
                (Some(tys.into_iter().map(s).collect()), Some(s(sig.ret)))
            }
            Callee::Foreign(f) => match tcx.sig_opt(f.def) {
                Some(s) => (Some(s.params.iter().map(|p| p.ty).collect()), Some(s.ret)),
                None => (None, None),
            },
            Callee::FnPtr(op) => ptr(self.operand_ty(op)),
            Callee::ClosureLocal(l) => ptr(self.b.locals.get(*l).map(|d| d.ty)),
            Callee::NamedFill { .. } | Callee::ImplicitCtor { .. } => {
                (None, Some(tcx.common().void))
            }
            Callee::Form(_) | Callee::FormParts { .. } => (None, None),
        }
    }

    fn terminator(&mut self, t: &Terminator, at: Point) {
        let p = Some(at);
        match &t.kind {
            TerminatorKind::Switch { value, .. } => {
                if let Some(ty) = self.operand_ty(value)
                    && !matches!(self.tcx.kind(ty), TyKind::Int(_) | TyKind::Bool)
                {
                    self.error(Rule::Types, p, "a switch on no integer or `bool`");
                }
            }
            TerminatorKind::Call {
                callee, args, dest, ..
            } => {
                // A callee names one type argument per parameter of its generics,
                // before an interface member's `Self` (A:580: types agree); with
                // another count no parameter or result type could be checked.
                if let Callee::Fn(f) | Callee::Virtual { method: f, .. } = callee
                    && let Some(sig) = self.tcx.sig_opt(f.def)
                {
                    let (want, given) = (
                        self.tcx.all_params(sig.generics).len(),
                        self.tcx.list(f.args).len(),
                    );
                    let with_self = iface_self(self.tcx, f.def).is_some() && given == want + 1;
                    if want != given && !with_self {
                        self.error(
                            Rule::Types,
                            p,
                            format!(
                                "`{}` takes {want} type arguments, given {given}",
                                self.tcx
                                    .def(f.def)
                                    .name()
                                    .map_or("_".into(), |n| n.to_string())
                            ),
                        );
                    }
                }
                let (params, ret) = self.callee_sig(callee, args);
                if let Some(mut params) = params {
                    let sig = match callee {
                        Callee::Fn(f) | Callee::Virtual { method: f, .. } => {
                            self.tcx.sig_opt(f.def).map(|s| (f.def, s))
                        }
                        _ => None,
                    };
                    // A callee with a defaulted parameter takes the arguments
                    // supplied, then hidden ones, then their count (A:937).
                    if let Some((d, s)) = sig
                        && s.params.iter().any(|p| p.has_default)
                        && let Some(Operand::Const(c)) = args.last()
                        && let ConstKind::Value(ConstValue::Int(n, _)) = c.kind
                    {
                        params.truncate(usize::from(self.tcx.takes_this(d)) + n as usize);
                    }
                    let by_move = sig.is_some_and(|(_, s)| s.receiver == Some(Receiver::Move));
                    for (i, (a, w)) in args.iter().zip(&params).enumerate() {
                        // A `move` receiver passes the object moved into the call
                        // (A:1277), where `this` is `&C`.
                        let moved = |g: Ty| {
                            i == 0
                                && by_move
                                && matches!(self.tcx.kind(*w), TyKind::Ref(c) if self.fits(g, c))
                        };
                        if let Some(g) = self.operand_ty(a)
                            && !self.fits(g, *w)
                            && !moved(g)
                        {
                            self.error(
                                Rule::Types,
                                p,
                                format!(
                                    "argument {i} is `{}`, the parameter `{}`",
                                    self.ty_str(g),
                                    self.ty_str(*w)
                                ),
                            );
                        }
                    }
                }
                if let (Some(r), Some(d)) = (ret, self.place_ty(*dest))
                    && !self.fits(r, d)
                {
                    self.error(
                        Rule::Types,
                        p,
                        format!(
                            "a call returning `{}` into `{}`",
                            self.ty_str(r),
                            self.ty_str(d)
                        ),
                    );
                }
                if let Some(fc) = callee.form()
                    && let Some(why) = self.form_args(fc, args)
                {
                    let name = format!("{fc:?}").to_lowercase();
                    self.error(Rule::Types, p, format!("form `{name}` {why}"));
                }
                // The written arguments together gave every operand (A:976).
                if let Callee::FormParts { form, parts } = callee
                    && parts.iter().map(|&n| n as usize).sum::<usize>() != args.len()
                {
                    let name = format!("{form:?}").to_lowercase();
                    self.error(
                        Rule::Types,
                        p,
                        format!("form `{name}`'s part counts do not cover its operands"),
                    );
                }
                // Phase 3 reads an `fn` value's contract from its type, and would
                // read none from another (`call_info`'s row): a nullable one is
                // narrowed to its payload first, as a closure local is.
                if let Callee::FnPtr(op) = callee
                    && let Some(t) = self.operand_ty(op)
                    && !matches!(self.tcx.kind(t), TyKind::FnPtr(..) | TyKind::Error)
                {
                    self.error(
                        Rule::Types,
                        p,
                        format!("an `fn` call through `{}`", self.ty_str(t)),
                    );
                }
                if let Callee::ClosureLocal(l) = callee
                    && let Some(d) = self.b.locals.get(*l)
                    && !matches!(self.tcx.kind(d.ty), TyKind::Closure(_) | TyKind::Error)
                {
                    self.error(
                        Rule::Types,
                        p,
                        format!("a closure call through `{}`", self.ty_str(d.ty)),
                    );
                }
                if let Callee::Virtual { method, table } = callee
                    && !self.virtual_ok(method.def, table, args)
                {
                    self.error(
                        Rule::Virtual,
                        p,
                        "a virtual call where no table can be read",
                    );
                }
            }
            _ => {}
        }
    }

    /// V16: through an extensible class's `&C` or `Box<C>` calling an overridable
    /// method (A:1279: not `private`, not `static`, not compiled once per type),
    /// through a `&T` or `Box<T>` of a type parameter calling one of an extensible
    /// class (a bound `T extends C`, A:1281), or through an interface `Box` or
    /// `&I`; the table read from the receiver's place (plan b.4).
    fn virtual_ok(&self, method: enrang_hir::DefId, table: &Operand, args: &[Operand]) -> bool {
        let tcx = self.tcx;
        let Some(t) = self.operand_ty(table) else {
            return false;
        };
        if table.place().is_none() || table.place() != args.first().and_then(Operand::place) {
            return false;
        }
        let inner = match tcx.kind(t) {
            TyKind::Ref(x) | TyKind::Boxed(x) => x,
            _ => return false,
        };
        let adt = match tcx.kind(inner) {
            TyKind::Adt(adt, _) => adt,
            TyKind::Param(_) => match tcx.def(method).parent.and_then(|p| tcx.adt_of(p)) {
                Some(c) if tcx.adt(c).is_class() => c,
                _ => return false,
            },
            _ => return false,
        };
        match &tcx.adt(adt).kind {
            AdtKind::Interface(_) => true,
            AdtKind::Class(c) => {
                let data = tcx.def(method);
                let static_ = tcx
                    .sig_opt(method)
                    .is_some_and(|s| s.receiver == Some(Receiver::Static));
                c.modifier != ClassModifier::Final
                    && data.vis != Vis::Private
                    && !static_
                    && tcx.once_per_type(method).is_none()
            }
            AdtKind::Enum(_) => false,
        }
    }

    // -----------------------------------------------------------------------------
    // V04.

    /// `SetTable` on a class with a hidden pointer, and, outside a `DropGlue` or
    /// `NamedFill` shim, as the first write to the object a `new` builds (A:580,
    /// A:939): a whole local of exactly that class that no path has written since
    /// its storage began, so never an argument.
    fn set_tables(&mut self) {
        let b = self.b;
        let tcx = self.tcx;
        let shim = matches!(
            b.owner,
            BodyOwner::Shim(ShimKind::DropGlue(_) | ShimKind::NamedFill(_))
        );
        let mut written = None;
        for (id, block) in b.blocks.iter_enumerated() {
            for (i, st) in block.stmts.iter().enumerate() {
                let StatementKind::SetTable { place, class } = &st.kind else {
                    continue;
                };
                let at = Point::new(id, i);
                let hidden = match tcx.kind(*class) {
                    TyKind::Adt(adt, _) => tcx.adt(adt).as_class().is_some_and(|c| c.hidden_table),
                    _ => false,
                };
                let first = shim || {
                    let written = written.get_or_insert_with(|| solve(b, GenKill(Written)));
                    place.is_local()
                        && self.place_ty(*place) == Some(*class)
                        && !written.before(b, at).contains(place.local)
                };
                if !hidden || !first {
                    self.error(
                        Rule::SetTable,
                        Some(at),
                        format!(
                            "`set_table` of `{}` is no first write of a new object of a class with a table",
                            self.ty_str(*class)
                        ),
                    );
                }
            }
        }
    }

    // -----------------------------------------------------------------------------
    // V08 and the `Built` guards V12-V14.

    /// V08 at each `for...of` head (A:580, A:952-956): after the head's `Len` only
    /// the compare, then a `Switch` straight to the bind's block, where only
    /// `StorageLive(x)` precedes the bind's `CheckBounds`. Silent when the `Len` or
    /// the `CheckBounds` is missing, which V12 and V18 report.
    fn forof_heads(&mut self) {
        let b = self.b;
        let mut bad = Vec::new();
        for l in &b.meta.loops {
            if l.head.index() >= b.blocks.len() || !self.point_ok(l.bind) {
                continue;
            }
            let head = &b.blocks[l.head];
            let bind = &b.blocks[l.bind.block].stmts[..l.bind.index as usize];
            let is_len = |s: &Statement| {
                matches!(
                    &s.kind,
                    StatementKind::Assign {
                        value: Rvalue::Len(_),
                        ..
                    }
                )
            };
            let (Some(len), Some(bounds)) = (
                head.stmts.iter().rposition(is_len),
                bind.iter()
                    .rposition(|s| matches!(s.kind, StatementKind::CheckBounds { .. })),
            ) else {
                continue;
            };
            for (k, st) in head.stmts.iter().enumerate().skip(len + 1) {
                let compare = k == len + 1
                    && matches!(&st.kind, StatementKind::Assign {
                        value: Rvalue::Binary(op, ..), ..
                    } if op.is_comparison());
                if !compare {
                    bad.push(Point::new(l.head, k));
                }
            }
            let to_bind = matches!(&head.term.kind, TerminatorKind::Switch { .. })
                && head.term.kind.successors().contains(&l.bind.block);
            if !to_bind {
                bad.push(b.terminator_point(l.head));
            }
            for (k, st) in bind[..bounds].iter().enumerate() {
                if st.kind != StatementKind::StorageLive(l.binding) {
                    bad.push(Point::new(l.bind.block, k));
                }
            }
        }
        for at in bad {
            self.error(
                Rule::CheckRuns,
                Some(at),
                "only the compare, the `Switch` and `StorageLive(x)` lie between a `for...of` head's `Len` and its `CheckBounds`",
            );
        }
    }

    /// The run of checks directly before statement `i` of `block`.
    fn run_before(&self, block: BlockId, i: usize) -> &'a [Statement] {
        let stmts = &self.b.blocks[block].stmts;
        let mut start = i;
        while start > 0 && is_check(&stmts[start - 1]) {
            start -= 1;
        }
        &stmts[start..i]
    }

    /// Whether `user` (a statement, or the terminator when `None`) uses `check`.
    fn uses(&self, check: &Statement, block: BlockId, user: Option<&Statement>) -> bool {
        let b = self.b;
        let user_places: Vec<Place> = match user {
            Some(st) => statement_places(&st.kind),
            None => terminator_places(&b.blocks[block].term.kind),
        };
        match &check.kind {
            StatementKind::CheckBounds { index, .. } => user_places.iter().any(|p| {
                b.projs(*p).iter().any(|proj| match (proj, index) {
                    (Proj::Index(l), Operand::Copy(ip) | Operand::Move(ip)) => ip.is_local() && ip.local == *l,
                    (Proj::ConstIndex(n), Operand::Const(c)) => {
                        matches!(c.kind, ConstKind::Value(ConstValue::Int(v, _)) if v == u128::from(*n))
                    }
                    _ => false,
                })
            }),
            StatementKind::CheckTag { place, variant } => {
                let prefix = b.projs(*place);
                user_places.iter().any(|p| {
                    let projs = b.projs(*p);
                    p.local == place.local
                        && projs.len() > prefix.len()
                        && projs.starts_with(prefix)
                        && projs[prefix.len()] == Proj::Variant(*variant)
                })
            }
            StatementKind::CheckClass { place, op, .. } => {
                matches!(op, ClassOp::MoveThis(_)) || user_places.iter().any(|p| p.local == place.local)
            }
            _ => true,
        }
    }

    /// V08 over one block: each maximal run is used by what directly follows it.
    fn runs(&mut self, block: BlockId) {
        let stmts = &self.b.blocks[block].stmts;
        let mut i = 0;
        while i < stmts.len() {
            if !is_check(&stmts[i]) {
                i += 1;
                continue;
            }
            let start = i;
            while i < stmts.len() && is_check(&stmts[i]) {
                i += 1;
            }
            let user = stmts.get(i);
            let ends_at_call = user.is_none()
                && matches!(self.b.blocks[block].term.kind, TerminatorKind::Call { .. });
            for (k, check) in stmts[start..i].iter().enumerate() {
                let move_this = block == BlockId::ENTRY
                    && start + k == 0
                    && matches!(
                        check.kind,
                        StatementKind::CheckClass {
                            op: ClassOp::MoveThis(_),
                            ..
                        }
                    );
                let class_on_call =
                    ends_at_call && matches!(check.kind, StatementKind::CheckClass { .. });
                if move_this || class_on_call {
                    continue;
                }
                if (user.is_none() && !ends_at_call) || !self.uses(check, block, user) {
                    self.error(
                        Rule::CheckRuns,
                        Some(Point::new(block, start + k)),
                        "a check is not directly before the statement it guards",
                    );
                }
            }
        }
    }

    /// V12-V14 for statement `i` of `block`.
    fn guards(&mut self, block: BlockId, i: usize, st: &Statement) {
        if self.b.phase != MirPhase::Built {
            return;
        }
        let b = self.b;
        let at = Some(Point::new(block, i));
        let run = self.run_before(block, i);
        for p in statement_places(&st.kind) {
            let projs = b.projs(p);
            let mut pt = PlaceTy::of(b.locals[p.local].ty);
            for (k, &proj) in projs.iter().enumerate() {
                let base = &projs[..k];
                match proj {
                    Proj::Variant(v) => {
                        let guarded = run.iter().any(|c| match &c.kind {
                            StatementKind::CheckTag { place, variant } => {
                                *variant == v && place.local == p.local && b.projs(*place) == base
                            }
                            _ => false,
                        });
                        if !guarded {
                            self.error(Rule::GuardTag, at, "a case projection with no tag check");
                        }
                    }
                    Proj::Index(_) | Proj::ConstIndex(_) => {
                        let static_len = match self.tcx.kind(pt.ty) {
                            TyKind::Fixed(_, n) => Some(n),
                            TyKind::Tuple(l) => Some(self.tcx.list(l).len() as u64),
                            _ => None,
                        };
                        match (proj, static_len) {
                            (Proj::ConstIndex(n), Some(len)) => {
                                if n >= len {
                                    self.error(
                                        Rule::GuardBounds,
                                        at,
                                        format!("index {n} of a length {len}"),
                                    );
                                }
                            }
                            _ => {
                                if !self.bounds_guarded(run, p.local, base, proj) {
                                    self.error(
                                        Rule::GuardBounds,
                                        at,
                                        "an index with no bounds check on its length",
                                    );
                                }
                            }
                        }
                    }
                    _ => {}
                }
                match pt.project(self.tcx, proj) {
                    Some(next) => pt = next,
                    None => break,
                }
            }
        }
        self.class_guards(block, Some(i));
    }

    /// Whether `run` checks the index of `base[proj]` against a `Len` of `base`.
    fn bounds_guarded(&self, run: &[Statement], local: Local, base: &[Proj], proj: Proj) -> bool {
        let b = self.b;
        run.iter().any(|c| {
            let StatementKind::CheckBounds { index, len } = &c.kind else {
                return false;
            };
            let index_ok = match (proj, index) {
                (Proj::Index(l), Operand::Copy(p) | Operand::Move(p)) => {
                    p.is_local() && p.local == l
                }
                (Proj::ConstIndex(n), Operand::Const(k)) => {
                    matches!(k.kind, ConstKind::Value(ConstValue::Int(v, _)) if v == u128::from(n))
                }
                _ => false,
            };
            let Some(len_place) = len.place().filter(|p| p.is_local()) else {
                return false;
            };
            index_ok
                && b.blocks.iter().any(|blk| {
                    blk.stmts.iter().any(|s| match &s.kind {
                        StatementKind::Assign {
                            dest,
                            value: Rvalue::Len(lp),
                        } => *dest == len_place && lp.local == local && b.projs(*lp) == base,
                        _ => false,
                    })
                })
        })
    }

    /// Whether an object of type `t` may be of a subclass: a class that can be
    /// extended, or a type parameter.
    fn extensible(&self, t: Ty) -> bool {
        match self.tcx.kind(t) {
            TyKind::Param(_) => true,
            TyKind::Adt(adt, _) => {
                (self.tcx.adt(adt).as_class()).is_some_and(|c| c.modifier != ClassModifier::Final)
            }
            _ => false,
        }
    }

    /// The object `local` with `projs` reaches, and what holds it, when its last
    /// step dereferences a reference or a box and its type may be of a subclass.
    fn object(&self, local: Local, projs: &[Proj]) -> Option<(ClassHolder, Local, Vec<Proj>)> {
        let (Proj::Deref, init) = projs.split_last()? else {
            return None;
        };
        let mut pt = PlaceTy::of(self.b.locals[local].ty);
        for &x in init {
            pt = pt.project(self.tcx, x)?;
        }
        let (via, t) = match self.tcx.kind(pt.ty) {
            TyKind::Ref(t) => (ClassHolder::Ref, t),
            TyKind::Boxed(t) => (ClassHolder::Box, t),
            _ => return None,
        };
        self.extensible(t).then(|| (via, local, projs.to_vec()))
    }

    /// V14 for statement `i` of `block`, or its terminator when `None`: the
    /// exact-class events of A:943 there, each with its `CheckClass` in the run
    /// directly before. A whole object written through a reference or a box
    /// (`Assign`, before the old value's `drop(..) [assign]` when there is one),
    /// copied out (`CopyOut`) or moved out of a box (`Unbox`), the object of a
    /// call to the `@lang("clone")` interface's `clone` or the `@lang("box")`
    /// class's `unbox`, which the receiver's borrow in the block names, and the
    /// objects of `mem.replace` (its first argument's borrow) and `mem.swap`
    /// (both arguments' borrows).
    fn class_guards(&mut self, block: BlockId, i: Option<usize>) {
        let (b, tcx) = (self.b, self.tcx);
        let data = &b.blocks[block];
        let end = i.unwrap_or(data.stmts.len());
        let (st, term) = match i {
            Some(i) => (Some(&data.stmts[i].kind), None),
            None => (None, Some(&data.term.kind)),
        };
        if b.phase != MirPhase::Built {
            return;
        }
        let mut events = Vec::new();
        let dest = match st {
            Some(StatementKind::Assign { dest, .. }) => Some((true, dest)),
            _ => None,
        };
        let ops = operands(st, term).filter_map(|o| match o {
            Operand::Copy(p) => Some((true, p)),
            Operand::Move(p) => Some((false, p)),
            Operand::Const(_) => None,
        });
        for (k, (copy, p)) in dest.into_iter().chain(ops).enumerate() {
            let op = match self.object(p.local, b.projs(*p)) {
                Some(_) if k == 0 && dest.is_some() => ClassOp::Assign,
                Some(_) if copy => ClassOp::CopyOut,
                Some((ClassHolder::Box, ..)) => ClassOp::Unbox,
                _ => continue,
            };
            // A write's check precedes the old value's drop, whatever checks follow it.
            let start = end - self.run_before(block, end).len();
            let at = match start.checked_sub(1).map(|d| &data.stmts[d].kind) {
                Some(StatementKind::Drop(d, DropOrigin::Assign))
                    if op == ClassOp::Assign && d == p =>
                {
                    start - 1
                }
                _ => end,
            };
            events.push((op, p.local, b.projs(*p).to_vec(), at));
        }
        if let Some(TerminatorKind::Call {
            callee: Callee::Fn(f),
            args,
            ..
        }) = term
            && let Some(recv) = args
                .first()
                .and_then(Operand::place)
                .filter(|p| p.is_local())
            && let Some(parent) = tcx.def(f.def).parent.and_then(|d| tcx.adt_of(d))
        {
            let name = tcx.def(f.def).name().map_or("", |n| n.as_str());
            let op = match name {
                "clone" if tcx.is_lang_adt(parent, LangItem::Clone) => Some(ClassOp::Clone),
                "unbox" if tcx.is_lang_adt(parent, LangItem::Boxed) => Some(ClassOp::Unbox),
                _ => None,
            };
            let borrowed = data.stmts[..end].iter().rev().find_map(|s| match &s.kind {
                StatementKind::Assign { dest, value } if *dest == recv => match value {
                    Rvalue::Ref { place, .. } => Some(Some(*place)),
                    _ => Some(None),
                },
                _ => None,
            });
            if let (Some(op), Some(Some(place))) = (op, borrowed) {
                let mut projs = b.projs(place).to_vec();
                let boxed = self
                    .place_ty(place)
                    .is_some_and(|t| matches!(tcx.kind(t), TyKind::Boxed(_)));
                if op == ClassOp::Unbox || boxed {
                    projs.push(Proj::Deref);
                }
                if self.object(place.local, &projs).is_some() {
                    // An object whose place needs a tag or bounds check is named
                    // through the receiver, `*recv`: the check ends the run before
                    // the `Call` (A:943), where neither of those may stand.
                    let guarded =
                        (projs.iter()).any(|p| matches!(p, Proj::Variant(_) | Proj::Index(_)));
                    // `*recv` of a reference to the object, `**recv` of one to a box.
                    let through_recv = match op == ClassOp::Unbox || boxed {
                        true => vec![Proj::Deref, Proj::Deref],
                        false => vec![Proj::Deref],
                    };
                    match guarded {
                        true => events.push((op, recv.local, through_recv, end)),
                        false => events.push((op, place.local, projs, end)),
                    }
                }
            }
        }
        if let Some(TerminatorKind::Call {
            callee: Callee::Fn(f),
            args,
            ..
        }) = term
        {
            let (op, n) = match tcx.lang_item_of(f.def) {
                Some(LangItem::MemReplace) => (ClassOp::Replace, 1),
                Some(LangItem::MemSwap) => (ClassOp::Swap, 2),
                _ => (ClassOp::Replace, 0),
            };
            // Each object is checked directly before the borrow that passes it,
            // which reserves it to the call (a check after it would read under it).
            for a in args.iter().take(n) {
                let Some(t) = a.place().filter(|p| p.is_local()) else {
                    continue;
                };
                let made = data.stmts[..end].iter().rposition(
                    |s| matches!(&s.kind, StatementKind::Assign { dest, .. } if *dest == t),
                );
                if let Some(k) = made
                    && let StatementKind::Assign {
                        value: Rvalue::Ref { place, .. },
                        ..
                    } = &data.stmts[k].kind
                    && self.object(place.local, b.projs(*place)).is_some()
                {
                    events.push((op, place.local, b.projs(*place).to_vec(), k));
                }
            }
        }
        for (op, local, projs, end) in events {
            let guarded = self.run_before(block, end).iter().any(|c| {
                matches!(&c.kind, StatementKind::CheckClass { place, op: cop, .. }
                    if *cop == op && place.local == local && b.projs(*place) == projs)
            });
            if !guarded {
                let at = Some(Point::new(block, end));
                let message = format!("a whole-object {op:?} with no class check");
                self.error(Rule::GuardClass, at, message);
            }
        }
    }

    /// V14 at the entry of a `move` method whose class may be of a subclass: its
    /// first statement is `check_class(*_1, move_this(name), ref)` (A:943).
    fn move_this(&mut self) {
        let (b, tcx) = (self.b, self.tcx);
        let BodyOwner::Fn(d) = b.owner else {
            return;
        };
        let moves = tcx.sig_opt(d).and_then(|s| s.receiver) == Some(Receiver::Move);
        if b.phase != MirPhase::Built || !moves || !self.extensible(crate::decls::self_ty(tcx, d)) {
            return;
        }
        let ok = matches!(
            b.blocks[BlockId::ENTRY].stmts.first().map(|s| &s.kind),
            Some(StatementKind::CheckClass { place, op: ClassOp::MoveThis(n), via: ClassHolder::Ref })
                if Some(*n) == tcx.def(d).name()
                    && place.local == Local(1)
                    && b.projs(*place) == [Proj::Deref]
        );
        if !ok {
            let at = Some(Point::new(BlockId::ENTRY, 0));
            self.error(
                Rule::GuardClass,
                at,
                "a `move` method that can be inherited starts with no `move_this` check",
            );
        }
    }

    // -----------------------------------------------------------------------------
    // V11.

    fn field_inits(&mut self) {
        let b = self.b;
        let tcx = self.tcx;
        let inits: Vec<(Point, Place)> = b
            .blocks
            .iter_enumerated()
            .flat_map(|(id, block)| {
                block
                    .stmts
                    .iter()
                    .enumerate()
                    .filter_map(move |(i, s)| match &s.kind {
                        StatementKind::FieldInit { field, .. } => Some((Point::new(id, i), *field)),
                        _ => None,
                    })
            })
            .collect();
        let class = match b.owner {
            BodyOwner::Fn(d) if tcx.def(d).kind == DefKind::Ctor => {
                tcx.def(d).parent.and_then(|p| tcx.adt_of(p))
            }
            _ => None,
        };
        let class_def = class.and_then(|a| tcx.adt(a).as_class().cloned());
        let extensible = class_def
            .as_ref()
            .is_some_and(|c| c.modifier != ClassModifier::Final);
        if !inits.is_empty() && !extensible {
            for (at, _) in &inits {
                self.error(
                    Rule::FieldInit,
                    Some(*at),
                    "a field initialiser outside a constructor of a class that can be extended",
                );
            }
            return;
        }
        let Some(c) = class_def else {
            return;
        };
        let cfg = Cfg::new(b);
        // The arm a `Switch` on `overridden(f)` takes when no class below sets `f`.
        let switches: Vec<(FieldIdx, Vec<BlockId>)> = b
            .blocks
            .iter()
            .filter_map(|block| match &block.term.kind {
                TerminatorKind::Switch {
                    value: Operand::Const(k),
                    arms,
                    otherwise,
                } => match k.kind {
                    ConstKind::Value(ConstValue::Overridden(f)) => Some((
                        f,
                        arms.iter()
                            .filter(|(v, t)| *v == 0 && Some(*t) != *otherwise)
                            .map(|(_, t)| *t)
                            .collect(),
                    )),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        for (at, field) in &inits {
            let Some(&Proj::Field(f)) = b.projs(*field).last() else {
                self.error(
                    Rule::FieldInit,
                    Some(*at),
                    "a field initialiser stores no field",
                );
                continue;
            };
            let entered = switches.iter().any(|(sf, targets)| {
                *sf == f && targets.iter().any(|&t| cfg.dominates(t, at.block))
            });
            if !entered {
                self.error(
                    Rule::FieldInit,
                    Some(*at),
                    "a field initialiser outside the switch on its field's `overridden`",
                );
            }
        }
        if c.overrides.is_empty() {
            return;
        }
        let base_adt = c.base.and_then(|t| match tcx.kind(t) {
            TyKind::Adt(a, _) => Some(a),
            _ => None,
        });
        let results = solve(
            b,
            Inits {
                body: b,
                fields: c.fields.len(),
            },
        );
        for (id, block) in b.blocks.iter_enumerated() {
            let TerminatorKind::Call { callee, .. } = &block.term.kind else {
                continue;
            };
            let is_super = match callee {
                Callee::Fn(f) => {
                    tcx.def(f.def).kind == DefKind::Ctor
                        && tcx.def(f.def).parent.and_then(|p| tcx.adt_of(p)) == base_adt
                }
                Callee::ImplicitCtor { .. } => true,
                _ => false,
            };
            if !is_super || !cfg.reachable.contains(id) {
                continue;
            }
            let at = b.terminator_point(id);
            let set = results.before(b, at);
            for f in &c.overrides {
                if !set.contains(*f) {
                    self.error(
                        Rule::FieldInit,
                        Some(at),
                        format!("field {} is not initialised before `super`", f.index()),
                    );
                }
            }
        }
    }
}

/// The built-in type a `@lang` class stands for (`Tcx::lang_class_of`'s inverse),
/// or `t`.
fn builtin(tcx: &Tcx, t: Ty) -> Ty {
    let TyKind::Adt(adt, args) = tcx.kind(t) else {
        return t;
    };
    let arg = tcx.list(args).first().copied();
    match (tcx.lang_item_of(tcx.adt(adt).def), arg) {
        (Some(LangItem::Str), _) => tcx.common().str,
        (Some(LangItem::Slice), Some(e)) => tcx.mk_slice(e),
        (Some(LangItem::Array), Some(e)) => tcx.mk_array(e),
        (Some(LangItem::Boxed), Some(e)) => tcx.mk_box(e),
        _ => t,
    }
}

/// The operands a statement or a terminator reads, a call's table or `fn`
/// value last.
pub(crate) fn operands<'b>(
    st: Option<&'b StatementKind>,
    term: Option<&'b TerminatorKind>,
) -> impl Iterator<Item = &'b Operand> {
    let mut out: Vec<&Operand> = Vec::new();
    match st {
        Some(StatementKind::Assign { value, .. }) => match value {
            Rvalue::Use(o)
            | Rvalue::Unary(_, o)
            | Rvalue::CheckedNeg(o)
            | Rvalue::Cast(_, o, _)
            | Rvalue::Convert(_, o) => out.push(o),
            Rvalue::Binary(_, x, y) | Rvalue::Checked(_, x, y) => out.extend([x, y]),
            Rvalue::Aggregate(_, ops) => out.extend(ops),
            _ => {}
        },
        Some(StatementKind::CheckBounds { index, len }) => out.extend([index, len]),
        Some(StatementKind::FieldInit { value, .. }) => out.push(value),
        Some(StatementKind::Intrinsic { args, .. } | StatementKind::HostCall { args, .. }) => {
            out.extend(args)
        }
        Some(StatementKind::Asm(a)) => out.extend(a.ins.iter().map(|(_, o)| o)),
        _ => {}
    }
    if let Some(TerminatorKind::Switch { value, .. }) = term {
        out.push(value);
    }
    if let Some(TerminatorKind::Call { callee, args, .. }) = term {
        out.extend(args);
        if let Callee::FnPtr(o) | Callee::Virtual { table: o, .. } = callee {
            out.push(o);
        }
    }
    out.into_iter()
}

/// The locals some path has written since their object began (V04): the
/// arguments at the entry; `StorageLive`, `StorageDead`, a whole-local `Drop` or
/// `DropGlue`, and a move of the whole local into a local, a literal or a call
/// (plan c.7, c.8) end the object, so a `new` into a local or temporary in a loop
/// starts afresh on every turn.
struct Written;

/// The whole locals `ops` move.
fn moved(ops: &[Operand]) -> impl Iterator<Item = Local> + '_ {
    ops.iter().filter_map(|op| match op {
        Operand::Move(p) if p.is_local() => Some(p.local),
        _ => None,
    })
}

impl GenKillAnalysis for Written {
    type Idx = Local;
    const FORWARD: bool = true;

    fn domain_size(&self, b: &Body) -> usize {
        b.locals.len()
    }

    fn entry_set(&self, b: &Body, set: &mut BitSet<Local>) {
        for l in b.args() {
            set.insert(l);
        }
    }

    fn statement_effect(&self, set: &mut BitSet<Local>, st: &Statement, _at: Point) {
        let (writes, ended): (Vec<Place>, Vec<Local>) = match &st.kind {
            StatementKind::StorageLive(l) | StatementKind::StorageDead(l) => (vec![], vec![*l]),
            StatementKind::Drop(p, _) | StatementKind::DropGlue(p) if p.is_local() => {
                (vec![], vec![p.local])
            }
            StatementKind::Assign { dest, value } => {
                let ops = match value {
                    Rvalue::Use(op) => std::slice::from_ref(op),
                    Rvalue::Aggregate(_, ops) => ops,
                    _ => &[],
                };
                (vec![*dest], moved(ops).collect())
            }
            StatementKind::FieldInit { field: p, .. }
            | StatementKind::SetTable { place: p, .. } => (vec![*p], vec![]),
            StatementKind::Intrinsic { dest, .. } | StatementKind::HostCall { dest, .. } => {
                (dest.iter().copied().collect(), vec![])
            }
            StatementKind::Asm(a) => (a.outs.iter().filter_map(|(_, p)| *p).collect(), vec![]),
            _ => (vec![], vec![]),
        };
        for l in ended {
            set.remove(l);
        }
        for p in writes {
            set.insert(p.local);
        }
    }

    fn terminator_effect(&self, set: &mut BitSet<Local>, t: &Terminator, _at: Point) {
        if let TerminatorKind::Call { dest, args, .. } = &t.kind {
            for l in moved(args) {
                set.remove(l);
            }
            set.insert(dest.local);
        }
    }
}

/// The overridden fields given a `FieldInit` on every path so far (V11). The
/// `otherwise` arm of a `Switch` on `overridden(f)`, where a class below sets `f`,
/// counts as setting it.
struct Inits<'b> {
    body: &'b Body,
    fields: usize,
}

impl DataflowAnalysis for Inits<'_> {
    type Domain = BitSet<FieldIdx>;
    const FORWARD: bool = true;

    fn bottom(&self, _b: &Body) -> BitSet<FieldIdx> {
        BitSet::full(self.fields)
    }

    fn entry(&self, _b: &Body) -> BitSet<FieldIdx> {
        BitSet::new(self.fields)
    }

    fn join(&self, into: &mut BitSet<FieldIdx>, from: &BitSet<FieldIdx>) -> bool {
        into.intersect(from)
    }

    fn statement(&self, set: &mut BitSet<FieldIdx>, st: &Statement, _at: Point) {
        if let StatementKind::FieldInit { field, .. } = &st.kind
            && let Some(&Proj::Field(f)) = self.body.projs(*field).last()
            && f.index() < self.fields
        {
            set.insert(f);
        }
    }

    fn terminator(&self, _set: &mut BitSet<FieldIdx>, _t: &Terminator, _at: Point) {}

    fn edge(&self, set: &mut BitSet<FieldIdx>, from: BlockId, to: BlockId) {
        if let TerminatorKind::Switch {
            value: Operand::Const(k),
            arms,
            otherwise: Some(o),
        } = &self.body.blocks[from].term.kind
            && let ConstKind::Value(ConstValue::Overridden(f)) = k.kind
            && *o == to
            && arms.iter().all(|(_, b)| *b != to)
            && f.index() < self.fields
        {
            set.insert(f);
        }
    }
}

/// The `Self` parameter of the interface that declares member `def`, if one does.
fn iface_self(tcx: &Tcx, def: DefId) -> Option<ParamId> {
    let parent = tcx.def(def).parent?;
    let adt = tcx.adt_of(parent)?;
    tcx.adt(adt).as_interface().map(|i| i.self_param)
}
