//! Inference variables (plan d.5; A:888; owner 3A): union-find over `InferVar` with
//! the kinds `Any`, `Int` and `Float`. An `Int` variable unifies with any integer or
//! float type, a `Float` one with a float (SPEC 4.7); `Int` with `Float` gives
//! `Float`. Variables unify across the whole body; at its end `Int` defaults to
//! `i32` (`isize` first for a variable used as an index), `Float` to `f64`, and an
//! `Any` left is EN0410 at the expression that made it.
//!
//! Unification compares types as `Tcx::same_ignoring_rows` does (N1): the marks and
//! `readonly` of a function type's rows, and which fields of an object type were
//! written `x?: T`, never matter. `Error` unifies with everything and binds the
//! variables it meets, so one rejection reports once. A failed unification leaves
//! the table as it was.
//!
//! The finished body is rewritten by [`Resolver`]: every type with its variables
//! replaced, each number literal's constant at its final type, each cast's kind
//! chosen from its resolved types (S:703), and an `Any` variable no origin names
//! reported at the first expression or local whose type holds it.

use std::collections::{BTreeMap, BTreeSet};

use enrang_base::{IdVec, Span};
use enrang_diag::{Code, Diagnostic, Help};
use enrang_hir::{
    self as hir, ArmBody, ArmValue, ArrayPart, ArrowBodyKind, Callee, ConstValue, ExpectArg,
    ExprId, ExprKind, FnPtrSig, ForSource, FormKind, InferVar, OptMember, StmtKind, Tcx, TplPart,
    Ty, TyKind,
};

use crate::typeck::FnCtxt;

/// What a variable may become.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum VarKind {
    Any,
    Int,
    Float,
}

/// One variable: its union-find parent, its kind, and what it is bound to.
#[derive(Copy, Clone, Debug)]
pub(crate) struct VarData {
    pub parent: InferVar,
    pub kind: VarKind,
    pub value: Option<Ty>,
}

/// What made a variable, for EN0410: where, and how the message names it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct VarOrigin {
    pub span: Span,
    /// `` `q` `` or `` `[]` ``, quoted as the message prints it.
    pub what: String,
}

/// The variables of one body.
#[derive(Clone, Debug, Default)]
pub(crate) struct InferTable {
    pub vars: IdVec<InferVar, VarData>,
    /// The origin of each variable made by [`FnCtxt::new_var`].
    pub origins: BTreeMap<InferVar, VarOrigin>,
    /// Variables used as an index, which default to `isize` (S:727).
    pub indexes: BTreeSet<InferVar>,
    /// Unannotated locals whose type is a variable, with the span of the name, for
    /// EN0411's `: i64` fix-it.
    pub locals: Vec<(InferVar, Span)>,
    /// The roots `apply_defaults` gave `int`.
    pub defaulted: BTreeSet<InferVar>,
}

impl InferTable {
    /// A fresh variable of `kind`.
    pub fn fresh(&mut self, kind: VarKind) -> InferVar {
        let var = self.vars.next_index();
        self.vars.push(VarData {
            parent: var,
            kind,
            value: None,
        })
    }

    /// The representative of `var`'s set, compressing the path.
    #[allow(dead_code)] // For the other stages; this file reads `root`.
    pub fn find(&mut self, var: InferVar) -> InferVar {
        let parent = self.vars[var].parent;
        if parent == var {
            return var;
        }
        let root = self.find(parent);
        self.vars[var].parent = root;
        root
    }

    /// The representative of `var`'s set, without path compression.
    pub fn root(&self, mut var: InferVar) -> InferVar {
        while self.vars[var].parent != var {
            var = self.vars[var].parent;
        }
        var
    }

    /// Whether some variable of `root`'s set is used as an index.
    fn indexed(&self, root: InferVar) -> bool {
        self.indexes.iter().any(|&v| self.root(v) == root)
    }
}

/// `t` with its outermost variable resolved: a bound variable's value, itself
/// resolved, or the representative of an unbound one.
pub(crate) fn shallow_in(tcx: &Tcx, infer: &InferTable, mut t: Ty) -> Ty {
    loop {
        let TyKind::Infer(v) = tcx.kind(t) else {
            return t;
        };
        let root = infer.root(v);
        match infer.vars[root].value {
            Some(value) => t = value,
            None => return tcx.intern_ty(TyKind::Infer(root)),
        }
    }
}

/// `t` with every bound variable replaced by its value, deeply; unbound ones stay,
/// as their representatives.
pub(crate) fn resolve_in(tcx: &Tcx, infer: &InferTable, t: Ty) -> Ty {
    if !tcx.has_infer(t) {
        return t;
    }
    tcx.map_ty(t, &mut |tcx, inner| match tcx.kind(inner) {
        TyKind::Infer(_) => {
            let shallow = shallow_in(tcx, infer, inner);
            Some(match tcx.kind(shallow) {
                TyKind::Infer(_) => shallow,
                _ => resolve_in(tcx, infer, shallow),
            })
        }
        _ => None,
    })
}

/// `t` as a message prints it: resolved, with an unbound integer variable as `int`
/// and a float one as `f64`, the types they would default to.
pub(crate) fn display_in(tcx: &Tcx, infer: &InferTable, t: Ty) -> Ty {
    let resolved = resolve_in(tcx, infer, t);
    if !tcx.has_infer(resolved) {
        return resolved;
    }
    let common = *tcx.common();
    tcx.map_ty(resolved, &mut |tcx, inner| match tcx.kind(inner) {
        TyKind::Infer(v) => match infer.vars[infer.root(v)].kind {
            VarKind::Int => Some(common.i32),
            VarKind::Float => Some(common.f64),
            VarKind::Any => None,
        },
        _ => None,
    })
}

/// Unifies `a` with `b`; on failure the table may be half-changed, so callers go
/// through [`unify_in`].
fn unify_rec(tcx: &Tcx, infer: &mut InferTable, a: Ty, b: Ty) -> bool {
    let a = shallow_in(tcx, infer, a);
    let b = shallow_in(tcx, infer, b);
    if a == b {
        return true;
    }
    match (tcx.kind(a), tcx.kind(b)) {
        (TyKind::Error, other) | (other, TyKind::Error) => {
            if let TyKind::Infer(v) = other {
                let root = infer.root(v);
                infer.vars[root].value = Some(tcx.common().error);
            }
            true
        }
        (TyKind::Infer(x), TyKind::Infer(y)) => {
            let (rx, ry) = (infer.root(x), infer.root(y));
            let kind = match (infer.vars[rx].kind, infer.vars[ry].kind) {
                (VarKind::Any, k) | (k, VarKind::Any) => k,
                (VarKind::Int, VarKind::Int) => VarKind::Int,
                _ => VarKind::Float,
            };
            infer.vars[rx].parent = ry;
            infer.vars[ry].kind = kind;
            true
        }
        (TyKind::Infer(x), _) => bind(tcx, infer, x, b),
        (_, TyKind::Infer(y)) => bind(tcx, infer, y, a),
        (TyKind::Array(x), TyKind::Array(y))
        | (TyKind::Slice(x), TyKind::Slice(y))
        | (TyKind::Boxed(x), TyKind::Boxed(y))
        | (TyKind::Nullable(x), TyKind::Nullable(y))
        | (TyKind::Ref(x), TyKind::Ref(y))
        | (TyKind::Raw(x), TyKind::Raw(y)) => unify_rec(tcx, infer, x, y),
        (TyKind::Fixed(x, n), TyKind::Fixed(y, m)) => n == m && unify_rec(tcx, infer, x, y),
        (TyKind::Tuple(x), TyKind::Tuple(y)) => {
            let (x, y) = (tcx.list(x), tcx.list(y));
            x.len() == y.len()
                && x.iter()
                    .zip(y.iter())
                    .all(|(&p, &q)| unify_rec(tcx, infer, p, q))
        }
        (TyKind::Adt(p, x), TyKind::Adt(q, y)) => {
            let (x, y) = (tcx.list(x), tcx.list(y));
            p == q
                && x.len() == y.len()
                && x.iter()
                    .zip(y.iter())
                    .all(|(&s, &t)| unify_rec(tcx, infer, s, t))
        }
        (TyKind::FnPtr(abi1, x), TyKind::FnPtr(abi2, y)) => {
            abi1 == abi2 && unify_sigs(tcx, infer, &tcx.fn_sig(x), &tcx.fn_sig(y))
        }
        (TyKind::Closure(x), TyKind::Closure(y)) => {
            unify_sigs(tcx, infer, &tcx.fn_sig(x), &tcx.fn_sig(y))
        }
        (TyKind::Object(x), TyKind::Object(y)) => {
            let (x, y) = (tcx.shape(x), tcx.shape(y));
            x.fields.len() == y.fields.len()
                && x.fields
                    .iter()
                    .zip(y.fields.iter())
                    .all(|((n, s), (m, t))| n == m && unify_rec(tcx, infer, *s, *t))
        }
        _ => false,
    }
}

fn unify_sigs(tcx: &Tcx, infer: &mut InferTable, x: &FnPtrSig, y: &FnPtrSig) -> bool {
    x.unsafety == y.unsafety
        && x.params.len() == y.params.len()
        && x.params
            .iter()
            .zip(y.params.iter())
            .all(|((a, _), (b, _))| unify_rec(tcx, infer, *a, *b))
        && unify_rec(tcx, infer, x.ret, y.ret)
}

/// Binds the unbound variable `var` to the non-variable `t`, when its kind allows.
fn bind(tcx: &Tcx, infer: &mut InferTable, var: InferVar, t: Ty) -> bool {
    let root = infer.root(var);
    let ok = match infer.vars[root].kind {
        VarKind::Any => !occurs(tcx, infer, root, t),
        VarKind::Int => matches!(tcx.kind(t), TyKind::Int(_) | TyKind::Float(_)),
        VarKind::Float => matches!(tcx.kind(t), TyKind::Float(_)),
    };
    if ok {
        infer.vars[root].value = Some(t);
    }
    ok
}

/// Whether `t` mentions a variable of `root`'s set.
fn occurs(tcx: &Tcx, infer: &InferTable, root: InferVar, t: Ty) -> bool {
    tcx.any_ty(t, &mut |tcx, inner| match tcx.kind(inner) {
        TyKind::Infer(v) => {
            let r = infer.root(v);
            r == root
                || infer.vars[r]
                    .value
                    .is_some_and(|value| occurs(tcx, infer, root, value))
        }
        _ => false,
    })
}

/// Unifies `a` with `b`, leaving the table as it was when they do not unify.
pub(crate) fn unify_in(tcx: &Tcx, infer: &mut InferTable, a: Ty, b: Ty) -> bool {
    // Unification changes only the variables themselves.
    let snapshot = infer.vars.clone();
    if unify_rec(tcx, infer, a, b) {
        true
    } else {
        infer.vars = snapshot;
        false
    }
}

impl FnCtxt<'_, '_> {
    /// A fresh variable of `kind`, made by the expression at `span`, which EN0410
    /// names as `what` (already quoted, `` `q` ``).
    pub(crate) fn new_var(&mut self, kind: VarKind, span: Span, what: impl Into<String>) -> Ty {
        let var = self.infer.fresh(kind);
        self.infer.origins.insert(
            var,
            VarOrigin {
                span,
                what: what.into(),
            },
        );
        self.sema.tcx.intern_ty(TyKind::Infer(var))
    }

    /// `t` with its outermost variable resolved ([`shallow_in`]).
    pub(crate) fn shallow(&self, t: Ty) -> Ty {
        shallow_in(self.sema.tcx, &self.infer, t)
    }

    /// `t` with every bound variable resolved ([`resolve_in`]).
    pub(crate) fn resolve(&self, t: Ty) -> Ty {
        resolve_in(self.sema.tcx, &self.infer, t)
    }

    /// `t` spelled for a message ([`display_in`]).
    pub(crate) fn ty_str(&self, t: Ty) -> String {
        let shown = display_in(self.sema.tcx, &self.infer, t);
        self.sema.tcx.ty_string(shown)
    }

    /// The kind of the unbound variable `t` resolves to, if it does.
    pub(crate) fn var_kind(&self, t: Ty) -> Option<VarKind> {
        match self.sema.tcx.kind(self.shallow(t)) {
            TyKind::Infer(v) => Some(self.infer.vars[self.infer.root(v)].kind),
            _ => None,
        }
    }

    /// Unifies `a` with `b` (C10 included); on failure nothing changes.
    pub(crate) fn unify(&mut self, a: Ty, b: Ty) -> bool {
        unify_in(self.sema.tcx, &mut self.infer, a, b)
    }

    /// Whether `a` would unify with `b`; nothing changes either way.
    pub(crate) fn can_unify(&mut self, a: Ty, b: Ty) -> bool {
        let snapshot = self.infer.vars.clone();
        let ok = unify_rec(self.sema.tcx, &mut self.infer, a, b);
        self.infer.vars = snapshot;
        ok
    }

    /// Marks the variable of `t`, if it is one, as used as an index.
    pub(crate) fn note_index(&mut self, t: Ty) {
        if let TyKind::Infer(v) = self.sema.tcx.kind(self.shallow(t)) {
            self.infer.indexes.insert(v);
        }
    }

    /// The defaults at the end of a body (S:727): `int`, or `isize` for a variable
    /// used as an index; `f64`; and EN0410 for an `Any` variable with an origin,
    /// once per set, at its first variable's origin, the set then bound to `Error`.
    pub(crate) fn apply_defaults(&mut self) {
        let common = *self.sema.tcx.common();
        let vars: Vec<InferVar> = self.infer.vars.indices().collect();
        let mut reported = BTreeSet::new();
        for v in vars {
            let root = self.infer.root(v);
            if self.infer.vars[root].value.is_some() {
                continue;
            }
            match self.infer.vars[root].kind {
                VarKind::Int => {
                    let ty = if self.infer.indexed(root) {
                        common.isize
                    } else {
                        self.infer.defaulted.insert(root);
                        common.i32
                    };
                    self.infer.vars[root].value = Some(ty);
                }
                VarKind::Float => self.infer.vars[root].value = Some(common.f64),
                VarKind::Any => {
                    if reported.contains(&root) {
                        continue;
                    }
                    let Some(origin) = self.infer.origins.get(&v).cloned() else {
                        continue;
                    };
                    reported.insert(root);
                    self.infer.vars[root].value = Some(common.error);
                    self.report_uninferred(origin.span, &origin.what);
                }
            }
        }
    }

    /// EN0410 at `span` for `what`.
    pub(crate) fn report_uninferred(&mut self, span: Span, what: &str) {
        self.sema.emit(
            Diagnostic::new(
                Code::EN0410,
                format!("cannot infer the type of {what}"),
                span,
                "nothing here decides its type",
            )
            .with_help(Help::text("add a type annotation")),
        );
    }

    /// Rewrites `body`'s types and literals once inference is done ([`Resolver`]).
    pub(crate) fn resolve_body(&mut self, body: &mut hir::Body) {
        let consts = std::mem::take(&mut self.literal_values);
        let arm_literals = std::mem::take(&mut self.arm_literals);
        let arm_ranges = std::mem::take(&mut self.arm_ranges);
        let mut unresolved = Vec::new();
        {
            let mut r = Resolver {
                tcx: self.sema.tcx,
                infer: &mut self.infer,
                consts: &consts,
                arm_literals: &arm_literals,
                arm_ranges: &arm_ranges,
                unresolved: &mut unresolved,
            };
            r.block(&mut body.root);
            for (_, e) in &mut body.param_defaults {
                r.expr(e);
            }
            for arrow in body.arrows.iter_mut() {
                match &mut arrow.body {
                    ArrowBodyKind::Expr(e) => r.expr(e),
                    ArrowBodyKind::Block(b) => r.block(b),
                }
                arrow.ret = r.ty(arrow.ret);
                let sig = (*r.tcx.fn_sig(arrow.sig)).clone();
                let sig = FnPtrSig {
                    params: sig.params.iter().map(|&(t, m)| (r.ty(t), m)).collect(),
                    ret: r.ty(sig.ret),
                    ..sig
                };
                arrow.sig = r.tcx.intern_fn_sig(sig);
            }
            for (_, local) in body.locals.iter_enumerated_mut() {
                if r.unbound(local.ty) {
                    let what = local
                        .name
                        .map_or_else(|| "this binding".to_owned(), |n| format!("`{n}`"));
                    r.unresolved.push((local.span, what));
                }
                local.ty = r.ty(local.ty);
            }
            body.ret = r.ty(body.ret);
        }
        for (span, what) in unresolved {
            self.report_uninferred(span, &what);
        }
    }
}

/// The rewrite of a finished body: every type resolved, an unbound `Any` variable
/// reported once at the first place that holds it and then bound to `Error`.
struct Resolver<'r> {
    tcx: &'r Tcx,
    infer: &'r mut InferTable,
    consts: &'r BTreeMap<ExprId, ConstValue>,
    arm_literals: &'r BTreeSet<ExprId>,
    arm_ranges: &'r BTreeSet<ExprId>,
    unresolved: &'r mut Vec<(Span, String)>,
}

impl Resolver<'_> {
    /// Whether `t` still holds an unbound variable.
    fn unbound(&self, t: Ty) -> bool {
        let resolved = resolve_in(self.tcx, self.infer, t);
        self.tcx.has_infer(resolved)
    }

    /// `t` resolved; any variable left becomes `Error`.
    fn ty(&mut self, t: Ty) -> Ty {
        let resolved = resolve_in(self.tcx, self.infer, t);
        if !self.tcx.has_infer(resolved) {
            return resolved;
        }
        let error = self.tcx.common().error;
        let mut roots = Vec::new();
        let infer = &*self.infer;
        let out = self
            .tcx
            .map_ty(resolved, &mut |tcx, inner| match tcx.kind(inner) {
                TyKind::Infer(v) => {
                    roots.push(infer.root(v));
                    Some(error)
                }
                _ => None,
            });
        for root in roots {
            self.infer.vars[root].value = Some(error);
        }
        out
    }

    fn list(&mut self, l: hir::TyList) -> hir::TyList {
        let tys: Vec<Ty> = self.tcx.list(l).iter().map(|&t| self.ty(t)).collect();
        self.tcx.intern_list(&tys)
    }

    fn block(&mut self, b: &mut hir::Block) {
        for s in &mut b.stmts {
            self.stmt(s);
        }
    }

    fn stmt(&mut self, s: &mut hir::Stmt) {
        match &mut s.kind {
            StmtKind::Let { init, .. } => {
                if let Some(e) = init {
                    self.expr(e);
                }
            }
            StmtKind::Destructure { init, .. } => self.expr(init),
            StmtKind::If { cond, then_, else_ } => {
                self.expr(cond);
                self.block(then_);
                if let Some(b) = else_ {
                    self.block(b);
                }
            }
            StmtKind::While { cond, body, .. } | StmtKind::DoWhile { body, cond, .. } => {
                self.expr(cond);
                self.block(body);
            }
            StmtKind::For {
                init,
                cond,
                step,
                body,
                ..
            } => {
                if let Some(s) = init {
                    self.stmt(s);
                }
                if let Some(c) = cond {
                    self.expr(c);
                }
                if let Some(s) = step {
                    self.stmt(s);
                }
                self.block(body);
            }
            StmtKind::ForOf { source, body, .. } => {
                match source {
                    ForSource::Path { place } => self.expr(place),
                    ForSource::Once { value, .. } => self.expr(value),
                    ForSource::Range { lo, hi } => {
                        self.expr(lo);
                        self.expr(hi);
                    }
                }
                self.block(body);
            }
            StmtKind::Return(e) => {
                if let Some(e) = e {
                    self.expr(e);
                }
            }
            StmtKind::Break(_) | StmtKind::Continue(_) => {}
            StmtKind::Block(b) | StmtKind::Unsafe(b) => self.block(b),
            StmtKind::Expr(e) => self.expr(e),
            StmtKind::Expect(x) => {
                self.expr(&mut x.actual);
                for arg in &mut x.args {
                    match arg {
                        ExpectArg::Expr(e) => self.expr(e),
                        ExpectArg::Arm(v) => self.arm_value(v),
                    }
                }
            }
        }
    }

    fn value(&mut self, v: &mut ConstValue) {
        match v {
            ConstValue::Int(_, t) | ConstValue::Float(_, t) => *t = self.ty(*t),
            ConstValue::FnAddr(f) => f.args = self.list(f.args),
            _ => {}
        }
    }

    fn arm_value(&mut self, v: &mut ArmValue) {
        match v {
            ArmValue::Const(c) => self.value(c),
            ArmValue::Range(a, b) => {
                self.value(a);
                self.value(b);
            }
            ArmValue::Cond(e) => {
                let id = e.id;
                self.expr(e);
                if self.arm_literals.contains(&id) {
                    let value = self.literal(e);
                    *v = ArmValue::Const(value);
                } else if self.arm_ranges.contains(&id) {
                    let range = match &e.kind {
                        ExprKind::TupleLit(ends) if ends.len() == 2 => {
                            Some((self.literal(&ends[0]), self.literal(&ends[1])))
                        }
                        _ => None,
                    };
                    *v = match range {
                        Some((lo, hi)) => ArmValue::Range(lo, hi),
                        None => ArmValue::Const(ConstValue::Void),
                    };
                }
            }
            ArmValue::Null | ArmValue::Case(_) => {}
        }
    }

    /// The constant of a resolved number literal of an arm value; `Void` when it did
    /// not fit (EN0411 was reported).
    fn literal(&self, e: &hir::Expr) -> ConstValue {
        match (&e.kind, self.consts.contains_key(&e.id)) {
            (ExprKind::Const(c), true) => *c,
            _ => ConstValue::Void,
        }
    }

    fn callee(&mut self, c: &mut Callee) {
        match c {
            Callee::Fn(f) | Callee::Super(f) => f.args = self.list(f.args),
            Callee::BoundMember { args, .. }
            | Callee::Intrinsic(_, args)
            | Callee::SuperCtor { args, .. } => *args = self.list(*args),
            Callee::FnPtr(e) => self.expr(e),
            Callee::Form(form) => match form {
                FormKind::SizeOf(t) | FormKind::AlignOf(t) | FormKind::OffsetOf(t, _) => {
                    *t = self.ty(*t);
                }
                _ => {}
            },
            Callee::Closure(_) | Callee::Foreign(_) | Callee::HostCall(_) => {}
        }
    }

    fn exprs(&mut self, es: &mut [hir::Expr]) {
        for e in es {
            self.expr(e);
        }
    }

    fn expr(&mut self, e: &mut hir::Expr) {
        if self.unbound(e.ty) {
            let what = "this expression".to_owned();
            self.unresolved.push((e.span, what));
        }
        e.ty = self.ty(e.ty);
        if let Some(value) = self.consts.get(&e.id) {
            e.kind = ExprKind::Const(*value);
        }
        match &mut e.kind {
            ExprKind::Local(_) | ExprKind::Static(_) | ExprKind::Arrow(_) => {}
            ExprKind::Never | ExprKind::NullLit => {}
            ExprKind::Field(b, _)
            | ExprKind::Deref(b)
            | ExprKind::NarrowedPayload(b, _, _)
            | ExprKind::Repeat(b, _)
            | ExprKind::Unary(_, b)
            | ExprKind::Borrow(b)
            | ExprKind::AddrOf(b)
            | ExprKind::Try(b, _)
            | ExprKind::NonNull(b)
            | ExprKind::VoidOp(b) => self.expr(b),
            ExprKind::Cast(b, kind) => {
                self.expr(b);
                if let Some(k) = crate::typeck::cast::cast_kind(self.tcx, b.ty, e.ty) {
                    *kind = k;
                }
            }
            ExprKind::Index(a, b)
            | ExprKind::Binary(_, a, b)
            | ExprKind::Logical(_, a, b)
            | ExprKind::Coalesce(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            ExprKind::Const(v) => self.value(v),
            ExprKind::Template(parts) => {
                for part in parts {
                    if let TplPart::Hole(h) = part {
                        self.expr(h);
                    }
                }
            }
            ExprKind::ArrayLit(es) | ExprKind::TupleLit(es) => self.exprs(es),
            ExprKind::ArrayBuild { elem, parts } => {
                *elem = self.ty(*elem);
                for part in parts {
                    match part {
                        ArrayPart::Item(x) | ArrayPart::Spread(x, _) => self.expr(x),
                    }
                }
            }
            ExprKind::NewNamed { args, fields, .. } => {
                *args = self.list(*args);
                for (_, x) in fields {
                    self.expr(x);
                }
            }
            ExprKind::ObjectLit { fields, .. } => self.exprs(fields),
            ExprKind::VariantLit { args, fields, .. } => {
                *args = self.list(*args);
                self.exprs(fields);
            }
            ExprKind::New { args, values, .. } => {
                *args = self.list(*args);
                self.exprs(values);
            }
            ExprKind::Call {
                callee,
                receiver,
                args,
            } => {
                self.callee(callee);
                if let Some(r) = receiver {
                    self.expr(r);
                }
                self.exprs(args);
            }
            ExprKind::OptionalChain(chain) => {
                self.expr(&mut chain.base);
                if let OptMember::Call { callee, args } = &mut chain.member {
                    self.callee(callee);
                    self.exprs(args);
                }
            }
            ExprKind::Ternary(c, a, b) => {
                self.expr(c);
                self.expr(a);
                self.expr(b);
            }
            ExprKind::Assign { target, value, .. } => {
                self.expr(target);
                self.expr(value);
            }
            ExprKind::IncDec { target, .. } => self.expr(target),
            ExprKind::Match { subject, arms } => {
                self.expr(subject);
                for arm in arms {
                    for v in &mut arm.values {
                        self.arm_value(v);
                    }
                    if let Some(g) = &mut arm.guard {
                        self.expr(g);
                    }
                    match &mut arm.body {
                        ArmBody::Expr(x) => self.expr(x),
                        ArmBody::Block(b) => self.block(b),
                        ArmBody::Return(x) => {
                            if let Some(x) = x {
                                self.expr(x);
                            }
                        }
                        ArmBody::Break(_) | ArmBody::Continue(_) => {}
                    }
                }
            }
            ExprKind::Asm(asm) => {
                for (_, x) in &mut asm.ins {
                    self.expr(x);
                }
                for (_, x) in &mut asm.outs {
                    if let Some(x) = x {
                        self.expr(x);
                    }
                }
            }
            ExprKind::Destructure { pat, value } => {
                for place in pat.places_mut() {
                    self.expr(place);
                }
                self.expr(value);
            }
        }
    }
}
