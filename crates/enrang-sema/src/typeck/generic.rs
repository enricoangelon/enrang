//! Generic calls (plan d.9; SPEC 4.7 S:729-732, 4.10; A:888; owner 4A).
//!
//! A call instantiates its callee ([`Target`]): every parameter of the callee's
//! generics stands for a type, given (a receiver's arguments, a written instance,
//! explicit type arguments, all or none, else EN0309) or a fresh variable. Its
//! arguments are then typed in SPEC 4.7's three steps: step 1 unifies the call's
//! value type with the expected type as a hint; step 2 types the non-arrow
//! arguments left to right, each at its parameter (`&?T` against a non-reference
//! `U` binds `T := U` and is EN0612; against `&Slice<U>` binds `T := Slice<U>`; `?T`
//! against `&U` waits for the end of the call, then takes another binding, else
//! reads through a Copy `U`, else binds the reference, which is EN0703); step 3 types
//! the arrows at their substituted parameter types. When a non-arrow argument fits
//! neither as it is nor by a coercion, the hint is dropped and the call typed again
//! from its arguments alone, its value meeting its own coercion site (C21, C22);
//! when both ways fail, the errors reported are the hinted way's. Trying a way
//! without reporting is a [`Probe`]: the typing state is kept, diagnostics go to a
//! scratch buffer, and the way is then kept (its diagnostics re-emitted) or undone.
//!
//! An implicit parameter (D5) is bound by its argument: an interface one to the
//! argument's class behind one `&` and through a `Box` (C04), or to the interface
//! itself for a two-word `&I`; a shape one to the argument's type, or, for an object
//! literal, to the shape itself, which the literal is typed at (EN0434).
//!
//! Each type argument is checked once it is known (plan d.9): a reference is
//! EN0703, an interface type EN1006, any other type outside `V` (a borrowing
//! class, a reference-holding tuple) EN0701, then each bound (EN0419: class bounds
//! by name, `final` alone; `Copy`, `Error` nominal; `Clone` by `is_clone`;
//! `Display` always; sealed bounds by the compiler's table, `VolatileValue` EN0805
//! at the call; any other interface by 4D's satisfaction engine), and a method's
//! `where` clause at the call with the clause as the secondary (S:323). An implicit
//! interface parameter's class must satisfy the interface (EN0401, as C22 would
//! say), never be a `string` behind `&` (EN0401, S:631) or a borrowing class
//! (EN0701); an implicit shape parameter's type must have every field of the shape,
//! public, at its type (EN0401, S:601). A type argument still unknown at the end of
//! the call is checked once the body's defaults have applied (`Deferred::Bounds`,
//! [`FnCtxt::check_deferred_bounds`]), with the call as its primary span; an
//! unresolved written parameter is EN0410 `` cannot infer the type of `T` in
//! `make(...)` ``, while the error type of the prelude's `Ok` and of a `Result`
//! case literal left open is `Failure` (S:1139; plan choice of mechanism). Every
//! known binding is recorded for 4E's view and string facts (`ViewUses`).
//!
//! Written types in declarations are checked against the bounds of the classes
//! and enums they instantiate ([`check_decl_types`]): `dup<T>(a: &Atomic<T>)` is
//! EN0419 (T:612).

use std::collections::BTreeMap;

use enrang_base::{IdVec, Span, Symbol};
use enrang_diag::{Code, DiagCtx, Diagnostic, Edit, Help};
use enrang_hir::{
    self as hir, Adjust, AdtId, ArrowBody, ArrowId, BodyOwner, Bound, BoundId, Callee, DefId,
    DefKind, ExprId, ExprKind, FactId, FactInfo, FnRef, Implicit, LangItem, LocalDecl, LocalId,
    LoopId, NarrowRecord, OptChain, OptMember, ParamEnv, ParamId, RecordKind, Ty, TyKind, Vis,
};
use enrang_syntax::ast;

use crate::classes::satisfy;
use crate::cx::Sema;
use crate::lower::ItemAstKind;
use crate::passes::views::ViewUse;
use crate::resolve::scope::ScopeStack;
use crate::typeck::call::CallSite;
use crate::typeck::iface::iface_unsupported;
use crate::typeck::infer::{InferTable, VarKind};
use crate::typeck::narrow::{FlowState, Prescan};
use crate::typeck::ops::IntDivision;
use crate::typeck::{ArrowFrame, CallFrame, Deferred, Expect, FnCtxt, RetCtx, Site};

/// A callee as one call instantiates it.
#[derive(Clone, Debug)]
pub(crate) struct Target {
    pub def: DefId,
    /// Every parameter in scope of the callee's generics (`Tcx::all_params`), then,
    /// for an interface method, the interface's `Self`.
    pub params: Vec<ParamId>,
    /// What each parameter stands for at this call.
    pub args: Vec<Ty>,
    /// How many entries of `params` are `Tcx::all_params`'s.
    pub scope_len: usize,
    /// The first parameter this call binds and so checks: the callee's own, or its
    /// owner's too where the call instantiates the owner (a constructor's class is
    /// checked as an instance instead, an `extend` block's parameters per call).
    pub check_from: usize,
    /// The type of the call's value: the result, or a constructor's class.
    pub result: Ty,
    /// How messages name the callee (`f`, `push`, `User`).
    pub name: String,
    /// Explicit type arguments, each with the parameter it gives.
    pub explicit: Vec<(ParamId, Span)>,
}

/// A call's arguments as typed against one [`Target`].
pub(crate) struct Typed {
    pub args: Vec<hir::Expr>,
    /// Some non-arrow argument fitted its parameter neither as it is nor by a
    /// coercion; read only while probing, where nothing else was reported.
    pub misfit: bool,
    /// Some argument needed a coercion chain (overload step 2).
    pub chain: bool,
}

/// One non-arrow argument as step 2 left it.
enum ArgOut {
    Done(hir::Expr),
    /// `?T` against `&U`, coerced at the end of step 2.
    Pending(hir::Expr),
}

/// A way of typing being tried (module doc): the typing state as it was, and the
/// real diagnostics buffer, swapped out for a scratch one.
pub(crate) struct Probe {
    locals: IdVec<LocalId, LocalDecl>,
    arrows: IdVec<ArrowId, ArrowBody>,
    infer: InferTable,
    scopes: ScopeStack,
    flow: FlowState,
    facts: IdVec<FactId, FactInfo>,
    records: Vec<NarrowRecord>,
    loops: Vec<LoopId>,
    next_loop: u32,
    next_expr: u32,
    ret: RetCtx,
    arrow_stack: Vec<ArrowFrame>,
    deferred: Vec<Deferred>,
    unsafe_depth: u32,
    env: ParamEnv,
    init_annotation: Option<(Span, Span)>,
    init_name: Option<Symbol>,
    calls: Vec<CallFrame>,
    reachable: bool,
    broken: std::collections::BTreeSet<LoopId>,
    continued: std::collections::BTreeSet<LoopId>,
    pending_label: Option<Symbol>,
    labelled: Vec<LoopId>,
    depth: u32,
    param_defaults: Vec<(LocalId, hir::Expr)>,
    literal_values: std::collections::BTreeMap<ExprId, hir::ConstValue>,
    int_divisions: Vec<IntDivision>,
    arm_literals: std::collections::BTreeSet<ExprId>,
    arm_ranges: std::collections::BTreeSet<ExprId>,
    views: usize,
    satisfactions: usize,
    early: Vec<DefId>,
    outer: DiagCtx,
}

impl FnCtxt<'_, '_> {
    // ---------------------------------------------------------------------------
    // Probes.

    /// Starts trying a way of typing: the state is saved and diagnostics go to a
    /// scratch buffer until [`Self::commit`] or [`Self::rollback`].
    pub(crate) fn probe(&mut self) -> Probe {
        let mut outer = DiagCtx::new();
        std::mem::swap(self.sema.dcx, &mut outer);
        Probe {
            locals: self.locals.clone(),
            arrows: self.arrows.clone(),
            infer: self.infer.clone(),
            scopes: self.scopes.clone(),
            flow: self.flow.clone(),
            facts: self.facts.clone(),
            records: self.records.clone(),
            loops: self.loops.clone(),
            next_loop: self.next_loop,
            next_expr: self.next_expr,
            ret: self.ret,
            arrow_stack: self.arrow_stack.clone(),
            deferred: self.deferred.clone(),
            unsafe_depth: self.unsafe_depth,
            env: self.env.clone(),
            init_annotation: self.init_annotation,
            init_name: self.init_name,
            calls: self.calls.clone(),
            reachable: self.reachable,
            broken: self.broken.clone(),
            continued: self.continued.clone(),
            pending_label: self.pending_label,
            labelled: self.labelled.clone(),
            depth: self.depth,
            param_defaults: self.param_defaults.clone(),
            literal_values: self.literal_values.clone(),
            int_divisions: self.int_divisions.clone(),
            arm_literals: self.arm_literals.clone(),
            arm_ranges: self.arm_ranges.clone(),
            views: self.sema.views.uses.len(),
            satisfactions: self.sema.classes.satisfactions.len(),
            early: self.sema.early_consts.keys().copied().collect(),
            outer,
        }
    }

    /// Whether the way being tried reported an error.
    pub(crate) fn probe_failed(&self) -> bool {
        self.sema.dcx.has_errors()
    }

    /// Keeps the way tried: its state stays and its diagnostics are reported.
    pub(crate) fn commit(&mut self, mut p: Probe) {
        std::mem::swap(self.sema.dcx, &mut p.outer);
        for diag in p.outer.take() {
            self.sema.emit(diag);
        }
    }

    /// Undoes the way tried: the state is as it was and its diagnostics are gone.
    pub(crate) fn rollback(&mut self, mut p: Probe) {
        std::mem::swap(self.sema.dcx, &mut p.outer);
        self.locals = p.locals;
        self.arrows = p.arrows;
        self.infer = p.infer;
        self.scopes = p.scopes;
        self.flow = p.flow;
        self.facts = p.facts;
        self.records = p.records;
        self.loops = p.loops;
        self.next_loop = p.next_loop;
        self.next_expr = p.next_expr;
        self.ret = p.ret;
        self.arrow_stack = p.arrow_stack;
        self.deferred = p.deferred;
        self.unsafe_depth = p.unsafe_depth;
        self.env = p.env;
        self.init_annotation = p.init_annotation;
        self.init_name = p.init_name;
        self.calls = p.calls;
        self.reachable = p.reachable;
        self.broken = p.broken;
        self.continued = p.continued;
        self.pending_label = p.pending_label;
        self.labelled = p.labelled;
        self.depth = p.depth;
        self.param_defaults = p.param_defaults;
        self.literal_values = p.literal_values;
        self.int_divisions = p.int_divisions;
        self.arm_literals = p.arm_literals;
        self.arm_ranges = p.arm_ranges;
        self.sema.views.uses.truncate(p.views);
        // A satisfaction is recorded only where the way that used it is kept.
        self.sema.classes.satisfactions.truncate(p.satisfactions);
        // A constant typed on demand while probing is typed again at its turn, so
        // its diagnostics are not lost with the probe's.
        self.sema
            .early_consts
            .retain(|def, _| p.early.contains(def));
    }

    // ---------------------------------------------------------------------------
    // The seam.

    /// A call to `f` that is generic, overloaded, given type arguments or bound by
    /// a `where` clause (plan d.9): the target, the three steps with the hint
    /// retry, the type arguments checked, and the call expression built.
    pub(crate) fn check_generic_call(
        &mut self,
        f: DefId,
        call: &CallSite,
        ex: Expect,
    ) -> hir::Expr {
        let target = self.call_target(f, call);
        let typed = self.infer_call(&target, call.args, ex, call.expr.span);
        self.finish_call(&target, typed, call)
    }

    /// `f` as `call` instantiates it.
    pub(crate) fn call_target(&mut self, f: DefId, call: &CallSite) -> Target {
        let owner_args: Option<Vec<Ty>> = call
            .methods
            .iter()
            .find(|m| m.def == f)
            .map(|m| self.sema.tcx.list(m.args).to_vec())
            .or_else(|| (!call.owner_args.is_empty()).then(|| call.owner_args.clone()));
        let name = self.callee_name(f);
        let mut target = self.make_target(
            f,
            owner_args.as_deref(),
            call.at,
            call.type_args,
            &name,
            call.expr.span,
        );
        let tcx = &*self.sema.tcx;
        let in_extend = tcx
            .def(f)
            .parent
            .is_some_and(|p| tcx.extends().iter().any(|e| e.def == p));
        if owner_args.is_none() || in_extend {
            target.check_from = 0;
        }
        target
    }

    /// The callee's name as messages give it: a constructor's class's.
    pub(crate) fn callee_name(&self, f: DefId) -> String {
        let tcx = &*self.sema.tcx;
        let data = tcx.def(f);
        match data.kind {
            DefKind::Ctor => data
                .parent
                .and_then(|p| tcx.def(p).name())
                .map_or_else(String::new, |n| n.as_str().to_owned()),
            _ => data
                .name()
                .map_or_else(String::new, |n| n.as_str().to_owned()),
        }
    }

    /// `def` instantiated: its owner's parameters at `owner_args` (fresh variables
    /// when `None`), its own at `explicit` (all or none, EN0309) or fresh
    /// variables, and an interface's `Self` at `self_ty`.
    pub(crate) fn make_target(
        &mut self,
        def: DefId,
        owner_args: Option<&[Ty]>,
        self_ty: Option<Ty>,
        explicit: &[ast::TypeExpr],
        name: &str,
        span: Span,
    ) -> Target {
        let error = self.error_ty();
        let Some(sig) = self.sema.tcx.sig_opt(def).cloned() else {
            return Target {
                def,
                params: Vec::new(),
                args: Vec::new(),
                scope_len: 0,
                check_from: 0,
                result: error,
                name: name.to_owned(),
                explicit: Vec::new(),
            };
        };
        let tcx = &*self.sema.tcx;
        let generics = tcx.generics(sig.generics).clone();
        let parent = generics
            .parent
            .map(|p| tcx.all_params(p))
            .unwrap_or_default();
        let own = generics.params.clone();
        let mut params = parent.clone();
        params.extend(own.iter().copied());
        let mut args = Vec::with_capacity(params.len());
        match owner_args {
            Some(given) if given.len() == parent.len() => args.extend_from_slice(given),
            _ => {
                for &p in &parent {
                    let var = self.param_var(def, p, name, span);
                    args.push(var);
                }
            }
        }
        let written: Vec<ParamId> = own
            .iter()
            .copied()
            .filter(|&p| self.sema.tcx.param(p).implicit.is_none())
            .collect();
        let mut given: Vec<Option<Ty>> = vec![None; own.len()];
        let mut explicit_at = Vec::new();
        if !explicit.is_empty() {
            if explicit.len() == written.len() {
                for (t, &p) in explicit.iter().zip(&written) {
                    let ty = self.lower_ty(t);
                    if let Some(i) = own.iter().position(|&q| q == p) {
                        given[i] = Some(ty);
                    }
                    explicit_at.push((p, t.span));
                }
            } else {
                let first = explicit[0].span;
                let last = explicit[explicit.len() - 1].span;
                let n = written.len();
                let plural = if n == 1 { "" } else { "s" };
                let were = if explicit.len() == 1 { "was" } else { "were" };
                self.sema.emit(Diagnostic::new(
                    Code::EN0309,
                    format!(
                        "`{name}` takes {n} type argument{plural}, but {} {were} given",
                        explicit.len()
                    ),
                    first.to(last),
                    format!("expected {n} type argument{plural}"),
                ));
            }
        }
        for (i, &p) in own.iter().enumerate() {
            let ty = match given[i] {
                Some(t) => t,
                None => self.param_var(def, p, name, span),
            };
            args.push(ty);
        }
        let scope_len = params.len();
        let tcx = &*self.sema.tcx;
        if let Some(self_ty) = self_ty
            && let Some(parent) = tcx.def(def).parent
            && let Some(adt) = tcx.adt_of(parent)
            && let Some(iface) = tcx.adt(adt).as_interface()
        {
            params.push(iface.self_param);
            args.push(self_ty);
        }
        let result = match tcx.def(def).kind {
            DefKind::Ctor => match tcx.def(def).parent.and_then(|p| tcx.adt_of(p)) {
                Some(adt) => self.class_ty(adt, &args[..parent.len()]),
                None => error,
            },
            _ => tcx.subst(sig.ret, &params, &args),
        };
        Target {
            def,
            params,
            args,
            scope_len,
            check_from: parent.len(),
            result,
            name: name.to_owned(),
            explicit: explicit_at,
        }
    }

    /// A fresh variable for parameter `p` of `def` at a call: a written one is
    /// EN0410 if nothing decides it; an implicit one, and the error type of the
    /// prelude's `Ok` (which defaults to `Failure`), report nothing of their own.
    fn param_var(&mut self, def: DefId, p: ParamId, name: &str, span: Span) -> Ty {
        let tcx = &*self.sema.tcx;
        let data = tcx.param(p);
        let quiet = data.implicit.is_some() || self.defaults_to_failure(def, p);
        if quiet {
            let var = self.infer.fresh(VarKind::Any);
            return self.sema.tcx.intern_ty(TyKind::Infer(var));
        }
        let what = format!("`{}` in `{name}(...)`", data.name);
        self.new_var(VarKind::Any, span, what)
    }

    /// Whether `p` of `def` is an error type that defaults to `Failure` when
    /// nothing decides it: `E` of the prelude's `Ok` functions and of `Result`
    /// itself (S:1139; plan choice of mechanism).
    pub(crate) fn defaults_to_failure(&self, def: DefId, p: ParamId) -> bool {
        let tcx = &*self.sema.tcx;
        let Some(result) = tcx.lang_adt(LangItem::Result) else {
            return false;
        };
        if tcx.adt_of(def) == Some(result) {
            let params = &tcx.generics(tcx.adt(result).generics).params;
            return params.get(1) == Some(&p);
        }
        let Some(ok) = tcx.lang_opt(LangItem::Ok) else {
            return false;
        };
        let data = tcx.def(def);
        if def != ok && (data.module != tcx.def(ok).module || data.name() != tcx.def(ok).name()) {
            return false;
        }
        let Some(sig) = tcx.sig_opt(def) else {
            return false;
        };
        match tcx.kind(sig.ret) {
            TyKind::Adt(adt, args) if adt == result => {
                tcx.list(args).get(1).copied() == Some(tcx.mk_param(p))
            }
            _ => false,
        }
    }

    /// Class `adt` at `args`, a lang class normalised to its kind (A:758).
    pub(crate) fn class_ty(&self, adt: AdtId, args: &[Ty]) -> Ty {
        let tcx = &*self.sema.tcx;
        let first = args.first().copied().unwrap_or(tcx.common().error);
        match tcx.lang_item_of(tcx.adt(adt).def) {
            Some(LangItem::Str) => tcx.common().str,
            Some(LangItem::Slice) => tcx.mk_slice(first),
            Some(LangItem::Array) => tcx.mk_array(first),
            Some(LangItem::Boxed) => tcx.mk_box(first),
            _ => tcx.mk_adt(adt, args),
        }
    }

    // ---------------------------------------------------------------------------
    // The three steps.

    /// Types `args` against `target` with the hint and its retry (S:729).
    pub(crate) fn infer_call(
        &mut self,
        target: &Target,
        args: &[ast::Expr],
        ex: Expect,
        span: Span,
    ) -> Typed {
        let hint = ex.ty().filter(|_| self.holds_var(target.result));
        let Some(hint) = hint else {
            return self.type_args(target, args, None, span);
        };
        let p = self.probe();
        let hinted = self.type_args(target, args, Some(hint), span);
        if !hinted.misfit {
            self.commit(p);
            return hinted;
        }
        self.rollback(p);
        let p = self.probe();
        let alone = self.type_args(target, args, None, span);
        let fits = !self.probe_failed() && self.result_fits(target.result, ex);
        if fits {
            self.commit(p);
            return alone;
        }
        self.rollback(p);
        self.type_args(target, args, Some(hint), span)
    }

    /// Whether `t` still holds a variable.
    fn holds_var(&self, t: Ty) -> bool {
        let t = self.resolve(t);
        self.sema.tcx.has_infer(t)
    }

    /// Whether a value of type `t` meets `ex` at its coercion site; nothing changes.
    /// A hint with no site (C19's `Has(Result<...>)`) is met unless `t` is an
    /// instance of the hint's own class or enum that does not convert to it: a
    /// leaf of another type may still be wrapped by its context (`Ok(x)` from `x`),
    /// but `Ok(5)` at `Result<string>` keeps the hinted typing, whose error wins
    /// (S:730).
    fn result_fits(&mut self, t: Ty, ex: Expect) -> bool {
        let (to, site) = match ex {
            Expect::Coerce(to, site) => (to, site),
            Expect::Has(to) => {
                let (t, to) = (self.shallow(t), self.shallow(to));
                match (self.sema.tcx.kind(t), self.sema.tcx.kind(to)) {
                    (TyKind::Adt(a, _), TyKind::Adt(b, _)) if a == b => (to, Site::Init),
                    _ => return true,
                }
            }
            Expect::None => return true,
        };
        let p = self.probe();
        let value = self.mk_expr(t, Span::DUMMY, ExprKind::Never);
        let _ = self.coerce(value, to, site);
        let ok = !self.probe_failed();
        self.rollback(p);
        ok
    }

    /// The three steps over `args` against `target`, `hint` first if any.
    pub(crate) fn type_args(
        &mut self,
        target: &Target,
        args: &[ast::Expr],
        hint: Option<Ty>,
        span: Span,
    ) -> Typed {
        let tcx = &*self.sema.tcx;
        let sig = tcx.sig_opt(target.def).cloned();
        let params: Vec<(Ty, bool, Ty)> = sig
            .as_ref()
            .map(|s| {
                s.params
                    .iter()
                    .map(|p| {
                        (
                            tcx.subst(p.ty, &target.params, &target.args),
                            p.has_default,
                            p.ty,
                        )
                    })
                    .collect()
            })
            .unwrap_or_default();
        let required = params.iter().filter(|p| !p.1).count();
        if sig.is_some() && (args.len() < required || args.len() > params.len()) {
            self.arity_error(
                &target.name,
                required,
                params.len(),
                args.len(),
                span,
                Some(target.def),
            );
        }
        // Step 1: the hint.
        if let Some(hint) = hint {
            let hint = self.shallow(hint);
            if !self.unify(target.result, hint)
                && let TyKind::Nullable(payload) = self.sema.tcx.kind(hint)
            {
                let _ = self.unify(target.result, payload);
            }
        }
        // Step 2: non-arrow arguments, left to right; one that passes an arrow
        // through a ternary, `??` or `match` prescans the call's arrows first.
        let before = self.sema.dcx.has_errors();
        let mut typed: Vec<Option<hir::Expr>> = vec![None; args.len()];
        let mut pending = Vec::new();
        let mut prescanned = false;
        for (i, arg) in args.iter().enumerate() {
            if is_arrow(arg) {
                continue;
            }
            if !prescanned && crate::typeck::narrow::holds_arrow(arg) {
                prescanned = true;
                self.prescan_kill(Prescan::Arrows(args));
            }
            let out = match params.get(i) {
                Some(&(p, _, declared)) => self.step_arg(arg, p, declared, target),
                None => ArgOut::Done(self.check_expr(arg, Expect::None)),
            };
            match out {
                ArgOut::Done(e) => typed[i] = Some(e),
                ArgOut::Pending(e) => pending.push((i, e)),
            }
        }
        // `?T` against `&U`: another binding, else a Copy read-through.
        for (i, e) in pending {
            let p = params[i].0;
            let var = self.shallow(p);
            if self.var_kind(var) == Some(VarKind::Any)
                && let TyKind::Ref(u) = self.sema.tcx.kind(self.shallow(e.ty))
                && self.copy_now(u)
            {
                let _ = self.unify(var, u);
            }
            typed[i] = Some(self.coerce(e, p, Site::Arg));
        }
        let misfit = self.sema.dcx.has_errors() && !before;
        // Step 3: arrows, at their substituted parameter types.
        for (i, arg) in args.iter().enumerate() {
            if !is_arrow(arg) {
                continue;
            }
            if !prescanned {
                prescanned = true;
                self.prescan_kill(Prescan::Arrows(args));
            }
            let e = match params.get(i) {
                Some(&(p, _, _)) => {
                    let p = self.resolve(p);
                    self.check_expr(arg, Expect::Coerce(p, Site::Arg))
                }
                None => self.check_expr(arg, Expect::None),
            };
            typed[i] = Some(e);
        }
        let args: Vec<hir::Expr> = typed.into_iter().flatten().collect();
        for e in &args {
            self.record_ref(e, RecordKind::CallArg);
        }
        let chain = args
            .iter()
            .any(|e| e.adjust.iter().any(|a| *a != Adjust::NeverToAny));
        Typed {
            args,
            misfit,
            chain,
        }
    }

    /// One non-arrow argument at parameter type `p` (`declared` before
    /// substitution).
    fn step_arg(&mut self, arg: &ast::Expr, p: Ty, declared: Ty, target: &Target) -> ArgOut {
        if let Some((x, behind_ref, implicit)) = self.implicit_of(declared) {
            let var = self.shallow(self.sema.tcx.subst(
                self.sema.tcx.mk_param(x),
                &target.params,
                &target.args,
            ));
            return ArgOut::Done(self.implicit_arg(arg, p, var, behind_ref, implicit, target));
        }
        let p_now = self.shallow(p);
        if let TyKind::Ref(inner) = self.sema.tcx.kind(p_now)
            && self.var_kind(inner) == Some(VarKind::Any)
        {
            // `&?T` against a non-reference `U` binds `T := U`; the coercion then
            // reports the missing `&` (EN0612).
            let e = self.check_expr(arg, Expect::Has(p));
            let t = self.shallow(e.ty);
            let tcx = &*self.sema.tcx;
            if !matches!(tcx.kind(t), TyKind::Ref(_) | TyKind::Error | TyKind::Never)
                && self.var_kind(t) != Some(VarKind::Any)
            {
                let _ = self.unify(inner, t);
            }
            return ArgOut::Done(self.coerce(e, p, Site::Arg));
        }
        if self.var_kind(p_now) == Some(VarKind::Any) {
            let e = self.check_expr(arg, Expect::Has(p));
            if matches!(self.sema.tcx.kind(self.shallow(e.ty)), TyKind::Ref(_)) {
                return ArgOut::Pending(e);
            }
            return ArgOut::Done(self.coerce(e, p, Site::Arg));
        }
        ArgOut::Done(self.check_expr(arg, Expect::Coerce(p, Site::Arg)))
    }

    /// The implicit parameter (D5) a declared parameter type `X` or `&X` names, with
    /// whether it is behind `&`.
    fn implicit_of(&self, declared: Ty) -> Option<(ParamId, bool, Implicit)> {
        let tcx = &*self.sema.tcx;
        let (inner, behind_ref) = match tcx.kind(declared) {
            TyKind::Ref(inner) => (inner, true),
            _ => (declared, false),
        };
        let TyKind::Param(x) = tcx.kind(inner) else {
            return None;
        };
        let implicit = tcx.param(x).implicit?;
        match implicit {
            Implicit::Interface(_) | Implicit::Shape(_) => Some((x, behind_ref, implicit)),
            Implicit::Opaque => None,
        }
    }

    /// An argument at an implicit parameter (module doc).
    fn implicit_arg(
        &mut self,
        arg: &ast::Expr,
        p: Ty,
        var: Ty,
        behind_ref: bool,
        implicit: Implicit,
        target: &Target,
    ) -> hir::Expr {
        if let Implicit::Shape(shape) = implicit
            && is_object_literal(arg)
        {
            let tcx = &*self.sema.tcx;
            // The shape's fields name the callee's type parameters: at this call,
            // their arguments (fix-5).
            let shape_ty = tcx.subst(
                tcx.intern_ty(TyKind::Object(shape)),
                &target.params,
                &target.args,
            );
            let at = if behind_ref {
                tcx.mk_ref(shape_ty)
            } else {
                shape_ty
            };
            let _ = self.unify(var, shape_ty);
            return self.check_expr(arg, Expect::Coerce(at, Site::Arg));
        }
        // A by-value `I` takes a whole argument of one class (4C, VI-03-branches).
        let branches = match implicit {
            Implicit::Interface(iface) if !behind_ref => {
                let callee = self.calls.last().and_then(|frame| frame.callee);
                self.by_value_iface_arg(arg, iface, callee)
            }
            _ => None,
        };
        let e = match branches {
            Some(e) => e,
            None => self.check_expr(arg, Expect::Has(p)),
        };
        let t = self.shallow(e.ty);
        let tcx = &*self.sema.tcx;
        let inner = match (behind_ref, tcx.kind(t)) {
            // C04 for a `Box<I>` alone (S:672's C22 row): `&Box<Speaker>` passes
            // the interface value. `&Box<C>` binds `Box<C>`, never `C`: C04 then
            // C22 would be two reference steps at one site (S:656).
            (true, TyKind::Ref(u)) => {
                let u = self.shallow(u);
                match (implicit, tcx.kind(u)) {
                    (Implicit::Interface(_), TyKind::Boxed(v))
                        if tcx.is_interface_ty(self.shallow(v)) =>
                    {
                        Some(self.shallow(v))
                    }
                    _ => Some(u),
                }
            }
            (true, _) => None,
            (false, TyKind::Ref(_)) => None,
            (false, _) => Some(t),
        };
        if let Some(inner) = inner
            && self.var_kind(var) == Some(VarKind::Any)
            && self.var_kind(inner) != Some(VarKind::Any)
        {
            let _ = self.unify(var, inner);
            // A shape's field types bind the callee's type parameters they name
            // (`show<T>(o: &{ v: T })` at a `{ v: i64 }` binds `T := i64`).
            if let Implicit::Shape(shape) = implicit {
                let want = self.sema.tcx.shape(shape).fields.clone();
                let (have, _) = self.public_fields(inner);
                for (name, want_ty) in want {
                    if let Some(&(_, have_ty)) = have.iter().find(|(n, _)| *n == name) {
                        let want_ty = self.sema.tcx.subst(want_ty, &target.params, &target.args);
                        let _ = self.unify(want_ty, have_ty);
                    }
                }
            }
        }
        self.coerce(e, p, Site::Arg)
    }

    /// The public fields of an object type or a class, at their types, and the
    /// names of a class's private ones.
    fn public_fields(&self, t: Ty) -> (Vec<(Symbol, Ty)>, Vec<Symbol>) {
        let tcx = &*self.sema.tcx;
        match tcx.kind(self.shallow(t)) {
            TyKind::Object(s) => (tcx.shape(s).fields.clone(), Vec::new()),
            TyKind::Adt(adt, args) => match tcx.adt(adt).as_class() {
                Some(class) => {
                    let mut have = Vec::new();
                    let mut private = Vec::new();
                    for (i, f) in class.fields.iter().enumerate() {
                        if f.vis == Vis::Public {
                            have.push((
                                f.name,
                                tcx.field_ty(adt, None, hir::FieldIdx(i as u32), args),
                            ));
                        } else {
                            private.push(f.name);
                        }
                    }
                    (have, private)
                }
                None => (Vec::new(), Vec::new()),
            },
            _ => (Vec::new(), Vec::new()),
        }
    }

    /// Whether `t`, resolved, is Copy: a number variable is.
    fn copy_now(&self, t: Ty) -> bool {
        let t = self.resolve(t);
        if matches!(self.var_kind(t), Some(VarKind::Int | VarKind::Float)) {
            return true;
        }
        !self.sema.tcx.has_infer(t) && self.sema.tcx.is_copy(t, &self.env)
    }

    // ---------------------------------------------------------------------------
    // The call built.

    /// The call expression for `target` with its typed arguments; the type
    /// arguments checked.
    fn finish_call(&mut self, target: &Target, typed: Typed, call: &CallSite) -> hir::Expr {
        let span = call.expr.span;
        let refused = self.check_call_type_args_refused(target, call.args, span);
        let f = target.def;
        let tcx = &*self.sema.tcx;
        let inst = tcx.intern_list(&target.args[..target.scope_len]);
        let is_super = matches!(
            &call.expr.kind,
            ast::ExprKind::Call { callee, .. }
                if matches!(&callee.kind, ast::ExprKind::Member { base, .. } if matches!(base.kind, ast::ExprKind::Super))
        );
        let member = match &call.expr.kind {
            ast::ExprKind::Call { callee, .. } => match &callee.kind {
                ast::ExprKind::Member { name, .. } => Some(name.name),
                _ => None,
            },
            _ => None,
        };
        let bound_param = call.at.and_then(|at| match tcx.kind(self.shallow(at)) {
            TyKind::Param(p) => Some(p),
            _ => None,
        });
        let callee = if is_super {
            Callee::Super(FnRef { def: f, args: inst })
        } else if let (Some(param), Some(member)) = (bound_param, member) {
            let owner = call
                .methods
                .iter()
                .find(|m| m.def == f)
                .map_or_else(|| tcx.empty_list(), |m| m.args);
            // The owner's arguments, then the method's own at this call, so the
            // callee names every parameter of its generics, as a class method's
            // `FnRef` does (A:562: the text form round-trips them).
            let own = tcx
                .sig_opt(f)
                .map_or(0, |sig| tcx.generics(sig.generics).params.len())
                .min(target.scope_len);
            let mut args = tcx.list(owner).to_vec();
            args.extend_from_slice(&target.args[target.scope_len - own..target.scope_len]);
            Callee::BoundMember {
                param,
                member,
                found: f,
                args: tcx.intern_list(&args),
            }
        } else {
            self.callee_of(f, inst)
        };
        // A result built from a refused type argument is `Error`: the one report
        // stands, and no position check repeats it at a local (one per mistake).
        let declared_ret = self.sema.tcx.sig_opt(f).map(|sig| sig.ret);
        let from_refused = declared_ret.is_some_and(|r| {
            self.sema.tcx.any_ty(
                r,
                &mut |tcx, t| matches!(tcx.kind(t), TyKind::Param(q) if refused.contains(&q)),
            )
        });
        let ret = if from_refused {
            self.error_ty()
        } else {
            target.result
        };
        if call.optional {
            let tcx = &*self.sema.tcx;
            let shown = self.shallow(ret);
            let (ty, void_result) = match tcx.kind(shown) {
                TyKind::Void => (ret, true),
                TyKind::Nullable(_) | TyKind::Error => (ret, false),
                _ => (tcx.mk_nullable(ret), false),
            };
            let base = call
                .receiver
                .clone()
                .unwrap_or_else(|| self.error_expr(span));
            return self.mk_expr(
                ty,
                span,
                ExprKind::OptionalChain(Box::new(OptChain {
                    base,
                    member: OptMember::Call {
                        callee,
                        args: typed.args,
                    },
                    void_result,
                })),
            );
        }
        // The candidate run decides whether its receiver upcasts (C21, A:4).
        let receiver = call.receiver.clone().map(|mut r| {
            if let Some(at) = call.at {
                self.upcast_inherited(&mut r, at, f);
            }
            Box::new(r)
        });
        let e = self.mk_expr(
            ret,
            span,
            ExprKind::Call {
                callee,
                receiver,
                args: typed.args,
            },
        );
        self.record_hidden_args(f, &e);
        e
    }

    /// The `where` clause and, for a method of an `extend` block, the block's
    /// parameters, at a call of non-generic method `def` whose owner's arguments
    /// are `owner_args` (plan d.9; called by `call.rs`'s one-candidate path).
    pub(crate) fn check_call_bounds(&mut self, def: DefId, owner_args: &[Ty], call: &ast::Expr) {
        let tcx = &*self.sema.tcx;
        let Some(sig) = tcx.sig_opt(def) else {
            return;
        };
        let in_extend = tcx
            .def(def)
            .parent
            .is_some_and(|p| tcx.extends().iter().any(|e| e.def == p));
        if sig.where_bounds.is_empty() && !in_extend {
            return;
        }
        let params = tcx.all_params(sig.generics);
        if params.len() != owner_args.len() {
            return;
        }
        let target = Target {
            def,
            params,
            args: owner_args.to_vec(),
            scope_len: owner_args.len(),
            check_from: if in_extend { 0 } else { owner_args.len() },
            result: sig.ret,
            name: self.callee_name(def),
            explicit: Vec::new(),
        };
        let args: &[ast::Expr] = match &call.kind {
            ast::ExprKind::Call { args, .. } => args,
            _ => &[],
        };
        self.check_call_type_args(&target, args, call.span);
    }

    // ---------------------------------------------------------------------------
    // Type arguments.

    /// Checks every type argument `target` binds that is known now, its `where`
    /// clause too, and leaves each of the rest to the end of the body: one
    /// `Deferred::Bounds` per such argument, the others `Error` in it, whose span is
    /// where its diagnostics point (the argument that binds it, else the call).
    pub(crate) fn check_call_type_args(&mut self, target: &Target, args: &[ast::Expr], span: Span) {
        let _ = self.check_call_type_args_refused(target, args, span);
    }

    /// [`Self::check_call_type_args`], returning the parameters whose type argument
    /// was refused outright (a reference, an interface or a borrowing type: EN0703,
    /// EN1006, EN0701), so the call's result can stop there.
    fn check_call_type_args_refused(
        &mut self,
        target: &Target,
        args: &[ast::Expr],
        span: Span,
    ) -> Vec<ParamId> {
        let mut refused = Vec::new();
        let error = self.error_ty();
        let where_params: Vec<ParamId> = self
            .sema
            .tcx
            .sig_opt(target.def)
            .map(|s| s.where_bounds.iter().map(|(p, _)| *p).collect())
            .unwrap_or_default();
        for i in 0..target.scope_len {
            let p = target.params[i];
            let t = self.resolve(target.args[i]);
            let checked = i >= target.check_from;
            let in_where = where_params.contains(&p);
            if !checked && !in_where {
                continue;
            }
            let primary = match checked {
                true => self.arg_span(target, p, args, span),
                false => span,
            };
            if self.sema.tcx.has_infer(t) || self.bound_waits(p, (&target.params, &target.args)) {
                let mut slots = vec![error; target.scope_len];
                slots[i] = target.args[i];
                self.deferred.push(Deferred::Bounds {
                    span: primary,
                    callee: target.def,
                    args: slots,
                });
                continue;
            }
            if checked {
                if self.check_type_arg(
                    target.def,
                    p,
                    t,
                    primary,
                    args,
                    span,
                    (&target.params, &target.args),
                ) {
                    refused.push(p);
                }
                self.record_view_use(target.def, p, t, span);
            }
            if in_where {
                self.check_where(target.def, p, t, span);
            }
        }
        refused
    }

    /// The checks of a call's type arguments that waited for the end of inference
    /// (`Deferred::Bounds`, run by `finish` after the defaults): `Ok`'s open error
    /// type becomes `Failure`, then each argument the entry holds is checked, its
    /// diagnostics at `span` (plan choice: a `where` clause or volatile access whose
    /// type argument waited reports there too, not at the whole call).
    pub(crate) fn check_deferred_bounds(&mut self, span: Span, callee: DefId, args: &[Ty]) {
        let (params, where_params) = self.generics_of(callee);
        for (i, &p) in params.iter().enumerate() {
            let Some(&arg) = args.get(i) else {
                break;
            };
            if self.defaults_to_failure(callee, p)
                && self.var_kind(arg) == Some(VarKind::Any)
                && let Some(failure) = self.sema.tcx.lang_adt(LangItem::Failure)
            {
                let failure = self.sema.tcx.mk_adt(failure, &[]);
                let _ = self.unify(arg, failure);
            }
            let t = self.resolve(arg);
            if self.sema.tcx.references_error(t) || self.sema.tcx.has_infer(t) {
                continue;
            }
            self.check_type_arg(callee, p, t, span, &[], span, (&params, args));
            self.record_view_use(callee, p, t, span);
            if where_params.contains(&p) {
                self.check_where(callee, p, t, span);
            }
        }
    }

    /// The parameters in scope of `def`'s generics (a function's, or a class's or
    /// enum's for an instance) and those its `where` clause bounds.
    fn generics_of(&self, def: DefId) -> (Vec<ParamId>, Vec<ParamId>) {
        let tcx = &*self.sema.tcx;
        if let Some(sig) = tcx.sig_opt(def) {
            return (
                tcx.all_params(sig.generics),
                sig.where_bounds.iter().map(|(p, _)| *p).collect(),
            );
        }
        match tcx.adt_of(def) {
            Some(adt) => (tcx.all_params(tcx.adt(adt).generics), Vec::new()),
            None => (Vec::new(), Vec::new()),
        }
    }

    /// Where a type argument's diagnostic points: its explicit type argument, else
    /// the first argument whose parameter mentions it, else the call.
    fn arg_span(&self, target: &Target, p: ParamId, args: &[ast::Expr], span: Span) -> Span {
        if let Some((_, at)) = target.explicit.iter().find(|(q, _)| *q == p) {
            return *at;
        }
        let tcx = &*self.sema.tcx;
        let Some(sig) = tcx.sig_opt(target.def) else {
            return span;
        };
        let param = tcx.mk_param(p);
        sig.params
            .iter()
            .zip(args)
            .find(|(sp, _)| tcx.any_ty(sp.ty, &mut |_, t| t == param))
            .map_or(span, |(_, a)| a.span)
    }

    /// Records a binding for 4E's view and string facts.
    fn record_view_use(&mut self, callee: DefId, param: ParamId, arg: Ty, span: Span) {
        if self.sema.tcx.param(param).implicit.is_some() {
            return;
        }
        self.sema.views.uses.push(ViewUse {
            caller: self.owner,
            span,
            callee,
            param,
            arg,
        });
    }

    /// One known type argument `t` for parameter `p` of `callee` (module doc);
    /// `true` when `t` is refused outright (EN0703, EN1006, EN0701).
    #[allow(clippy::too_many_arguments)]
    fn check_type_arg(
        &mut self,
        callee: DefId,
        p: ParamId,
        t: Ty,
        primary: Span,
        args: &[ast::Expr],
        call: Span,
        subst: (&[ParamId], &[Ty]),
    ) -> bool {
        let tcx = &*self.sema.tcx;
        if tcx.references_error(t) {
            return false;
        }
        let pdef = tcx.param(p).clone();
        match pdef.implicit {
            Some(Implicit::Interface(iface)) => {
                self.check_implicit_iface((callee, p, iface), &pdef.bounds, t, (primary, call));
                return false;
            }
            Some(Implicit::Shape(shape)) => {
                // By value, C20's class must be a value type (S:678, A:892).
                let tcx = &*self.sema.tcx;
                if !self.implicit_behind_ref(callee, p) && !tcx.is_value_type(t) {
                    let shown = self.ty_str(t);
                    let shape_shown = tcx.ty_string(tcx.intern_ty(TyKind::Object(shape)));
                    self.sema.emit(Diagnostic::new(
                        Code::EN0701,
                        format!(
                            "{} `{shape_shown}` can't hold {} `{shown}`, because `{shown}` holds a reference",
                            crate::classes::sig::article(&shape_shown),
                            crate::classes::sig::article(&shown)
                        ),
                        primary,
                        "only a value type is passed by value as an object type",
                    ));
                    return true;
                }
                self.check_implicit_shape(shape, t, primary, subst);
                return false;
            }
            Some(Implicit::Opaque) => return false,
            None => {}
        }
        let name = pdef.name;
        let shown = self.ty_str(t);
        let tcx = &*self.sema.tcx;
        let reference = match tcx.kind(t) {
            TyKind::Ref(_) => true,
            TyKind::Nullable(inner) => matches!(tcx.kind(inner), TyKind::Ref(_)),
            _ => false,
        };
        if reference {
            let mut diag = Diagnostic::new(
                Code::EN0703,
                format!("`{name}` can't stand for the reference `{shown}`"),
                primary,
                format!("this makes `{name}` the reference `{shown}`"),
            );
            diag = self.nullable_method_help(diag, callee, args, call);
            self.sema.emit(diag);
            return true;
        }
        // `Box<I>` is the one constructor that takes an interface (S:560).
        let boxed_iface =
            tcx.lang_item_of(pdef.owner) == Some(LangItem::Boxed) && tcx.is_interface_ty(t);
        if tcx.is_interface_ty(t) && !boxed_iface {
            // SPEC 16's head, with A:894's helps for `&*b` arguments (4C).
            let diag = self.iface_type_arg(callee, call, args, t, primary);
            self.sema.emit(diag);
            return true;
        }
        if !tcx.is_value_type(t) && !matches!(tcx.kind(t), TyKind::Slice(_)) && !boxed_iface {
            self.sema.emit(Diagnostic::new(
                Code::EN0701,
                format!(
                    "`{name}` can't stand for {} `{shown}`, because `{shown}` holds a reference",
                    crate::classes::sig::article(&shown)
                ),
                primary,
                "no generic argument can hold a reference",
            ));
            return true;
        }
        for b in pdef.bounds.clone() {
            if self.meets_bound_at(t, b, subst) {
                continue;
            }
            self.bound_failed_at(p, b, t, primary, call, None, subst);
            return false;
        }
        for b in pdef.bounds {
            self.satisfy_bound(t, b, subst, call);
        }
        false
    }

    /// A bound `b` that `t` met at `site`, a call or instance whose generic's
    /// parameters stand for `subst`'s arguments, given to the one satisfaction
    /// routine (`satisfy::satisfy`, SPEC 4.4), which records what it relied on.
    fn satisfy_bound(&mut self, t: Ty, b: BoundId, subst: (&[ParamId], &[Ty]), site: Span) {
        let tcx = &*self.sema.tcx;
        if tcx.references_error(t) {
            return;
        }
        let args = self.bound_args_at(b, subst);
        let tcx = &*self.sema.tcx;
        let iface = tcx.mk_adt(tcx.bound(b).adt(), &args);
        let _ = satisfy::satisfy(self.sema, t, iface, &self.env, site);
    }

    /// The fix-it of EN0703 for a method of `T | null` called on a nullable
    /// reference (S:1387, T:625): `t.isNull()` is `t == null`, and `t.orElse(() =>
    /// d)` is `t ?? d`.
    fn nullable_method_help(
        &self,
        diag: Diagnostic,
        callee: DefId,
        args: &[ast::Expr],
        call: Span,
    ) -> Diagnostic {
        let tcx = &*self.sema.tcx;
        let Some(name) = tcx.def(callee).name() else {
            return diag;
        };
        let text = self.snippet(call);
        let Some(at) = text.rfind(&format!(".{name}(")) else {
            return diag;
        };
        let recv = &text[..at];
        let (help, fixed) = match (name.as_str(), args) {
            ("isNull", []) => ("compare with `null`", format!("{recv} == null")),
            ("orElse", [d]) => {
                let value = match &strip_parens(d).kind {
                    ast::ExprKind::Arrow(arrow) if arrow.params.is_empty() => match &arrow.body {
                        ast::ArrowBody::Expr(body) => self.snippet(body.span),
                        ast::ArrowBody::Block(_) => format!("({})()", self.snippet(d.span)),
                    },
                    _ => format!("{}()", self.snippet(d.span)),
                };
                ("use `??`", format!("{recv} ?? {value}"))
            }
            _ => return diag,
        };
        diag.with_help(Help::machine(
            format!("{help}: `{fixed}`"),
            vec![Edit::replace(call, fixed.clone())],
        ))
    }

    /// Whether `t` meets bound `b` here, written with no type parameter of a call.
    fn meets_bound(&self, t: Ty, b: BoundId) -> bool {
        self.meets_bound_at(t, b, (&[], &[]))
    }

    /// Whether `t` meets bound `b` at a call or instance whose generic's parameters
    /// stand for `subst`'s arguments: the bound's own arguments count, `Cell<i64>`
    /// admitting no `Cell<string>` (S:762, S:764), and a bound naming a parameter,
    /// `T extends Cmp<T>`, is read at the arguments.
    fn meets_bound_at(&self, t: Ty, b: BoundId, subst: (&[ParamId], &[Ty])) -> bool {
        let tcx = &*self.sema.tcx;
        if tcx.references_error(t) {
            return true;
        }
        let args = self.bound_args_at(b, subst);
        bound_holds(tcx, t, tcx.bound(b).clone(), &args, &self.env)
    }

    /// Bound `b`'s type arguments with `subst` applied, resolved.
    fn bound_args_at(&self, b: BoundId, subst: (&[ParamId], &[Ty])) -> Vec<Ty> {
        let tcx = &*self.sema.tcx;
        let args = tcx.list(tcx.bound(b).args()).to_vec();
        args.into_iter()
            .map(|a| self.resolve(tcx.subst(a, subst.0, subst.1)))
            .collect()
    }

    /// Whether a bound of `p`, read at `subst`, still holds an inference variable,
    /// so its check waits for the end of inference (`Deferred::Bounds`).
    fn bound_waits(&self, p: ParamId, subst: (&[ParamId], &[Ty])) -> bool {
        let tcx = &*self.sema.tcx;
        tcx.param(p).bounds.clone().into_iter().any(|b| {
            self.bound_args_at(b, subst)
                .into_iter()
                .any(|a| tcx.has_infer(a))
        })
    }

    /// EN0419 for `t` failing bound `b` of `p` (EN0805 for `VolatileValue`, at the
    /// call), with the bound as the secondary in user code; `clause` is the `where`
    /// clause's span for a method's bound.
    fn bound_failed(
        &mut self,
        p: ParamId,
        b: BoundId,
        t: Ty,
        primary: Span,
        call: Span,
        clause: Option<(DefId, Span)>,
    ) {
        self.bound_failed_at(p, b, t, primary, call, clause, (&[], &[]));
    }

    /// [`FnCtxt::bound_failed`], with the bound shown at the call's arguments.
    #[allow(clippy::too_many_arguments)]
    fn bound_failed_at(
        &mut self,
        p: ParamId,
        b: BoundId,
        t: Ty,
        primary: Span,
        call: Span,
        clause: Option<(DefId, Span)>,
        subst: (&[ParamId], &[Ty]),
    ) {
        let bound_args = self.bound_args_at(b, subst);
        let tcx = &*self.sema.tcx;
        let bound = tcx.bound(b).clone();
        let bound_adt = bound.adt();
        let bound_ty = tcx.mk_adt(bound_adt, &bound_args);
        // The class's own `implements` of the bound already failed with EN0416, or
        // its base is unknown (EN0302).
        if self.sema.conversion_reported(self.resolve(t), bound_ty) {
            return;
        }
        let tcx = &*self.sema.tcx;
        let bound_name = tcx.ty_string(bound_ty);
        let shown = self.ty_str(t);
        let pdef = tcx.param(p).clone();
        let item = tcx.lang_item_of(tcx.adt(bound_adt).def);
        if item == Some(LangItem::VolatileValue) {
            let target = tcx.target().name.to_string();
            self.sema.emit(
                Diagnostic::new(
                    Code::EN0805,
                    format!("`{shown}` can't be accessed volatile on `{target}`"),
                    call,
                    format!("`{shown}` is not a `VolatileValue`"),
                )
                .note(
                    "volatile access takes `u8 u16 u32 i8 i16 i32 usize isize bool` and raw \
                     pointers, and `u64 i64` on `x86_64-*`",
                ),
            );
            return;
        }
        let mut diag = Diagnostic::new(
            Code::EN0419,
            format!("`{shown}` does not satisfy `{bound_name}`"),
            primary,
            format!("`{}` must satisfy `{bound_name}`", pdef.name),
        );
        match clause {
            Some((def, span)) => {
                let method = tcx.def(def).name().map_or("", |n| n.as_str()).to_owned();
                if !span.is_dummy() {
                    diag = diag.with_secondary(
                        span,
                        format!("required by this `where` clause of `{method}`"),
                    );
                } else {
                    diag = diag.note(format!(
                        "`{method}` requires `{} extends {bound_name}`",
                        pdef.name
                    ));
                }
                if matches!(method.as_str(), "testAndSet" | "testAndClear")
                    && item == Some(LangItem::AtomicBits)
                {
                    diag = diag.with_help(Help::text(format!(
                        "use `exchange`: `bts` has no byte form, so `{shown}` has no `{method}`"
                    )));
                }
            }
            None => {
                if !pdef.span.is_dummy() {
                    diag = diag.with_secondary(pdef.span, format!("the bound on `{}`", pdef.name));
                }
            }
        }
        self.sema.emit(diag);
    }

    /// A method's `where` clause for parameter `p` at `t` (S:323).
    fn check_where(&mut self, def: DefId, p: ParamId, t: Ty, call: Span) {
        let tcx = &*self.sema.tcx;
        if tcx.references_error(t) {
            return;
        }
        let Some(sig) = tcx.sig_opt(def) else {
            return;
        };
        let bounds: Vec<BoundId> = sig
            .where_bounds
            .iter()
            .filter(|(q, _)| *q == p)
            .flat_map(|(_, bs)| bs.iter().copied())
            .collect();
        for &b in &bounds {
            if self.meets_bound(t, b) {
                continue;
            }
            let clause = self.where_span(def, p);
            self.bound_failed(p, b, t, call, call, Some((def, clause)));
            return;
        }
        for b in bounds {
            self.satisfy_bound(t, b, (&[], &[]), call);
        }
    }

    /// The span of `def`'s `where` clause entry for `p`, when its AST is at hand.
    fn where_span(&self, def: DefId, p: ParamId) -> Span {
        where_entry_span(self.sema, def, p)
    }

    /// Whether the implicit parameter `p` of `callee` stands behind `&` in its
    /// parameter's type (one `| null` aside).
    fn implicit_behind_ref(&self, callee: DefId, p: ParamId) -> bool {
        let tcx = &*self.sema.tcx;
        let param = tcx.mk_param(p);
        tcx.sig_opt(callee).is_some_and(|sig| {
            sig.params.iter().any(|q| {
                let inner = match tcx.kind(q.ty) {
                    TyKind::Nullable(n) => n,
                    _ => q.ty,
                };
                matches!(tcx.kind(inner), TyKind::Ref(r) if r == param)
            })
        })
    }

    /// An implicit interface parameter's binding (module doc), its diagnostics at
    /// `primary` and the satisfaction it relies on recorded at the call.
    fn check_implicit_iface(
        &mut self,
        (callee, p, iface): (DefId, ParamId, AdtId),
        bounds: &[BoundId],
        t: Ty,
        (primary, call): (Span, Span),
    ) {
        let tcx = &*self.sema.tcx;
        let iface_name = tcx.adt(iface).name;
        // A `&string` never becomes an `&I`; a by-value `string` does (S:631).
        let behind_ref = self.implicit_behind_ref(callee, p);
        let tcx = &*self.sema.tcx;
        match tcx.kind(t) {
            // A two-word `&I`; by value the interface itself has no size, even where
            // a by-value `I` parameter would take a class (S:631, 4C's EN1006).
            TyKind::Adt(adt, _) if adt == iface => {
                if !behind_ref {
                    let shown = self.ty_str(t);
                    let text = self.snippet(primary);
                    self.sema.emit(iface_unsupported(
                        primary,
                        format!(
                            "this is {} `{shown}` by value",
                            crate::classes::sig::article(&shown)
                        ),
                        format!("`{shown}` is an interface, so the size of `{text}` isn't known"),
                        Some(format!(
                            "`&{shown}` to refer to one, `Box<{shown}>` to own one"
                        )),
                    ));
                }
                return;
            }
            // A type parameter that meets `I`: bounded by `I`, which relies on no
            // member, or by a class whose members meet it, which the call uses as
            // `I` (SPEC 4.4).
            TyKind::Param(_) if bounds.iter().all(|&b| self.meets_bound(t, b)) => {
                for &b in bounds {
                    self.satisfy_bound(t, b, (&[], &[]), call);
                }
                return;
            }
            TyKind::Str if behind_ref => {
                let arg = self.snippet(primary);
                let copy = arg.trim_start_matches('&').trim_start();
                self.sema.emit(
                    Diagnostic::new(
                        Code::EN0401,
                        format!(
                            "a `&string` can't become a `&{iface_name}`, because it may be a part of a string"
                        ),
                        primary,
                        format!("this is a `&string`, not a `&{iface_name}`"),
                    )
                    .with_help(Help::text(format!(
                        "take <T extends {iface_name}>(m: &T)"
                    )))
                    .with_help(Help::text(format!("or keep a copy: {copy}.toString()"))),
                );
                return;
            }
            TyKind::Str => return,
            _ => {}
        }
        if self.report_object_at_iface(primary, t, iface) {
            return;
        }
        let tcx = &*self.sema.tcx;
        let shown = self.ty_str(t);
        if !tcx.is_value_type(t) {
            self.sema.emit(Diagnostic::new(
                Code::EN0701,
                format!(
                    "{} `{iface_name}` can't hold {} `{shown}`, because `{shown}` holds a reference",
                    crate::classes::sig::article(iface_name.as_str()),
                    crate::classes::sig::article(&shown)
                ),
                primary,
                "only a value type becomes an interface value",
            ));
            return;
        }
        if bounds.iter().all(|&b| self.meets_bound(t, b)) {
            // An argument to a by-value `I` or non-null `&I` parameter uses its
            // class as `I` (SPEC 4.4).
            for &b in bounds {
                self.satisfy_bound(t, b, (&[], &[]), call);
            }
            return;
        }
        // The class's own `implements` already failed with EN0416, or its base is
        // unknown (EN0302).
        let iface_ty = self.sema.tcx.mk_adt(iface, &[]);
        if self.sema.conversion_reported(t, iface_ty) {
            return;
        }
        self.sema.emit(Diagnostic::new(
            Code::EN0401,
            format!("mismatched types: `{shown}` does not satisfy `{iface_name}`"),
            primary,
            format!("this is `{shown}`"),
        ));
    }

    /// An implicit shape parameter's binding: every field of the shape, public, at
    /// its type (S:601).
    fn check_implicit_shape(
        &mut self,
        shape: hir::ShapeId,
        t: Ty,
        primary: Span,
        (params, args): (&[ParamId], &[Ty]),
    ) {
        if let TyKind::Param(_) = self.sema.tcx.kind(t) {
            return;
        }
        // The shape's field types at this call's type arguments (fix-5): a field
        // fits when its type unifies with the argument's, an argument not known here
        // included (one refused is `Error`, which unifies with anything).
        let want: Vec<(Symbol, Ty)> = self
            .sema
            .tcx
            .shape(shape)
            .fields
            .clone()
            .into_iter()
            .map(|(name, ty)| (name, self.resolve(self.sema.tcx.subst(ty, params, args))))
            .collect();
        let shown = self.ty_str(t);
        let (have, private) = self.public_fields(t);
        let have: Vec<(Symbol, Ty)> = have
            .into_iter()
            .map(|(name, ty)| (name, self.resolve(ty)))
            .collect();
        // Which of the argument's fields fit the shape's (nothing is bound).
        let fitting: Vec<Symbol> = want
            .iter()
            .filter_map(|&(name, want_ty)| {
                let &(_, have_ty) = have.iter().find(|(n, _)| *n == name)?;
                self.can_unify(have_ty, want_ty).then_some(name)
            })
            .collect();
        // The shape as messages show it: at this call's type arguments once known.
        let at_call = self.resolve(self.sema.tcx.subst(
            self.sema.tcx.intern_ty(TyKind::Object(shape)),
            params,
            args,
        ));
        let tcx = &*self.sema.tcx;
        let shape_shown = if tcx.references_error(at_call) || tcx.has_infer(at_call) {
            tcx.ty_string(tcx.intern_ty(TyKind::Object(shape)))
        } else {
            tcx.ty_string(at_call)
        };
        let fits = |name: Symbol| fitting.contains(&name);
        // S:600: a variable of an object type that lacks only optional fields of
        // the shape is EN0433, as at an annotation.
        if let TyKind::Object(_) = tcx.kind(t) {
            let target = tcx.shape(shape).clone();
            let missing: Vec<Symbol> = want
                .iter()
                .map(|&(name, _)| name)
                .filter(|name| !have.iter().any(|(n, _)| n == name))
                .collect();
            let present_fit = want.iter().all(|(name, _)| {
                have.iter()
                    .find(|(n, _)| n == name)
                    .is_none_or(|_| fits(*name))
            });
            if present_fit && !missing.is_empty() && missing.iter().all(|&n| target.is_optional(n))
            {
                let fill: Vec<String> = missing.iter().map(|n| format!("{n}: null")).collect();
                let names: Vec<String> = missing.iter().map(|n| format!("`{n}`")).collect();
                let names = match names.as_slice() {
                    [init @ .., last] if !init.is_empty() => {
                        format!("{} and {last}", init.join(", "))
                    }
                    _ => names.join(""),
                };
                self.sema.emit(
                    Diagnostic::new(
                        Code::EN0433,
                        format!("missing {names}"),
                        primary,
                        format!(
                            "`{shape_shown}` needs every field it names, optional ones included"
                        ),
                    )
                    .with_help(Help::text(format!("add `{}`", fill.join(", ")))),
                );
                return;
            }
        }
        for (name, _) in &want {
            match have.iter().find(|(n, _)| n == name) {
                Some((_, have_ty)) => {
                    if !fits(*name) {
                        self.sema.emit(Diagnostic::new(
                            Code::EN0401,
                            format!("mismatched types: expected `{shape_shown}`, found `{shown}`"),
                            primary,
                            format!("`{name}` is `{}` here", tcx.ty_string(*have_ty)),
                        ));
                        return;
                    }
                }
                None => {
                    let mut diag = Diagnostic::new(
                        Code::EN0401,
                        format!("`{shown}` has no public field `{name}`"),
                        primary,
                        format!("this is `{shown}`"),
                    );
                    if private.contains(name) {
                        diag = diag.note(format!("`{name}` is private to `{shown}`"));
                    }
                    self.sema.emit(diag);
                    return;
                }
            }
        }
    }
}

// -------------------------------------------------------------------------------
// Declarations.

/// The span of `def`'s `where` clause entry for `p`, when its AST is at hand.
fn where_entry_span(sema: &Sema, def: DefId, p: ParamId) -> Span {
    let name = sema.tcx.param(p).name;
    let Some(crate::lower::BodyAst::Method(m)) = sema.decls.body_ast(BodyOwner::Fn(def)) else {
        return Span::DUMMY;
    };
    m.where_clause
        .iter()
        .find(|w| w.param.name == name)
        .map_or(Span::DUMMY, |w| {
            let end = w.bounds.last().map_or(w.param.span, |b| b.span);
            w.param.span.to(end)
        })
}

/// The written types of every user declaration (parameters, results, fields, a
/// class's `extends` and `implements` at the written type, the bounds of type
/// parameters and of `where` clauses) against the bounds of the classes and enums
/// they instantiate (EN0419, T:612).
pub(crate) fn check_decl_types(sema: &mut Sema) {
    let mut sites: Vec<(Span, Ty, ParamEnv, Span)> = Vec::new();
    // Each user class's written `extends` and `implements` spans.
    let mut written: BTreeMap<AdtId, (Option<Span>, Vec<Span>)> = BTreeMap::new();
    for item in &sema.decls.items {
        if let ItemAstKind::Class(adt, decl, _) = &item.kind {
            written.insert(
                *adt,
                (
                    decl.extends.as_ref().map(|t| t.span),
                    decl.implements.iter().map(|t| t.span).collect(),
                ),
            );
        }
    }
    let tcx = &*sema.tcx;
    // A bound written on a type parameter, or added by a `where` clause.
    let bound_ty = |b: BoundId| {
        let bound = tcx.bound(b);
        tcx.mk_adt(bound.adt(), &tcx.list(bound.args()))
    };
    for (def, data) in tcx.defs() {
        if tcx.module(data.module).library {
            continue;
        }
        if let Some(sig) = tcx.sig_opt(def) {
            let env = ParamEnv {
                bounds: sig.where_bounds.clone(),
            };
            for p in &sig.params {
                let at = if p.span.is_dummy() {
                    data.name_span
                } else {
                    p.span
                };
                sites.push((at, p.ty, env.clone(), data.span));
            }
            sites.push((data.name_span, sig.ret, env.clone(), data.span));
            for &q in &tcx.generics(sig.generics).params {
                let pdef = tcx.param(q);
                let at = if pdef.span.is_dummy() {
                    data.name_span
                } else {
                    pdef.span
                };
                for &b in &pdef.bounds {
                    sites.push((at, bound_ty(b), env.clone(), data.span));
                }
            }
            for (q, bounds) in &sig.where_bounds {
                let mut at = where_entry_span(sema, def, *q);
                if at.is_dummy() {
                    at = data.name_span;
                }
                for &b in bounds {
                    sites.push((at, bound_ty(b), env.clone(), data.span));
                }
            }
        }
    }
    for (id, adt) in tcx.adts() {
        if tcx.module(tcx.def(adt.def).module).library {
            continue;
        }
        let fields: Vec<&hir::FieldDef> = match &adt.kind {
            hir::AdtKind::Class(class) => class.own_fields().map(|(_, f)| f).collect(),
            hir::AdtKind::Enum(e) => e.variants.iter().flat_map(|v| v.fields.iter()).collect(),
            hir::AdtKind::Interface(_) => Vec::new(),
        };
        for f in fields {
            sites.push((f.span, f.ty, ParamEnv::empty(), f.span));
        }
        let name_span = tcx.def(adt.def).name_span;
        for &q in &tcx.generics(adt.generics).params {
            let pdef = tcx.param(q);
            let at = if pdef.span.is_dummy() {
                name_span
            } else {
                pdef.span
            };
            for &b in &pdef.bounds {
                sites.push((at, bound_ty(b), ParamEnv::empty(), at));
            }
        }
        // `extends` and `implements`, at the written type (the class's name when
        // it is not at hand).
        if let hir::AdtKind::Class(class) = &adt.kind {
            let (base_at, impl_at) = written.get(&id).cloned().unwrap_or_default();
            if let Some(t) = class.base {
                sites.push((
                    base_at.unwrap_or(name_span),
                    t,
                    ParamEnv::empty(),
                    name_span,
                ));
            }
            for (i, &t) in class.implements.iter().enumerate() {
                let at = impl_at.get(i).copied().unwrap_or(name_span);
                sites.push((at, t, ParamEnv::empty(), name_span));
            }
        }
    }
    sites.sort_by_key(|s| (s.0, s.3));
    sites.dedup_by_key(|s| (s.0, s.1));
    for (span, ty, env, _) in sites {
        check_written(sema, span, ty, &env);
    }
}

/// One written type `ty` at `span`: each class or enum instance in it against its
/// parameters' bounds. Declarations' types come here from [`check_decl_types`],
/// and the types written inside bodies from `FnCtxt::lower_ty`.
pub(crate) fn check_written(sema: &mut Sema, span: Span, ty: Ty, env: &ParamEnv) {
    let mut instances = Vec::new();
    let tcx = &*sema.tcx;
    tcx.any_ty(ty, &mut |tcx, t| {
        if let TyKind::Adt(adt, args) = tcx.kind(t)
            && !tcx.list(args).is_empty()
        {
            instances.push((adt, args));
        }
        false
    });
    for (adt, args) in instances {
        let tcx = &*sema.tcx;
        let params = tcx.generics(tcx.adt(adt).generics).params.clone();
        let args = tcx.list(args);
        // S:1140: writing `Result<T, E>` implies `E extends Error`, so its `E` is
        // EN0454's alone (lowering), and a type parameter there meets it.
        let result = tcx.is_lang_adt(adt, LangItem::Result);
        for (i, (&p, &a)) in params.iter().zip(args.iter()).enumerate() {
            if result && i == 1 {
                continue;
            }
            let bounds = sema.tcx.param(p).bounds.clone();
            for b in bounds {
                // A bound naming the class's parameters is read at this instance's
                // arguments (`Sorted<T extends Cmp<T>>` at `Sorted<P>` needs `Cmp<P>`).
                if !decl_meets(sema.tcx, a, b, env, (&params, &args)) {
                    let tcx = &*sema.tcx;
                    let bound = tcx.bound(b).clone();
                    let bound_args: Vec<Ty> = tcx
                        .list(bound.args())
                        .iter()
                        .map(|&x| tcx.subst(x, &params, &args))
                        .collect();
                    let bound_name = tcx.ty_string(tcx.mk_adt(bound.adt(), &bound_args));
                    let shown = tcx.ty_string(a);
                    let class = tcx.adt(adt).name;
                    let pname = tcx.param(p).name;
                    sema.emit(Diagnostic::new(
                        Code::EN0419,
                        format!("`{shown}` does not satisfy `{bound_name}`"),
                        span,
                        format!("`{class}` requires `{pname} extends {bound_name}`"),
                    ));
                    return;
                }
                satisfy_written(sema, a, b, env, (&params, &args), span);
            }
        }
    }
}

/// A bound that the written type argument `t` met at `span`, read at the
/// instance's arguments `subst`, given to the one satisfaction routine
/// (`satisfy::satisfy`, SPEC 4.4), which records what it relied on. A type
/// argument outside `V` is the position rules', as in [`decl_meets`].
fn satisfy_written(
    sema: &mut Sema,
    t: Ty,
    b: BoundId,
    env: &ParamEnv,
    subst: (&[ParamId], &[Ty]),
    span: Span,
) {
    let tcx = &*sema.tcx;
    if tcx.references_error(t) || !tcx.is_value_type(t) {
        return;
    }
    let args: Vec<Ty> = tcx
        .list(tcx.bound(b).args())
        .iter()
        .map(|&a| tcx.subst(a, subst.0, subst.1))
        .collect();
    let iface = tcx.mk_adt(tcx.bound(b).adt(), &args);
    let _ = satisfy::satisfy(sema, t, iface, env, span);
}

/// [`FnCtxt::meets_bound`] outside a body, under `env`, at the instance's
/// arguments `subst`. A type argument outside `V` (a reference, a view, a
/// borrowing class, an interface by value) is the position rules' (EN0701, EN0401,
/// EN1006), reported once there (EF-08).
fn decl_meets(
    tcx: &hir::Tcx,
    t: Ty,
    b: BoundId,
    env: &ParamEnv,
    subst: (&[ParamId], &[Ty]),
) -> bool {
    if tcx.references_error(t) || !tcx.is_value_type(t) {
        return true;
    }
    let args: Vec<Ty> = tcx
        .list(tcx.bound(b).args())
        .iter()
        .map(|&a| tcx.subst(a, subst.0, subst.1))
        .collect();
    bound_holds(tcx, t, tcx.bound(b).clone(), &args, env)
}

/// Whether `t` meets `bound` read at the arguments `args` (S:762, S:764): a class
/// bound admits that class at those arguments and its subclasses, through their
/// bases' arguments; an interface bound is met by satisfaction at those arguments,
/// or by a type parameter bounded by it at equal arguments; the compiler's
/// interfaces by their own rules.
pub(crate) fn bound_holds(
    tcx: &hir::Tcx,
    t: Ty,
    bound: Bound,
    args: &[Ty],
    env: &ParamEnv,
) -> bool {
    let adt = bound.adt();
    let at = tcx.mk_adt(adt, args);
    match bound {
        Bound::Class { .. } => satisfy::satisfies(tcx, t, at, env).is_ok(),
        Bound::Iface { .. } => match tcx.lang_item_of(tcx.adt(adt).def) {
            Some(LangItem::Copy) => tcx.is_copy(t, env),
            Some(LangItem::Clone) => tcx.is_clone(t, env),
            Some(LangItem::Display) => true,
            Some(LangItem::Error) => {
                tcx.lang_adt(LangItem::Error).is_none() || satisfy::is_error_type(tcx, t, env)
            }
            Some(item) if item.is_sealed() => match tcx.kind(t) {
                TyKind::Param(_) => satisfy::satisfies(tcx, t, at, env).is_ok(),
                _ => tcx.sealed_implements(item, t),
            },
            _ => satisfy::satisfies(tcx, t, at, env).is_ok(),
        },
    }
}

// -------------------------------------------------------------------------------
// AST shapes.

/// `e` without the parentheses around it.
pub(crate) fn strip_parens(mut e: &ast::Expr) -> &ast::Expr {
    while let ast::ExprKind::Paren(inner) = &e.kind {
        e = inner;
    }
    e
}

/// Whether `e` is an arrow, which step 3 types.
pub(crate) fn is_arrow(e: &ast::Expr) -> bool {
    matches!(strip_parens(e).kind, ast::ExprKind::Arrow(_))
}

/// Whether `e` is an object literal, or `&` of one.
fn is_object_literal(e: &ast::Expr) -> bool {
    match &strip_parens(e).kind {
        ast::ExprKind::ObjectLit(_) => true,
        ast::ExprKind::Borrow(inner) => {
            matches!(strip_parens(inner).kind, ast::ExprKind::ObjectLit(_))
        }
        _ => false,
    }
}

/// Whether `e` is a number literal, a `-` before it included: an integer one
/// (`Int`) or a float one (`Float`).
pub(crate) fn number_literal(e: &ast::Expr) -> Option<VarKind> {
    match &strip_parens(e).kind {
        ast::ExprKind::Int { .. } => Some(VarKind::Int),
        ast::ExprKind::Float(_) => Some(VarKind::Float),
        ast::ExprKind::Unary(ast::UnOp::Neg, inner) => match &strip_parens(inner).kind {
            ast::ExprKind::Int { .. } => Some(VarKind::Int),
            ast::ExprKind::Float(_) => Some(VarKind::Float),
            _ => None,
        },
        _ => None,
    }
}

/// The span of a list of arguments, first to last.
pub(crate) fn args_span(args: &[ast::Expr]) -> Option<Span> {
    let first = args.first()?;
    let last = args.last()?;
    Some(first.span.to(last.span))
}
