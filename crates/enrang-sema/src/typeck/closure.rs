//! Arrows and function values (plan d.12; SPEC 4.5 C11-C17, 5.5; A:920; owner 4C).
//!
//! **Typing an arrow.** An arrow is typed from its expected type, through one
//! `| null` (an optional closure parameter, C12 then C06): each unannotated
//! parameter takes the expected parameter type at its place, and the result is the
//! expected one (`RetOrigin::Expected`). With no expected `fn` or closure type, a
//! parameter needs an annotation (EN0409 `` `x` needs a type annotation ``), unless
//! a known expected type fits no arrow (no `fn` or closure type, or one with fewer
//! parameters), which is EN0401 at the arrow, once (plan choice), and the
//! result is the written one (`Written`) or, with none, decided by the body
//! (`Body`): its returns are typed as they are and unify once the body is typed, in
//! source order, never wrapped (no C19, A:920), so `Err(e)` there takes its error
//! type from `e`; two that do not unify are EN0401 at the later one, with `help:
//! annotate the result, `(s: &string): Result<isize> => ...`, or write
//! `Ok(s.length())`` when one is a `Result` and the other is not (T:902). With no
//! value returned, the result is `void`; a return already rejected leaves it unknown
//! and silent. An arrow whose block can end where a value
//! is due is EN0427 `this arrow may end without returning a `T`` (plan choice: the
//! rule of S:1137 for functions). Its type is `fn(...)` when it captures nothing and
//! its `Closure` type when it does, which a local holding it keeps (A:258).
//!
//! **Captures** are computed from the typed body, nested arrows included: one
//! `Capture` per outer local used, at its first use in walk order, an outer local
//! being one declared before the arrow, `this`, a top-level variable, or a local
//! function's hidden argument, plus the hidden arguments of a local function the
//! body calls (N13). Phase 3 gives each its mode (N4).
//!
//! **Conversions** (`coerce_fn`, A:888): C11 `FnToPtr` for a non-capturing arrow or a
//! safe function name at `fn(...)`; a capturing arrow, or a closure value, there is
//! EN1007 `a function pointer cannot capture variables`, naming the variable (S:968).
//! C12 `ArrowToClosure` for an arrow, a safe function name or an `fn` value at a
//! closure parameter type; C14 `ClosureReborrow` for a closure parameter passed on.
//! C15 `FnToUnsafePtr` for a safe function or `fn` value at `unsafe fn(...)`, C16 the
//! same for an `unsafe`, `@requires`, `declare` or `@naked` function name of the same
//! ABI, which at a safe `fn` or a closure parameter is EN0803; C17 `FnToHandler` for
//! an `@interrupt` function at `InterruptHandler`, EN0803 anywhere else; a local
//! function with hidden arguments at `fn(...)` is EN0803, while at a closure parameter
//! it captures them (S:981). Identical signatures ignore permission rows (N1). A
//! generic function named as a value takes fresh variables for its written type
//! parameters, its bounds checked after inference (`Deferred::Bounds`); an `&I`
//! parameter names its copy for two-word `&I` arguments, an object-type parameter
//! the copy for its own shape, and a by-value interface parameter, or an `&I` of an
//! interface no table can serve, makes the conversion EN1006 (S:682, A:894).

use std::sync::Arc;

use enrang_base::{BytePos, Idx, Span};
use enrang_diag::{Code, Diagnostic, Help};
use enrang_hir::{
    self as hir, Abi, Adjust, ArmBody, ArmValue, ArrayPart, ArrowBodyKind, ArrowId, Callee,
    Capture, ConstValue, DefKind, ExpectArg, ExprKind, FnPtrSig, FnRef, ForSource, Implicit,
    LangItem, LocalId, LocalKind, Mark, OptMember, StmtKind, TplPart, Ty, TyKind,
};
use enrang_syntax::ast;

use crate::resolve::toplevel;
use crate::typeck::iface::iface_unsupported;
use crate::typeck::infer::VarKind;
use crate::typeck::{ArrowFrame, Deferred, Expect, FnCtxt, RetCtx, RetOrigin};

impl FnCtxt<'_, '_> {
    /// Declares this body's local of each top-level variable that a local function
    /// called in arrow body `body` takes as a hidden argument, so the arrow can
    /// capture it (A:1360): a local function's body has one only for the
    /// variables it names itself.
    fn hidden_locals_of_calls(&mut self, body: &ArrowBodyKind) {
        let mut vars = Vec::new();
        let mut visit = |seen: Seen<'_>| {
            if let Seen::Expr(e) = seen
                && let ExprKind::Call {
                    callee: Callee::Fn(FnRef { def, .. }),
                    ..
                } = &e.kind
                && self.sema.tcx.def(*def).kind == DefKind::LocalFn
            {
                vars.extend(toplevel::hidden_args(self.sema, *def).iter().copied());
            }
        };
        match body {
            ArrowBodyKind::Expr(e) => walk_expr(e, &mut visit),
            ArrowBodyKind::Block(b) => walk_block(b, &mut visit),
        }
        let statements = self.at.statements;
        for var in vars {
            let kind = match statements {
                true => LocalKind::TopVar(var),
                false => LocalKind::Hidden(var),
            };
            self.top_var_local(var, kind);
        }
    }

    /// An arrow, typed from `expected` when that is an `fn` or closure type.
    pub(crate) fn check_arrow(&mut self, a: &ast::ArrowFn, expected: Option<Ty>) -> hir::Expr {
        // A known expected type that no arrow fits: an unannotated parameter takes
        // nothing from it, and the arrow is reported once, below.
        let known = expected
            .map(|t| self.shallow(t))
            .filter(|&t| self.var_kind(t).is_none() && !self.is_error(t));
        // An expected type an error made (a refused annotation, EN0705) silences
        // the arrow's own checks: one mistake, one diagnostic.
        let errored = expected.is_some_and(|t| self.is_error(self.shallow(t)));
        let expected = expected.and_then(|t| self.expected_sig(t));
        let mut misfit = false;
        let error = self.error_ty();
        // The id is taken first, so the arrows nested in this one come after it.
        let placeholder = self.sema.tcx.intern_fn_sig(FnPtrSig::new(&[], error));
        let id = self.arrows.push(hir::ArrowBody {
            params: Vec::new(),
            body: ArrowBodyKind::Block(hir::Block {
                stmts: Vec::new(),
                span: a.span,
            }),
            ret: error,
            sig: placeholder,
            captures: Vec::new(),
            span: a.span,
        });
        self.scopes.push();
        let first_local = self.locals.next_index();
        let mut params = Vec::with_capacity(a.params.len());
        let mut sig_params = Vec::with_capacity(a.params.len());
        for (i, p) in a.params.iter().enumerate() {
            let ty = match (&p.ty, expected.as_ref().and_then(|s| s.params.get(i))) {
                (Some(t), _) => self.lower_arrow_param_ty(t),
                (None, Some(&(t, _))) => t,
                (None, None) => {
                    // An argument of a call that reported its own error (EN0423,
                    // EN0451, an untyped callee) is that call's; any other gets
                    // EN0409, a form's, a type parameter's and `new Box`'s included.
                    if known.is_some() {
                        misfit = true;
                    } else if !errored && !self.call_reported(a.span) {
                        self.report_untyped_param(p);
                    }
                    error
                }
            };
            let mark = if p.is_let { Mark::Let } else { Mark::None };
            let local = self.declare(
                Some(p.name.name),
                ty,
                false,
                LocalKind::Arrow(id),
                p.name.span,
            );
            params.push(local);
            sig_params.push((ty, mark));
        }
        let (ret, origin, ret_readonly) = match (&a.ret, &expected) {
            (Some(r), _) => (self.lower_ty(&r.ty), RetOrigin::Written, r.readonly),
            (None, Some(sig)) => (sig.ret, RetOrigin::Expected, sig.ret_readonly),
            (None, None) => {
                let var = self.infer.fresh(VarKind::Any);
                let var = self.sema.tcx.intern_ty(TyKind::Infer(var));
                (var, RetOrigin::Body, false)
            }
        };
        self.arrow_stack.push(ArrowFrame {
            ret: RetCtx { ty: ret, origin },
            first_local,
            captures: Vec::new(),
            try_fixed: None,
        });
        self.reachable = true;
        let body = match &a.body {
            ast::ArrowBody::Expr(e) => ArrowBodyKind::Expr(match origin {
                RetOrigin::Body => self.check_expr(e, Expect::None),
                RetOrigin::Written | RetOrigin::Expected => self.check_ret_value(e),
            }),
            ast::ArrowBody::Block(b) => ArrowBodyKind::Block(self.check_block(b)),
        };
        let reachable = self.reachable;
        let try_fixed = self.arrow_stack.pop().and_then(|f| f.try_fixed);
        self.scopes.pop();
        if origin == RetOrigin::Body {
            self.decide_ret(a, &body, ret, try_fixed);
        }
        if let (ast::ArrowBody::Block(b), true) = (&a.body, reachable) {
            self.check_arrow_end(a, b.span, ret);
        }
        self.hidden_locals_of_calls(&body);
        let captures = self.arrow_captures(id, first_local, &body);
        if let (true, Some(want)) = (misfit, known) {
            self.report_arrow_misfit(a, want);
        }
        // A capturing arrow is a closure, whose result is `V` (S:979). With an
        // expected signature, that type's own checks decide (a written closure
        // type's result, EN0703; a type argument's bound, EN0703; an `fn` type
        // takes no capturing arrow, EN1007); without one, as for a local, here.
        let resolved = self.resolve(ret);
        if !misfit
            && !errored
            && expected.is_none()
            && !captures.is_empty()
            && crate::lower::types::closure_result_holds_refs(self.sema, resolved)
        {
            let at = a.ret.as_ref().map_or(a.span, |r| r.ty.span);
            crate::lower::types::closure_result_error(self.sema, resolved, at);
        }
        let sig = FnPtrSig {
            unsafety: false,
            params: sig_params,
            ret,
            ret_readonly,
        };
        let sig_id = self.sema.tcx.intern_fn_sig(sig.clone());
        let ty = match (misfit, captures.is_empty()) {
            (true, _) => error,
            (false, true) => self.sema.tcx.mk_fn_ptr(Abi::Enrang, sig),
            (false, false) => self.sema.tcx.mk_closure(sig),
        };
        self.arrows[id] = hir::ArrowBody {
            params,
            body,
            ret,
            sig: sig_id,
            captures,
            span: a.span,
        };
        self.mk_expr(ty, a.span, ExprKind::Arrow(id))
    }

    /// The signature of an expected `fn` or closure type, through one `| null`.
    fn expected_sig(&self, t: Ty) -> Option<Arc<FnPtrSig>> {
        let tcx = &*self.sema.tcx;
        let t = self.shallow(t);
        let t = match tcx.kind(t) {
            TyKind::Nullable(inner) => self.shallow(inner),
            _ => t,
        };
        match tcx.kind(t) {
            TyKind::FnPtr(_, sig) | TyKind::Closure(sig) => Some(tcx.fn_sig(sig)),
            _ => None,
        }
    }

    /// Whether `span` is an argument of the innermost call being typed, and that
    /// call reported an error of its own.
    fn call_reported(&self, span: Span) -> bool {
        self.calls
            .last()
            .is_some_and(|frame| frame.reported && frame.args.contains(&span))
    }

    /// Marks the innermost call as having reported its own error.
    pub(crate) fn mark_call_reported(&mut self) {
        if let Some(frame) = self.calls.last_mut() {
            frame.reported = true;
        }
    }

    /// EN0409 for an arrow parameter with no type and no expected one (S:724).
    fn report_untyped_param(&mut self, p: &ast::ArrowParam) {
        let name = p.name.name;
        self.sema.emit(
            Diagnostic::new(
                Code::EN0409,
                format!("`{name}` needs a type annotation"),
                p.name.span,
                format!("nothing here gives `{name}` a type"),
            )
            .with_help(Help::text(
                "annotate it, or pass the arrow where an `fn` or closure type is expected",
            )),
        );
    }

    /// EN0401 for an arrow with an unannotated parameter where the expected type
    /// `want` is no `fn` or closure type, or one with fewer parameters (plan choice).
    fn report_arrow_misfit(&mut self, a: &ast::ArrowFn, want: Ty) {
        let shown = self.ty_str(want);
        let n = a.params.len();
        let (found, label) = match self.expected_sig(want) {
            Some(_) => {
                let count = match n {
                    1 => "1 parameter".to_owned(),
                    n => format!("{n} parameters"),
                };
                (
                    format!("an arrow with {count}"),
                    format!("this arrow takes {count}"),
                )
            }
            None => ("an arrow".to_owned(), "this is an arrow".to_owned()),
        };
        self.sema.emit(Diagnostic::new(
            Code::EN0401,
            format!("mismatched types: expected `{shown}`, found {found}"),
            a.span,
            label,
        ));
    }

    /// The result of an arrow whose body decides it, `ret` a fresh variable: its
    /// returns unify in source order (A:920), else it is `void`.
    fn decide_ret(
        &mut self,
        a: &ast::ArrowFn,
        body: &ArrowBodyKind,
        ret: Ty,
        try_fixed: Option<Span>,
    ) {
        let mut returns: Vec<(Option<hir::Expr>, Span)> = Vec::new();
        let mut collect = |seen: Seen<'_>| {
            if let Seen::Return(e, span) = seen {
                returns.push((e.cloned(), span));
            }
        };
        match body {
            ArrowBodyKind::Expr(e) => walk_expr(e, &mut collect),
            ArrowBodyKind::Block(b) => walk_block(b, &mut collect),
        }
        if let ArrowBodyKind::Expr(e) = body
            && self.sema.tcx.kind(self.shallow(e.ty)) != TyKind::Never
        {
            returns.push((Some(e.clone()), e.span));
        }
        let void = self.sema.tcx.common().void;
        let mut first: Option<(Option<hir::Expr>, Ty)> = None;
        let mut rejected = false;
        for (value, _) in &returns {
            let ty = value.as_ref().map_or(void, |v| v.ty);
            if self.is_error(ty) {
                rejected = true;
                continue;
            }
            if self.unify(ret, ty) {
                first.get_or_insert((value.clone(), ty));
                continue;
            }
            let decided = first.as_ref().map(|(v, _)| v.clone()).unwrap_or_default();
            self.report_returns_differ(a, ret, value.as_ref(), decided.as_ref(), ty, try_fixed);
            self.poison(ret);
            self.poison(ty);
            return;
        }
        if rejected {
            // A return already reported leaves what it would have decided unknown.
            self.poison(ret);
        } else if self.var_kind(ret) == Some(VarKind::Any) {
            let _ = self.unify(ret, void);
        }
    }

    /// EN0401 for a return of an arrow whose body decides its result that does not
    /// unify with an earlier one (T:902).
    fn report_returns_differ(
        &mut self,
        a: &ast::ArrowFn,
        ret: Ty,
        value: Option<&hir::Expr>,
        first: Option<&hir::Expr>,
        ty: Ty,
        try_fixed: Option<Span>,
    ) {
        let (want, have) = (self.ty_str(ret), self.ty_str(ty));
        let Some(value) = value else {
            return;
        };
        let mut diag = Diagnostic::new(
            Code::EN0401,
            format!("mismatched types: expected `{want}`, found `{have}`"),
            value.span,
            format!("this is `{have}`"),
        );
        // A `?` decided the result before any return did: it is where the type
        // comes from, and a plain value is wrapped as with a `Result` return.
        if first.is_none()
            && let Some(mark) = try_fixed
        {
            diag = diag.with_secondary(mark, "the arrow's result type comes from this `?`");
            if let Some((_, err)) = self.result_parts(ret)
                && self.result_parts(value.ty).is_none()
            {
                let success = self.ty_str(value.ty);
                let result = match self.is_failure(err) {
                    true => format!("Result<{success}>"),
                    false => format!("Result<{success}, {}>", self.ty_str(err)),
                };
                let params = self.arrow_params_text(a);
                let text = self.snippet(value.span);
                diag = diag.with_help(Help::text(format!(
                    "annotate the result, `{params}: {result} => ...`, or write `Ok({text})`"
                )));
            }
        }
        if let Some(first) = first {
            diag = diag.with_secondary(first.span, "the arrow's result type comes from here");
            let plain = match (self.result_parts(first.ty), self.result_parts(value.ty)) {
                (Some((_, err)), None) => Some((value, err)),
                (None, Some((_, err))) => Some((first, err)),
                _ => None,
            };
            if let Some((plain, err)) = plain {
                let success = self.ty_str(plain.ty);
                let result = match self.is_failure(err) {
                    true => format!("Result<{success}>"),
                    false => format!("Result<{success}, {}>", self.ty_str(err)),
                };
                let params = self.arrow_params_text(a);
                let text = self.snippet(plain.span);
                diag = diag.with_help(Help::text(format!(
                    "annotate the result, `{params}: {result} => ...`, or write `Ok({text})`"
                )));
            }
        }
        self.sema.emit(diag);
    }

    /// An arrow's parameter list as written: `(s: &string)`.
    fn arrow_params_text(&self, a: &ast::ArrowFn) -> String {
        let params: Vec<String> = a
            .params
            .iter()
            .map(|p| {
                let mark = if p.is_let { "let " } else { "" };
                match &p.ty {
                    Some(t) => format!("{mark}{}: {}", p.name.name, self.snippet(t.span)),
                    None => format!("{mark}{}", p.name.name),
                }
            })
            .collect();
        format!("({})", params.join(", "))
    }

    /// Binds every unbound variable of `t` to `Error`, so a rejected arrow reports
    /// nothing more.
    fn poison(&mut self, t: Ty) {
        let t = self.resolve(t);
        let mut vars = Vec::new();
        self.sema.tcx.any_ty(t, &mut |tcx, inner| {
            if let TyKind::Infer(_) = tcx.kind(inner) {
                vars.push(inner);
            }
            false
        });
        let error = self.error_ty();
        for var in vars {
            let _ = self.unify(var, error);
        }
    }

    /// EN0427 for an arrow whose block can end where its result needs a value.
    fn check_arrow_end(&mut self, a: &ast::ArrowFn, block: Span, ret: Ty) {
        let ret = self.resolve(ret);
        // Only a result the body has not decided may still be `void`: a number a
        // `return 2;` gave is due on every path (S:1136), defaulted or not.
        let open = |me: &Self, t: Ty| me.var_kind(me.shallow(t)) == Some(VarKind::Any);
        let open_ok = match self.sema.tcx.kind(ret) {
            TyKind::Adt(adt, args) if self.sema.tcx.is_lang_adt(adt, LangItem::Result) => self
                .sema
                .tcx
                .list(args)
                .first()
                .is_some_and(|&ok| open(self, ok)),
            _ => false,
        };
        if self.nothing_due(ret) || open(self, ret) || open_ok {
            return;
        }
        let close = Span {
            lo: BytePos(block.hi.0.saturating_sub(1)),
            hi: block.hi,
        };
        let shown = self.ty_str(ret);
        let mut diag = Diagnostic::new(
            Code::EN0427,
            format!(
                "this arrow may end without returning {}",
                crate::classes::sig::a_ty(&shown)
            ),
            close,
            "the end of the body is reached without a `return`",
        );
        if let Some(r) = &a.ret {
            diag = diag.with_secondary(
                r.ty.span,
                format!("`{shown}` is required by the return type"),
            );
        }
        self.sema.emit(diag);
    }

    /// The outer locals arrow `id` uses, nested arrows included, each once at its
    /// first use.
    ///
    /// The top-level variables a local function called in the arrow takes as
    /// hidden arguments are captures too (A:1360), so this body declares a local
    /// for each first, as naming one would (`hidden_locals_of_calls`).
    fn arrow_captures(
        &self,
        id: ArrowId,
        first_local: LocalId,
        body: &ArrowBodyKind,
    ) -> Vec<Capture> {
        let mut captures: Vec<Capture> = Vec::new();
        let mut uses: Vec<(LocalId, Span)> = Vec::new();
        let mut visit = |seen: Seen<'_>| {
            let Seen::Expr(e) = seen else {
                return;
            };
            match &e.kind {
                ExprKind::Local(local) => uses.push((*local, e.span)),
                ExprKind::Call { callee, .. } => match callee {
                    Callee::Closure(local) => uses.push((*local, e.span)),
                    Callee::Fn(FnRef { def, .. }) => {
                        if self.sema.tcx.def(*def).kind == DefKind::LocalFn {
                            for var in toplevel::hidden_args(self.sema, *def) {
                                let found = self.locals.iter_enumerated().find(|(_, d)| {
                                    matches!(d.kind, LocalKind::TopVar(v) | LocalKind::Hidden(v) if v == *var)
                                });
                                if let Some((local, _)) = found {
                                    uses.push((local, e.span));
                                }
                            }
                        }
                    }
                    _ => {}
                },
                _ => {}
            }
        };
        match body {
            ArrowBodyKind::Expr(e) => walk_expr(e, &mut visit),
            ArrowBodyKind::Block(b) => walk_block(b, &mut visit),
        }
        for (_, nested) in self
            .arrows
            .iter_enumerated()
            .filter(|(i, _)| i.index() > id.index())
        {
            match &nested.body {
                ArrowBodyKind::Expr(e) => walk_expr(e, &mut visit),
                ArrowBodyKind::Block(b) => walk_block(b, &mut visit),
            }
        }
        for (local, span) in uses {
            let decl = &self.locals[local];
            let outer = local.index() < first_local.index()
                || matches!(decl.kind, LocalKind::TopVar(_) | LocalKind::Hidden(_));
            if outer && !captures.iter().any(|c| c.local == local) {
                captures.push(Capture { local, span });
            }
        }
        captures
    }

    // ---------------------------------------------------------------------------
    // C11, C12, C14-C17.

    /// C11, C12, C14-C17 at `to`, or `None` when none applies, which leaves `e` to
    /// unification and the rest of the table.
    pub(crate) fn coerce_fn(&mut self, e: hir::Expr, to: Ty) -> Option<hir::Expr> {
        let target = self.shallow(to);
        let tcx = &*self.sema.tcx;
        if let TyKind::Adt(adt, _) = tcx.kind(target)
            && tcx.is_lang_adt(adt, LangItem::InterruptHandler)
        {
            return self.handler_at(e);
        }
        let (closure, sig, abi) = match tcx.kind(target) {
            TyKind::FnPtr(abi, sig) => (false, tcx.fn_sig(sig), abi),
            TyKind::Closure(sig) => (true, tcx.fn_sig(sig), Abi::Enrang),
            _ => return None,
        };
        let at = FnSite {
            closure,
            sig,
            abi,
            target,
        };
        match &e.kind {
            ExprKind::Arrow(id) => {
                let id = *id;
                self.arrow_at(e, id, &at)
            }
            ExprKind::Const(ConstValue::FnAddr(f)) => {
                let f = f.clone();
                self.fn_name_at(e, f, &at)
            }
            _ => self.fn_value_at(e, &at),
        }
    }

    /// C17: an `@interrupt` function's name at `InterruptHandler`.
    fn handler_at(&mut self, mut e: hir::Expr) -> Option<hir::Expr> {
        let ExprKind::Const(ConstValue::FnAddr(f)) = &e.kind else {
            return None;
        };
        if self.sema.tcx.def(f.def).attrs.interrupt.is_none() {
            return None;
        }
        e.adjust.push(Adjust::FnToHandler);
        Some(e)
    }

    /// An arrow at an `fn` or closure type: C11 or C12; a capturing one at `fn` is
    /// EN1007.
    fn arrow_at(&mut self, mut e: hir::Expr, id: ArrowId, at: &FnSite) -> Option<hir::Expr> {
        if !at.closure
            && let Some(capture) = self.arrows[id].captures.first().copied()
        {
            self.report_capture(&e, capture);
            e.ty = self.error_ty();
            return Some(e);
        }
        let own = self.fn_sig_of(e.ty)?;
        if !self.sigs_fit(&own, &at.sig) {
            return None;
        }
        e.adjust.push(match (at.closure, at.sig.unsafety) {
            (true, _) => Adjust::ArrowToClosure,
            (false, true) => Adjust::FnToUnsafePtr,
            (false, false) => Adjust::FnToPtr,
        });
        Some(e)
    }

    /// EN1007: a capturing arrow where an `fn` value is needed (S:968).
    fn report_capture(&mut self, e: &hir::Expr, capture: Capture) {
        let name = self.locals[capture.local]
            .name
            .map_or_else(|| "a variable".to_owned(), |n| format!("`{n}`"));
        self.sema.emit(
            Diagnostic::new(
                Code::EN1007,
                "a function pointer cannot capture variables",
                e.span,
                format!("this arrow uses {name}"),
            )
            .with_secondary(capture.span, format!("{name} is captured here"))
            .note("an `fn` value holds no variables; only a closure parameter takes an arrow that uses them")
            .with_help(Help::text(CAPTURE_HELP)),
        );
    }

    /// A function's name at an `fn` or closure type: C11, C12, C15, C16, or EN0803,
    /// EN1006.
    fn fn_name_at(&mut self, mut e: hir::Expr, f: FnRef, at: &FnSite) -> Option<hir::Expr> {
        let tcx = &*self.sema.tcx;
        let data = tcx.def(f.def).clone();
        let sig = tcx.sig_opt(f.def)?.clone();
        // A `declare` or `@naked` function is `unsafe` too: the most specific reason
        // comes first.
        let precondition = if data.attrs.interrupt.is_some() {
            Some(Precondition::Interrupt)
        } else if data.kind == DefKind::DeclareFn {
            Some(Precondition::Declare)
        } else if data.attrs.naked {
            Some(Precondition::Naked)
        } else if !sig.requires.is_empty() {
            Some(Precondition::Requires)
        } else if sig.unsafety {
            Some(Precondition::Unsafe)
        } else {
            None
        };
        let hidden =
            data.kind == DefKind::LocalFn && !toplevel::hidden_args(self.sema, f.def).is_empty();
        let refused = match precondition {
            Some(Precondition::Interrupt) => Some(Precondition::Interrupt),
            Some(p) if at.closure || !at.sig.unsafety => Some(p),
            _ if hidden && !at.closure => Some(Precondition::Hidden),
            _ => None,
        };
        if let Some(why) = refused {
            self.report_precondition(&e, f.def, why, at.closure);
            e.ty = self.error_ty();
            return Some(e);
        }
        if let Some(problem) = self.copy_problem(f.def) {
            self.report_no_copy(&e, f.def, problem, at.closure);
            e.ty = self.error_ty();
            return Some(e);
        }
        self.instantiate_fn_value(&mut e, &f);
        let own = self.fn_sig_of(e.ty)?;
        let own_abi = match self.sema.tcx.kind(self.shallow(e.ty)) {
            TyKind::FnPtr(abi, _) => abi,
            _ => Abi::Enrang,
        };
        if !at.closure && own_abi != at.abi {
            return None;
        }
        if !self.sigs_fit(&own, &at.sig) {
            return None;
        }
        e.adjust.push(match (at.closure, at.sig.unsafety) {
            (true, _) => Adjust::ArrowToClosure,
            (false, true) => Adjust::FnToUnsafePtr,
            (false, false) => Adjust::FnToPtr,
        });
        Some(e)
    }

    /// An `fn` or closure value at an `fn` or closure type: C12 for an `fn` value at
    /// a closure parameter, C14 for a closure parameter passed on, C15 for a safe
    /// `fn` value at `unsafe fn`; a closure value at `fn` is EN1007.
    fn fn_value_at(&mut self, mut e: hir::Expr, at: &FnSite) -> Option<hir::Expr> {
        let own_ty = self.shallow(e.ty);
        let tcx = &*self.sema.tcx;
        let (own_closure, own_abi) = match tcx.kind(own_ty) {
            TyKind::FnPtr(abi, _) => (false, abi),
            TyKind::Closure(_) => (true, Abi::Enrang),
            _ => return None,
        };
        let own = self.fn_sig_of(own_ty)?;
        if own_closure && !at.closure {
            self.report_closure_value(&e);
            e.ty = self.error_ty();
            return Some(e);
        }
        let adjust = match (own_closure, at.closure) {
            (true, true) => {
                let param = matches!(
                    e.kind,
                    ExprKind::Local(l) if matches!(self.locals[l].kind, LocalKind::Param(_))
                );
                match param {
                    true => Adjust::ClosureReborrow,
                    false => Adjust::ArrowToClosure,
                }
            }
            (false, true) if !own.unsafety => Adjust::ArrowToClosure,
            (false, false) if !own.unsafety && at.sig.unsafety && own_abi == at.abi => {
                Adjust::FnToUnsafePtr
            }
            _ => return None,
        };
        let as_safe = FnPtrSig {
            unsafety: at.sig.unsafety,
            ..(*own).clone()
        };
        if !self.sigs_fit(&as_safe, &at.sig) {
            return None;
        }
        e.adjust.push(adjust);
        Some(e)
    }

    /// EN1007 for a closure value, which may capture, where an `fn` value is needed.
    fn report_closure_value(&mut self, e: &hir::Expr) {
        let text = self.snippet(e.span);
        // The variable a local's arrow captures first, named as S:966 names it.
        let capture = match e.kind {
            ExprKind::Local(l) => self
                .local_arrows
                .get(&l)
                .and_then(|&id| self.arrows[id].captures.first().copied()),
            _ => None,
        };
        let captured = capture.map(|c| {
            let name = self.locals[c.local]
                .name
                .map_or_else(|| "a variable".to_owned(), |n| format!("`{n}`"));
            (name, c.span)
        });
        let label = match (&e.kind, &captured) {
            (ExprKind::Local(l), _) if matches!(self.locals[*l].kind, LocalKind::Param(_)) => {
                format!("`{text}` is a closure parameter, which may use outer variables")
            }
            (_, Some((name, _))) => format!("`{text}` holds an arrow that uses {name}"),
            _ => format!("`{text}` holds an arrow that uses outer variables"),
        };
        let mut diag = Diagnostic::new(
            Code::EN1007,
            "a function pointer cannot capture variables",
            e.span,
            label,
        );
        if let Some((name, span)) = captured {
            diag = diag.with_secondary(span, format!("{name} is captured here"));
        }
        self.sema.emit(
            diag.note("an `fn` value holds no variables; only a closure parameter takes an arrow that uses them")
                .with_help(Help::text(CAPTURE_HELP)),
        );
    }

    /// EN0803 for function `def` at a safe `fn` or a closure parameter (S:674-675,
    /// S:981).
    fn report_precondition(
        &mut self,
        e: &hir::Expr,
        def: hir::DefId,
        why: Precondition,
        closure: bool,
    ) {
        let text = self.snippet(e.span);
        let into = if closure { "a closure" } else { "a safe `fn`" };
        let (message, label, help) = match why {
            Precondition::Unsafe => (
                format!("`{text}` is an `unsafe function`, so it can't become {into}"),
                "its callers must uphold what it requires".to_owned(),
                Some("convert it to an `unsafe fn(...)` type, which only `unsafe` code may call"),
            ),
            Precondition::Requires => (
                format!("`{text}` has `@requires`, so it can't become {into}"),
                "it runs only where the CPU features it requires were checked".to_owned(),
                Some("convert it to an `unsafe fn(...)` type, which only `unsafe` code may call"),
            ),
            Precondition::Declare => (
                format!("`{text}` is a `declare function`, so it can't become {into}"),
                "foreign code is called only from `unsafe`".to_owned(),
                Some("convert it to an `unsafe fn(...)` type of the same ABI"),
            ),
            Precondition::Naked => (
                format!("`{text}` is `@naked`, so it can't become {into}"),
                "a naked function has no frame a safe call could rely on".to_owned(),
                Some("convert it to an `unsafe fn(...)` type, which only `unsafe` code may call"),
            ),
            Precondition::Interrupt => (
                format!(
                    "`{text}` is an `@interrupt` function, so it can only become an `InterruptHandler`"
                ),
                "the CPU calls it, never code".to_owned(),
                None,
            ),
            Precondition::Hidden => {
                let vars: Vec<String> = toplevel::hidden_args(self.sema, def)
                    .iter()
                    .filter_map(|v| self.sema.res.toplevel.vars.get(v.0 as usize))
                    .map(|v| format!("`{}`", v.name))
                    .collect();
                let what = match vars.len() {
                    1 => "a hidden argument",
                    _ => "hidden arguments",
                };
                (
                    format!("`{text}` uses top-level variables, so it can't become an `fn`"),
                    format!("it takes {} as {what}", vars.join(", ")),
                    Some("pass it where a closure parameter is expected, which may use them"),
                )
            }
        };
        let mut diag = Diagnostic::new(Code::EN0803, message, e.span, label);
        if let Some(help) = help {
            diag = diag.with_help(Help::text(help));
        }
        self.sema.emit(diag);
    }

    /// Why function `def` has no single copy an `fn` value or closure could name: a
    /// by-value interface parameter, or an `&I` parameter of an interface that no
    /// table can serve (S:682, A:894).
    fn copy_problem(&self, def: hir::DefId) -> Option<CopyProblem> {
        let tcx = &*self.sema.tcx;
        let sig = tcx.sig_opt(def)?;
        for p in &sig.params {
            let (inner, by_value) = match tcx.kind(p.ty) {
                TyKind::Ref(inner) => (inner, false),
                _ => (p.ty, true),
            };
            let TyKind::Param(param) = tcx.kind(inner) else {
                continue;
            };
            let Some(Implicit::Interface(adt)) = tcx.param(param).implicit else {
                continue;
            };
            if by_value {
                return Some(CopyProblem::ByValue(p.name, adt));
            }
            if let Some(member) = self.needs_class(adt) {
                return Some(CopyProblem::NoTable(p.name, adt, member));
            }
        }
        None
    }

    /// EN1006 for a function with no copy an `fn` value or closure could name
    /// (S:682, A:894).
    fn report_no_copy(
        &mut self,
        e: &hir::Expr,
        def: hir::DefId,
        problem: CopyProblem,
        closure: bool,
    ) {
        let text = self.snippet(e.span);
        let into = if closure { "a closure" } else { "an `fn`" };
        let fn_name = self
            .sema
            .tcx
            .def(def)
            .name()
            .map_or_else(|| text.clone(), |n| n.as_str().to_owned());
        let (label, note, help) = match problem {
            CopyProblem::ByValue(param, adt) => {
                let iface = self.sema.tcx.adt(adt).name;
                (
                    format!(
                        "`{text}` takes `{param}`, {} `{iface}`, by value",
                        crate::classes::sig::article(iface.as_str())
                    ),
                    format!(
                        "`{fn_name}` has a copy per class passed as `{param}`, and none {into} could name"
                    ),
                    format!(
                        "take `{param}: &{iface}`, which one copy serves through the method table"
                    ),
                )
            }
            CopyProblem::NoTable(param, adt, member) => {
                let iface = self.sema.tcx.adt(adt).name;
                let why = self.member_reason(adt, member);
                (
                    format!(
                        "`{text}` takes `{param}`, a `&{iface}`, which needs its two-word form here"
                    ),
                    why,
                    format!("make it generic: `{fn_name}<T extends {iface}>({param}: &T)`"),
                )
            }
        };
        self.sema
            .emit(iface_unsupported(e.span, label, note, Some(help)));
    }

    /// A generic function named as a value at its use: each written type parameter a
    /// fresh variable, whose bounds are checked after inference; each `&I`
    /// parameter's class the interface, its two-word form; each object-type
    /// parameter's its own shape.
    fn instantiate_fn_value(&mut self, e: &mut hir::Expr, f: &FnRef) {
        let tcx = &*self.sema.tcx;
        let Some(sig) = tcx.sig_opt(f.def) else {
            return;
        };
        let own = tcx.generics(sig.generics).params.clone();
        if own.is_empty() {
            return;
        }
        let mut args = Vec::with_capacity(own.len());
        let mut written = false;
        for &p in &own {
            let tcx = &*self.sema.tcx;
            let arg = match tcx.param(p).implicit {
                Some(Implicit::Interface(adt)) => {
                    let bound = tcx
                        .param(p)
                        .bounds
                        .iter()
                        .map(|&b| tcx.bound(b))
                        .find(|b| b.adt() == adt)
                        .map_or_else(|| tcx.empty_list(), |b| b.args());
                    tcx.intern_ty(TyKind::Adt(adt, bound))
                }
                Some(Implicit::Shape(shape)) => tcx.intern_ty(TyKind::Object(shape)),
                Some(Implicit::Opaque) => tcx.mk_param(p),
                None => {
                    written = true;
                    let var = self.infer.fresh(VarKind::Any);
                    self.sema.tcx.intern_ty(TyKind::Infer(var))
                }
            };
            args.push(arg);
        }
        let tcx = &*self.sema.tcx;
        let ty = tcx.subst(e.ty, &own, &args);
        let all = tcx.list(f.args).to_vec();
        let n = all.len().saturating_sub(own.len());
        let mut full = all[..n].to_vec();
        full.extend(args);
        let list = tcx.intern_list(&full);
        e.ty = ty;
        e.kind = ExprKind::Const(ConstValue::FnAddr(FnRef {
            def: f.def,
            args: list,
        }));
        if written {
            self.deferred.push(Deferred::Bounds {
                span: e.span,
                callee: f.def,
                args: full,
            });
        }
    }

    /// The signature of an `fn` or closure type.
    fn fn_sig_of(&self, t: Ty) -> Option<Arc<FnPtrSig>> {
        let tcx = &*self.sema.tcx;
        match tcx.kind(self.shallow(t)) {
            TyKind::FnPtr(_, sig) | TyKind::Closure(sig) => Some(tcx.fn_sig(sig)),
            _ => None,
        }
    }

    /// Whether `own` fits `want`: the same parameter and result types, rows
    /// ignored, unified at once or not at all; `own` may be safe where `want` is
    /// `unsafe` (C15).
    fn sigs_fit(&mut self, own: &FnPtrSig, want: &FnPtrSig) -> bool {
        if own.params.len() != want.params.len() || (own.unsafety && !want.unsafety) {
            return false;
        }
        let tcx = &*self.sema.tcx;
        let mut a: Vec<Ty> = own.params.iter().map(|&(t, _)| t).collect();
        a.push(own.ret);
        let mut b: Vec<Ty> = want.params.iter().map(|&(t, _)| t).collect();
        b.push(want.ret);
        let (a, b) = (tcx.mk_tuple(&a), tcx.mk_tuple(&b));
        self.unify(a, b)
    }
}

/// EN1007's help, SPEC 16's workaround column.
const CAPTURE_HELP: &str =
    "Keep it in a local or pass it as a closure parameter, or pass the data explicitly";

/// An `fn` or closure type a value converts to.
struct FnSite {
    closure: bool,
    sig: Arc<FnPtrSig>,
    abi: Abi,
    #[allow(dead_code)] // Kept for the messages of later rows.
    target: Ty,
}

/// Why a function name never becomes a safe `fn` or a closure (EN0803).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Precondition {
    Unsafe,
    Requires,
    Declare,
    Naked,
    Interrupt,
    /// A local function with hidden arguments, at an `fn` type only.
    Hidden,
}

/// Why a function has no single copy to name (EN1006).
#[derive(Copy, Clone, Debug)]
enum CopyProblem {
    /// A by-value interface parameter.
    ByValue(enrang_base::Symbol, hir::AdtId),
    /// An `&I` parameter of an interface whose member needs the class.
    NoTable(enrang_base::Symbol, hir::AdtId, enrang_base::Symbol),
}

// -------------------------------------------------------------------------------
// The walk over a typed arrow body: every expression, and each `return` with its
// operand. Nested arrows are other `ArrowBody`s, reached only by id.

/// What the walk meets.
pub(crate) enum Seen<'e> {
    Expr(&'e hir::Expr),
    Return(Option<&'e hir::Expr>, Span),
}

pub(crate) fn walk_block<'e>(b: &'e hir::Block, f: &mut dyn FnMut(Seen<'e>)) {
    for s in &b.stmts {
        walk_stmt(s, f);
    }
}

fn walk_opt<'e>(e: Option<&'e hir::Expr>, f: &mut dyn FnMut(Seen<'e>)) {
    if let Some(e) = e {
        walk_expr(e, f);
    }
}

fn walk_stmt<'e>(s: &'e hir::Stmt, f: &mut dyn FnMut(Seen<'e>)) {
    match &s.kind {
        StmtKind::Let { init, .. } => walk_opt(init.as_ref(), f),
        StmtKind::Destructure { init, .. } => walk_expr(init, f),
        StmtKind::If { cond, then_, else_ } => {
            walk_expr(cond, f);
            walk_block(then_, f);
            if let Some(b) = else_ {
                walk_block(b, f);
            }
        }
        StmtKind::While { cond, body, .. } | StmtKind::DoWhile { body, cond, .. } => {
            walk_expr(cond, f);
            walk_block(body, f);
        }
        StmtKind::For {
            init,
            cond,
            step,
            body,
            ..
        } => {
            if let Some(s) = init {
                walk_stmt(s, f);
            }
            walk_opt(cond.as_ref(), f);
            if let Some(s) = step {
                walk_stmt(s, f);
            }
            walk_block(body, f);
        }
        StmtKind::ForOf { source, body, .. } => {
            match source {
                ForSource::Path { place } => walk_expr(place, f),
                ForSource::Once { value, .. } => walk_expr(value, f),
                ForSource::Range { lo, hi } => {
                    walk_expr(lo, f);
                    walk_expr(hi, f);
                }
            }
            walk_block(body, f);
        }
        StmtKind::Return(e) => {
            f(Seen::Return(e.as_ref(), s.span));
            walk_opt(e.as_ref(), f);
        }
        StmtKind::Break(_) | StmtKind::Continue(_) => {}
        StmtKind::Block(b) | StmtKind::Unsafe(b) => walk_block(b, f),
        StmtKind::Expr(e) => walk_expr(e, f),
        StmtKind::Expect(x) => {
            walk_expr(&x.actual, f);
            for arg in &x.args {
                match arg {
                    ExpectArg::Expr(e) => walk_expr(e, f),
                    ExpectArg::Arm(v) => walk_arm_value(v, f),
                }
            }
        }
    }
}

fn walk_arm_value<'e>(v: &'e ArmValue, f: &mut dyn FnMut(Seen<'e>)) {
    if let ArmValue::Cond(e) = v {
        walk_expr(e, f);
    }
}

fn walk_callee<'e>(c: &'e Callee, f: &mut dyn FnMut(Seen<'e>)) {
    if let Callee::FnPtr(e) = c {
        walk_expr(e, f);
    }
}

fn walk_all<'e>(es: &'e [hir::Expr], f: &mut dyn FnMut(Seen<'e>)) {
    for e in es {
        walk_expr(e, f);
    }
}

pub(crate) fn walk_expr<'e>(e: &'e hir::Expr, f: &mut dyn FnMut(Seen<'e>)) {
    f(Seen::Expr(e));
    match &e.kind {
        ExprKind::Local(_)
        | ExprKind::Static(_)
        | ExprKind::Const(_)
        | ExprKind::Arrow(_)
        | ExprKind::Never
        | ExprKind::NullLit => {}
        ExprKind::Field(b, _)
        | ExprKind::Deref(b)
        | ExprKind::NarrowedPayload(b, ..)
        | ExprKind::Repeat(b, _)
        | ExprKind::Unary(_, b)
        | ExprKind::Cast(b, _)
        | ExprKind::Borrow(b)
        | ExprKind::AddrOf(b)
        | ExprKind::Try(b, _)
        | ExprKind::NonNull(b)
        | ExprKind::VoidOp(b) => walk_expr(b, f),
        ExprKind::Index(a, b)
        | ExprKind::Binary(_, a, b)
        | ExprKind::Logical(_, a, b)
        | ExprKind::Coalesce(a, b) => {
            walk_expr(a, f);
            walk_expr(b, f);
        }
        ExprKind::Template(parts) => {
            for part in parts {
                if let TplPart::Hole(h) = part {
                    walk_expr(h, f);
                }
            }
        }
        ExprKind::ArrayLit(items) | ExprKind::TupleLit(items) => walk_all(items, f),
        ExprKind::ArrayBuild { parts, .. } => {
            for part in parts {
                match part {
                    ArrayPart::Item(x) | ArrayPart::Spread(x, _) => walk_expr(x, f),
                }
            }
        }
        ExprKind::NewNamed { fields, .. } => {
            for (_, x) in fields {
                walk_expr(x, f);
            }
        }
        ExprKind::ObjectLit { fields, .. } | ExprKind::VariantLit { fields, .. } => {
            walk_all(fields, f)
        }
        ExprKind::New { values, .. } => walk_all(values, f),
        ExprKind::Call {
            callee,
            receiver,
            args,
        } => {
            walk_callee(callee, f);
            if let Some(r) = receiver {
                walk_expr(r, f);
            }
            walk_all(args, f);
        }
        ExprKind::OptionalChain(chain) => {
            walk_expr(&chain.base, f);
            if let OptMember::Call { callee, args } = &chain.member {
                walk_callee(callee, f);
                walk_all(args, f);
            }
        }
        ExprKind::Ternary(a, b, c) => {
            walk_expr(a, f);
            walk_expr(b, f);
            walk_expr(c, f);
        }
        ExprKind::Assign { target, value, .. } => {
            walk_expr(target, f);
            walk_expr(value, f);
        }
        ExprKind::IncDec { target, .. } => walk_expr(target, f),
        ExprKind::Match { subject, arms } => {
            walk_expr(subject, f);
            for arm in arms {
                for v in &arm.values {
                    walk_arm_value(v, f);
                }
                walk_opt(arm.guard.as_ref(), f);
                match &arm.body {
                    ArmBody::Expr(x) => walk_expr(x, f),
                    ArmBody::Block(b) => walk_block(b, f),
                    ArmBody::Return(x) => {
                        f(Seen::Return(x.as_ref(), arm.span));
                        walk_opt(x.as_ref(), f);
                    }
                    ArmBody::Break(_) | ArmBody::Continue(_) => {}
                }
            }
        }
        ExprKind::Asm(asm) => {
            for (_, x) in &asm.ins {
                walk_expr(x, f);
            }
            for (_, x) in &asm.outs {
                walk_opt(x.as_ref(), f);
            }
        }
        ExprKind::Destructure { pat, value } => {
            pat.places().into_iter().for_each(|p| walk_expr(p, f));
            walk_expr(value, f);
        }
    }
}
