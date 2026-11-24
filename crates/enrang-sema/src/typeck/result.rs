//! `Result`, `Err` and `?` (plan d.12; SPEC 4.5 C19, 6; A:888; owner 4C).
//!
//! **C19.** In a function or arrow whose result type `Result<T, E>` is written or
//! expected (never one its body decides, A:920), a `return` operand, an arrow's
//! expression body, and the ternary branches and `match` arms that flow there are
//! wrapped as a success. An operand that takes its type from context (a bracket or
//! object literal, `[]`, `null`, a number literal, or a string literal where `T` is a
//! string-literal union) is checked against `T`, then `WrapOk`; any other is typed
//! with the whole `Result` as its hint, so `Ok(x)` and `Err(x)` read it, and is
//! coerced to the `Result` when it is one (or `never`), else coerced to `T` and
//! wrapped, so a C06 or C22 chain may come first (plan choice). A wrapped operand that
//! `Err` would also take as it is, a text at `E = Failure`, a fixed text that is a
//! value of a literal-union `E`, or a value whose own type is `E`, is EN0455 with
//! `help: write `Ok(x)` or `Err(x)``, or, for a `string` place no move may leave,
//! `Ok(x.clone())` or `Err(&x)` (S:1139); a text at `E = Failure` is EN0455 even
//! where `T` is a literal union that also takes it (plan choice). A `match` that flows to a C19 site is typed
//! with each expression arm as a `return` of its value, the same program written arm
//! by arm, so the arms get C19 one by one and the `match` itself is `never` (plan
//! choice: the typing seams give arms no hook of their own); a `match` with a block arm
//! is coerced as a whole, with no C19 in its arms. `return;` and falling off a
//! `Result<void, E>` body are `return Ok();` (S:677).
//!
//! **`Err(e)`** (SPEC 6's form table) reads `Result<T, E>` from the expected type, or,
//! with none, takes `E` from `e`, `Failure` for a text, and a fresh `T`. Its
//! `ErrForm` (A:888): at `Failure`, `Text` for a fixed text or a template,
//! `TextMove` for any other `string`, `TextCopy` for a `&string`, `Value` for a
//! `Failure`, `IntoFailure` for a value of another error type; at a literal-union
//! `E`, `Text` for a fixed text (EN0401 when it is no value of the union), `Value`
//! for a value of `E`; at any other `E`, `Value`, the operand coerced to `E`
//! (EN0401). Anything else is EN0401.
//!
//! **`e?`** on `Result<T, E>` is `T`: `TryKind::Result` into a `Result<_, E>` of the
//! identical `E`, `ResultIntoFailure` into a `Result<_, Failure>` from another error
//! type, else EN0425 with the `Result<T>` help; among a program's statements any
//! error type (`Result`, S:1143). On `T | null` it is `T`, `TryKind::Nullable`, in a
//! function or arrow returning `_ | null`. In an arrow whose body decides its result,
//! `?` decides it as `Result<_, E>` or `_ | null`. Anywhere else EN0424, and on any
//! other type EN0429.
//!
//! **Unused results.** An expression statement of type `Result` is EN0426 (G20); a
//! call of a `@mustUse` function or method whose result is unused is warning EN0453
//! with the `keep it` fix when the receiver is a local it may assign, a `let` local
//! or a `let` parameter, of the result's type, else a help naming `void` (S:1142,
//! G23); an interface value by value there, as `b.unbox();` or `void
//! b.unbox();`, is EN1006 (T:862). `void e` silences the first two, and so does an
//! assignment.

use enrang_base::{BytePos, Span};
use enrang_diag::{Code, Diagnostic, Edit, Help};
use enrang_hir::{
    self as hir, Adjust, AdtKind, Callee, DefId, ErrForm, ExprKind, FormKind, LangItem, LocalKind,
    Mark, OptMember, StmtKind, TryKind, Ty, TyKind,
};
use enrang_syntax::ast;

use crate::typeck::expr::strip_parens;
use crate::typeck::infer::VarKind;
use crate::typeck::{Expect, FnCtxt, RetOrigin, Site};

/// A C19 site's result type and its parts.
#[derive(Copy, Clone, Debug)]
pub(crate) struct C19 {
    pub result: Ty,
    pub ok: Ty,
    pub err: Ty,
}

impl FnCtxt<'_, '_> {
    /// `return e;`. In an arrow whose body decides its result the operand is typed as
    /// it is, and `check_arrow` unifies the returns once the body is typed; at a
    /// written or expected `Result` the operand is C19's; anywhere else it coerces
    /// to the result type. `return;` where a value is due is EN0401 `` mismatched
    /// types: expected `i64`, found `void` `` at the `return` (only a
    /// `Result<void, E>` result takes it as `return Ok();`, S:677).
    pub(crate) fn check_return(&mut self, e: Option<&ast::Expr>, span: Span) -> StmtKind {
        let ctx = self.ret_ctx();
        if ctx.origin == RetOrigin::Body {
            return StmtKind::Return(e.map(|e| self.check_expr(e, Expect::None)));
        }
        let Some(e) = e else {
            self.check_bare_return(ctx.ty, span);
            return StmtKind::Return(None);
        };
        if let Some(c) = self.c19_target(ctx.ty) {
            if let Some(arms) = self.c19_match(e) {
                if self.sema.tcx.kind(self.shallow(arms.ty)) == TyKind::Never {
                    return StmtKind::Expr(arms);
                }
                // A block arm that ends gives `void` to the `return` (S:1131).
                return StmtKind::Return(Some(self.coerce(arms, c.result, Site::Return)));
            }
            return StmtKind::Return(Some(self.check_wrapped(e, c)));
        }
        StmtKind::Return(Some(
            self.check_expr(e, Expect::Coerce(ctx.ty, Site::Return)),
        ))
    }

    /// An arrow's expression body at its written or expected result: C19's when that
    /// is a `Result`, else coerced to it (S:656).
    pub(crate) fn check_ret_value(&mut self, e: &ast::Expr) -> hir::Expr {
        let ctx = self.ret_ctx();
        if ctx.origin != RetOrigin::Body
            && let Some(c) = self.c19_target(ctx.ty)
        {
            return self.check_wrapped(e, c);
        }
        self.check_expr(e, Expect::Coerce(ctx.ty, Site::Return))
    }

    /// EN0401 for `return;` in a body whose result `ret` is no `void`, `Error` or
    /// `Result<void, E>`. Among a program's statements `return;` exits with 0, as no
    /// `return` does (S:1143, plan choice).
    fn check_bare_return(&mut self, ret: Ty, span: Span) {
        if matches!(self.owner, hir::BodyOwner::Statements(_)) && self.arrow_stack.is_empty() {
            return;
        }
        let void = self.sema.tcx.common().void;
        let t = self.shallow(ret);
        if self.var_kind(t) == Some(VarKind::Any) {
            let _ = self.unify(t, void);
            return;
        }
        let resolved = self.resolve(t);
        if self.nothing_due(resolved) {
            return;
        }
        let keyword = self.return_keyword(span);
        let shown = self.ty_str(resolved);
        let mut diag = Diagnostic::new(
            Code::EN0401,
            format!("mismatched types: expected `{shown}`, found `void`"),
            keyword,
            "this `return` gives no value",
        );
        if self.arrow_stack.is_empty()
            && let Some(ret_span) = self.ret_span
        {
            diag = diag.with_secondary(
                ret_span,
                format!("`{shown}` is required by the return type"),
            );
        }
        self.sema.emit(diag);
    }

    /// Whether a body whose result is the resolved `ret` may end with no value:
    /// `void`, `never`, `Error`, or `Result<void, E>`.
    pub(crate) fn nothing_due(&self, ret: Ty) -> bool {
        let tcx = &*self.sema.tcx;
        match tcx.kind(ret) {
            TyKind::Void | TyKind::Never | TyKind::Error => true,
            TyKind::Adt(adt, args) if tcx.is_lang_adt(adt, LangItem::Result) => tcx
                .list(args)
                .first()
                .is_some_and(|&ok| tcx.kind(self.shallow(ok)) == TyKind::Void),
            _ => tcx.references_error(ret),
        }
    }

    /// The `return` keyword at the start of the statement or arm at `span`.
    fn return_keyword(&self, span: Span) -> Span {
        let text = self.snippet(span);
        match text.find("return") {
            Some(offset) => {
                let lo = BytePos(span.lo.0 + offset as u32);
                Span {
                    lo,
                    hi: BytePos(lo.0 + 6),
                }
            }
            None => span,
        }
    }

    // ---------------------------------------------------------------------------
    // C19.

    /// The C19 site a written or expected result `ret` makes: `Result<T, E>`.
    fn c19_target(&self, ret: Ty) -> Option<C19> {
        let t = self.shallow(ret);
        let (ok, err) = self.result_parts(t)?;
        Some(C19 { result: t, ok, err })
    }

    /// `T` and `E` of a type that is `Result<T, E>`.
    pub(crate) fn result_parts(&self, t: Ty) -> Option<(Ty, Ty)> {
        let tcx = &*self.sema.tcx;
        match tcx.kind(self.shallow(t)) {
            TyKind::Adt(adt, args) if tcx.is_lang_adt(adt, LangItem::Result) => {
                let args = tcx.list(args);
                Some((*args.first()?, *args.get(1)?))
            }
            _ => None,
        }
    }

    /// `e` at C19 site `c`: a ternary's branches each at `c`, a `match` arm by arm,
    /// anything else as a leaf.
    fn check_wrapped(&mut self, e: &ast::Expr, c: C19) -> hir::Expr {
        let inner = strip_parens(e);
        match &inner.kind {
            ast::ExprKind::Ternary(cond, a, b) => {
                let cond = self.check_cond(cond);
                let (when_true, when_false) = self.cond_facts(&cond);
                self.flow = when_true;
                let then_ = self.check_wrapped(a, c);
                let after_then = std::mem::replace(&mut self.flow, when_false);
                let else_ = self.check_wrapped(b, c);
                let after_else = std::mem::take(&mut self.flow);
                self.join(vec![after_then, after_else]);
                self.mk_expr(
                    c.result,
                    inner.span,
                    ExprKind::Ternary(Box::new(cond), Box::new(then_), Box::new(else_)),
                )
            }
            ast::ExprKind::Match { .. } => match self.c19_match(inner) {
                Some(mut arms) => {
                    if self.sema.tcx.kind(self.shallow(arms.ty)) == TyKind::Never {
                        arms.adjust.push(Adjust::NeverToAny);
                        arms
                    } else {
                        // A block arm that ends gives `void` to the site.
                        self.coerce(arms, c.result, Site::Return)
                    }
                }
                None => self.check_expr(inner, Expect::Coerce(c.result, Site::Return)),
            },
            _ => self.wrap_leaf(inner, c),
        }
    }

    /// A `match` flowing to a C19 site, typed with each expression arm as a `return`
    /// of its value (S:1139); a block arm is kept, and one that ends gives the
    /// `match` its `void`, which the caller reports at the site.
    fn c19_match(&mut self, e: &ast::Expr) -> Option<hir::Expr> {
        let inner = strip_parens(e);
        let ast::ExprKind::Match { subject, arms } = &inner.kind else {
            return None;
        };
        let arms: Vec<ast::MatchArm> = arms
            .iter()
            .map(|arm| {
                let mut arm = arm.clone();
                if let ast::ArmBody::Expr(value) = arm.body {
                    arm.body = ast::ArmBody::Return(Some(value));
                }
                arm
            })
            .collect();
        Some(self.check_match(subject, &arms, inner.span, Expect::None, true))
    }

    /// A C19 operand that is neither a ternary nor a `match`.
    fn wrap_leaf(&mut self, e: &ast::Expr, c: C19) -> hir::Expr {
        if self.contextual(e, c.ok) {
            let typed = self.check_expr(e, Expect::Coerce(c.ok, Site::Return));
            return self.finish_wrap(e, typed, c);
        }
        let typed = self.check_expr(e, Expect::Has(c.result));
        let t = self.shallow(typed.ty);
        let whole = self.is_error(t)
            || self.sema.tcx.kind(t) == TyKind::Never
            || self.var_kind(t) == Some(VarKind::Any)
            || self.result_parts(t).is_some();
        if whole {
            return self.coerce(typed, c.result, Site::Return);
        }
        let before = typed.adjust.len();
        let mut typed = self.coerce(typed, c.ok, Site::Return);
        // C19 is the site's one wrap (S:656, G51): an operand that needs C06 or
        // C07 to reach `T` first is EN0401, as `Ok(x)` would take it.
        if typed.adjust[before.min(typed.adjust.len())..]
            .iter()
            .any(|a| matches!(a, Adjust::WrapNull | Adjust::WrapNullRef))
        {
            let (st, sf) = (self.ty_str(c.result), self.ty_str(t));
            let text = self.snippet(typed.span);
            self.sema.emit(
                Diagnostic::new(
                    Code::EN0401,
                    format!("mismatched types: expected `{st}`, found `{sf}`"),
                    typed.span,
                    format!("this is `{sf}`"),
                )
                .note("a `return` wraps its value once, as a success; making it nullable too would be a second wrap")
                .with_help(Help::text(format!("wrap it yourself: `Ok({text})`"))),
            );
            typed.ty = self.error_ty();
            return typed;
        }
        self.finish_wrap(e, typed, c)
    }

    /// Whether operand `e` takes its type from context (S:1139), so it is checked
    /// against `ok` itself.
    fn contextual(&self, e: &ast::Expr, ok: Ty) -> bool {
        let number =
            |e: &ast::Expr| matches!(e.kind, ast::ExprKind::Int { .. } | ast::ExprKind::Float(_));
        match &e.kind {
            ast::ExprKind::Array(_)
            | ast::ExprKind::Repeat(..)
            | ast::ExprKind::ObjectLit(_)
            | ast::ExprKind::Null => true,
            _ if number(e) => true,
            ast::ExprKind::Unary(ast::UnOp::Neg, inner) => number(strip_parens(inner)),
            ast::ExprKind::Str(_) | ast::ExprKind::RawTemplate(_) => {
                let t = self.shallow(ok);
                let t = match self.sema.tcx.kind(t) {
                    TyKind::Nullable(inner) => inner,
                    _ => t,
                };
                self.str_union_of(t).is_some()
            }
            _ => false,
        }
    }

    /// `typed`, already at `T`, wrapped as a success, or EN0455 when `Err` would
    /// also take it as it is.
    fn finish_wrap(&mut self, e: &ast::Expr, mut typed: hir::Expr, c: C19) -> hir::Expr {
        if self.is_error(typed.ty) {
            return typed;
        }
        if self.err_would_take(e, &typed, c.err) {
            self.report_either(&typed);
            typed.ty = self.error_ty();
            return typed;
        }
        typed.adjust.push(Adjust::WrapOk);
        typed
    }

    /// Whether `Err` at `err` would take the operand `e` (typed `typed`) as it is:
    /// a text at `Failure`, a fixed text that is a value of a literal-union `E`, or
    /// a value whose own type is `E` (S:1139).
    fn err_would_take(&self, e: &ast::Expr, typed: &hir::Expr, err: Ty) -> bool {
        let e = strip_parens(e);
        let fixed = match &e.kind {
            ast::ExprKind::Str(text) | ast::ExprKind::RawTemplate(text) => Some(*text),
            _ => None,
        };
        let template = matches!(e.kind, ast::ExprKind::Template(_));
        let ty = self.resolve(typed.ty);
        let err = self.resolve(err);
        if self.is_failure(err) && (fixed.is_some() || template || self.is_text(ty)) {
            return true;
        }
        if let (Some(adt), Some(text)) = (self.str_union_of(err), fixed)
            && self.union_case(adt, text).is_some()
        {
            return true;
        }
        let tcx = &*self.sema.tcx;
        !tcx.has_infer(ty) && !tcx.references_error(ty) && ty == err
    }

    /// EN0455 at the wrapped operand `typed` (S:1139, A:888).
    fn report_either(&mut self, typed: &hir::Expr) {
        let text = self.snippet(typed.span);
        let help = if self.no_move_place(typed) {
            let place = text.trim_start_matches('&');
            format!("write `Ok({place}.clone())` or `Err(&{place})`")
        } else {
            format!("write `Ok({text})` or `Err({text})`")
        };
        self.sema.emit(
            Diagnostic::new(
                Code::EN0455,
                format!("`{text}` could be a success or an error here"),
                typed.span,
                "`Err` would take this as it is",
            )
            .with_help(Help::text(help)),
        );
    }

    /// Whether `e` is a `string` place that no move may leave: one reached through a
    /// reference or an index (A:888).
    fn no_move_place(&self, e: &hir::Expr) -> bool {
        if self.sema.tcx.kind(self.resolve(e.ty)) != TyKind::Str {
            return false;
        }
        fn behind_ref(tcx: &hir::Tcx, e: &hir::Expr) -> bool {
            match &e.kind {
                ExprKind::Index(..) => true,
                ExprKind::Deref(base) => {
                    matches!(tcx.kind(base.ty), TyKind::Ref(_) | TyKind::Boxed(_))
                        || behind_ref(tcx, base)
                }
                ExprKind::Field(base, _) | ExprKind::NarrowedPayload(base, ..) => {
                    behind_ref(tcx, base)
                }
                _ => false,
            }
        }
        behind_ref(self.sema.tcx, e)
    }

    /// Whether the resolved `t` is `string` or `&string`.
    fn is_text(&self, t: Ty) -> bool {
        let tcx = &*self.sema.tcx;
        match tcx.kind(t) {
            TyKind::Str => true,
            TyKind::Ref(inner) => tcx.kind(self.shallow(inner)) == TyKind::Str,
            _ => false,
        }
    }

    /// Whether `t` is the prelude's `Failure`.
    pub(crate) fn is_failure(&self, t: Ty) -> bool {
        let tcx = &*self.sema.tcx;
        match tcx.kind(self.shallow(t)) {
            TyKind::Adt(adt, _) => tcx.is_lang_adt(adt, LangItem::Failure),
            _ => false,
        }
    }

    /// Whether `t` is an error type (SPEC 6): an enum, `Failure`, or a class that
    /// implements `Error`.
    fn is_result_error_type(&self, t: Ty) -> bool {
        let tcx = &*self.sema.tcx;
        let TyKind::Adt(adt, _) = tcx.kind(self.shallow(t)) else {
            return false;
        };
        match &tcx.adt(adt).kind {
            AdtKind::Enum(_) => true,
            AdtKind::Class(class) => {
                tcx.is_lang_adt(adt, LangItem::Failure)
                    || class.implements.iter().any(|&i| match tcx.kind(i) {
                        TyKind::Adt(iface, _) => tcx.is_lang_adt(iface, LangItem::Error),
                        _ => false,
                    })
            }
            AdtKind::Interface(_) => false,
        }
    }

    // ---------------------------------------------------------------------------
    // `Err(e)`.

    /// `Err(...)`: its `Result` type from the expected one or its operand, and its
    /// `ErrForm`.
    pub(crate) fn check_err(&mut self, e: &ast::Expr, ex: Expect) -> hir::Expr {
        let ast::ExprKind::Call { args, .. } = &e.kind else {
            return self.error_expr(e.span);
        };
        let [arg] = args.as_slice() else {
            let given = match args.len() {
                0 => "none were given".to_owned(),
                n => format!("{n} were given"),
            };
            let label = match args.is_empty() {
                true => "too few arguments",
                false => "too many arguments",
            };
            self.sema.emit(Diagnostic::new(
                Code::EN0423,
                format!("`Err` takes 1 argument, but {given}"),
                e.span,
                label,
            ));
            for arg in args {
                let _ = self.check_expr(arg, Expect::None);
            }
            return self.error_expr(e.span);
        };
        let expected = ex.ty().map(|t| {
            let t = self.shallow(t);
            match self.sema.tcx.kind(t) {
                TyKind::Nullable(inner) => self.shallow(inner),
                _ => t,
            }
        });
        let (ok, err) = match expected.and_then(|t| self.result_parts(t)) {
            Some((ok, err)) => (ok, Some(err)),
            None => (self.fresh_var(), None),
        };
        let known = err.filter(|&e| self.var_kind(e).is_none());
        let (value, form, err_ty) = match known {
            Some(err) if self.is_failure(err) => {
                let (value, form) = self.err_at_failure(arg);
                (value, form, err)
            }
            Some(err) if self.str_union_of(err).is_some() => {
                let value = self.check_expr(arg, Expect::Coerce(err, Site::Arg));
                let form = match strip_parens(arg).kind {
                    ast::ExprKind::Str(_) | ast::ExprKind::RawTemplate(_) => ErrForm::Text,
                    _ => ErrForm::Value,
                };
                (value, form, err)
            }
            Some(err) => {
                let value = self.check_expr(arg, Expect::Coerce(err, Site::Arg));
                (value, ErrForm::Value, err)
            }
            None => {
                let (value, form, own) = self.err_from_operand(arg);
                if let Some(var) = err {
                    let _ = self.unify(var, own);
                }
                (value, form, own)
            }
        };
        let error = self.error_ty();
        // A rejected operand makes the whole form `Error`, its success type included,
        // so nothing more is reported about it.
        let ty = if self.is_error(value.ty) || self.is_error(err_ty) {
            let _ = self.unify(ok, error);
            error
        } else {
            self.sema.tcx.mk_result(ok, err_ty).unwrap_or(error)
        };
        self.mk_expr(
            ty,
            e.span,
            ExprKind::Call {
                callee: Callee::Form(FormKind::Err(form)),
                receiver: None,
                args: vec![value],
            },
        )
    }

    /// A fresh variable no message names: `Err`'s success type with no expected one.
    fn fresh_var(&mut self) -> Ty {
        let var = self.infer.fresh(VarKind::Any);
        self.sema.tcx.intern_ty(TyKind::Infer(var))
    }

    /// `Err(arg)` at `E = Failure`: a text or an error value.
    fn err_at_failure(&mut self, arg: &ast::Expr) -> (hir::Expr, ErrForm) {
        let value = self.check_expr(arg, Expect::None);
        let form = match strip_parens(arg).kind {
            ast::ExprKind::Str(_) | ast::ExprKind::RawTemplate(_) | ast::ExprKind::Template(_) => {
                Some(ErrForm::Text)
            }
            _ => self.text_or_error_form(&value),
        };
        match form {
            Some(form) => (value, form),
            None => {
                self.report_not_text(&value);
                let mut value = value;
                value.ty = self.error_ty();
                (value, ErrForm::Value)
            }
        }
    }

    /// `Err(arg)` with no expected `E`: `Failure` for a text, the operand's own type
    /// for an error value.
    fn err_from_operand(&mut self, arg: &ast::Expr) -> (hir::Expr, ErrForm, Ty) {
        let value = self.check_expr(arg, Expect::None);
        let failure = self
            .sema
            .tcx
            .lang_adt(LangItem::Failure)
            .map(|adt| self.sema.tcx.mk_adt(adt, &[]));
        let fixed = matches!(
            strip_parens(arg).kind,
            ast::ExprKind::Str(_) | ast::ExprKind::RawTemplate(_) | ast::ExprKind::Template(_)
        );
        let t = self.resolve(value.ty);
        let error = self.error_ty();
        if self.is_error(t) {
            return (value, ErrForm::Value, error);
        }
        if fixed || self.is_text(t) {
            let form = match fixed {
                true => ErrForm::Text,
                false => self.text_or_error_form(&value).unwrap_or(ErrForm::TextMove),
            };
            return (value, form, failure.unwrap_or(error));
        }
        if self.is_result_error_type(t) {
            return (value, ErrForm::Value, t);
        }
        self.report_not_text(&value);
        (value, ErrForm::Value, error)
    }

    /// The form of an operand at `Failure` by its type: `TextMove`, `TextCopy`,
    /// `Value` for a `Failure`, `IntoFailure` for another error type.
    fn text_or_error_form(&self, value: &hir::Expr) -> Option<ErrForm> {
        let t = self.resolve(value.ty);
        let tcx = &*self.sema.tcx;
        match tcx.kind(t) {
            TyKind::Error | TyKind::Never => Some(ErrForm::Value),
            TyKind::Str => Some(ErrForm::TextMove),
            TyKind::Ref(inner) if tcx.kind(inner) == TyKind::Str => Some(ErrForm::TextCopy),
            _ if self.is_failure(t) => Some(ErrForm::Value),
            _ if self.is_result_error_type(t) => Some(ErrForm::IntoFailure),
            _ => None,
        }
    }

    /// EN0401: `Err` at `Failure` takes a text or an error value (plan choice).
    fn report_not_text(&mut self, value: &hir::Expr) {
        let shown = self.ty_str(value.ty);
        self.sema.emit(Diagnostic::new(
            Code::EN0401,
            format!("`Err` takes a text or an error value here, found `{shown}`"),
            value.span,
            format!("this is `{shown}`"),
        ));
    }

    // ---------------------------------------------------------------------------
    // `e?`.

    /// `e?` (S:1141).
    pub(crate) fn check_try(&mut self, e: &ast::Expr) -> hir::Expr {
        let ast::ExprKind::Try(inner) = &e.kind else {
            return self.error_expr(e.span);
        };
        let operand = self.check_expr(inner, Expect::None);
        let mark = Span {
            lo: BytePos(e.span.hi.0.saturating_sub(1)),
            hi: e.span.hi,
        };
        let t = self.shallow(operand.ty);
        if self.is_error(t) {
            return self.error_expr(e.span);
        }
        if self.var_kind(t) == Some(VarKind::Any) {
            let what = format!("`{}`", self.snippet(operand.span));
            self.report_uninferred(operand.span, &what);
            return self.error_expr(e.span);
        }
        if let Some((ok, err)) = self.result_parts(t) {
            return match self.try_result(ok, err, mark) {
                Some(kind) => self.mk_expr(ok, e.span, ExprKind::Try(Box::new(operand), kind)),
                None => self.error_expr(e.span),
            };
        }
        if let TyKind::Nullable(payload) = self.sema.tcx.kind(t) {
            return match self.try_nullable(mark) {
                true => self.mk_expr(
                    payload,
                    e.span,
                    ExprKind::Try(Box::new(operand), TryKind::Nullable),
                ),
                false => self.error_expr(e.span),
            };
        }
        let shown = self.ty_str(t);
        let written = self.snippet(operand.span);
        self.sema.emit(Diagnostic::new(
            Code::EN0429,
            format!("`?` needs a `Result` or `T | null`, found `{shown}`"),
            mark,
            format!("`{written}` is `{shown}`"),
        ));
        self.error_expr(e.span)
    }

    /// `?` on `Result<ok, err>`: its kind, or `None` after reporting.
    fn try_result(&mut self, ok: Ty, err: Ty, mark: Span) -> Option<TryKind> {
        let _ = ok;
        let ret = self.shallow(self.ret_ctx().ty);
        if self.is_error(ret) {
            return None;
        }
        if self.var_kind(ret) == Some(VarKind::Any) {
            let fresh = self.fresh_var();
            let error = self.error_ty();
            let result = self.sema.tcx.mk_result(fresh, err).unwrap_or(error);
            let _ = self.unify(ret, result);
            self.note_try_fixed(mark);
            return Some(TryKind::Result);
        }
        if let Some((ret_ok, ret_err)) = self.result_parts(ret) {
            if self.unify(err, ret_err) {
                return Some(TryKind::Result);
            }
            if self.is_failure(ret_err) {
                return Some(TryKind::ResultIntoFailure);
            }
            let (have, want) = (self.ty_str(err), self.ty_str(ret_err));
            let ok_shown = self.ty_str(ret_ok);
            self.sema.emit(
                Diagnostic::new(
                    Code::EN0425,
                    format!("`?` returns `{have}`, but the function returns `{want}`"),
                    mark,
                    format!(
                        "this returns {} `{have}` error early",
                        crate::classes::sig::article(&have)
                    ),
                )
                .with_help(Help::text(format!(
                    "return `Result<{ok_shown}>`, which takes any error as its text"
                ))),
            );
            return None;
        }
        if matches!(self.owner, hir::BodyOwner::Statements(_)) && self.arrow_stack.is_empty() {
            // A failed `?` among the statements prints the error and exits 1.
            return Some(TryKind::Result);
        }
        self.report_no_early_return(ret, mark, false);
        None
    }

    /// Keeps `mark`, a `?` that decided the result of the innermost arrow, for the
    /// report of a return that then misfits (T:902).
    fn note_try_fixed(&mut self, mark: Span) {
        if let Some(frame) = self.arrow_stack.last_mut()
            && frame.ret.origin == RetOrigin::Body
        {
            frame.try_fixed.get_or_insert(mark);
        }
    }

    /// `?` on a nullable: whether the result allows it, after reporting when not.
    fn try_nullable(&mut self, mark: Span) -> bool {
        let ret = self.shallow(self.ret_ctx().ty);
        if self.is_error(ret) {
            return false;
        }
        if self.var_kind(ret) == Some(VarKind::Any) {
            let fresh = self.fresh_var();
            let nullable = self.sema.tcx.mk_nullable(fresh);
            let _ = self.unify(ret, nullable);
            self.note_try_fixed(mark);
            return true;
        }
        if matches!(self.sema.tcx.kind(ret), TyKind::Nullable(_)) {
            return true;
        }
        let in_result = self.result_parts(ret).is_some();
        self.report_no_early_return(ret, mark, in_result);
        false
    }

    /// EN0424: the enclosing function or arrow returns neither `Result` nor
    /// `T | null`, or a `Result` where `?` would return `null`.
    fn report_no_early_return(&mut self, ret: Ty, mark: Span, in_result: bool) {
        let shown = self.ty_str(ret);
        let owner = match (self.arrow_stack.is_empty(), self.name, self.owner) {
            (false, _, _) => "this arrow".to_owned(),
            (true, _, hir::BodyOwner::Statements(_)) => "the program's statements".to_owned(),
            (true, Some(name), _) => format!("`{name}`"),
            (true, None, _) => "this function".to_owned(),
        };
        // "the program's statements return", a plural owner.
        let verb = match self.owner {
            hir::BodyOwner::Statements(_) if self.arrow_stack.is_empty() => "return",
            _ => "returns",
        };
        let mut diag = Diagnostic::new(
            Code::EN0424,
            "`?` needs the function to return `Result` or `T | null`",
            mark,
            format!("{owner} {verb} `{shown}`"),
        );
        if self.arrow_stack.is_empty()
            && let Some(ret_span) = self.ret_span
        {
            diag = diag.with_secondary(ret_span, format!("`{shown}` is the return type"));
        }
        if in_result {
            diag = diag.note(
                "the early return of `?` is never wrapped as a success, so it can't return `null` here",
            );
        }
        self.sema.emit(diag);
    }

    // ---------------------------------------------------------------------------
    // Unused results.

    /// EN0426, EN0453 and EN1006 for the expression statement `s` (S:1142).
    pub(crate) fn check_unused(&mut self, s: &hir::Expr) {
        if let ExprKind::VoidOp(inner) = &s.kind {
            // `void` drops the value, which an interface by value has no size to do.
            let t = self.resolve(inner.ty);
            if !self.is_error(t) && self.sema.tcx.is_interface_ty(t) {
                self.report_iface_value(inner);
            }
            return;
        }
        if matches!(
            s.kind,
            ExprKind::Assign { .. } | ExprKind::IncDec { .. } | ExprKind::Destructure { .. }
        ) {
            return;
        }
        let t = self.resolve(s.ty);
        if self.is_error(t) {
            return;
        }
        if self.result_parts(t).is_some() {
            let shown = self.ty_str(t);
            self.sema.emit(
                Diagnostic::new(
                    Code::EN0426,
                    "this `Result` is not used, so an error would be lost silently",
                    s.span,
                    format!("returns `{shown}`"),
                )
                .from_typescript(
                    "a thrown exception cannot be ignored by accident, and neither can this.",
                )
                .with_help(Help::machine("discard it deliberately", self.void_edits(s))),
            );
            return;
        }
        if let Some((def, receiver)) = self.must_use_call(s) {
            self.report_unused_result(s, def, receiver, t);
            return;
        }
        if self.sema.tcx.is_interface_ty(t) {
            self.report_iface_value(s);
        }
    }

    /// The edits that put `void` before the statement `s`: `void (` and `)` when
    /// `s` is an operator of lower precedence than the prefix `void` (SPEC 3.5),
    /// unless its source is already parenthesised whole.
    fn void_edits(&self, s: &hir::Expr) -> Vec<Edit> {
        let low = matches!(
            s.kind,
            ExprKind::Binary(..)
                | ExprKind::Logical(..)
                | ExprKind::Coalesce(..)
                | ExprKind::Ternary(..)
                | ExprKind::Cast(..)
        );
        if !low || parenthesised_whole(&self.snippet(s.span)) {
            return vec![Edit::insert(s.span.lo, "void ")];
        }
        vec![
            Edit::insert(s.span.lo, "void ("),
            Edit::insert(s.span.hi, ")"),
        ]
    }

    /// The `@mustUse` function or method `s` calls, with its receiver.
    fn must_use_call<'e>(&self, s: &'e hir::Expr) -> Option<(DefId, Option<&'e hir::Expr>)> {
        let (callee, receiver) = match &s.kind {
            ExprKind::Call {
                callee, receiver, ..
            } => (callee, receiver.as_deref()),
            ExprKind::OptionalChain(chain) => match &chain.member {
                OptMember::Call { callee, .. } => (callee, Some(&chain.base)),
                OptMember::Field(_) => return None,
            },
            _ => return None,
        };
        let def = match callee {
            Callee::Fn(f) | Callee::Super(f) => f.def,
            Callee::BoundMember { found, .. } => *found,
            Callee::Foreign(def) => *def,
            _ => return None,
        };
        self.sema
            .tcx
            .def(def)
            .attrs
            .must_use
            .then_some((def, receiver))
    }

    /// Warning EN0453 for the unused result of `@mustUse` `def` (S:1142, G23).
    fn report_unused_result(
        &mut self,
        s: &hir::Expr,
        def: DefId,
        receiver: Option<&hir::Expr>,
        result: Ty,
    ) {
        let name = self
            .sema
            .tcx
            .def(def)
            .name()
            .map_or_else(String::new, |n| n.as_str().to_owned());
        let receiver_text = receiver
            .map(|r| self.snippet(r.span))
            .filter(|t| !t.is_empty());
        let label = match &receiver_text {
            Some(recv) => {
                let what = match self.sema.tcx.kind(result) {
                    TyKind::Str => "string",
                    _ => "value",
                };
                format!("`{name}` returns a new {what} and leaves `{recv}` as it was")
            }
            None => format!("`{name}` is marked `@mustUse`"),
        };
        let mut diag = Diagnostic::new(
            Code::EN0453,
            format!("the result of `{name}` is not used"),
            s.span,
            label,
        );
        let keep = receiver.and_then(|r| {
            let ExprKind::Local(local) = r.kind else {
                return None;
            };
            let decl = &self.locals[local];
            let same = self.resolve(decl.ty) == result;
            let assignable = decl.mutable || decl.kind == LocalKind::Param(Mark::Let);
            (assignable && same).then(|| self.snippet(r.span))
        });
        diag = match keep {
            Some(recv) => diag.with_help(Help::machine(
                "keep it",
                vec![Edit::insert(s.span.lo, format!("{recv} = "))],
            )),
            None => diag.with_help(Help::text(
                "keep the result, or discard it deliberately with `void`",
            )),
        };
        self.sema.emit(diag);
    }
}

/// Whether `text` is one parenthesised expression: its first `(` closes at its
/// last character.
fn parenthesised_whole(text: &str) -> bool {
    if !text.starts_with('(') || !text.ends_with(')') {
        return false;
    }
    let mut depth = 0usize;
    for (i, c) in text.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return i == text.len() - 1;
                }
            }
            _ => {}
        }
    }
    false
}
