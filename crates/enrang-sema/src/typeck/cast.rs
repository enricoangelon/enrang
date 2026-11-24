//! Casts (plan d.6; SPEC 4.6 S:703-716; owner 3A): a direct literal operand,
//! optionally negated, takes the numeric target type (`300 as u8` is EN0411; a
//! raw-pointer target makes it `usize`, so `0xB8000 as *u16` is legal); any other
//! operand that still holds a variable (`a`, `&a`) does not unify with the target,
//! and the kind is chosen after defaulting: the check waits for the end of
//! inference (`Deferred::Cast`), so `let a = 0xB8000; a as *u16` is EN0404 once
//! `a` is `int`, and `infer.rs`'s resolver recomputes the kind from the resolved
//! types; the table gives the `CastKind`; anything else is EN0404.
//!
//! The table: integer to integer, integer or float to float, float to integer, a
//! payload-free enum without texts to an integer, `bool` to an integer, `usize` to a
//! raw pointer, a raw pointer to `usize`, `&T` to `*T`, `*T` to `*U`. A numeric
//! operand behind one reference is read through it (S:684, plan choice).

use enrang_base::Span;
use enrang_diag::{Code, Diagnostic, Help};
use enrang_hir::{self as hir, AdtKind, CastKind, EnumValues, ExprKind, IntTy, Tcx, Ty, TyKind};
use enrang_syntax::ast;

use crate::typeck::expr::strip_parens;
use crate::typeck::infer::VarKind;
use crate::typeck::{Deferred, Expect, FnCtxt};

/// The kind of `from as to` on resolved types, or `None` when the table has no row.
pub(crate) fn cast_kind(tcx: &Tcx, from: Ty, to: Ty) -> Option<CastKind> {
    let from = match (tcx.kind(from), tcx.kind(to)) {
        (TyKind::Ref(inner), TyKind::Int(_) | TyKind::Float(_))
            if matches!(
                tcx.kind(inner),
                TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool
            ) =>
        {
            inner
        }
        _ => from,
    };
    match (tcx.kind(from), tcx.kind(to)) {
        (TyKind::Int(_), TyKind::Int(_)) => Some(CastKind::IntToInt),
        (TyKind::Int(_), TyKind::Float(_)) => Some(CastKind::IntToFloat),
        (TyKind::Float(_), TyKind::Float(_)) => Some(CastKind::FloatToFloat),
        (TyKind::Float(_), TyKind::Int(_)) => Some(CastKind::FloatToInt),
        (TyKind::Bool, TyKind::Int(_)) => Some(CastKind::BoolToInt),
        (TyKind::Adt(adt, _), TyKind::Int(_)) => match &tcx.adt(adt).kind {
            AdtKind::Enum(e) if e.is_payload_free() && e.values != EnumValues::Texts => {
                Some(CastKind::EnumToInt)
            }
            _ => None,
        },
        (TyKind::Int(IntTy::Usize), TyKind::Raw(_)) => Some(CastKind::UsizeToRaw),
        (TyKind::Raw(_), TyKind::Int(IntTy::Usize)) => Some(CastKind::RawToUsize),
        (TyKind::Ref(a), TyKind::Raw(b)) if tcx.same_ignoring_rows(a, b) => {
            Some(CastKind::RefToRaw)
        }
        (TyKind::Raw(_), TyKind::Raw(_)) => Some(CastKind::RawToRaw),
        (TyKind::Error, _) | (_, TyKind::Error) => Some(CastKind::IntToInt),
        _ => None,
    }
}

impl FnCtxt<'_, '_> {
    pub(crate) fn check_cast(
        &mut self,
        operand: &ast::Expr,
        ty: &ast::TypeExpr,
        span: Span,
    ) -> hir::Expr {
        let target = self.lower_ty(ty);
        let common = *self.sema.tcx.common();
        let literal = is_literal(operand);
        let value = match self.sema.tcx.kind(target) {
            TyKind::Int(_) | TyKind::Float(_) if literal => {
                self.check_expr(operand, Expect::Has(target))
            }
            TyKind::Raw(_) if literal => self.check_expr(operand, Expect::Has(common.usize)),
            _ => self.check_expr(operand, Expect::None),
        };
        if self.is_error(target) || self.is_error(value.ty) {
            let kind = CastKind::IntToInt;
            return self.mk_expr(target, span, ExprKind::Cast(Box::new(value), kind));
        }
        let from = self.shallow(value.ty);
        let resolved = self.resolve(from);
        if self.var_kind(from) != Some(VarKind::Any) && self.sema.tcx.has_infer(resolved) {
            // A variable's kind is chosen after defaulting (S:703): the check waits
            // for the final type, and the resolver writes the kind; until then the
            // types the variables would default to stand for them.
            self.deferred.push(Deferred::Cast {
                span,
                value: value.span,
                from,
                to: target,
            });
            let shown = super::infer::display_in(self.sema.tcx, &self.infer, resolved);
            let kind = cast_kind(self.sema.tcx, shown, target).unwrap_or(CastKind::IntToInt);
            return self.mk_expr(target, span, ExprKind::Cast(Box::new(value), kind));
        }
        let kind = match self.var_kind(from) {
            Some(VarKind::Any) => None,
            _ => cast_kind(self.sema.tcx, resolved, target),
        };
        let Some(kind) = kind else {
            self.report_bad_cast(value.span, from, target, span);
            let error = self.error_ty();
            return self.mk_expr(
                error,
                span,
                ExprKind::Cast(Box::new(value), CastKind::IntToInt),
            );
        };
        self.mk_expr(target, span, ExprKind::Cast(Box::new(value), kind))
    }

    /// The deferred check of a cast whose operand held a variable: EN0404 when the
    /// table has no row for the operand's final type (S:703).
    pub(crate) fn check_deferred_cast(&mut self, span: Span, value: Span, from: Ty, to: Ty) {
        let resolved = self.resolve(from);
        let tcx = &*self.sema.tcx;
        if tcx.has_infer(resolved) || tcx.references_error(resolved) {
            return;
        }
        if cast_kind(tcx, resolved, to).is_none() {
            self.report_bad_cast(value, resolved, to, span);
        }
    }

    /// EN0404 `` `T` can't be converted to `U` with `as` ``; `value` is the
    /// operand's span.
    fn report_bad_cast(&mut self, value: Span, from: Ty, to: Ty, span: Span) {
        let (sf, st) = (self.ty_str(from), self.ty_str(to));
        let mut diag = Diagnostic::new(
            Code::EN0404,
            format!("`{sf}` can't be converted to `{st}` with `as`"),
            span,
            format!("this is `{sf}`"),
        );
        let tcx = &*self.sema.tcx;
        let help = match (tcx.kind(self.resolve(from)), tcx.kind(to)) {
            (TyKind::Int(_) | TyKind::Infer(_), TyKind::Bool) => Some(format!(
                "compare it instead: `{} != 0`",
                self.snippet(value)
            )),
            (TyKind::Adt(adt, _), TyKind::Int(_)) if matches!(&tcx.adt(adt).kind, AdtKind::Enum(e) if e.values == EnumValues::Texts) => {
                Some("an enum with text values has no number".to_owned())
            }
            _ => None,
        };
        if let Some(help) = help {
            diag = diag.with_help(Help::text(help));
        }
        self.sema.emit(diag);
    }
}

/// Whether `e` is a number literal, optionally negated (S:703). Parentheses keep
/// it direct, around the literal or around its `-` (plan choice, fix-6).
fn is_literal(e: &ast::Expr) -> bool {
    match &strip_parens(e).kind {
        ast::ExprKind::Int { .. } | ast::ExprKind::Float(_) => true,
        ast::ExprKind::Unary(ast::UnOp::Neg, inner) => {
            matches!(
                strip_parens(inner).kind,
                ast::ExprKind::Int { .. } | ast::ExprKind::Float(_)
            )
        }
        _ => false,
    }
}
