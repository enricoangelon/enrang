//! `?`, `Err` and `Result` returns (A:944-946; M3 plan c.12; owner 2C), with the
//! `Failure` conversions as forms (D19).
//!
//! `e?` puts `e` in a statement temporary and switches on its tag: the error arm
//! moves the payload into `_0` as `Err` (through `IntoFailure` for
//! `ResultIntoFailure`) or makes `_0` `null`, and exits through the scheduled drops;
//! the other arm's payload, moved into a temporary, is the value. Among a
//! program's statements, whose result is the exit status, the error arm prints
//! `error: <e>` through `Display` and makes `_0` 1, as `__rt_start` maps a failed
//! `?` there (A:1539).

use enrang_base::Span;
use enrang_hir::{self as hir, ConstValue, ErrForm, ExprKind, TryKind, TyKind, VariantIdx};
use enrang_mir::{AggregateKind, BorrowOrigin, Callee, FormCall, Local, Operand, Place, Rvalue};

use crate::builder::Builder;
use crate::matches::{borrow, call, discr, payload, read, switch, temp, to_temp, value_temp};
use crate::scope::ExitTarget;

/// Lowers `e?`, leaving the `Ok` (or present) payload (c.12).
pub fn lower_try(b: &mut Builder, e: &hir::Expr, kind: TryKind) -> Operand {
    // A statement temporary, which its scope drops (c.3).
    let r = value_temp(b, e);
    let (ok, fail) = match kind {
        TryKind::Nullable => (VariantIdx::PRESENT, VariantIdx::NULL),
        _ => (VariantIdx::OK, VariantIdx::ERR),
    };
    let d = discr(b, r, e.span);
    let (okb, failb) = (b.new_block(), b.new_block());
    match kind {
        TryKind::Nullable => switch(b, d, vec![(0, failb)], okb, e.span),
        _ => switch(b, d, vec![(0, okb)], failb, e.span),
    }
    b.switch_to(failb);
    let ret = Place::local(Local::RETURN);
    match kind {
        TryKind::Nullable => b.assign(ret, Rvalue::Aggregate(AggregateKind::Null, vec![]), e.span),
        _ if matches!(b.body.owner, enrang_mir::BodyOwner::Statements(_)) => {
            let tcx = b.cx.tcx;
            let p = payload(b, r, fail, e.span);
            let et = b.place_ty(p);
            let shown = to_temp(
                b,
                borrow(p, BorrowOrigin::AutoBorrow),
                tcx.mk_ref(et),
                e.span,
            );
            let text = tcx.mk_ref(tcx.common().str);
            let head = Operand::constant(ConstValue::Str(tcx.intern_str("error: ")), text);
            let done = temp(b, tcx.common().void, e.span);
            let args = vec![head, Operand::Move(shown)];
            call(b, Callee::Form(FormCall::Error), args, done, e.span);
            let rt = b.place_ty(ret);
            let one = Operand::constant(ConstValue::Int(1, rt), rt);
            b.assign(ret, Rvalue::Use(one), e.span);
        }
        _ => {
            let p = payload(b, r, fail, e.span);
            let mut err = read(b, p);
            if kind == TryKind::ResultIntoFailure {
                err = failure(b, FormCall::IntoFailure, err, b.place_ty(ret), e.span);
            }
            err_into(b, ret, err, e.span);
        }
    }
    b.exit_to(ExitTarget::Return, e.span);
    b.switch_to(okb);
    let p = payload(b, r, ok, e.span);
    let (v, t) = (read(b, p), b.place_ty(p));
    let v = to_temp(b, Rvalue::Use(v), t, e.span);
    read(b, v)
}

/// `dest = Result::Err { error }`, at `dest`'s own `Result` type.
fn err_into(b: &mut Builder, dest: Place, error: Operand, span: Span) {
    if let TyKind::Adt(adt, args) = b.cx.tcx.kind(b.place_ty(dest)) {
        let kind = AggregateKind::Adt {
            adt,
            variant: Some(VariantIdx::ERR),
            args,
        };
        b.assign(dest, Rvalue::Aggregate(kind, vec![error]), span);
    }
}

/// The error type `E` of `Result<T, E>`.
fn err_ty(b: &Builder, result: hir::Ty) -> hir::Ty {
    let tcx = b.cx.tcx;
    match tcx.kind(result) {
        TyKind::Adt(_, args) if tcx.list(args).len() == 2 => tcx.list(args)[1],
        _ => tcx.common().error,
    }
}

/// `_f = form(arg)`, a `Failure` (or the error type of `result`).
fn failure(b: &mut Builder, form: FormCall, arg: Operand, result: hir::Ty, span: Span) -> Operand {
    let f = temp(b, err_ty(b, result), span);
    call(b, Callee::Form(form), vec![arg], f, span);
    Operand::Move(f)
}

/// Lowers `Err(arg)` into `dest` by its form (A:945).
pub fn lower_err(b: &mut Builder, form: ErrForm, arg: &hir::Expr, dest: Place, span: Span) {
    let tcx = b.cx.tcx;
    let dt = b.place_ty(dest);
    let et = err_ty(b, dt);
    let form = match (form, &arg.kind) {
        (ErrForm::Value, _) => None,
        (ErrForm::Text, ExprKind::Template(_)) => {
            let s = temp(b, tcx.common().str, arg.span);
            b.expr_into(arg, s);
            let f = failure(b, FormCall::FailureMove, Operand::Move(s), dt, span);
            return err_into(b, dest, f, span);
        }
        (ErrForm::Text, _) if arg.ty == et => None,
        (ErrForm::Text, _) => Some(FormCall::FailureText),
        (ErrForm::TextMove, _) => Some(FormCall::FailureMove),
        (ErrForm::TextCopy, _) => Some(FormCall::FailureCopy),
        (ErrForm::IntoFailure, _) => Some(FormCall::IntoFailure),
    };
    let mut err = b.as_operand(arg);
    // A fixed text is a static descriptor, `const "..": &string` (A:945).
    if let (Some(FormCall::FailureText), Operand::Const(c)) = (form, &mut err)
        && matches!(c.kind, enrang_mir::ConstKind::Value(ConstValue::Str(_)))
        && tcx.kind(c.ty) == TyKind::Str
    {
        c.ty = tcx.mk_ref(c.ty);
    }
    if let Some(form) = form {
        err = failure(b, form, err, dt, span);
    }
    err_into(b, dest, err, span);
}
