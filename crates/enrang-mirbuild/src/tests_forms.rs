//! Test forms (A:979; M3 plan c.19; owner 2C): `expect(actual).matcher(args)` as
//! one `Form(Expect)` call over shared borrows of its values (D19), real borrows
//! for one statement; a constant argument is passed as it is, and a packed field
//! is copied to a temporary first (A:977).

use enrang_hir::{self as hir, ArmValue, ConstValue, ExpectArg, ExprKind, TyKind};
use enrang_mir::{BorrowOrigin, Callee, FormCall, Operand, Place, PlaceTy, Proj, Rvalue};

use crate::builder::Builder;
use crate::matches::{Subject, borrow, call, cond, is_place, temp, to_temp, value_temp};
use crate::scope::ScopeKind;

/// Lowers one `expect` (c.19).
pub fn lower_expect(b: &mut Builder, f: &hir::ExpectForm) {
    let tcx = b.cx.tcx;
    b.open(ScopeKind::Statement, f.span);
    let mut args = vec![shared(b, &f.actual)];
    for a in &f.args {
        args.push(match a {
            ExpectArg::Expr(e) if matches!(e.kind, ExprKind::Const(_)) => b.as_operand(e),
            ExpectArg::Expr(e) => shared(b, e),
            ExpectArg::Arm(ArmValue::Cond(e)) => cond(b, e),
            ExpectArg::Arm(v) => {
                let isize = tcx.common().isize;
                let c = match v {
                    ArmValue::Const(c) | ArmValue::Range(c, _) => *c,
                    ArmValue::Case(v) => ConstValue::Int(u128::from(v.0), isize),
                    _ => ConstValue::Void,
                };
                let t = match c {
                    ConstValue::Int(_, t) | ConstValue::Float(_, t) => t,
                    ConstValue::Bool(_) => tcx.common().bool,
                    _ => tcx.common().void,
                };
                Operand::constant(c, t)
            }
        });
    }
    let form = FormCall::Expect {
        matcher: f.matcher,
        negated: f.negated,
    };
    let d = temp(b, tcx.common().void, f.span);
    call(b, Callee::Form(form), args, d, f.span);
    b.pop_scope();
}

/// A shared borrow of `e`'s place, or of a temporary holding its value or a
/// packed field's copy.
fn shared(b: &mut Builder, e: &hir::Expr) -> Operand {
    let tcx = b.cx.tcx;
    let (place, origin) = match is_place(e) {
        true => {
            let mut s = Subject::of(b, e);
            match packed(b, s.place) {
                true => {
                    s.guard(b, s.place, e.span);
                    let t = b.place_ty(s.place);
                    let v = to_temp(b, Rvalue::Use(Operand::Copy(s.place)), t, e.span);
                    (v, BorrowOrigin::TempArg)
                }
                false => {
                    s.guard(b, s.place, e.span);
                    (s.place, BorrowOrigin::AutoBorrow)
                }
            }
        }
        false => {
            let v = value_temp(b, e);
            (v, BorrowOrigin::TempArg)
        }
    };
    let r = tcx.mk_ref(b.place_ty(place));
    Operand::Move(to_temp(b, borrow(place, origin), r, e.span))
}

/// Whether `p` steps into a field of a `@packed` class.
pub(crate) fn packed(b: &Builder, p: Place) -> bool {
    let tcx = b.cx.tcx;
    let mut pt = PlaceTy::of(b.body.locals[p.local].ty);
    for &x in b.body.projs(p) {
        if let (Proj::Field(_), TyKind::Adt(a, _)) = (x, tcx.kind(pt.ty))
            && tcx.def(tcx.adt(a).def).attrs.packed
        {
            return true;
        }
        match pt.project(tcx, x) {
            Some(n) => pt = n,
            None => return false,
        }
    }
    false
}
