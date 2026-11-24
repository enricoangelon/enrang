//! Exhaustiveness of `match` (plan d.13; SPEC 6 S:1134-1135; A:916; owner 2D): runs
//! `exhaust::check_match` on every `match` of a finished body, nested ones and
//! those in arrows and parameter defaults included, and reports what it finds: a
//! value no arm handles is EN0501 at the subject, an arm or arm value no value
//! reaches warning EN0503 at the value (`Arm.value_spans`, D7).

use enrang_hir::{Body, ExprKind};

use crate::cx::Sema;
use crate::exhaust;
use crate::passes::for_each_expr;

/// Checks every `match` of `b`.
pub(crate) fn check(sema: &mut Sema, b: &Body) {
    let tcx = &*sema.tcx;
    let mut found = Vec::new();
    for_each_expr(b, &mut |e| {
        if matches!(e.kind, ExprKind::Match { .. }) {
            found.extend(exhaust::check_match(tcx, e));
        }
    });
    for diag in found {
        sema.dcx.emit(diag);
    }
}
