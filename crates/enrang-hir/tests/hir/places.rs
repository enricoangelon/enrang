//! `is_path_place` on each place form (A:424-426).

use enrang_base::Span;
use enrang_hir::{
    Callee, ConstValue, DefId, Expr, ExprId, ExprKind, FactId, FieldIdx, FnRef, LocalId, Ty,
    VariantIdx, is_path_place,
};
use enrang_testkit::Harness;

use crate::support::World;

fn e(ty: Ty, kind: ExprKind) -> Expr {
    Expr::new(ExprId(0), ty, Span::DUMMY, kind)
}

pub fn register(h: &mut Harness) {
    h.case(
        "places/locals, fields, payloads and derefs of references and boxes",
        || {
            let w = World::new();
            let t = &w.tcx;
            let i64 = t.common().i64;
            let local = || e(i64, ExprKind::Local(LocalId(0)));
            let r = t.mk_ref(i64);
            let b = t.mk_box(i64);
            let raw = t.mk_raw(i64);
            let yes = [
                local(),
                e(i64, ExprKind::Field(Box::new(local()), FieldIdx(1))),
                e(
                    i64,
                    ExprKind::NarrowedPayload(Box::new(local()), VariantIdx(1), FactId(0)),
                ),
                e(
                    i64,
                    ExprKind::Deref(Box::new(e(r, ExprKind::Local(LocalId(1))))),
                ),
                e(
                    i64,
                    ExprKind::Deref(Box::new(e(b, ExprKind::Local(LocalId(1))))),
                ),
                e(
                    i64,
                    ExprKind::Field(
                        Box::new(e(
                            i64,
                            ExprKind::Deref(Box::new(e(r, ExprKind::Local(LocalId(2))))),
                        )),
                        FieldIdx(0),
                    ),
                ),
            ];
            for place in &yes {
                assert!(is_path_place(t, place), "{:?}", place.kind);
            }
            let call = e(
                i64,
                ExprKind::Call {
                    callee: Callee::Fn(FnRef {
                        def: DefId(0),
                        args: t.empty_list(),
                    }),
                    receiver: None,
                    args: Vec::new(),
                },
            );
            let no = [
                e(i64, ExprKind::Index(Box::new(local()), Box::new(local()))),
                e(i64, ExprKind::Static(DefId(0))),
                call.clone(),
                e(
                    i64,
                    ExprKind::Deref(Box::new(e(raw, ExprKind::Local(LocalId(1))))),
                ),
                e(i64, ExprKind::Field(Box::new(call), FieldIdx(0))),
                e(i64, ExprKind::Const(ConstValue::Bool(true))),
                e(
                    i64,
                    ExprKind::Deref(Box::new(e(r, ExprKind::Static(DefId(1))))),
                ),
            ];
            for place in &no {
                assert!(!is_path_place(t, place), "{:?}", place.kind);
            }
        },
    );
}
