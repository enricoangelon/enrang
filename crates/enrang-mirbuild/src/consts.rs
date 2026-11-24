//! Constant reads and literal views (A:970, S:964, S:756; M3 plan c.18; owner 2C):
//! a scalar as a constant, an aggregate built from its tree, a `&string` constant
//! or literal view as `static_addr`, a bracket literal of constants behind `&` as
//! a `[literal-view]` borrow.
//!
//! A read copies the constant's value (S 4.9): an aggregate is built part by part,
//! each nested part in a temporary first; a reference-typed constant names its
//! static, so it holds no loan (the top-level `const` mark, plan d.3).

use enrang_base::{Idx, Span};
use enrang_hir::{
    self as hir, ConstTree, ConstValue, ConvKind, DefId, ExprKind, FieldIdx, Ty, TyKind,
};
use enrang_mir::{AggregateKind, BorrowOrigin, Operand, Place, Rvalue};

use crate::builder::Builder;
use crate::matches::{borrow, temp, to_temp};

/// Reads the constant `def` of type `ty` into `dest` (c.18).
pub fn lower_const_read(b: &mut Builder, def: DefId, ty: Ty, dest: Place, span: Span) {
    let tree = b.cx.tcx.const_value(def).cloned();
    let value = match tree {
        Some(t) if !matches!(b.cx.tcx.kind(ty), TyKind::Ref(_)) => build(b, &t, ty, span),
        _ => Rvalue::Use(Operand::constant(ConstValue::StaticAddr(def), ty)),
    };
    b.assign(dest, value, span);
}

/// The value of `tree` at type `ty`, nested parts in temporaries.
fn build(b: &mut Builder, tree: &ConstTree, ty: Ty, span: Span) -> Rvalue {
    let tcx = b.cx.tcx;
    let part = |b: &mut Builder, t: &ConstTree, ty: Ty| match build(b, t, ty, span) {
        Rvalue::Use(op) => op,
        rv => Operand::Move(to_temp(b, rv, ty, span)),
    };
    let (kind, ops) = match (tree, tcx.kind(ty)) {
        (ConstTree::Scalar(v), _) => return Rvalue::Use(Operand::constant(*v, ty)),
        (ConstTree::Null, _) => (AggregateKind::Null, Vec::new()),
        (ConstTree::Present(t), TyKind::Nullable(inner)) => {
            (AggregateKind::Present, vec![part(b, t, inner)])
        }
        (ConstTree::Array(ts), TyKind::Fixed(e, _)) => {
            let ops = ts.iter().map(|t| part(b, t, e)).collect();
            (AggregateKind::Fixed(e), ops)
        }
        (ConstTree::Tuple(ts), TyKind::Tuple(l)) => {
            let tys = tcx.list(l);
            let ops = ts
                .iter()
                .zip(tys.iter())
                .map(|(t, &ty)| part(b, t, ty))
                .collect();
            (AggregateKind::Tuple, ops)
        }
        (ConstTree::Object(ts), TyKind::Object(shape)) => {
            let fields = tcx.shape(shape).fields.clone();
            let ops = ts
                .iter()
                .zip(&fields)
                .map(|(t, f)| part(b, t, f.1))
                .collect();
            (AggregateKind::Object(shape), ops)
        }
        (
            ConstTree::Adt {
                adt,
                variant,
                fields,
            },
            TyKind::Adt(_, args),
        ) => {
            let ops = (fields.iter().enumerate())
                .map(|(i, t)| {
                    let fty = tcx.field_ty(*adt, *variant, FieldIdx::new(i), args);
                    part(b, t, fty)
                })
                .collect();
            let kind = AggregateKind::Adt {
                adt: *adt,
                variant: *variant,
                args,
            };
            (kind, ops)
        }
        _ => return Rvalue::Use(Operand::constant(ConstValue::Void, ty)),
    };
    Rvalue::Aggregate(kind, ops)
}

/// A constant literal view `&[..]` (c.18): the literal into a statement temporary
/// `_t`, `&_t [literal-view]`, then the expression's conversion (`FixedToSlice`,
/// A:936); borrowck decides it and elaboration may make it static.
pub fn lower_literal_view(b: &mut Builder, e: &hir::Expr) -> Operand {
    let tcx = b.cx.tcx;
    let lit = match &e.kind {
        ExprKind::Borrow(inner) => &**inner,
        _ => e,
    };
    // A statement temporary: its storage ends with the statement (S:964).
    let t = temp(b, lit.ty, lit.span);
    b.scope_local(t.local);
    b.expr_into(lit, t);
    let r = to_temp(
        b,
        borrow(t, BorrowOrigin::LiteralView),
        tcx.mk_ref(lit.ty),
        e.span,
    );
    let mut v = Operand::Move(r);
    for k in e.adjust.iter().filter_map(|&a| ConvKind::of_adjust(a)) {
        let elem = match tcx.kind(lit.ty) {
            TyKind::Fixed(x, _) | TyKind::Array(x) => x,
            _ => tcx.common().error,
        };
        let s = tcx.mk_ref(tcx.mk_slice(elem));
        v = Operand::Move(to_temp(b, Rvalue::Convert(k, v), s, e.span));
    }
    v
}
