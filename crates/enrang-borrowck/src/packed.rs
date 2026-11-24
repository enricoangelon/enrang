//! EN0804, phase 4 (A:653, S:1300, H16, H23; M3 plan d.6; owner 2E): a `Ref` whose
//! place crosses a field of a `@packed` class with no later deref, to a referent
//! aligned above 1, one report per `Ref` span.
//!
//! Choice: borrowck may not depend on enrang-layout (A:69-96), so "aligned above
//! 1" is decided here from the type alone: `bool`, `i8`, `u8`, `void` and `never`
//! align to 1, and so do a fixed array, tuple, object, nullable or class built only
//! of them, a `@packed` class, and an enum with an 8-bit `@repr` whose fields all
//! do; everything else (pointers, wider scalars, type parameters) aligns above 1.

use enrang_diag::DiagCtx;
use enrang_hir::{AdtKind, IntTy, Repr, Tcx, Ty, TyKind};
use enrang_mir::{Bodies, PlaceTy, Proj, Rvalue, StatementKind};

pub fn check(tcx: &Tcx, bodies: &Bodies, dcx: &mut DiagCtx) {
    for b in bodies.values() {
        for st in b.blocks.iter().flat_map(|bl| &bl.stmts) {
            let StatementKind::Assign {
                value: Rvalue::Ref { place, .. },
                ..
            } = &st.kind
            else {
                continue;
            };
            let mut pt = PlaceTy::of(b.locals[place.local].ty);
            let mut crossed = false;
            for &p in b.projs(*place) {
                match (p, tcx.kind(pt.ty)) {
                    (Proj::Field(_), TyKind::Adt(adt, _)) if pt.variant.is_none() => {
                        crossed |= tcx.def(tcx.adt(adt).def).attrs.packed;
                    }
                    (Proj::Deref, _) => crossed = false,
                    _ => {}
                }
                match pt.project(tcx, p) {
                    Some(next) => pt = next,
                    None => break,
                }
            }
            if crossed && !align1(tcx, pt.ty, &mut Vec::new()) {
                dcx.emit(crate::report::report_packed(tcx, b, *place, st.span));
            }
        }
    }
}

/// Whether a value of type `ty` aligns to 1 (see the module doc).
fn align1(tcx: &Tcx, ty: Ty, seen: &mut Vec<Ty>) -> bool {
    if seen.contains(&ty) {
        return true;
    }
    seen.push(ty);
    let ok = match tcx.kind(ty) {
        TyKind::Bool | TyKind::Void | TyKind::Never => true,
        TyKind::Int(i) => matches!(i, IntTy::I8 | IntTy::U8),
        TyKind::Fixed(t, _) | TyKind::Nullable(t) => align1(tcx, t, seen),
        TyKind::Tuple(parts) => tcx.list(parts).iter().all(|&p| align1(tcx, p, seen)),
        TyKind::Object(shape) => tcx
            .shape(shape)
            .fields
            .iter()
            .all(|&(_, f)| align1(tcx, f, seen)),
        TyKind::Adt(adt, args) => {
            let def = tcx.adt(adt);
            let attrs = &tcx.def(def.def).attrs;
            let fields = tcx.adt_field_tys(adt, args);
            match &def.kind {
                AdtKind::Class(_) if attrs.align.is_some_and(|a| a > 1) => false,
                AdtKind::Class(_) => {
                    attrs.packed || fields.into_iter().all(|f| align1(tcx, f, seen))
                }
                AdtKind::Enum(_) => {
                    matches!(attrs.repr, Some(Repr::U8))
                        && fields.into_iter().all(|f| align1(tcx, f, seen))
                }
                AdtKind::Interface(_) => false,
            }
        }
        _ => false,
    };
    seen.pop();
    ok
}
