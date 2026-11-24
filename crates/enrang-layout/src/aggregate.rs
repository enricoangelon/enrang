//! Classes, anonymous objects, tuples and fixed arrays (S:1636, S:1640-1642;
//! SPEC 7.6; ARCHITECTURE 7.7).
//!
//! A class keeps its fields in declaration order, each at the next offset aligned
//! for it, its size rounded up to its alignment, the largest field alignment and at
//! least 1. A class that can be extended starts with a hidden method-table pointer
//! of `P` bytes at offset 0, placed like a first field, and a class that extends one
//! keeps its base's pointer and fields at the base's offsets and places its own
//! fields from the base's whole size, never in its tail padding. `@packed` drops
//! the padding and the alignment to 1; `@align(n)` raises the alignment and rounds
//! the size; `@repr("C")` is the default order, as a promise. Anonymous objects and
//! tuples place their fields by alignment, largest first, ties broken by name in
//! byte order or by position, and then as a class.

use std::sync::Arc;

use enrang_hir::{AdtId, AdtKind, FieldIdx, ShapeId, Ty, TyList};

use crate::limits::{Placer, count_fits};
use crate::{Layout, LayoutCx, LayoutError};

/// `T[N]`: `N` elements with no header, size `N * sizeOf<T>()`, align of `T`. `N`
/// above `isize.MAX` is too large whatever `T` is, so it is checked before `T` is
/// laid out.
pub(crate) fn fixed(
    cx: &mut LayoutCx<'_>,
    ty: Ty,
    elem: Ty,
    count: u64,
) -> Result<Layout, LayoutError> {
    if !count_fits(cx.dl, count) {
        return Err(LayoutError::TooLarge { ty });
    }
    let elem = cx.layout_of(elem)?;
    let size = elem
        .size
        .checked_mul(count)
        .filter(|&size| size <= cx.max_size())
        .ok_or(LayoutError::TooLarge { ty })?;
    Ok(Layout::scalar(size, elem.align))
}

/// A tuple: its parts sorted by alignment, largest first, ties by position, then
/// placed as a class's fields. A borrowing tuple's reference parts take the forms
/// their permissions give them (S:1640), so it has no layout before contracts.
pub(crate) fn tuple(cx: &mut LayoutCx<'_>, ty: Ty, parts: TyList) -> Result<Layout, LayoutError> {
    if cx.tcx.is_borrowing(ty) {
        return Err(LayoutError::DependsOnContracts { ty });
    }
    let parts = cx.tcx.list(parts);
    let mut layouts = Vec::with_capacity(parts.len());
    for &part in parts.iter() {
        layouts.push(cx.layout_of(part)?);
    }
    let mut order: Vec<usize> = (0..layouts.len()).collect();
    order.sort_by(|&a, &b| layouts[b].align.cmp(&layouts[a].align).then(a.cmp(&b)));
    sorted(cx, ty, &layouts, &order)
}

/// An anonymous object type, a fields-only interface among them: its fields sorted
/// by alignment, largest first, ties by name in byte order, then placed as a
/// class's fields. `fields` is indexed by the field's position in the shape.
pub(crate) fn object(cx: &mut LayoutCx<'_>, ty: Ty, shape: ShapeId) -> Result<Layout, LayoutError> {
    let shape = cx.tcx.shape(shape);
    let mut layouts = Vec::with_capacity(shape.fields.len());
    for &(_, field) in &shape.fields {
        layouts.push(cx.layout_of(field)?);
    }
    let mut order: Vec<usize> = (0..layouts.len()).collect();
    order.sort_by(|&a, &b| {
        let name = |i: usize| shape.fields[i].0.as_str().as_bytes();
        layouts[b]
            .align
            .cmp(&layouts[a].align)
            .then_with(|| name(a).cmp(name(b)))
    });
    sorted(cx, ty, &layouts, &order)
}

/// Places `layouts` in `order`, recording each offset at its own index.
fn sorted(
    cx: &LayoutCx<'_>,
    ty: Ty,
    layouts: &[Arc<Layout>],
    order: &[usize],
) -> Result<Layout, LayoutError> {
    let too_large = LayoutError::TooLarge { ty };
    let mut placer = Placer::new(cx.max_size(), false);
    let mut fields = vec![0; layouts.len()];
    for &i in order {
        fields[i] = placer
            .place(layouts[i].size, layouts[i].align)
            .ok_or(too_large)?;
    }
    let (size, align) = placer.finish(1).ok_or(too_large)?;
    Ok(Layout {
        size,
        align,
        fields,
        variants: None,
    })
}

/// A class at the arguments `args`. `fields` has one offset per flattened field:
/// the base's at the base's offsets, then the class's own.
pub(crate) fn class(
    cx: &mut LayoutCx<'_>,
    ty: Ty,
    adt: AdtId,
    args: TyList,
) -> Result<Layout, LayoutError> {
    let tcx = cx.tcx;
    if tcx.is_borrowing(ty) {
        return Err(LayoutError::DependsOnContracts { ty });
    }
    let def = tcx.adt(adt);
    let AdtKind::Class(class) = &def.kind else {
        unreachable!("class() is called on classes only");
    };
    let attrs = &tcx.def(def.def).attrs;
    let packed = attrs.packed;
    let too_large = LayoutError::TooLarge { ty };
    let (mut placer, mut fields) = match class.base {
        Some(base) => {
            let params = &tcx.generics(def.generics).params;
            let base = tcx.subst(base, params, &tcx.list(args));
            let base = cx.layout_of(base)?;
            let placer = Placer::resume(base.size, base.align, cx.max_size(), packed);
            (placer, base.fields.clone())
        }
        None => {
            let mut placer = Placer::new(cx.max_size(), packed);
            if class.hidden_table {
                let p = cx.ptr();
                placer.place(p, cx.dl.ptr_bytes).ok_or(too_large)?;
            }
            (placer, Vec::new())
        }
    };
    for i in fields.len()..class.fields.len() {
        let field = tcx.field_ty(adt, None, FieldIdx(i as u32), args);
        let field = cx.layout_of(field)?;
        fields.push(placer.place(field.size, field.align).ok_or(too_large)?);
    }
    let min_align = attrs.align.filter(|n| n.is_power_of_two()).unwrap_or(1);
    let (size, align) = placer.finish(min_align).ok_or(too_large)?;
    Ok(Layout {
        size,
        align,
        fields,
        variants: None,
    })
}
