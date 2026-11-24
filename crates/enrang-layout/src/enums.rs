//! Sum types: enums, `Result` among them, and `T | null` (S:1644-1650).
//!
//! The tag sits at offset 0, a `u32` unless a payload-free enum has `@repr("u8")`
//! or `@repr("u16")`. Every case's fields start at one payload offset, the first
//! after the tag aligned for the largest case alignment, and each case is laid out
//! as a `final` class beginning there. The alignment is the largest of the tag's
//! size and every case's alignment, and the size is rounded up to it. Tags number
//! the cases from 0 in declaration order, but a payload-free enum's tag is its
//! case's discriminant, unless its cases carry texts. `T | null` is the same rule
//! with two cases, `null` at tag 0 and present at tag 1, and no niche, but for
//! `&I | null`, whose object word is 0 for `null`.

use std::sync::Arc;

use enrang_hir::{AdtId, AdtKind, FieldIdx, Repr, Ty, TyKind, TyList, VariantIdx, VariantValue};

use crate::limits::{Placer, align_up};
use crate::scalar::words;
use crate::{Layout, LayoutCx, LayoutError, TagLayout, VariantLayout, VariantsLayout};

/// `T | null`.
pub(crate) fn nullable(cx: &mut LayoutCx<'_>, ty: Ty, inner: Ty) -> Result<Layout, LayoutError> {
    if let TyKind::Ref(object) = cx.tcx.kind(inner)
        && cx.is_interface(object)
    {
        return Ok(null_word(cx));
    }
    let present = cx.layout_of(inner)?;
    let cases = vec![Vec::new(), vec![present]];
    sum(cx, ty, 4, &cases, &[0, 1])
}

/// `&I | null`: the two words of `&I`, `2P`, align `P`, with an object word of 0 as
/// `null` (S:1638).
fn null_word(cx: &LayoutCx<'_>) -> Layout {
    let present = words(cx.dl, 2);
    Layout {
        size: present.size,
        align: present.align,
        fields: Vec::new(),
        variants: Some(VariantsLayout {
            tag: TagLayout::NullWord,
            payload: 0,
            variants: vec![
                VariantLayout {
                    tag: 0,
                    fields: Vec::new(),
                    size: 0,
                },
                VariantLayout {
                    tag: 1,
                    fields: vec![0],
                    size: present.size,
                },
            ],
        }),
    }
}

/// An enum at the arguments `args`.
pub(crate) fn enumeration(
    cx: &mut LayoutCx<'_>,
    ty: Ty,
    adt: AdtId,
    args: TyList,
) -> Result<Layout, LayoutError> {
    let tcx = cx.tcx;
    let AdtKind::Enum(e) = &tcx.adt(adt).kind else {
        unreachable!("enumeration() is called on enums only");
    };
    let mut cases = Vec::with_capacity(e.variants.len());
    for (v, variant) in e.variants.iter().enumerate() {
        let mut fields = Vec::with_capacity(variant.fields.len());
        for f in 0..variant.fields.len() {
            let field = tcx.field_ty(adt, Some(VariantIdx(v as u32)), FieldIdx(f as u32), args);
            fields.push(cx.layout_of(field)?);
        }
        cases.push(fields);
    }
    let payload_free = e.is_payload_free();
    let tag_size = match (payload_free, e.repr) {
        (true, Some(Repr::U8)) => 1,
        (true, Some(Repr::U16)) => 2,
        _ => 4,
    };
    let mask = u64::MAX >> (64 - 8 * tag_size);
    // A payload-free enum's tag is its discriminant: the written integer, or the
    // one after the case before, from 0 (S:591). A case that carries a text has no
    // integer, so a text enum keeps the positions (S:1648).
    let tags: Vec<u64> = if payload_free {
        let mut next: i128 = 0;
        e.variants
            .iter()
            .map(|variant| {
                let value = match variant.value {
                    Some(VariantValue::Int(value)) => value,
                    _ => next,
                };
                next = value.wrapping_add(1);
                (value as u64) & mask
            })
            .collect()
    } else {
        (0..e.variants.len() as u64).collect()
    };
    sum(cx, ty, tag_size, &cases, &tags)
}

/// A sum type with a tag of `tag_size` bytes at offset 0, one field list per case
/// and one tag value per case.
fn sum(
    cx: &LayoutCx<'_>,
    ty: Ty,
    tag_size: u32,
    cases: &[Vec<Arc<Layout>>],
    tags: &[u64],
) -> Result<Layout, LayoutError> {
    let too_large = LayoutError::TooLarge { ty };
    let case_align = cases
        .iter()
        .flatten()
        .map(|field| field.align)
        .max()
        .unwrap_or(1);
    let payload = align_up(u64::from(tag_size), case_align).ok_or(too_large)?;
    let align = tag_size.max(case_align);
    let mut end = payload;
    let mut variants = Vec::with_capacity(cases.len());
    for (fields, &tag) in cases.iter().zip(tags) {
        let mut placer = Placer::resume(payload, 1, cx.max_size(), false);
        let offsets = fields
            .iter()
            .map(|field| placer.place(field.size, field.align))
            .collect::<Option<Vec<u64>>>()
            .ok_or(too_large)?;
        let own_align = fields.iter().map(|field| field.align).max().unwrap_or(1);
        let size = align_up(placer.end() - payload, own_align).ok_or(too_large)?;
        end = end.max(placer.end());
        variants.push(VariantLayout {
            tag,
            fields: offsets,
            size,
        });
    }
    let size = align_up(end, align)
        .filter(|&size| size <= cx.max_size())
        .ok_or(too_large)?;
    Ok(Layout {
        size,
        align,
        fields: Vec::new(),
        variants: Some(VariantsLayout {
            tag: TagLayout::Direct { size: tag_size },
            payload,
            variants,
        }),
    })
}
