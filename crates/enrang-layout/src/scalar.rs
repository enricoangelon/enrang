//! Primitives, references, pointers, `string`, `T[]`, `Box` and closures: SPEC 11's
//! table (S:1615-1624) and the two-word forms beside it (S:1626, S:1630-1638).

use enrang_hir::{FloatTy, IntTy, Ty, TyKind};
use enrang_target::DataLayout;

use crate::{Layout, LayoutCx, LayoutError};

/// An integer: its width, aligned to itself, but `i64` and `u64` at the target's
/// `i64` alignment (4 when `P == 4`) and `isize`, `usize` at `P`.
pub(crate) fn int(dl: DataLayout, int: IntTy) -> Layout {
    match int {
        IntTy::I8 | IntTy::U8 => Layout::scalar(1, 1),
        IntTy::I16 | IntTy::U16 => Layout::scalar(2, 2),
        IntTy::I32 | IntTy::U32 => Layout::scalar(4, 4),
        IntTy::I64 | IntTy::U64 => Layout::scalar(8, dl.i64_align),
        IntTy::Isize | IntTy::Usize => words(dl, 1),
    }
}

/// `f32` at 4, `f64` at the target's `f64` alignment.
pub(crate) fn float(dl: DataLayout, float: FloatTy) -> Layout {
    match float {
        FloatTy::F32 => Layout::scalar(4, 4),
        FloatTy::F64 => Layout::scalar(8, dl.f64_align),
    }
}

/// `n` pointer-sized words at `P`: one is a scalar (a pointer, `usize`), two are a
/// pair whose words are its fields (`&Slice<T>`: pointer and length; `&I` and
/// `Box<I>`: object and table; a closure: code and environment).
pub(crate) fn words(dl: DataLayout, n: u64) -> Layout {
    let p = u64::from(dl.ptr_bytes);
    let fields = if n == 1 {
        Vec::new()
    } else {
        (0..n).map(|i| i * p).collect()
    };
    Layout {
        size: n * p,
        align: dl.ptr_bytes,
        fields,
        variants: None,
    }
}

/// `string` and `T[]`: `{ ptr @0, len @P, cap @2P }`, size `3P`, align `P`.
pub(crate) fn descriptor(dl: DataLayout) -> Layout {
    words(dl, 3)
}

/// `&T`: one pointer, but two words for a `&Slice<T>` and an `&I` (S:1626,
/// S:1634, S:1638). A `&string` has one form or the other by the permission
/// inferred for it (S:1630), and a `&T` of a type parameter may stand for either, so
/// neither has a layout before contracts or mono. Every other `&T` is one pointer,
/// `&T[]` included, which always points at the whole array (S:1632).
pub(crate) fn reference(cx: &LayoutCx<'_>, ty: Ty, inner: Ty) -> Result<Layout, LayoutError> {
    match cx.tcx.kind(inner) {
        TyKind::Str => Err(LayoutError::DependsOnContracts { ty }),
        TyKind::Slice(_) => Ok(words(cx.dl, 2)),
        TyKind::Param(_) | TyKind::Infer(_) => Err(LayoutError::Generic { ty }),
        TyKind::Error => Err(LayoutError::ErrorType { ty: inner }),
        _ if cx.is_interface(inner) => Ok(words(cx.dl, 2)),
        _ => Ok(words(cx.dl, 1)),
    }
}

/// `Box<T>`: one pointer to the heap block, but two words for an interface `I`:
/// the object and its class's table for `I` (S:1638). A type parameter never
/// stands for an interface (ARCHITECTURE 2.4), so `Box<T>` is one pointer.
pub(crate) fn boxed(cx: &LayoutCx<'_>, ty: Ty, inner: Ty) -> Result<Layout, LayoutError> {
    match cx.tcx.kind(inner) {
        TyKind::Infer(_) => Err(LayoutError::Generic { ty }),
        TyKind::Error => Err(LayoutError::ErrorType { ty: inner }),
        _ if cx.is_interface(inner) => Ok(words(cx.dl, 2)),
        _ => Ok(words(cx.dl, 1)),
    }
}
