//! Data layout (ARCHITECTURE 1, 3; SPEC 11): the size, alignment and field offsets
//! of every concrete type of the typed HIR, per the target's `DataLayout`, and the
//! size limits of SPEC 11.
//!
//! `layout_of(tcx, ty)` is ARCHITECTURE 3's entry point, memoised in the `Tcx`;
//! [`LayoutCx`] is the same computation with a cache of its own, for a pass that
//! asks about many types of one `Tcx`.
//! The rules live by kind of type:
//!
//! - `scalar`: primitives, references and their two-word forms, raw and function
//!   pointers, `string`, `T[]`, `Box`, closures (S:1615-1626, S:1630-1638);
//! - `aggregate`: classes with the hidden table pointer and subclass placement,
//!   `@packed`, `@align`, `@repr`, anonymous objects and tuples sorted by alignment,
//!   fixed arrays (S:1636, S:1640-1642, SPEC 7.6);
//! - `enums`: tags and payloads, `T | null`, `Result`, the one niche of `&I | null`
//!   (S:1644-1650);
//! - `limits`: `isize.MAX`, the `T[N]` count, the frame limit, and the checked
//!   placement every aggregate uses, so a size never wraps (S:1628).
//!
//! A layout is never guessed: a type whose layout is not known in phase 2 or 4 is a
//! [`LayoutError`]. Sema turns `TooLarge` into EN0435 and `DependsOnContracts` into
//! EN0412's note; the other errors stand for a type that has no layout of its own,
//! or none yet. Nothing here iterates a hash map, and no id orders anything this
//! crate returns (ARCHITECTURE 1).

#![forbid(unsafe_code)]

mod aggregate;
mod enums;
mod limits;
mod scalar;

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use enrang_base::intern;
use enrang_hir::{AdtKind, FieldIdx, Tcx, Ty, TyKind};
use enrang_target::DataLayout;

pub use limits::{FRAME_MAX, Frame, count_fits, max_size};

/// A type's layout (ARCHITECTURE 3).
///
/// `fields` holds one offset per field, from the start of the value, indexed by
/// `FieldIdx`: a class's flattened fields (base fields first), a tuple's parts by
/// position, an anonymous object's fields by their position in the shape, and the
/// words of a descriptor (`string` and `T[]`: `ptr`, `len`, `cap`; a two-word
/// reference, `Box<I>` or closure: its first and second word). Scalars and fixed
/// arrays have none. A sum type (an enum, `T | null`) has no `fields`, and its
/// cases' fields are in `variants`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    pub size: u64,
    pub align: u32,
    pub fields: Vec<u64>,
    pub variants: Option<VariantsLayout>,
}

impl Layout {
    /// A value with no fields.
    pub fn scalar(size: u64, align: u32) -> Layout {
        Layout {
            size,
            align,
            fields: Vec::new(),
            variants: None,
        }
    }
}

/// The cases of a sum type: an enum, `Result` among them, or `T | null`
/// (S:1644-1650).
///
/// ARCHITECTURE 3 names `VariantsLayout` without defining it. Every case's fields
/// start at one payload offset, and each case is laid out as a `final` class
/// beginning there. `T | null` has two cases, `null` (0) and present (1), the
/// second with one field, the value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VariantsLayout {
    pub tag: TagLayout,
    /// Where every case's fields begin.
    pub payload: u64,
    /// One per case, in declaration order.
    pub variants: Vec<VariantLayout>,
}

/// How a sum type's value tells its case.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TagLayout {
    /// A tag of `size` bytes at offset 0: 4 (`u32`) by default, 1 or 2 for a
    /// payload-free enum with `@repr("u8")` or `@repr("u16")`.
    Direct { size: u32 },
    /// No tag: the object word at offset 0 is 0 for `null` and is never 0 for a
    /// present value. Only `&I | null` for an interface `I` has it, SPEC 11's one
    /// exception to its rule of no niche.
    NullWord,
}

/// One case of a sum type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VariantLayout {
    /// The tag value that names the case: its position, or, in a payload-free enum
    /// whose cases carry no texts, its discriminant, truncated to the tag's width.
    /// Under [`TagLayout::NullWord`] it is 0 for `null` and 1 for present, and no
    /// tag is stored.
    pub tag: u64,
    /// The offset of each of the case's fields, from the start of the value.
    pub fields: Vec<u64>,
    /// The size of the case laid out as a `final` class, without the tag.
    pub size: u64,
}

/// Why a type has no layout (ARCHITECTURE 3 names the type without listing its
/// cases). Each names the type it is about: the innermost one that has the problem,
/// so a too-large field names the field's type, not its class.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum LayoutError {
    /// Its size would exceed the target's `isize.MAX`, or it is a `T[N]` with `N`
    /// above `isize.MAX`, whatever the size of `T` (S:1628): EN0435.
    TooLarge { ty: Ty },
    /// A borrowing class or tuple, or a `&string`: its reference forms follow the
    /// inferred permissions, so its layout is known only after contracts (S:1630,
    /// S:1640), and `sizeOf` of one is not a constant (S:756).
    DependsOnContracts { ty: Ty },
    /// A type parameter or an inference variable stands where the layout depends on
    /// what it is: mono lays out the instance.
    Generic { ty: Ty },
    /// A view `Slice<T>` or an interface `I` by value: found only behind `&` or, for
    /// an interface, `Box` (SPEC 4.1), so it has no layout of its own.
    Unsized { ty: Ty },
    /// A class or enum that holds itself inline, with no `Box` between (EN0408 is
    /// sema's).
    Recursive { ty: Ty },
    /// The type is or holds `Error`, which typing already reported.
    ErrorType { ty: Ty },
}

impl LayoutError {
    /// The type the error is about.
    pub fn ty(self) -> Ty {
        match self {
            LayoutError::TooLarge { ty }
            | LayoutError::DependsOnContracts { ty }
            | LayoutError::Generic { ty }
            | LayoutError::Unsized { ty }
            | LayoutError::Recursive { ty }
            | LayoutError::ErrorType { ty } => ty,
        }
    }
}

/// The layout of `ty` on `tcx`'s target (ARCHITECTURE 3), memoised in `tcx`'s
/// layout table (A:762), so a second call returns the same `Arc`. Each first call
/// computes in a fresh [`LayoutCx`], so the result is a function of `ty` alone: a
/// type with the same structure always gets the same layout, and nothing depends
/// on interning order or on which types were asked before.
pub fn layout_of(tcx: &Tcx, ty: Ty) -> Result<Arc<Layout>, LayoutError> {
    type Memo = Result<Arc<Layout>, LayoutError>;
    if let Some(memo) = tcx.layout_memo(ty)
        && let Some(done) = memo.downcast_ref::<Memo>()
    {
        return done.clone();
    }
    let result = LayoutCx::new(tcx).layout_of(ty);
    let stored = tcx.memo_layout(ty, Arc::new(result.clone()));
    stored.downcast_ref::<Memo>().cloned().unwrap_or(result)
}

/// A layout computation with a cache, for one `Tcx` (plan a.2). Results, errors
/// included, are kept per `Ty`; a type being laid out that is reached again from
/// inside itself is [`LayoutError::Recursive`].
pub struct LayoutCx<'t> {
    tcx: &'t Tcx,
    dl: DataLayout,
    cache: BTreeMap<Ty, Result<Arc<Layout>, LayoutError>>,
    active: BTreeSet<Ty>,
}

impl<'t> LayoutCx<'t> {
    pub fn new(tcx: &'t Tcx) -> LayoutCx<'t> {
        LayoutCx {
            tcx,
            dl: tcx.target().layout,
            cache: BTreeMap::new(),
            active: BTreeSet::new(),
        }
    }

    pub fn tcx(&self) -> &'t Tcx {
        self.tcx
    }

    /// The target's data layout: `P` and the alignments of `i64` and `f64`.
    pub fn data_layout(&self) -> DataLayout {
        self.dl
    }

    /// `P`, the size and alignment of a pointer.
    pub fn ptr(&self) -> u64 {
        u64::from(self.dl.ptr_bytes)
    }

    /// The largest size of a type or static: the target's `isize.MAX` (S:1628).
    pub fn max_size(&self) -> u64 {
        limits::max_size(self.dl)
    }

    /// The layout of `ty`, computed once.
    pub fn layout_of(&mut self, ty: Ty) -> Result<Arc<Layout>, LayoutError> {
        if let Some(done) = self.cache.get(&ty) {
            return done.clone();
        }
        if !self.active.insert(ty) {
            return Err(LayoutError::Recursive { ty });
        }
        let result = self.compute(ty).map(Arc::new);
        self.active.remove(&ty);
        self.cache.insert(ty, result.clone());
        result
    }

    /// `sizeOf<T>()`.
    pub fn size_of(&mut self, ty: Ty) -> Result<u64, LayoutError> {
        Ok(self.layout_of(ty)?.size)
    }

    /// `alignOf<T>()`.
    pub fn align_of(&mut self, ty: Ty) -> Result<u32, LayoutError> {
        Ok(self.layout_of(ty)?.align)
    }

    /// `offsetOf<T>("f")`: the offset of a class's field, or of an anonymous
    /// object's, by name, or of a tuple's part by its position written in decimal.
    /// `Ok(None)` when `ty` has no such field (EN0303 is sema's). The layout comes
    /// first, so a borrowing class reports `DependsOnContracts` whatever the name.
    pub fn offset_of(&mut self, ty: Ty, name: &str) -> Result<Option<u64>, LayoutError> {
        let layout = self.layout_of(ty)?;
        let index = match self.tcx.kind(ty) {
            TyKind::Adt(adt, _) => match &self.tcx.adt(adt).kind {
                AdtKind::Class(class) => class.field_named(intern(name)).map(|(i, _)| i),
                _ => None,
            },
            TyKind::Object(shape) => self
                .tcx
                .shape(shape)
                .position(intern(name))
                .map(|i| FieldIdx(i as u32)),
            TyKind::Tuple(parts) => {
                let count = self.tcx.list(parts).len();
                name.parse::<usize>()
                    .ok()
                    .filter(|&i| i < count && name == i.to_string())
                    .map(|i| FieldIdx(i as u32))
            }
            _ => None,
        };
        Ok(index.and_then(|i| layout.fields.get(i.0 as usize).copied()))
    }

    fn compute(&mut self, ty: Ty) -> Result<Layout, LayoutError> {
        match self.tcx.kind(ty) {
            TyKind::Bool => Ok(Layout::scalar(1, 1)),
            TyKind::Int(int) => Ok(scalar::int(self.dl, int)),
            TyKind::Float(float) => Ok(scalar::float(self.dl, float)),
            TyKind::Void | TyKind::Never => Ok(Layout::scalar(0, 1)),
            TyKind::Str | TyKind::Array(_) => Ok(scalar::descriptor(self.dl)),
            TyKind::Raw(_) | TyKind::FnPtr(..) => Ok(scalar::words(self.dl, 1)),
            TyKind::Closure(_) => Ok(scalar::words(self.dl, 2)),
            TyKind::Ref(inner) => scalar::reference(self, ty, inner),
            TyKind::Boxed(inner) => scalar::boxed(self, ty, inner),
            TyKind::Slice(_) => Err(LayoutError::Unsized { ty }),
            TyKind::Nullable(inner) => enums::nullable(self, ty, inner),
            TyKind::Fixed(elem, count) => aggregate::fixed(self, ty, elem, count),
            TyKind::Tuple(parts) => aggregate::tuple(self, ty, parts),
            TyKind::Object(shape) => aggregate::object(self, ty, shape),
            TyKind::Adt(adt, args) => match &self.tcx.adt(adt).kind {
                AdtKind::Class(_) => aggregate::class(self, ty, adt, args),
                AdtKind::Enum(_) => enums::enumeration(self, ty, adt, args),
                AdtKind::Interface(_) => Err(LayoutError::Unsized { ty }),
            },
            TyKind::Param(_) | TyKind::Infer(_) => Err(LayoutError::Generic { ty }),
            TyKind::Error => Err(LayoutError::ErrorType { ty }),
        }
    }

    /// Whether `ty` is a method interface type `I`.
    fn is_interface(&self, ty: Ty) -> bool {
        match self.tcx.kind(ty) {
            TyKind::Adt(adt, _) => self.tcx.adt(adt).is_interface(),
            _ => false,
        }
    }
}
