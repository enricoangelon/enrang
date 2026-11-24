//! Constant values (A:331-334) and the aggregate constants of SPEC 4.9 (D3).

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::sync::Arc;

use enrang_base::Idx;

use crate::ids::{AdtId, DefId, FieldIdx, StringId, TyList, VariantIdx};
use crate::tcx::Tcx;
use crate::ty::{FloatTy, Ty, TyKind};

/// A function with its type arguments.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct FnRef {
    pub def: DefId,
    pub args: TyList,
}

/// A scalar constant (A:332-334). A float keeps its bits at its type's width.
///
/// The derived `Ord` compares the stored bits, so it orders a negative integer
/// above every positive one (`-10` in `i32` is `0xFFFF_FFF6`): it serves map keys
/// only. A comparison by value, as a `match` range, an interval cover or const
/// eval needs, is [`ConstValue::cmp_numeric`] or [`ConstValue::as_i128`].
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum ConstValue {
    /// The two's-complement bits at the type's width, zero-extended.
    Int(u128, Ty),
    Float(u64, Ty),
    Bool(bool),
    Void,
    Str(StringId),
    FnAddr(FnRef),
    StaticAddr(DefId),
    /// In a constructor: whether its instance's override set holds the field; mono
    /// folds it to a `Bool` (ARCHITECTURE 2.6, 5).
    Overridden(FieldIdx),
}

impl ConstValue {
    /// An integer constant's value, sign-extended from its type's width when the
    /// type is signed (`isize` and `usize` at the target's pointer width); `None`
    /// for anything else.
    pub fn as_i128(&self, tcx: &Tcx) -> Option<i128> {
        let ConstValue::Int(bits, ty) = *self else {
            return None;
        };
        let TyKind::Int(int) = tcx.kind(ty) else {
            return None;
        };
        let width = int.bits(u32::from(tcx.target().layout.ptr_bytes) * 8);
        if int.is_signed() {
            let shift = 128 - width;
            Some(((bits << shift) as i128) >> shift)
        } else {
            i128::try_from(bits).ok()
        }
    }

    /// Compares two constants of one type by value: integers as numbers, signed
    /// by their type; floats by IEEE order (`None` with a NaN); `false` before
    /// `true`. `None` for any other pair.
    pub fn cmp_numeric(&self, other: &ConstValue, tcx: &Tcx) -> Option<Ordering> {
        match (*self, *other) {
            (ConstValue::Int(..), ConstValue::Int(..)) => {
                Some(self.as_i128(tcx)?.cmp(&other.as_i128(tcx)?))
            }
            (ConstValue::Float(a, at), ConstValue::Float(b, bt)) => {
                float_of(a, at, tcx)?.partial_cmp(&float_of(b, bt, tcx)?)
            }
            (ConstValue::Bool(a), ConstValue::Bool(b)) => Some(a.cmp(&b)),
            _ => None,
        }
    }
}

/// A float constant's value: `f32` bits widen exactly to `f64`.
fn float_of(bits: u64, ty: Ty, tcx: &Tcx) -> Option<f64> {
    match tcx.kind(ty) {
        TyKind::Float(FloatTy::F32) => Some(f64::from(f32::from_bits(bits as u32))),
        TyKind::Float(FloatTy::F64) => Some(f64::from_bits(bits)),
        _ => None,
    }
}

/// A constant's whole value (departure D3): SPEC 4.9 makes fixed-array and class
/// literals, and constant literal views, constant expressions, and ARCHITECTURE's
/// `ConstValue` has no aggregate. Stored per constant in `Tcx` (`const_value`); a
/// read of a constant in a body stays `ExprKind::Static(def)` (A:574).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstTree {
    Scalar(ConstValue),
    /// A fixed array `[a, b, c]` or `[x; n]`.
    Array(Vec<ConstTree>),
    /// A class's named form, or an enum case (`variant`), fields in `FieldIdx` order.
    Adt {
        adt: AdtId,
        variant: Option<VariantIdx>,
        fields: Vec<ConstTree>,
    },
    Tuple(Vec<ConstTree>),
    /// An anonymous object, fields in shape order.
    Object(Vec<ConstTree>),
    /// `null` of a nullable.
    Null,
    /// A present value of a nullable.
    Present(Box<ConstTree>),
    /// A constant literal view `&[1, 2]` at `&Slice<T>` (SPEC 4.5 C18, 4.9).
    View {
        elem: Ty,
        items: Vec<ConstTree>,
    },
}

impl ConstTree {
    /// The scalar, when the tree is one.
    pub fn as_scalar(&self) -> Option<ConstValue> {
        match self {
            ConstTree::Scalar(value) => Some(*value),
            _ => None,
        }
    }
}

/// Interned literal texts: `StringId` to text, ids in order of first interning.
#[derive(Clone, Debug, Default)]
pub struct StringTable {
    texts: Vec<Arc<str>>,
    ids: BTreeMap<Arc<str>, StringId>,
}

impl StringTable {
    pub fn new() -> StringTable {
        StringTable::default()
    }

    /// The id of `text`, interning it on first use.
    pub fn intern(&mut self, text: &str) -> StringId {
        if let Some(&id) = self.ids.get(text) {
            return id;
        }
        let id = StringId::new(self.texts.len());
        let text: Arc<str> = Arc::from(text);
        self.texts.push(Arc::clone(&text));
        self.ids.insert(text, id);
        id
    }

    /// The text of `id`. Panics on an id of another table.
    pub fn get(&self, id: StringId) -> Arc<str> {
        Arc::clone(&self.texts[id.index()])
    }

    pub fn len(&self) -> usize {
        self.texts.len()
    }

    pub fn is_empty(&self) -> bool {
        self.texts.is_empty()
    }

    /// Every text with its id, in interning order.
    pub fn iter(&self) -> impl Iterator<Item = (StringId, &str)> {
        self.texts
            .iter()
            .enumerate()
            .map(|(i, text)| (StringId::new(i), &**text))
    }
}
