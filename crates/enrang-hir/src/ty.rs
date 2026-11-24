//! Types (ARCHITECTURE 2.4): the interned [`Ty`], its [`TyKind`], and the interned
//! signatures, lists and shapes it refers to.
//!
//! **Departure D2.** ARCHITECTURE's `Tcx::kind(&self, t) -> &TyKind` beside
//! `intern_ty(&self, k)` would hand out references into a table that grows behind
//! `&self`, which safe Rust cannot do. So `TyKind` holds only ids and is `Copy`, and
//! `Tcx::kind` returns it by value; `FnPtr` and `Closure` carry an [`FnSigId`], a
//! tuple and an ADT's arguments a [`TyList`], an object a [`ShapeId`], each interned
//! the same way. Interning makes structural equality identity: two equal kinds are
//! one `Ty`, and two signatures that differ only in their rows (marks, `readonly`)
//! are two types, which typing compares with `Tcx::same_ignoring_rows` (A:288-291).

use std::fmt;

use enrang_base::Symbol;

use crate::ids::{AdtId, FnSigId, InferVar, ParamId, ShapeId, TyList};
use crate::sig::Mark;

/// An interned type; equality is identity (ARCHITECTURE 2.4).
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Ty(pub u32);

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Ty({})", self.0)
    }
}

/// What a [`Ty`] is (ARCHITECTURE 2.4, with D2's ids for the variable-size parts).
///
/// `Slice` is a view, found only as the pointee of a `Ref` (SPEC 4.1) or as the
/// argument of a type parameter whose `views_ok` holds (ARCHITECTURE 4). A lang
/// class reached by name is normalised to its kind: `string` is `Str`, `Slice<T>`
/// `Slice(T)`, `T[]` `Array(T)`, `Box<T>` `Boxed(T)`, and no `Adt` of those four
/// ever exists (`Tcx::lang` maps back to their `@lang` classes). `Closure` is
/// written only as a parameter type, at most under one `Nullable` at the top
/// (EN0705), and is also the inferred type of a local holding a capturing arrow.
/// `Infer` appears only while a body is typed; a finished body holds none.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum TyKind {
    Bool,
    Int(IntTy),
    Float(FloatTy),
    Void,
    Never,
    Str,
    Array(Ty),
    Fixed(Ty, u64),
    Slice(Ty),
    Tuple(TyList),
    Boxed(Ty),
    Nullable(Ty),
    /// One reference kind: read or write is a contract (phase 3).
    Ref(Ty),
    /// One raw pointer kind.
    Raw(Ty),
    FnPtr(Abi, FnSigId),
    Closure(FnSigId),
    Adt(AdtId, TyList),
    Param(ParamId),
    Infer(InferVar),
    /// An anonymous object type: structural, so one field set is one type.
    Object(ShapeId),
    /// A type that typing rejected; it absorbs every later check.
    Error,
}

/// The integer types; `int` is `I32` (SPEC 4.6).
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum IntTy {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    Isize,
    Usize,
}

impl IntTy {
    pub const ALL: [IntTy; 10] = [
        IntTy::I8,
        IntTy::I16,
        IntTy::I32,
        IntTy::I64,
        IntTy::U8,
        IntTy::U16,
        IntTy::U32,
        IntTy::U64,
        IntTy::Isize,
        IntTy::Usize,
    ];

    /// The keyword, with `i32` as written: diagnostics print `int` (`Tcx::ty_string`).
    pub fn name(self) -> &'static str {
        match self {
            IntTy::I8 => "i8",
            IntTy::I16 => "i16",
            IntTy::I32 => "i32",
            IntTy::I64 => "i64",
            IntTy::U8 => "u8",
            IntTy::U16 => "u16",
            IntTy::U32 => "u32",
            IntTy::U64 => "u64",
            IntTy::Isize => "isize",
            IntTy::Usize => "usize",
        }
    }

    pub fn is_signed(self) -> bool {
        matches!(
            self,
            IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I64 | IntTy::Isize
        )
    }

    /// The width in bits, with `ptr_bits` for `isize` and `usize`.
    pub fn bits(self, ptr_bits: u32) -> u32 {
        match self {
            IntTy::I8 | IntTy::U8 => 8,
            IntTy::I16 | IntTy::U16 => 16,
            IntTy::I32 | IntTy::U32 => 32,
            IntTy::I64 | IntTy::U64 => 64,
            IntTy::Isize | IntTy::Usize => ptr_bits,
        }
    }
}

/// The float types (SPEC 4.6).
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum FloatTy {
    F32,
    F64,
}

impl FloatTy {
    pub fn name(self) -> &'static str {
        match self {
            FloatTy::F32 => "f32",
            FloatTy::F64 => "f64",
        }
    }
}

/// A function pointer's calling convention: Enrang's own, or a foreign one named by
/// `@abi` (SPEC 7.3). ARCHITECTURE 2.4 names `Abi` without listing its values.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Abi {
    Enrang,
    Win64,
    Sysv,
}

impl Abi {
    /// The `@abi("...")` argument that names it; `None` for Enrang's own.
    pub fn name(self) -> Option<&'static str> {
        match self {
            Abi::Enrang => None,
            Abi::Win64 => Some("win64"),
            Abi::Sysv => Some("sysv"),
        }
    }
}

/// A function pointer's signature, part of `Ty` identity, marks and `readonly`
/// included, so mono and layout tell rows apart; typing unifies two of them ignoring
/// marks, and phase 3 compares the rows (N1, EN0615). Parameter names are not part
/// of it (A:288).
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct FnPtrSig {
    pub unsafety: bool,
    pub params: Vec<(Ty, Mark)>,
    pub ret: Ty,
    pub ret_readonly: bool,
}

impl FnPtrSig {
    /// A safe signature with unmarked parameters and a writable result.
    pub fn new(params: &[Ty], ret: Ty) -> FnPtrSig {
        FnPtrSig {
            unsafety: false,
            params: params.iter().map(|&t| (t, Mark::None)).collect(),
            ret,
            ret_readonly: false,
        }
    }
}

/// A closure type's signature: the same row as a function pointer's, never `unsafe`
/// (ARCHITECTURE 2.4 names it without defining it).
pub type ClosureSig = FnPtrSig;

/// An anonymous object type: its fields, sorted by name (`Symbol` orders by text),
/// with `x?: T` already collapsed to `T | null` (A:888), and, sorted too, the names
/// of the fields written `x?: T`, which a literal at the type may leave out (SPEC 3.2,
/// S:600). One field set is one type.
///
/// **Departure D13.** ARCHITECTURE's shape is the fields alone, which would make
/// `{ v?: i64 | null }` and `{ v: i64 | null }` one type, so typing could not tell
/// whether a literal may leave `v` out. `optional` is part of identity, as a
/// function pointer's rows are, and typing compares two shapes ignoring it
/// (`Tcx::same_ignoring_rows`); layout reads only `fields`.
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Shape {
    pub fields: Vec<(Symbol, Ty)>,
    pub optional: Vec<Symbol>,
}

impl Shape {
    /// A shape of `fields` in any order, none of them optional; they are sorted here.
    pub fn new(fields: Vec<(Symbol, Ty)>) -> Shape {
        Shape::with_optional(fields, Vec::new())
    }

    /// A shape of `fields` whose fields named in `optional` were written `x?: T`;
    /// both are sorted here, and a name that is no field is dropped.
    pub fn with_optional(mut fields: Vec<(Symbol, Ty)>, mut optional: Vec<Symbol>) -> Shape {
        fields.sort_by_key(|field| field.0);
        optional.retain(|name| fields.iter().any(|(field, _)| field == name));
        optional.sort();
        optional.dedup();
        Shape { fields, optional }
    }

    /// The position of `name`, its `FieldIdx` in an `Object` of this shape.
    pub fn position(&self, name: Symbol) -> Option<usize> {
        self.fields.iter().position(|(field, _)| *field == name)
    }

    /// Whether the field `name` was written `name?: T`, so a literal may leave it out.
    pub fn is_optional(&self, name: Symbol) -> bool {
        self.optional.binary_search(&name).is_ok()
    }
}
