//! The id types of the typed HIR (ARCHITECTURE 2.4).
//!
//! ARCHITECTURE names `DefId`, `AdtId`, `Ty` and the ids inside `TyKind` without
//! defining them; every one here is a dense `u32` index handed out in definition or
//! interning order. Those orders follow load order, so an id never orders anything
//! that reaches output or an interface file (ARCHITECTURE 1, 2.1): such data is
//! sorted by [`crate::ItemPath`] instead.

use enrang_base::Idx;

macro_rules! define_ids {
    ($($(#[$doc:meta])* $name:ident;)*) => {$(
        $(#[$doc])*
        #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
        pub struct $name(pub u32);

        impl Idx for $name {
            fn new(i: usize) -> Self {
                $name(u32::try_from(i).expect(concat!(stringify!($name), " exceeds u32")))
            }

            fn index(self) -> usize {
                self.0 as usize
            }
        }
    )*};
}

define_ids! {
    /// A definition: an item, a member, a constructor or destructor, an `extend`
    /// block, a test, a module (ARCHITECTURE 2.4).
    DefId;
    /// A class, enum or method interface: the payload of `TyKind::Adt`.
    AdtId;
    /// A module of the program, user or library, in load order.
    ModuleId;
    /// A type parameter, written or implicit (`TyKind::Param`).
    ParamId;
    /// A generics list: an item's own type parameters, linked to its parent's.
    GenericsId;
    /// A bound on a type parameter: an interface or a class with its arguments.
    BoundId;
    /// An interned anonymous object type's field list ([`crate::Shape`]).
    ShapeId;
    /// An interned list of types: a tuple's parts, an ADT's arguments.
    TyList;
    /// An interned function pointer or closure signature ([`crate::FnPtrSig`]).
    FnSigId;
    /// A field: of a class, its place in the flattened field list, base fields
    /// first; of a tuple, the part's position; of an anonymous object, the field's
    /// position in its shape (fields sorted by name).
    FieldIdx;
    /// A case of an enum, in declaration order. `Result`'s `Ok` is 0, `Err` 1.
    VariantIdx;
    /// A local of one body: `this`, a parameter, a binding, a hidden argument.
    LocalId;
    /// An arrow function of one body.
    ArrowId;
    /// A loop of one body, the target of `break` and `continue`.
    LoopId;
    /// An expression of one body, `0..Body::expr_count`, the anchor a narrowing
    /// record names (plan departure D1).
    ExprId;
    /// A narrowing fact of one body (plan departure D1).
    FactId;
    /// An interned literal text ([`crate::StringTable`]).
    StringId;
    /// An interned `@hostCall("name")` name (no table before M4).
    HostCallId;
    /// An inference variable, alive only while one body is typed.
    InferVar;
    /// A program's top-level variable, in declaration order (SPEC 7, N13).
    TopVar;
}

impl FieldIdx {
    /// The index as a `u32`, as `ConstTree` and MIR projections print it.
    pub fn as_u32(self) -> u32 {
        self.0
    }
}

impl VariantIdx {
    /// `Result`'s `Ok` case.
    pub const OK: VariantIdx = VariantIdx(0);
    /// `Result`'s `Err` case.
    pub const ERR: VariantIdx = VariantIdx(1);
    /// `T | null`'s `null` case (layout `enums.rs`; M3 plan K5).
    pub const NULL: VariantIdx = VariantIdx(0);
    /// `T | null`'s present case, whose one field is the `T`.
    pub const PRESENT: VariantIdx = VariantIdx(1);
}
