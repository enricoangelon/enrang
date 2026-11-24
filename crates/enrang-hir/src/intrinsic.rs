//! The intrinsic table (ARCHITECTURE 2.5, A:527-534). It lives here because HIR
//! names it; `enrang-mir` re-exports it.
//!
//! `define_intrinsics!` generates [`IntrinsicKind`], whose kinds carry what a call
//! decides (a type, an operation), and [`IntrinsicName`], the payload-free name that
//! `@intrinsic("Kind")` binds, with `ALL`, the name table and the safety bit: set for
//! a kind a safe declaration names, as `SizeOf` is, or that mirbuild emits in safe
//! code, as `AllocArray` is; clear for `SliceFromRaw`, the memory, volatile and
//! unaligned kinds and `DivWideU32`, which only an `unsafe` declaration names. The
//! MIR verifier reads the bit, and a meta-test compares it with every `@intrinsic`
//! declaration of the library.
//!
//! `AtomicAlu(AluOp)` and `AtomicBitTest(bool)` carry a parameter that an
//! `@intrinsic("...")` string cannot name (plan doc gap G13): the name binds the
//! kind, and the declaration that uses it decides the payload.

use std::fmt;

use enrang_target::Feature;

use crate::ids::FieldIdx;
use crate::ty::Ty;

/// The read-modify-write operation of `AtomicAlu` (SPEC 10.5: `add`, `sub`, `and`,
/// `or`, `xor`, with no result).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum AluOp {
    Add,
    Sub,
    And,
    Or,
    Xor,
}

macro_rules! define_intrinsics {
    ($($variant:ident $(($($payload:ty),*))? = $safe:literal,)*) => {
        /// A compiler intrinsic with what one call decides.
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
        pub enum IntrinsicKind {
            $($variant $(($($payload),*))?,)*
        }

        /// The name of an intrinsic kind: what `@intrinsic("Kind")` binds.
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
        pub enum IntrinsicName {
            $($variant,)*
        }

        impl IntrinsicName {
            /// Every kind, in A:527-534's order.
            pub const ALL: &'static [IntrinsicName] = &[$(IntrinsicName::$variant,)*];

            /// The `@intrinsic("...")` argument: the kind's name.
            pub fn name(self) -> &'static str {
                match self {
                    $(IntrinsicName::$variant => stringify!($variant),)*
                }
            }

            /// Whether a safe declaration may name it, or mirbuild emit it in safe
            /// code.
            pub fn is_safe(self) -> bool {
                match self {
                    $(IntrinsicName::$variant => $safe,)*
                }
            }
        }

        impl IntrinsicKind {
            /// The kind's name.
            pub fn name(&self) -> IntrinsicName {
                match self {
                    $(IntrinsicKind::$variant { .. } => IntrinsicName::$variant,)*
                }
            }
        }
    };
}

define_intrinsics! {
    VolatileRead = false,
    VolatileWrite = false,
    ReadUnaligned = false,
    WriteUnaligned = false,
    MemCopy = false,
    MemCopyOverlap = false,
    MemSet = false,
    AtomicLoad = true,
    AtomicStore = true,
    AtomicExchange = true,
    AtomicAlu(AluOp) = true,
    AtomicIncDecTest(bool) = true,
    AtomicBitTest(bool) = true,
    AtomicFence = true,
    AtomicCompareExchange = true,
    AtomicFetchAdd = true,
    MulWideU32 = true,
    DivWideU32 = false,
    CpuHas(Feature) = true,
    SizeOf(Ty) = true,
    AlignOf(Ty) = true,
    OffsetOf(Ty, FieldIdx) = true,
    AllocArray(Ty) = true,
    ToBitsCanon = true,
    FromBits = true,
    SliceFromRaw(Ty) = false,
}

impl IntrinsicName {
    /// The kind `@intrinsic(name)` names; an unknown name is EN0806 in sema.
    pub fn from_name(name: &str) -> Option<IntrinsicName> {
        IntrinsicName::ALL
            .iter()
            .copied()
            .find(|k| k.name() == name)
    }
}

impl IntrinsicKind {
    /// Whether the kind's safety bit is set.
    pub fn is_safe(&self) -> bool {
        self.name().is_safe()
    }

    /// `CpuHas` of the feature spelled `feature` (`sse2`), for a reader that cannot
    /// name `enrang-target`'s `Feature`, as the MIR text parser.
    pub fn cpu_has_named(feature: &str) -> Option<IntrinsicKind> {
        Feature::from_name(feature).map(IntrinsicKind::CpuHas)
    }
}

impl fmt::Display for IntrinsicName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}
