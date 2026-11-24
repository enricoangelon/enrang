//! The id types of MIR (ARCHITECTURE 2.5): dense `u32` indices into one body.

use std::fmt;

use enrang_base::Idx;

macro_rules! define_ids {
    ($($(#[$doc:meta])* $name:ident $prefix:literal;)*) => {$(
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

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, concat!($prefix, "{}"), self.0)
            }
        }
    )*};
}

define_ids! {
    /// A local: `_0` the return slot, `_1.._arg_count` the arguments (A:455).
    Local "_";
    /// A basic block; `bb0` is the entry.
    BlockId "bb";
    /// An interned projection list of one body ([`crate::ProjTable`]); `ProjId(0)`
    /// is the empty list.
    ProjId "proj";
    /// An `unsafe` region of one body (`Body::unsafe_regions`).
    RegionId "r";
}

impl Local {
    /// The return slot.
    pub const RETURN: Local = Local(0);
}

impl BlockId {
    /// The entry block.
    pub const ENTRY: BlockId = BlockId(0);
}

impl ProjId {
    /// The empty projection list: a place that is its local.
    pub const EMPTY: ProjId = ProjId(0);
}

/// A position in a body: statement `index` of `block`, the terminator when `index`
/// is the block's statement count. Ordered by block, then index (plan b.1).
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Point {
    pub block: BlockId,
    pub index: u32,
}

impl Point {
    pub fn new(block: BlockId, index: usize) -> Point {
        Point {
            block,
            index: u32::try_from(index).expect("a statement index exceeds u32"),
        }
    }
}

/// `bb3[1]`, as the text form prints a point.
impl fmt::Display for Point {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}[{}]", self.block, self.index)
    }
}
