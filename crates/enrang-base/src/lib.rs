//! Foundation shared by every Enrang crate: source positions and the source
//! map, interned symbols, typed index vectors and dense bit sets.

#![forbid(unsafe_code)]

mod bitset;
mod index;
mod source;
mod symbol;

pub use bitset::{BitMatrix, BitSet};
pub use index::{IdVec, Idx};
pub use source::{BytePos, FileId, FileOrigin, Loc, SourceFile, SourceMap, Span};
pub use symbol::{Symbol, intern};
