//! Contracts: what a caller sees of a function (SPEC 5, N1-N14; A:293-325).
//!
//! Inferred from bodies in phase 3, or built from marks and SPEC 5.4's defaults
//! where no body can be read or trusted. Type checking never reads one, so M2
//! writes none: these are the types only, kept field for field, with the three
//! additions phase 3 needs that ARCHITECTURE names but 2.4 does not list (M3 plan
//! K1-K3): `Store::read_set_only`, `Contract::moves_or_writes` and three causes of a
//! read-only result.

use crate::ids::FieldIdx;
use crate::path::ItemPath;

/// The sources of a returned reference: none, or these parameters (sorted; index 0
/// is `this` when there is a receiver).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum RetSources {
    NoLoans,
    Params(Vec<u32>),
}

/// A function's contract (A:295-305).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Contract {
    pub perms: Vec<Perm>,
    pub sources: RetSources,
    pub result: ResultPerm,
    /// Sources the result reaches only through the reference fields of a borrowing
    /// value whose class never writes through them (section 6.3).
    pub through_fields: Vec<u32>,
    /// Sources the result reaches only through the `readonly &` fields of a
    /// borrowing value (section 6.3).
    pub through_read: Vec<u32>,
    pub stores: Vec<Store>,
    /// One per by-value parameter, in parameter order: the body moves or writes it
    /// (A:1336, A:1370; M3 plan K2). Read only by G07's help (A:1314); a fact of the
    /// contract, so it is printed and checked for freshness, but kept out of
    /// `sigHash` (ledger 84).
    pub moves_or_writes: Vec<bool>,
}

/// What parameter `from` holds is stored in the borrowing value behind parameter
/// `into` (A:306-310).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Store {
    pub from: u32,
    pub into: u32,
    /// Only what `from`'s reference fields hold.
    pub fields_only: bool,
    /// It reaches a `readonly &` field, so the value's read set too.
    pub read: bool,
    /// Only what `from`'s `readonly &` fields hold (its read set) is stored,
    /// whatever its class writes; never also `fields_only`; with `from == into` the
    /// caller runs no read-set check (A:308-310, A:1281; M3 plan K1).
    pub read_set_only: bool,
}

/// One per `&` parameter, `this` first, then one per reference part of each
/// by-value borrowing tuple parameter (A:311-313); `Own` only for a `move` method.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Perm {
    Read,
    Write,
    Own,
}

/// One per borrowing class and borrowing tuple type, inferred with the contracts
/// (A:314-320).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ClassContract {
    pub writes_through_fields: bool,
}

/// Whether a returned reference may be written (A:329): `ReadOnly` carries the
/// first cause, for the diagnostic.
#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum ResultPerm {
    None,
    ReadOnly(Reason),
    Writable,
}

/// The first cause of a read-only result (S:939, S:773). ARCHITECTURE names it
/// without defining it. A contract goes into the hashed API section of an interface
/// file and into `sigHash`, keyed by stable item path, so no contract names a
/// `DefId` (A:440, A:1281) or a `Span`, whose `FileId` follows load order: a cause
/// names a definition by its [`ItemPath`], and where in the body the cause sits is
/// the checker's to keep beside the contract, in the unhashed witnesses of
/// ARCHITECTURE 6.7, as the chain behind a Write permission is.
#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Reason {
    /// The return type says `readonly`.
    Declared,
    /// A `const` local or by-value parameter of the body, or what it owns.
    ConstRoot,
    /// A top-level `const`.
    Constant(ItemPath),
    /// A static (`unsafe let`).
    Static(ItemPath),
    /// A callee's read-only result.
    ReadonlyResult(ItemPath),
    /// A part of a string, or a string literal.
    StringPart,
    /// A read through a raw pointer.
    RawDeref,
    /// A `readonly` field, or a reference field or tuple part declared `readonly &`,
    /// of the class at this path.
    ReadonlyField(ItemPath, FieldIdx),
    /// The result may also come from what parameter `n` stored in a borrowing value
    /// (S:939 "`keep` also keeps a reference from `x` in `this`"; M3 plan K3).
    StoredSource(u32),
    /// Two returned parts may point at the same data (S:939; M3 plan K3).
    AliasedParts,
    /// A constant literal view, which may point at a constant (S:964; M3 plan K3).
    ConstLiteral,
}
