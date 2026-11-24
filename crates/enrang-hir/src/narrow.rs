//! Narrowing facts and recorded references (departure D1; A:898, A:1250).
//!
//! Typing narrows a path inside `check_expr` and records every reference made to a
//! proper prefix of a fact's path, or to the path at its nullable type, because it
//! cannot tell which of them write: phase 3 checks the records on MIR (A:1250).
//! ARCHITECTURE 2.4 gives them no place in the HIR, so a body stores its facts and
//! records here, and each record names the expression it was made at by `ExprId`,
//! which mirbuild maps to a MIR point.

use enrang_base::Span;

use crate::ids::{ExprId, FactId, FieldIdx, LocalId, VariantIdx};

/// What a fact is about: a local (or `this`) plus field steps (A:898).
#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct FactPath {
    pub root: LocalId,
    pub steps: Vec<PathStep>,
}

impl FactPath {
    /// Whether `self` is a proper prefix of `other`.
    pub fn is_proper_prefix_of(&self, other: &FactPath) -> bool {
        self.root == other.root
            && self.steps.len() < other.steps.len()
            && other.steps.starts_with(&self.steps)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum PathStep {
    Field(FieldIdx),
    /// Through `&` or `Box` (SPEC 4.8).
    Deref,
    /// Into a narrowed nullable's payload.
    Payload,
}

/// A fact: non-null, or inside a `match` arm and its guard, the arm's case (A:898).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Fact {
    NonNull,
    Case(VariantIdx),
}

/// One fact of a body, with the test that made it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FactInfo {
    pub path: FactPath,
    pub fact: Fact,
    pub span: Span,
    /// The later tests of the same path made while the fact held, which keep it
    /// (sema's choice) but are new tests for phase 3 (S:742, I6: "with no new
    /// test between").
    pub retests: Vec<Span>,
}

/// How a recorded reference was made (A:898, SPEC 4.8).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum RecordKind {
    CallArg,
    Receiver,
    Copy,
    Binding,
    Capture,
    HiddenArg,
}

/// A reference that phase 3 must check against `fact`, made at expression `expr`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NarrowRecord {
    pub fact: FactId,
    pub expr: ExprId,
    pub kind: RecordKind,
    pub span: Span,
}
