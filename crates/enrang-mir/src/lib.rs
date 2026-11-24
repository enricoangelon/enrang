//! MIR: the types, the text form (print and parse), the verifier, the CFG tools and
//! the dataflow framework (ARCHITECTURE 1, 2.5, 3; M3 plan b).
//!
//! This is a contract crate (ARCHITECTURE 1 "Parallel work rules"): mirbuild writes
//! MIR, borrowck, mono, the VM and codegen read it, so it changes only through its
//! owner. The text form decouples them: a `.mir` fixture is a whole module,
//! declarations then bodies, and `parse_module` builds its own `Tcx` through the
//! public `define_*` API, so borrowck, the VM and codegen test with no front end.
//!
//! Determinism: no hash map anywhere; bodies print in owner `ItemPath` order and
//! declarations in `ItemPath` order, never by an id (ARCHITECTURE 1).

#![forbid(unsafe_code)]

mod body;
pub mod cfg;
pub mod dataflow;
mod decls;
mod ids;
mod parse;
mod print;
mod proj;
mod remap;
mod verify;

pub use body::{
    AdtNames, AggregateKind, AsmStmt, BinOp, Block, Bodies, Body, BodyNames, BodyOwner,
    BorrowOrigin, Callee, Capture, CaptureKind, CheckedOp, ClassHolder, ClassOp, ClosureFn,
    ConstKind, Constant, DropOrigin, ForOfLoop, ForeignRef, FormCall, LiteralStatic, LocalDecl,
    LocalKind, LoopRole, LoopSource, MirFact, MirPhase, MirRecord, MovePathKey, MoveStep, Operand,
    PhaseMeta, Place, Proj, Rvalue, ShimKind, Statement, StatementKind, Terminator, TerminatorKind,
    UnOp, UnsafeKind, UnsafeRegion,
};
pub use cfg::Cfg;
pub use dataflow::{DataflowAnalysis, GenKill, GenKillAnalysis, Results, solve};
pub use enrang_hir::{CastKind, ConvKind, IntrinsicKind, IntrinsicName};
pub use ids::{BlockId, Local, Point, ProjId, RegionId};
pub use parse::{MirParseError, parse_module, redefine_adts};
pub use print::{DEFAULT_MODULE, DEFAULT_TARGET, print_body, print_module};
pub use proj::{
    PlaceTy, ProjTable, canonicalize_projs, places, statement_places, statement_places_mut,
    tag_value, terminator_places, terminator_places_mut, variant_count, variant_name,
    variant_named, visit_places_mut,
};
pub use remap::{RemapError, remap_ids};
pub use verify::{Rule, VerifyError, callee_types, verify};
