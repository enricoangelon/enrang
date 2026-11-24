//! Test support shared by the compiler's own test suites (TESTING 10).
//!
//! Suites are `harness = false` test binaries, because libtest cannot generate
//! tests dynamically. A suite registers its cases on a [`Harness`] and returns
//! the harness's exit code:
//!
//! ```no_run
//! use std::process::ExitCode;
//!
//! use enrang_testkit::{Harness, golden};
//!
//! fn main() -> ExitCode {
//!     let mut h = Harness::new("demo");
//!     h.goldens("demo");
//!     h.case("adds", || assert_eq!(1 + 1, 2));
//!     h.case("renders", || golden("demo", "hello.txt", "hello\n"));
//!     h.run()
//! }
//! ```
//!
//! The rest of the kit: seeded generators and the `ENRANG_SEED` and
//! `ENRANG_SCALE` knobs ([`Rng`], [`seed`], [`scaled`]), a shrinker ([`shrink()`]),
//! goldens and bless ([`golden()`]), tool lookup and skip accounting ([`tool`],
//! [`skip()`]), the document extractors ([`extract_cases`], [`fenced_blocks`],
//! [`row_ids`]), compile-test anchors ([`anchors()`], [`reported()`], [`compare`])
//! and milestone gating ([`gate`]). Oracle wrappers, the x86 decoder, `x86sim` and the
//! ptrace stepper arrive with the milestones that need them.

#![forbid(unsafe_code)]

mod anchors;
mod diff;
mod doc_cases;
mod gating;
mod golden;
mod harness;
mod markdown;
mod rng;
mod rows;
mod shrink;
mod skip;
mod temp;

pub use anchors::{
    Anchor, AnchorError, FixtureHeader, Mismatch, Reported, anchors, compare, fixture_header,
    fixture_target, reported,
};
pub use diff::line_diff;
pub use doc_cases::{
    Case, CaseFile, Expected, ExtractError, ExtractErrors, FencedBlock, StreamSource,
    extract_cases, fenced_blocks, headings_without_cases,
};
pub use gating::{
    FixtureStatus, GateFinding, GateReport, GateRow, gate, gate_building, gate_covers,
};
pub use golden::{
    BlessMode, GoldenDiff, GoldenFailure, GoldenStore, default_store, golden, golden_in,
    workspace_root,
};
pub use harness::{Harness, IntoOutcome, RunOptions, RunReport, catch_panic, speed_budget};
pub use rng::{
    DEFAULT_SEED, Rng, SplitMix64, Xoshiro256, parse_scale, parse_seed, rng_for, scale, scaled,
    seed,
};
pub use rows::{
    DocRow, ROW_FAMILIES, RowError, RowFamily, RowForm, numbered_row_ids, parse_covers, row_ids,
};
pub use shrink::{SHRINK_ATTEMPTS, Shrink, shrink, shrink_within};
pub use skip::{
    SkipLedger, ToolPath, find_tool, global_ledger, parse_require, require_matches, skip,
    skip_oracle, tool,
};
pub use temp::TempDir;
