//! Diagnostics, the compiler's first-class feature: the code registry, the
//! `Diagnostic` model, the text and JSON renderers, fix-it application,
//! did-you-mean and explain pages (ARCHITECTURE 2.2, SPEC 13).
//!
//! A compiler phase builds [`Diagnostic`]s and emits them to a [`DiagCtx`]. The
//! driver takes them, sorted, and renders them with [`render_text`] or
//! [`render_json`]. Nothing here reads a clock, a path outside the [`SourceMap`]
//! or a hash order, so equal input renders to equal bytes.
//!
//! [`SourceMap`]: enrang_base::SourceMap

#![forbid(unsafe_code)]

mod codes;
mod ctx;
mod diagnostic;
mod explain;
mod fix;
mod json;
mod snippet;
mod suggest;
mod text;

pub use codes::{CURRENT_MILESTONE, Code, CodeRow, FixtureKind, Milestone, Owner, Phase, ROWS};
pub use ctx::{Aborted, DiagCtx};
pub use diagnostic::{Applicability, Diagnostic, Edit, Entry, EntryKind, Help, Label, Severity};
pub use explain::{ExplainPage, explain};
pub use fix::{FixConflict, apply_fixes};
pub use json::{JSON_VERSION, render_json};
pub use suggest::did_you_mean;
pub use text::{RenderOpts, render_text, shown};
