//! Compilation sessions and pipelines (ARCHITECTURE 3 and 11).
//!
//! No pipeline exists yet, because nothing can be compiled at this milestone. What
//! the command line needs today is a [`Session`], which is where every diagnostic
//! of a run goes and where it is rendered from.

#![forbid(unsafe_code)]

use std::sync::Arc;

use enrang_base::SourceMap;
use enrang_diag::{DiagCtx, RenderOpts, render_text};

/// One run of the compiler: its sources and its diagnostics. The fields of
/// ARCHITECTURE 3 that are missing come with the crates that define their types.
#[derive(Debug, Default)]
pub struct Session {
    pub map: Arc<SourceMap>,
    pub dcx: DiagCtx,
}

impl Session {
    /// A session with no sources and no diagnostics.
    pub fn new() -> Session {
        Session::default()
    }

    /// Renders what was emitted since the last call, sorted, as stderr shows it.
    pub fn render(&mut self, opts: &RenderOpts) -> String {
        render_text(&self.dcx.take(), &self.map, opts)
    }
}
