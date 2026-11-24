//! The buffer diagnostics are emitted to during a compile (ARCHITECTURE 3).

use std::collections::BTreeSet;

use enrang_base::Span;

use crate::codes::Code;
use crate::diagnostic::Diagnostic;

/// A compile stopped at the end of the phase that reported an error (SPEC 13.1).
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Aborted;

/// Buffers diagnostics and keeps the first of each `(code, primary span)`. With no
/// span, which is no place at all, the message stands in for the place.
#[derive(Debug, Default)]
pub struct DiagCtx {
    buffered: Vec<Diagnostic>,
    seen: BTreeSet<(Code, Span, String)>,
    phase_failed: bool,
    failed: bool,
}

impl DiagCtx {
    pub fn new() -> Self {
        Self::default()
    }

    /// Buffers `diag`, unless an earlier one had its code and primary span. That
    /// holds across phases and across [`DiagCtx::take`], so recovery that reaches
    /// one mistake twice reports it once.
    ///
    /// Two different command-line errors under one code are two mistakes (SPEC 13.1:
    /// each phase reports all its errors), so spanless diagnostics compare by message.
    pub fn emit(&mut self, diag: Diagnostic) {
        let place = if diag.primary.span.is_dummy() {
            diag.message.clone()
        } else {
            String::new()
        };
        if !self.seen.insert((diag.code, diag.primary.span, place)) {
            return;
        }
        if diag.severity.fails() {
            self.phase_failed = true;
            self.failed = true;
        }
        self.buffered.push(diag);
    }

    /// Whether anything that fails a run was ever emitted, taken or not.
    pub fn has_errors(&self) -> bool {
        self.failed
    }

    /// Whether a diagnostic with `code` at the primary `span` was emitted, taken or
    /// not, so that a later step can leave alone a place an earlier one reported: the
    /// lexer skips a U+FFFD where the driver reported EN0001. Always `false` for a
    /// dummy span, which is no place.
    pub fn reported(&self, code: Code, span: Span) -> bool {
        !span.is_dummy() && self.seen.contains(&(code, span, String::new()))
    }

    /// Ends a phase: `Err` when this phase, since the last call, reported an
    /// error. Warnings and notes alone let the compile continue.
    pub fn finish_phase(&mut self) -> Result<(), Aborted> {
        if std::mem::take(&mut self.phase_failed) {
            Err(Aborted)
        } else {
            Ok(())
        }
    }

    /// Empties the buffer, sorted by file, then position. Global positions grow
    /// from file to file, so the primary span's order is both. Diagnostics with no
    /// span come first, and equal spans keep the order they were emitted in.
    pub fn take(&mut self) -> Vec<Diagnostic> {
        let mut diags = std::mem::take(&mut self.buffered);
        diags.sort_by_key(|diag| diag.primary.span);
        diags
    }
}
