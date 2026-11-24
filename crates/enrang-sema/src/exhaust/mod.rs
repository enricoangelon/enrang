//! Exhaustiveness and redundancy of `match` (plan d.13; SPEC 6 S:1134-1135; A:916;
//! owner 2D): Maranget's usefulness algorithm with witnesses over the one column
//! a `match` has (`matrix.rs`, `witness.rs`), the reading of a `hir::Match` into
//! that column (`lower.rs`), and the diagnostics (`report.rs`): a value no arm
//! handles is EN0501, an arm or arm value no value reaches warning EN0503.
//! `passes/matches.rs` runs [`check_match`] on every `match` of a finished body.
//!
//! The module needs nothing of sema but `Tcx`, so the sema suite includes these
//! files as they are and runs them on hand-built `hir::Match` expressions and on
//! random columns checked against a brute-force model (TESTING 23, plan g.3).
//! Paths inside it are therefore relative (`super::`), never `crate::`.

pub(crate) mod lower;
pub(crate) mod matrix;
pub(crate) mod report;
pub(crate) mod witness;

use enrang_diag::Diagnostic;
use enrang_hir::{Expr, ExprKind, Tcx};

use self::matrix::{Pat, Space, satisfiable, useful};
use self::witness::Witness;

/// How a guard bears on what an arm value covers.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Guard {
    /// No guard: the value covers what it matches, for every later value.
    None,
    /// The arm's `if`: the value covers the later values of its own arm, which
    /// share the guard, and nothing for later arms (A:916, a guarded arm covers
    /// nothing).
    Arm,
    /// A condition of `match (true)`, a `default` with its own condition: it
    /// covers nothing, not even the next value of its arm.
    Own,
}

/// One arm value: its pattern and its guard.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ArmPat {
    pub pat: Pat,
    pub guard: Guard,
}

/// What the algorithm says of one arm value.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) struct Verdict {
    /// Some value reaches it: it matches a value no row above it matches.
    pub reachable: bool,
    /// For an unreachable value that matches something, the first value above
    /// it that alone covers it, as `(arm, value)`.
    pub covered_by: Option<(usize, usize)>,
}

/// The verdicts of one `match`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Analysis {
    /// Per arm, per value.
    pub values: Vec<Vec<Verdict>>,
    /// The values no unguarded arm value matches, in the order of
    /// `witness::missing`; empty when the `match` is exhaustive.
    pub missing: Vec<Witness>,
}

/// Runs the usefulness algorithm over the arms of one `match`, top to bottom:
/// each value against the rows above it (the unguarded values of earlier arms,
/// and the earlier values of its own arm unless they carry their own condition),
/// then the witnesses of the whole matrix.
pub(crate) fn analyze(space: &Space, arms: &[Vec<ArmPat>]) -> Analysis {
    let mut rows: Vec<(&Pat, (usize, usize))> = Vec::new();
    let mut values = Vec::with_capacity(arms.len());
    for (a, arm) in arms.iter().enumerate() {
        let mut own = rows.clone();
        let mut verdicts = Vec::with_capacity(arm.len());
        for (v, value) in arm.iter().enumerate() {
            let pats: Vec<&Pat> = own.iter().map(|(pat, _)| *pat).collect();
            let reachable = useful(&pats, &value.pat, space);
            let covered_by = if reachable || !satisfiable(&value.pat, space) {
                None
            } else {
                own.iter()
                    .find(|(pat, _)| !useful(&[pat], &value.pat, space))
                    .map(|(_, at)| *at)
            };
            verdicts.push(Verdict {
                reachable,
                covered_by,
            });
            if value.guard != Guard::Own {
                own.push((&value.pat, (a, v)));
            }
        }
        for (v, value) in arm.iter().enumerate() {
            if value.guard == Guard::None {
                rows.push((&value.pat, (a, v)));
            }
        }
        values.push(verdicts);
    }
    let pats: Vec<&Pat> = rows.iter().map(|(pat, _)| *pat).collect();
    Analysis {
        values,
        missing: witness::missing(&pats, space),
    }
}

/// The diagnostics of the `match` expression `e`: at most one EN0501, and one
/// EN0503 per arm no value reaches, or per unreachable value of a reachable arm.
/// Nothing for any other expression, nor for a `match` whose subject typing
/// rejected or whose arm values do not fit its subject's type, which typing has
/// reported (EN0504).
pub(crate) fn check_match(tcx: &Tcx, e: &Expr) -> Vec<Diagnostic> {
    let ExprKind::Match { subject, arms } = &e.kind else {
        return Vec::new();
    };
    let Some(column) = lower::column(tcx, subject) else {
        return Vec::new();
    };
    let Some(pats) = arms
        .iter()
        .map(|arm| lower::arm_pats(tcx, &column, arm))
        .collect::<Option<Vec<_>>>()
    else {
        return Vec::new();
    };
    let analysis = analyze(&column.space, &pats);
    report::diagnostics(
        tcx,
        &report::Match {
            span: e.span,
            subject,
            arms,
            column: &column,
            pats: &pats,
        },
        &analysis,
    )
}
