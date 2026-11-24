//! Milestone gating (TESTING 18).
//!
//! Every macro row and extracted case carries `since(Mn)`, and meta-tests enforce
//! only rows with `since <= CURRENT_MILESTONE`. A row that has reached its
//! milestone and has no passing fixture is a gap. A row that has not, yet claims a
//! passing fixture, has a stale `since`. Both fail.
//!
//! The milestone being built, the one after the current, lands its work before the
//! commit that closes it bumps the constant. [`gate_building`] lets that milestone's
//! rows pass early: they are listed as early, not stale, and a row two milestones
//! ahead is still stale. [`gate`] allows nothing early.
//!
//! Rows are plain data and the milestone type is the caller's, so this does not
//! depend on `enrang-diag`.

use std::collections::BTreeSet;
use std::fmt;
use std::fmt::Debug;

/// What a row's fixture is doing today. The order is from worst to best.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub enum FixtureStatus {
    Missing,
    /// It exists but does not pass.
    Failing,
    Passing,
}

impl FixtureStatus {
    /// The status of a row that either piece of evidence proves: the better one.
    pub fn best(self, other: FixtureStatus) -> FixtureStatus {
        self.max(other)
    }

    /// The status of a row that needs both pieces of evidence: the worse one.
    pub fn worst(self, other: FixtureStatus) -> FixtureStatus {
        self.min(other)
    }
}

/// One row of a registry or document.
#[derive(Clone, Debug)]
pub struct GateRow<'a, M> {
    pub id: &'a str,
    pub since: M,
    pub fixture: FixtureStatus,
}

/// A row that fails the gate.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct GateFinding {
    pub id: String,
    /// The row's milestone, as its `Debug` form.
    pub since: String,
    pub fixture: FixtureStatus,
}

/// The outcome of a gate over some rows.
#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub struct GateReport {
    /// The current milestone, as its `Debug` form.
    pub current: String,
    /// Rows with `since <= current`, which the gate enforced.
    pub enforced: usize,
    /// Rows with `since > current`, which must not claim a passing fixture yet.
    pub deferred: usize,
    /// Deferred rows of the milestone being built that already pass. They fail
    /// nothing; the commit closing that milestone turns them into enforced rows.
    pub early: Vec<GateFinding>,
    /// Enforced rows without a passing fixture.
    pub gaps: Vec<GateFinding>,
    /// Deferred rows that claim a passing fixture.
    pub stale: Vec<GateFinding>,
    /// IDs that more than one row uses.
    pub duplicates: Vec<String>,
    /// `covers` claims that name no row.
    pub orphans: Vec<String>,
}

impl GateReport {
    pub fn is_clean(&self) -> bool {
        self.gaps.is_empty()
            && self.stale.is_empty()
            && self.duplicates.is_empty()
            && self.orphans.is_empty()
    }

    /// `Ok` if the gate passed, so a harness case can return it directly.
    pub fn into_result(self) -> Result<(), GateReport> {
        if self.is_clean() { Ok(()) } else { Err(self) }
    }
}

impl fmt::Display for GateReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let current = &self.current;
        for gap in &self.gaps {
            let state = match gap.fixture {
                FixtureStatus::Missing => "has no fixture",
                _ => "has a failing fixture",
            };
            writeln!(
                f,
                "gap: {} {state} (since {}, current {current})",
                gap.id, gap.since
            )?;
        }
        for row in &self.stale {
            writeln!(
                f,
                "stale: {} claims a passing fixture before its milestone (since {}, current {current})",
                row.id, row.since
            )?;
        }
        for id in &self.duplicates {
            writeln!(f, "duplicate: {id} is used by more than one row")?;
        }
        for id in &self.orphans {
            writeln!(f, "orphan: `covers: {id}` names no row")?;
        }
        Ok(())
    }
}

/// Checks rows against the current milestone. Findings keep the rows' order.
pub fn gate<M: Ord + Debug>(rows: &[GateRow<'_, M>], current: &M) -> GateReport {
    gate_with(rows, current, None)
}

/// [`gate`], with `building` the milestone after `current`: a deferred row of that
/// milestone that passes is early, not stale. When `building` is not after
/// `current`, no row is deferred and early at once, so this is [`gate`].
pub fn gate_building<M: Ord + Debug>(
    rows: &[GateRow<'_, M>],
    current: &M,
    building: &M,
) -> GateReport {
    gate_with(rows, current, Some(building))
}

fn gate_with<M: Ord + Debug>(
    rows: &[GateRow<'_, M>],
    current: &M,
    building: Option<&M>,
) -> GateReport {
    let mut report = GateReport {
        current: format!("{current:?}"),
        ..GateReport::default()
    };
    let mut seen = BTreeSet::new();
    let mut repeated = BTreeSet::new();
    for row in rows {
        if !seen.insert(row.id) && repeated.insert(row.id) {
            report.duplicates.push(row.id.to_owned());
        }
        let finding = || GateFinding {
            id: row.id.to_owned(),
            since: format!("{:?}", row.since),
            fixture: row.fixture,
        };
        if row.since <= *current {
            report.enforced += 1;
            if row.fixture != FixtureStatus::Passing {
                report.gaps.push(finding());
            }
        } else {
            report.deferred += 1;
            if row.fixture == FixtureStatus::Passing {
                if building == Some(&row.since) {
                    report.early.push(finding());
                } else {
                    report.stale.push(finding());
                }
            }
        }
    }
    report
}

/// Checks document rows, given as `(id, since)`, against the IDs fixtures claim.
/// A claim counts as a passing fixture, and a claim naming no row is an orphan
/// whatever the milestone.
pub fn gate_covers<M: Ord + Debug + Clone>(
    rows: &[(&str, M)],
    covers: &[String],
    current: &M,
) -> GateReport {
    let claimed: BTreeSet<&str> = covers.iter().map(String::as_str).collect();
    let known: BTreeSet<&str> = rows.iter().map(|(id, _)| *id).collect();
    let gated: Vec<GateRow<'_, M>> = rows
        .iter()
        .map(|(id, since)| GateRow {
            id,
            since: since.clone(),
            fixture: if claimed.contains(id) {
                FixtureStatus::Passing
            } else {
                FixtureStatus::Missing
            },
        })
        .collect();
    let mut report = gate(&gated, current);
    report.orphans = claimed
        .difference(&known)
        .map(|id| (*id).to_owned())
        .collect();
    report
}
