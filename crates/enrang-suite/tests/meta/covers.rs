//! The document rows M2's gate asks fixtures for (TESTING 18 and 23, M2 plan g.4 to
//! g.6), over the anchored compile fixtures of `tests/compile/`:
//!
//! - every `C` row of SPEC 4.5 has an accept, a near-miss `<name>.pass.en` that
//!   passes `check` and claims the row with `//! covers: Cnn`, and a reject, a
//!   firing fixture `<name>.fail.en` that fires as its anchors say and claims the
//!   row too; a claim that names no row of any document family is an orphan;
//! - every clause of SPEC 4.4's exact-satisfaction rule has a firing fixture at
//!   `implements`, `tests/compile/EN0416/satisfy-<clause>.fail.en`, one at a bound,
//!   `tests/compile/EN0419/satisfy-<clause>.fail.en`, each anchoring the code of its
//!   directory, and a near-miss `satisfy-<clause>.pass.en` in either directory;
//! - every row of TESTING 18's three attack reviews whose first cell opens with a
//!   backticked ID and whose "Must give" cell names a code of phase 2, or EN0435,
//!   has a firing fixture named after the ID that anchors each such code, and a
//!   near-miss of that name when the row says that one of its programs compiles or
//!   prints.
//!
//! Each line of evidence takes the milestone of what it shows: a `C` row's is M2,
//! which types SPEC 4.5's coercions; a clause's or an attack row's line is its
//! code's `since`. So before the bump that closes M2 its evidence is early, never
//! stale, and its absence no gap, and once M2 is reached every line needs its
//! evidence (`gate_building`). The evidence is always a run of `enrang check`, and
//! the fake rows of the self-tests go through the same gate functions as the real
//! ones, so each case is shown to trip.
//!
//! TESTING 23's M3 row adds three gates (M3 plan f.5, f.8, f.10), each of whose lines
//! is M3's at the earliest, so before the bump that closed M3 their evidence was
//! early and its absence no gap, and since M3 is reached every line needs it:
//!
//! - the M3 view of the attack rows: the phase 3 codes, and EN0804, that an attack
//!   row names, and a near-miss for a row that says a program compiles or prints
//!   when the phase 2 view above gives it none, beside the phase 2 lines, which stay
//!   as they were, but the near-misses [`NEAR_MISS_LATER`] gives a later milestone,
//!   each with its reason; the reload scenarios of the reviews are none of these;
//! - the rows of the tables before the reviews, named fixtures, `for...of` and
//!   inferred permissions: each code of phase 2 or 3, EN0435 or EN0804 a row names
//!   needs a firing fixture of the row that anchors it, a row that says a program
//!   compiles or prints needs a near-miss of the row, and `f1`-`f6`, `h1`-`h8` and
//!   `l1`-`l10` need a fixture of the row per program, named after it. A fixture is
//!   the row's when it claims it with `//! row: <the first cell's opening>`, at least
//!   40 characters of it, or the whole cell, and so many that no other row's first
//!   cell opens with them, or, for a row whose first cell opens with IDs, when it
//!   claims no row and is named after one of them, as an attack row's fixture is.
//!   A `//! row:` line stands after the `//! target:` and `//! library` lines, which
//!   must open a fixture. The MIR-level rows, `` `.mir`: ... ``, are the mir and
//!   borrowck suites' `.mir` fixtures, and a row the attack review lists as beside
//!   the row it extends is an attack row, so neither is a row of this gate;
//! - every `H` row of SPEC 5.8, claimed by a fixture's `//! covers:` line that works,
//!   but the rows [`H_LATER`] gives a later milestone, each with its reason.
//!
//! A fixture of a row may be `<name>.fail.en` or `<name>-<n>.fail.en`, `<name>-2`
//! for a row's second firing program (M3 plan f.5), and a near-miss alike, unless
//! `<name>-<n>` names another row.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;

use enrang_diag::{CURRENT_MILESTONE, Code, Milestone, Phase};
use enrang_testkit::{
    FixtureStatus, GateFinding, GateReport, GateRow, Harness, ROW_FAMILIES, gate_building,
    gate_covers, parse_covers, workspace_root,
};

use crate::gating::{FakeCli, Run, fake_fixture, fixture_status};
use crate::support::{Fixture, Place, being_built, fixtures, gate_transcripts, read, run_cached};

/// The milestone of every `C` row: M2 types SPEC 4.5's coercions (TESTING 23).
const C_ROWS_SINCE: Milestone = Milestone::M2;

/// Where TESTING 18's three attack reviews begin and end.
pub const ATTACK_START: &str = "**The attack review of the applied design.**";
pub const ATTACK_END: &str = "**Hermeticity:**";

/// SPEC 4.4's exact-satisfaction rule as fixtures break it: each bullet of the rule's
/// list, by the words it opens with, and the clauses that each fail it.
const RULE: &[(&str, &[&str])] = &[
    ("It is public.", &["private", "protected"]),
    (
        "It has the same unsafety",
        &["unsafe-member", "unsafe-method"],
    ),
    ("It has no `@requires`.", &["requires"]),
    ("It is a method.", &["field"]),
    (
        "It has equal type parameters and bounds, equal parameter types and an equal return type.",
        &["type-params", "param-types", "return-type"],
    ),
];

/// The sentence before the rule's list that rules out auto-deref, and its clause: a
/// member found only through `Box`.
const DEREF: (&str, &[&str]) = ("auto-deref never contributes a member", &["box"]);

/// The codes a satisfaction clause fires, as M2 plan g.5 names their directories:
/// EN0416 at `implements`, EN0419 at a bound.
const SATISFY_CODES: [Code; 2] = [Code::EN0416, Code::EN0419];

/// Codes an attack row names that the row itself says phase 2 does not report: found
/// in a later phase, named only as a comparison, or named to say it does not fire. So
/// the gate asks no fixture to anchor it, and the row needs a near-miss instead (M2
/// plan g.6). Each must still name a code its row names, or reading fails. An entry
/// with an `until` milestone excuses the code only before it: from that milestone on,
/// the code is a line a firing fixture must show, as for a code found in a later
/// phase once that phase lands.
const NOT_FIRED: &[NotFired] = &[
    // EN0455 is named only to say why the fourth program compiles: "because EN0455
    // fires only where `Err` would also take the value as it is".
    ("EF-03", "EN0455", None),
    // EN0418 is "found in phase 3 once the flag is known": a firing fixture at M3,
    // whose plan turns the row's near-miss into one.
    ("S2-08-copy", "EN0418", Some(Milestone::M3)),
    // EN0435 is named only as another instance-dependent code: the row's own code
    // is EN0820, reported in phase 5.
    ("S2-32-lift", "EN0435", None),
    // "EN0701 once each, with no EN0454".
    ("EF-08", "EN0454", None),
    // "prints `view: [7, 7]` and `any: [7, 7, 7, 7] 4`, with no EN0401".
    ("VI-07-overloads", "EN0401", None),
];

/// An excused code of an attack row: the row's ID, the code, and the milestone from
/// which it is no longer excused, if any.
pub type NotFired = (&'static str, &'static str, Option<Milestone>);

/// A compile fixture, the row IDs its `//! covers:` lines claim, and the table rows
/// its `//! row:` lines claim.
#[derive(Clone, Debug)]
pub struct Claiming {
    pub fixture: Fixture,
    pub covers: Vec<String>,
    pub rows: Vec<String>,
}

/// The table rows a fixture claims with `//! row: <the opening of the first cell>`
/// lines, one claim a line, each trimmed. A `//! row:` line may stand anywhere after
/// the header lines `fixture_header` reads.
pub fn parse_row_claims(fixture: &str) -> Vec<String> {
    fixture
        .lines()
        .filter_map(|line| line.trim_start().strip_prefix("//! row:"))
        .map(str::trim)
        .map(str::to_owned)
        .collect()
}

/// What the gates look at: the fixtures, and the command line that runs them.
pub struct Evidence<'a> {
    pub fixtures: &'a [Claiming],
    pub run: &'a Run<'a>,
}

impl Evidence<'_> {
    /// The best status of the fixtures `pick` chooses, each weighed by `status`;
    /// `Missing` when it chooses none.
    fn best(
        &self,
        pick: impl Fn(&Claiming) -> bool,
        status: impl Fn(&Fixture) -> FixtureStatus,
    ) -> FixtureStatus {
        self.fixtures
            .iter()
            .filter(|claiming| pick(claiming))
            .map(|claiming| status(&claiming.fixture))
            .fold(FixtureStatus::Missing, FixtureStatus::best)
    }

    /// Whether a fixture does what its kind says.
    fn works(&self, fixture: &Fixture) -> FixtureStatus {
        fixture_status(fixture, self.run)
    }

    /// Whether a firing fixture shows `code`: it must anchor the code and fire.
    fn shows(&self, fixture: &Fixture, code: &str) -> FixtureStatus {
        if anchors_code(fixture, code) {
            self.works(fixture)
        } else {
            FixtureStatus::Failing
        }
    }
}

/// Whether a fixture's anchors, when they can be read, name `code`.
fn anchors_code(fixture: &Fixture, code: &str) -> bool {
    matches!(&fixture.anchors, Ok(anchors) if anchors.iter().any(|anchor| anchor.code == code))
}

/// A fixture's file name without `.fail.en` or `.pass.en`.
pub fn stem(fixture: &Fixture) -> &str {
    let name = fixture.path.rsplit('/').next().unwrap_or(&fixture.path);
    name.strip_suffix(".fail.en")
        .or_else(|| name.strip_suffix(".pass.en"))
        .unwrap_or(name)
}

/// Whether a fixture's stem names a row's fixture called `name`: `name` itself, or
/// `name-<n>`, a row's further program (M3 plan f.5). No row's name is another's
/// with `-<n>` ([`numbered_names`]), so this never takes another row's fixture.
pub fn stem_names(stem: &str, name: &str) -> bool {
    stem == name
        || stem
            .strip_prefix(name)
            .and_then(|rest| rest.strip_prefix('-'))
            .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
}

/// The names in `names` that are another one's with `-<n>`, each with that one, so
/// that [`stem_names`] would give a fixture of the first to the second too.
pub fn numbered_names(names: &[String]) -> Vec<(String, String)> {
    let mut found = Vec::new();
    for name in names {
        for other in names {
            if name != other && stem_names(name, other) {
                found.push((name.clone(), other.clone()));
            }
        }
    }
    found
}

/// One line of evidence: what it claims, its milestone and its status.
pub struct Line {
    pub id: String,
    pub since: Milestone,
    pub status: FixtureStatus,
}

/// Gates lines of evidence at `current`, the milestone after it being built: a line
/// of that milestone that passes is early, one later still is stale.
pub fn gate_lines(lines: &[Line], current: Milestone) -> GateReport {
    let rows: Vec<GateRow<'_, Milestone>> = lines
        .iter()
        .map(|line| GateRow {
            id: &line.id,
            since: line.since,
            fixture: line.status,
        })
        .collect();
    gate_building(&rows, &current, &being_built(current))
}

/// Gates the `C` rows, each `(id, since)`: a reached row needs a near-miss that
/// passes and a firing fixture that fires, both claiming it. A claim from any
/// fixture, passing or not, naming neither one of `rows` nor one of `known` (the
/// rows of the other document families, which their own gates check) is an orphan.
pub fn gate_c_rows(
    rows: &[(&str, Milestone)],
    known: &[&str],
    evidence: &Evidence<'_>,
    current: Milestone,
) -> GateReport {
    let mut lines = Vec::new();
    for &(id, since) in rows {
        for (word, near_miss) in [("accept", true), ("reject", false)] {
            let status = evidence.best(
                |claiming| {
                    claiming.fixture.near_miss == near_miss
                        && claiming.covers.iter().any(|claim| claim == id)
                },
                |fixture| evidence.works(fixture),
            );
            lines.push(Line {
                id: format!("{id} {word}"),
                since,
                status,
            });
        }
    }
    let mut report = gate_lines(&lines, current);
    let every: Vec<(&str, Milestone)> = rows
        .iter()
        .map(|(id, _)| *id)
        .chain(known.iter().copied())
        .map(|id| (id, current))
        .collect();
    let claims: Vec<String> = evidence
        .fixtures
        .iter()
        .flat_map(|claiming| claiming.covers.iter().cloned())
        .collect();
    report.orphans = gate_covers(&every, &claims, &current).orphans;
    report
}

/// Gates the clauses of SPEC 4.4's exact-satisfaction rule. For each clause and each
/// `(code, since)` of `fired`, `tests/compile/<code>/satisfy-<clause>.fail.en` must
/// anchor `code` and fire, and a near-miss `satisfy-<clause>.pass.en` in one of those
/// directories must pass, by the earliest of their milestones. A `satisfy-` fixture
/// there whose name is no clause is an orphan.
pub fn gate_clauses(
    clauses: &[&str],
    fired: &[(&str, Milestone)],
    evidence: &Evidence<'_>,
    current: Milestone,
) -> GateReport {
    let in_dirs = |fixture: &Fixture| fired.iter().any(|(code, _)| fixture.code == *code);
    let mut lines = Vec::new();
    for clause in clauses {
        let name = format!("satisfy-{clause}");
        for &(code, since) in fired {
            let status = evidence.best(
                |claiming| {
                    let fixture = &claiming.fixture;
                    !fixture.near_miss && fixture.code == code && stem(fixture) == name
                },
                |fixture| evidence.shows(fixture, code),
            );
            lines.push(Line {
                id: format!("{name} {code}"),
                since,
                status,
            });
        }
        if let Some(since) = fired.iter().map(|(_, since)| *since).min() {
            let status = evidence.best(
                |claiming| {
                    let fixture = &claiming.fixture;
                    fixture.near_miss && in_dirs(fixture) && stem(fixture) == name
                },
                |fixture| evidence.works(fixture),
            );
            lines.push(Line {
                id: format!("{name} near-miss"),
                since,
                status,
            });
        }
    }
    let mut report = gate_lines(&lines, current);
    let orphans: BTreeSet<String> = evidence
        .fixtures
        .iter()
        .map(|claiming| &claiming.fixture)
        .filter(|fixture| in_dirs(fixture))
        .filter_map(|fixture| {
            let clause = stem(fixture).strip_prefix("satisfy-")?;
            (!clauses.contains(&clause)).then(|| stem(fixture).to_owned())
        })
        .collect();
    report.orphans = orphans.into_iter().collect();
    report
}

/// A row of TESTING 18's attack reviews that names a code of phase 2, or EN0435.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct AttackRow {
    /// The IDs its first cell opens with; the first names the row's lines.
    pub ids: Vec<String>,
    /// The row's line in the document.
    pub line: usize,
    /// Each code a firing fixture of the row must anchor, with its milestone.
    pub fires: Vec<(String, Milestone)>,
    /// The milestone of the near-miss the row needs, when it says that a program of
    /// it compiles or prints, or names a code that phase 2 does not report.
    pub near_miss: Option<Milestone>,
}

/// The name of an attack row's fixtures: its ID lowercased, with every character
/// outside `[a-z0-9-]` replaced by `-` (M2 plan g.6), so `D20-core-1 both` is
/// `d20-core-1-both`.
pub fn slug(id: &str) -> String {
    id.chars()
        .map(|c| {
            let c = c.to_ascii_lowercase();
            if c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-' {
                c
            } else {
                '-'
            }
        })
        .collect()
}

/// The cells of a table row, split at pipes that are not escaped and trimmed.
pub fn row_cells(row: &str) -> Vec<String> {
    let mut cells = Vec::new();
    let mut cell = String::new();
    let mut escaped = false;
    for c in row.trim().chars() {
        if c == '|' && !escaped {
            cells.push(std::mem::take(&mut cell));
        } else {
            cell.push(c);
        }
        escaped = c == '\\' && !escaped;
    }
    cells.push(cell);
    // The pipes that open and close a row leave an empty cell at each end.
    if cells.first().is_some_and(|first| first.trim().is_empty()) {
        cells.remove(0);
    }
    if cells.last().is_some_and(|last| last.trim().is_empty()) {
        cells.pop();
    }
    cells.iter().map(|cell| cell.trim().to_owned()).collect()
}

/// The backticked IDs a first cell opens with, separated by `, ` and followed by
/// `:`, as in `` `INF-06`, `MR-6`: ``. An ID is letters, digits, `-` and spaces,
/// opening with a letter or digit. `None` when the cell opens otherwise.
pub fn leading_ids(cell: &str) -> Option<Vec<String>> {
    let mut ids = Vec::new();
    let mut rest = cell;
    loop {
        let (id, tail) = rest.strip_prefix('`')?.split_once('`')?;
        let shaped = id.starts_with(|c: char| c.is_ascii_alphanumeric())
            && id
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == ' ');
        if !shaped {
            return None;
        }
        ids.push(id.to_owned());
        if tail.starts_with(':') {
            return Some(ids);
        }
        rest = tail.strip_prefix(", ")?;
    }
}

/// The IDs the attack review's paragraph `line` lists as rows that sit beside the
/// rows they extend, in the tables above it: the backticked words of its
/// parenthesis after `sit beside it in the tables above`.
pub fn beside_ids(line: &str) -> BTreeSet<String> {
    let Some((_, after)) = line.split_once("sit beside it in the tables above (") else {
        return BTreeSet::new();
    };
    let list = after.split_once(')').map_or(after, |(list, _)| list);
    backticked(list).into_iter().collect()
}

/// The words a text writes between backticks, in order.
fn backticked(text: &str) -> Vec<String> {
    text.split('`')
        .skip(1)
        .step_by(2)
        .map(str::to_owned)
        .collect()
}

/// The codes a cell names, `EN` and four digits, sorted.
pub fn named_codes(cell: &str) -> BTreeSet<String> {
    let bytes = cell.as_bytes();
    let mut codes = BTreeSet::new();
    for (at, _) in cell.match_indices("EN") {
        let digits = bytes.get(at + 2..at + 6);
        let whole = digits.is_some_and(|digits| digits.iter().all(u8::is_ascii_digit))
            && !bytes.get(at + 6).is_some_and(u8::is_ascii_alphanumeric)
            && !(at > 0 && bytes[at - 1].is_ascii_alphanumeric());
        if whole {
            codes.insert(cell[at..at + 6].to_owned());
        }
    }
    codes
}

/// A cell's prose: its text with code spans and parenthesised asides, where twins
/// and other languages are quoted, left out.
fn prose(cell: &str) -> String {
    let chars: Vec<char> = cell.chars().collect();
    let mut text = String::new();
    let mut at = 0;
    while at < chars.len() {
        if chars[at] == '`' {
            let run = chars[at..].iter().take_while(|&&c| c == '`').count();
            // A code span closes at the next run of exactly as many backticks.
            let mut close = None;
            let mut look = at + run;
            while look < chars.len() {
                if chars[look] == '`' {
                    let other = chars[look..].iter().take_while(|&&c| c == '`').count();
                    if other == run {
                        close = Some(look + other);
                        break;
                    }
                    look += other;
                } else {
                    look += 1;
                }
            }
            match close {
                Some(end) => {
                    text.push_str(" code ");
                    at = end;
                }
                None => {
                    at += run;
                }
            }
            continue;
        }
        text.push(chars[at]);
        at += 1;
    }
    let mut depth = 0usize;
    let mut outside = String::new();
    for c in text.chars() {
        match c {
            '(' => depth += 1,
            ')' => depth = depth.saturating_sub(1),
            _ if depth == 0 => outside.push(c),
            _ => {}
        }
    }
    outside
}

/// Whether a "Must give" cell says, in its own prose, that a program compiles or
/// prints.
pub fn says_compiles(cell: &str) -> bool {
    prose(cell)
        .split(|c: char| !c.is_ascii_alphabetic())
        .any(|word| matches!(word, "compiles" | "Compiles" | "prints" | "Prints"))
}

/// [`says_compiles`] as M3's gates read a cell: the plural verbs too, `Compile and
/// print` said of a row's programs together, but not `compile time`. The phase 2
/// view keeps [`says_compiles`], so M3's reading adds no line due at M2.
pub fn says_compiles_m3(cell: &str) -> bool {
    let text = prose(cell);
    let words: Vec<&str> = text
        .split(|c: char| !c.is_ascii_alphabetic())
        .filter(|word| !word.is_empty())
        .collect();
    words.iter().enumerate().any(|(at, word)| match *word {
        "compiles" | "Compiles" | "prints" | "Prints" | "print" | "Print" => true,
        "compile" | "Compile" => words.get(at + 1) != Some(&"time"),
        _ => false,
    })
}

/// The attack rows of a TESTING document: those between [`ATTACK_START`] and
/// [`ATTACK_END`] whose first cell opens with a backtick and whose other cells name
/// a code `info` gates, as `Some((gated, since))`. A row whose first cell opens with
/// a backtick but no ID, a code `info` does not know, and an entry of `not_fired`
/// that names no gated code of a row with that ID are errors, so a reworded
/// document cannot drop a row unseen. An excused code still fires from its entry's
/// `until` milestone, or its own `since` if later. The rows of a table whose header
/// opens `| Scenario |` are reload scenarios, which declare `covers` for their
/// `DEV_RUNTIME.md` row and are no compile fixtures.
pub fn attack_rows(
    doc: &str,
    info: &dyn Fn(&str) -> Option<(bool, Milestone)>,
    not_fired: &[NotFired],
) -> Result<Vec<AttackRow>, String> {
    read_attack_rows(doc, info, not_fired, None)
}

/// [`attack_rows`] with every line due at `floor` at the earliest, and a near-miss,
/// due at `floor`, for a row that says a program compiles or prints though it names
/// no gated code: the rows as a later milestone's gate reads them.
pub fn attack_rows_from(
    doc: &str,
    info: &dyn Fn(&str) -> Option<(bool, Milestone)>,
    not_fired: &[NotFired],
    floor: Milestone,
) -> Result<Vec<AttackRow>, String> {
    read_attack_rows(doc, info, not_fired, Some(floor))
}

fn read_attack_rows(
    doc: &str,
    info: &dyn Fn(&str) -> Option<(bool, Milestone)>,
    not_fired: &[NotFired],
    floor: Option<Milestone>,
) -> Result<Vec<AttackRow>, String> {
    let lines: Vec<&str> = doc.lines().collect();
    let start = lines
        .iter()
        .position(|line| line.starts_with(ATTACK_START))
        .ok_or_else(|| format!("no line opens with {ATTACK_START}"))?;
    let end = lines[start..]
        .iter()
        .position(|line| line.starts_with(ATTACK_END))
        .map(|offset| start + offset)
        .ok_or_else(|| format!("no line after the attack reviews opens with {ATTACK_END}"))?;
    // The rows that extend an existing row sit beside it in the tables above, as
    // the review's paragraph lists them (`WD-4` at SPEC 11's limits among them):
    // they are attack rows too, wherever they stand.
    let beside = beside_ids(lines[start]);
    let floored = |since: Milestone| floor.map_or(since, |floor| since.max(floor));
    let mut rows = Vec::new();
    let mut used: BTreeSet<(&str, &str)> = BTreeSet::new();
    let mut scenarios = false;
    for (index, text) in lines.iter().enumerate().take(end) {
        let line = index + 1;
        if text.starts_with("| Scenario |") {
            scenarios = true;
        } else if text.starts_with("| Fixture |") {
            scenarios = false;
        }
        if !text.starts_with("| ") || scenarios {
            continue;
        }
        let cells = row_cells(text);
        let ids = if index < start {
            let named: Vec<String> = backticked(&cells[0])
                .into_iter()
                .filter(|id| beside.contains(id))
                .collect();
            if named.is_empty() {
                continue;
            }
            named
        } else if text.starts_with("| `") {
            leading_ids(&cells[0])
                .ok_or_else(|| format!("line {line}: the first cell opens with no ID"))?
        } else {
            continue;
        };
        let must = cells[1..].join(" | ");
        let mut fires = Vec::new();
        let mut earliest: Option<Milestone> = None;
        let mut near_miss = if floor.is_some() {
            says_compiles_m3(&must)
        } else {
            says_compiles(&must)
        };
        for code in named_codes(&must) {
            let (gated, since) =
                info(&code).ok_or_else(|| format!("line {line}: {code} is no code"))?;
            if !gated {
                continue;
            }
            let since = floored(since);
            earliest = Some(earliest.map_or(since, |first| first.min(since)));
            let excused = not_fired
                .iter()
                .find(|(id, excused, _)| *excused == code && ids.iter().any(|own| own == id));
            if let Some(&(id, excused, until)) = excused {
                used.insert((id, excused));
                near_miss = true;
                if let Some(until) = until {
                    fires.push((code, since.max(until)));
                }
            } else {
                fires.push((code, since));
            }
        }
        let earliest = match (earliest, floor) {
            (Some(earliest), _) => earliest,
            (None, Some(floor)) if near_miss => floor,
            (None, _) => continue,
        };
        rows.push(AttackRow {
            ids,
            line,
            fires,
            near_miss: near_miss.then_some(earliest),
        });
    }
    if let Some((id, code, _)) = not_fired
        .iter()
        .find(|(id, code, _)| !used.contains(&(*id, *code)))
    {
        return Err(format!("no attack row {id} names the gated code {code}"));
    }
    Ok(rows)
}

/// The lines `later` adds to `earlier`, two readings of the same attack rows: each
/// row's codes the earlier reading does not fire, and its near-miss when the
/// earlier gives it none. A row left with nothing is dropped.
pub fn added_rows(earlier: &[AttackRow], later: &[AttackRow]) -> Vec<AttackRow> {
    later
        .iter()
        .filter_map(|row| {
            let before = earlier
                .iter()
                .find(|old| old.ids[0] == row.ids[0] && old.line == row.line);
            let fires: Vec<(String, Milestone)> = row
                .fires
                .iter()
                .filter(|(code, _)| {
                    !before.is_some_and(|old| old.fires.iter().any(|(had, _)| had == code))
                })
                .cloned()
                .collect();
            let near_miss = row
                .near_miss
                .filter(|_| !before.is_some_and(|old| old.near_miss.is_some()));
            (!fires.is_empty() || near_miss.is_some()).then(|| AttackRow {
                ids: row.ids.clone(),
                line: row.line,
                fires,
                near_miss,
            })
        })
        .collect()
}

/// The excuses of `not_fired` that a firing fixture named after their row anchors:
/// a row's own fixture showing the code says it fires, so excusing it would turn
/// that firing line into a near-miss line unseen.
pub fn anchored_excuses(not_fired: &[NotFired], fixtures: &[Claiming]) -> Vec<String> {
    not_fired
        .iter()
        // An excuse that ends at a milestone expects the row's own fixture to anchor
        // the code from then on, so one that lands early is no conflict (S2-08-copy).
        .filter(|(_, _, until)| until.is_none())
        .flat_map(|&(id, code, _)| {
            let name = slug(id);
            fixtures
                .iter()
                .map(|claiming| &claiming.fixture)
                .filter(move |fixture| {
                    !fixture.near_miss && stem(fixture) == name && anchors_code(fixture, code)
                })
                .map(move |fixture| format!("{id} excuses {code}, which {} anchors", fixture.path))
        })
        .collect()
}

/// Whether a fixture is named after one of `names`, the slugs of a row's IDs, and
/// claims no table row: a fixture that claims a row is that row's alone, so a
/// program named `f1` of `f1`-`f6` is no fixture of the attack row `F1`.
fn named_after(claiming: &Claiming, names: &BTreeSet<String>) -> bool {
    claiming.rows.is_empty()
        && names
            .iter()
            .any(|name| stem_names(stem(&claiming.fixture), name))
}

/// Gates attack rows: each code a row fires needs a firing fixture, named after one
/// of the row's IDs, that anchors the code and fires; a fixture of that name in the
/// code's directory that does not anchor it is a failing one. A row that needs a
/// near-miss needs one of that name that passes.
pub fn gate_attack(rows: &[AttackRow], evidence: &Evidence<'_>, current: Milestone) -> GateReport {
    gate_lines(&attack_lines(rows, evidence, &|_, _| false), current)
}

/// The lines of [`gate_attack`], each with its status. `claims` says whether a
/// fixture claims the row at a line of the document with `//! row:`, which a row of
/// the tables before the reviews that the review lists as beside the row it extends
/// can be: such a fixture is the row's too, whatever its name.
fn attack_lines(
    rows: &[AttackRow],
    evidence: &Evidence<'_>,
    claims: &dyn Fn(&Claiming, usize) -> bool,
) -> Vec<Line> {
    let mut lines = Vec::new();
    for row in rows {
        let names: BTreeSet<String> = row.ids.iter().map(|id| slug(id)).collect();
        let first = &row.ids[0];
        let ours =
            |claiming: &Claiming| named_after(claiming, &names) || claims(claiming, row.line);
        for (code, since) in &row.fires {
            let status = evidence.best(
                |claiming| {
                    let fixture = &claiming.fixture;
                    !fixture.near_miss
                        && ours(claiming)
                        && (fixture.code == *code || anchors_code(fixture, code))
                },
                |fixture| evidence.shows(fixture, code),
            );
            lines.push(Line {
                id: format!("{first} {code}"),
                since: *since,
                status,
            });
        }
        if let Some(since) = row.near_miss {
            let status = evidence.best(
                |claiming| claiming.fixture.near_miss && ours(claiming),
                |fixture| evidence.works(fixture),
            );
            lines.push(Line {
                id: format!("{first} near-miss"),
                since,
                status,
            });
        }
    }
    lines
}

/// Where TESTING 18's tables before the attack reviews begin: named fixtures, then
/// `for...of` and array spread, then inferred permissions, up to [`ATTACK_START`].
pub const TABLES_START: &str = "**Named fixtures.**";

/// How many characters of a first cell a `//! row:` claim holds at the least, unless
/// it holds the whole cell (M3 plan f.5).
pub const CLAIM_LEAST: usize = 40;

/// A row of the tables before the attack reviews, as their gate reads it.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TableRow {
    /// The row's line in the document.
    pub line: usize,
    /// Its place among the data rows of the tables ([`table_cells`]).
    pub at: usize,
    /// Its first cell, as written.
    pub cell: String,
    /// The IDs the first cell opens with ([`table_ids`]), which name its fixtures as
    /// an attack row's do; empty when it opens with none.
    pub ids: Vec<String>,
    /// What its lines are called: its first ID, or the shortest claim that names it.
    pub label: String,
    /// Each code a firing fixture of the row must anchor, with its milestone.
    pub fires: Vec<(String, Milestone)>,
    /// The milestone of the near-miss the row needs, if it needs one.
    pub near_miss: Option<Milestone>,
    /// The programs a numbered row lists, `f1` to `f6`, each needing a fixture of
    /// the row named after it, due at the gate's floor.
    pub programs: Vec<(String, Milestone)>,
}

/// An excused code of a table row (as [`NotFired`]): the row, by an ID its first cell
/// opens with or by the opening of that cell, the code it names only to say that it
/// does not fire, and whether that says a program of the row compiles, so the row
/// needs a near-miss though it says no `compiles` of its own.
pub type TableExcuse = (&'static str, &'static str, bool);

/// Codes a row of the tables names only to say they do not fire, or as what another
/// program would give.
const TABLE_NOT_FIRED: &[TableExcuse] = &[
    // "is that EN0615 in phase 3, never EN0401, because phase-2 type identity
    // ignores rows".
    ("A reading function where", "EN0401", false),
    // "since the `Hold`'s EN0706 in both columns is kept for accesses that change the
    // held source": named to say why the row's loops give EN0707 and EN0708.
    ("LTK-4", "EN0706", false),
    // "No EN0613: each turn binds a new `x`": the binding compiles.
    ("A `const` binding over many turns", "EN0613", true),
    // "EN0706, `cannot reassign `xs` during iteration`, each; no EN0711".
    (
        "`xs = []` in the body of a loop over `&xs`",
        "EN0711",
        false,
    ),
    // "so `console.log(r, q)` would read `q` under it, EN0708": the reason the two
    // reads are separate statements.
    ("TK-02-reassign-break", "EN0708", false),
    // "No EN0401, because the source is evaluated once".
    (
        "Under `o != null`: `for (const x of o.kids())",
        "EN0401",
        false,
    ),
    // "and never give EN0708".
    ("S2-24-narrowed", "EN0708", false),
    // "EN1013 at `...`, and no EN1010, EN1042 or EN0114".
    ("Deferred forms:", "EN1042", false),
    // "EN0412 with the note, before any EN0401": named only to say EN0412 comes
    // first; every spreading form gives EN0412 alone.
    ("`private const Y = [...X];`", "EN0401", false),
];

/// Whether a table row is a MIR-level fixture, `` `.mir`: ... ``, which the mir and
/// borrowck suites hold as `.mir` text (M3 plan f.1), and no compile fixture shows.
pub fn mir_level(cell: &str) -> bool {
    cell.starts_with("`.mir`:")
}

/// The IDs a table row's first cell opens with: backticked words of letters, digits
/// and `-`, opening with a letter and holding a digit or a `-`, separated by `, `,
/// the last followed by `:` or by `, ` and prose. So `` `h06`, the longest-word
/// loop `` names `h06`, while `` `Atomic64` at `i486` ``, `` `unsafe`, `@requires` ``
/// and `` `f1`-`f6` `` name none.
pub fn table_ids(cell: &str) -> Vec<String> {
    let shaped = |id: &str| {
        id.starts_with(|c: char| c.is_ascii_alphabetic())
            && id.chars().all(|c| c.is_ascii_alphanumeric() || c == '-')
            && id.chars().any(|c| c.is_ascii_digit() || c == '-')
    };
    let mut ids = Vec::new();
    let mut rest = cell;
    loop {
        let Some((id, tail)) = rest.strip_prefix('`').and_then(|r| r.split_once('`')) else {
            return Vec::new();
        };
        if !shaped(id) {
            return Vec::new();
        }
        if tail.starts_with(':') {
            ids.push(id.to_owned());
            return ids;
        }
        let Some(after) = tail.strip_prefix(", ") else {
            return Vec::new();
        };
        ids.push(id.to_owned());
        if !after.starts_with('`') {
            return ids;
        }
        rest = after;
    }
}

/// The programs a first cell that opens `` `f1`-`f6`, `` numbers: `f1` to `f6`.
pub fn numbered_programs(cell: &str) -> Vec<String> {
    let parse = |part: &str| {
        let letters: String = part.chars().take_while(char::is_ascii_lowercase).collect();
        let digits = &part[letters.len()..];
        let number: Option<u32> = digits.parse().ok();
        (!letters.is_empty() && !digits.starts_with('0'))
            .then_some(number)
            .flatten()
            .map(|number| (letters, number))
    };
    let Some(rest) = cell.strip_prefix('`') else {
        return Vec::new();
    };
    let Some((first, rest)) = rest.split_once("`-`") else {
        return Vec::new();
    };
    let Some((last, rest)) = rest.split_once('`') else {
        return Vec::new();
    };
    if !rest.starts_with(',') {
        return Vec::new();
    }
    match (parse(first), parse(last)) {
        (Some((a, from)), Some((b, to))) if a == b && from < to => {
            (from..=to).map(|n| format!("{a}{n}")).collect()
        }
        _ => Vec::new(),
    }
}

/// A first cell, or a claim, as compared: `\|` read as `|`, trimmed.
fn claim_text(text: &str) -> String {
    text.replace("\\|", "|").trim().to_owned()
}

/// Whether `claim` names a row whose first cell is `cell`: the cell opens with it,
/// and it is at least [`CLAIM_LEAST`] characters long or the whole cell.
pub fn claim_fits(claim: &str, cell: &str) -> bool {
    let (claim, cell) = (claim_text(claim), claim_text(cell));
    if claim.is_empty() || !cell.starts_with(&claim) {
        return false;
    }
    // A claim's trailing spaces are lost to a trimmed line, so the spaces that
    // follow it in the cell count towards its length.
    let spaces = cell[claim.len()..]
        .chars()
        .take_while(|c| c.is_whitespace())
        .count();
    claim == cell || claim.chars().count() + spaces >= CLAIM_LEAST
}

/// The one row of `cells` that `claim` names, by index, or why it names none.
pub fn claimed_row(claim: &str, cells: &[String]) -> Result<usize, String> {
    let fits: Vec<usize> = (0..cells.len())
        .filter(|&at| claim_fits(claim, &cells[at]))
        .collect();
    match fits[..] {
        [one] => Ok(one),
        [] => Err(format!("`row: {claim}` names no row of the tables")),
        _ => Err(format!(
            "`row: {claim}` names {} rows of the tables; claim more of the first cell",
            fits.len()
        )),
    }
}

/// The shortest claim that names the row of `cells` at `at`: at least
/// [`CLAIM_LEAST`] characters of its first cell, as written, or the whole cell.
pub fn shortest_claim(cells: &[String], at: usize) -> String {
    let cell: Vec<char> = cells[at].trim().chars().collect();
    let mut length = CLAIM_LEAST.min(cell.len());
    loop {
        let claim: String = cell[..length].iter().collect();
        if length == cell.len() || claimed_row(&claim, cells).is_ok() {
            return claim;
        }
        length += 1;
    }
}

/// The data rows of the tables before the attack reviews, each with its line and
/// cells, the header rows left out.
fn table_lines(doc: &str) -> Result<Vec<(usize, Vec<String>)>, String> {
    let lines: Vec<&str> = doc.lines().collect();
    let start = lines
        .iter()
        .position(|line| line.starts_with(TABLES_START))
        .ok_or_else(|| format!("no line opens with {TABLES_START}"))?;
    let end = lines[start..]
        .iter()
        .position(|line| line.starts_with(ATTACK_START))
        .map(|offset| start + offset)
        .ok_or_else(|| format!("no line after the tables opens with {ATTACK_START}"))?;
    Ok((start..end)
        .filter(|&index| lines[index].starts_with("| "))
        .filter(|&index| {
            !lines
                .get(index + 1)
                .is_some_and(|next| next.starts_with("|-"))
        })
        .map(|index| (index + 1, row_cells(lines[index])))
        .collect())
}

/// Each data row of the tables by its line in the document, with its place among
/// [`table_cells`].
pub fn table_places(doc: &str) -> Result<BTreeMap<usize, usize>, String> {
    Ok(table_lines(doc)?
        .into_iter()
        .enumerate()
        .map(|(at, (line, _))| (line, at))
        .collect())
}

/// The first cells of every data row of the tables, the rows a claim may name.
pub fn table_cells(doc: &str) -> Result<Vec<String>, String> {
    Ok(table_lines(doc)?
        .into_iter()
        .map(|(_, cells)| cells[0].clone())
        .collect())
}

/// The rows of the tables before the attack reviews that the gate asks fixtures for,
/// read as [`attack_rows`] reads the reviews: each code `info` gates is a firing line
/// due at `floor` at the earliest, unless `not_fired` excuses it, and a row that says
/// a program compiles or prints, or whose excuse says so, needs a near-miss due at
/// `floor`; a numbered row needs a fixture per program. A row the attack review
/// lists as beside the row it extends is an attack row, and a MIR-level row
/// ([`mir_level`]) is the mir and borrowck suites', so neither is a row here. A code
/// `info` does not know, and an excuse that names no row, or several, or a code its
/// row does not gate, are errors.
pub fn table_rows(
    doc: &str,
    info: &dyn Fn(&str) -> Option<(bool, Milestone)>,
    not_fired: &[TableExcuse],
    floor: Milestone,
) -> Result<Vec<TableRow>, String> {
    let beside = doc
        .lines()
        .find(|line| line.starts_with(ATTACK_START))
        .map(beside_ids)
        .unwrap_or_default();
    let read = table_lines(doc)?;
    let cells: Vec<String> = read.iter().map(|(_, cells)| cells[0].clone()).collect();
    let excused_row = |key: &str, cell: &str| {
        table_ids(cell).iter().any(|id| id == key) || claim_text(cell).starts_with(&claim_text(key))
    };
    for (key, code, _) in not_fired {
        let named: Vec<&(usize, Vec<String>)> = read
            .iter()
            .filter(|(_, row)| excused_row(key, &row[0]))
            .collect();
        let [(line, row)] = named[..] else {
            return Err(format!("the excuse {key:?} names {} rows", named.len()));
        };
        let gates = named_codes(&row[1..].join(" | "))
            .into_iter()
            .any(|named| named == *code && info(&named).is_some_and(|(gated, _)| gated));
        if !gates {
            return Err(format!("line {line}: the row {key:?} gates no {code}"));
        }
    }
    let mut rows = Vec::new();
    for (at, (line, row)) in read.iter().enumerate() {
        if mir_level(&row[0]) || backticked(&row[0]).iter().any(|id| beside.contains(id)) {
            continue;
        }
        let must = row[1..].join(" | ");
        let mut fires = Vec::new();
        let mut near_miss = says_compiles_m3(&must);
        for code in named_codes(&must) {
            let (gated, since) =
                info(&code).ok_or_else(|| format!("line {line}: {code} is no code"))?;
            if !gated {
                continue;
            }
            let excused = not_fired
                .iter()
                .find(|(key, excused, _)| *excused == code && excused_row(key, &row[0]));
            match excused {
                Some((_, _, compiles)) => near_miss |= compiles,
                None => fires.push((code, since.max(floor))),
            }
        }
        let programs: Vec<(String, Milestone)> = numbered_programs(&row[0])
            .into_iter()
            .map(|program| (program, floor))
            .collect();
        if fires.is_empty() && !near_miss && programs.is_empty() {
            continue;
        }
        let ids = table_ids(&row[0]);
        let label = ids
            .first()
            .cloned()
            .unwrap_or_else(|| shortest_claim(&cells, at));
        rows.push(TableRow {
            line: *line,
            at,
            cell: row[0].clone(),
            ids,
            label,
            fires,
            near_miss: near_miss.then_some(floor),
            programs,
        });
    }
    Ok(rows)
}

/// The table rows each fixture claims, by path, as places among `cells`: a claim
/// that names no single row names none here ([`claim_problems`] reports it).
pub type Claims = BTreeMap<String, BTreeSet<usize>>;

/// [`Claims`] of `fixtures` over the first cells `cells`, each claim resolved once.
pub fn resolve_claims(fixtures: &[Claiming], cells: &[String]) -> Claims {
    fixtures
        .iter()
        .filter(|claiming| !claiming.rows.is_empty())
        .map(|claiming| {
            let rows = claiming
                .rows
                .iter()
                .filter_map(|claim| claimed_row(claim, cells).ok())
                .collect();
            (claiming.fixture.path.clone(), rows)
        })
        .collect()
}

/// Whether a fixture claims the table row at `at`.
fn claims_at(claims: &Claims, claiming: &Claiming, at: usize) -> bool {
    claims
        .get(&claiming.fixture.path)
        .is_some_and(|rows| rows.contains(&at))
}

/// Whether a fixture is the table row's: it claims the row, or it claims none and is
/// named after one of the row's IDs.
fn of_table_row(claiming: &Claiming, row: &TableRow, claims: &Claims) -> bool {
    let names: BTreeSet<String> = row.ids.iter().map(|id| slug(id)).collect();
    claims_at(claims, claiming, row.at) || named_after(claiming, &names)
}

/// The lines of [`gate_tables`], each with its status.
fn table_row_lines(rows: &[TableRow], cells: &[String], evidence: &Evidence<'_>) -> Vec<Line> {
    let claims = resolve_claims(evidence.fixtures, cells);
    let mut lines = Vec::new();
    for row in rows {
        let at = row.at;
        let ours = |claiming: &Claiming| of_table_row(claiming, row, &claims);
        for (code, since) in &row.fires {
            let status = evidence.best(
                |claiming| {
                    let fixture = &claiming.fixture;
                    !fixture.near_miss
                        && ours(claiming)
                        && (fixture.code == *code || anchors_code(fixture, code))
                },
                |fixture| evidence.shows(fixture, code),
            );
            lines.push(Line {
                id: format!("{} {code}", row.label),
                since: *since,
                status,
            });
        }
        if let Some(since) = row.near_miss {
            let status = evidence.best(
                |claiming| claiming.fixture.near_miss && ours(claiming),
                |fixture| evidence.works(fixture),
            );
            lines.push(Line {
                id: format!("{} near-miss", row.label),
                since,
                status,
            });
        }
        for (program, since) in &row.programs {
            let status = evidence.best(
                |claiming| {
                    claims_at(&claims, claiming, at) && stem_names(stem(&claiming.fixture), program)
                },
                |fixture| evidence.works(fixture),
            );
            lines.push(Line {
                id: format!("{} program {program}", row.label),
                since: *since,
                status,
            });
        }
    }
    lines
}

/// Gates the table rows `rows`, `cells` being the first cells of every row of the
/// tables: each firing line needs a firing fixture of the row that anchors the code
/// and fires, a near-miss line a near-miss of the row that passes, and a program a
/// fixture of either kind that claims the row, is named after the program and
/// works.
pub fn gate_tables(
    rows: &[TableRow],
    cells: &[String],
    evidence: &Evidence<'_>,
    current: Milestone,
) -> GateReport {
    gate_lines(&table_row_lines(rows, cells, evidence), current)
}

/// What is wrong with the `//! row:` claims of `fixtures`: each must name exactly one
/// row of the tables whose first cells are `cells`.
pub fn claim_problems(fixtures: &[Claiming], cells: &[String]) -> Vec<String> {
    fixtures
        .iter()
        .flat_map(|claiming| {
            claiming.rows.iter().filter_map(|claim| {
                claimed_row(claim, cells)
                    .err()
                    .map(|why| format!("{}: {why}", claiming.fixture.path))
            })
        })
        .collect()
}

// ---------------------------------------------------------------------------------
// SPEC 5.8's `H` rows.

/// The `H` rows whose mechanism no M3 phase has, each with the milestone that brings
/// it and why (M3 plan f.8): every other `H` row is an M3 line.
pub const H_LATER: &[(&str, Milestone, &str)] = &[
    (
        "H09",
        Milestone::M5,
        "descending stack probes and limit checks are code generation",
    ),
    (
        "H13",
        Milestone::M9,
        "EN0824, the allocator re-entered from an interrupt or a panic",
    ),
    (
        "H15",
        Milestone::M4,
        "`pushByte` panics at run time, in the VM",
    ),
    (
        "H17",
        Milestone::M5,
        "the caller's temporary elided under ARCHITECTURE 7.6's rule",
    ),
    (
        "H25",
        Milestone::M4,
        "`push` panics `capacity overflow` at run time, in the VM",
    ),
    (
        "H35",
        Milestone::M4,
        "a recheck or a load of a module with no source",
    ),
];

/// Each `H` row's line: due at its [`H_LATER`] milestone, or at `floor`. An excuse
/// that names no row, or a milestone not after `floor`, is an error.
pub fn h_lines_due(
    ids: &[String],
    later: &[(&str, Milestone, &str)],
    floor: Milestone,
) -> Result<Vec<(String, Milestone)>, String> {
    for (id, milestone, _) in later {
        if !ids.iter().any(|row| row == id) {
            return Err(format!("H_LATER names {id}, which is no H row"));
        }
        if *milestone <= floor {
            return Err(format!(
                "H_LATER gives {id} {milestone}, which is not after {floor}"
            ));
        }
    }
    Ok(ids
        .iter()
        .map(|id| {
            let since = later
                .iter()
                .find(|(row, _, _)| row == id)
                .map_or(floor, |(_, milestone, _)| *milestone);
            (id.clone(), since)
        })
        .collect())
}

/// The lines of [`gate_h_rows`], each with its status.
fn h_row_lines(due: &[(String, Milestone)], evidence: &Evidence<'_>) -> Vec<Line> {
    due.iter()
        .map(|(id, since)| Line {
            id: format!("{id} covered"),
            since: *since,
            status: evidence.best(
                |claiming| claiming.covers.iter().any(|claim| claim == id),
                |fixture| evidence.works(fixture),
            ),
        })
        .collect()
}

/// Gates the `H` rows: each needs a fixture of either kind that claims it with
/// `//! covers:` and works.
pub fn gate_h_rows(
    due: &[(String, Milestone)],
    evidence: &Evidence<'_>,
    current: Milestone,
) -> GateReport {
    gate_lines(&h_row_lines(due, evidence), current)
}

/// The clauses of SPEC 4.4's rule, one per way to break it, in the rule's order.
pub fn clauses() -> Vec<&'static str> {
    RULE.iter()
        .chain([&DEREF])
        .flat_map(|(_, clauses)| clauses.iter().copied())
        .collect()
}

/// Where SPEC 4.4's text differs from the rule [`RULE`] and [`DEREF`] read: its
/// bullet list must be exactly `RULE`'s bullets, in order, and the text before the
/// list must say `DEREF`'s words.
pub fn rule_differences(spec: &str) -> Vec<String> {
    let Some(start) = spec.find("\n### 4.4 Interfaces\n") else {
        return vec!["no `### 4.4 Interfaces`".to_owned()];
    };
    let section = &spec[start + 1..];
    let end = section[4..]
        .find("\n#")
        .map_or(section.len(), |offset| offset + 4);
    let section = &section[..end];
    let lines: Vec<&str> = section.lines().collect();
    let first = lines.iter().position(|line| line.starts_with("- "));
    let before = first.map_or(&lines[..], |first| &lines[..first]).join("\n");
    let bullets: Vec<&str> = first.map_or(Vec::new(), |first| {
        lines[first..]
            .iter()
            .take_while(|line| line.starts_with("- "))
            .copied()
            .collect()
    });
    let mut differences = Vec::new();
    if !before.contains(DEREF.0) {
        differences.push(format!("the text before the list lacks {:?}", DEREF.0));
    }
    if bullets.len() != RULE.len() {
        differences.push(format!(
            "the rule has {} bullets, not {}",
            bullets.len(),
            RULE.len()
        ));
    }
    for (bullet, (opening, _)) in bullets.iter().zip(RULE) {
        if !bullet.trim_start_matches("- ").starts_with(opening) {
            differences.push(format!("{bullet:?} does not open with {opening:?}"));
        }
    }
    differences
}

/// Whether a code's fixtures are gated as an attack row's: a code of phase 2, or
/// EN0435, the layout code `check` reports in phase 4 (M2 plan g.6).
fn gated(code: Code) -> bool {
    code.phase() == Phase::Types || code == Code::EN0435
}

fn registry_info(name: &str) -> Option<(bool, Milestone)> {
    Code::from_name(name).map(|code| (gated(code), code.since()))
}

/// The milestone of every line TESTING 23's M3 row adds: the M3 view of the attack
/// rows, the rows of the tables before them and the `H` rows.
pub const M3_LINES_SINCE: Milestone = Milestone::M3;

/// Whether a code's fixtures are gated in M3's reading of TESTING 18: a code of
/// phase 2 or 3, or EN0435 or EN0804, which `check` reports in phase 4 (M3 plan
/// f.10).
fn gated_m3(code: Code) -> bool {
    matches!(code.phase(), Phase::Types | Phase::Borrows)
        || code == Code::EN0435
        || code == Code::EN0804
}

fn registry_info_m3(name: &str) -> Option<(bool, Milestone)> {
    Code::from_name(name).map(|code| (gated_m3(code), code.since()))
}

/// Codes an attack row names, in M3's reading, only to say they do not fire (as
/// [`NOT_FIRED`], which M3's reading keeps).
const NOT_FIRED_M3: &[NotFired] = &[
    // "EN0714 once, at the `return`, with the declaring member as the secondary span;
    // no EN0615": a row of the named fixtures the review lists as beside the row it
    // extends.
    ("INF-11", "EN0615", None),
    // "with the help to declare it `let lib`; no EN0614, because `book` does not
    // change the library".
    ("INF-12", "EN0614", None),
    // "stays writable and `c.step()` is no EN0614".
    ("FV-02-alias-other", "EN0614", None),
    // "EN0707 at `k.push(4)`, not EN0706".
    ("FV-05-pad-flag", "EN0706", None),
    // "`sub.next()`, which writes `sub.pos`, is no EN0614".
    ("BC-08-readonly", "EN0614", None),
    // "where counting `c` as write-live made that loan exclusive, EN0608 at
    // `&table`": the reading the row replaced; its program compiles.
    ("FV-02-class-writelive", "EN0608", None),
    // "made the write, or the later `c.retarget(c.peek())`, EN0616": the reading
    // the row replaced; both its programs compile.
    ("FV-02-whole-write", "EN0616", None),
    // "EN0707 at `o.push(3)` for one parameter order and none for the other": the
    // reading the row replaced; its first two programs compile.
    ("FV-02-store-snapshot", "EN0707", None),
    // "which `FV-02-alias`'s rows, whose `return` is EN0709 as well, cannot show":
    // the row's own program gives EN0616 "and nothing else".
    ("FV-02-alias-peek", "EN0709", None),
    // "as EN0615's help asks": the row's first program compiles, and its second is
    // EN0214, a phase 1 code.
    ("RR-05", "EN0615", None),
    // "so the two-token form of `INF-08` stays EN0707": the row's own programs
    // are EN0701, a phase 2 code.
    ("RR-06", "EN0707", None),
];

/// The real compile fixtures, each with its claims.
fn real_fixtures() -> Vec<Claiming> {
    fixtures()
        .into_iter()
        .map(|fixture| {
            let bytes = fs::read(workspace_root().join(&fixture.path)).expect("a fixture");
            let text = String::from_utf8_lossy(&bytes);
            Claiming {
                covers: parse_covers(&text),
                rows: parse_row_claims(&text),
                fixture,
            }
        })
        .collect()
}

/// The rows of the document family with this prefix.
fn family_rows(prefix: &str) -> Vec<String> {
    let family = ROW_FAMILIES
        .iter()
        .find(|family| family.prefix == prefix)
        .unwrap_or_else(|| panic!("no family {prefix}"));
    family
        .extract(&read(family.doc))
        .unwrap_or_else(|error| panic!("{}: {error}", family.doc))
        .into_iter()
        .map(|row| row.id)
        .collect()
}

fn real_c_report(current: Milestone) -> GateReport {
    let c_rows = family_rows("C");
    let rows: Vec<(&str, Milestone)> = c_rows
        .iter()
        .map(|id| (id.as_str(), C_ROWS_SINCE))
        .collect();
    let others: Vec<String> = ROW_FAMILIES
        .iter()
        .filter(|family| family.prefix != "C")
        .flat_map(|family| family_rows(family.prefix))
        .collect();
    let known: Vec<&str> = others.iter().map(String::as_str).collect();
    let fixtures = real_fixtures();
    let evidence = Evidence {
        fixtures: &fixtures,
        run: &run_cached,
    };
    gate_c_rows(&rows, &known, &evidence, current)
}

fn real_clause_report(current: Milestone) -> GateReport {
    let fired: Vec<(&str, Milestone)> = SATISFY_CODES
        .iter()
        .map(|code| (code.name(), code.since()))
        .collect();
    let fixtures = real_fixtures();
    let evidence = Evidence {
        fixtures: &fixtures,
        run: &run_cached,
    };
    gate_clauses(&clauses(), &fired, &evidence, current)
}

fn real_attack_rows() -> Vec<AttackRow> {
    attack_rows(&read("docs/TESTING.md"), &registry_info, NOT_FIRED)
        .unwrap_or_else(|error| panic!("TESTING 18: {error}"))
}

fn real_attack_report(current: Milestone) -> GateReport {
    let fixtures = real_fixtures();
    let evidence = Evidence {
        fixtures: &fixtures,
        run: &run_cached,
    };
    gate_attack(&real_attack_rows(), &evidence, current)
}

/// M3's reading of TESTING 18's attack rows: the lines it adds to [`real_attack_rows`],
/// each near-miss of [`NEAR_MISS_LATER`] due at its own milestone.
fn real_attack_rows_m3() -> Vec<AttackRow> {
    let doc = read("docs/TESTING.md");
    let excuses: Vec<NotFired> = NOT_FIRED.iter().chain(NOT_FIRED_M3).copied().collect();
    let later = attack_rows_from(&doc, &registry_info_m3, &excuses, M3_LINES_SINCE)
        .unwrap_or_else(|error| panic!("TESTING 18, M3's reading: {error}"));
    defer_near_misses(
        added_rows(&real_attack_rows(), &later),
        NEAR_MISS_LATER,
        M3_LINES_SINCE,
    )
    .unwrap_or_else(|error| panic!("TESTING 18, M3's reading: {error}"))
}

/// The attack rows whose near-miss no compile fixture can show before a later
/// milestone, each with that milestone and why: the near-miss line is due then.
pub const NEAR_MISS_LATER: &[(&str, Milestone, &str)] = &[(
    "V-ME-10-err",
    Milestone::M4,
    "its programs are tests in a `math.test.en` test part, whose failure texts only \
     `enrang test` shows, and `enrang test` is M4's; a compile fixture is one file",
)];

/// `rows` with the near-miss of each row that `later` names due at its milestone.
/// An entry that names no row with a near-miss, or a milestone not after `floor`,
/// is an error.
pub fn defer_near_misses(
    mut rows: Vec<AttackRow>,
    later: &[(&str, Milestone, &str)],
    floor: Milestone,
) -> Result<Vec<AttackRow>, String> {
    for (id, milestone, _) in later {
        if *milestone <= floor {
            return Err(format!(
                "NEAR_MISS_LATER gives {id} {milestone}, which is not after {floor}"
            ));
        }
        let row = rows
            .iter_mut()
            .find(|row| row.ids.iter().any(|own| own == id) && row.near_miss.is_some())
            .ok_or_else(|| format!("NEAR_MISS_LATER names {id}, which needs no near-miss"))?;
        row.near_miss = row.near_miss.map(|since| since.max(*milestone));
    }
    Ok(rows)
}

/// The rows of TESTING 18's tables before the attack reviews, and the first cells of
/// every row of those tables.
fn real_table_rows() -> (Vec<TableRow>, Vec<String>) {
    let doc = read("docs/TESTING.md");
    let rows = table_rows(&doc, &registry_info_m3, TABLE_NOT_FIRED, M3_LINES_SINCE)
        .unwrap_or_else(|error| panic!("TESTING 18's tables: {error}"));
    let cells = table_cells(&doc).unwrap_or_else(|error| panic!("TESTING 18's tables: {error}"));
    (rows, cells)
}

/// The `.mir` fixtures of the mir and borrowck suites, each path from the
/// workspace root and text, in path order.
fn mir_fixtures() -> Vec<(String, String)> {
    fn walk(dir: &std::path::Path, root: &std::path::Path, out: &mut Vec<(String, String)>) {
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                walk(&path, root, out);
            } else if path.extension().is_some_and(|e| e == "mir") {
                let shown = path.strip_prefix(root).unwrap_or(&path);
                let text = fs::read_to_string(&path).unwrap_or_default();
                out.push((shown.to_string_lossy().into_owned(), text));
            }
        }
    }
    let root = enrang_testkit::workspace_root();
    let mut out = Vec::new();
    for suite in [
        "crates/enrang-borrowck/tests/mir",
        "crates/enrang-mir/tests",
    ] {
        walk(&root.join(suite), &root, &mut out);
    }
    out.sort();
    out
}

/// One line per gated code of each `.mir` row of TESTING 18's tables ([`mir_level`],
/// which no compile fixture shows): a `.mir` fixture whose first line claims the row,
/// `// row: ` and the start of its first cell as [`claim_fits`] reads it, and that
/// anchors the code (T:628, A:1029-1031's normal forms).
pub fn mir_row_lines(
    doc: &str,
    fixtures: &[(String, String)],
    info: &dyn Fn(&str) -> Option<(bool, Milestone)>,
) -> Result<Vec<Line>, String> {
    let mut lines = Vec::new();
    for (at, row) in table_lines(doc)? {
        if !mir_level(&row[0]) {
            continue;
        }
        for code in named_codes(&row[1..].join(" | ")) {
            let Some((true, since)) = info(&code) else {
                continue;
            };
            let shows = fixtures.iter().any(|(_, text)| {
                let claims = (text.lines().next())
                    .and_then(|line| line.strip_prefix("// row: "))
                    .is_some_and(|claim| claim_fits(claim, &row[0]));
                claims
                    && enrang_testkit::anchors(text)
                        .is_ok_and(|found| found.iter().any(|a| a.code == code))
            });
            lines.push(Line {
                id: format!("TESTING line {at}, `.mir` row, {code}"),
                since,
                status: match shows {
                    true => FixtureStatus::Passing,
                    false => FixtureStatus::Missing,
                },
            });
        }
    }
    Ok(lines)
}

/// Each `H` row of SPEC 5.8 with the milestone its line is due at.
fn real_h_due() -> Vec<(String, Milestone)> {
    h_lines_due(&family_rows("H"), H_LATER, M3_LINES_SINCE)
        .unwrap_or_else(|error| panic!("SPEC 5.8: {error}"))
}

/// The lines of each M3 gate over the real fixtures, by name: the M3 view of the
/// attack rows, the table rows and the `H` rows.
pub fn real_m3_lines() -> Vec<(&'static str, Vec<Line>)> {
    let fixtures = real_fixtures();
    let evidence = Evidence {
        fixtures: &fixtures,
        run: &run_cached,
    };
    let (rows, cells) = real_table_rows();
    let places = table_places(&read("docs/TESTING.md"))
        .unwrap_or_else(|error| panic!("TESTING 18's tables: {error}"));
    let claims = resolve_claims(&fixtures, &cells);
    let claimed = |claiming: &Claiming, line: usize| {
        places
            .get(&line)
            .is_some_and(|&at| claims_at(&claims, claiming, at))
    };
    vec![
        (
            "attack rows, M3's reading",
            attack_lines(&real_attack_rows_m3(), &evidence, &claimed),
        ),
        ("table rows", table_row_lines(&rows, &cells, &evidence)),
        ("H rows", h_row_lines(&real_h_due(), &evidence)),
    ]
}

/// What is wrong with a gate's report at `current` against its lines: it must
/// enforce exactly the lines due by `current`, defer the rest, and report as gaps
/// exactly the due lines whose evidence does not pass, so a line due at the bump
/// cannot slip through it unenforced.
pub fn bump_problems(lines: &[Line], current: Milestone) -> Vec<String> {
    report_problems(lines, &gate_lines(lines, current), current)
}

/// What [`bump_problems`] finds wrong with `report`, the gate's report of `lines`
/// at `current`: a due line it does not enforce, or a due line without a passing
/// fixture that it does not name as a gap.
pub fn report_problems(lines: &[Line], report: &GateReport, current: Milestone) -> Vec<String> {
    let due: Vec<&Line> = lines.iter().filter(|line| line.since <= current).collect();
    let mut problems = Vec::new();
    if report.enforced != due.len() || report.deferred != lines.len() - due.len() {
        problems.push(format!(
            "enforced {} and deferred {} of {} lines, {} due",
            report.enforced,
            report.deferred,
            lines.len(),
            due.len()
        ));
    }
    let wanted: Vec<&str> = due
        .iter()
        .filter(|line| line.status != FixtureStatus::Passing)
        .map(|line| line.id.as_str())
        .collect();
    if ids_of(&report.gaps) != wanted {
        problems.push(format!(
            "gaps {:?}, wanted {wanted:?}",
            ids_of(&report.gaps)
        ));
    }
    problems
}

/// How many lines a report enforced and deferred together.
fn lines_of(report: &GateReport) -> usize {
    report.enforced + report.deferred
}

/// The attack rows TESTING 18 has today whose codes are phase 2 (M2 plan g.6), in
/// document order: first the rows that sit beside the rows they extend, in the
/// tables above the reviews (fix-6), then the reviews' own.
const ATTACK_IDS: &[&str] = &[
    "OQ24-nested",
    "F14",
    "WD-4",
    "EF-09",
    "D20-core-5",
    "D20E-01",
    "F1",
    "F5",
    "F7",
    "F9",
    "MR-9",
    "MR-2",
    "OQ13-slice",
    "MR-4",
    "MR-5",
    "V-ME-09-arrow",
    "EF-03",
    "OQ20-age",
    "S2-33-err",
    "V-ME-06-err",
    "S2-32-lift",
    "EF-06",
    "EF-08",
    "EP-06-opt",
    "OQ24-onKey",
    "S2-08-copy",
    "S2-15-field",
    "S2-26-test",
    "Q37-private",
    "RR-06",
    "C4-super-paths",
    "C4-ctorless-base",
    "Q32-field-rules",
    "S2-03-into",
    "C4-move-inherited",
    "VI-04-copy",
    "S2-09-self",
    "VI-03-swap",
    "VI-03-branches",
    "S2-10-swap",
    "VI-01-part",
    "VI-06-tables",
    "S2-29-fmt",
    "D8-super",
    "D8-bound",
    "EP-07",
    "Q39-from-raw",
    "SL-10-helps",
    "Q44-show",
    "VI-02-measured",
    "VI-02-cast",
    "VI-02-class",
    "VI-02-arrow",
    "VI-02-structural",
    "VI-02-inherited",
    "VI-02-bound",
    "VI-05-dumper",
    "VI-05-override",
    "VI-07-overloads",
];

/// The attack rows above that say no program of theirs compiles or prints.
/// The firing lines of TESTING 18's attack rows: the codes their firing fixtures
/// must anchor, summed over the rows (`C4-super-paths`'s `super();` in a class
/// with no base is phase 2's EN0219 since the fix-sound stage).
const FIRING_LINES: usize = 68;

const ATTACK_WITHOUT_NEAR_MISS: &[&str] = &[
    "F14",
    "D20-core-5",
    "D20E-01",
    "MR-4",
    "S2-15-field",
    "RR-06",
    "C4-super-paths",
    "VI-03-swap",
    "VI-02-measured",
    "VI-02-cast",
    "VI-02-class",
    "VI-02-arrow",
    "VI-02-inherited",
    "VI-02-bound",
    "VI-05-dumper",
    "VI-05-override",
];

/// A fake fixture whose claims are read from its text, as the real ones are.
fn fake_claiming(path: &str, text: &str) -> Claiming {
    Claiming {
        fixture: fake_fixture(path, text),
        covers: parse_covers(text),
        rows: parse_row_claims(text),
    }
}

/// The stderr of a fake run of `path` that fires `code` at `line`.
fn fired_at(path: &str, code: &str, line: usize) -> String {
    format!("error[{code}]: fake\n --> {path}:{line}:1\n")
}

/// A fake command line from `(path, stderr)` pairs, each the run of `check <path>`,
/// with the runs in `noisy` exiting 1, as a near-miss that fails would.
fn fake_cli(table: &[(&str, String)], noisy: &[&str]) -> FakeCli {
    let keyed: Vec<(String, &str)> = table
        .iter()
        .map(|(path, stderr)| (format!("check {path}"), stderr.as_str()))
        .collect();
    let mut cli = FakeCli::new(keyed.iter().map(|(key, stderr)| (key.as_str(), *stderr)));
    for path in noisy {
        cli = cli.breaking(&format!("check {path}"), 1, "");
    }
    cli
}

/// A fake registry of `C` rows with every kind of claim that matters: C90 and C94
/// (claimed in a list) have both kinds of evidence, C91 only an accept, C92 a
/// near-miss that fails and a firing fixture that does not fire, C93 nothing; C99
/// names no row, while H01 names a row of another family.
fn c_fake(current: Milestone) -> GateReport {
    let dir = "tests/compile/EN9401";
    let fixtures = [
        fake_claiming(&format!("{dir}/c90.pass.en"), "//! covers: C90\ny\n"),
        fake_claiming(
            &format!("{dir}/c90.fail.en"),
            "//! covers: C90, C94\nx //~ EN9401\n",
        ),
        fake_claiming(&format!("{dir}/c91.pass.en"), "//! covers: C91\ny\n"),
        fake_claiming(&format!("{dir}/c92.pass.en"), "//! covers: C92\ny\n"),
        fake_claiming(
            &format!("{dir}/c92.fail.en"),
            "//! covers: C92\nx //~ EN9401\n",
        ),
        fake_claiming(&format!("{dir}/c94.pass.en"), "y\n//! covers: C94\n"),
        fake_claiming(
            &format!("{dir}/orphan.pass.en"),
            "//! covers: C99, H01\ny\n",
        ),
    ];
    let c90 = format!("{dir}/c90.fail.en");
    let c92 = format!("{dir}/c92.pass.en");
    let cli = fake_cli(
        &[(c90.as_str(), fired_at(&c90, "EN9401", 2))],
        &[c92.as_str()],
    );
    let run = |place: &Place, args: &[String]| cli.run(place, args);
    let evidence = Evidence {
        fixtures: &fixtures,
        run: &run,
    };
    let rows = [
        ("C90", Milestone::M2),
        ("C91", Milestone::M2),
        ("C92", Milestone::M2),
        ("C93", Milestone::M2),
        ("C94", Milestone::M2),
    ];
    gate_c_rows(&rows, &["H01"], &evidence, current)
}

/// A fake rule of three clauses fired as EN9416 and EN9419: `private` has all its
/// fixtures; `box` a fixture at EN9416 that anchors another code, none at EN9419
/// and a near-miss that fails; `field` its firing fixtures and a near-miss in a
/// directory of neither code. `satisfy-bogus` is no clause, and a `satisfy-` file
/// of another directory is none of this gate's business.
fn clause_fake(current: Milestone) -> GateReport {
    let path = |code: &str, name: &str| format!("tests/compile/{code}/{name}");
    let paths = [
        path("EN9416", "satisfy-private.fail.en"),
        path("EN9419", "satisfy-private.fail.en"),
        path("EN9416", "satisfy-private.pass.en"),
        path("EN9416", "satisfy-box.fail.en"),
        path("EN9419", "satisfy-box.pass.en"),
        path("EN9416", "satisfy-field.fail.en"),
        path("EN9419", "satisfy-field.fail.en"),
        path("EN9401", "satisfy-field.pass.en"),
        path("EN9419", "satisfy-bogus.fail.en"),
        path("EN9401", "satisfy-other.fail.en"),
    ];
    let text = |at: usize| match at {
        0 | 5 => "x //~ EN9416\n",
        1 | 6 | 8 => "x //~ EN9419\n",
        3 | 9 => "x //~ EN9401\n",
        _ => "y\n",
    };
    let fixtures: Vec<Claiming> = paths
        .iter()
        .enumerate()
        .map(|(at, path)| fake_claiming(path, text(at)))
        .collect();
    let fires = [
        (paths[0].as_str(), fired_at(&paths[0], "EN9416", 1)),
        (paths[1].as_str(), fired_at(&paths[1], "EN9419", 1)),
        (paths[3].as_str(), fired_at(&paths[3], "EN9401", 1)),
        (paths[5].as_str(), fired_at(&paths[5], "EN9416", 1)),
        (paths[6].as_str(), fired_at(&paths[6], "EN9419", 1)),
        (paths[8].as_str(), fired_at(&paths[8], "EN9419", 1)),
    ];
    let cli = fake_cli(&fires, &[paths[4].as_str()]);
    let run = |place: &Place, args: &[String]| cli.run(place, args);
    let evidence = Evidence {
        fixtures: &fixtures,
        run: &run,
    };
    gate_clauses(
        &["private", "box", "field"],
        &[("EN9416", Milestone::M2), ("EN9419", Milestone::M2)],
        &evidence,
        current,
    )
}

/// A fake TESTING document: rows before and after the attack reviews, and inside
/// them a row of each shape that matters.
const ATTACK_DOC: &str = "\
Intro.

| Fixture | Must give |
|---|---|
| `X-1`: before the reviews | EN9701 |

**The attack review of the applied design.** Prose naming `EN9701`.

| Fixture | Must give |
|---|---|
| `A-1`: `f(x)` | EN9701 at `x` (twin compiles) |
| `A-2 both`: `g()` \\| `h()` | Compiles; EN9701 and EN9702 |
| `A-3`, `B-3`: `k()` | EN9703 only |
| `A-4`: `m()` | EN9704, found later; prints `1` |
| `A-5`: `p()` | EN9705, found in phase 3 |
| `A-6`, `B-6`: `q()` | EN9701 |
| `A-7`: `r()` | Compiles; EN9701 is found in phase 3 |
| Each other row | EN9701 |

**Hermeticity:** after.

| Fixture | Must give |
|---|---|
| `Z-1`: after the reviews | EN9701 |
";

/// The fake codes of [`ATTACK_DOC`]: EN9703 is not gated, EN9704 is due at M4.
fn fake_info(name: &str) -> Option<(bool, Milestone)> {
    match name {
        "EN9701" | "EN9702" | "EN9705" => Some((true, Milestone::M2)),
        "EN9703" => Some((false, Milestone::M3)),
        "EN9704" => Some((true, Milestone::M4)),
        _ => None,
    }
}

const FAKE_NOT_FIRED: &[NotFired] = &[
    ("A-5", "EN9705", None),
    ("A-7", "EN9701", Some(Milestone::M3)),
];

/// The line of `ATTACK_DOC` that opens with `start`.
fn doc_line(start: &str) -> usize {
    ATTACK_DOC
        .lines()
        .position(|line| line.starts_with(start))
        .expect("a line")
        + 1
}

/// [`ATTACK_DOC`]'s rows gated over fixtures of each kind that matters: `A-1`
/// fires; `A-2 both` fires EN9701, while EN9702 is anchored only by `a-2`, another
/// name, and its near-miss passes; `A-4`'s M4 fixture already passes; `A-5`'s
/// near-miss fails; `A-6` fires under its second ID.
fn attack_fake(current: Milestone) -> GateReport {
    let rows = attack_rows(ATTACK_DOC, &fake_info, FAKE_NOT_FIRED).expect("the fake reads");
    let firing = [
        ("tests/compile/EN9701/a-1.fail.en", "EN9701"),
        ("tests/compile/EN9701/a-2-both.fail.en", "EN9701"),
        ("tests/compile/EN9702/a-2.fail.en", "EN9702"),
        ("tests/compile/EN9704/a-4.fail.en", "EN9704"),
        ("tests/compile/EN9701/b-6.fail.en", "EN9701"),
    ];
    let near = [
        "tests/compile/EN9701/a-2-both.pass.en",
        "tests/compile/EN9705/a-5.pass.en",
        "tests/compile/EN9701/a-7.pass.en",
    ];
    let mut fixtures: Vec<Claiming> = firing
        .iter()
        .map(|(path, code)| fake_claiming(path, &format!("x //~ {code}\n")))
        .collect();
    fixtures.extend(near.iter().map(|path| fake_claiming(path, "y\n")));
    let table: Vec<(&str, String)> = firing
        .iter()
        .map(|(path, code)| (*path, fired_at(path, code, 1)))
        .collect();
    let cli = fake_cli(&table, &[near[1]]);
    let run = |place: &Place, args: &[String]| cli.run(place, args);
    let evidence = Evidence {
        fixtures: &fixtures,
        run: &run,
    };
    gate_attack(&rows, &evidence, current)
}

pub fn ids_of(findings: &[GateFinding]) -> Vec<&str> {
    findings.iter().map(|finding| finding.id.as_str()).collect()
}

pub fn register(h: &mut Harness) {
    register_m3(h);
    h.case(
        "covers/every C row of SPEC 4.5 has an accept and a reject",
        || {
            let report = real_c_report(CURRENT_MILESTONE);
            assert!(report.is_clean(), "\n{report}");
        },
    );
    h.case(
        "covers/every clause of SPEC 4.4's satisfaction rule has its fixtures",
        || {
            let report = real_clause_report(CURRENT_MILESTONE);
            assert!(report.is_clean(), "\n{report}");
        },
    );
    h.case(
        "covers/every attack-review row with a phase 2 code has its fixtures",
        || {
            let report = real_attack_report(CURRENT_MILESTONE);
            assert!(report.is_clean(), "\n{report}");
        },
    );
    h.case(
        "covers/at M2 the gates enforce every line, and before it none",
        || {
            let rows = real_attack_rows();
            let attack_lines: usize = rows
                .iter()
                .map(|row| row.fires.len() + usize::from(row.near_miss.is_some()))
                .sum();
            let due = |milestone: Milestone| {
                let c = if C_ROWS_SINCE <= milestone { 2 * 19 } else { 0 };
                let clause = SATISFY_CODES
                    .iter()
                    .filter(|code| code.since() <= milestone)
                    .count()
                    * 10;
                let near = SATISFY_CODES.iter().map(|code| code.since()).min();
                let clause_near = if near.is_some_and(|near| near <= milestone) {
                    10
                } else {
                    0
                };
                let attack: usize = rows
                    .iter()
                    .map(|row| {
                        let fires = row.fires.iter().filter(|(_, since)| *since <= milestone);
                        fires.count() + usize::from(row.near_miss.is_some_and(|s| s <= milestone))
                    })
                    .sum();
                (c, clause + clause_near, attack)
            };
            assert!(
                Milestone::M2 <= CURRENT_MILESTONE,
                "M2's lines are enforced"
            );
            for milestone in [Milestone::M1, Milestone::M2, CURRENT_MILESTONE] {
                let (c, clause, attack) = due(milestone);
                let reports = [
                    (real_c_report(milestone), c, 2 * 19),
                    (real_clause_report(milestone), clause, 3 * 10),
                    (real_attack_report(milestone), attack, attack_lines),
                ];
                for (report, enforced, lines) in reports {
                    assert_eq!(report.current, format!("{milestone:?}"));
                    assert_eq!(report.enforced, enforced, "{milestone:?}\n{report}");
                    assert_eq!(lines_of(&report), lines, "{milestone:?}\n{report}");
                }
            }
            // Every line is due at M2 but the lines an excuse defers past it: S2-08-copy's
            // EN0418, a firing line from M3.
            let later: usize = rows
                .iter()
                .flat_map(|row| &row.fires)
                .filter(|(_, since)| *since > Milestone::M2)
                .count();
            assert_eq!(later, 1);
            assert_eq!(due(Milestone::M2), (38, 30, attack_lines - later));
            // Before the bump that closed M2, no line was due: its evidence was early.
            assert_eq!(due(Milestone::M1), (0, 0, 0));
        },
    );
    h.case(
        "covers/at the current milestone the gates lack nothing, and nothing is stale",
        || {
            // The registry gate, the three of this module that M2 added and the three
            // M3 added together, at the current milestone, which closed M3: a lost
            // near-miss, a blanked claim, a renamed attack or row fixture, a lost `H`
            // claim or a deleted page is a gap. EN0439, the last held M2 item, landed
            // with the `//! library` header (G50); the only M3 lines not enforced are
            // those `H_LATER`, `NEAR_MISS_LATER` and later codes give a later milestone.
            assert!(
                Milestone::M3 <= CURRENT_MILESTONE,
                "M3's lines are enforced"
            );
            let mut reports = vec![
                crate::gating::real_report_at(&gate_transcripts(), CURRENT_MILESTONE),
                real_c_report(CURRENT_MILESTONE),
                real_clause_report(CURRENT_MILESTONE),
                real_attack_report(CURRENT_MILESTONE),
            ];
            for (name, lines) in real_m3_lines() {
                let report = gate_lines(&lines, CURRENT_MILESTONE);
                let due = lines
                    .iter()
                    .filter(|line| line.since <= CURRENT_MILESTONE)
                    .count();
                assert_eq!(report.enforced, due, "{name}");
                assert!(report.enforced > 0, "{name}: nothing enforced");
                reports.push(report);
            }
            let mut gaps = Vec::new();
            for report in &reports {
                assert!(report.stale.is_empty(), "\n{report}");
                assert!(report.duplicates.is_empty(), "\n{report}");
                assert!(report.orphans.is_empty(), "\n{report}");
                gaps.extend(report.gaps.iter().map(|gap| gap.id.clone()));
            }
            assert_eq!(gaps, Vec::<String>::new());
        },
    );
    h.case("covers/SPEC 4.5's C rows are C04 to C22", || {
        let rows = family_rows("C");
        let wanted: Vec<String> = (4..=22).map(|n| format!("C{n:02}")).collect();
        assert_eq!(rows, wanted);
    });
    h.case(
        "covers/the satisfaction clauses are SPEC 4.4's rule, one per way to break it",
        || {
            assert_eq!(
                rule_differences(&read("docs/SPEC.md")),
                Vec::<String>::new()
            );
            assert_eq!(
                clauses(),
                [
                    "private",
                    "protected",
                    "unsafe-member",
                    "unsafe-method",
                    "requires",
                    "field",
                    "type-params",
                    "param-types",
                    "return-type",
                    "box"
                ]
            );
            assert_eq!(SATISFY_CODES.map(Code::since), [Milestone::M2; 2]);
        },
    );
    h.case("covers/a changed satisfaction rule is seen", || {
        let rule = "intro\n\n### 4.4 Interfaces\n\nStructural. Own members count; \
                    auto-deref never contributes a member, so no.\n\n\
                    - It is public. More.\n- It has the same unsafety: more.\n\
                    - It has no `@requires`.\n- It is a method.\n\
                    - It has equal type parameters and bounds, equal parameter types and an \
                    equal return type.\n\nAfter.\n\n### 4.5 Next\n\n- A later list.\n";
        assert_eq!(rule_differences(rule), Vec::<String>::new());
        let added = rule.replace("- It is a method.\n", "- It is a method.\n- It is pure.\n");
        assert_eq!(
            rule_differences(&added),
            [
                "the rule has 6 bullets, not 5",
                "\"- It is pure.\" does not open with \"It has equal type parameters and \
                 bounds, equal parameter types and an equal return type.\""
            ]
        );
        let derefs = rule.replace("auto-deref never contributes a member", "auto-deref counts");
        assert_eq!(
            rule_differences(&derefs),
            ["the text before the list lacks \"auto-deref never contributes a member\""]
        );
        assert_eq!(rule_differences("no section"), ["no `### 4.4 Interfaces`"]);
    });
    h.case(
        "covers/no excused code of an attack row is one its own firing fixture anchors",
        || {
            assert_eq!(
                anchored_excuses(NOT_FIRED, &real_fixtures()),
                Vec::<String>::new()
            );
            // An excuse added for a code the row's fixture anchors (m38) is seen.
            let mut planted = NOT_FIRED.to_vec();
            planted.push(("MR-2", "EN0401", None));
            assert_eq!(
                anchored_excuses(&planted, &real_fixtures()),
                ["MR-2 excuses EN0401, which tests/compile/EN0401/mr-2.fail.en anchors"]
            );
        },
    );
    h.case("covers/TESTING 18's attack rows are read whole", || {
        let rows = real_attack_rows();
        // Every firing line the rows give, pinned: a new excuse turns one into a
        // near-miss line, so it changes this number even when the row's fixture is
        // deleted with it (m24).
        let firing: usize = rows.iter().map(|row| row.fires.len()).sum();
        assert_eq!(firing, FIRING_LINES, "firing lines");
        let ids: Vec<&str> = rows.iter().map(|row| row.ids[0].as_str()).collect();
        assert_eq!(ids, ATTACK_IDS);
        assert!(rows.iter().all(|row| row.ids.len() == 1), "{rows:?}");
        let without: Vec<&str> = rows
            .iter()
            .filter(|row| row.near_miss.is_none())
            .map(|row| row.ids[0].as_str())
            .collect();
        assert_eq!(without, ATTACK_WITHOUT_NEAR_MISS);
        let row = |id: &str| rows.iter().find(|row| row.ids[0] == id).expect("a row");
        let codes = |id: &str| -> Vec<&str> {
            row(id)
                .fires
                .iter()
                .map(|(code, _)| code.as_str())
                .collect()
        };
        assert_eq!(codes("D20-core-5"), ["EN0701"]);
        assert_eq!(codes("EF-03"), ["EN0401"]);
        assert_eq!(codes("EF-08"), ["EN0701"]);
        assert_eq!(codes("VI-07-overloads"), ["EN0451"]);
        assert_eq!(codes("MR-4"), ["EN0313", "EN0803"]);
        // EN0418 is excused until M3, when phase 3 finds it (T:945).
        assert_eq!(codes("S2-08-copy"), ["EN0418"]);
        assert_eq!(row("S2-08-copy").fires[0].1, Milestone::M3);
        assert_eq!(codes("S2-32-lift"), Vec::<&str>::new());
        for id in [
            "EF-03",
            "EF-08",
            "S2-08-copy",
            "S2-32-lift",
            "VI-07-overloads",
        ] {
            assert_eq!(row(id).near_miss, Some(Milestone::M2), "{id}");
        }
        assert!(
            rows.iter()
                .filter(|row| row.ids[0] != "S2-08-copy")
                .flat_map(|row| &row.fires)
                .all(|(_, since)| *since == Milestone::M2),
            "{rows:?}"
        );
        let testing = read("docs/TESTING.md");
        let text = |line: usize| testing.lines().nth(line - 1).expect("a line");
        assert!(text(row("D20E-01").line).starts_with("| `D20E-01`: "));
        assert!(text(row("VI-07-overloads").line).starts_with("| `VI-07-overloads`: "));
    });
    h.case("covers/a C row needs a working claim of each kind", || {
        assert_eq!(
            c_fake(Milestone::M2).to_string(),
            "gap: C91 reject has no fixture (since M2, current M2)\n\
             gap: C92 accept has a failing fixture (since M2, current M2)\n\
             gap: C92 reject has a failing fixture (since M2, current M2)\n\
             gap: C93 accept has no fixture (since M2, current M2)\n\
             gap: C93 reject has no fixture (since M2, current M2)\n\
             orphan: `covers: C99` names no row\n"
        );
        assert_eq!(c_fake(Milestone::M2).enforced, 10);
    });
    h.case(
        "covers/before M2 a C row's evidence is early and its absence no gap",
        || {
            let report = c_fake(Milestone::M1);
            assert_eq!(report.to_string(), "orphan: `covers: C99` names no row\n");
            assert_eq!(
                ids_of(&report.early),
                [
                    "C90 accept",
                    "C90 reject",
                    "C91 accept",
                    "C94 accept",
                    "C94 reject"
                ]
            );
            assert_eq!((report.enforced, report.deferred), (0, 10));
            // Two milestones ahead the same evidence is stale.
            let report = c_fake(Milestone::M0);
            assert!(report.early.is_empty(), "{report}");
            assert_eq!(
                ids_of(&report.stale),
                [
                    "C90 accept",
                    "C90 reject",
                    "C91 accept",
                    "C94 accept",
                    "C94 reject"
                ]
            );
        },
    );
    h.case("covers/each satisfaction case trips", || {
        assert_eq!(
            clause_fake(Milestone::M2).to_string(),
            "gap: satisfy-box EN9416 has a failing fixture (since M2, current M2)\n\
             gap: satisfy-box EN9419 has no fixture (since M2, current M2)\n\
             gap: satisfy-box near-miss has a failing fixture (since M2, current M2)\n\
             gap: satisfy-field near-miss has no fixture (since M2, current M2)\n\
             orphan: `covers: satisfy-bogus` names no row\n"
        );
        let report = clause_fake(Milestone::M1);
        assert_eq!(
            report.to_string(),
            "orphan: `covers: satisfy-bogus` names no row\n"
        );
        assert_eq!(
            ids_of(&report.early),
            [
                "satisfy-private EN9416",
                "satisfy-private EN9419",
                "satisfy-private near-miss",
                "satisfy-field EN9416",
                "satisfy-field EN9419"
            ]
        );
        assert_eq!((report.enforced, report.deferred), (0, 9));
    });
    h.case(
        "covers/a row the review lists as beside the row it extends is an attack row (fix-6)",
        || {
            let doc = "| Program | Must |\n|---|---|\n\
| `x` one; `B-7`, the near-misses at a limit | Compiles; EN9701 |\n\
| `B-8`: unlisted, so no attack row | EN9701 |\n\
**The attack review of the applied design.** Rows that extend an existing row sit beside it in the tables above (`B-7`).\n\
**Hermeticity:** end.\n";
            let rows = attack_rows(doc, &fake_info, &[]).expect("the fake reads");
            let ids: Vec<&str> = rows.iter().map(|row| row.ids[0].as_str()).collect();
            assert_eq!(ids, ["B-7"]);
            assert_eq!(rows[0].near_miss, Some(Milestone::M2));
            assert_eq!(
                beside_ids("sit beside it in the tables above (`W-1`, `W-2`), more"),
                ["W-1".to_owned(), "W-2".to_owned()].into_iter().collect()
            );
        },
    );
    h.case("covers/attack rows are read by the plan's rule", || {
        let rows = attack_rows(ATTACK_DOC, &fake_info, FAKE_NOT_FIRED).expect("the fake reads");
        let owned = |ids: &[&str]| ids.iter().map(|id| (*id).to_owned()).collect::<Vec<_>>();
        let fires = |codes: &[(&str, Milestone)]| {
            codes
                .iter()
                .map(|(code, since)| ((*code).to_owned(), *since))
                .collect::<Vec<_>>()
        };
        assert_eq!(
            rows,
            [
                AttackRow {
                    ids: owned(&["A-1"]),
                    line: doc_line("| `A-1`"),
                    fires: fires(&[("EN9701", Milestone::M2)]),
                    near_miss: None,
                },
                AttackRow {
                    ids: owned(&["A-2 both"]),
                    line: doc_line("| `A-2 both`"),
                    fires: fires(&[("EN9701", Milestone::M2), ("EN9702", Milestone::M2)]),
                    near_miss: Some(Milestone::M2),
                },
                AttackRow {
                    ids: owned(&["A-4"]),
                    line: doc_line("| `A-4`"),
                    fires: fires(&[("EN9704", Milestone::M4)]),
                    near_miss: Some(Milestone::M4),
                },
                AttackRow {
                    ids: owned(&["A-5"]),
                    line: doc_line("| `A-5`"),
                    fires: Vec::new(),
                    near_miss: Some(Milestone::M2),
                },
                AttackRow {
                    ids: owned(&["A-6", "B-6"]),
                    line: doc_line("| `A-6`"),
                    fires: fires(&[("EN9701", Milestone::M2)]),
                    near_miss: None,
                },
                // Excused until M3: a near-miss now, a firing fixture from M3.
                AttackRow {
                    ids: owned(&["A-7"]),
                    line: doc_line("| `A-7`"),
                    fires: fires(&[("EN9701", Milestone::M3)]),
                    near_miss: Some(Milestone::M2),
                },
            ]
        );
    });
    h.case("covers/each attack-row case trips", || {
        assert_eq!(
            attack_fake(Milestone::M2).to_string(),
            "gap: A-2 both EN9702 has no fixture (since M2, current M2)\n\
             gap: A-5 near-miss has a failing fixture (since M2, current M2)\n\
             stale: A-4 EN9704 claims a passing fixture before its milestone (since M4, current M2)\n"
        );
        let report = attack_fake(Milestone::M1);
        assert_eq!(
            report.to_string(),
            "stale: A-4 EN9704 claims a passing fixture before its milestone (since M4, current M1)\n"
        );
        assert_eq!(
            ids_of(&report.early),
            [
                "A-1 EN9701",
                "A-2 both EN9701",
                "A-2 both near-miss",
                "A-6 EN9701",
                "A-7 near-miss"
            ]
        );
        assert_eq!((report.enforced, report.deferred), (0, 10));
        // From its `until` milestone an excused code needs a firing fixture.
        let report = attack_fake(Milestone::M4);
        assert_eq!(
            report.to_string(),
            "gap: A-2 both EN9702 has no fixture (since M2, current M4)\n\
             gap: A-4 near-miss has no fixture (since M4, current M4)\n\
             gap: A-5 near-miss has a failing fixture (since M2, current M4)\n\
             gap: A-7 EN9701 has no fixture (since M3, current M4)\n"
        );
    });
    h.case(
        "covers/an attack fixture's name is the row's slug, whole, never a prefix",
        || {
            // `a-1-x` is no fixture of `A-1`, though it opens with its slug.
            let rows = attack_rows(ATTACK_DOC, &fake_info, FAKE_NOT_FIRED).expect("the fake reads");
            let path = "tests/compile/EN9701/a-1-x.fail.en";
            let fixtures = [fake_claiming(path, "x //~ EN9701\n")];
            let cli = fake_cli(&[(path, fired_at(path, "EN9701", 1))], &[]);
            let run = |place: &Place, args: &[String]| cli.run(place, args);
            let evidence = Evidence {
                fixtures: &fixtures,
                run: &run,
            };
            let report = gate_attack(&rows[..1], &evidence, Milestone::M2);
            assert_eq!(
                report.to_string(),
                "gap: A-1 EN9701 has no fixture (since M2, current M2)\n"
            );
        },
    );
    h.case(
        "covers/an attack fixture must anchor the code of its line",
        || {
            // A fixture named after the row, in the code's directory, that fires but
            // anchors another code is a failing fixture of that line.
            let rows = attack_rows(ATTACK_DOC, &fake_info, FAKE_NOT_FIRED).expect("the fake reads");
            let path = "tests/compile/EN9702/a-2-both.fail.en";
            let fixtures = [
                fake_claiming(path, "x //~ EN9701\n"),
                fake_claiming("tests/compile/EN9701/a-1.fail.en", "x //~ EN9701\n"),
            ];
            let cli = fake_cli(
                &[
                    (path, fired_at(path, "EN9701", 1)),
                    (
                        "tests/compile/EN9701/a-1.fail.en",
                        fired_at("tests/compile/EN9701/a-1.fail.en", "EN9701", 1),
                    ),
                ],
                &[],
            );
            let run = |place: &Place, args: &[String]| cli.run(place, args);
            let evidence = Evidence {
                fixtures: &fixtures,
                run: &run,
            };
            let report = gate_attack(&rows[..2], &evidence, Milestone::M2);
            assert_eq!(
                report.to_string(),
                "gap: A-2 both EN9702 has a failing fixture (since M2, current M2)\n\
             gap: A-2 both near-miss has no fixture (since M2, current M2)\n"
            );
        },
    );
    let unreadable: &[(&str, &str, &str)] = &[
        (
            "a document with no attack reviews",
            "| `A-1`: x | EN9701 |\n**Hermeticity:**\n",
            "no line opens with **The attack review of the applied design.**",
        ),
        (
            "attack reviews that never end",
            "**The attack review of the applied design.**\n| `A-1`: x | EN9701 |\n",
            "no line after the attack reviews opens with **Hermeticity:**",
        ),
        (
            "a row that opens with code, not an ID",
            "**The attack review of the applied design.**\n\
             | `f(x)` with y | EN9701 |\n**Hermeticity:**\n",
            "line 2: the first cell opens with no ID",
        ),
        (
            "a code no registry has",
            "**The attack review of the applied design.**\n\
             | `A-7`: x | EN9799 |\n**Hermeticity:**\n",
            "line 2: EN9799 is no code",
        ),
    ];
    for (name, doc, error) in unreadable {
        let (doc, error) = (*doc, *error);
        h.case(format!("covers/reading fails on {name}"), move || {
            assert_eq!(attack_rows(doc, &fake_info, &[]), Err(error.to_owned()));
        });
    }
    h.case(
        "covers/an excuse that names no row's code is an error",
        || {
            let missing = attack_rows(ATTACK_DOC, &fake_info, &[("A-9", "EN9701", None)]);
            assert_eq!(
                missing,
                Err("no attack row A-9 names the gated code EN9701".to_owned())
            );
            let other = attack_rows(ATTACK_DOC, &fake_info, &[("A-1", "EN9702", None)]);
            assert_eq!(
                other,
                Err("no attack row A-1 names the gated code EN9702".to_owned())
            );
            let ungated = attack_rows(ATTACK_DOC, &fake_info, &[("A-3", "EN9703", None)]);
            assert_eq!(
                ungated,
                Err("no attack row A-3 names the gated code EN9703".to_owned())
            );
            // The real excuses each name a code of their row.
            assert!(attack_rows(&read("docs/TESTING.md"), &registry_info, NOT_FIRED).is_ok());
        },
    );
    let slugs: &[(&str, &str)] = &[
        ("D20E-01", "d20e-01"),
        ("D20-core-1 both", "d20-core-1-both"),
        ("S2-08-copy", "s2-08-copy"),
        ("F1", "f1"),
        ("Q39-from-raw", "q39-from-raw"),
        ("V-ME-09-arrow", "v-me-09-arrow"),
        ("a.b_c", "a-b-c"),
    ];
    for (id, wanted) in slugs {
        let (id, wanted) = (*id, *wanted);
        h.case(format!("covers/the fixture name of {id:?}"), move || {
            assert_eq!(slug(id), wanted);
        });
    }
    let compiles: &[(&str, bool)] = &[
        ("Compiles; EN0401", true),
        ("EN0401; compiles, and prints `1`", true),
        ("Prints `x` then `y`", true),
        ("EN0401 (twin compiles)", false),
        ("EN0401 (a (nested) aside that compiles) here", false),
        ("EN0401 at `compiles`", false),
        ("EN0401 at ``a `compiles` b``", false),
        ("chosen at compile time", false),
        ("it reprints nothing", false),
        ("EN0401 `` x ` compiles", true),
    ];
    for (cell, wanted) in compiles {
        let (cell, wanted) = (*cell, *wanted);
        h.case(
            format!("covers/says a program compiles: {cell:?}"),
            move || {
                assert_eq!(says_compiles(cell), wanted);
            },
        );
    }
    let compiles_m3: &[(&str, bool)] = &[
        ("Compiles; EN0401", true),
        ("Compile and print `[3, 4]`", true),
        ("Compile; print `9`, `1` and `1`", true),
        ("the forms compile, as the near-miss", true),
        ("EN0401 (twins compile)", false),
        ("chosen at compile time", false),
        ("chosen at compile-time", false),
        ("EN0706 at `print`", false),
        ("a compiler bug", false),
    ];
    for (cell, wanted) in compiles_m3 {
        let (cell, wanted) = (*cell, *wanted);
        h.case(
            format!("covers/M3: says its programs compile: {cell:?}"),
            move || {
                assert_eq!(says_compiles_m3(cell), wanted);
            },
        );
    }
    let leading: &[(&str, Option<&[&str]>)] = &[
        ("`F1`: x", Some(&["F1"])),
        ("`INF-06`, `MR-6`: x", Some(&["INF-06", "MR-6"])),
        ("`D20-core-1 both`: x", Some(&["D20-core-1 both"])),
        ("`f(x)` with y", None),
        ("`F1` and more", None),
        ("`F1`, more: x", None),
        ("`-x`: y", None),
        ("``: y", None),
        ("F1: x", None),
    ];
    for (cell, wanted) in leading {
        let (cell, wanted) = (*cell, *wanted);
        h.case(format!("covers/the IDs of {cell:?}"), move || {
            let wanted = wanted.map(|ids| ids.iter().map(|id| (*id).to_owned()).collect());
            assert_eq!(leading_ids(cell), wanted);
        });
    }
    let split: &[(&str, &[&str])] = &[
        ("| a | b |", &["a", "b"]),
        ("| `T \\| null` | b |", &["`T \\| null`", "b"]),
        ("| a \\\\| b |", &["a \\\\", "b"]),
        ("| a | b", &["a", "b"]),
    ];
    for (row, wanted) in split {
        let (row, wanted) = (*row, *wanted);
        h.case(format!("covers/the cells of {row:?}"), move || {
            assert_eq!(row_cells(row), wanted);
        });
    }
    let codes: &[(&str, &[&str])] = &[
        ("EN0401 and EN0455, EN0401 again", &["EN0401", "EN0455"]),
        ("`EN0701` at x", &["EN0701"]),
        ("EN04011 XEN0401 EN040", &[]),
        ("(twin E0308) EN1006.", &["EN1006"]),
    ];
    for (cell, wanted) in codes {
        let (cell, wanted) = (*cell, *wanted);
        h.case(format!("covers/the codes named in {cell:?}"), move || {
            let found: Vec<String> = named_codes(cell).into_iter().collect();
            assert_eq!(found, wanted);
        });
    }
}

// ---------------------------------------------------------------------------------
// The M3 gates' fakes.

/// A fake TESTING document for M3's reading of the attack rows: `A-1` names only a
/// phase 2 code, `A-2` a phase 3 code beside it, `A-3` no code but prints, `A-4` a
/// phase 3 code and compiles, `A-5` the phase 3 code only to say it does not fire,
/// and `R-1` is a reload scenario.
const ATTACK_DOC_M3: &str = "\
**The attack review of the applied design.** Prose.

| Fixture | Must give |
|---|---|
| `A-1`: `f(x)` | EN9701 at `x` |
| `A-2`: `g()` | EN9701; EN9706 at `g` |
| `A-3`: `h()` | Compiles and prints `1` |
| `A-4`: `k()` | EN9706, and compiles |
| `A-5`: `m()` | EN9701, and no EN9706 |

| Scenario | Must give |
|---|---|
| `R-1`: v2 reloads | EN9706 |

**Hermeticity:** after.
";

/// The codes of [`ATTACK_DOC_M3`] as M3 reads them: EN9701 of phase 2, EN9706 of
/// phase 3, both gated.
fn fake_info_m3(name: &str) -> Option<(bool, Milestone)> {
    match name {
        "EN9701" => Some((true, Milestone::M2)),
        "EN9706" => Some((true, Milestone::M3)),
        _ => None,
    }
}

/// The same as M2 reads them: EN9706, of phase 3, is not gated.
fn fake_info_m2(name: &str) -> Option<(bool, Milestone)> {
    fake_info_m3(name).map(|(gated, since)| (gated && since == Milestone::M2, since))
}

/// A fake document with a row of each shape the table gate reads: one named by its
/// ID, two whose first 40 characters are one, a numbered row, a beside row, a row
/// due at M4, one with no line, a MIR-level row and one whose excuse says it
/// compiles.
const TABLE_DOC: &str = "\
Intro.

**Named fixtures.** Prose.

| Fixture | Must give |
|---|---|
| `X-1`: `f()` | EN9701; compiles |
| `g()` and more words that make the cell long enough here | EN9702 at `g` |
| `g()` and more words that make the cell long enough there | Prints `1`, and no EN9702 |
| `f1`-`f3`, three programs | EN9701; compiles |
| `B-1`: beside, an attack row | EN9701 |
| `h()` alone | EN9704 |
| `k()` a panic at run time | Panic |
| `.mir`: a body | EN9701 |
| `m()` over many turns | No EN9702: each turn binds anew |

**The attack review of the applied design.** Rows sit beside it in the tables above (`B-1`).

**Hermeticity:** after.
";

const TABLE_EXCUSES: &[TableExcuse] = &[
    (
        "`g()` and more words that make the cell long enough there",
        "EN9702",
        false,
    ),
    ("`m()` over many turns", "EN9702", true),
];

/// [`TABLE_DOC`]'s rows gated over fixtures of each kind that matters: `X-1` named
/// after its ID; the first `g()` row claimed; the second with no fixture; `f1` and
/// `f2` claimed, `f3` only named, which no program of a numbered row counts; the
/// M4 row `h()` passing already; and two claims that name no single row.
fn table_fake(current: Milestone) -> (GateReport, Vec<String>) {
    let rows = table_rows(TABLE_DOC, &fake_info, TABLE_EXCUSES, M3_LINES_SINCE).expect("reads");
    let cells = table_cells(TABLE_DOC).expect("reads");
    let fixtures = [
        ("tests/compile/EN9701/x-1.fail.en", "x //~ EN9701\n"),
        ("tests/compile/EN9701/x-1.pass.en", "y\n"),
        (
            "tests/compile/EN9702/g.fail.en",
            "//! row: `g()` and more words that make the cell long enough h\nx //~ EN9702\n",
        ),
        (
            "tests/compile/EN9701/f1.fail.en",
            "//! row: `f1`-`f3`, three programs\nx //~ EN9701\n",
        ),
        (
            "tests/compile/EN9701/f2.pass.en",
            "//! row: `f1`-`f3`, three programs\ny\n",
        ),
        ("tests/compile/EN9701/f3.pass.en", "y\n"),
        (
            "tests/compile/EN9704/h.fail.en",
            "//! row: `h()` alone\nx //~ EN9704\n",
        ),
        (
            "tests/compile/EN9702/bad.pass.en",
            "//! row: `g()` and more words that make the cell long\n//! row: nothing\ny\n",
        ),
    ];
    let claiming: Vec<Claiming> = fixtures
        .iter()
        .map(|(path, text)| fake_claiming(path, text))
        .collect();
    let fires: Vec<(&str, String)> = [
        ("tests/compile/EN9701/x-1.fail.en", "EN9701", 1),
        ("tests/compile/EN9702/g.fail.en", "EN9702", 2),
        ("tests/compile/EN9701/f1.fail.en", "EN9701", 2),
        ("tests/compile/EN9704/h.fail.en", "EN9704", 2),
    ]
    .iter()
    .map(|(path, code, line)| (*path, fired_at(path, code, *line)))
    .collect();
    let cli = fake_cli(&fires, &[]);
    let run = |place: &Place, args: &[String]| cli.run(place, args);
    let evidence = Evidence {
        fixtures: &claiming,
        run: &run,
    };
    (
        gate_tables(&rows, &cells, &evidence, current),
        claim_problems(&claiming, &cells),
    )
}

/// Fake `H` rows: `H01` claimed by a near-miss that passes, `H02` by a firing
/// fixture that does not fire, `H03` due at M4 and passing already.
fn h_fake(current: Milestone) -> GateReport {
    let ids: Vec<String> = ["H01", "H02", "H03"].map(str::to_owned).to_vec();
    let due = h_lines_due(&ids, &[("H03", Milestone::M4, "later")], M3_LINES_SINCE)
        .expect("the excuse names a row");
    let fixtures = [
        fake_claiming("tests/compile/EN9701/h01.pass.en", "//! covers: H01\ny\n"),
        fake_claiming(
            "tests/compile/EN9701/h02.fail.en",
            "//! covers: H02\nx //~ EN9701\n",
        ),
        fake_claiming("tests/compile/EN9701/h03.pass.en", "y\n//! covers: H03\n"),
    ];
    let cli = fake_cli(&[], &[]);
    let run = |place: &Place, args: &[String]| cli.run(place, args);
    let evidence = Evidence {
        fixtures: &fixtures,
        run: &run,
    };
    gate_h_rows(&due, &evidence, current)
}

/// Every fixture name the rows of TESTING 18 give: the slugs of the attack rows'
/// IDs in both readings, of the table rows' IDs, and the numbered programs.
fn real_row_names() -> Vec<String> {
    let mut names: BTreeSet<String> = BTreeSet::new();
    for row in real_attack_rows().iter().chain(&real_attack_rows_m3()) {
        names.extend(row.ids.iter().map(|id| slug(id)));
    }
    let (rows, _) = real_table_rows();
    for row in &rows {
        names.extend(row.ids.iter().map(|id| slug(id)));
        names.extend(row.programs.iter().map(|(program, _)| program.clone()));
    }
    names.into_iter().collect()
}

/// How many data rows TESTING 18's tables before the attack reviews have, how many
/// of them the gate asks fixtures for, and their firing lines; and how many attack
/// rows M3's reading adds lines to, and the firing lines it adds.
const TABLE_CELLS: usize = 237;
const TABLE_GATED_ROWS: usize = 196;
const TABLE_FIRING_LINES: usize = 172;
const ATTACK_M3_ROWS: usize = 207;
const ATTACK_M3_FIRING_LINES: usize = 184;

/// The table rows of TESTING 18 today whose first cell opens with IDs, by first ID,
/// in document order.
const TABLE_IDS: &[&str] = &[
    "LTK-4",
    "S2-23-rerun",
    "S2-25-pair",
    "TK-01-dup",
    "TK-01-lastTwice",
    "TK-01-nested",
    "TK-01-two-turns",
    "TK-01-tuple-arg",
    "TK-01-split-wrap",
    "TK-01-split-written",
    "TK-01-local",
    "TK-01-local-stale",
    "TK-01-local-kill",
    "TK-01-pick",
    "TK-01-owned-fields",
    "TK-01-own-view",
    "TK-01-pick-param",
    "TK-01-copy-join",
    "TK-01-field-copy-join",
    "TK-01-repoint",
    "TK-01-local-ref",
    "TK-03-first-two",
    "TK-03-last-two",
    "TK-03-tail",
    "TK-03-tail-mixed",
    "TK-03-tail-mixed-join",
    "TK-03-two-loops",
    "TK-03-copied-ref",
    "TK-03-copied-ref-join",
    "TK-03-stale-join",
    "TK-03-whole-join",
    "TK-03-field-join",
    "TK-03-mark-literal",
    "TK-03-mark-rename",
    "TK-03-fields-of-turn",
    "TK-03-inner-pair",
    "HOLD-through",
    "TK-02-reassign-break",
    "LTK-5",
    "S2-14-const",
    "S2-24-narrowed",
    "h06",
    "w06b",
    "h5",
    "a4",
    "b1",
    "b2",
    "b6",
    "b4",
    "b5",
    "a5",
    "b11",
    "b13",
    "l8",
    "l9",
    "b8",
    "b9",
    "b10",
    "a7",
];

pub fn register_m3(h: &mut Harness) {
    h.case(
        "covers/M3: every attack row's phase 3 codes and near-misses have their fixtures",
        || {
            let lines = &real_m3_lines()[0].1;
            let report = gate_lines(lines, CURRENT_MILESTONE);
            assert!(report.is_clean(), "\n{report}");
        },
    );
    h.case(
        "covers/M3: every row of the named-fixture, for...of and inferred-permission tables has its fixtures",
        || {
            let lines = &real_m3_lines()[1].1;
            let report = gate_lines(lines, CURRENT_MILESTONE);
            assert!(report.is_clean(), "\n{report}");
        },
    );
    h.case("covers/M3: every H row of SPEC 5.8 is covered", || {
        let lines = &real_m3_lines()[2].1;
        let report = gate_lines(lines, CURRENT_MILESTONE);
        assert!(report.is_clean(), "\n{report}");
    });
    h.case(
        "covers/M3: H40, H41 and the type-parameter row's EN0607 already pass, as the \
         bump will ask",
        || {
            let all = real_m3_lines();
            let status = |gate: usize, id: &str| {
                (all[gate].1.iter())
                    .find(|line| line.id.as_str() == id || line.id.ends_with(id))
                    .map(|line| line.status)
            };
            assert_eq!(status(2, "H40 covered"), Some(FixtureStatus::Passing));
            assert_eq!(status(2, "H41 covered"), Some(FixtureStatus::Passing));
            let row = (all[1].1.iter())
                .find(|line| {
                    line.id.contains("function steal<T extends Base>")
                        && line.id.ends_with("EN0607")
                })
                .map(|line| line.status);
            assert_eq!(row, Some(FixtureStatus::Passing));
        },
    );
    h.case(
        "covers/M3: every row claim names exactly one row of the tables",
        || {
            let (_, cells) = real_table_rows();
            assert_eq!(
                claim_problems(&real_fixtures(), &cells),
                Vec::<String>::new()
            );
        },
    );
    h.case(
        "covers/M3: no row's fixture name is another row's with a number",
        || {
            assert_eq!(
                numbered_names(&real_row_names()),
                Vec::<(String, String)>::new()
            );
        },
    );
    h.case(
        "covers/M3: before the bump no M3 line is due, and at the bump every one is",
        || {
            // What the bump that closes M3 does to each M3 gate, simulated on the
            // real fixtures: today every line is deferred, so missing evidence fails
            // nothing; at M3 every line is enforced, and each one whose evidence
            // does not pass is a gap.
            for (name, lines) in real_m3_lines() {
                assert!(!lines.is_empty(), "{name}: no lines");
                assert!(
                    lines.iter().all(|line| line.since >= M3_LINES_SINCE),
                    "{name}: a line due before M3"
                );
                assert_eq!(
                    gate_lines(&lines, Milestone::M2).enforced,
                    0,
                    "{name}: a line due at M2"
                );
                for current in [CURRENT_MILESTONE, Milestone::M3] {
                    let problems = bump_problems(&lines, current);
                    assert!(problems.is_empty(), "{name} at {current}: {problems:?}");
                }
                let due = lines
                    .iter()
                    .filter(|line| line.since <= Milestone::M3)
                    .count();
                let at_bump = gate_lines(&lines, Milestone::M3);
                assert_eq!(at_bump.enforced, due, "{name}");
                assert!(at_bump.stale.is_empty(), "{name}: {at_bump}");
                // A line stays deferred at M3 only for a code, or an H row, that a
                // later milestone brings: the floor is M3 itself.
                for line in lines.iter().filter(|line| line.since > Milestone::M3) {
                    let later_code = line
                        .id
                        .rsplit(' ')
                        .next()
                        .and_then(Code::from_name)
                        .is_some_and(|code| code.since() == line.since);
                    let later_row = H_LATER.iter().any(|(id, since, _)| {
                        line.id == format!("{id} covered") && *since == line.since
                    });
                    let later_near_miss = NEAR_MISS_LATER.iter().any(|(id, since, _)| {
                        line.id == format!("{id} near-miss") && *since == line.since
                    });
                    assert!(
                        later_code || later_row || later_near_miss,
                        "{name}: {} is due at {}",
                        line.id,
                        line.since
                    );
                }
            }
            assert_eq!(M3_LINES_SINCE, Milestone::M3);
            // The H rows due later stay deferred at M3, each at its own milestone.
            let h = &real_m3_lines()[2].1;
            assert_eq!(
                h.iter().filter(|line| line.since > Milestone::M3).count(),
                H_LATER.len()
            );
        },
    );
    h.case("covers/M3: TESTING 18's tables are read whole", || {
        let (rows, cells) = real_table_rows();
        let ids: Vec<&str> = rows
            .iter()
            .filter(|row| !row.ids.is_empty())
            .map(|row| row.ids[0].as_str())
            .collect();
        assert_eq!(ids, TABLE_IDS);
        let programs: Vec<&str> = rows
            .iter()
            .flat_map(|row| row.programs.iter().map(|(program, _)| program.as_str()))
            .collect();
        let wanted: Vec<String> = (1..=6)
            .map(|n| format!("f{n}"))
            .chain((1..=8).map(|n| format!("h{n}")))
            .chain((1..=10).map(|n| format!("l{n}")))
            .collect();
        assert_eq!(programs, wanted);
        // Every row a claim may name, the beside rows among them, and the ones the
        // gate asks fixtures for.
        assert_eq!(cells.len(), TABLE_CELLS);
        assert_eq!(rows.len(), TABLE_GATED_ROWS);
        let firing: usize = rows.iter().map(|row| row.fires.len()).sum();
        assert_eq!(firing, TABLE_FIRING_LINES);
        // Each label names its row: an ID, or the shortest claim, which names it.
        for row in &rows {
            if row.ids.is_empty() {
                assert_eq!(claimed_row(&row.label, &cells), Ok(row.at), "{}", row.label);
            }
        }
        let testing = read("docs/TESTING.md");
        let text = |line: usize| testing.lines().nth(line - 1).expect("a line");
        let row = |id: &str| {
            rows.iter()
                .find(|row| row.ids.first().is_some_and(|f| f == id))
        };
        assert!(text(row("LTK-4").expect("LTK-4").line).starts_with("| `LTK-4`, nested"));
        // The beside rows are attack rows, and no table row.
        for id in ["WD-4", "EF-09", "OQ24-nested", "INF-12", "WD-2", "WD-5"] {
            assert!(row(id).is_none(), "{id}");
        }
    });
    h.case(
        "covers/M3: M3's reading of the attack rows is read whole",
        || {
            let rows = real_attack_rows_m3();
            assert_eq!(rows.len(), ATTACK_M3_ROWS);
            let firing: usize = rows.iter().map(|row| row.fires.len()).sum();
            assert_eq!(firing, ATTACK_M3_FIRING_LINES);
            assert!(
                rows.iter().flat_map(|row| &row.fires).all(|(code, _)| {
                    Code::from_name(code)
                        .is_some_and(|code| code.phase() == Phase::Borrows || code == Code::EN0804)
                }),
                "{rows:?}"
            );
            let row = |id: &str| rows.iter().find(|row| row.ids[0] == id).expect("a row");
            // A phase 3 row and its near-miss; an excused code; a phase 2 row that only
            // gains its phase 3 code.
            assert_eq!(row("FV-02-move").fires.len(), 2);
            assert_eq!(row("BC-08-readonly").near_miss, Some(Milestone::M3));
            assert!(
                row("FV-02-alias-other")
                    .fires
                    .iter()
                    .all(|(code, _)| code != "EN0614")
            );
            // No reload scenario is read.
            for id in ["D20E-07", "S2-19-pinned", "C4-06-adopt", "VI-09-reload"] {
                assert!(rows.iter().all(|row| row.ids[0] != id), "{id}");
            }
        },
    );
    h.case(
        "covers/M3: each `.mir` table row with a phase 3 code has a `.mir` fixture that \
         claims it and anchors the code (T:628), and the gate sees one that does not",
        || {
            let doc = read("docs/TESTING.md");
            let lines = mir_row_lines(&doc, &mir_fixtures(), &registry_info_m3)
                .unwrap_or_else(|error| panic!("TESTING 18's tables: {error}"));
            let ids: Vec<&str> = lines.iter().map(|l| l.id.as_str()).collect();
            assert!(
                ids.iter().any(|id| id.ends_with("`.mir` row, EN0707")),
                "{ids:?}"
            );
            let report = gate_lines(&lines, Milestone::M3);
            assert!(report.gaps.is_empty(), "{:?}", ids_of(&report.gaps));
            // With no fixture that claims it, the row's line is a gap at M3.
            let none = mir_row_lines(&doc, &[], &registry_info_m3).expect("reads");
            let report = gate_lines(&none, Milestone::M3);
            assert!(!report.gaps.is_empty());
            // A claim of the row that anchors another code proves nothing.
            let other = vec![(
                "x.mir".to_owned(),
                "// row: `.mir`: `(*(x as Present).0).f` and `*((*_env).i)` with overlapping\n\
                 _1 = const 0: i64; //~ EN0706\n"
                    .to_owned(),
            )];
            let lines = mir_row_lines(&doc, &other, &registry_info_m3).expect("reads");
            let t628 = (lines.iter())
                .find(|l| l.id.ends_with("EN0707"))
                .expect("the line");
            assert_eq!(t628.status, FixtureStatus::Missing);
        },
    );
    h.case(
        "covers/M3: each later H row's milestone, read whole",
        || {
            let found: Vec<(&str, Milestone)> =
                H_LATER.iter().map(|(id, m, _)| (*id, *m)).collect();
            assert_eq!(
                found,
                [
                    ("H09", Milestone::M5),
                    ("H13", Milestone::M9),
                    ("H15", Milestone::M4),
                    ("H17", Milestone::M5),
                    ("H25", Milestone::M4),
                    ("H35", Milestone::M4),
                ]
            );
            assert!(H_LATER.iter().all(|(_, _, why)| !why.is_empty()));
        },
    );
    h.case(
        "covers/M3: an H line takes only a claim of its own ID, never a longer one that \
         starts with it",
        || {
            let due = vec![("H01".to_owned(), Milestone::M3)];
            let fixtures = [fake_claiming(
                "tests/compile/EN9701/h010.pass.en",
                "//! covers: H010\ny\n",
            )];
            let cli = fake_cli(&[], &[]);
            let run = |place: &Place, args: &[String]| cli.run(place, args);
            let evidence = Evidence {
                fixtures: &fixtures,
                run: &run,
            };
            let lines = h_row_lines(&due, &evidence);
            assert_eq!(lines[0].status, FixtureStatus::Missing);
        },
    );
    h.case("covers/M3: SPEC 5.8's H rows are H01 to H42", || {
        let due = real_h_due();
        let ids: Vec<&str> = due.iter().map(|(id, _)| id.as_str()).collect();
        let wanted: Vec<String> = (1..=42).map(|n| format!("H{n:02}")).collect();
        assert_eq!(ids, wanted);
        let later: Vec<&str> = due
            .iter()
            .filter(|(_, since)| *since > Milestone::M3)
            .map(|(id, _)| id.as_str())
            .collect();
        assert_eq!(later, ["H09", "H13", "H15", "H17", "H25", "H35"]);
    });
    h.case(
        "covers/M3: an H excuse must name a row and a later milestone",
        || {
            let ids: Vec<String> = ["H01".to_owned()].to_vec();
            assert_eq!(
                h_lines_due(&ids, &[("H02", Milestone::M4, "x")], Milestone::M3),
                Err("H_LATER names H02, which is no H row".to_owned())
            );
            assert_eq!(
                h_lines_due(&ids, &[("H01", Milestone::M3, "x")], Milestone::M3),
                Err("H_LATER gives H01 M3, which is not after M3".to_owned())
            );
        },
    );
    h.case(
        "covers/M3: a near-miss excuse must name a row's near-miss and a later milestone",
        || {
            let row = |id: &str, near_miss: Option<Milestone>| AttackRow {
                ids: vec![id.to_owned()],
                line: 1,
                fires: Vec::new(),
                near_miss,
            };
            let rows = vec![row("A-1", Some(Milestone::M3)), row("B-1", None)];
            let later = |id: &'static str, m: Milestone| [(id, m, "x")];
            assert_eq!(
                defer_near_misses(rows.clone(), &later("A-1", Milestone::M4), Milestone::M3)
                    .map(|rows| rows.iter().map(|r| r.near_miss).collect::<Vec<_>>()),
                Ok(vec![Some(Milestone::M4), None])
            );
            assert_eq!(
                defer_near_misses(rows.clone(), &later("B-1", Milestone::M4), Milestone::M3),
                Err("NEAR_MISS_LATER names B-1, which needs no near-miss".to_owned())
            );
            assert_eq!(
                defer_near_misses(rows.clone(), &later("C-1", Milestone::M4), Milestone::M3),
                Err("NEAR_MISS_LATER names C-1, which needs no near-miss".to_owned())
            );
            assert_eq!(
                defer_near_misses(rows, &later("A-1", Milestone::M3), Milestone::M3),
                Err("NEAR_MISS_LATER gives A-1 M3, which is not after M3".to_owned())
            );
            // The real excuse defers exactly the V-ME-10-err near-miss, to M4.
            let deferred: Vec<(String, Option<Milestone>)> = real_attack_rows_m3()
                .into_iter()
                .filter(|row| row.near_miss.is_some_and(|m| m > Milestone::M3))
                .map(|row| (row.ids[0].clone(), row.near_miss))
                .collect();
            assert_eq!(deferred, [("V-ME-10-err".to_owned(), Some(Milestone::M4))]);
        },
    );
    h.case("covers/M3: each H row case trips, and the bump makes it due", || {
        assert_eq!(
            h_fake(Milestone::M3).to_string(),
            "gap: H02 covered has a failing fixture (since M3, current M3)\n"
        );
        assert_eq!(ids_of(&h_fake(Milestone::M3).early), ["H03 covered"]);
        let report = h_fake(Milestone::M2);
        assert_eq!(
            report.to_string(),
            "stale: H03 covered claims a passing fixture before its milestone (since M4, current M2)\n"
        );
        assert_eq!(ids_of(&report.early), ["H01 covered"]);
        assert_eq!((report.enforced, report.deferred), (0, 3));
    });
    h.case("covers/M3: the attack rows as M3 reads them", || {
        let m2 = attack_rows(ATTACK_DOC_M3, &fake_info_m2, &[]).expect("reads");
        let ids: Vec<&str> = m2.iter().map(|row| row.ids[0].as_str()).collect();
        assert_eq!(ids, ["A-1", "A-2", "A-5"]);
        let excuses = [("A-5", "EN9706", None)];
        let m3 =
            attack_rows_from(ATTACK_DOC_M3, &fake_info_m3, &excuses, Milestone::M3).expect("reads");
        // Every line due at M3 at the earliest, and the reload scenario left out.
        let ids: Vec<&str> = m3.iter().map(|row| row.ids[0].as_str()).collect();
        assert_eq!(ids, ["A-1", "A-2", "A-3", "A-4", "A-5"]);
        assert!(
            m3.iter()
                .flat_map(|row| &row.fires)
                .all(|(_, since)| *since == Milestone::M3)
        );
        let row = |id: &str, fires: &[&str], near_miss: Option<Milestone>| AttackRow {
            ids: vec![id.to_owned()],
            line: ATTACK_DOC_M3
                .lines()
                .position(|line| line.starts_with(&format!("| `{id}`")))
                .expect("a line")
                + 1,
            fires: fires
                .iter()
                .map(|code| ((*code).to_owned(), Milestone::M3))
                .collect(),
            near_miss,
        };
        let due = Some(Milestone::M3);
        assert_eq!(
            added_rows(&m2, &m3),
            [
                row("A-2", &["EN9706"], None),
                row("A-3", &[], due),
                row("A-4", &["EN9706"], due),
                row("A-5", &[], due),
            ]
        );
    });
    h.case(
        "covers/M3: the table rows are read by the plan's rule",
        || {
            let rows =
                table_rows(TABLE_DOC, &fake_info, TABLE_EXCUSES, M3_LINES_SINCE).expect("reads");
            let labels: Vec<&str> = rows.iter().map(|row| row.label.as_str()).collect();
            assert_eq!(
                labels,
                [
                    "X-1",
                    "`g()` and more words that make the cell long enough h",
                    "`g()` and more words that make the cell long enough t",
                    "`f1`-`f3`, three programs",
                    "`h()` alone",
                    "`m()` over many turns",
                ]
            );
            let shapes: Vec<(usize, Option<Milestone>, usize)> = rows
                .iter()
                .map(|row| (row.fires.len(), row.near_miss, row.programs.len()))
                .collect();
            let m3 = Some(Milestone::M3);
            assert_eq!(
                shapes,
                [
                    (1, m3, 0),
                    (1, None, 0),
                    (0, m3, 0),
                    (1, m3, 3),
                    (1, None, 0),
                    (0, m3, 0)
                ]
            );
            assert_eq!(table_cells(TABLE_DOC).map(|cells| cells.len()), Ok(9));
            // A phase 2 code is due at M3, a later code at its own milestone.
            assert_eq!(rows[0].fires, [("EN9701".to_owned(), Milestone::M3)]);
            assert_eq!(rows[4].fires, [("EN9704".to_owned(), Milestone::M4)]);
            // An excuse that names no row, several rows, or a code its row does not give.
            let errors = [
                (
                    ("nothing", "EN9702", false),
                    "the excuse \"nothing\" names 0 rows",
                ),
                (
                    ("`g()` and more words", "EN9702", false),
                    "the excuse \"`g()` and more words\" names 2 rows",
                ),
                (
                    ("X-1", "EN9702", false),
                    "line 7: the row \"X-1\" gates no EN9702",
                ),
            ];
            for (excuse, error) in errors {
                assert_eq!(
                    table_rows(TABLE_DOC, &fake_info, &[excuse], M3_LINES_SINCE),
                    Err(error.to_owned())
                );
            }
        },
    );
    h.case("covers/M3: each table row case trips, and the bump makes it due", || {
        let (report, problems) = table_fake(Milestone::M3);
        assert_eq!(
            report.to_string(),
            "gap: `g()` and more words that make the cell long enough t near-miss has no fixture (since M3, current M3)\n\
             gap: `f1`-`f3`, three programs program f3 has no fixture (since M3, current M3)\n\
             gap: `m()` over many turns near-miss has no fixture (since M3, current M3)\n"
        );
        assert_eq!((report.enforced, report.deferred), (10, 1));
        assert_eq!(ids_of(&report.early), ["`h()` alone EN9704"]);
        assert_eq!(
            problems,
            [
                "tests/compile/EN9702/bad.pass.en: `row: `g()` and more words that make the cell long` names 2 rows of the tables; claim more of the first cell",
                "tests/compile/EN9702/bad.pass.en: `row: nothing` names no row of the tables",
            ]
        );
        // Before the bump the same evidence is early, its absence no gap, and a line
        // two milestones ahead that passes is stale.
        let (report, _) = table_fake(Milestone::M2);
        assert_eq!(
            report.to_string(),
            "stale: `h()` alone EN9704 claims a passing fixture before its milestone (since M4, current M2)\n"
        );
        assert_eq!((report.enforced, report.deferred), (0, 11));
        assert_eq!(
            ids_of(&report.early),
            [
                "X-1 EN9701",
                "X-1 near-miss",
                "`g()` and more words that make the cell long enough h EN9702",
                "`f1`-`f3`, three programs EN9701",
                "`f1`-`f3`, three programs near-miss",
                "`f1`-`f3`, three programs program f1",
                "`f1`-`f3`, three programs program f2",
            ]
        );
    });
    let ids: &[(&str, &[&str])] = &[
        ("`OQ12-fn`: x", &["OQ12-fn"]),
        ("`LTK-4`, nested loops", &["LTK-4"]),
        ("`a7`, `a10`, `a12`: reads", &["a7", "a10", "a12"]),
        ("`h06`, the loop; `b3`, the same", &["h06"]),
        ("`HOLD-through`: a `Bag`", &["HOLD-through"]),
        ("`Atomic64` at `i486`", &[]),
        ("`unsafe`, `@requires`, `declare`", &[]),
        ("`codePointAt` on bytes", &[]),
        ("`f1`-`f6`, loop bindings", &[]),
        ("`0xB8000 as *u16`, `x`", &[]),
        ("`300 as u8`", &[]),
        ("The owner's form: `x`", &[]),
    ];
    for (cell, wanted) in ids {
        let (cell, wanted) = (*cell, *wanted);
        h.case(format!("covers/M3: the table IDs of {cell:?}"), move || {
            let wanted: Vec<String> = wanted.iter().map(|id| (*id).to_owned()).collect();
            assert_eq!(table_ids(cell), wanted);
        });
    }
    let numbered: &[(&str, &[&str])] = &[
        ("`f1`-`f3`, loop bindings", &["f1", "f2", "f3"]),
        ("`l9`-`l11`, more", &["l9", "l10", "l11"]),
        ("`f1`-`f3` loop bindings", &[]),
        ("`f1`-`g3`, mixed", &[]),
        ("`f3`-`f1`, backwards", &[]),
        ("`f1`-`f1`, one program as a range", &[]),
        ("`f01`-`f3`, zero", &[]),
        ("`F1`-`F3`, upper", &[]),
        ("`f1`: one", &[]),
    ];
    for (cell, wanted) in numbered {
        let (cell, wanted) = (*cell, *wanted);
        h.case(format!("covers/M3: the programs of {cell:?}"), move || {
            let wanted: Vec<String> = wanted.iter().map(|id| (*id).to_owned()).collect();
            assert_eq!(numbered_programs(cell), wanted);
        });
    }
    h.case(
        "covers/M3: a claim names a row by the opening of its first cell",
        || {
            let long = "Under `p != null`: `for (const x of &p) { p = null; }`";
            let other = "Under `p != null`: `for (const x of &p) { p.push(1); }`";
            let cells = [
                long.to_owned(),
                other.to_owned(),
                "`x`".to_owned(),
                "`T \\| null` y".to_owned(),
            ];
            // Forty characters of either open both rows; one more tells them apart.
            assert_eq!(
                long.chars().take(40).collect::<String>(),
                other.chars().take(40).collect::<String>()
            );
            assert!(claimed_row(&long[..40], &cells).is_err());
            assert_eq!(
                shortest_claim(&cells, 0),
                "Under `p != null`: `for (const x of &p) { p ="
            );
            assert_eq!(claimed_row(&shortest_claim(&cells, 0), &cells), Ok(0));
            assert_eq!(
                shortest_claim(&cells, 1),
                "Under `p != null`: `for (const x of &p) { p."
            );
            // A short cell is claimed whole, never in part; an escaped pipe matches
            // either spelling.
            assert_eq!(claimed_row("`x`", &cells), Ok(2));
            assert!(claimed_row("`x", &cells).is_err());
            assert_eq!(claimed_row("`T | null` y", &cells), Ok(3));
            assert_eq!(claimed_row("`T \\| null` y", &cells), Ok(3));
            assert!(claim_fits(long, long) && !claim_fits("", long));
            assert_eq!(
                parse_row_claims("//! target: x\n//! row: `x` \ny\n  //! row:two\n"),
                ["`x`", "two"]
            );
            // Forty characters that end in a space, trimmed off the line, still count.
            let cells = [long.to_owned(), "`x`".to_owned()];
            assert_eq!(claimed_row(&long[..40], &cells), Ok(0));
            assert_eq!(
                claimed_row(&long[..38], &cells),
                Err(format!("`row: {}` names no row of the tables", &long[..38]))
            );
        },
    );
    h.case(
        "covers/M3: a row's fixture may carry a number, never another name",
        || {
            assert!(stem_names("tk-01-local", "tk-01-local"));
            assert!(stem_names("tk-01-local-2", "tk-01-local"));
            assert!(!stem_names("tk-01-local-stale", "tk-01-local"));
            assert!(!stem_names("tk-01-local-", "tk-01-local"));
            assert!(!stem_names("tk-01-locals", "tk-01-local"));
            let names = [
                "d20-core".to_owned(),
                "d20-core-2".to_owned(),
                "f1".to_owned(),
            ];
            assert_eq!(
                numbered_names(&names),
                [("d20-core-2".to_owned(), "d20-core".to_owned())]
            );
            // A fixture that claims a table row is that row's alone: `f1` of `f1`-`f6`
            // is no fixture of the attack row `F1`.
            let rows = attack_rows(ATTACK_DOC, &fake_info, FAKE_NOT_FIRED).expect("the fake reads");
            let path = "tests/compile/EN9701/a-1.fail.en";
            let fixtures = [fake_claiming(
                path,
                "//! row: some table row\nx //~ EN9701\n",
            )];
            let cli = fake_cli(&[(path, fired_at(path, "EN9701", 2))], &[]);
            let run = |place: &Place, args: &[String]| cli.run(place, args);
            let evidence = Evidence {
                fixtures: &fixtures,
                run: &run,
            };
            assert_eq!(
                gate_attack(&rows[..1], &evidence, Milestone::M2).to_string(),
                "gap: A-1 EN9701 has no fixture (since M2, current M2)\n"
            );
            // Without the claim, `a-1-2` is a fixture of `A-1`.
            let path = "tests/compile/EN9701/a-1-2.fail.en";
            let fixtures = [fake_claiming(path, "x //~ EN9701\n")];
            let cli = fake_cli(&[(path, fired_at(path, "EN9701", 1))], &[]);
            let run = |place: &Place, args: &[String]| cli.run(place, args);
            let evidence = Evidence {
                fixtures: &fixtures,
                run: &run,
            };
            assert!(gate_attack(&rows[..1], &evidence, Milestone::M2).is_clean());
        },
    );
    h.case(
        "covers/M3: a fixture that claims a beside row is that attack row's",
        || {
            // `B-1` sits beside the row it extends, in the tables: an attack row whose
            // fixture may claim it by its first cell, whatever its name.
            let rows = attack_rows_from(TABLE_DOC, &fake_info, &[], Milestone::M3).expect("reads");
            let ids: Vec<&str> = rows.iter().map(|row| row.ids[0].as_str()).collect();
            assert_eq!(ids, ["B-1"]);
            let cells = table_cells(TABLE_DOC).expect("reads");
            let places = table_places(TABLE_DOC).expect("reads");
            let path = "tests/compile/EN9701/beside.fail.en";
            let fixtures = [fake_claiming(
                path,
                "//! row: `B-1`: beside, an attack row\nx //~ EN9701\n",
            )];
            let cli = fake_cli(&[(path, fired_at(path, "EN9701", 2))], &[]);
            let run = |place: &Place, args: &[String]| cli.run(place, args);
            let evidence = Evidence {
                fixtures: &fixtures,
                run: &run,
            };
            let claims = resolve_claims(&fixtures, &cells);
            let claimed = |claiming: &Claiming, line: usize| {
                places
                    .get(&line)
                    .is_some_and(|&at| claims_at(&claims, claiming, at))
            };
            let lines = attack_lines(&rows, &evidence, &claimed);
            assert_eq!(gate_lines(&lines, Milestone::M3).to_string(), "");
            // Unclaimed, a fixture of another name is none of the row's.
            let lines = attack_lines(&rows, &evidence, &|_, _| false);
            assert_eq!(
                gate_lines(&lines, Milestone::M3).to_string(),
                "gap: B-1 EN9701 has no fixture (since M3, current M3)\n"
            );
        },
    );
    h.case("covers/M3: a report that hides a due line is seen", || {
        let line = |id: &str, since: Milestone, status: FixtureStatus| Line {
            id: id.to_owned(),
            since,
            status,
        };
        let lines = [
            line("a", Milestone::M3, FixtureStatus::Passing),
            line("b", Milestone::M3, FixtureStatus::Missing),
            line("c", Milestone::M4, FixtureStatus::Missing),
        ];
        assert_eq!(bump_problems(&lines, Milestone::M2), Vec::<String>::new());
        assert_eq!(bump_problems(&lines, Milestone::M3), Vec::<String>::new());
        // A report that drops the due line `b`, which lacks a passing fixture, or
        // that miscounts what it enforced, is seen.
        let mut dropped = gate_lines(&lines, Milestone::M3);
        dropped.gaps.clear();
        assert_eq!(
            report_problems(&lines, &dropped, Milestone::M3),
            vec!["gaps [], wanted [\"b\"]".to_owned()]
        );
        let mut miscounted = gate_lines(&lines, Milestone::M3);
        miscounted.enforced -= 1;
        assert_eq!(report_problems(&lines, &miscounted, Milestone::M3).len(), 1);
        assert_eq!(
            gate_lines(&lines, Milestone::M3).to_string(),
            "gap: b has no fixture (since M3, current M3)\n"
        );
        assert_eq!(gate_lines(&lines, Milestone::M2).to_string(), "");
    });
}
