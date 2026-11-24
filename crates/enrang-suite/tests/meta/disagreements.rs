//! TESTING 13's named intended disagreements with `rustc`, against the rows of
//! `corpus/rustc_disagreements.txt` (M3 plan f.7; TESTING 23's M3 item "`rustc` twin
//! disagreements all named").
//!
//! TESTING 13's paragraph that opens `**Named intended disagreements**` lists them,
//! separated by `;`, up to the sentence that begins the cases which are no
//! disagreement. Each item names its programs by the IDs of their TESTING 18 rows,
//! or, for three, by its words alone, which [`UNNAMED`] gives an ID. The corpus holds
//! one row per disagreement, in the order the paragraph names them, and no other: a
//! disagreement the document adds, or one it drops, trips here until the corpus
//! follows. Each row's outcomes must be the ones its TESTING 18 row gives, read from
//! the document, never from the compiler.
//!
//! Each row also needs evidence, M3's from the bump that closes M3 on, and early
//! before it (`gate_building`): its compile fixture must give Enrang's outcome
//! through `enrang check`, and its twin, `corpus/twins/<ID>.rs`, must exist. The
//! twins run only when `RUSTC_TWINS` is set and `rustc` is found, each giving the
//! stated `rustc` outcome; otherwise the run skips visibly, with a TESTING 20 notice
//! (`rustc` is a test-time oracle, and its use is nightly-scale, TESTING 13).

use std::collections::BTreeSet;
use std::env;

use enrang_diag::{CURRENT_MILESTONE, Milestone};
use enrang_testkit::{
    FixtureStatus, GateReport, Harness, TempDir, skip_oracle, tool, workspace_root,
};

use crate::covers::{
    Line, bump_problems, gate_lines, ids_of, leading_ids, named_codes, row_cells, says_compiles_m3,
    stem, stem_names, table_ids,
};
use crate::gating::{FakeCli, Run, fake_fixture, fixture_status};
use crate::support::{Fixture, Place, fixtures, read, run_cached};

/// The corpus of named disagreements.
pub const CORPUS: &str = "corpus/rustc_disagreements.txt";

/// The milestone of each row's evidence: TESTING 23's M3 row names the
/// disagreements.
pub const DISAGREEMENTS_SINCE: Milestone = Milestone::M3;

/// What opens TESTING 13's paragraph of named disagreements.
const HEAD: &str = "**Named intended disagreements** with `rustc`: ";

/// The sentence after the last named disagreement, which begins the cases that are
/// no disagreement.
const TAIL: &str = " A result with several reference parts";

/// The disagreements TESTING 13 names by their words and no ID, each with the ID its
/// corpus row takes (M3 plan f.7's choice) and the words that name it.
pub const UNNAMED: &[(&str, &str)] = &[
    ("NLL-3", "NLL problem case #3"),
    ("R1", "Enrang's own R1 rejections"),
    (
        "ONE-PART-WRITABLE",
        "bodies that form a writable result with one reference part",
    ),
];

/// TESTING 13's disagreements as read: their IDs in the order named, the item of the
/// paragraph that names each one, and the IDs the paragraph names afterwards only to
/// say they are no disagreement.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Named {
    pub ids: Vec<(String, String)>,
    pub not_disagreements: Vec<String>,
}

/// Whether a backticked word is a TESTING 18 row ID: letters, digits and `-`,
/// opening with a capital and holding a digit, as `F12` or `FV-02-alias`.
fn id_shaped(word: &str) -> bool {
    word.starts_with(|c: char| c.is_ascii_uppercase())
        && word.chars().all(|c| c.is_ascii_alphanumeric() || c == '-')
        && word.chars().any(|c| c.is_ascii_digit())
}

/// The row IDs a text writes between backticks, in order, each once.
fn ids_in(text: &str) -> Vec<String> {
    let mut seen = BTreeSet::new();
    text.split('`')
        .skip(1)
        .step_by(2)
        .filter(|word| id_shaped(word))
        .filter(|word| seen.insert(word.to_string()))
        .map(str::to_owned)
        .collect()
}

/// The items of a list separated by `; `, outside code spans and parentheses.
pub fn items(text: &str) -> Vec<String> {
    let mut found = Vec::new();
    let mut item = String::new();
    let (mut code, mut depth) = (false, 0usize);
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '`' => code = !code,
            '(' if !code => depth += 1,
            ')' if !code => depth = depth.saturating_sub(1),
            ';' if !code && depth == 0 && chars.peek() == Some(&' ') => {
                chars.next();
                found.push(std::mem::take(&mut item));
                continue;
            }
            _ => {}
        }
        item.push(c);
    }
    found.push(item);
    found
}

/// TESTING 13's named disagreements. A document whose paragraph lacks its opening
/// or the sentence after its list, an item that names no ID and is none of
/// `unnamed`, and an entry of `unnamed` whose words no item holds, or several do,
/// are errors.
pub fn named_disagreements(testing: &str, unnamed: &[(&str, &str)]) -> Result<Named, String> {
    let line = testing
        .lines()
        .find(|line| line.starts_with(HEAD))
        .ok_or_else(|| format!("no paragraph opens with {HEAD:?}"))?;
    let body = &line[HEAD.len()..];
    let (list, tail) = body
        .split_once(TAIL)
        .ok_or_else(|| format!("the paragraph has no sentence opening {TAIL:?}"))?;
    let list = items(list);
    let mut ids: Vec<(String, String)> = Vec::new();
    for item in &list {
        let words: Vec<&str> = unnamed
            .iter()
            .filter(|(_, words)| item.contains(words))
            .map(|(id, _)| *id)
            .collect();
        let named = ids_in(item);
        if words.is_empty() && named.is_empty() {
            let opening: String = item.chars().take(60).collect();
            return Err(format!(
                "a disagreement names no ID and none of the unnamed ones: {opening:?}"
            ));
        }
        for id in words
            .into_iter()
            .map(str::to_owned)
            .chain(named)
            .collect::<Vec<String>>()
        {
            if !ids.iter().any(|(had, _)| *had == id) {
                ids.push((id, item.clone()));
            }
        }
    }
    for (id, words) in unnamed {
        let holding = list.iter().filter(|item| item.contains(words)).count();
        if holding != 1 {
            return Err(format!("{holding} disagreements say {words:?}, named {id}"));
        }
    }
    let not_disagreements = ids_in(tail)
        .into_iter()
        .filter(|id| !ids.iter().any(|(had, _)| had == id))
        .collect();
    Ok(Named {
        ids,
        not_disagreements,
    })
}

/// An outcome as a corpus row states it.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Outcome {
    /// The program compiles.
    Compiles,
    /// It is rejected, with no code given (`rustc` only).
    Rejects,
    /// It is rejected with these codes.
    Codes(Vec<String>),
}

/// A row of the corpus.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CorpusRow {
    pub id: String,
    pub enrang: Outcome,
    pub rustc: Outcome,
    /// `tests/compile/<CODE or *>/<name>.fail.en` or `.pass.en`.
    pub fixture: String,
    pub twin: String,
}

/// Whether a word is an Enrang code, `EN` and four digits.
fn enrang_code(word: &str) -> bool {
    word.len() == 6 && word.starts_with("EN") && word[2..].bytes().all(|b| b.is_ascii_digit())
}

/// Whether a word is a `rustc` error code, `E` and four digits.
fn rustc_code(word: &str) -> bool {
    word.len() == 5 && word.starts_with('E') && word[1..].bytes().all(|b| b.is_ascii_digit())
}

fn outcome(text: &str, code: fn(&str) -> bool, rejects: bool) -> Result<Outcome, String> {
    match text {
        "compiles" => Ok(Outcome::Compiles),
        "rejects" if rejects => Ok(Outcome::Rejects),
        _ => {
            let codes: Vec<String> = text.split(' ').map(str::to_owned).collect();
            if codes.iter().all(|word| code(word)) {
                Ok(Outcome::Codes(codes))
            } else {
                Err(format!("{text:?} is no outcome"))
            }
        }
    }
}

/// The parts of a fixture column: the directory, a code or `*`, the name and whether
/// it is a near-miss.
fn fixture_parts(path: &str) -> Option<(&str, &str, bool)> {
    let rest = path.strip_prefix("tests/compile/")?;
    let (dir, file) = rest.split_once('/')?;
    let (name, near_miss) = match file.strip_suffix(".pass.en") {
        Some(name) => (name, true),
        None => (file.strip_suffix(".fail.en")?, false),
    };
    let dir_ok = dir == "*" || enrang_code(dir);
    let name_ok = !name.is_empty() && !name.contains('/');
    (dir_ok && name_ok).then_some((dir, name, near_miss))
}

/// The rows of a corpus text: comment lines (`#`) and blank lines left out, each
/// other line five fields separated by tabs, as the file's own comment says. A
/// malformed row, a fixture whose kind does not fit Enrang's outcome, a twin not at
/// `corpus/twins/<ID>.rs` and an ID given twice are errors.
pub fn parse_corpus(text: &str) -> Result<Vec<CorpusRow>, String> {
    let mut rows: Vec<CorpusRow> = Vec::new();
    for (index, line) in text.lines().enumerate() {
        let at = index + 1;
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let fields: Vec<&str> = line.split('\t').collect();
        let [id, enrang, rustc, fixture, twin] = fields[..] else {
            return Err(format!("line {at}: {} fields, not 5", fields.len()));
        };
        let id_ok = id.starts_with(|c: char| c.is_ascii_uppercase())
            && id.chars().all(|c| c.is_ascii_alphanumeric() || c == '-');
        if !id_ok {
            return Err(format!("line {at}: {id:?} is no ID"));
        }
        let enrang = outcome(enrang, enrang_code, false).map_err(|e| format!("line {at}: {e}"))?;
        let rustc = outcome(rustc, rustc_code, true).map_err(|e| format!("line {at}: {e}"))?;
        let Some((_, _, near_miss)) = fixture_parts(fixture) else {
            return Err(format!("line {at}: {fixture:?} is no compile fixture"));
        };
        if near_miss != (enrang == Outcome::Compiles) {
            return Err(format!(
                "line {at}: {fixture} cannot show {enrang:?}: a program that compiles is a \
                 `.pass.en`, one rejected a `.fail.en`"
            ));
        }
        if twin != format!("corpus/twins/{id}.rs") {
            return Err(format!(
                "line {at}: the twin of {id} is corpus/twins/{id}.rs"
            ));
        }
        if rows.iter().any(|row| row.id == id) {
            return Err(format!("line {at}: {id} has a row already"));
        }
        rows.push(CorpusRow {
            id: id.to_owned(),
            enrang,
            rustc,
            fixture: fixture.to_owned(),
            twin: twin.to_owned(),
        });
    }
    Ok(rows)
}

/// What is wrong with the corpus against the disagreements the document names: the
/// same IDs in the same order, with no row for an ID the document names only to say
/// it is no disagreement.
pub fn one_to_one(named: &Named, rows: &[CorpusRow]) -> Vec<String> {
    let wanted: Vec<&str> = named.ids.iter().map(|(id, _)| id.as_str()).collect();
    let have: Vec<&str> = rows.iter().map(|row| row.id.as_str()).collect();
    let mut problems = Vec::new();
    for id in &wanted {
        if !have.contains(id) {
            problems.push(format!("{id} is a named disagreement with no corpus row"));
        }
    }
    for id in &have {
        if named.not_disagreements.iter().any(|no| no == id) {
            problems.push(format!(
                "{id} has a corpus row, but TESTING 13 says it is no disagreement"
            ));
        } else if !wanted.contains(id) {
            problems.push(format!(
                "{id} has a corpus row, but TESTING 13 names no such disagreement"
            ));
        }
    }
    if problems.is_empty() && wanted != have {
        problems.push(format!(
            "the corpus rows are {have:?}, not in TESTING 13's order {wanted:?}"
        ));
    }
    problems
}

/// The "Must give" cell of the TESTING 18 row whose first cell opens with `id`.
fn row_result(testing: &str, id: &str) -> Option<String> {
    testing
        .lines()
        .filter(|line| line.starts_with("| `"))
        .map(row_cells)
        .find(|cells| {
            let first = &cells[0];
            leading_ids(first).is_some_and(|ids| ids.iter().any(|own| own == id))
                || table_ids(first).iter().any(|own| own == id)
        })
        .map(|cells| cells[1..].join(" | "))
}

/// What is wrong with a row's outcomes against the documents. A row of a named ID
/// must be one of TESTING 18's rows, whose cell names each of Enrang's codes, or
/// says a program compiles where Enrang's outcome is `compiles`, and each `rustc`
/// code must be named there or in TESTING 13's item. A row of `unnamed` follows
/// its item's words: `Enrang accepts` for `compiles`, and `` `rustc` accepts ``
/// for a twin that compiles.
pub fn outcome_problems(
    testing: &str,
    named: &Named,
    rows: &[CorpusRow],
    unnamed: &[(&str, &str)],
) -> Vec<String> {
    let mut problems = Vec::new();
    for row in rows {
        let Some((_, item)) = named.ids.iter().find(|(id, _)| *id == row.id) else {
            continue;
        };
        let id = &row.id;
        let unnamed = unnamed.iter().any(|(own, _)| own == id);
        let enrang_accepts = row.enrang == Outcome::Compiles;
        if unnamed {
            if item.contains("Enrang accepts") != enrang_accepts {
                problems.push(format!(
                    "{id}: TESTING 13's item does not say {:?}",
                    row.enrang
                ));
            }
            if item.contains("`rustc` accepts") != (row.rustc == Outcome::Compiles) {
                problems.push(format!(
                    "{id}: TESTING 13's item does not say rustc {:?}",
                    row.rustc
                ));
            }
            continue;
        }
        let Some(cell) = row_result(testing, id) else {
            problems.push(format!("{id}: no row of TESTING 18 opens with it"));
            continue;
        };
        match &row.enrang {
            Outcome::Compiles if !says_compiles_m3(&cell) => {
                problems.push(format!("{id}: its row says no program compiles"));
            }
            Outcome::Codes(codes) => {
                let said = named_codes(&cell);
                for code in codes.iter().filter(|code| !said.contains(*code)) {
                    problems.push(format!("{id}: its row never names {code}"));
                }
            }
            _ => {}
        }
        if let Outcome::Codes(codes) = &row.rustc {
            for code in codes {
                if !cell.contains(code.as_str()) && !item.contains(code.as_str()) {
                    problems.push(format!("{id}: neither its row nor TESTING 13 names {code}"));
                }
            }
        }
    }
    problems
}

/// The fixtures a corpus row's fixture column names: of its kind, in its directory
/// or any, named `<name>` or `<name>-<n>`.
fn row_fixtures<'f>(row: &CorpusRow, fixtures: &'f [Fixture]) -> Vec<&'f Fixture> {
    let Some((dir, name, near_miss)) = fixture_parts(&row.fixture) else {
        return Vec::new();
    };
    fixtures
        .iter()
        .filter(|fixture| fixture.near_miss == near_miss)
        .filter(|fixture| dir == "*" || fixture.code == dir)
        .filter(|fixture| stem_names(stem(fixture), name))
        .collect()
}

/// Whether a row's fixtures give Enrang's outcome: a near-miss that passes for
/// `compiles`, and for codes, for each code a firing fixture that anchors it and
/// fires as anchored.
fn fixture_status_of(row: &CorpusRow, fixtures: &[Fixture], run: &Run<'_>) -> FixtureStatus {
    let found = row_fixtures(row, fixtures);
    if found.is_empty() {
        return FixtureStatus::Missing;
    }
    let works = |fixture: &Fixture| fixture_status(fixture, run);
    match &row.enrang {
        Outcome::Codes(codes) => codes
            .iter()
            .map(|code| {
                found
                    .iter()
                    .map(|fixture| {
                        let anchors = matches!(&fixture.anchors,
                            Ok(anchors) if anchors.iter().any(|anchor| anchor.code == *code));
                        if anchors {
                            works(fixture)
                        } else {
                            FixtureStatus::Failing
                        }
                    })
                    .fold(FixtureStatus::Missing, FixtureStatus::best)
            })
            .fold(FixtureStatus::Passing, FixtureStatus::worst),
        _ => found
            .iter()
            .map(|fixture| works(fixture))
            .fold(FixtureStatus::Missing, FixtureStatus::best),
    }
}

/// Each row's lines of evidence: its fixture and its twin, both M3's.
pub fn evidence_lines(
    rows: &[CorpusRow],
    fixtures: &[Fixture],
    run: &Run<'_>,
    twin_exists: &dyn Fn(&str) -> bool,
) -> Vec<Line> {
    rows.iter()
        .flat_map(|row| {
            let twin = if twin_exists(&row.twin) {
                FixtureStatus::Passing
            } else {
                FixtureStatus::Missing
            };
            [
                Line {
                    id: format!("{} fixture", row.id),
                    since: DISAGREEMENTS_SINCE,
                    status: fixture_status_of(row, fixtures, run),
                },
                Line {
                    id: format!("{} twin", row.id),
                    since: DISAGREEMENTS_SINCE,
                    status: twin,
                },
            ]
        })
        .collect()
}

/// Whether a twin's run through `rustc` gives the outcome: `compiles` exits 0, any
/// rejection exits otherwise, and each code stated opens an `error[...]` of its
/// stderr.
pub fn twin_gives(outcome: &Outcome, code: i32, stderr: &str) -> bool {
    match outcome {
        Outcome::Compiles => code == 0,
        Outcome::Rejects => code != 0,
        Outcome::Codes(codes) => {
            code != 0
                && codes
                    .iter()
                    .all(|wanted| stderr.contains(&format!("error[{wanted}]")))
        }
    }
}

fn real_named() -> Named {
    named_disagreements(&read("docs/TESTING.md"), UNNAMED)
        .unwrap_or_else(|error| panic!("TESTING 13: {error}"))
}

fn real_rows() -> Vec<CorpusRow> {
    parse_corpus(&read(CORPUS)).unwrap_or_else(|error| panic!("{CORPUS}: {error}"))
}

fn twin_on_disk(path: &str) -> bool {
    workspace_root().join(path).is_file()
}

/// The real rows' lines of evidence.
pub fn real_lines() -> Vec<Line> {
    evidence_lines(&real_rows(), &fixtures(), &run_cached, &twin_on_disk)
}

/// The real rows' report at `current`.
pub fn real_report(current: Milestone) -> GateReport {
    gate_lines(&real_lines(), current)
}

/// The disagreements TESTING 13 names today, in order.
const NAMED_IDS: &[&str] = &[
    "NLL-3",
    "F12",
    "OQ25-order",
    "S2-22-copy",
    "R1",
    "ONE-PART-WRITABLE",
    "TK-02-reassign-break",
    "SLB-02-element",
    "TK-03-first-two",
    "TK-03-last-two",
    "TK-03-fields-of-turn",
    "TK-01-local-ref",
    "FV-02-alias",
    "FV-02-alias-peek",
    "FV-02-alias-split",
    "FV-02-reset",
    "FV-02-upcast-local",
    "FV-02-field-copy",
    "FV-02-through-ref",
    "FV-02-lost-store",
    "FV-02-skip",
    "FV-02-move",
    "D20-core-3",
    "FV-02-closure",
];

/// A fake TESTING 13 paragraph: an unnamed disagreement, items with IDs, a
/// semicolon inside a code span and one inside a parenthesis, and after the list an
/// ID that is both a disagreement and named among the cases that are not.
const FAKE_DOC: &str = "\
Intro.

**Named intended disagreements** with `rustc`: the old case, which Enrang accepts; \
a call order (`F1`, `F2`); a loop `a; b;` (`TK-1`); and a store (as `x; y` does) \
(`FV-1`, `F1`). A result with several reference parts is no disagreement (`INF-1`, \
`FV-1`).

| Fixture | Must give |
|---|---|
| `F1`: `f()` | EN9601 at `f` |
| `F2`: `g()` | Prints `1` (twin E0001) |
| `TK-1`: `h()` | Compiles |
| `FV-1`, `FV-1b`: `k()` | EN9602 |
";

const FAKE_UNNAMED: &[(&str, &str)] = &[("OLD-1", "the old case")];

fn fake_row(id: &str, enrang: &str, rustc: &str, fixture: &str) -> String {
    format!("{id}\t{enrang}\t{rustc}\t{fixture}\tcorpus/twins/{id}.rs\n")
}

/// A fake corpus for [`FAKE_DOC`], one row per disagreement, in order.
fn fake_corpus() -> String {
    [
        "# a comment\n\n".to_owned(),
        fake_row(
            "OLD-1",
            "compiles",
            "rejects",
            "tests/compile/*/old-1.pass.en",
        ),
        fake_row("F1", "EN9601", "compiles", "tests/compile/*/f1.fail.en"),
        fake_row("F2", "compiles", "E0001", "tests/compile/*/f2.pass.en"),
        fake_row(
            "TK-1",
            "compiles",
            "compiles",
            "tests/compile/*/tk-1.pass.en",
        ),
        fake_row(
            "FV-1",
            "EN9602",
            "compiles",
            "tests/compile/EN9602/fv-1.fail.en",
        ),
    ]
    .concat()
}

/// The fake rows' report at `current` over fixtures of each kind that matters:
/// `F1` fires in another directory under a numbered name; `F2`'s near-miss fails;
/// `TK-1` has none; `FV-1`'s fixture is in another directory than its row names;
/// `OLD-1` passes; and only `F1` and `F2` have twins.
fn fake_report(current: Milestone) -> GateReport {
    let rows = parse_corpus(&fake_corpus()).expect("the fake corpus reads");
    let fixtures = [
        fake_fixture("tests/compile/EN9601/f1-2.fail.en", "x //~ EN9601\n"),
        fake_fixture("tests/compile/EN9601/f2.pass.en", "y\n"),
        fake_fixture("tests/compile/EN9601/fv-1.fail.en", "x //~ EN9602\n"),
        fake_fixture("tests/compile/EN9601/old-1.pass.en", "y\n"),
    ];
    let cli = FakeCli::new([
        (
            "check tests/compile/EN9601/f1-2.fail.en",
            "error[EN9601]: fake\n --> tests/compile/EN9601/f1-2.fail.en:1:1\n",
        ),
        (
            "check tests/compile/EN9601/fv-1.fail.en",
            "error[EN9602]: fake\n --> tests/compile/EN9601/fv-1.fail.en:1:1\n",
        ),
    ])
    .breaking("check tests/compile/EN9601/f2.pass.en", 1, "");
    let run = |place: &Place, args: &[String]| cli.run(place, args);
    let twins = |path: &str| path.ends_with("/F1.rs") || path.ends_with("/F2.rs");
    gate_lines(&evidence_lines(&rows, &fixtures, &run, &twins), current)
}

pub fn register(h: &mut Harness) {
    h.case(
        "disagreements/TESTING 13 names its disagreements as the corpus rows, one to one",
        || {
            assert_eq!(
                one_to_one(&real_named(), &real_rows()),
                Vec::<String>::new()
            );
        },
    );
    h.case(
        "disagreements/each corpus row states the outcomes its rows give",
        || {
            let testing = read("docs/TESTING.md");
            assert_eq!(
                outcome_problems(&testing, &real_named(), &real_rows(), UNNAMED),
                Vec::<String>::new()
            );
        },
    );
    h.case(
        "disagreements/every reached row's fixture gives Enrang's outcome, and its twin exists",
        || {
            let report = real_report(CURRENT_MILESTONE);
            assert!(report.is_clean(), "\n{report}");
        },
    );
    h.case(
        "disagreements/before the bump no row is due, and at the bump every one is",
        || {
            let lines = real_lines();
            assert_eq!(lines.len(), 2 * NAMED_IDS.len());
            assert_eq!(gate_lines(&lines, Milestone::M2).enforced, 0);
            for current in [CURRENT_MILESTONE, Milestone::M3] {
                let problems = bump_problems(&lines, current);
                assert!(problems.is_empty(), "{current}: {problems:?}");
            }
            assert_eq!(gate_lines(&lines, Milestone::M3).enforced, lines.len());
        },
    );
    h.case(
        "disagreements/TESTING 13's disagreements are read whole",
        || {
            let named = real_named();
            let ids: Vec<&str> = named.ids.iter().map(|(id, _)| id.as_str()).collect();
            assert_eq!(ids, NAMED_IDS);
            assert_eq!(
                named.not_disagreements,
                [
                    "INF-01",
                    "INF-02",
                    "S2-22-string",
                    "SLB-02-read",
                    "S2-25-pair",
                    "TK-03-tail",
                    "TK-03-copied-ref",
                    "TK-03-inner-pair",
                    "TK-01-owned-fields",
                    "TK-01-own-view",
                    "FV-02-whole-write"
                ]
            );
            // `FV-02-skip` is a disagreement in two forms, and its flag-set form is
            // named among the cases that are none: it keeps its row.
            let testing = read("docs/TESTING.md");
            let line = testing
                .lines()
                .find(|l| l.starts_with(HEAD))
                .expect("the paragraph");
            let tail = line.split_once(TAIL).expect("the tail").1;
            assert!(tail.contains("(`FV-02-skip`)"));
            // Each named ID is a row of TESTING 18 with a program.
            for id in ids
                .iter()
                .filter(|id| !UNNAMED.iter().any(|(own, _)| own == *id))
            {
                assert!(row_result(&testing, id).is_some(), "{id}");
            }
        },
    );
    h.case(
        "disagreements/the fake paragraph is read by the rule",
        || {
            let named = named_disagreements(FAKE_DOC, FAKE_UNNAMED).expect("reads");
            let ids: Vec<&str> = named.ids.iter().map(|(id, _)| id.as_str()).collect();
            assert_eq!(ids, ["OLD-1", "F1", "F2", "TK-1", "FV-1"]);
            assert_eq!(named.not_disagreements, ["INF-1"]);
            let rows = parse_corpus(&fake_corpus()).expect("reads");
            assert_eq!(one_to_one(&named, &rows), Vec::<String>::new());
            assert_eq!(
                outcome_problems(FAKE_DOC, &named, &rows, FAKE_UNNAMED),
                Vec::<String>::new()
            );
        },
    );
    h.case(
        "disagreements/a missing, stale or misplaced row is seen",
        || {
            let named = named_disagreements(FAKE_DOC, FAKE_UNNAMED).expect("reads");
            let rows = parse_corpus(&fake_corpus()).expect("reads");
            let mut fewer = rows.clone();
            fewer.remove(2);
            assert_eq!(
                one_to_one(&named, &fewer),
                ["F2 is a named disagreement with no corpus row"]
            );
            let mut more = rows.clone();
            let mut extra = rows[1].clone();
            extra.id = "INF-1".to_owned();
            more.push(extra.clone());
            extra.id = "ZZ-9".to_owned();
            more.push(extra);
            assert_eq!(
                one_to_one(&named, &more),
                [
                    "INF-1 has a corpus row, but TESTING 13 says it is no disagreement",
                    "ZZ-9 has a corpus row, but TESTING 13 names no such disagreement"
                ]
            );
            let mut swapped = rows.clone();
            swapped.swap(1, 2);
            assert_eq!(one_to_one(&named, &swapped).len(), 1);
            // A disagreement the document drops makes its row stale.
            let dropped = FAKE_DOC.replace("a loop `a; b;` (`TK-1`); ", "");
            let named = named_disagreements(&dropped, FAKE_UNNAMED).expect("reads");
            assert_eq!(
                one_to_one(&named, &rows),
                ["TK-1 has a corpus row, but TESTING 13 names no such disagreement"]
            );
        },
    );
    h.case(
        "disagreements/an outcome its row does not give is seen",
        || {
            let named = named_disagreements(FAKE_DOC, FAKE_UNNAMED).expect("reads");
            let mut rows = parse_corpus(&fake_corpus()).expect("reads");
            rows[1].enrang = Outcome::Codes(vec!["EN9603".to_owned()]);
            rows[2].rustc = Outcome::Codes(vec!["E0002".to_owned()]);
            rows[3].enrang = Outcome::Codes(vec!["EN9601".to_owned()]);
            rows[0].rustc = Outcome::Compiles;
            assert_eq!(
                outcome_problems(FAKE_DOC, &named, &rows, FAKE_UNNAMED),
                [
                    "OLD-1: TESTING 13's item does not say rustc Compiles",
                    "F1: its row never names EN9603",
                    "F2: neither its row nor TESTING 13 names E0002",
                    "TK-1: its row never names EN9601"
                ]
            );
            let mut rows = parse_corpus(&fake_corpus()).expect("reads");
            rows[4].enrang = Outcome::Compiles;
            rows[4].id = "FV-1b".to_owned();
            let named = Named {
                ids: vec![("FV-1b".to_owned(), String::new())],
                not_disagreements: Vec::new(),
            };
            assert_eq!(
                outcome_problems(FAKE_DOC, &named, &rows[4..], FAKE_UNNAMED),
                ["FV-1b: its row says no program compiles"]
            );
        },
    );
    let unreadable: &[(&str, &str, &str)] = &[
        (
            "no paragraph",
            "Intro.\n",
            "no paragraph opens with \"**Named intended disagreements** with `rustc`: \"",
        ),
        (
            "a reworded tail",
            "**Named intended disagreements** with `rustc`: x (`F1`). Nothing more.\n",
            "the paragraph has no sentence opening \" A result with several reference parts\"",
        ),
        (
            "an item with no ID",
            "**Named intended disagreements** with `rustc`: x (`F1`); a new one. A result \
             with several reference parts.\n",
            "a disagreement names no ID and none of the unnamed ones: \"a new one.\"",
        ),
        (
            "unnamed words no item holds",
            "**Named intended disagreements** with `rustc`: x (`F1`). A result with several \
             reference parts.\n",
            "0 disagreements say \"the old case\", named OLD-1",
        ),
    ];
    for (name, doc, error) in unreadable {
        let (doc, error) = (*doc, *error);
        h.case(
            format!("disagreements/reading fails on {name}"),
            move || {
                assert_eq!(
                    named_disagreements(doc, FAKE_UNNAMED),
                    Err(error.to_owned())
                );
            },
        );
    }
    let corrupt: &[(&str, &str, &str)] = &[
        (
            "four fields",
            "F1\tEN9601\tcompiles\tx\n",
            "line 1: 4 fields, not 5",
        ),
        (
            "no ID",
            "f1\tEN9601\tcompiles\ttests/compile/*/f1.fail.en\tcorpus/twins/f1.rs\n",
            "line 1: \"f1\" is no ID",
        ),
        (
            "rejects for Enrang",
            "F1\trejects\tcompiles\ttests/compile/*/f1.fail.en\tcorpus/twins/F1.rs\n",
            "line 1: \"rejects\" is no outcome",
        ),
        (
            "a rustc code for Enrang",
            "F1\tE0502\tcompiles\ttests/compile/*/f1.fail.en\tcorpus/twins/F1.rs\n",
            "line 1: \"E0502\" is no outcome",
        ),
        (
            "a fixture outside tests/compile",
            "F1\tEN9601\tcompiles\tcorpus/f1.fail.en\tcorpus/twins/F1.rs\n",
            "line 1: \"corpus/f1.fail.en\" is no compile fixture",
        ),
        (
            "a near-miss for a rejection",
            "F1\tEN9601\tcompiles\ttests/compile/*/f1.pass.en\tcorpus/twins/F1.rs\n",
            "line 1: tests/compile/*/f1.pass.en cannot show Codes([\"EN9601\"]): a program \
             that compiles is a `.pass.en`, one rejected a `.fail.en`",
        ),
        (
            "a twin elsewhere",
            "F1\tEN9601\tcompiles\ttests/compile/*/f1.fail.en\tcorpus/F1.rs\n",
            "line 1: the twin of F1 is corpus/twins/F1.rs",
        ),
        (
            "an ID twice",
            "F1\tEN9601\tcompiles\ttests/compile/*/f1.fail.en\tcorpus/twins/F1.rs\n\
             F1\tEN9601\tcompiles\ttests/compile/*/f1.fail.en\tcorpus/twins/F1.rs\n",
            "line 2: F1 has a row already",
        ),
    ];
    for (name, text, error) in corrupt {
        let (text, error) = (*text, *error);
        h.case(
            format!("disagreements/the corpus refuses {name}"),
            move || {
                assert_eq!(parse_corpus(text), Err(error.to_owned()));
            },
        );
    }
    h.case(
        "disagreements/each fake row's evidence trips, and the bump makes it due",
        || {
            assert_eq!(
                fake_report(Milestone::M3).to_string(),
                "gap: OLD-1 twin has no fixture (since M3, current M3)\n\
             gap: F2 fixture has a failing fixture (since M3, current M3)\n\
             gap: TK-1 fixture has no fixture (since M3, current M3)\n\
             gap: TK-1 twin has no fixture (since M3, current M3)\n\
             gap: FV-1 fixture has no fixture (since M3, current M3)\n\
             gap: FV-1 twin has no fixture (since M3, current M3)\n"
            );
            let report = fake_report(Milestone::M2);
            assert_eq!(report.to_string(), "");
            assert_eq!(
                ids_of(&report.early),
                ["OLD-1 fixture", "F1 fixture", "F1 twin", "F2 twin"]
            );
            assert_eq!((report.enforced, report.deferred), (0, 10));
        },
    );
    h.case(
        "disagreements/a row of two codes needs a fixture anchoring each",
        || {
            let text = fake_row(
                "F1",
                "EN9601 EN9602",
                "compiles",
                "tests/compile/*/f1.fail.en",
            );
            let rows = parse_corpus(&text).expect("reads");
            let one = "tests/compile/EN9601/f1.fail.en";
            let two = "tests/compile/EN9602/f1-2.fail.en";
            let fired = |path: &str, code: &str| format!("error[{code}]: fake\n --> {path}:1:1\n");
            let (key_one, key_two) = (format!("check {one}"), format!("check {two}"));
            let (err_one, err_two) = (fired(one, "EN9601"), fired(two, "EN9602"));
            let cli = FakeCli::new([
                (key_one.as_str(), err_one.as_str()),
                (key_two.as_str(), err_two.as_str()),
            ]);
            let run = |place: &Place, args: &[String]| cli.run(place, args);
            let both = [
                fake_fixture(one, "x //~ EN9601\n"),
                fake_fixture(two, "x //~ EN9602\n"),
            ];
            let status = |fixtures: &[Fixture]| fixture_status_of(&rows[0], fixtures, &run);
            assert_eq!(status(&both), FixtureStatus::Passing);
            assert_eq!(status(&both[..1]), FixtureStatus::Failing);
            assert_eq!(status(&[]), FixtureStatus::Missing);
        },
    );
    h.case(
        "disagreements/a twin's run gives its outcome or not",
        || {
            let rejected = "error[E0506]: cannot assign to `r` because it is borrowed\n";
            assert!(twin_gives(&Outcome::Compiles, 0, ""));
            assert!(!twin_gives(&Outcome::Compiles, 1, rejected));
            assert!(twin_gives(&Outcome::Rejects, 1, rejected));
            assert!(!twin_gives(&Outcome::Rejects, 0, ""));
            let e0506 = Outcome::Codes(vec!["E0506".to_owned()]);
            assert!(twin_gives(&e0506, 1, rejected));
            assert!(!twin_gives(&e0506, 1, "error[E0502]: x\n"));
            assert!(!twin_gives(&e0506, 0, rejected));
        },
    );
    h.case(
        "disagreements/the items of a list split outside code and asides",
        || {
            assert_eq!(
                items("a `x; y` b; c (d; e) f; g"),
                ["a `x; y` b", "c (d; e) f", "g"]
            );
            assert_eq!(items("one"), ["one"]);
        },
    );
    register_twins(h);
}

/// The twins' runs, when `RUSTC_TWINS` is set and `rustc` is found: one case per
/// twin that exists, giving its row's `rustc` outcome. Otherwise a skip notice
/// counts the rows, so the skip is never silent (TESTING 20).
fn register_twins(h: &mut Harness) {
    let rows = match parse_corpus(&read(CORPUS)) {
        Ok(rows) => rows,
        Err(error) => {
            h.case(
                "disagreements/the corpus reads, so its twins can run",
                move || Err::<(), String>(format!("{CORPUS}: {error}")),
            );
            return;
        }
    };
    if env::var_os("RUSTC_TWINS")
        .filter(|value| !value.is_empty())
        .is_none()
    {
        skip_oracle("rustc", rows.len(), "RUSTC_TWINS is unset");
        return;
    }
    let Some(rustc) = tool("rustc") else {
        skip_oracle("rustc", rows.len(), "not found");
        return;
    };
    let (written, unwritten): (Vec<CorpusRow>, Vec<CorpusRow>) =
        rows.into_iter().partition(|row| twin_on_disk(&row.twin));
    if !unwritten.is_empty() {
        skip_oracle("rustc", unwritten.len(), "twin not written yet");
    }
    for row in written {
        let rustc = rustc.clone();
        h.case(
            format!(
                "disagreements/rustc twin of {} gives {:?}",
                row.id, row.rustc
            ),
            move || {
                let dir = TempDir::new("twin");
                let output = rustc
                    .command()
                    .args(["--edition", "2021", "--crate-type", "bin", "-o"])
                    .arg(dir.join("twin"))
                    .arg(workspace_root().join(&row.twin))
                    .output()
                    .expect("rustc runs");
                let stderr = String::from_utf8_lossy(&output.stderr);
                let code = output.status.code().unwrap_or(-1);
                assert!(
                    twin_gives(&row.rustc, code, &stderr),
                    "{} gives exit {code}, not {:?}:\n{stderr}",
                    row.twin,
                    row.rustc
                );
            },
        );
    }
}
