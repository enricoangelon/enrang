//! TESTING 23's M2 row, item by item, as the meta suite enforces it (M2 bump).
//!
//! The row is read from TESTING 23 and split at its `;`s, and each item must be one
//! this module maps to the meta cases that enforce it, so an item added to the row,
//! or one reworded, trips here until the map follows it, and a mapped case that is
//! renamed or removed trips too. Six items are the gates of other modules: the counts
//! (`counts.rs`), the G cases as processes (`cases.rs`), every `since(M2)` code
//! (`gating.rs`), and the `C` rows, the satisfaction clauses and the attack rows
//! (`covers.rs`). The other four were proved only inside the sema and layout suites,
//! which the meta suite cannot run, so this module runs each of them through
//! `enrang check` as a process, with its own model of what must come out:
//!
//! - Maranget against brute force: random `match` columns over enums, nullable enums,
//!   booleans and integers, written as the functions of one program, must give
//!   exactly the EN0501 and EN0503 that a brute-force evaluation over a finite model
//!   of the subject's values predicts;
//! - the spread typing and `Clone` rows of TESTING 18, and its narrowed `for...of`
//!   rows (a source typed once under the facts at the loop, the state after the loop
//!   joined over its `break`s): each program gives the phase 2 diagnostics its row
//!   gives, and each program is tied to its row, which must still say so;
//! - SPEC 11's worked sizes, read from SPEC, as compile-time asserts on
//!   `i386-linux` (`P == 4`) and `x86_64-linux` (`P == 8`), and each one byte off is
//!   EN0415 at its assert.
//!
//! A diagnostic of a later phase is not compared: these are the M2 parts of the rows,
//! and a later milestone adds its own.
//!
//! TESTING 23's M3 row is mapped the same way ([`M3_ITEMS`]), item by item, to the
//! cases that enforce it (M3 plan f.10): the counts, the G cases, every `since(M3)`
//! code, the rows of TESTING 18 and the `H` rows, and the named disagreements are
//! other modules' gates. This module adds the four that look at what the M3
//! crates hold, each a gate of lines due at M3, early before the bump that closes
//! M3 and enforced from it:
//!
//! - the MIR verifier after every pass: `enrang check --emit=mir`, which verifies
//!   the MIR after it is built and after it is elaborated and exits 3 when either
//!   fails, on every compile fixture, a near-miss printing its module; and a
//!   narrowed `for...of` head with its tag check and its bounds check before the
//!   projection (TESTING 18's `.mir` row);
//! - the `.mir` round trip: the mir suite's hand-written modules, each a case of its
//!   round trip, and the borrowck suite's `.mir` fixtures, which need no front end;
//! - the `remap_ids` text fixtures, each a case of the mir suite;
//! - the drop-trace goldens of the pipeline suite: one per row of SPEC 5.7's D2
//!   table of temporaries, and three for partly moved values, whose tag `switch`
//!   comes before the ladder.
//!
//! A fifth is ARCHITECTURE 12's runnable proof of M3 beside `check`, which the row
//! leaves to the CLI suite: the `--emit` transcripts. SPEC 1's ownership block and
//! G08 run again as processes against their goldens, and each construct family of
//! MIR building and each kind of contract has a golden that worked, made by the CLI
//! suite (M3 plan f.3).
//!
//! The `.mir` fixtures live in the crates that read them, as built, not under the
//! workspace's `tests/mir/` the plan names: `crates/enrang-mir/tests/mir/` and
//! `crates/enrang-borrowck/tests/mir/borrowck/`.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use enrang_diag::{CURRENT_MILESTONE, Code, Milestone, Phase};
use enrang_testkit::{
    FixtureStatus, GateReport, Harness, Rng, Xoshiro256, reported, rng_for, scaled, workspace_root,
};

use crate::covers::{Line, bump_problems, gate_lines, row_cells};
use crate::for_of_docs::split_row;
use crate::gating::Run;
use crate::support::{Fixture, Place, Ran, files_under, fixtures, milestone_in, read, run_cached};

/// Each item of TESTING 23's M2 row, exactly as written, with the meta cases that
/// enforce it.
const ITEMS: &[(&str, &[&str])] = &[
    (
        "2,500 more cases",
        &[
            "counts/TESTING 23 asks M2 for 2,500 more cases",
            "counts/the shares of M2's suites add up to TESTING 23's count",
            "counts/M2's shares are those its suites declare (M2 plan g.8, as built)",
        ],
    ),
    (
        "Maranget against brute force",
        &[
            "row/Maranget agrees with brute force through enrang check",
            "row/the brute force predicts the hand-checked columns",
        ],
    ),
    (
        "G05, G06, G12, G13, G17, G19, G20, G22 byte-exact",
        &[
            "cases/every reached case is byte-exact as a process",
            "cases/every case due at M2 is byte-exact as a process",
            "cases/a drifted M2 case is a gap",
        ],
    ),
    (
        "the spread typing and `Clone` rows of section 18",
        &[
            "row/the spread typing and Clone rows of TESTING 18 through enrang check",
            "row/every spread typing and Clone row of TESTING 18 has its programs or says why not",
        ],
    ),
    (
        "narrowed `for...of` sources typed once under the facts at the loop, and the state after the loop joined over its `break`s",
        &[
            "row/the narrowed for...of rows of TESTING 18 through enrang check",
            "row/every narrowed for...of row of TESTING 18 has its programs or says why not",
        ],
    ),
    (
        "SPEC 11 worked sizes for both `P`",
        &[
            "row/SPEC 11's worked sizes hold on i386-linux",
            "row/SPEC 11's worked sizes hold on x86_64-linux",
            "row/a worked size one byte off is EN0415 on both targets",
        ],
    ),
    (
        "every `since(M2)` code",
        &[
            "gating/the real registry passes at the current milestone",
            "gating/the real registry passes at M2: every M2 code has a fixture, a near-miss and a page",
            "gating/removing the fixtures or the page of an M2 row opens a gap at M2",
        ],
    ),
    (
        "every `C` row covered with an accept and a reject",
        &[
            "covers/every C row of SPEC 4.5 has an accept and a reject",
            "covers/at M2 the gates enforce every line, and before it none",
        ],
    ),
    (
        "the exact-satisfaction rule of SPEC 4.4 has a fixture per clause",
        &["covers/every clause of SPEC 4.4's satisfaction rule has its fixtures"],
    ),
    (
        "the attack-review rows of section 18 whose codes are phase 2",
        &["covers/every attack-review row with a phase 2 code has its fixtures"],
    ),
];

/// Each item of TESTING 23's M3 row, exactly as written, with the meta cases that
/// enforce it.
const M3_ITEMS: &[(&str, &[&str])] = &[
    (
        "4,000 more cases, half negative with fixed siblings",
        &[
            "counts/TESTING 23 asks M3 for 4,000 more cases",
            "counts/the shares of M3's suites add up to TESTING 23's count",
            "counts/M3's shares are those its suites declare (M3 plan f.9, as built)",
            "counts/M3: the shares of M3's suites add up to TESTING 23's count once M3 is reached",
            "counts/M3: every firing fixture of an M3 code has its fixed sibling",
        ],
    ),
    (
        "MIR verifier after every pass, including a narrowed `for...of` head",
        &[
            "row/M3: the MIR of every compile fixture verifies after every pass",
            "row/M3: a narrowed for...of head checks its tag and bounds before the projection",
        ],
    ),
    (
        "`.mir` module round trip, with fixtures needing no front end",
        &["row/M3: the .mir round trip covers hand-written modules that need no front end"],
    ),
    (
        "`remap_ids` text fixtures",
        &["row/M3: the remap_ids text fixtures are each a case of the mir suite"],
    ),
    (
        "G07-G11, G16, G18, G21, G23, G24 byte-exact",
        &[
            "cases/every reached case is byte-exact as a process",
            "cases/every case due at M3 is byte-exact as a process",
            "cases/a drifted M3 case is a gap",
            "cases/each milestone is the one TESTING 23 makes the case exact at",
        ],
    ),
    (
        "every row of the `for...of`, inferred-permission and attack-review tables of section 18, `f1`-`f6`, `h1`-`h8` and `l1`-`l10` included",
        &[
            "covers/M3: every attack row's phase 3 codes and near-misses have their fixtures",
            "covers/M3: every row of the named-fixture, for...of and inferred-permission tables has its fixtures",
            "covers/M3: every row claim names exactly one row of the tables",
            "covers/M3: before the bump no M3 line is due, and at the bump every one is",
            "covers/at the current milestone the gates lack nothing, and nothing is stale",
        ],
    ),
    (
        "`rustc` twin disagreements all named",
        &[
            "disagreements/TESTING 13 names its disagreements as the corpus rows, one to one",
            "disagreements/each corpus row states the outcomes its rows give",
            "disagreements/every reached row's fixture gives Enrang's outcome, and its twin exists",
        ],
    ),
    (
        "every `since(M3)` code",
        &[
            "gating/the real registry passes at the current milestone",
            "gating/the real registry passes at M3: every M3 code has a fixture, a near-miss and a page",
            "gating/removing the fixtures or the page of an M3 row opens a gap at M3",
        ],
    ),
    (
        "every `H` row covered",
        &[
            "covers/M3: every H row of SPEC 5.8 is covered",
            "covers/M3: each H row case trips, and the bump makes it due",
        ],
    ),
    (
        "drop-trace fixtures for the D2 temporary table and for partly moved `T \\| null`, `Result` and a user enum",
        &["row/M3: the drop traces cover SPEC 5.7's table of temporaries and partly moved values"],
    ),
];

/// The milestone of this module's M3 lines.
const M3_ROW_SINCE: Milestone = Milestone::M3;

/// The mir suite's hand-written modules, which its round trip prints back.
const ROUNDTRIP_DIR: &str = "crates/enrang-mir/tests/mir/roundtrip";

/// The mir suite's `remap_ids` text fixtures.
const REMAP_DIR: &str = "crates/enrang-mir/tests/mir/remap";

/// The borrowck suite's `.mir` fixtures, which need no front end.
const BORROWCK_MIR_DIR: &str = "crates/enrang-borrowck/tests/mir/borrowck";

/// The pipeline suite's drop-trace goldens (M3 plan f.8), and the case file that
/// compares them.
const DROPS_DIR: &str = "tests/golden/pipeline/drops";
const DROPS_SUITE: &str = "crates/enrang-driver/tests/pipeline/drops.rs";

/// The `.mir` files under a directory of the workspace, recursively.
fn mir_files(dir: &str) -> Vec<String> {
    files_under(&workspace_root().join(dir))
        .into_iter()
        .filter(|name| name.ends_with(".mir"))
        .collect()
}

/// A line that passes when `holds`.
fn line_if(id: &str, holds: bool) -> Line {
    Line {
        id: id.to_owned(),
        since: M3_ROW_SINCE,
        status: if holds {
            FixtureStatus::Passing
        } else {
            FixtureStatus::Missing
        },
    }
}

/// Whether a run of `check --emit=mir` on a fixture shows its MIR verified after
/// every pass: never exit 3, the driver's verdict when the verifier fails after
/// building or after elaborating, and a near-miss exits 0 printing its MIR as
/// [`printed_mir`] reads it.
pub fn verified(near_miss: bool, ran: &Ran) -> bool {
    if near_miss {
        ran.code == 0 && printed_mir(&ran.stdout)
    } else {
        ran.code == 0 || ran.code == 1
    }
}

/// Whether `out` is what `check --emit=mir` prints: nothing when no module has a
/// body, since `emit` skips a module with none (a fixture of types or enums alone),
/// else modules each opening with `print_module`'s documented header, `[target
/// "..";] [module "..";]`: a fixture's module is named after its file, never
/// `main`, so its header holds the module line, after the target line when its
/// `//! target:` names one other than the host's default.
pub fn printed_mir(out: &str) -> bool {
    let mut lines = out.lines();
    let quoted = |line: &str, word: &str| {
        line.strip_prefix(word)
            .and_then(|rest| rest.strip_prefix(" \""))
            .is_some_and(|rest| rest.ends_with("\";"))
    };
    match lines.next() {
        None => true,
        Some(first) if quoted(first, "target") => lines.next().is_some_and(|m| quoted(m, "module")),
        Some(first) => quoted(first, "module"),
    }
}

/// One line per compile fixture: `check --emit=mir`, with the flags its header asks
/// for, shows its MIR verified.
pub fn verify_lines(fixtures: &[Fixture], run: &Run<'_>) -> Vec<Line> {
    fixtures
        .iter()
        .map(|fixture| {
            let holds = fixture.check_args().is_some_and(|mut args| {
                args.insert(1, "--emit=mir".to_owned());
                verified(fixture.near_miss, &run(&Place::Root, &args))
            });
            line_if(&format!("verified {}", fixture.path), holds)
        })
        .collect()
}

/// A narrowed `for...of` head, the program TESTING 18's `.mir` row is about.
const NARROWED_HEAD: &str = "public function total(p: i64[] | null): i64 {
  let n = 0;
  if (p != null) {
    for (const x of &p) {
      n += *x;
    }
  }
  return n;
}
";

/// What is wrong with the element borrows of a printed MIR module's narrowed
/// `for...of` heads: each `[for-of-element]` borrow through a narrowed payload,
/// `(_n as Case)`, must follow a `check_bounds` of its block, with the `check_tag`
/// right before it (SPEC H18: the tag check adjacent to the projection).
pub fn narrowed_head_problems(mir: &str) -> Vec<String> {
    let lines: Vec<&str> = mir.lines().map(str::trim).collect();
    let mut problems = Vec::new();
    let mut found = 0;
    for (at, line) in lines.iter().enumerate() {
        if !(line.ends_with("[for-of-element];") && line.contains(" as ")) {
            continue;
        }
        found += 1;
        let block_start = lines[..at]
            .iter()
            .rposition(|line| line.starts_with("bb") && line.ends_with('{'))
            .map_or(0, |start| start + 1);
        let block = &lines[block_start..at];
        if !block.iter().any(|line| line.starts_with("check_bounds(")) {
            problems.push(format!("no check_bounds before {line:?}"));
        }
        if !block
            .last()
            .is_some_and(|last| last.starts_with("check_tag("))
        {
            problems.push(format!("no check_tag right before {line:?}"));
        }
    }
    if found == 0 {
        problems.push("no element borrow through a narrowed payload".to_owned());
    }
    problems
}

/// The narrowed head's line: `check --emit=mir` on [`NARROWED_HEAD`] passes and its
/// MIR checks the tag and the bounds before the projection.
fn narrowed_head_lines(run: &Run<'_>) -> Vec<Line> {
    let files = vec![("main.en".to_owned(), NARROWED_HEAD.as_bytes().to_vec())];
    let args: Vec<String> = ["check", "--emit=mir", "main.en"]
        .map(str::to_owned)
        .to_vec();
    let ran = run(&Place::Files(files), &args);
    let holds = ran.code == 0 && narrowed_head_problems(&ran.stdout).is_empty();
    vec![line_if("a narrowed for...of head is checked", holds)]
}

/// Whether a suite's source runs a case per `.mir` file of its fixtures directory
/// `sub`: it reads them with `fixtures("<sub>")` and registers a case for each.
fn suite_runs_each(source: &str, sub: &str) -> bool {
    source.contains(&format!("for (name, text) in fixtures(\"{sub}\")"))
        && source.contains(&format!("format!(\"{sub}/{{name}}"))
}

/// The pipeline suite's round trip of every body it builds (M3 plan f.4).
const PIPELINE_ROUNDTRIP: &str = "crates/enrang-driver/tests/pipeline/roundtrip.rs";

/// The pipeline suite's entry, which registers its modules.
const PIPELINE_MAIN: &str = "crates/enrang-driver/tests/pipeline/main.rs";

/// Whether the pipeline suite round-trips every body it builds: a case per input
/// group, each printing its built and elaborated bodies, parsing them back and
/// comparing the text printed again, and the suite registering it.
pub fn pipeline_roundtrips(roundtrip: Option<&str>, main: Option<&str>) -> bool {
    roundtrip.is_some_and(|source| {
        source.contains("for (group, inputs) in groups()")
            && source.contains("[(\"built\", &built), (\"elaborated\", &elaborated)]")
            && source.contains("parse_module(&text)")
            && source.contains("again == text")
    }) && main.is_some_and(|source| source.contains("roundtrip::register(&mut h);"))
}

/// Whether the pipeline suite feeds the driver a body that fails the verifier, at
/// phase 3 and at `--emit=mir`, and expects an internal error from each.
pub fn pipeline_seams(verify_all: Option<&str>) -> bool {
    verify_all.is_some_and(|source| {
        source.contains("enrang_driver::run_phase3(&mut session, &typed)")
            && source.contains("enrang_driver::emit(&checked, enrang_driver::Emit::Mir)")
            && source.contains("the MIR of `main::f` fails the verifier")
            && source.contains("the elaborated MIR of `main::f` fails the verifier")
    })
}

/// The pipeline suite's verifier cases.
const PIPELINE_VERIFY: &str = "crates/enrang-driver/tests/pipeline/verify_all.rs";

/// The `.mir` round trip's lines: hand-written modules exist, the mir suite's round
/// trip runs a case for each, `.mir` fixtures that need no front end exist for the
/// borrow checker, and the pipeline suite round-trips every body it builds.
fn roundtrip_lines(read_source: &dyn Fn(&str) -> Option<String>) -> Vec<Line> {
    let roundtrip = read_source("crates/enrang-mir/tests/mir/roundtrip.rs");
    let pipeline = read_source(PIPELINE_ROUNDTRIP);
    let main = read_source(PIPELINE_MAIN);
    vec![
        line_if(
            "the pipeline suite round-trips every body it builds",
            pipeline_roundtrips(pipeline.as_deref(), main.as_deref()),
        ),
        line_if(
            "hand-written .mir modules",
            !mir_files(ROUNDTRIP_DIR).is_empty(),
        ),
        line_if(
            "the mir suite prints each back",
            roundtrip.is_some_and(|source| suite_runs_each(&source, "roundtrip")),
        ),
        line_if(
            "the borrow checker's .mir fixtures",
            !mir_files(BORROWCK_MIR_DIR).is_empty(),
        ),
    ]
}

/// The `remap_ids` fixtures' lines: they exist and the mir suite remaps each.
fn remap_lines(read_source: &dyn Fn(&str) -> Option<String>) -> Vec<Line> {
    let remap = read_source("crates/enrang-mir/tests/mir/remap.rs");
    vec![
        line_if("remap_ids text fixtures", !mir_files(REMAP_DIR).is_empty()),
        line_if(
            "the mir suite remaps each",
            remap.is_some_and(|source| suite_runs_each(&source, "remap")),
        ),
    ]
}

/// The rows of SPEC 5.7's D2 table of temporaries.
fn d2_rows(spec: &str) -> usize {
    spec.lines()
        .map(str::trim)
        .skip_while(|line| *line != "| Temporaries created in | End |")
        .skip(2)
        .take_while(|line| line.starts_with('|'))
        .count()
}

/// The three partly moved values TESTING 23's M3 row names, `T | null`, `Result`
/// and a user enum, by their goldens' names.
const PARTLY_MOVED: [&str; 3] = [
    "partly_moved_nullable",
    "partly_moved_result",
    "partly_moved_enum",
];

/// Whether a drop trace switches on a tag before its drop ladder: a `switch` on a
/// `discriminant` read before the first drop of a case's field.
pub fn tag_switch_before_ladder(text: &str) -> bool {
    let Some(ladder) = text.find("drop_glue((") else {
        return false;
    };
    let before: Vec<&str> = text[..ladder].lines().map(str::trim).collect();
    before
        .windows(2)
        .any(|pair| pair[0].contains(" = discriminant(") && pair[1].starts_with("switch move "))
}

/// The drop traces' lines, from the goldens `(name, text)`: one per row of the D2
/// table and three for partly moved values, at least; each of the three partly
/// moved values of the row by name, with a tag `switch` before its drop ladder; and
/// the pipeline suite's case file comparing that directory.
pub fn drop_lines(goldens: &[(String, String)], rows: usize, suite: Option<&str>) -> Vec<Line> {
    let mut lines = vec![line_if(
        "a drop trace per row of the table and per partly moved value",
        goldens.len() >= rows + 3,
    )];
    for name in PARTLY_MOVED {
        let file = format!("{name}.mir");
        lines.push(line_if(
            &format!("{name} switches on its tag before its drop ladder"),
            goldens
                .iter()
                .any(|(n, text)| *n == file && tag_switch_before_ladder(text)),
        ));
    }
    lines.push(line_if(
        "the pipeline suite compares them",
        suite.is_some_and(|source| source.contains("pipeline/drops")),
    ));
    lines
}

fn read_if_there(relative: &str) -> Option<String> {
    std::fs::read_to_string(workspace_root().join(relative)).ok()
}

fn real_drop_lines() -> Vec<Line> {
    let root = workspace_root().join(DROPS_DIR);
    let goldens: Vec<(String, String)> = files_under(&root)
        .into_iter()
        .map(|name| {
            let text = std::fs::read_to_string(root.join(&name)).unwrap_or_default();
            (name, text)
        })
        .collect();
    let suite = read_if_there(DROPS_SUITE);
    drop_lines(&goldens, d2_rows(&read("docs/SPEC.md")), suite.as_deref())
}

/// The `--emit` transcripts of the CLI's project suite (M3 plan f.3 and b.11), the
/// runnable proof ARCHITECTURE 12 names for M3 beside `check`: the elaborated MIR of
/// SPEC 1's ownership block and of a program with errors, then one program per
/// construct family of MIR building and one per kind of contract a summary states.
const EMIT_DIR: &str = "tests/golden/cli-project/check";

/// The CLI suite's files that make those transcripts.
const EMIT_SUITE: &str = "crates/enrang-cli/tests/cli/emit.rs";
const EMIT_PROJECT: &str = "crates/enrang-cli/tests/cli/project.rs";

/// The construct families `--emit=mir` shows, each by its golden's name.
const EMIT_MIR: [&str; 9] = [
    "g08_fixed",
    "for_of_narrowed",
    "match_guard",
    "result_forms",
    "closure_local_function",
    "extendable_constructor",
    "named_fill",
    "spread",
    "destructuring_assignment",
];

/// The kinds of contract `--emit=summary` states, each by its golden's name.
const EMIT_SUMMARY: [&str; 6] = [
    "lexer",
    "holder",
    "copier",
    "longest_first",
    "wrapper_retarget",
    "local_function",
];

/// Whether `text` is a transcript of `check --emit=<what> main.en` that worked: exit
/// 0, nothing on stderr, and on stdout MIR verified and elaborated (each body says
/// `phase elaborated;`), or a summary opening with its module.
pub fn emit_golden_holds(what: &str, text: &str) -> bool {
    let head = format!("$ enrang check --emit={what} main.en\n[exit 0]\n[stdout]\n");
    let stdout = text
        .strip_prefix(&head)
        .and_then(|rest| rest.strip_suffix("[stderr]\n"));
    match stdout {
        Some(out) if out.contains("[stderr]\n") || out.is_empty() => false,
        Some(out) if what == "mir" => out.contains("\n  phase elaborated;\n"),
        Some(out) => out.starts_with("module \""),
        None => false,
    }
}

/// Whether a run reproduces a transcript: its body equals the golden's below the
/// command line.
fn reproduces(ran: &Ran, golden: Option<&str>) -> bool {
    golden
        .and_then(|text| text.split_once('\n'))
        .is_some_and(|(_, body)| ran.body() == body)
}

/// The `--emit` lines: two transcripts run again as processes, from SPEC's own
/// programs, and the goldens of the construct families and contract kinds, each
/// one that worked and made by the CLI suite. `read` reads a file of the workspace;
/// `ownership` is SPEC 1's ownership block and `g08` G08's file, name and text.
pub fn emit_lines(
    run: &Run<'_>,
    read: &dyn Fn(&str) -> Option<String>,
    ownership: &str,
    g08: (&str, &str),
) -> Vec<Line> {
    let golden = |name: &str| read(&format!("{EMIT_DIR}/{name}.txt"));
    let files = vec![("main.en".to_owned(), ownership.as_bytes().to_vec())];
    let args = ["check", "--emit=mir", "main.en"].map(str::to_owned);
    let ownership_mir = golden("emit_mir");
    let ownership_holds = ownership_mir
        .as_deref()
        .is_some_and(|text| emit_golden_holds("mir", text))
        && reproduces(&run(&Place::Files(files), &args), ownership_mir.as_deref());
    let files = vec![(g08.0.to_owned(), g08.1.as_bytes().to_vec())];
    let args = ["check", "--emit=mir", g08.0].map(str::to_owned);
    let ran = run(&Place::Files(files), &args);
    let errors_hold = ran.code == 1
        && ran.stdout.is_empty()
        && reproduces(&ran, golden("emit_mir_with_errors").as_deref());
    let all_hold = |what: &str, names: &[&str]| {
        names.iter().all(|name| {
            golden(&format!("emit-{what}/{name}"))
                .is_some_and(|text| emit_golden_holds(what, &text))
        })
    };
    let suite = read(EMIT_SUITE).unwrap_or_default();
    let project = read(EMIT_PROJECT).unwrap_or_default();
    let made = suite.contains("name: format!(\"check/emit-{what}/{name}.txt\"),")
        && EMIT_MIR
            .iter()
            .chain(&EMIT_SUMMARY)
            .all(|name| suite.contains(&format!("    (\n        \"{name}\",\n")))
        && project.contains(
            "ProjectCase::new(\"check/emit_mir\", &[\"check\", \"--emit=mir\", \"main.en\"], 0)",
        )
        && project.contains("\"check/emit_mir_with_errors\",");
    vec![
        line_if("the ownership block's MIR, as a process", ownership_holds),
        line_if(
            "a program with errors prints no MIR, as a process",
            errors_hold,
        ),
        line_if(
            "a MIR golden per construct family",
            all_hold("mir", &EMIT_MIR),
        ),
        line_if(
            "a summary golden per kind of contract",
            all_hold("summary", &EMIT_SUMMARY)
                && golden("emit_summary").is_some_and(|text| emit_golden_holds("summary", &text)),
        ),
        line_if("the CLI suite makes each of them", made),
    ]
}

fn real_emit_lines() -> Vec<Line> {
    let case = |id: &str| {
        crate::cases::spec_cases()
            .iter()
            .find(|case| case.id == id)
            .unwrap_or_else(|| panic!("SPEC has no case {id}"))
    };
    let g08 = &case("G08").files[0];
    emit_lines(
        &run_cached,
        &read_if_there,
        &case("ownership").files[0].contents,
        (&g08.name, &g08.contents),
    )
}

/// This module's M3 gates, each by the case that enforces it.
const M3_GATES: [&str; 6] = [
    "row/M3: the MIR of every compile fixture verifies after every pass",
    "row/M3: a narrowed for...of head checks its tag and bounds before the projection",
    "row/M3: the .mir round trip covers hand-written modules that need no front end",
    "row/M3: the remap_ids text fixtures are each a case of the mir suite",
    "row/M3: the drop traces cover SPEC 5.7's table of temporaries and partly moved values",
    "row/M3: the --emit transcripts reproduce, one per construct family and contract kind",
];

/// The lines of the M3 gate `name` ([`M3_GATES`]) over the real repository.
fn real_m3_gate(name: &str) -> Vec<Line> {
    match M3_GATES.iter().position(|gate| *gate == name) {
        Some(0) => {
            let mut lines = verify_lines(&fixtures(), &run_cached);
            lines.push(line_if(
                "the driver's own verifier runs: a body that fails it is an internal error",
                pipeline_seams(read_if_there(PIPELINE_VERIFY).as_deref()),
            ));
            lines
        }
        Some(1) => narrowed_head_lines(&run_cached),
        Some(2) => roundtrip_lines(&read_if_there),
        Some(3) => remap_lines(&read_if_there),
        Some(4) => real_drop_lines(),
        Some(5) => real_emit_lines(),
        _ => panic!("no M3 gate {name:?}"),
    }
}

/// The report of one of this module's M3 gates at `current`.
fn m3_report(lines: &[Line], current: Milestone) -> GateReport {
    gate_lines(lines, current)
}

/// The items of TESTING 23's row for `milestone`, split at its `;`s. The cells are
/// split at pipes that are not escaped, since M3's row writes `T \| null`.
fn row_items(milestone: Milestone) -> Vec<String> {
    let testing = read("docs/TESTING.md");
    let row = testing
        .lines()
        .skip_while(|line| *line != "| M | Gate |")
        .map(row_cells)
        .find(|row| {
            row.first()
                .and_then(|cell| milestone_in(cell))
                .is_some_and(|m| m == milestone)
        })
        .unwrap_or_else(|| panic!("TESTING 23 has no row for {milestone}"));
    row[1]
        .split(';')
        .map(|item| item.trim().to_owned())
        .collect()
}

// ---------------------------------------------------------------------------------
// One program through `enrang check`, against the phase 2 diagnostics it must give.

/// A diagnostic a program must give: its line, its code and a piece of its message.
type Want = (usize, &'static str, &'static str);

/// A program and the phase 2 diagnostics `check` must give on it, exactly.
struct RowProgram {
    /// What it shows, for a failure's message.
    name: &'static str,
    source: &'static str,
    want: &'static [Want],
}

/// A row of TESTING 18 and the programs that show its M2 part.
struct DocRow {
    /// The text the row's line opens with, after `| `, which must open exactly one
    /// line of TESTING.md.
    starts: &'static str,
    /// What the row's last cell must still say.
    gives: &'static str,
    programs: &'static [RowProgram],
}

/// The codes a diagnostic of which is compared: those found by phase 2 or earlier.
fn compared(code: &str) -> bool {
    Code::from_name(code).is_some_and(|code| {
        matches!(
            code.phase(),
            Phase::CommandLine | Phase::Syntax | Phase::Types
        )
    })
}

/// `enrang check main.en` in a fresh directory holding `source`.
fn check_source(source: &str, args: &[&str]) -> Ran {
    let mut command = vec!["check".to_owned()];
    command.extend(args.iter().map(|arg| (*arg).to_owned()));
    command.push("main.en".to_owned());
    let files = vec![("main.en".to_owned(), source.as_bytes().to_vec())];
    run_cached(&Place::Files(files), &command)
}

/// What is wrong with a run against the diagnostics it must give: the phase 2
/// diagnostics must be exactly `want`, by line and code, each with its piece of the
/// message, stdout empty and the exit status 1 exactly when an error was reported.
fn mismatch(ran: &Ran, want: &[Want]) -> Option<String> {
    let found = reported(&ran.stderr);
    let mut got: Vec<(usize, String)> = found
        .iter()
        .filter(|diag| compared(&diag.code))
        .map(|diag| (diag.line().unwrap_or(0), diag.code.clone()))
        .collect();
    got.sort();
    let mut wanted: Vec<(usize, String)> = want
        .iter()
        .map(|(line, code, _)| (*line, (*code).to_owned()))
        .collect();
    wanted.sort();
    let errors = ran.stderr.lines().any(|line| line.starts_with("error"));
    let mut problems = Vec::new();
    if got != wanted {
        problems.push(format!("reported {got:?}, wanted {wanted:?}"));
    }
    for (line, code, piece) in want {
        let said = found.iter().any(|diag| {
            diag.line() == Some(*line) && diag.code == *code && diag.message.contains(piece)
        });
        if !said {
            problems.push(format!("no {code} at line {line} saying {piece:?}"));
        }
    }
    if !ran.stdout.is_empty() {
        problems.push(format!("stdout: {:?}", ran.stdout));
    }
    if ran.code != i32::from(errors) {
        problems.push(format!("exit {} with errors {errors}", ran.code));
    }
    (!problems.is_empty()).then(|| format!("{}\n{}", problems.join("\n"), ran.stderr))
}

/// Every row's line in TESTING.md, and every program's run, as `rows` say.
fn check_rows(rows: &[DocRow]) -> Result<(), String> {
    let testing = read("docs/TESTING.md");
    let mut failures = Vec::new();
    for row in rows {
        let head = format!("| {}", row.starts);
        let lines: Vec<&str> = testing.lines().filter(|l| l.starts_with(&head)).collect();
        let [line] = lines[..] else {
            failures.push(format!(
                "{} lines of TESTING.md open with {head:?}",
                lines.len()
            ));
            continue;
        };
        let (_, result) = split_row(line);
        if !result.contains(row.gives) {
            failures.push(format!(
                "the row {head:?} no longer gives {:?}: {result}",
                row.gives
            ));
        }
        for program in row.programs {
            if let Some(problem) = mismatch(&check_source(program.source, &[]), program.want) {
                failures.push(format!("{}: {problem}\n{}", program.name, program.source));
            }
        }
    }
    if failures.is_empty() {
        Ok(())
    } else {
        Err(failures.join("\n\n"))
    }
}

/// The table lines of TESTING.md from the one opening with `from` (with `after`,
/// the line after it) up to the one before the line opening with `to`.
fn section<'t>(testing: &'t str, from: &str, after: bool, to: &str) -> Vec<&'t str> {
    let lines: Vec<&str> = testing.lines().collect();
    let start = lines
        .iter()
        .position(|line| line.starts_with(from))
        .unwrap_or_else(|| panic!("no line of TESTING.md opens with {from:?}"))
        + usize::from(after);
    let end = lines[start..]
        .iter()
        .position(|line| line.starts_with(to))
        .map(|offset| start + offset)
        .unwrap_or_else(|| panic!("no line after {from:?} opens with {to:?}"));
    lines[start..end]
        .iter()
        .copied()
        .filter(|line| line.starts_with("| "))
        .collect()
}

/// What ties the rows of a TESTING 18 section to this module wrongly: each line
/// must open with exactly one DocRow's `starts` or one entry of `without`, the rows
/// with no phase 1-2 part, and each of those must open a line of the section. So a
/// DocRow deleted, or a row added to the document, fails here.
fn rows_tied(lines: &[&str], starts: &[&str], without: &[&str]) -> Result<(), String> {
    let mut problems = Vec::new();
    for line in lines {
        let opened: Vec<&&str> = starts
            .iter()
            .chain(without)
            .filter(|head| line.starts_with(&format!("| {head}")))
            .collect();
        if opened.len() != 1 {
            problems.push(format!(
                "{} rows of this module open the line {line:?}",
                opened.len()
            ));
        }
    }
    for head in starts.iter().chain(without) {
        if !lines
            .iter()
            .any(|line| line.starts_with(&format!("| {head}")))
        {
            problems.push(format!("no line of the section opens with {head:?}"));
        }
    }
    if problems.is_empty() {
        Ok(())
    } else {
        Err(problems.join("\n"))
    }
}

/// TESTING 18's spread rows: from the first line opening `| Spread: ` up to the
/// freestanding row, which is M5's.
fn spread_section(testing: &str) -> Vec<&str> {
    section(
        testing,
        "| Spread: ",
        false,
        "| `[...a]` on a freestanding target",
    )
}

/// TESTING 18's narrowed `for...of` rows (T:723-732): after the row of the writes
/// a hold rejects, up to the `.mir` row.
fn for_of_section(testing: &str) -> Vec<&str> {
    section(
        testing,
        "| Under `p != null`: `for (const x of &p) { p = null; }`, and in place of",
        true,
        "| `.mir`: a narrowed head",
    )
}

/// The spread rows with no phase 1-2 part: a run's result (M4), and a phase 3 code.
const SPREAD_WITHOUT_PROGRAM: &[&str] = &[
    "`[...a, g()?]` with `g` failing",
    "`const r = &f; const c = [...f]; r[0] = 1;` with `let f`",
];

/// The narrowed `for...of` rows with no phase 1-2 part: a phase 3 code alone.
const FOR_OF_WITHOUT_PROGRAM: &[&str] =
    &["Under `p != null`: `for (const x of &p) { p.push(1); }`"];

/// [`rows_tied`] for `rows` over `lines`.
fn doc_rows_tied(lines: &[&str], rows: &[DocRow], without: &[&str]) -> Result<(), String> {
    let starts: Vec<&str> = rows.iter().map(|row| row.starts).collect();
    rows_tied(lines, &starts, without)
}

const NEEDS_ARRAY: &str = "`...` needs an array";

/// TESTING 18's spread typing and `Clone` rows (T:735-749), their phase 2 parts.
const SPREAD_ROWS: &[DocRow] = &[
    DocRow {
        starts: "Spread: `[...a, f(&a)]`, `[f(&a), ...a]`, `a = [...a, x]`",
        gives: "Compiles",
        programs: &[RowProgram {
            name: "spreads beside a borrow of their operand",
            source: "public function f(a: &i64[]): i64 { return 0; }
public function g(a: i64[], x: i64): void {
  const b = [...a, f(&a)];
  const c = [f(&a), ...a];
  a = [...a, x];
}
",
            want: &[],
        }],
    },
    DocRow {
        starts: "`const f: i32[3] = [1, 2, 3]; const c = [...f];`",
        gives: "Compiles",
        programs: &[RowProgram {
            name: "fixed arrays, references and borrowed views spread",
            source: "public function g(a: &i32[3]): i32[] { return [...a]; }
public function h(r: &i64[]): void { const c = [...r]; console.log(r.length()); }
public function k(): void {
  const f: i32[3] = [1, 2, 3];
  const c = [...f];
  const d = [...&f];
  let q: i64[] = [1];
  const e = [...&q];
  const w: i64[] = [2];
  const m = [...&w];
}
",
            want: &[],
        }],
    },
    DocRow {
        starts: "`[...b]` with `b: Box<T[]>`",
        gives: "EN0438, with a `...*b` help on the first",
        programs: &[RowProgram {
            name: "a spread of a box, a number, a text and a nullable array",
            source: "public function f1(b: Box<i64[]>): void { const a = [...b]; }
public function f2(): void { const a = [...5]; }
public function f3(): void { const a = [...\"abc\"]; }
public function f4(o: i64[] | null): void { const a = [...o]; }
",
            want: &[
                (1, "EN0438", "found `Box<i64[]>`"),
                (2, "EN0438", NEEDS_ARRAY),
                (3, "EN0438", NEEDS_ARRAY),
                (4, "EN0438", "found `i64[] | null`"),
            ],
        }],
    },
    DocRow {
        starts: "`const a: i64[3] = [...b];`",
        gives: "EN0401",
        programs: &[RowProgram {
            name: "a spread is growable and never converts its elements",
            source: "public function f1(b: i64[]): void { const a: i64[3] = [...b]; }
public function f2(xs: i64[]): void { const n: (i64 | null)[] = [...xs]; }
public function f3(xs: i64[]): void { const n: (i64 | null)[] = [0, ...xs]; }
public function f4(a: i32[], b: i64[]): void { const c = [...a, ...b]; }
",
            want: &[
                (1, "EN0401", "expected `i64[3]`, found `i64[]`"),
                (2, "EN0401", "expected `(i64 | null)[]`"),
                (3, "EN0401", "expected `(i64 | null)[]`"),
                (4, "EN0401", "found `i64[]`"),
            ],
        }],
    },
    DocRow {
        starts: "`[...move a]`; `a.extendCloned(&a)`",
        gives: "EN0228; EN0706",
        programs: &[RowProgram {
            name: "a spread moves its operand already (its EN0706 is phase 3)",
            source: "public function f(a: i64[]): void { const b = [...move a]; }
",
            want: &[(1, "EN0228", "`move` is not needed here")],
        }],
    },
    DocRow {
        starts: "`let q; const c = [...q]; q = [1];`",
        gives: "EN0410; compiles; EN0410",
        programs: &[RowProgram {
            name: "a spread of an array of unknown type",
            source: "public function f1(): void { let q; const c = [...q]; q = [1]; }
public function f2(): void { let q = []; const c = [...q]; q.push(1); }
public function f3(): void { const c = [...[]]; }
",
            want: &[
                (1, "EN0410", "cannot infer the type of `q`"),
                (3, "EN0410", "cannot infer"),
            ],
        }],
    },
    DocRow {
        starts: "`<T>(xs: &T[])`, `T extends Clone`, `T extends Copy`",
        gives: "EN0438 (G22); compiles; compiles",
        programs: &[RowProgram {
            name: "a spread of a type parameter's elements needs `Clone`",
            source: "public function f1<T>(xs: &T[]): T[] { return [...xs]; }
public function f2<T extends Clone>(xs: &T[]): T[] { return [...xs]; }
public function f3<T extends Copy>(xs: &T[]): T[] { return [...xs]; }
",
            want: &[(1, "EN0438", "`T` has no `Clone` bound")],
        }],
    },
    DocRow {
        starts: "Elements: `i64`, `(*u8)[]`",
        gives: "Compiles; a `.clone()` on each resolves too",
        programs: &[RowProgram {
            name: "elements that are `Clone`, spread and cloned",
            source: "public final class Raw implements Copy { public p: *u8; }
public class Node { public next: Box<Node> | null = null; }
public function f<T extends Clone>(a: i64[], b: (*u8)[], c: Raw[], d: Node[], e: (T | null)[], h: i64[2][], i: Box<i64>[], j: Result<i64>[]): void {
  const x1 = [...a]; const x2 = [...b]; const x3 = [...c]; const x4 = [...d];
  const x5 = [...e]; const x6 = [...h]; const x7 = [...i]; const x8 = [...j];
  const y1 = a.clone(); const y2 = b.clone(); const y3 = c.clone(); const y4 = d.clone();
  const y5 = e.clone(); const y6 = h.clone(); const y7 = i.clone(); const y8 = j.clone();
}
",
            want: &[],
        }],
    },
    DocRow {
        starts: "Elements: a class with a destructor and no `clone`",
        gives: "EN0438; compiles",
        programs: &[RowProgram {
            name: "elements that are not `Clone`, and one with its own `clone`",
            source: "public class R { public x: i64 = 0; public destructor() {} }
public class P { public p: *u8; }
public class S { public x: i64 = 0; public destructor() {} public clone(): S { return new S(); } }
public function f1(xs: &R[]): void { const c = [...xs]; }
public function f2(xs: &P[]): void { const c = [...xs]; }
public function f3(xs: &S[]): void { const c = [...xs]; }
",
            want: &[
                (4, "EN0438", "`R` is not `Clone`"),
                (5, "EN0438", "`P` is not `Clone`"),
            ],
        }],
    },
    DocRow {
        starts: "`private const Y = [...X];`",
        gives: "EN0412 with the note, before any EN0401",
        programs: &[RowProgram {
            name: "a spread in each constant context",
            source: "assert([...X].length() == 3, \"three\");

private const X: i64[3] = [1, 2, 3];
private const Y: i64[3] = [...X];
private unsafe let counts: i64[3] = [...X];
private const Z: u8[[...X].length()] = [0; 3];
private const W: u8[3] = [0; [...X].length()];
private const V = [...X];
",
            want: &[
                (1, "EN0412", "`...` is not constant"),
                (4, "EN0412", "`...` is not constant"),
                (5, "EN0412", "`...` is not constant"),
                (6, "EN0412", "`...` is not constant"),
                (7, "EN0412", "`...` is not constant"),
                (8, "EN0412", "`...` is not constant"),
            ],
        }],
    },
    DocRow {
        starts: "`const ys = [...xs];` in a function",
        gives: "Compiles",
        programs: &[RowProgram {
            name: "a spread in a body and in a field initialiser",
            source: "private const BASE: i64[2] = [1, 2];
public class Bag { public items: i64[] = [...BASE]; }
public function f(xs: i64[]): void { const ys = [...xs]; }
",
            want: &[],
        }],
    },
    DocRow {
        starts: "`[...p]` under `p != null`",
        gives: "Compiles",
        programs: &[RowProgram {
            name: "a spread of a narrowed array and of a loop's binding",
            source: "public function f(p: i64[] | null): void { if (p != null) { const a = [...p]; } }
public function g(rows: i64[][]): void { for (const x of rows) { const b = [...x]; } }
",
            want: &[],
        }],
    },
    DocRow {
        starts: "`for (const j of [...queue]) { queue.push(s); }`",
        gives: "Compiles",
        programs: &[RowProgram {
            name: "a spread as a loop's source, and of a clone",
            source: "public function f(queue: string[], s: string): void {
  for (const j of [...queue]) { queue.push(s); }
  const c = [...queue.clone()];
}
",
            want: &[],
        }],
    },
];

/// `f` with `body` under `if (p != null)`, `p: string[] | null`; the body starts on
/// line 3.
macro_rules! under_p {
    ($body:literal) => {
        concat!(
            "public function f(p: string[] | null, c: bool): void {\n  if (p != null) {\n",
            $body,
            "  }\n}\n"
        )
    };
}

const NO_LENGTH: &str = "`string[] | null` has no member `length`";
const NOT_NARROWED: &str = "expected `&string[]`, found `&(string[] | null)`";

/// TESTING 18's narrowed `for...of` rows (T:723-732), their phase 2 parts.
const FOR_OF_ROWS: &[DocRow] = &[
    DocRow {
        starts: "Under `p != null`: `for (const x of &p) { p = null; break; }`; `for (const x of &p) { p = null; if (p == null) { break; } }` |",
        gives: "Compiles; EN0706",
        programs: &[
            RowProgram {
                name: "a held source changed before a `break` passes typing (its EN0706 is phase 3)",
                source: under_p!("    for (const x of &p) { p = null; break; }\n"),
                want: &[],
            },
            RowProgram {
                name: "a held source changed before a conditional `break` passes typing",
                source: under_p!(
                    "    for (const x of &p) { p = null; if (p == null) { break; } }\n"
                ),
                want: &[],
            },
        ],
    },
    DocRow {
        starts: "Under `p != null`, with `p: string[] \\| null`: `for (const x of &p) { p = null; break; } console.log(p.length());`",
        gives: "EN0303; EN0401",
        programs: &[
            RowProgram {
                name: "a `break` without the fact loses it after the loop",
                source: under_p!(
                    "    for (const x of &p) { p = null; break; }\n    console.log(p.length());\n"
                ),
                want: &[(4, "EN0303", NO_LENGTH)],
            },
            RowProgram {
                name: "the same, read as a reference",
                source: under_p!(
                    "    for (const x of &p) { p = null; break; }\n    const r: &string[] = &p;\n"
                ),
                want: &[(4, "EN0401", NOT_NARROWED)],
            },
        ],
    },
    DocRow {
        starts: "Under `p != null`, with `p: string[] \\| null`: `outer: for (const a of &p) { for (const x of &p) { p = null; break outer; } } console.log(p.length());`",
        gives: "EN0303; EN0401",
        programs: &[
            RowProgram {
                name: "a `break outer` records its state for `outer`",
                source: under_p!(
                    "    outer: for (const a of &p) { for (const x of &p) { p = null; break outer; } }\n    console.log(p.length());\n"
                ),
                want: &[(4, "EN0303", NO_LENGTH)],
            },
            RowProgram {
                name: "the same, read as a reference",
                source: under_p!(
                    "    outer: for (const a of &p) { for (const x of &p) { p = null; break outer; } }\n    const r: &string[] = &p;\n"
                ),
                want: &[(4, "EN0401", NOT_NARROWED)],
            },
        ],
    },
    DocRow {
        starts: "Under `p != null`: `for (const x of &p) { if (c) { p = null; break; } } console.log(p.length());`",
        gives: "EN0303 each",
        programs: &[
            RowProgram {
                name: "one `break` without the fact is enough",
                source: under_p!(
                    "    for (const x of &p) { if (c) { p = null; break; } }\n    console.log(p.length());\n"
                ),
                want: &[(4, "EN0303", NO_LENGTH)],
            },
            RowProgram {
                name: "even when the back edge has it",
                source: under_p!(
                    "    for (const x of &p) { p = null; if (p == null) { break; } }\n    console.log(p.length());\n"
                ),
                want: &[(4, "EN0303", NO_LENGTH)],
            },
        ],
    },
    DocRow {
        starts: "Under `p != null`: `outer: for (const a of &p) { while (c) { p = null; break outer; } }` |",
        gives: "Compiles with no warning",
        programs: &[RowProgram {
            name: "a source fact is not checked at the back edges",
            source: under_p!(
                "    outer: for (const a of &p) { while (c) { p = null; break outer; } }\n"
            ),
            want: &[],
        }],
    },
    DocRow {
        starts: "Under `p != null`: `for (const x of &p) { if (c) { break; } } console.log(p.length());`",
        gives: "Compiles with no warning",
        programs: &[RowProgram {
            name: "every `break` holding the fact, a `return` and an inner `break` keep it",
            source: under_p!(
                "    for (const x of &p) { if (c) { break; } }
    console.log(p.length());
    for (const x of &p) { if (c) { p = null; return; } }
    console.log(p.length());
    outer: for (const a of &p) { for (const x of &p) { if (c) { p = null; break outer; } } console.log(p.length()); }
"
            ),
            want: &[],
        }],
    },
    DocRow {
        starts: "Under `p != null`: `for (const x of [...p]) { p = null; }`",
        gives: "Compiles",
        programs: &[RowProgram {
            name: "a source evaluated once uses its fact before the body's kill",
            source: "public function f(p: i64[] | null): void {
  if (p != null) { for (const x of [...p]) { p = null; } }
}
public function g(): void {
  let p: i64[] | null = [1, 2, 3];
  if (p != null) { for (const x of &p) { *x = 1; } }
}
public function h(p: string[] | null): void {
  if (p != null) { for (const x of &p) { console.log(p.length()); p = null; break; } }
}
",
            want: &[],
        }],
    },
    DocRow {
        starts: "Under `o != null`: `for (const x of o.kids()) { o = null; }`",
        gives: "No EN0401, because the source is evaluated once",
        programs: &[RowProgram {
            name: "a method's result as the source is typed once (its EN0706 is phase 3)",
            source: "public class T { public kids(): &i64[] { unreachable(); } }
public function f(o: T | null): void {
  if (o != null) { for (const x of o.kids()) { o = null; } }
}
",
            want: &[],
        }],
    },
    DocRow {
        starts: "`S2-24-narrowed`:",
        gives: "Compile, and print",
        programs: &[RowProgram {
            name: "`S2-24-narrowed`'s three programs pass typing",
            source: "public class Bag { public items: i64[] | null = null; }
public function bump(xs?: &Slice<i64>): void { if (xs != null) { for (const x of xs) { *x += 1; } } }
public function f(b: Bag): void {
  b.items = [1, 5, 3, 7];
  let keep: &i64 | null = null;
  if (b.items != null) { for (const x of &b.items) { if (*x > 2) { keep = x; } } }
  if (keep != null) { *keep = 0; }
  console.log(b.items);
  let p: i64[] | null = [1, 2, 3];
  if (p != null) { for (const x of &p) { *x += 1; } }
  console.log(p);
  let v: i64[] = [1, 2, 3];
  bump(v.slice(0, 3));
  console.log(v);
}
",
            want: &[],
        }],
    },
];

// ---------------------------------------------------------------------------------
// SPEC 11's worked sizes, as compile-time asserts.

const TARGETS: [(&str, usize); 2] = [("i386-linux", 1), ("x86_64-linux", 2)];

const SIZES_HEADER: &str = "| Type | `P == 4` | `P == 8` |";

/// The cells of a SPEC table line, with `\|` read back as `|`.
fn spec_cells(line: &str) -> Vec<String> {
    let inner = line.trim().trim_start_matches('|');
    let mut out = Vec::new();
    let mut cell = String::new();
    let mut chars = inner.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\\' if chars.peek() == Some(&'|') => {
                cell.push('|');
                chars.next();
            }
            '|' => out.push(std::mem::take(&mut cell).trim().to_owned()),
            _ => cell.push(c),
        }
    }
    out
}

/// SPEC 11's worked sizes: each row's declaration (empty for a type) and type, with
/// its size at `P == 4` and at `P == 8`. "same with `level: i32` added" is the row
/// above with that field appended.
fn worked_sizes() -> Vec<(String, String, [u64; 2])> {
    let spec = read("docs/SPEC.md");
    let mut lines = spec.lines().skip_while(|line| line.trim() != SIZES_HEADER);
    assert!(lines.next().is_some(), "SPEC has no table {SIZES_HEADER:?}");
    lines.next();
    let mut rows: Vec<(String, String, [u64; 2])> = Vec::new();
    for line in lines.take_while(|line| line.starts_with('|')) {
        let row = spec_cells(line);
        let text = if row[0].starts_with("same with ") {
            let field = row[0].split('`').nth(1).expect("a field");
            let previous = &rows.last().expect("a row above").0;
            let close = previous.rfind('}').expect("a declaration");
            format!("{}public {field}; }}", &previous[..close])
        } else {
            row[0].split('`').nth(1).expect("a type").to_owned()
        };
        let size = |cell: &str| cell.parse::<u64>().expect("a size");
        let words: Vec<&str> = text.split_whitespace().collect();
        let (decl, ty) = match words.iter().position(|w| *w == "class" || *w == "enum") {
            Some(at) => (text.clone(), words[at + 1].trim_end_matches('{').to_owned()),
            None => (String::new(), text.clone()),
        };
        rows.push((decl, ty, [size(&row[1]), size(&row[2])]));
    }
    rows
}

/// The program asserting one worked size: the declaration, then the assert on line
/// 2.
fn size_program(decl: &str, ty: &str, size: u64) -> String {
    format!("{decl}\nassert(sizeOf<{ty}>() == {size});\n")
}

fn sizes_hold(target: &str, column: usize) -> Result<(), String> {
    let rows = worked_sizes();
    if rows.len() != 8 {
        return Err(format!("SPEC 11 has {} worked sizes, not 8", rows.len()));
    }
    let mut failures = Vec::new();
    for (decl, ty, sizes) in &rows {
        let size = sizes[column - 1];
        let source = size_program(decl, ty, size);
        let ran = check_source(&source, &[&format!("--target={target}")]);
        if let Some(problem) = mismatch(&ran, &[]) {
            failures.push(format!(
                "sizeOf<{ty}>() is not {size} on {target}: {problem}"
            ));
        }
    }
    if failures.is_empty() {
        Ok(())
    } else {
        Err(failures.join("\n"))
    }
}

// ---------------------------------------------------------------------------------
// Maranget against brute force, through the command line.

/// The type a column matches on.
#[derive(Copy, Clone, Debug, PartialEq)]
enum Subject {
    /// `E<n>`, a payload-free enum of `n` cases, maybe `| null`.
    Enum(u32, bool),
    /// `bool`, maybe `| null`.
    Bool(bool),
    Int,
}

/// One value an arm names.
#[derive(Copy, Clone, Debug, PartialEq)]
enum ArmValue {
    Default,
    Null,
    Case(u32),
    Bool(bool),
    Int(i64),
    /// A half-open range, maybe empty.
    Range(i64, i64),
}

#[derive(Clone, Debug, PartialEq)]
struct MatchArm {
    values: Vec<ArmValue>,
    guarded: bool,
}

#[derive(Clone, Debug, PartialEq)]
struct Column {
    subject: Subject,
    arms: Vec<MatchArm>,
}

/// A value of a subject, in the finite model the brute force walks.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum Point {
    Null,
    Case(u32),
    Bool(bool),
    Int(i64),
}

const CASE_NAMES: [&str; 6] = ["A", "B", "C", "D", "E", "F"];

impl Column {
    /// Every value of the subject, or for an integer every literal, both ends of
    /// every range and the integer outside each end, and one that no arm names: an
    /// uncovered stretch of integers starts at one of these, so the model is exact.
    fn points(&self) -> Vec<Point> {
        let mut points: BTreeSet<Point> = BTreeSet::new();
        match self.subject {
            Subject::Enum(n, nullable) => {
                points.extend((0..n).map(Point::Case));
                if nullable {
                    points.insert(Point::Null);
                }
            }
            Subject::Bool(nullable) => {
                points.extend([Point::Bool(false), Point::Bool(true)]);
                if nullable {
                    points.insert(Point::Null);
                }
            }
            Subject::Int => {
                points.insert(Point::Int(1_000_000));
                for value in self.arms.iter().flat_map(|arm| &arm.values) {
                    match *value {
                        ArmValue::Int(n) => points.extend([n - 1, n, n + 1].map(Point::Int)),
                        ArmValue::Range(lo, hi) => {
                            points.extend([lo - 1, lo, hi - 1, hi].map(Point::Int));
                        }
                        _ => {}
                    }
                }
            }
        }
        points.into_iter().collect()
    }

    /// The source of the column as the function `f<index>`, one arm per line.
    fn function(&self, index: usize) -> String {
        let ty = match self.subject {
            Subject::Enum(n, false) => format!("E{n}"),
            Subject::Enum(n, true) => format!("E{n} | null"),
            Subject::Bool(false) => "bool".to_owned(),
            Subject::Bool(true) => "bool | null".to_owned(),
            Subject::Int => "i64".to_owned(),
        };
        let mut out = format!("public function f{index}(s: {ty}, g: bool): i64 {{\n");
        out.push_str("  return match (s) {\n");
        for arm in &self.arms {
            let values: Vec<String> = arm
                .values
                .iter()
                .map(|value| match *value {
                    ArmValue::Default => "default".to_owned(),
                    ArmValue::Null => "null".to_owned(),
                    ArmValue::Case(c) => match self.subject {
                        Subject::Enum(n, _) => format!("E{n}.{}", CASE_NAMES[c as usize]),
                        _ => unreachable!("a case of an enum"),
                    },
                    ArmValue::Bool(b) => b.to_string(),
                    ArmValue::Int(n) => n.to_string(),
                    ArmValue::Range(lo, hi) => format!("{lo}..{hi}"),
                })
                .collect();
            let guard = if arm.guarded { " if g" } else { "" };
            writeln!(out, "    {}{guard} => 1,", values.join(", ")).expect("a string");
        }
        out.push_str("  };\n}\n");
        out
    }
}

/// Whether an arm value matches a point.
fn matches_point(value: ArmValue, point: Point) -> bool {
    match (value, point) {
        (ArmValue::Default, _) => true,
        (ArmValue::Null, Point::Null) => true,
        (ArmValue::Case(c), Point::Case(d)) => c == d,
        (ArmValue::Bool(a), Point::Bool(b)) => a == b,
        (ArmValue::Int(n), Point::Int(m)) => n == m,
        (ArmValue::Range(lo, hi), Point::Int(m)) => lo <= m && m < hi,
        _ => false,
    }
}

/// The brute force: whether some point no unguarded arm matches is left, and for
/// each arm, whether each of its values matches a point that neither an earlier
/// unguarded arm nor an earlier value of its own arm does, whatever the arm's
/// guard: the values of one arm share it (`A, A` leaves the second unreachable).
fn brute(column: &Column) -> (bool, Vec<Vec<bool>>) {
    let points = column.points();
    let mut covered: BTreeSet<Point> = BTreeSet::new();
    let mut reach = Vec::new();
    for arm in &column.arms {
        let mut own = covered.clone();
        let flags: Vec<bool> = arm
            .values
            .iter()
            .map(|&value| {
                let reached = points
                    .iter()
                    .any(|&point| matches_point(value, point) && !own.contains(&point));
                own.extend(points.iter().filter(|&&p| matches_point(value, p)));
                reached
            })
            .collect();
        reach.push(flags);
        if !arm.guarded {
            for &value in &arm.values {
                covered.extend(points.iter().filter(|&&p| matches_point(value, p)));
            }
        }
    }
    let missing = points.iter().any(|point| !covered.contains(point));
    (missing, reach)
}

/// What `check` must report on `column` written as a function from line `first`:
/// EN0501 at the `match` when a point is left, and EN0503 at an arm whose values are
/// all unreachable, once, or else once per unreachable value.
fn predicted(column: &Column, first: usize) -> Vec<(usize, String)> {
    let (missing, reach) = brute(column);
    let mut out = Vec::new();
    if missing {
        out.push((first + 1, "EN0501".to_owned()));
    }
    for (index, flags) in reach.iter().enumerate() {
        let line = first + 2 + index;
        let dead = flags.iter().filter(|reached| !**reached).count();
        let count = if dead == flags.len() { 1 } else { dead };
        out.extend((0..count).map(|_| (line, "EN0503".to_owned())));
    }
    out
}

/// A random column. Even indexes match on a nullable enum; the others on an enum,
/// a boolean, maybe nullable, or an integer with literals, ranges and `default`.
fn gen_column(rng: &mut Xoshiro256, nullable_enum: bool) -> Column {
    let subject = if nullable_enum {
        Subject::Enum(1 + rng.below(6) as u32, true)
    } else {
        match rng.below(4) {
            0 => Subject::Enum(1 + rng.below(6) as u32, false),
            1 => Subject::Bool(rng.below(2) == 0),
            _ => Subject::Int,
        }
    };
    let atoms: Vec<ArmValue> = match subject {
        Subject::Enum(n, nullable) => (0..n)
            .map(ArmValue::Case)
            .chain(nullable.then_some(ArmValue::Null))
            .collect(),
        Subject::Bool(nullable) => [ArmValue::Bool(false), ArmValue::Bool(true)]
            .into_iter()
            .chain(nullable.then_some(ArmValue::Null))
            .collect(),
        Subject::Int => Vec::new(),
    };
    let count = 1 + rng.below(6) as usize;
    let mut arms = Vec::new();
    for _ in 0..count {
        let guarded = rng.below(5) == 0;
        let int_value = |rng: &mut Xoshiro256| {
            let lo = rng.below(9) as i64;
            if rng.below(2) == 0 {
                ArmValue::Int(lo - 3)
            } else {
                ArmValue::Range(lo, lo + rng.below(6) as i64)
            }
        };
        let mut values = if rng.below(if subject == Subject::Int { 4 } else { 8 }) == 0 {
            vec![ArmValue::Default]
        } else if subject == Subject::Int {
            vec![int_value(rng)]
        } else {
            vec![atoms[rng.below(atoms.len() as u64) as usize]]
        };
        // A second value in the same arm, a third of the time: the same one again,
        // any atom, or an integer or range that may overlap the first, so an arm's
        // earlier values covering its later ones is exercised too. (`default` may
        // not follow another value: that is EN0100.)
        if values[0] != ArmValue::Default && rng.below(3) == 0 {
            let second = match rng.below(4) {
                0 => values[0],
                _ if subject == Subject::Int => int_value(rng),
                _ => atoms[rng.below(atoms.len() as u64) as usize],
            };
            values.push(second);
        }
        arms.push(MatchArm { values, guarded });
    }
    Column { subject, arms }
}

/// The declarations every program of columns starts with: `E1` to `E6`, on lines 1
/// to 6.
fn prelude() -> String {
    let mut out = String::new();
    for n in 1..=6 {
        writeln!(out, "public enum E{n} {{ {} }}", CASE_NAMES[..n].join(", ")).expect("a string");
    }
    out
}

/// Runs `columns` as one program and returns each column whose diagnostics differ
/// from the brute force's, with its function, what was reported and what was due.
fn disagreements(columns: &[Column]) -> Vec<String> {
    disagreements_with(columns, &predicted)
}

/// [`disagreements`] against the diagnostics `predict` says are due.
fn disagreements_with(
    columns: &[Column],
    predict: &dyn Fn(&Column, usize) -> Vec<(usize, String)>,
) -> Vec<String> {
    let mut source = prelude();
    let mut spans = Vec::new();
    for (index, column) in columns.iter().enumerate() {
        let first = source.lines().count() + 1;
        let function = column.function(index);
        let last = first + function.lines().count() - 1;
        spans.push((first, last));
        source.push_str(&function);
    }
    let ran = check_source(&source, &[]);
    let found: Vec<(usize, String)> = reported(&ran.stderr)
        .iter()
        .map(|diag| (diag.line().unwrap_or(0), diag.code.clone()))
        .collect();
    let mut out = Vec::new();
    let stray: Vec<&(usize, String)> = found
        .iter()
        .filter(|(line, code)| {
            !(code == "EN0501" || code == "EN0503")
                || !spans.iter().any(|(a, b)| a <= line && line <= b)
        })
        .collect();
    if !stray.is_empty() || !ran.stdout.is_empty() {
        out.push(format!(
            "unexpected output {stray:?} {:?}\n{}",
            ran.stdout, ran.stderr
        ));
    }
    let errors = found.iter().any(|(_, code)| code == "EN0501");
    if ran.code != i32::from(errors) {
        out.push(format!("exit {} with EN0501 {errors}", ran.code));
    }
    for (column, &(first, last)) in columns.iter().zip(&spans) {
        let mut got: Vec<(usize, String)> = found
            .iter()
            .filter(|(line, _)| first <= *line && *line <= last)
            .cloned()
            .collect();
        got.sort();
        let mut due = predict(column, first);
        due.sort();
        if got != due {
            let text: String = source.lines().skip(first - 1).take(last + 1 - first).fold(
                String::new(),
                |mut text, line| {
                    text.push_str(line);
                    text.push('\n');
                    text
                },
            );
            out.push(format!("reported {got:?}, the brute force {due:?}\n{text}"));
        }
    }
    out
}

/// Columns whose verdicts were checked by hand against the binary's output.
fn hand_checked() -> Vec<(Column, Vec<(usize, &'static str)>)> {
    let arm = |values: &[ArmValue], guarded: bool| MatchArm {
        values: values.to_vec(),
        guarded,
    };
    use ArmValue::*;
    vec![
        (
            // A duplicate case, and a guarded one that leaves `B` and `C` unmatched.
            Column {
                subject: Subject::Enum(3, false),
                arms: vec![
                    arm(&[Case(0)], false),
                    arm(&[Case(0)], false),
                    arm(&[Case(1)], true),
                ],
            },
            vec![(2, "EN0501"), (4, "EN0503")],
        ),
        (
            // Every value named, so the `default` after them is never reached.
            Column {
                subject: Subject::Enum(3, true),
                arms: vec![
                    arm(&[Null], false),
                    arm(&[Case(0), Case(1)], false),
                    arm(&[Case(2)], false),
                    arm(&[Default], false),
                ],
            },
            vec![(6, "EN0503")],
        ),
        (
            // An empty range, one inside an earlier range, and a guarded `default`.
            Column {
                subject: Subject::Int,
                arms: vec![
                    arm(&[Int(1)], false),
                    arm(&[Range(0, 5)], false),
                    arm(&[Range(3, 3)], false),
                    arm(&[Range(2, 4)], false),
                    arm(&[Default], true),
                ],
            },
            vec![(2, "EN0501"), (5, "EN0503"), (6, "EN0503")],
        ),
        (
            // An arm of two values, both handled: one EN0503 for the arm.
            Column {
                subject: Subject::Bool(true),
                arms: vec![
                    arm(&[Bool(true)], false),
                    arm(&[Bool(false), Null], false),
                    arm(&[Bool(true), Bool(false)], false),
                ],
            },
            vec![(5, "EN0503")],
        ),
        (
            // An arm of two values, one handled: one EN0503 for that value.
            Column {
                subject: Subject::Enum(2, false),
                arms: vec![arm(&[Case(0)], false), arm(&[Case(0), Case(1)], false)],
            },
            vec![(4, "EN0503")],
        ),
        (
            // The same case twice in one arm: its first value covers its second.
            Column {
                subject: Subject::Enum(2, false),
                arms: vec![arm(&[Case(0), Case(0)], false), arm(&[Case(1)], false)],
            },
            vec![(3, "EN0503")],
        ),
        (
            // The same, under the arm's guard, which its values share; the `match`
            // then misses `A`.
            Column {
                subject: Subject::Enum(2, false),
                arms: vec![arm(&[Case(0), Case(0)], true), arm(&[Case(1)], false)],
            },
            vec![(2, "EN0501"), (3, "EN0503")],
        ),
        (
            // Overlapping ranges in one arm, the second inside the first.
            Column {
                subject: Subject::Int,
                arms: vec![
                    arm(&[Range(0, 5), Range(1, 3)], false),
                    arm(&[Default], false),
                ],
            },
            vec![(3, "EN0503")],
        ),
    ]
}

pub fn register(h: &mut Harness) {
    h.case(
        "row/the brute force predicts the hand-checked columns",
        || {
            for (column, wanted) in hand_checked() {
                let wanted: Vec<(usize, String)> = wanted
                    .into_iter()
                    .map(|(line, code)| (line, code.to_owned()))
                    .collect();
                let mut got = predicted(&column, 1);
                got.sort();
                assert_eq!(got, wanted, "{}", column.function(0));
                assert_eq!(disagreements(&[column]), Vec::<String>::new());
            }
        },
    );
    h.case(
        "row/Maranget agrees with brute force through enrang check",
        || {
            let mut rng = rng_for("row/maranget");
            let total = scaled(400);
            let mut columns: Vec<Column> = (0..total)
                .map(|index| gen_column(&mut rng, index % 2 == 0))
                .collect();
            let exhaustive = columns.iter().filter(|c| !brute(c).0).count();
            let dead = columns
                .iter()
                .filter(|c| brute(c).1.iter().flatten().any(|reached| !reached))
                .count();
            // Both verdicts come often, and half the columns are nullable enums.
            assert!(exhaustive * 10 >= total && (total - exhaustive) * 10 >= total);
            assert!(
                dead * 10 >= total,
                "{dead} of {total} have an unreachable value"
            );
            let mut found = Vec::new();
            while !columns.is_empty() {
                let rest = columns.split_off(columns.len().min(50));
                found.extend(disagreements(&columns));
                columns = rest;
            }
            assert!(found.is_empty(), "{}", found.join("\n\n"));
        },
    );
    h.case(
        "row/the spread typing and Clone rows of TESTING 18 through enrang check",
        || check_rows(SPREAD_ROWS),
    );
    h.case(
        "row/the narrowed for...of rows of TESTING 18 through enrang check",
        || check_rows(FOR_OF_ROWS),
    );
    h.case(
        "row/every spread typing and Clone row of TESTING 18 has its programs or says why not",
        || {
            let testing = read("docs/TESTING.md");
            doc_rows_tied(
                &spread_section(&testing),
                SPREAD_ROWS,
                SPREAD_WITHOUT_PROGRAM,
            )
        },
    );
    h.case(
        "row/every narrowed for...of row of TESTING 18 has its programs or says why not",
        || {
            let testing = read("docs/TESTING.md");
            doc_rows_tied(
                &for_of_section(&testing),
                FOR_OF_ROWS,
                FOR_OF_WITHOUT_PROGRAM,
            )
        },
    );
    h.case("row/a row deleted or added breaks the tie", || {
        let lines = [
            "| `a` x | Compiles |",
            "| `b` y | EN0706 |",
            "| `c` z | EN0401 |",
        ];
        assert_eq!(rows_tied(&lines, &["`a`", "`c`"], &["`b`"]), Ok(()));
        // A DocRow deleted (m29), a document row added, a stale exemption, and a
        // line two entries open.
        assert!(rows_tied(&lines, &["`a`"], &["`b`"]).is_err());
        assert!(rows_tied(&lines[..2], &["`a`", "`c`"], &["`b`"]).is_err());
        assert!(rows_tied(&lines, &["`a`", "`c`"], &["`b`", "`d`"]).is_err());
        assert!(rows_tied(&lines, &["`a`", "`c`", "`a` x"], &["`b`"]).is_err());
        let testing = read("docs/TESTING.md");
        let rest: Vec<&DocRow> = SPREAD_ROWS
            .iter()
            .filter(|row| row.starts != "`private const Y = [...X];`")
            .collect();
        let starts: Vec<&str> = rest.iter().map(|row| row.starts).collect();
        assert!(rows_tied(&spread_section(&testing), &starts, SPREAD_WITHOUT_PROGRAM).is_err());
    });
    for (target, column) in TARGETS {
        h.case(
            format!("row/SPEC 11's worked sizes hold on {target}"),
            move || sizes_hold(target, column),
        );
    }
    h.case(
        "row/a worked size one byte off is EN0415 on both targets",
        || {
            let mut ran_programs = 0;
            for (target, column) in TARGETS {
                for (decl, ty, sizes) in worked_sizes() {
                    let source = size_program(&decl, &ty, sizes[column - 1] + 1);
                    let ran = check_source(&source, &[&format!("--target={target}")]);
                    let wanted = [(2, "EN0415", "compile-time assert failed")];
                    if let Some(problem) = mismatch(&ran, &wanted) {
                        panic!("sizeOf<{ty}>() on {target}: {problem}");
                    }
                    ran_programs += 1;
                }
            }
            // The 8 worked sizes on each of the 2 targets, as the holding cases run.
            assert_eq!(ran_programs, 8 * TARGETS.len(), "programs run");
        },
    );
    h.case("row/each check here sees what it must", || {
        // A program giving a diagnostic its row does not, or missing one it does,
        // or a later phase's diagnostic mistaken for phase 2's.
        let clean = check_source("public function f(): void { }\n", &[]);
        assert_eq!(mismatch(&clean, &[]), None);
        assert!(mismatch(&clean, &[(1, "EN0401", "")]).is_some());
        let wrong = check_source("const a: string = 5;\n", &[]);
        assert!(mismatch(&wrong, &[]).is_some());
        assert_eq!(mismatch(&wrong, &[(1, "EN0401", "mismatched types")]), None);
        assert!(mismatch(&wrong, &[(1, "EN0401", "no such words")]).is_some());
        assert!(mismatch(&wrong, &[(2, "EN0401", "mismatched types")]).is_some());
        assert!(compared("EN0401") && compared("EN0201") && compared("EN1305"));
        assert!(!compared("EN0706") && !compared("EN0435") && !compared("T0001"));
        // A planted disagreement: a brute force that lets a guarded arm cover its
        // values, a plausible bug, disagrees with the binary on `E2.A if g, E2.B`.
        let column = Column {
            subject: Subject::Enum(2, false),
            arms: vec![
                MatchArm {
                    values: vec![ArmValue::Case(0)],
                    guarded: true,
                },
                MatchArm {
                    values: vec![ArmValue::Case(1)],
                    guarded: false,
                },
            ],
        };
        let mutant = |column: &Column, first: usize| {
            let mut unguarded = column.clone();
            for arm in &mut unguarded.arms {
                arm.guarded = false;
            }
            predicted(&unguarded, first)
        };
        let columns = std::slice::from_ref(&column);
        assert_eq!(disagreements(columns), Vec::<String>::new());
        assert_eq!(disagreements_with(columns, &mutant).len(), 1);
    });
    for name in M3_GATES {
        h.case(name, move || {
            let report = m3_report(&real_m3_gate(name), CURRENT_MILESTONE);
            assert!(report.is_clean(), "\n{report}");
        });
    }
    h.case(
        "row/M3: before the bump nothing here is due, and at the bump every line is",
        || {
            for name in M3_GATES {
                let lines = real_m3_gate(name);
                assert!(!lines.is_empty(), "{name}: no lines");
                assert!(
                    lines.iter().all(|line| line.since == M3_ROW_SINCE),
                    "{name}: a line not due at M3"
                );
                assert_eq!(m3_report(&lines, Milestone::M2).enforced, 0, "{name}");
                for current in [CURRENT_MILESTONE, Milestone::M3] {
                    let problems = bump_problems(&lines, current);
                    assert!(problems.is_empty(), "{name} at {current}: {problems:?}");
                }
                assert_eq!(
                    m3_report(&lines, Milestone::M3).enforced,
                    lines.len(),
                    "{name}"
                );
            }
        },
    );
    h.case("row/M3: each M3 check here sees what it must", || {
        let ran = |code: i32, stdout: &str| Ran {
            stdout: stdout.to_owned(),
            stderr: String::new(),
            code,
        };
        // A verifier failure is exit 3; a near-miss must print its module, after
        // its target line for a target other than the default, or nothing when no
        // module has a body.
        assert!(verified(true, &ran(0, "module \"m\";\n")));
        assert!(verified(true, &ran(0, "target \"i386-linux\";\nmodule \"m\";\n")));
        assert!(verified(true, &ran(0, "")));
        assert!(!verified(true, &ran(0, "target \"i386-linux\";\n")));
        assert!(!verified(true, &ran(0, "target \"i386-linux\";\nfn f() {}\n")));
        assert!(!verified(true, &ran(0, "fn f() -> void {\n}\n")));
        assert!(!verified(true, &ran(0, "modules\n")));
        assert!(!verified(true, &ran(1, "")));
        assert!(verified(false, &ran(1, "")));
        assert!(!verified(false, &ran(3, "")));
        assert!(!verified(true, &ran(3, "module \"m\";\n")));
        // The narrowed head: both checks before the projection, the tag check right
        // before it; a head with one missing or out of place is seen.
        let good = "  bb4: {\n    storage_live(_8);\n    check_bounds(copy _5, copy _6);\n    \
                    check_tag(_1, Present);\n    _8 = &(_1 as Present).0[_5] [for-of-element];\n  }\n";
        assert_eq!(narrowed_head_problems(good), Vec::<String>::new());
        let no_bounds = good.replace("    check_bounds(copy _5, copy _6);\n", "");
        assert_eq!(narrowed_head_problems(&no_bounds).len(), 1);
        let swapped = good
            .replace("    check_bounds(copy _5, copy _6);\n", "")
            .replace("    check_tag(_1, Present);\n", "    check_tag(_1, Present);\n    check_bounds(copy _5, copy _6);\n");
        assert_eq!(narrowed_head_problems(&swapped).len(), 1);
        let other_block = good.replace("    check_tag(_1, Present);\n", "  }\n  bb5: {\n    check_tag(_1, Present);\n");
        assert_eq!(narrowed_head_problems(&other_block).len(), 1);
        let bare = "  bb4: {\n    _8 = &(_1 as Present).0[_5] [for-of-element];\n  }\n";
        assert_eq!(narrowed_head_problems(bare).len(), 2);
        assert_eq!(
            narrowed_head_problems("fn f() {\n}\n"),
            ["no element borrow through a narrowed payload"]
        );
        // The drop traces: enough goldens, three tag switches, and the suite.
        let golden = |name: &str, text: &str| (name.to_owned(), text.to_owned());
        let ladder = "  bb0: {\n    _4 = discriminant(_1);\n    switch move _4 [0: bb1, otherwise: bb2];\n  }\n  bb1: {\n    drop_glue((_1 as Ok).value);\n";
        let late = "  bb0: {\n    drop_glue((_1 as Ok).value);\n    _4 = discriminant(_1);\n    switch move _4 [0: bb1];\n";
        let some = vec![
            golden("partly_moved_nullable.mir", ladder),
            golden("partly_moved_result.mir", late),
            golden("c.mir", "switch"),
        ];
        let ids = |lines: Vec<Line>| -> Vec<FixtureStatus> { lines.into_iter().map(|l| l.status).collect() };
        let (p, m) = (FixtureStatus::Passing, FixtureStatus::Missing);
        // The result's switch comes after its ladder, the enum's trace is missing.
        assert_eq!(ids(drop_lines(&some, 0, Some("pipeline/drops"))), [p, p, m, m, p]);
        assert_eq!(ids(drop_lines(&some, 1, None)), [m, p, m, m, m]);
        let mut all: Vec<(String, String)> = PARTLY_MOVED.iter().map(|n| golden(&format!("{n}.mir"), ladder)).collect();
        all.extend((0..5).map(|n| golden(&format!("{n}.mir"), "switch")));
        assert_eq!(ids(drop_lines(&all, 5, Some("x pipeline/drops"))), [p, p, p, p, p]);
        // A trace that switches on no tag, or names another file, is no evidence.
        assert!(!tag_switch_before_ladder("    switch copy _8 [0: bb1];\n    drop_glue((_1 as Ok).value);\n"));
        assert!(tag_switch_before_ladder(ladder));
        all.retain(|(n, _)| n != "partly_moved_enum.mir");
        all.push(golden("partly_moved_enum_old.mir", ladder));
        assert_eq!(ids(drop_lines(&all, 5, Some("pipeline/drops"))), [p, p, p, m, p]);
        // The pipeline's round trip of every built body, and its verifier seams: each
        // seen from the real files, and a part removed is seen as missing.
        let real_rt = read(PIPELINE_ROUNDTRIP);
        let real_main = read(PIPELINE_MAIN);
        assert!(pipeline_roundtrips(Some(&real_rt), Some(&real_main)));
        assert!(!pipeline_roundtrips(Some(&real_rt), Some("mod roundtrip;")));
        assert!(!pipeline_roundtrips(Some(&real_rt.replace("again == text", "true")), Some(&real_main)));
        assert!(!pipeline_roundtrips(None, Some(&real_main)));
        let real_verify = read(PIPELINE_VERIFY);
        assert!(pipeline_seams(Some(&real_verify)));
        assert!(!pipeline_seams(Some(&real_verify.replace("enrang_driver::emit(&checked, enrang_driver::Emit::Mir)", "Ok(())"))));
        assert!(!pipeline_seams(None));
        assert_eq!(d2_rows("  | Temporaries created in | End |\n  |---|---|\n  | a | b |\n  | c | d |\n\nx\n"), 2);
        assert_eq!(d2_rows(&read("docs/SPEC.md")), 5);
        // The --emit transcripts: a golden that worked, and each way one does not;
        // then the gate over fake goldens, a fake suite and a fake command line.
        let mir = "$ enrang check --emit=mir main.en\n[exit 0]\n[stdout]\nfn f() -> void {\n  phase elaborated;\n}\n[stderr]\n";
        let summary = "$ enrang check --emit=summary main.en\n[exit 0]\n[stdout]\nmodule \"main\"\n[stderr]\n";
        assert!(emit_golden_holds("mir", mir));
        assert!(emit_golden_holds("summary", summary));
        assert!(!emit_golden_holds("mir", &mir.replace("elaborated", "built")));
        assert!(!emit_golden_holds("mir", &mir.replace("[exit 0]", "[exit 1]")));
        assert!(!emit_golden_holds("mir", &format!("{mir}warning: x\n")));
        assert!(!emit_golden_holds("mir", &mir.replace("main.en", "other.en")));
        assert!(!emit_golden_holds("summary", mir));
        assert!(!emit_golden_holds("summary", &summary.replace("module ", "modules ")));
        let errors = "$ enrang check --emit=mir g.en\n[exit 1]\n[stdout]\n[stderr]\nerror: x\n";
        let entries: String = EMIT_MIR
            .iter()
            .chain(&EMIT_SUMMARY)
            .map(|name| format!("    (\n        \"{name}\",\n"))
            .collect();
        let suite = format!("        name: format!(\"check/emit-{{what}}/{{name}}.txt\"),\n{entries}");
        let project = "ProjectCase::new(\"check/emit_mir\", &[\"check\", \"--emit=mir\", \"main.en\"], 0)\n\"check/emit_mir_with_errors\",\n";
        let fake_read = |suite: String, project: &'static str| {
            move |path: &str| -> Option<String> {
                if path == EMIT_SUITE {
                    return Some(suite.clone());
                }
                if path == EMIT_PROJECT {
                    return Some(project.to_owned());
                }
                let name = path.strip_prefix(EMIT_DIR)?.strip_suffix(".txt")?;
                Some(match name {
                    "/emit_mir_with_errors" => errors.to_owned(),
                    "/emit_mir" => mir.to_owned(),
                    _ if name.starts_with("/emit-mir/") => mir.to_owned(),
                    _ => summary.to_owned(),
                })
            }
        };
        let fake_run = |stdout: &'static str| {
            move |_: &Place, args: &[String]| -> Ran {
                if args.last().is_some_and(|file| file == "g.en") {
                    Ran {
                        stdout: String::new(),
                        stderr: "error: x\n".to_owned(),
                        code: 1,
                    }
                } else {
                    ran(0, stdout)
                }
            }
        };
        let body = "fn f() -> void {\n  phase elaborated;\n}\n";
        let good = emit_lines(&fake_run(body), &fake_read(suite.clone(), project), "x", ("g.en", "y"));
        assert_eq!(ids(good), [p, p, p, p, p]);
        let drifted = emit_lines(&fake_run("fn g() {}\n"), &fake_read(suite.clone(), project), "x", ("g.en", "y"));
        assert_eq!(ids(drifted), [m, p, p, p, p]);
        let lost = suite.replace("        \"spread\",\n", "");
        let unmade = emit_lines(&fake_run(body), &fake_read(lost, project), "x", ("g.en", "y"));
        assert_eq!(ids(unmade), [p, p, p, p, m]);
        // A suite that runs a case per fixture, and one that does not.
        let source = "for (name, text) in fixtures(\"remap\") {\n h.case(format!(\"remap/{name}: x\"), ..)";
        assert!(suite_runs_each(source, "remap"));
        assert!(!suite_runs_each(source, "roundtrip"));
        assert!(!suite_runs_each("for (name, text) in fixtures(\"remap\") {}", "remap"));
    });
    let names: Vec<String> = h.names().map(str::to_owned).collect();
    h.case(
        "row/TESTING 23's M3 row is the list the meta suite enforces",
        || {
            let items = row_items(Milestone::M3);
            let mapped: Vec<String> = M3_ITEMS
                .iter()
                .map(|(item, _)| (*item).to_owned())
                .collect();
            assert_eq!(items, mapped);
            assert!(Milestone::M3 <= CURRENT_MILESTONE, "M3's row is enforced");
        },
    );
    let m3_names = names.clone();
    h.case(
        "row/every item of M3's row names meta cases that run",
        move || {
            for (item, cases) in M3_ITEMS {
                assert!(!cases.is_empty(), "{item}");
                for case in *cases {
                    assert!(
                        m3_names.iter().any(|name| name == case),
                        "{item}: no case {case:?}"
                    );
                }
            }
        },
    );
    h.case(
        "row/TESTING 23's M2 row is the list the meta suite enforces",
        || {
            let items = row_items(Milestone::M2);
            let mapped: Vec<String> = ITEMS.iter().map(|(item, _)| (*item).to_owned()).collect();
            assert_eq!(items, mapped);
            assert!(Milestone::M2 <= CURRENT_MILESTONE, "M2's row is enforced");
        },
    );
    h.case(
        "row/every item of M2's row names meta cases that run",
        move || {
            for (item, cases) in ITEMS {
                assert!(!cases.is_empty(), "{item}");
                for case in *cases {
                    assert!(
                        names.iter().any(|name| name == case),
                        "{item}: no case {case:?}"
                    );
                }
            }
        },
    );
}
