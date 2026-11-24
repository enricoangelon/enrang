//! The milestone of each case SPEC extracts (TESTING 17 and 18, M1 plan d.3).
//!
//! A case marker has no `since` field, so `tests/trace/case_since.txt` gives each case
//! its milestone: one `ID Mn` line per case, in SPEC order. From that milestone the
//! case is enforced: its command runs as a process in a fresh directory holding its
//! files, and the exit status, stdout and stderr equal SPEC's byte for byte. A case of
//! a later milestone claims nothing, however its command behaves today, since a
//! `check` that passes before borrows are checked is no evidence that borrows are.
//!
//! Before its own milestone a case may be due to parse: TESTING 23's M1 row says
//! that the tour and the `Ownership in three lines` block parse. Those rows are read
//! from TESTING 23, each with the milestone of its row, and gated the same way: from
//! that milestone each file of the case goes through `enrang check` as a process, in
//! a fresh directory holding the case's files, and must exit 0 with nothing on either
//! stream, which is what `check` prints for a file with no error.

use std::sync::OnceLock;

use enrang_cli::{LATER, WORKING};
use enrang_diag::{CURRENT_MILESTONE, Code, Milestone};
use enrang_testkit::{
    Case, FixtureStatus, GateReport, GateRow, Harness, StreamSource, extract_cases, gate,
};

use crate::support::{Place, fired_codes, milestone_in, read, run_cached, table_after};

/// The side table of case milestones.
pub const CASE_SINCE: &str = "tests/trace/case_since.txt";

pub fn spec_cases() -> &'static [Case] {
    static CASES: OnceLock<Vec<Case>> = OnceLock::new();
    CASES.get_or_init(|| {
        extract_cases(&read("docs/SPEC.md")).unwrap_or_else(|errors| panic!("{errors}"))
    })
}

/// A milestone written alone, as `M1`.
fn milestone_named(word: &str) -> Option<Milestone> {
    milestone_in(word).filter(|milestone| format!("{milestone:?}") == word)
}

/// The lines of the side table, or the first malformed one.
pub fn parse_case_since(text: &str) -> Result<Vec<(String, Milestone)>, String> {
    let mut rows = Vec::new();
    for (index, line) in text.lines().enumerate() {
        let words: Vec<&str> = line.split(' ').collect();
        let parsed = match words[..] {
            [id, since] if !id.is_empty() => milestone_named(since).map(|m| (id.to_owned(), m)),
            _ => None,
        };
        let row = parsed.ok_or_else(|| format!("line {}: {line:?} is not `ID Mn`", index + 1))?;
        rows.push(row);
    }
    Ok(rows)
}

pub fn case_since() -> Vec<(String, Milestone)> {
    parse_case_since(&read(CASE_SINCE)).unwrap_or_else(|error| panic!("{CASE_SINCE}: {error}"))
}

/// The case IDs a phrase of TESTING 23 names: `G05`, `S10`, and ranges such as
/// `G07-G11` or `S1-S8`.
pub fn case_ids(phrase: &str) -> Vec<String> {
    let mut ids = Vec::new();
    let single = |word: &str| -> Option<(char, u32, usize)> {
        let mut chars = word.chars();
        let letter = chars.next().filter(|c| *c == 'G' || *c == 'S')?;
        let digits = chars.as_str();
        let number = digits
            .parse()
            .ok()
            .filter(|_| digits.bytes().all(|b| b.is_ascii_digit()))?;
        Some((letter, number, digits.len()))
    };
    for word in phrase.split(|c: char| c.is_whitespace() || c == ',' || c == '`') {
        let word = word.trim_matches(|c: char| !c.is_ascii_alphanumeric() && c != '-');
        if let Some((letter, number, width)) = single(word) {
            ids.push(format!("{letter}{number:0width$}"));
        } else if let Some((first, last)) = word.split_once('-')
            && let (Some((a, from, width)), Some((b, to, _))) = (single(first), single(last))
            && a == b
        {
            ids.extend((from..=to).map(|n| format!("{a}{n:0width$}")));
        }
    }
    ids
}

/// Each case TESTING 23 makes byte-exact, with the milestone of its row. A row's
/// gate is a list split by `;`, and only the items saying `exact` count: the M0 row
/// names G01 for the renderer's hand-built shape, which is no run of the case.
fn exact_in_testing_23() -> Vec<(String, Milestone)> {
    let testing = read("docs/TESTING.md");
    let mut found = Vec::new();
    for row in table_after(&testing, "| M | Gate |") {
        let milestone = milestone_in(&row[0]).expect("a milestone");
        for item in row[1].split(';').filter(|item| item.contains("exact")) {
            found.extend(case_ids(item).into_iter().map(|id| (id, milestone)));
        }
    }
    found
}

/// The cases a phrase names, in its order: a word that is a case's ID, as `the tour`,
/// or a backticked name that is the bold lead-in of a paragraph of SPEC, as `the
/// `Ownership in three lines` block`, which names the first case after that paragraph.
pub fn cases_named(phrase: &str, spec: &str, cases: &[Case]) -> Vec<String> {
    let mut ids = Vec::new();
    for (index, piece) in phrase.split('`').enumerate() {
        if index % 2 == 1 {
            let lead = format!("**{piece}.**");
            let line = spec
                .lines()
                .position(|line| line.starts_with(&lead))
                .map(|at| at + 1);
            if let Some(line) = line
                && let Some(case) = cases.iter().find(|case| case.line > line)
            {
                ids.push(case.id.clone());
            }
        } else {
            for word in piece.split(|c: char| c.is_whitespace() || c == ',') {
                if let Some(case) = cases.iter().find(|case| case.id == word) {
                    ids.push(case.id.clone());
                }
            }
        }
    }
    ids
}

/// Each case TESTING 23 says must parse, with the milestone of its row: the items of
/// a row's gate that end in ` parse`.
fn parsing_in_testing_23() -> Vec<(String, Milestone)> {
    let testing = read("docs/TESTING.md");
    let spec = read("docs/SPEC.md");
    let mut found = Vec::new();
    for row in table_after(&testing, "| M | Gate |") {
        let milestone = milestone_in(&row[0]).expect("a milestone");
        for item in row[1]
            .split(';')
            .map(str::trim)
            .filter(|item| item.ends_with(" parse"))
        {
            let ids = cases_named(item, &spec, spec_cases());
            assert!(!ids.is_empty(), "{item:?} names no case");
            found.extend(ids.into_iter().map(|id| (id, milestone)));
        }
    }
    found
}

/// A case's files, each through `enrang check` in a fresh directory holding them all:
/// passing when every one exits 0 with nothing on stdout or stderr.
fn parse_status(case: &Case) -> FixtureStatus {
    let files: Vec<(String, Vec<u8>)> = case
        .files
        .iter()
        .map(|file| (file.name.clone(), file.contents.clone().into_bytes()))
        .collect();
    let clean = case.files.iter().all(|file| {
        let args = vec!["check".to_owned(), file.name.clone()];
        let ran = run_cached(&Place::Files(files.clone()), &args);
        (ran.code, ran.stdout.as_str(), ran.stderr.as_str()) == (0, "", "")
    });
    if clean {
        FixtureStatus::Passing
    } else {
        FixtureStatus::Failing
    }
}

/// The parse rows gated at `milestone`, one `<ID> parses` line each: each reached row
/// must pass; a later one is not run, so it claims nothing.
fn parse_report(milestone: Milestone) -> GateReport {
    let rows = parsing_in_testing_23();
    let lines: Vec<(String, Milestone, FixtureStatus)> = rows
        .iter()
        .map(|(id, since)| {
            let case = spec_cases()
                .iter()
                .find(|case| &case.id == id)
                .expect("a case");
            let status = if *since <= milestone {
                parse_status(case)
            } else {
                FixtureStatus::Missing
            };
            (format!("{id} parses"), *since, status)
        })
        .collect();
    let rows: Vec<GateRow<'_, Milestone>> = lines
        .iter()
        .map(|(id, since, fixture)| GateRow {
            id,
            since: *since,
            fixture: *fixture,
        })
        .collect();
    gate(&rows, &milestone)
}

/// A case run as SPEC says, in a fresh directory holding its files.
fn case_status(case: &Case) -> FixtureStatus {
    let files = case
        .files
        .iter()
        .map(|file| (file.name.clone(), file.contents.clone().into_bytes()))
        .collect();
    let args: Vec<String> = case
        .cmd
        .split_whitespace()
        .skip(1)
        .map(str::to_owned)
        .collect();
    let ran = run_cached(&Place::Files(files), &args);
    let exact = ran.code == case.exit
        && ran.stdout == case.stdout.text
        && ran.stderr == case.stderr.text
        && case.serial.source == StreamSource::Unnamed;
    if exact {
        FixtureStatus::Passing
    } else {
        FixtureStatus::Failing
    }
}

/// The cases gated at `milestone`: each reached case must be byte-exact; a later one
/// is not run, so it claims nothing.
fn case_report(milestone: Milestone) -> GateReport {
    let cases = spec_cases();
    let table = case_since();
    let rows: Vec<GateRow<'_, Milestone>> = table
        .iter()
        .map(|(id, since)| {
            let case = cases
                .iter()
                .find(|case| &case.id == id)
                .unwrap_or_else(|| panic!("{CASE_SINCE} names {id}, which SPEC has no case of"));
            let fixture = if *since <= milestone {
                case_status(case)
            } else {
                FixtureStatus::Missing
            };
            GateRow {
                id,
                since: *since,
                fixture,
            }
        })
        .collect();
    gate(&rows, &milestone)
}

pub fn register(h: &mut Harness) {
    h.case(
        "cases/the table names every case of SPEC once, in SPEC order",
        || {
            let named: Vec<String> = case_since().into_iter().map(|(id, _)| id).collect();
            let extracted: Vec<String> = spec_cases().iter().map(|case| case.id.clone()).collect();
            assert_eq!(named, extracted);
        },
    );
    h.case(
        "cases/each milestone is the one TESTING 23 makes the case exact at",
        || {
            let table = case_since();
            let exact = exact_in_testing_23();
            assert!(exact.len() >= 34, "{exact:?}");
            for (id, milestone) in exact {
                let since = table
                    .iter()
                    .find(|(named, _)| *named == id)
                    .unwrap_or_else(|| panic!("TESTING 23 names {id}, which the table does not"));
                assert_eq!(since.1, milestone, "{id}");
            }
        },
    );
    h.case(
        "cases/the cases TESTING 23 makes exact nowhere have the plan's milestones",
        || {
            // No document gives these three a milestone by ID, and a case of a later
            // milestone is never run, so nothing else would notice a wrong one. The M1
            // plan (d.3) reads them from TESTING 23 and ARCHITECTURE 12: the tour runs
            // with S1-S8 at M4, the ownership block passes `check` once borrows are
            // checked at M3, and the kernel tour boots with S9 at M9.
            let exact: Vec<String> = exact_in_testing_23()
                .into_iter()
                .map(|(id, _)| id)
                .collect();
            let rest: Vec<(String, Milestone)> = case_since()
                .into_iter()
                .filter(|(id, _)| !exact.contains(id))
                .collect();
            let wanted = [
                ("tour".to_owned(), Milestone::M4),
                ("ownership".to_owned(), Milestone::M3),
                ("tour-kernel".to_owned(), Milestone::M9),
            ];
            assert_eq!(rest, wanted);
        },
    );
    h.case("cases/a case comes no earlier than its codes", || {
        let table = case_since();
        for case in spec_cases() {
            let since = table
                .iter()
                .find(|(id, _)| *id == case.id)
                .expect("a row")
                .1;
            for name in fired_codes(&case.stderr.text) {
                let code = Code::from_name(&name).unwrap_or_else(|| panic!("{name}"));
                assert!(
                    code.since() <= since,
                    "{}: {name} is {}",
                    case.id,
                    code.since()
                );
            }
        }
    });
    h.case("cases/a case comes no earlier than its command", || {
        let table = case_since();
        for case in spec_cases() {
            let since = table
                .iter()
                .find(|(id, _)| *id == case.id)
                .expect("a row")
                .1;
            let name = case.cmd.split_whitespace().nth(1).expect("a command");
            let due = WORKING
                .iter()
                .find(|command| command.name == name)
                .map(|command| command.since)
                .or_else(|| LATER.iter().find(|c| c.name == name).map(|c| c.since))
                .unwrap_or_else(|| panic!("{}: `{name}` is no command", case.id));
            assert!(due <= since, "{}: `{name}` arrives at {due}", case.id);
        }
    });
    h.case(
        "cases/every reached case is byte-exact as a process",
        || {
            let report = case_report(CURRENT_MILESTONE);
            assert!(report.is_clean(), "\n{report}");
        },
    );
    h.case(
        "cases/every case due at M1 is byte-exact as a process",
        || {
            let report = case_report(Milestone::M1);
            assert!(report.is_clean(), "\n{report}");
            assert_eq!(report.enforced, 4, "G01-G04");
        },
    );
    h.case(
        "cases/every case due at M2 is byte-exact as a process",
        || {
            // TESTING 23's M2 row: G05, G06, G12, G13, G17, G19, G20 and G22, beside M1's
            // four, each `enrang check` in a fresh directory, exit status, stdout and
            // stderr byte for byte.
            let report = case_report(Milestone::M2);
            assert!(report.is_clean(), "\n{report}");
            assert_eq!(report.enforced, 12, "G01-G06, G12, G13, G17, G19, G20, G22");
            let due: Vec<String> = case_since()
                .into_iter()
                .filter(|(_, since)| *since == Milestone::M2)
                .map(|(id, _)| id)
                .collect();
            assert_eq!(
                due,
                ["G05", "G06", "G12", "G13", "G17", "G19", "G20", "G22"]
            );
            assert!(
                Milestone::M2 <= CURRENT_MILESTONE,
                "M2's cases are enforced"
            );
        },
    );
    h.case(
        "cases/every case due at M3 is byte-exact as a process",
        || {
            // TESTING 23's M3 row: G07-G11, G16, G18, G21, G23 and G24, beside the
            // twelve before them, each `enrang check` in a fresh directory, exit
            // status, stdout and stderr byte for byte; and SPEC 1's ownership block,
            // which now checks clean, borrows and all (M3 plan f.2).
            let report = case_report(Milestone::M3);
            assert!(report.is_clean(), "\n{report}");
            let due: Vec<String> = case_since()
                .into_iter()
                .filter(|(_, since)| *since == Milestone::M3)
                .map(|(id, _)| id)
                .collect();
            assert_eq!(
                due,
                [
                    "ownership",
                    "G07",
                    "G08",
                    "G09",
                    "G10",
                    "G11",
                    "G16",
                    "G18",
                    "G21",
                    "G23",
                    "G24"
                ]
            );
            assert_eq!(report.enforced, 12 + due.len());
            assert_eq!(
                exact_in_testing_23()
                    .into_iter()
                    .filter(|(_, since)| *since == Milestone::M3)
                    .map(|(id, _)| id)
                    .collect::<Vec<_>>(),
                [
                    "G07", "G08", "G09", "G10", "G11", "G16", "G18", "G21", "G23", "G24"
                ]
            );
            assert!(
                Milestone::M3 <= CURRENT_MILESTONE,
                "M3's cases are enforced"
            );
        },
    );
    h.case("cases/a drifted M3 case is a gap", || {
        // Phase 3 output, a loop's source pushed to (G08) and a warning beside an
        // error (G23), each drifted by a word from SPEC; and the ownership block,
        // which checks clean only while its borrows do.
        for (id, from, to) in [
            (
                "G08",
                "conflicting mutable access",
                "conflicting mutable use",
            ),
            ("G23", "1 warning emitted", "1 warnings emitted"),
        ] {
            let mut case = spec_cases()
                .iter()
                .find(|case| case.id == id)
                .expect("the case")
                .clone();
            assert_eq!(case_status(&case), FixtureStatus::Passing, "{id}");
            assert!(
                case.stderr.text.contains(from),
                "{id}: {}",
                case.stderr.text
            );
            case.stderr.text = case.stderr.text.replacen(from, to, 1);
            assert_eq!(case_status(&case), FixtureStatus::Failing, "{id}");
        }
        // Byte-exact means whitespace too: a trailing newline or space more in
        // SPEC's stderr, or in its stdout, is a drift.
        let g08 = spec_cases()
            .iter()
            .find(|case| case.id == "G08")
            .expect("the case")
            .clone();
        for drift in ["\n", " "] {
            let mut case = g08.clone();
            case.stderr.text.push_str(drift);
            assert_eq!(
                case_status(&case),
                FixtureStatus::Failing,
                "G08 stderr + {drift:?}"
            );
            let mut case = g08.clone();
            case.stdout.text.push_str(drift);
            assert_eq!(
                case_status(&case),
                FixtureStatus::Failing,
                "G08 stdout + {drift:?}"
            );
        }
        let mut case = spec_cases()
            .iter()
            .find(|case| case.id == "ownership")
            .expect("the ownership block")
            .clone();
        assert_eq!(case_status(&case), FixtureStatus::Passing);
        // `a` was moved into `keep`: using it again is EN0601, as its comment says.
        case.files[0].contents.push_str("console.log(a);\n");
        assert_eq!(case_status(&case), FixtureStatus::Failing);
    });
    h.case("cases/a drifted M2 case is a gap", || {
        // Phase 2 output, a type mismatch (G05) and a non-exhaustive match (G12), each
        // drifted by a word from SPEC.
        for (id, from, to) in [
            ("G05", "found `i64`", "found `i32`"),
            ("G12", "doesn't handle", "does not handle"),
        ] {
            let mut case = spec_cases()
                .iter()
                .find(|case| case.id == id)
                .expect("the case")
                .clone();
            assert_eq!(case_status(&case), FixtureStatus::Passing, "{id}");
            assert!(
                case.stderr.text.contains(from),
                "{id}: {}",
                case.stderr.text
            );
            case.stderr.text = case.stderr.text.replacen(from, to, 1);
            assert_eq!(case_status(&case), FixtureStatus::Failing, "{id}");
        }
    });
    h.case(
        "cases/TESTING 23 says the tour and the ownership block parse at M1",
        || {
            let rows = parsing_in_testing_23();
            let wanted = [
                ("tour".to_owned(), Milestone::M1),
                ("ownership".to_owned(), Milestone::M1),
            ];
            assert_eq!(rows, wanted);
        },
    );
    h.case(
        "cases/every case due to parse passes check as a process",
        || {
            let report = parse_report(CURRENT_MILESTONE);
            assert!(report.is_clean(), "\n{report}");
            let due = parsing_in_testing_23()
                .iter()
                .filter(|(_, since)| *since <= CURRENT_MILESTONE)
                .count();
            assert_eq!(report.enforced, due);
            assert!(due >= 2, "the tour and the ownership block");
        },
    );
    h.case("cases/a case due to parse that does not is a gap", || {
        let mut case = spec_cases()
            .iter()
            .find(|case| case.id == "tour")
            .expect("the tour")
            .clone();
        assert_eq!(parse_status(&case), FixtureStatus::Passing);
        case.files[0].contents = case.files[0].contents.replacen(';', "", 1);
        assert_eq!(parse_status(&case), FixtureStatus::Failing);
        let mut case = spec_cases()
            .iter()
            .find(|case| case.id == "ownership")
            .expect("the ownership block")
            .clone();
        case.files[0].contents.push_str("const late = 1\n");
        assert_eq!(parse_status(&case), FixtureStatus::Failing);
    });
    h.case("cases/a drifted case is a gap", || {
        let mut case = spec_cases()
            .iter()
            .find(|case| case.id == "G03")
            .expect("G03")
            .clone();
        assert_eq!(case_status(&case), FixtureStatus::Passing);
        case.stderr.text = case.stderr.text.replace("use `==` here", "use == here");
        assert_eq!(case_status(&case), FixtureStatus::Failing);
    });
    let lines: &[(&str, Result<&[(&str, Milestone)], usize>)] = &[
        ("", Ok(&[])),
        ("G01 M1\n", Ok(&[("G01", Milestone::M1)])),
        (
            "tour M4\ntour-kernel M10\n",
            Ok(&[("tour", Milestone::M4), ("tour-kernel", Milestone::M10)]),
        ),
        ("G01 M1\nG02\n", Err(2)),
        ("G01  M1\n", Err(1)),
        ("G01 m1\n", Err(1)),
        ("G01 M11\n", Err(1)),
        ("G01 M1 x\n", Err(1)),
        (" M1\n", Err(1)),
    ];
    for (text, expected) in lines {
        let (text, expected) = (*text, expected.clone());
        h.case(format!("cases/reads the table {text:?}"), move || {
            let parsed = parse_case_since(text);
            match expected {
                Ok(rows) => {
                    let rows: Vec<(String, Milestone)> =
                        rows.iter().map(|(id, m)| ((*id).to_owned(), *m)).collect();
                    assert_eq!(parsed, Ok(rows));
                }
                Err(line) => {
                    let error = parsed.expect_err("malformed");
                    assert!(error.starts_with(&format!("line {line}:")), "{error}");
                }
            }
        });
    }
    let phrases: &[(&str, &[&str])] = &[
        ("G01-G04 byte-exact", &["G01", "G02", "G03", "G04"]),
        (
            "S1-S8, S10, S11 byte-exact",
            &["S1", "S2", "S3", "S4", "S5", "S6", "S7", "S8", "S10", "S11"],
        ),
        ("G05, G06 byte-exact", &["G05", "G06"]),
        ("S9 exact on bench", &["S9"]),
        ("`f1`-`f6`, `h1`-`h8`; GenExpr; G1x", &[]),
        ("G07-S09", &[]),
    ];
    for (phrase, expected) in phrases {
        let (phrase, expected) = (*phrase, *expected);
        h.case(format!("cases/the IDs of {phrase:?}"), move || {
            assert_eq!(case_ids(phrase), expected);
        });
    }
    let named: &[(&str, &[&str])] = &[
        ("the tour", &["tour"]),
        ("the `Ownership in three lines` block", &["ownership"]),
        (
            "the tour and the `Ownership in three lines` block",
            &["tour", "ownership"],
        ),
        ("G01, tour-kernel", &["G01", "tour-kernel"]),
        ("the `No such paragraph` block", &[]),
        ("a tourist", &[]),
    ];
    for (phrase, expected) in named {
        let (phrase, expected) = (*phrase, *expected);
        h.case(format!("cases/the cases {phrase:?} names"), move || {
            let spec = read("docs/SPEC.md");
            assert_eq!(cases_named(phrase, &spec, spec_cases()), expected);
        });
    }
}
