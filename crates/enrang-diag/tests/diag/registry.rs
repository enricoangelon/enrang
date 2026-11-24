//! The registry against SPEC 13.2: one row per line, in both directions.

use std::collections::BTreeSet;
use std::sync::OnceLock;

use enrang_diag::{
    CURRENT_MILESTONE, Code, CodeRow, FixtureKind, Milestone, Owner, Phase, ROWS, Severity,
};
use enrang_testkit::{Harness, workspace_root};

use crate::support::doc;

/// One line of the catalog, as written.
#[derive(Clone, Eq, PartialEq, Debug)]
struct CatalogRow {
    code: String,
    severity: String,
    phase: String,
    owner: String,
    since: String,
    fixture: String,
    title: String,
}

/// The lines of the `text` block under the heading `### 13.2 Catalog`.
fn catalog_lines(document: &str) -> Result<Vec<&str>, String> {
    let mut lines = document.lines();
    lines
        .find(|line| *line == "### 13.2 Catalog")
        .ok_or("no `### 13.2 Catalog` heading")?;
    lines
        .find(|line| *line == "```text")
        .ok_or("no `text` block under the heading")?;
    let mut rows = Vec::new();
    for line in lines {
        if line == "```" {
            return Ok(rows);
        }
        if !line.trim().is_empty() {
            rows.push(line);
        }
    }
    Err("the catalog block never closes".to_owned())
}

fn parse_row(line: &str) -> Result<CatalogRow, String> {
    let mut parts = line.splitn(7, ' ');
    let mut next = |what: &str| {
        parts
            .next()
            .filter(|part| !part.is_empty())
            .map(str::to_owned)
            .ok_or_else(|| format!("`{line}` has no {what}"))
    };
    Ok(CatalogRow {
        code: next("code")?,
        severity: next("severity")?,
        phase: next("phase")?,
        owner: next("owner")?,
        since: next("since")?,
        fixture: next("fixture")?,
        title: next("title")?,
    })
}

fn parse_catalog(document: &str) -> Result<Vec<CatalogRow>, String> {
    catalog_lines(document)?
        .into_iter()
        .map(parse_row)
        .collect()
}

/// The codes SPEC 13.2 retired, by hand. Codes are never reused, so none may come
/// back as a row.
const RETIRED: [&str; 18] = [
    "EN0204", "EN0212", "EN0217", "EN0223", "EN0306", "EN0407", "EN0431", "EN0505", "EN0620",
    "EN0704", "EN0716", "EN0719", "EN0720", "EN0810", "EN1008", "EN1016", "EN1020", "EN1040",
];

/// The paragraph of SPEC 13.2 that says how codes retire and which have.
fn catalog_preface(document: &str) -> &str {
    let section = document
        .split_once("### 13.2 Catalog")
        .expect("the catalog heading exists")
        .1;
    let section = section.split_once("```text").expect("the catalog block").0;
    section
        .split("\n\n")
        .find(|paragraph| paragraph.contains("Codes are never reused."))
        .expect("the paragraph on retired codes")
}

/// The documents whose prose names codes: the four of `docs/` and the README.
fn documents() -> Vec<(&'static str, String)> {
    let mut found: Vec<(&str, String)> =
        ["SPEC.md", "ARCHITECTURE.md", "DEV_RUNTIME.md", "TESTING.md"]
            .into_iter()
            .map(|name| (name, doc(name).to_owned()))
            .collect();
    let readme = workspace_root().join("README.md");
    let text = std::fs::read_to_string(&readme)
        .unwrap_or_else(|error| panic!("cannot read README.md: {error}"));
    found.push(("README.md", text));
    found
}

/// Each place `text` calls a code by a severity, as `warning EN0828`, `errors
/// EN0430`, `error (EN0706)` or `error[EN0601]`, in either case and with the code in
/// backticks or not: the severity, the code and the phrase as written.
fn severity_phrases(text: &str) -> Vec<(Severity, &str, &str)> {
    let bytes = text.as_bytes();
    let mut found = Vec::new();
    for (at, _) in text.match_indices("EN") {
        let end = at + 6;
        let is_code = end <= bytes.len()
            && bytes[at + 2..end].iter().all(u8::is_ascii_digit)
            && bytes.get(end).is_none_or(|b| !b.is_ascii_alphanumeric());
        if !is_code {
            continue;
        }
        let before = &text[..at];
        let before = before.strip_suffix('`').unwrap_or(before);
        let Some(before) = [" (", " ", "["]
            .iter()
            .find_map(|joint| before.strip_suffix(joint))
        else {
            continue;
        };
        let words = [
            ("warnings", Severity::Warning),
            ("warning", Severity::Warning),
            ("errors", Severity::Error),
            ("error", Severity::Error),
        ];
        for (word, severity) in words {
            let Some(start) = before.len().checked_sub(word.len()) else {
                continue;
            };
            let Some(tail) = before.get(start..) else {
                continue;
            };
            let whole_word = start == 0 || !bytes[start - 1].is_ascii_alphanumeric();
            if whole_word && tail.eq_ignore_ascii_case(word) {
                found.push((severity, &text[at..end], &text[start..end]));
                break;
            }
        }
    }
    found
}

/// The `ENdddd` and `Tdddd` codes `text` names, each as a whole word, in order.
fn named_codes(text: &str) -> Vec<&str> {
    let bytes = text.as_bytes();
    let mut found = Vec::new();
    for (at, _) in text.match_indices(['E', 'T']) {
        let prefix = if text[at..].starts_with("EN") {
            2
        } else if bytes[at] == b'T' {
            1
        } else {
            continue;
        };
        let end = at + prefix + 4;
        let is_code = end <= bytes.len()
            && (at == 0 || !bytes[at - 1].is_ascii_alphanumeric())
            && bytes[at + prefix..end].iter().all(u8::is_ascii_digit)
            && bytes.get(end).is_none_or(|b| !b.is_ascii_alphanumeric());
        if is_code {
            found.push(&text[at..end]);
        }
    }
    found
}

/// The cells of the last column of the table under `header`.
fn last_column<'a>(document: &'a str, header: &str) -> Vec<&'a str> {
    let table = document
        .split_once(header)
        .unwrap_or_else(|| panic!("no table `{header}`"))
        .1;
    table
        .lines()
        .skip(2)
        .take_while(|line| line.starts_with('|'))
        .map(|line| {
            line.trim_end_matches('|')
                .rsplit(" | ")
                .next()
                .unwrap_or("")
        })
        .collect()
}

/// The rules a stored body reruns on load, from `fixed list` through `EN1006`, in
/// the paragraph of `document` that lists them.
fn rerun_list(document: &str) -> Vec<&str> {
    let start = document
        .find("fixed list")
        .expect("the paragraph on stored bodies");
    let rest = &document[start..];
    let end = rest.find("EN1006").expect("the list ends with EN1006") + "EN1006".len();
    named_codes(&rest[..end])
}

fn spec_rows() -> &'static [CatalogRow] {
    static ROWS: OnceLock<Vec<CatalogRow>> = OnceLock::new();
    ROWS.get_or_init(|| parse_catalog(doc("SPEC.md")).expect("the SPEC catalog parses"))
}

fn severity_letter(severity: Severity) -> &'static str {
    match severity {
        Severity::Error => "E",
        Severity::Warning => "W",
        Severity::Fail => "F",
        Severity::Note => unreachable!("the catalog has no note severity"),
    }
}

/// A registry row in the catalog's spelling.
fn written(row: &CodeRow) -> CatalogRow {
    CatalogRow {
        code: row.name.to_owned(),
        severity: severity_letter(row.severity).to_owned(),
        phase: row.phase.to_string(),
        owner: row.owner.to_string(),
        since: row.since.to_string(),
        fixture: row.fixture.to_string(),
        title: row.title.to_owned(),
    }
}

/// Everything on which the two tables differ, in both directions.
fn differences(document: &[CatalogRow], registry: &[CatalogRow]) -> Vec<String> {
    let mut found = Vec::new();
    let in_document: BTreeSet<&str> = document.iter().map(|row| row.code.as_str()).collect();
    let in_registry: BTreeSet<&str> = registry.iter().map(|row| row.code.as_str()).collect();
    for code in in_document.difference(&in_registry) {
        found.push(format!("{code} is in the document but not the registry"));
    }
    for code in in_registry.difference(&in_document) {
        found.push(format!("{code} is in the registry but not the document"));
    }
    for row in document {
        if let Some(other) = registry.iter().find(|other| other.code == row.code)
            && other != row
        {
            found.push(format!("{} differs: {row:?} against {other:?}", row.code));
        }
    }
    let shared = |rows: &[CatalogRow]| -> Vec<String> {
        rows.iter()
            .filter(|row| in_document.contains(row.code.as_str()))
            .filter(|row| in_registry.contains(row.code.as_str()))
            .map(|row| row.code.clone())
            .collect()
    };
    if shared(document) != shared(registry) {
        found.push("the rows are in a different order".to_owned());
    }
    let unique = |rows: &[CatalogRow]| {
        rows.iter()
            .map(|row| &row.code)
            .collect::<BTreeSet<_>>()
            .len()
            == rows.len()
    };
    if !unique(document) || !unique(registry) {
        found.push("a code has two rows".to_owned());
    }
    found
}

fn registry_rows() -> Vec<CatalogRow> {
    ROWS.iter().map(written).collect()
}

/// The drift detector has to be able to fail, so each kind of drift is applied to
/// the real tables and has to be found.
fn register_drift(h: &mut Harness) {
    type Tamper = fn(&mut Vec<CatalogRow>);
    let tampers: [(&str, Tamper, &str); 11] = [
        (
            "a row removed",
            |rows| drop(rows.remove(10)),
            "not the document",
        ),
        (
            "a row added",
            |rows| {
                let mut extra = rows[0].clone();
                extra.code = "EN0704".to_owned();
                rows.insert(5, extra);
            },
            "EN0704 is in the document but not the registry",
        ),
        (
            "severity",
            |rows| rows[3].severity = "W".to_owned(),
            "differs",
        ),
        ("phase", |rows| rows[3].phase = "R".to_owned(), "differs"),
        ("owner", |rows| rows[3].owner = "cli".to_owned(), "differs"),
        ("since", |rows| rows[3].since = "M9".to_owned(), "differs"),
        (
            "fixture",
            |rows| rows[3].fixture = "Cli".to_owned(),
            "differs",
        ),
        ("title", |rows| rows[3].title.push('.'), "differs"),
        ("order", |rows| rows.swap(1, 2), "a different order"),
        (
            "a duplicate",
            |rows| {
                let copy = rows[7].clone();
                rows.push(copy);
            },
            "two rows",
        ),
        (
            "a retired code in the registry's place",
            |rows| rows[0].code = "EN0704".to_owned(),
            "EN0704",
        ),
    ];
    for (name, tamper, expected) in tampers {
        h.case(format!("registry/drift is caught/{name}"), move || {
            let mut tampered = spec_rows().to_vec();
            tamper(&mut tampered);
            let found = differences(&tampered, &registry_rows());
            assert!(
                found.iter().any(|line| line.contains(expected)),
                "wanted `{expected}` in {found:?}"
            );
        });
    }
}

fn register_parser(h: &mut Harness) {
    let bad: [(&str, &str, &str); 4] = [
        ("no heading", "# nothing\n", "no `### 13.2 Catalog` heading"),
        ("no block", "### 13.2 Catalog\ntext\n", "no `text` block"),
        (
            "unclosed block",
            "### 13.2 Catalog\n```text\nEN0001 E 1 syntax M1 Compile t\n",
            "never closes",
        ),
        (
            "short row",
            "### 13.2 Catalog\n```text\nEN0001 E 1 syntax\n```\n",
            "has no since",
        ),
    ];
    for (name, document, expected) in bad {
        h.case(format!("registry/catalog parser/{name}"), move || {
            let error = parse_catalog(document).expect_err("it must not parse");
            assert!(error.contains(expected), "{error}");
        });
    }
    h.case("registry/catalog parser/a title keeps its spaces", || {
        let row = parse_row("EN0001 E 1 syntax M1 Compile source is  not valid").unwrap();
        assert_eq!(row.title, "source is  not valid");
        assert_eq!(row.fixture, "Compile");
    });
}

/// The rows of `define_codes!` that ARCHITECTURE 2.2 shows as examples.
fn architecture_rows() -> Vec<CatalogRow> {
    let mut rows = Vec::new();
    for line in doc("ARCHITECTURE.md").lines() {
        let line = line.trim();
        let Some((head, title)) = line.split_once(" \"") else {
            continue;
        };
        let fields: Vec<&str> = head.split(' ').collect();
        let [code, severity, phase, owner, since, fixture] = fields[..] else {
            continue;
        };
        let inner = |text: &str, key: &str| {
            text.strip_prefix(key)
                .and_then(|rest| rest.strip_prefix('('))
                .and_then(|rest| rest.strip_suffix(')'))
                .map(str::to_owned)
        };
        let (Some(phase), Some(owner), Some(since), Some(fixture)) = (
            inner(phase, "phase"),
            inner(owner, "owner"),
            inner(since, "since"),
            inner(fixture, "fixture"),
        ) else {
            continue;
        };
        rows.push(CatalogRow {
            code: code.to_owned(),
            severity: severity[..1].to_owned(),
            phase,
            owner,
            since,
            fixture,
            title: title.strip_suffix("\",").unwrap_or(title).to_owned(),
        });
    }
    rows
}

pub fn register(h: &mut Harness) {
    h.case("registry/agrees with SPEC 13.2 in both directions", || {
        let found = differences(spec_rows(), &registry_rows());
        assert!(found.is_empty(), "{}", found.join("\n"));
    });
    h.case("registry/has 282 rows, like the document", || {
        assert_eq!(spec_rows().len(), 282, "the document");
        assert_eq!(ROWS.len(), 282, "ROWS");
        assert_eq!(Code::ALL.len(), 282, "Code::ALL");
    });
    for code in RETIRED {
        h.case(
            format!("registry/{code} is retired and absent"),
            move || {
                assert_eq!(Code::from_name(code), None);
                assert!(ROWS.iter().all(|row| row.name != code));
                assert!(spec_rows().iter().all(|row| row.code != code));
            },
        );
    }
    h.case(
        "registry/the catalog's preface names every retired code",
        || {
            let preface = catalog_preface(doc("SPEC.md"));
            for code in RETIRED {
                let named = format!("{code} ");
                assert!(preface.contains(&named), "{code} is not named: {preface}");
            }
            assert!(preface.contains("Codes are never reused."), "{preface}");
        },
    );
    // Only a rewrite of `define_codes!` can break this: it checks the macro.
    h.case("registry/ALL and ROWS line up", || {
        for (index, code) in Code::ALL.iter().enumerate() {
            assert_eq!(code.row(), &ROWS[index], "{code}");
            assert_eq!(*code as usize, index, "{code}");
        }
    });
    h.case("registry/codes are in ascending order", || {
        let names: Vec<&str> = Code::ALL.iter().map(|code| code.name()).collect();
        let mut sorted = names.clone();
        sorted.sort();
        // `EN` sorts before `T` and fixed widths compare numerically.
        assert_eq!(names, sorted);
        assert!(Code::EN0001 < Code::EN0002);
        assert!(Code::EN1307 < Code::T0001);
    });
    h.case("registry/no row is a note", || {
        assert!(ROWS.iter().all(|row| row.severity != Severity::Note));
    });
    h.case("registry/from_name is exact", || {
        for name in [
            "", "EN", "en0601", "EN601", "EN06010", " EN0601", "EN0601 ", "T1", "t0001",
        ] {
            assert_eq!(Code::from_name(name), None, "{name:?}");
        }
    });
    h.case("registry/warnings are exactly the W rows", || {
        let warnings: Vec<&str> = ROWS
            .iter()
            .filter(|row| row.severity == Severity::Warning)
            .map(|row| row.name)
            .collect();
        assert_eq!(
            warnings,
            [
                "EN0314", "EN0430", "EN0453", "EN0459", "EN0503", "EN0828", "EN0914", "EN1212"
            ]
        );
    });
    h.case(
        "registry/the severity reader finds the phrases it must",
        || {
            let text = "Error EN0102, warnings `EN0503` and EN0430, a compile error (EN0706), \
                    warning[EN0453], terror EN0101, error EN01011, error naming EN0608";
            let found: Vec<(Severity, &str)> = severity_phrases(text)
                .into_iter()
                .map(|(severity, code, _)| (severity, code))
                .collect();
            assert_eq!(
                found,
                [
                    (Severity::Error, "EN0102"),
                    (Severity::Warning, "EN0503"),
                    (Severity::Error, "EN0706"),
                    (Severity::Warning, "EN0453"),
                ]
            );
        },
    );
    h.case(
        "registry/prose calls each code by its catalog severity",
        || {
            let mut checked = 0;
            for (name, text) in documents() {
                for (severity, written, phrase) in severity_phrases(&text) {
                    let code = Code::from_name(written)
                        .unwrap_or_else(|| panic!("{name}: `{phrase}` names no catalog row"));
                    assert_eq!(code.severity(), severity, "{name}: `{phrase}`");
                    checked += 1;
                }
            }
            assert!(checked > 0, "no phrase was found to check");
        },
    );
    h.case("registry/test verdicts are exactly the T rows", || {
        for row in ROWS {
            assert_eq!(
                row.severity == Severity::Fail,
                row.name.starts_with('T'),
                "{}",
                row.name
            );
        }
    });
    h.case("registry/the current milestone is M3", || {
        assert_eq!(CURRENT_MILESTONE, Milestone::M3);
    });
    h.case(
        "registry/M3 reaches M0's commands, M1's syntax and command-line rows, M2's type rows and M3's borrow rows",
        || {
            let reached: Vec<Code> = Code::ALL.iter().copied().filter(|c| c.reached()).collect();
            let of = |milestone: Milestone| -> Vec<Code> {
                reached
                    .iter()
                    .copied()
                    .filter(|code| code.since() == milestone)
                    .collect()
            };
            assert_eq!(of(Milestone::M0), [Code::EN1301, Code::EN1302]);
            let m1 = of(Milestone::M1);
            let m2 = of(Milestone::M2);
            let m3 = of(Milestone::M3);
            assert_eq!(reached.len(), 2 + m1.len() + m2.len() + m3.len());
            // ARCHITECTURE 12's M1 row: the syntax-owned rows, and what `check`'s flags
            // report before any source is read.
            let command_line: Vec<Code> = m1
                .iter()
                .copied()
                .filter(|code| code.phase() == Phase::CommandLine)
                .collect();
            assert_eq!(
                command_line,
                [
                    Code::EN0909,
                    Code::EN0911,
                    Code::EN0912,
                    Code::EN1031,
                    Code::EN1034,
                    Code::EN1041,
                    Code::EN1303,
                    Code::EN1304,
                    Code::EN1305,
                    Code::EN1307,
                ]
            );
            for code in m1.iter().filter(|code| code.phase() != Phase::CommandLine) {
                assert_eq!(code.phase(), Phase::Syntax, "{code}");
                assert_eq!(code.owner(), Owner::Syntax, "{code}");
                assert_eq!(code.fixture(), FixtureKind::Compile, "{code}");
            }
            assert_eq!(m1.len(), 75, "{m1:?}");
            // Every syntax row of M1 is reached; those of M4 wait for `enrang test`.
            for code in Code::ALL
                .iter()
                .filter(|code| code.owner() == Owner::Syntax)
            {
                assert_eq!(code.reached(), code.since() == Milestone::M1, "{code}");
            }
            // ARCHITECTURE 12's M2 row: resolve and types, every one a compile fixture's,
            // and EN0435, the layout limit, which phase 4 reports once phase 2 passed.
            for &code in &m2 {
                assert_eq!(code.fixture(), FixtureKind::Compile, "{code}");
                if code == Code::EN0435 {
                    assert_eq!(code.phase(), Phase::Layout, "{code}");
                    assert_eq!(code.owner(), Owner::Layout, "{code}");
                } else {
                    assert_eq!(code.phase(), Phase::Types, "{code}");
                    assert_eq!(code.owner(), Owner::Sema, "{code}");
                }
            }
            assert!(m2.contains(&Code::EN0435));
            assert_eq!(m2.len(), 117, "{m2:?}");
            let warnings = m2
                .iter()
                .filter(|code| code.severity() == Severity::Warning)
                .count();
            assert_eq!(warnings, 6);
            // The sema rows of M2 are reached; those of M4, M6 and M9 wait for the
            // features that report them.
            for code in Code::ALL.iter().filter(|code| code.owner() == Owner::Sema) {
                assert_eq!(code.reached(), code.since() == Milestone::M2, "{code}");
            }
            // ARCHITECTURE 12's M3 row: moves, read-only marks, loans, contracts and R3,
            // every one a compile fixture's and an error; phase 3 reports them all but
            // EN0804, a packed field's reference, which phase 4 reports once phase 3
            // passed (SPEC 13.1). Every borrow checker row is M3's, so all are reached.
            for &code in &m3 {
                assert_eq!(code.fixture(), FixtureKind::Compile, "{code}");
                assert_eq!(code.severity(), Severity::Error, "{code}");
                assert_eq!(code.owner(), Owner::Borrowck, "{code}");
                let phase = if code == Code::EN0804 {
                    Phase::Layout
                } else {
                    Phase::Borrows
                };
                assert_eq!(code.phase(), phase, "{code}");
            }
            assert!(m3.contains(&Code::EN0804));
            assert_eq!(m3.len(), 29, "{m3:?}");
            for code in Code::ALL
                .iter()
                .filter(|code| code.owner() == Owner::Borrowck)
            {
                assert_eq!(code.reached(), code.since() == Milestone::M3, "{code}");
            }
            // Every phase 3 row is the borrow checker's and M3's, but EN0316, the
            // check of an interface file's stored code on load, which M4 brings.
            for code in Code::ALL
                .iter()
                .filter(|code| code.phase() == Phase::Borrows && **code != Code::EN0316)
            {
                assert_eq!(code.owner(), Owner::Borrowck, "{code}");
                assert!(code.reached(), "{code}");
            }
            assert_eq!(Code::EN0316.since(), Milestone::M4);
            assert!(!Code::EN0316.reached());
        },
    );
    h.case(
        "registry/every milestone with rows is one the catalog can name",
        || {
            let used: BTreeSet<Milestone> = ROWS.iter().map(|row| row.since).collect();
            let expected = [
                Milestone::M0,
                Milestone::M1,
                Milestone::M2,
                Milestone::M3,
                Milestone::M4,
                Milestone::M5,
                Milestone::M6,
                Milestone::M9,
            ];
            assert_eq!(used.into_iter().collect::<Vec<_>>(), expected);
        },
    );
    h.case("registry/spellings/phases", || {
        let table = [
            (Phase::CommandLine, "0"),
            (Phase::Syntax, "1"),
            (Phase::Types, "2"),
            (Phase::Borrows, "3"),
            (Phase::Layout, "4"),
            (Phase::Reachability, "5"),
            (Phase::Runtime, "R"),
        ];
        for (phase, written) in table {
            assert_eq!(phase.to_string(), written);
        }
    });
    h.case("registry/spellings/owners", || {
        let table = [
            (Owner::Borrowck, "borrowck"),
            (Owner::Cli, "cli"),
            (Owner::Codegen, "codegen"),
            (Owner::Dev, "dev"),
            (Owner::Driver, "driver"),
            (Owner::Layout, "layout"),
            (Owner::Link, "link"),
            (Owner::Mono, "mono"),
            (Owner::Sema, "sema"),
            (Owner::Syntax, "syntax"),
            (Owner::Target, "target"),
            (Owner::Testrun, "testrun"),
            (Owner::Vm, "vm"),
        ];
        for (owner, written) in table {
            assert_eq!(owner.to_string(), written);
        }
    });
    h.case("registry/spellings/fixture kinds", || {
        let table = [
            (FixtureKind::Compile, "Compile"),
            (FixtureKind::Cli, "Cli"),
            (FixtureKind::Reload, "Reload"),
            (FixtureKind::TestRun, "TestRun"),
        ];
        for (kind, written) in table {
            assert_eq!(kind.to_string(), written);
        }
    });
    h.case("registry/ARCHITECTURE's sample rows agree", || {
        let rows = architecture_rows();
        let codes: Vec<&str> = rows.iter().map(|row| row.code.as_str()).collect();
        assert_eq!(codes, ["EN0601", "EN0430", "EN0414", "EN1215", "T0001"]);
        let registry = registry_rows();
        for row in &rows {
            let known = registry
                .iter()
                .find(|known| known.code == row.code)
                .unwrap();
            assert_eq!(row, known);
        }
    });
    h.case("registry/section 16 lists exactly the EN10xx rows", || {
        let mut listed = BTreeSet::new();
        let section = doc("SPEC.md")
            .split_once("## 16. Deferred features")
            .expect("section 16 exists")
            .1;
        for line in section.lines() {
            if let Some(code) = line.strip_prefix("| EN").and_then(|rest| rest.get(..4)) {
                listed.insert(format!("EN{code}"));
            }
        }
        let rows: BTreeSet<String> = ROWS
            .iter()
            .filter(|row| row.name.starts_with("EN10"))
            .map(|row| row.name.to_owned())
            .collect();
        assert_eq!(listed, rows);
    });
    h.case(
        "registry/every code the documents name is a row, a retired one only in the preface",
        || {
            let preface = catalog_preface(doc("SPEC.md")).to_owned();
            for (name, text) in documents() {
                let text = if name == "SPEC.md" {
                    text.replacen(&preface, "", 1)
                } else {
                    text
                };
                for code in named_codes(&text) {
                    assert!(
                        Code::from_name(code).is_some(),
                        "{name} names {code}, which is no catalog row{}",
                        if RETIRED.contains(&code) {
                            " (it is retired)"
                        } else {
                            ""
                        }
                    );
                }
            }
        },
    );
    h.case(
        "registry/ARCHITECTURE 6.1 reports only phase-3 borrowck rows",
        || {
            let cells = last_column(doc("ARCHITECTURE.md"), "| State at a use | Report |");
            let mut checked = 0;
            for cell in cells {
                for name in named_codes(cell) {
                    let code = Code::from_name(name).expect("a row");
                    assert_eq!(code.phase(), Phase::Borrows, "{name}");
                    assert_eq!(code.owner(), Owner::Borrowck, "{name}");
                    checked += 1;
                }
            }
            assert!(checked >= 9, "{checked}");
        },
    );
    h.case(
        "registry/a stored body reruns the same phase-2 sema rules in three documents",
        || {
            let spec = rerun_list(doc("SPEC.md"));
            assert_eq!(rerun_list(doc("ARCHITECTURE.md")), spec, "ARCHITECTURE");
            assert_eq!(rerun_list(doc("TESTING.md")), spec, "TESTING");
            for name in &spec {
                let code = Code::from_name(name).expect("a row");
                assert_eq!(code.phase(), Phase::Types, "{name}");
                assert_eq!(code.owner(), Owner::Sema, "{name}");
            }
            for name in ["EN0457", "EN0458", "EN0460"] {
                assert!(spec.contains(&name), "{name}: {spec:?}");
            }
        },
    );
    h.case(
        "registry/syntax, sema and borrowck rows are Compile rows",
        || {
            for row in ROWS {
                if matches!(row.owner, Owner::Syntax | Owner::Sema | Owner::Borrowck) {
                    assert_eq!(row.fixture, FixtureKind::Compile, "{}", row.name);
                }
            }
        },
    );
    h.case(
        "registry/the comment atop codes.rs names exactly the retired codes",
        || {
            let path = workspace_root().join("crates/enrang-diag/src/codes.rs");
            let source = std::fs::read_to_string(path).expect("codes.rs");
            let comment: String = source
                .lines()
                .take_while(|line| line.starts_with("//!"))
                .collect::<Vec<_>>()
                .join("\n");
            let mut named = named_codes(&comment);
            named.sort_unstable();
            assert_eq!(named, RETIRED, "{comment}");
        },
    );
    register_drift(h);
    register_parser(h);
    for &code in Code::ALL {
        h.case(format!("registry/row/{code}"), move || {
            let row = spec_rows()
                .iter()
                .find(|row| row.code == code.name())
                .unwrap_or_else(|| panic!("{code} is not in the document"));
            assert_eq!(severity_letter(code.severity()), row.severity);
            assert_eq!(code.phase().to_string(), row.phase);
            assert_eq!(code.owner().to_string(), row.owner);
            assert_eq!(code.since().to_string(), row.since);
            assert_eq!(code.fixture().to_string(), row.fixture);
            assert_eq!(code.title(), row.title);
            assert_eq!(Code::from_name(&row.code), Some(code));
            assert_eq!(code.to_string(), row.code);
            assert_eq!(code.reached(), code.since() <= CURRENT_MILESTONE);
        });
    }
}
