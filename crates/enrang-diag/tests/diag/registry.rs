//! The registry against SPEC 13.2: one row per line, in both directions.

use std::collections::BTreeSet;
use std::sync::OnceLock;

use enrang_diag::{
    CURRENT_MILESTONE, Code, CodeRow, FixtureKind, Milestone, Owner, Phase, ROWS, Severity,
};
use enrang_testkit::Harness;

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
    h.case("registry/has 254 rows, like the document", || {
        assert_eq!(spec_rows().len(), 254, "the document");
        assert_eq!(ROWS.len(), 254, "ROWS");
        assert_eq!(Code::ALL.len(), 254, "Code::ALL");
    });
    h.case("registry/EN0704 is retired and absent", || {
        assert_eq!(Code::from_name("EN0704"), None);
        assert!(ROWS.iter().all(|row| row.name != "EN0704"));
        assert!(spec_rows().iter().all(|row| row.code != "EN0704"));
    });
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
            ["EN0430", "EN0431", "EN0503", "EN0719", "EN0914", "EN1212"]
        );
    });
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
    h.case("registry/the current milestone is M0", || {
        assert_eq!(CURRENT_MILESTONE, Milestone::M0);
    });
    h.case(
        "registry/M0 reaches only the deferred and unknown commands",
        || {
            let reached: Vec<Code> = Code::ALL.iter().copied().filter(|c| c.reached()).collect();
            assert_eq!(reached, [Code::EN1301, Code::EN1302]);
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
