//! `targets --evidence` must never claim evidence that does not exist (TESTING 21).

use enrang_cli::{CLASSES, FAMILIES};
use enrang_diag::CURRENT_MILESTONE;
use enrang_target::CpuLevel;
use enrang_testkit::Harness;

use crate::support::inproc;

fn table() -> Vec<Vec<String>> {
    let outcome = inproc(&["targets", "--evidence"]);
    assert_eq!(outcome.code, 0);
    assert_eq!(outcome.stderr, "");
    outcome
        .stdout
        .lines()
        .skip_while(|line| !line.starts_with("family"))
        .take_while(|line| !line.is_empty())
        .map(|line| {
            line.split("  ")
                .map(str::trim)
                .filter(|cell| !cell.is_empty())
                .map(str::to_owned)
                .collect()
        })
        .collect()
}

pub fn register(h: &mut Harness) {
    h.case("evidence/the header names the four classes", || {
        assert_eq!(table()[0], ["family", "rung", "C1", "C2", "C3", "C4"]);
    });
    h.case("evidence/every family has one row, in table order", || {
        let rows = table();
        assert_eq!(rows.len() - 1, FAMILIES.len());
        assert_eq!(FAMILIES.len(), 12);
        for (row, family) in rows[1..].iter().zip(FAMILIES) {
            assert_eq!(row[0], family.name);
            assert_eq!(row[1], family.rung);
        }
    });
    for family in FAMILIES {
        let name = family.name;
        h.case(format!("evidence/{name} claims nothing"), move || {
            let rows = table();
            let row = rows
                .iter()
                .find(|row| row[0] == name)
                .expect("the family has a row");
            assert_eq!(row.len(), 2 + CLASSES.len(), "{row:?}");
            assert_eq!(row[2..5], ["planned"; 3], "{row:?}");
            let testable = name.contains("Q8400") || name == "Newer";
            let c4 = if testable { "planned" } else { "no hardware" };
            assert_eq!(row[5], c4, "{row:?}");
        });
    }
    for family in FAMILIES {
        let name = family.name;
        let rung = family.rung;
        h.case(
            format!("evidence/the rung of {name} is a real level"),
            move || {
                let cleaned = rung.replace(';', ",");
                for part in cleaned.split(',') {
                    let level = part.split_whitespace().next().expect("a word");
                    assert!(CpuLevel::from_name(level).is_some(), "{name}: {level}");
                }
            },
        );
    }
    h.case(
        "evidence/no word in the output claims an achievement",
        || {
            let text = inproc(&["targets", "--evidence"]).stdout;
            let table_text: String = text
                .lines()
                .skip_while(|line| !line.starts_with("family"))
                .take_while(|line| !line.is_empty())
                .collect::<Vec<_>>()
                .join("\n");
            for claim in [
                "reached", "achieved", "proven", "verified", "passed", "yes", "commit",
            ] {
                assert!(!table_text.contains(claim), "{claim}");
            }
        },
    );
    h.case("evidence/the output says nothing has been achieved", || {
        let text = inproc(&["targets", "--evidence"]).stdout;
        assert!(
            text.contains(&format!(
                "Nothing has been achieved: this is milestone {CURRENT_MILESTONE}, which generates no code, and no\nchip has run any Enrang output. `no hardware` means no such chip is available to test on.\n"
            )),
            "{text}"
        );
    });
    h.case(
        "evidence/it reads no file, so it holds in an empty directory",
        || {
            let directory = enrang_testkit::TempDir::new("evidence");
            let args = crate::support::strings(&["targets", "--evidence"]);
            let there = crate::support::enrang_in(directory.path(), &args);
            assert_eq!(there.stdout, inproc(&["targets", "--evidence"]).stdout);
            directory.write("evidence/ledger.json", "{\"i386\": \"C1\"}\n");
            directory.write("evidence/hardware.txt", "Q8400 C4\n");
            let with_ledger = crate::support::enrang_in(directory.path(), &args);
            assert_eq!(with_ledger, there);
        },
    );
}
