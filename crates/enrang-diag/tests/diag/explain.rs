//! Explain pages: what exists at this milestone, and the transcripts' truth.

use std::fs;

use enrang_diag::{CURRENT_MILESTONE, Code, Diagnostic, FixtureKind, Help, explain};
use enrang_testkit::{FixtureStatus, GateRow, Harness, gate, workspace_root};

use crate::support::{Src, doc, lines, same};

fn page_text() -> String {
    let path = workspace_root().join("crates/enrang-diag/explain/EN13.txt");
    fs::read_to_string(path).expect("the family file exists")
}

pub fn register(h: &mut Harness) {
    h.case(
        "explain/reached rows have pages and others do not yet",
        || {
            let rows: Vec<GateRow<'static, _>> = Code::ALL
                .iter()
                .map(|&code| GateRow {
                    id: code.name(),
                    since: code.since(),
                    fixture: if explain(code).is_some() {
                        FixtureStatus::Passing
                    } else {
                        FixtureStatus::Missing
                    },
                })
                .collect();
            let report = gate(&rows, &CURRENT_MILESTONE);
            assert!(report.is_clean(), "{report}");
            assert_eq!(report.enforced, 2);
            assert_eq!(report.deferred, 252);
        },
    );
    h.case(
        "explain/a code whose page has not arrived gives None",
        || {
            for code in [Code::EN0601, Code::EN0101, Code::T0001, Code::EN1303] {
                assert_eq!(explain(code), None, "{code}");
            }
        },
    );
    h.case("explain/every page in the directory is wired in", || {
        let directory = workspace_root().join("crates/enrang-diag/explain");
        let mut files = Vec::new();
        for entry in fs::read_dir(directory).expect("the directory exists") {
            let entry = entry.expect("a directory entry");
            files.push(entry.file_name().to_string_lossy().into_owned());
            let text = fs::read_to_string(entry.path()).expect("a text file");
            for line in text.lines() {
                if let Some(name) = line.strip_prefix("=== ") {
                    let code = Code::from_name(name).expect("a known code");
                    assert!(explain(code).is_some(), "{name} is not loaded");
                }
            }
        }
        assert_eq!(
            files,
            ["EN13.txt"],
            "a new family must be added to FAMILIES"
        );
    });
    for code in [Code::EN1301, Code::EN1302] {
        h.case(
            format!("explain/{code}/has a transcript of its kind"),
            move || {
                assert_eq!(code.fixture(), FixtureKind::Cli);
                let page = explain(code).expect("a page");
                assert_eq!(page.code, code);
                assert!(page.failing.starts_with("$ enrang "), "{}", page.failing);
                assert!(page.fixed.starts_with("$ enrang "), "{}", page.fixed);
                assert!(page.failing.contains(&format!("error[{code}]:")));
                assert!(!page.fixed.contains("error["), "the fixed run has no error");
                assert!(!page.rule.is_empty());
                assert!(page.typescript.is_some());
            },
        );
        h.case(
            format!("explain/{code}/renders with its title first"),
            move || {
                let page = explain(code).expect("a page");
                let text = page.to_string();
                let first = text.lines().next().expect("a first line");
                assert_eq!(first, format!("{code}: {}", code.title()));
                assert!(text.ends_with('\n') && !text.ends_with("\n\n"), "{text:?}");
                for part in [page.rule, page.typescript.unwrap()] {
                    assert!(text.contains(part));
                }
            },
        );
    }
    h.case("explain/the rendered page has its parts in order", || {
        let page = explain(Code::EN1301).unwrap();
        let text = page.to_string();
        let places: Vec<usize> = [
            page.rule,
            "Failing:",
            "    $ enrang fmt",
            "Fixed:",
            "    $ enrang --help",
            "From TypeScript:",
        ]
        .iter()
        .map(|part| {
            text.find(part)
                .unwrap_or_else(|| panic!("no `{part}` in {text}"))
        })
        .collect();
        let mut sorted = places.clone();
        sorted.sort_unstable();
        assert_eq!(places, sorted, "{text}");
    });
    h.case(
        "explain/EN1301's page names every command SPEC 13.2 lists",
        || {
            let sentence = doc("SPEC.md")
                .lines()
                .find(|line| line.starts_with("`EN1301` covers "))
                .expect("the sentence exists");
            let rule = explain(Code::EN1301).unwrap().rule;
            let commands: Vec<&str> = sentence
                .split_once(". ")
                .expect("it is a sentence")
                .0
                .split('`')
                .skip(3)
                .step_by(2)
                .collect();
            assert_eq!(commands.len(), 10, "{commands:?}");
            for command in commands {
                assert!(rule.contains(&format!("`{command}`")), "{command}");
            }
        },
    );
    h.case(
        "explain/EN1302's page carries the aliases of SPEC 13.2",
        || {
            let rule = explain(Code::EN1302).unwrap().rule;
            for (from, to) in [
                ("`tsc` and `lint`", "`check`"),
                ("`compile`", "`build`"),
                ("`start`", "`run`"),
            ] {
                assert!(
                    rule.contains(&format!("{from} at {to}")),
                    "{from} {to}\n{rule}"
                );
            }
        },
    );
    let transcripts: [(Code, fn() -> Diagnostic); 2] = [
        (Code::EN1301, || {
            Diagnostic::spanless(Code::EN1301, "`enrang fmt` is not part of the prototype")
        }),
        (Code::EN1302, || {
            Diagnostic::spanless(Code::EN1302, "`targest` is not an `enrang` command")
                .with_help(Help::text("did you mean `enrang targets`?"))
        }),
    ];
    for (code, build) in transcripts {
        h.case(
            format!("explain/{code}/its transcript is what the renderer prints"),
            move || {
                let page = explain(code).unwrap();
                let (command, output) =
                    page.failing.split_once('\n').expect("a command and output");
                assert!(command.starts_with("$ "));
                let src = Src::new("a.en", "");
                same(&format!("{output}\n"), &src.one(build()));
            },
        );
    }
    h.case(
        "explain/the family file has no trailing white space",
        || {
            for line in page_text().lines() {
                assert_eq!(line, line.trim_end(), "{line:?}");
            }
        },
    );
    h.case("explain/page order is code order", || {
        let text = page_text();
        let names: Vec<&str> = text
            .lines()
            .filter_map(|line| line.strip_prefix("=== "))
            .collect();
        assert_eq!(names, ["EN1301", "EN1302"]);
    });
    h.case(
        "explain/a section marker cannot hide inside a transcript",
        || {
            let page = explain(Code::EN1301).unwrap();
            assert_eq!(
                lines(&[page.rule]).matches('\n').count(),
                1,
                "the rule is one paragraph"
            );
            assert!(!page.failing.contains("--- "));
            assert!(!page.failing.contains("=== "));
        },
    );
}
