//! Explain pages: what exists at this milestone, and the transcripts' truth.
//!
//! Every reached row has its page (TESTING 18). A page may arrive before its row's
//! milestone is reached, but only for the milestone being built, as a crate may
//! (`enrang-suite`'s docs meta-test); it need not, since nothing is due before the
//! commit that closes that milestone. A page of any later row is stale. Pages of
//! `Compile` codes hold source, which `enrang-diag` cannot parse: the syntax suite
//! (`crates/enrang-syntax/tests/syntax/explain.rs`) checks that each failing example
//! fires its code and each fixed one parses clean and is formatted.

use std::fs;

use enrang_diag::{CURRENT_MILESTONE, Code, Diagnostic, FixtureKind, Help, Milestone, explain};
use enrang_testkit::{FixtureStatus, GateRow, Harness, gate, workspace_root};

use crate::support::{Src, doc, lines, same};

/// The family files, in file-name order.
const FAMILY_FILES: [&str; 12] = [
    "EN00.txt", "EN01.txt", "EN02.txt", "EN03.txt", "EN04.txt", "EN05.txt", "EN06.txt", "EN07.txt",
    "EN08.txt", "EN09.txt", "EN10.txt", "EN13.txt",
];

/// Each family file and its text.
fn family_texts() -> Vec<(&'static str, String)> {
    FAMILY_FILES
        .iter()
        .map(|&file| {
            let path = workspace_root()
                .join("crates/enrang-diag/explain")
                .join(file);
            let text = fs::read_to_string(path).expect("the family file exists");
            (file, text)
        })
        .collect()
}

/// The milestone after `current`: the one being built, whose pages may arrive
/// before the commit that closes it bumps `CURRENT_MILESTONE`. The last is its own.
fn being_built(current: Milestone) -> Milestone {
    use Milestone::*;
    const ORDER: [Milestone; 11] = [M0, M1, M2, M3, M4, M5, M6, M7, M8, M9, M10];
    let at = ORDER
        .iter()
        .position(|&milestone| milestone == current)
        .expect("a milestone");
    ORDER[(at + 1).min(ORDER.len() - 1)]
}

/// Codes with a page, in code order.
fn paged() -> Vec<Code> {
    Code::ALL
        .iter()
        .copied()
        .filter(|&code| explain(code).is_some())
        .collect()
}

pub fn register(h: &mut Harness) {
    h.case(
        "explain/reached rows have pages, and only the milestone being built has some early",
        || {
            let next = being_built(CURRENT_MILESTONE);
            let early = |code: Code| code.since() == next && next > CURRENT_MILESTONE;
            let rows: Vec<GateRow<'static, _>> = Code::ALL
                .iter()
                .filter(|&&code| !early(code))
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
            // M3 reaches M0's two rows, M1's 75, M2's 117 and its own 29; M4's 31 rows
            // are being built, and the 28 of M5 and later wait.
            assert_eq!(report.enforced, 223);
            assert_eq!(report.deferred, 28);
            // Any number of the milestone being built may have arrived, none later.
            for code in paged() {
                assert!(code.reached() || early(code), "{code} has a page too early");
            }
        },
    );
    h.case("explain/every reached row has its page", || {
        let reached: Vec<Code> = Code::ALL
            .iter()
            .copied()
            .filter(|code| code.reached())
            .collect();
        assert_eq!(reached.len(), 223);
        for code in reached {
            assert!(explain(code).is_some(), "{code} has no page");
        }
    });
    h.case(
        "explain/the milestone being built follows the current one",
        || {
            assert_eq!(being_built(Milestone::M0), Milestone::M1);
            assert_eq!(being_built(Milestone::M9), Milestone::M10);
            assert_eq!(being_built(Milestone::M10), Milestone::M10);
        },
    );
    h.case(
        "explain/a code whose page has not arrived gives None",
        || {
            for code in [Code::EN0310, Code::T0001, Code::EN1306] {
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
        files.sort();
        assert_eq!(
            files, FAMILY_FILES,
            "a new family must be added to FAMILIES"
        );
    });
    for code in paged() {
        h.case(
            format!("explain/{code}/has examples of its kind"),
            move || {
                let page = explain(code).expect("a page");
                assert_eq!(page.code, code);
                assert!(!page.rule.is_empty());
                match code.fixture() {
                    FixtureKind::Compile => {
                        for source in [page.failing, page.fixed] {
                            assert!(!source.starts_with("$ "), "source, not a transcript");
                            assert!(!source.contains("error["), "source, not a transcript");
                        }
                        assert_ne!(page.failing, page.fixed);
                    }
                    _ => {
                        assert!(page.failing.starts_with("$ enrang "), "{}", page.failing);
                        assert!(page.fixed.starts_with("$ enrang "), "{}", page.fixed);
                        assert!(page.failing.contains(&format!("error[{code}]:")));
                        assert!(!page.fixed.contains('\n'), "a fixed run shows its command");
                    }
                }
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
                assert!(text.contains(page.rule));
                if let Some(typescript) = page.typescript {
                    assert!(text.contains(typescript));
                }
            },
        );
        h.case(
            format!("explain/{code}/its rule is one paragraph"),
            move || {
                let page = explain(code).expect("a page");
                assert_eq!(lines(&[page.rule]).matches('\n').count(), 1);
                if let Some(typescript) = page.typescript {
                    assert!(!typescript.contains("\n\n"), "{typescript}");
                }
            },
        );
    }
    for code in [Code::EN1301, Code::EN1302] {
        h.case(
            format!("explain/{code}/has a TypeScript perspective"),
            move || {
                let page = explain(code).expect("a page");
                assert!(page.typescript.is_some());
            },
        );
    }
    h.case("explain/the rendered page has its parts in order", || {
        let page = explain(Code::EN1301).unwrap();
        let text = page.to_string();
        let places: Vec<usize> = [
            page.rule,
            "Failing:",
            "    $ enrang install",
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
            assert_eq!(commands.len(), 9, "{commands:?}");
            for command in &commands {
                assert!(rule.contains(&format!("`{command}`")), "{command}");
            }
            // And no more: a command that left the list leaves the page too.
            let listed: Vec<&str> = rule
                .split_once(". ")
                .expect("the rule opens with its list")
                .0
                .split('`')
                .skip(1)
                .step_by(2)
                .collect();
            assert_eq!(listed, commands, "{rule}");
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
            Diagnostic::spanless(
                Code::EN1301,
                "`enrang install` is not part of the prototype",
            )
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
        "explain/the family files have no trailing white space",
        || {
            for (file, text) in family_texts() {
                for line in text.lines() {
                    assert_eq!(line, line.trim_end(), "{file}: {line:?}");
                }
                // A family whose pages have not arrived is an empty file (plan h.1, 1B).
                assert!(
                    text.is_empty() || (text.ends_with('\n') && !text.ends_with("\n\n")),
                    "{file}"
                );
            }
        },
    );
    h.case("explain/page order is code order", || {
        let mut all = Vec::new();
        for (file, text) in family_texts() {
            let names: Vec<String> = text
                .lines()
                .filter_map(|line| line.strip_prefix("=== "))
                .map(str::to_owned)
                .collect();
            let mut sorted = names.clone();
            sorted.sort();
            assert_eq!(names, sorted, "{file}");
            all.extend(names);
        }
        let paged: Vec<&str> = paged().iter().map(|code| code.name()).collect();
        assert_eq!(all, paged);
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
