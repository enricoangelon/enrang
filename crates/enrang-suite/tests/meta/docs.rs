//! The command line's tables against the documents they come from, so that neither
//! can drift. Everything here reads `docs/`, and nothing writes there.

use std::collections::{BTreeMap, BTreeSet};

use enrang_cli::{ALIASES, CLASSES, DEFERRED, FAMILIES, LATER, WORKING};
use enrang_diag::{CURRENT_MILESTONE, Code};
use enrang_target::CpuLevel;
use enrang_testkit::Harness;

use crate::hermetic::{manifest_of, read_manifest};
use crate::support::{backticked, crates, milestone_in, read, run_cli, table_after};

fn spec() -> String {
    read("docs/SPEC.md")
}

fn architecture() -> String {
    read("docs/ARCHITECTURE.md")
}

/// The one line of `doc` that starts with `head`.
pub fn line_starting(doc: &str, head: &str) -> String {
    let found: Vec<&str> = doc.lines().filter(|line| line.starts_with(head)).collect();
    assert_eq!(found.len(), 1, "lines starting {head:?}: {found:?}");
    found[0].to_owned()
}

/// The aliases a sentence names: `` `tsc`, `lint` to `check`, `compile` to `build` ``
/// gives each name the first target after it.
pub fn alias_pairs(sentence: &str) -> Vec<(String, String)> {
    let parts: Vec<&str> = sentence.split('`').collect();
    let mut pairs = Vec::new();
    let mut pending: Vec<String> = Vec::new();
    let mut index = 1;
    while index < parts.len() {
        let before = parts[index - 1];
        let token = parts[index].to_owned();
        if before.trim_end().ends_with(" to") {
            for name in pending.drain(..) {
                pairs.push((name, token.clone()));
            }
        } else {
            pending.push(token);
        }
        index += 2;
    }
    pairs
}

fn cli_aliases() -> Vec<(String, String)> {
    ALIASES
        .iter()
        .map(|alias| (alias.name.to_owned(), alias.target.to_owned()))
        .collect()
}

fn deferred_names() -> Vec<String> {
    DEFERRED.iter().map(|name| (*name).to_owned()).collect()
}

fn command_table() -> Vec<Vec<String>> {
    table_after(&architecture(), "| Command | From | Behaviour |")
}

/// `enrang build [file]` from a table cell, as the name and the usage without `enrang`.
fn command_cell(cell: &str) -> (String, String) {
    let usage = cell
        .trim_matches('`')
        .strip_prefix("enrang ")
        .unwrap_or_else(|| panic!("a command cell: {cell}"))
        .to_owned();
    let name = usage.split(' ').next().unwrap_or("").to_owned();
    (name, usage)
}

/// The crate table of ARCHITECTURE 1: each crate and the milestone it is due.
fn crate_table() -> BTreeMap<String, enrang_diag::Milestone> {
    let rows = table_after(&architecture(), "| Crate | Owns | Rust lines | From |");
    let mut table = BTreeMap::new();
    for row in rows {
        let names = backticked(&row[0]);
        let Some(name) = names.first() else {
            continue;
        };
        let since = milestone_in(row.last().expect("a last cell"))
            .unwrap_or_else(|| panic!("no milestone in {row:?}"));
        table.insert(name.clone(), since);
    }
    table
}

/// The dependency graph of ARCHITECTURE 1: each crate's allowed direct dependencies,
/// or `None` for the suite, which may use everything.
fn dependency_graph() -> BTreeMap<String, Option<BTreeSet<String>>> {
    let doc = architecture();
    let mut graph = BTreeMap::new();
    let mut before: BTreeSet<String> = BTreeSet::new();
    let block = doc
        .split("### Dependency graph")
        .nth(1)
        .expect("the section")
        .split("```")
        .nth(1)
        .expect("the block");
    for line in block.lines() {
        let Some((left, right)) = line.split_once("->") else {
            continue;
        };
        let name = left.trim().to_owned();
        let right = right.split('(').next().unwrap_or("").trim();
        let allowed = if right.contains("everything") {
            None
        } else if right.contains("all of the above") {
            Some(before.clone())
        } else {
            Some(
                right
                    .split_whitespace()
                    .map(|word| format!("enrang-{word}"))
                    .collect(),
            )
        };
        graph.insert(name.clone(), allowed);
        before.insert(name);
    }
    graph
}

pub fn register(h: &mut Harness) {
    h.case("docs/the deferred commands are those of SPEC 13.2", || {
        let line = line_starting(&spec(), "`EN1301` covers ");
        let names = backticked(line.split(" `EN1302` carries").next().expect("a head"));
        assert_eq!(names[0], "EN1301");
        assert_eq!(names[1..], deferred_names());
    });
    h.case("docs/the deferred commands are those of SPEC 16", || {
        let line = line_starting(&spec(), "**Compiler commands outside the prototype**");
        assert_eq!(backticked(&line), deferred_names());
    });
    h.case(
        "docs/the deferred commands are those of ARCHITECTURE 11",
        || {
            let line = line_starting(&architecture(), "**Deferred commands**");
            let names = backticked(line.split(" are EN1301").next().expect("a head"));
            assert_eq!(names, deferred_names());
        },
    );
    h.case("docs/the aliases are those of SPEC 13.2", || {
        let spec_text = spec();
        let line = spec_text
            .lines()
            .find(|line| line.starts_with("`EN1301` covers "))
            .expect("the line");
        let sentence = line
            .split("`EN1302` carries the aliases ")
            .nth(1)
            .expect("the sentence");
        assert_eq!(alias_pairs(sentence), cli_aliases());
    });
    h.case("docs/the aliases are those of ARCHITECTURE 11", || {
        let line = line_starting(&architecture(), "**Deferred commands**");
        let sentence = line.split("are EN1041. ").nth(1).expect("the sentence");
        let sentence = sentence.split(" (EN1302)").next().expect("the end");
        assert_eq!(alias_pairs(sentence), cli_aliases());
    });
    let alias_rows: &[(&str, &[(&str, &str)])] = &[
        ("`a` to `b`", &[("a", "b")]),
        ("`a`, `b` to `c`", &[("a", "c"), ("b", "c")]),
        (
            "`a` and `b` point to `c`, `d` to `e`",
            &[("a", "c"), ("b", "c"), ("d", "e")],
        ),
        ("no names", &[]),
    ];
    for (sentence, expected) in alias_rows {
        let (sentence, expected) = (*sentence, *expected);
        h.case(format!("docs/alias pairs of {sentence:?}"), move || {
            let wanted: Vec<(String, String)> = expected
                .iter()
                .map(|(a, b)| ((*a).to_owned(), (*b).to_owned()))
                .collect();
            assert_eq!(alias_pairs(sentence), wanted);
        });
    }
    h.case("docs/the command table names exactly the commands", || {
        let documented: BTreeSet<String> = command_table()
            .iter()
            .map(|row| command_cell(&row[0]).0)
            .collect();
        let known: BTreeSet<String> = WORKING
            .iter()
            .map(|command| command.name)
            .chain(LATER.iter().map(|command| command.name))
            .map(str::to_owned)
            .collect();
        assert_eq!(documented, known);
    });
    h.case(
        "docs/a later command is due later, with its usage and milestone",
        || {
            let rows = command_table();
            for command in LATER {
                let row = rows
                    .iter()
                    .find(|row| command_cell(&row[0]).0 == command.name)
                    .expect("a row");
                assert_eq!(command_cell(&row[0]).1, command.usage, "{}", command.name);
                let due = milestone_in(&row[1]).expect("a milestone");
                assert_eq!(due, command.since, "{}", command.name);
                assert!(
                    due > CURRENT_MILESTONE,
                    "`{}` was due at {due} but still reports that it arrives later",
                    command.name
                );
            }
        },
    );
    h.case("docs/a working command has reached its milestone", || {
        let rows = command_table();
        for command in WORKING {
            let row = rows
                .iter()
                .find(|row| command_cell(&row[0]).0 == command.name)
                .expect("a row");
            assert_eq!(command_cell(&row[0]).1, command.usage, "{}", command.name);
            let due = milestone_in(&row[1]).expect("a milestone");
            assert!(due <= CURRENT_MILESTONE, "{}", command.name);
        }
    });
    h.case("docs/the reached rows' commands exit as SPEC 13.2 says", || {
        let spec_text = spec();
        assert!(spec_text.contains(
            "Exit codes: 0 success, 1 compile errors, failed tests or lost output, 2 usage, 3 internal compiler error."
        ));
        for name in DEFERRED {
            assert_eq!(run_cli(&[(*name).to_owned()]).code, 2, "{name}");
        }
    });
    h.case(
        "docs/EN1301 and EN1302 keep the codes the command line uses",
        || {
            assert_eq!(Code::EN1301.title(), "deferred command");
            assert_eq!(Code::EN1302.title(), "unknown command");
            assert!(Code::EN1301.reached());
            assert!(Code::EN1302.reached());
        },
    );
    h.case("docs/the families are those of ARCHITECTURE 8.6", || {
        let rows = table_after(
            &architecture(),
            "| Family | Rung | C1, C2 | C3 route | C4 |",
        );
        let documented: Vec<(String, String)> = rows
            .iter()
            .map(|row| (row[0].clone(), row[1].replace('`', "")))
            .collect();
        let shown: Vec<(String, String)> = FAMILIES
            .iter()
            .map(|family| (family.name.to_owned(), family.rung.to_owned()))
            .collect();
        assert_eq!(shown, documented);
    });
    h.case(
        "docs/the evidence table has the four classes of SPEC 10.6",
        || {
            let doc = spec();
            for class in CLASSES {
                assert!(doc.contains(&format!("**{class}**")), "{class}");
            }
            assert_eq!(CLASSES.len(), 4);
        },
    );
    h.case("docs/every rung the family table names is a level", || {
        for family in FAMILIES {
            let names: Vec<&str> = family
                .rung
                .split([',', ';'])
                .map(|part| part.split_whitespace().next().expect("a word"))
                .collect();
            for name in names {
                assert!(CpuLevel::from_name(name).is_some(), "{name}");
            }
        }
    });
    h.case(
        "docs/the crates are exactly those due at this milestone",
        || {
            let due: Vec<String> = crate_table()
                .into_iter()
                .filter(|(_, since)| *since <= CURRENT_MILESTONE)
                .map(|(name, _)| name)
                .collect();
            assert_eq!(crates(), due);
        },
    );
    h.case(
        "docs/the crate table has crates of later milestones too",
        || {
            let table = crate_table();
            assert!(table.len() > crates().len(), "{table:?}");
        },
    );
    h.case("docs/every dependency is an edge of the graph", || {
        let graph = dependency_graph();
        for name in crates() {
            let allowed = graph
                .get(&name)
                .unwrap_or_else(|| panic!("{name} is not in the graph"));
            let (dependencies, _) = read_manifest(&manifest_of(&name));
            let Some(allowed) = allowed else {
                continue;
            };
            for dependency in dependencies {
                let testkit_for_tests =
                    dependency.name == "enrang-testkit" && dependency.table == "dev-dependencies";
                assert!(
                    testkit_for_tests || allowed.contains(&dependency.name),
                    "{name} depends on {} in [{}]",
                    dependency.name,
                    dependency.table
                );
            }
        }
    });
    h.case("docs/the graph reader finds the shapes it must", || {
        let graph = dependency_graph();
        let cli = graph["enrang-cli"].clone().expect("a list");
        assert!(cli.contains("enrang-driver"), "{cli:?}");
        assert!(!cli.contains("enrang-base"), "{cli:?}");
        let driver = graph["enrang-driver"].clone().expect("a list");
        assert!(driver.contains("enrang-format"), "{driver:?}");
        assert!(!driver.contains("enrang-cli"), "{driver:?}");
        assert_eq!(graph["enrang-suite"], None);
        assert_eq!(
            graph["enrang-testkit"],
            Some(BTreeSet::from(["enrang-base".to_owned()]))
        );
    });
}
