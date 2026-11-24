//! The command line's tables against the documents they come from, so that neither
//! can drift. Everything here reads `docs/`, and nothing writes there.

use std::collections::{BTreeMap, BTreeSet};

use enrang_cli::{ALIASES, CLASSES, DEFERRED, FAMILIES, LATER, WORKING};
use enrang_diag::{CURRENT_MILESTONE, Code};
use enrang_target::CpuLevel;
use enrang_testkit::Harness;

use crate::hermetic::{manifest_of, read_manifest};
use crate::support::{backticked, being_built, crates, milestone_in, read, run_cli, table_after};

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

/// The codes SPEC 13.2 retired, each with the live codes its reason there points
/// to, written by hand. A reason shared by several codes names the union of theirs.
/// `enrang explain` may name fewer: EN1040's text shows the new form instead.
const RETIRED: [(&str, &[&str]); 18] = [
    ("EN0204", &["EN0442"]),
    ("EN0212", &[]),
    ("EN0217", &[]),
    ("EN0223", &[]),
    ("EN0306", &["EN0311"]),
    ("EN0407", &[]),
    ("EN0431", &["EN0441"]),
    ("EN0505", &[]),
    ("EN0620", &["EN0460"]),
    ("EN0704", &["EN0710", "EN0712"]),
    ("EN0716", &[]),
    ("EN0719", &["EN0706"]),
    ("EN0720", &["EN0401"]),
    ("EN0810", &[]),
    ("EN1008", &[]),
    ("EN1016", &[]),
    ("EN1020", &[]),
    ("EN1040", &["EN0456"]),
];

fn successors(code: &str) -> &'static [&'static str] {
    RETIRED
        .iter()
        .find(|(retired, _)| *retired == code)
        .unwrap_or_else(|| panic!("{code} is not retired by hand"))
        .1
}

/// The `ENdddd` codes `text` names, in order.
fn codes_in(text: &str) -> Vec<String> {
    let bytes = text.as_bytes();
    let mut found = Vec::new();
    for (at, _) in text.match_indices("EN") {
        let end = at + 6;
        let is_code = end <= bytes.len()
            && (at == 0 || !bytes[at - 1].is_ascii_alphanumeric())
            && bytes[at + 2..end].iter().all(u8::is_ascii_digit)
            && bytes.get(end).is_none_or(|b| !b.is_ascii_alphanumeric());
        if is_code {
            found.push(text[at..end].to_owned());
        }
    }
    found
}

/// Codes SPEC 13.2 retires with one reason, and whether the reason is a sentence of
/// its own (`EN0704 is retired: <why>.`) or a parenthesis after the codes in a list
/// (`EN0204 and EN0212 (<why>)`).
#[derive(Debug)]
struct Retirement {
    codes: Vec<String>,
    why: String,
    sentence: bool,
}

/// Every retirement in the paragraph of SPEC 13.2 that says codes are never reused.
fn retirements(spec: &str) -> Vec<Retirement> {
    let section = spec.split_once("### 13.2 Catalog").expect("SPEC 13.2").1;
    let section = section.split_once("```text").expect("the catalog block").0;
    let paragraph = section
        .split("\n\n")
        .find(|paragraph| paragraph.contains("Codes are never reused."))
        .expect("the paragraph on retired codes");
    let mut found = Vec::new();
    // The sentences first, then the lists in what is left.
    let mut rest = String::new();
    let mut tail = paragraph;
    while let Some(at) = tail.find(" is retired: ") {
        let Some(code) = tail
            .get(at.saturating_sub(6)..at)
            .filter(|code| codes_in(code).len() == 1)
        else {
            rest.push_str(&tail[..at + 1]);
            tail = &tail[at + 1..];
            continue;
        };
        let why_start = at + " is retired: ".len();
        let why_len = tail[why_start..]
            .find(". ")
            .or_else(|| tail[why_start..].trim_end().strip_suffix('.').map(str::len))
            .expect("the sentence ends");
        found.push(Retirement {
            codes: vec![code.to_owned()],
            why: tail[why_start..why_start + why_len].to_owned(),
            sentence: true,
        });
        rest.push_str(&tail[..at - 6]);
        rest.push_str(". ");
        tail = tail[why_start + why_len + 1..].trim_start();
    }
    rest.push_str(tail);
    let mut depth = 0;
    let mut outside = String::new();
    let mut why = String::new();
    for c in rest.chars() {
        match (c, depth) {
            ('(', 0) => depth = 1,
            (')', 1) => {
                depth = 0;
                let codes = codes_in(&outside);
                if !codes.is_empty() {
                    found.push(Retirement {
                        codes,
                        why: why.clone(),
                        sentence: false,
                    });
                }
                outside.clear();
                why.clear();
            }
            ('(', _) => {
                depth += 1;
                why.push(c);
            }
            (')', _) => {
                depth -= 1;
                why.push(c);
            }
            (_, 0) => {
                outside.push(c);
                if outside.ends_with(". ") {
                    outside.clear();
                }
            }
            _ => why.push(c),
        }
    }
    assert_eq!(depth, 0, "a parenthesis never closes: {paragraph}");
    found
}

fn retired(h: &mut Harness) {
    h.case(
        "docs/the retirement reader finds the shapes it must",
        || {
            let spec = "### 13.2 Catalog\n\nIntro (`TESTING.md` section 18). Codes are never \
                    reused. EN0001 is retired: rule 3 (of R3) with EN0002 covers it. Also \
                    retired: EN0003 and EN0004 (see EN0005; a (nested) part), EN0006 \
                    (gone) and EN0007 (the end).\n\n```text\n```\n";
            let found: Vec<String> = retirements(spec)
                .iter()
                .map(|r| format!("{} {:?} {}", r.codes.join(","), r.why, r.sentence))
                .collect();
            assert_eq!(
                found,
                [
                    "EN0001 \"rule 3 (of R3) with EN0002 covers it\" true",
                    "EN0003,EN0004 \"see EN0005; a (nested) part\" false",
                    "EN0006 \"gone\" false",
                    "EN0007 \"the end\" false",
                ]
            );
        },
    );
    h.case("docs/SPEC 13.2 retires the codes written down here", || {
        let mut named: Vec<String> = retirements(&spec())
            .into_iter()
            .flat_map(|retirement| retirement.codes)
            .collect();
        named.sort();
        let hand: Vec<&str> = RETIRED.iter().map(|(code, _)| *code).collect();
        assert_eq!(named, hand, "each retired code once, with its reason");
    });
    h.case(
        "docs/SPEC 13.2 points each retired code to the live codes written down here",
        || {
            for retirement in retirements(&spec()) {
                let mut named = codes_in(&retirement.why);
                named.sort();
                named.dedup();
                let mut hand: Vec<String> = retirement
                    .codes
                    .iter()
                    .flat_map(|code| successors(code).iter().map(|s| (*s).to_owned()))
                    .collect();
                hand.sort();
                hand.dedup();
                assert_eq!(named, hand, "{:?}: {}", retirement.codes, retirement.why);
                for successor in &hand {
                    assert!(
                        Code::from_name(successor).is_some(),
                        "{:?} points to {successor}, which is no catalog row",
                        retirement.codes
                    );
                }
            }
        },
    );
    h.case(
        "docs/`enrang explain` agrees with SPEC 13.2 on each retired code",
        || {
            for retirement in retirements(&spec()) {
                for code in &retirement.codes {
                    let ran = run_cli(&["explain".to_owned(), code.clone()]);
                    let prefix = format!("error: `{code}` is retired: ");
                    let why = ran
                        .stderr
                        .strip_prefix(&prefix)
                        .and_then(|rest| rest.strip_suffix('\n'))
                        .unwrap_or_else(|| panic!("{code}: {ran:?}"));
                    assert_eq!((ran.code, ran.stdout.as_str()), (2, ""), "{code}");
                    for named in codes_in(why) {
                        assert!(
                            successors(code).contains(&named.as_str()),
                            "`enrang explain {code}` points to {named}; SPEC 13.2 does not"
                        );
                    }
                    if retirement.sentence {
                        assert_eq!(why, retirement.why, "{code}: SPEC's sentence is explain's");
                    }
                }
            }
        },
    );
}

fn retired_alone(h: &mut Harness) {
    h.case(
        "docs/`enrang explain` gives SPEC 13.2's reason for a code retired alone",
        || {
            let mut checked = 0;
            for retirement in retirements(&spec()) {
                let [code] = &retirement.codes[..] else {
                    continue;
                };
                // EN1040's text shows the new form instead.
                if code == "EN1040" {
                    continue;
                }
                let ran = run_cli(&["explain".to_owned(), code.clone()]);
                let prefix = format!("error: `{code}` is retired: ");
                let why = ran
                    .stderr
                    .strip_prefix(&prefix)
                    .and_then(|rest| rest.strip_suffix('\n'))
                    .unwrap_or_else(|| panic!("{code}: {ran:?}"));
                let plain = why.replace(" now,", "").replace(" now", "");
                assert_eq!(plain, retirement.why, "{code}");
                checked += 1;
            }
            assert_eq!(checked, 15, "the codes retired alone, less EN1040");
        },
    );
}

/// The message quoted right after `head` in `doc`, in double backticks or in single
/// ones.
fn quoted_after(doc: &str, head: &str) -> String {
    let at = doc.find(head).unwrap_or_else(|| panic!("no `{head}`")) + head.len();
    let rest = &doc[at..];
    if let Some(rest) = rest.strip_prefix("`` ") {
        return rest[..rest.find(" ``").expect("the quote closes")].to_owned();
    }
    let rest = rest.strip_prefix('`').expect("a quoted message");
    rest[..rest.find('`').expect("the quote closes")].to_owned()
}

/// For codes whose message is fixed, the places each document quotes it, which
/// must all give the catalog title.
fn quoted_messages(h: &mut Harness) {
    let places: [(Code, &[(&str, &str)]); 3] = [
        (
            Code::EN0458,
            &[
                (
                    "docs/SPEC.md",
                    "`rex.into()` on a `const rex = new Dog(\"Rex\");` whose class does not override `into` is EN0458, ",
                ),
                (
                    "docs/ARCHITECTURE.md",
                    "outside generic code and per-class copies: EN0458, ",
                ),
                ("docs/TESTING.md", "EN0458 at `rex.into()`, "),
                ("docs/TESTING.md", "EN0458 at `b.build()`, "),
            ],
        ),
        (
            Code::EN0459,
            &[
                ("docs/SPEC.md", "so it is warning EN0459, "),
                ("docs/ARCHITECTURE.md", "gets EN0459, "),
                ("docs/TESTING.md", "warning EN0459 at `run`, "),
            ],
        ),
        (
            Code::EN0621,
            &[
                ("docs/SPEC.md", "so it is EN0621, "),
                ("docs/ARCHITECTURE.md", "so it is EN0621 in phase 3, "),
                ("docs/TESTING.md", "EN0621 at `(s += \"?\")`, "),
            ],
        ),
    ];
    for (code, quotes) in places {
        h.case(
            format!("docs/each document quotes {code} by its title"),
            move || {
                for (file, head) in quotes {
                    let message = quoted_after(&read(file), head);
                    assert_eq!(message, code.title(), "{file}: `{head}`");
                }
            },
        );
    }
}

/// The panic that `FV-06-codepoint` expects is SPEC 9.1's row for `codePointAt`, the
/// only operation left that raises it.
fn char_boundary_panic(h: &mut Harness) {
    h.case(
        "docs/TESTING's codePointAt row panics as SPEC 9.1 says",
        || {
            let spec = spec();
            let rows: Vec<&str> = spec
                .lines()
                .filter(|line| line.starts_with("| `") && line.contains("`string.codePointAt`"))
                .collect();
            assert_eq!(rows.len(), 1, "{rows:?}");
            let template = rows[0]
                .strip_prefix("| `")
                .and_then(|rest| rest.split_once("` |"))
                .expect("a message cell")
                .0;
            assert!(!rows[0].contains("`string.slice` at"), "{}", rows[0]);
            let row = line_starting(&read("docs/TESTING.md"), "| `FV-06-codepoint`:");
            let expected = row
                .split_once("then panics `")
                .and_then(|(_, rest)| rest.split_once('`'))
                .expect("the row names its panic")
                .0;
            let general: String = expected
                .split(' ')
                .map(|word| {
                    if word.bytes().all(|b| b.is_ascii_digit()) {
                        "I"
                    } else {
                        word
                    }
                })
                .collect::<Vec<_>>()
                .join(" ");
            assert_eq!(general, template);
        },
    );
}

pub fn register(h: &mut Harness) {
    retired(h);
    retired_alone(h);
    quoted_messages(h);
    char_boundary_panic(h);
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
        // A command of the milestone being built works before the commit that
        // closes it, as a crate of that milestone may exist.
        let rows = command_table();
        for command in WORKING {
            let row = rows
                .iter()
                .find(|row| command_cell(&row[0]).0 == command.name)
                .expect("a row");
            assert_eq!(command_cell(&row[0]).1, command.usage, "{}", command.name);
            let due = milestone_in(&row[1]).expect("a milestone");
            assert_eq!(due, command.since, "{}", command.name);
            assert!(due <= being_built(CURRENT_MILESTONE), "{}", command.name);
        }
    });
    h.case("docs/the reached rows' commands exit as SPEC 13.2 says", || {
        let spec_text = spec();
        assert!(spec_text.contains(
            "Exit codes: 0 success, 1 compile errors, failed tests or lost output, 2 usage, 3 internal compiler error. `enrang fmt --check` also exits 1 when a file would change."
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
        "docs/the crates are those due at this milestone, and some of the next",
        || {
            let table = crate_table();
            let present = crates();
            let next = being_built(CURRENT_MILESTONE);
            for (name, since) in &table {
                if *since <= CURRENT_MILESTONE {
                    assert!(
                        present.contains(name),
                        "{name} is due at {since} and missing"
                    );
                }
            }
            for name in &present {
                let since = table
                    .get(name)
                    .unwrap_or_else(|| panic!("{name} is not in the crate table"));
                assert!(
                    *since <= next,
                    "{name} is due at {since}, after {next}, the milestone being built"
                );
            }
        },
    );
    h.case(
        "docs/the crates M2 delivers are present: hir, layout, rtlib and sema",
        || {
            use enrang_diag::Milestone;
            let table = crate_table();
            let due: Vec<&str> = table
                .iter()
                .filter(|(_, since)| **since == Milestone::M2)
                .map(|(name, _)| name.as_str())
                .collect();
            assert_eq!(
                due,
                ["enrang-hir", "enrang-layout", "enrang-rtlib", "enrang-sema"]
            );
            assert!(Milestone::M2 <= CURRENT_MILESTONE, "M2's crates are due");
            let present = crates();
            for name in due {
                assert!(present.iter().any(|p| p == name), "{name} is due at M2");
            }
        },
    );
    h.case(
        "docs/the crates M3 delivers are present: borrowck, mir and mirbuild",
        || {
            use enrang_diag::Milestone;
            let table = crate_table();
            let due: Vec<&str> = table
                .iter()
                .filter(|(_, since)| **since == Milestone::M3)
                .map(|(name, _)| name.as_str())
                .collect();
            assert_eq!(due, ["enrang-borrowck", "enrang-mir", "enrang-mirbuild"]);
            assert!(Milestone::M3 <= CURRENT_MILESTONE, "M3's crates are due");
            let present = crates();
            for name in due {
                assert!(present.iter().any(|p| p == name), "{name} is due at M3");
            }
        },
    );
    h.case(
        "docs/the milestone being built follows the current one",
        || {
            use enrang_diag::Milestone;
            assert_eq!(being_built(Milestone::M0), Milestone::M1);
            assert_eq!(being_built(Milestone::M9), Milestone::M10);
            assert_eq!(being_built(Milestone::M10), Milestone::M10);
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
