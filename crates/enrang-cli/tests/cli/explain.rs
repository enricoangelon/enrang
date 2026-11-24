//! `explain` over every row of the registry, and over everything that is not a row.
//!
//! A page's transcripts run as processes in a project that `enrang init` made, so a
//! command that reads a project finds one, and one that writes, as `init` does,
//! writes there and never into the crate. A `Compile` page holds source instead,
//! whose examples the syntax suite checks (`crates/enrang-syntax/tests/syntax/explain.rs`).

use std::path::Path;

use enrang_cli::EXIT_USAGE;
use enrang_diag::{CURRENT_MILESTONE, Code, FixtureKind, did_you_mean, explain};
use enrang_testkit::{Harness, TempDir};

use crate::support::{RETIRED, Ran, enrang_in, inproc, strings};

/// Runs the command a transcript shows on its first line, in `dir`.
fn run_transcript_command<'a>(transcript: &'a str, dir: &Path) -> (Ran, &'a str) {
    let (command, output) = transcript.split_once('\n').unwrap_or((transcript, ""));
    let words: Vec<&str> = command
        .strip_prefix("$ enrang ")
        .expect("a transcript opens with a command")
        .split(' ')
        .collect();
    (enrang_in(dir, &strings(&words)), output)
}

/// A fresh directory holding the project `enrang init` makes.
fn project() -> TempDir {
    let directory = TempDir::new("explain");
    let ran = enrang_in(directory.path(), &strings(&["init"]));
    assert_eq!(ran.code, 0, "{ran:?}");
    directory
}

/// The name in the help line of a failed lookup, if it offers one.
fn suggested(stderr: &str) -> Option<&str> {
    stderr
        .lines()
        .find_map(|line| line.strip_prefix("help: did you mean `"))
        .and_then(|rest| rest.strip_suffix("`?"))
}

pub fn register(h: &mut Harness) {
    for &code in Code::ALL {
        let name = code.name();
        h.case(format!("explain/every code/{name}"), move || {
            let outcome = inproc(&["explain", name]);
            assert_eq!(outcome.code, 0, "{outcome:?}");
            assert_eq!(outcome.stderr, "");
            assert!(
                outcome
                    .stdout
                    .starts_with(&format!("{name}: {}\n", code.title())),
                "{}",
                outcome.stdout
            );
            match explain(code) {
                Some(page) => {
                    assert_eq!(outcome.stdout, page.to_string());
                    assert!(!outcome.stdout.contains("No explain page yet"));
                }
                None => {
                    let expected = format!(
                        "{name}: {}\n\nNo explain page yet: it arrives with milestone {}, and this is milestone {CURRENT_MILESTONE}.\n",
                        code.title(),
                        code.since()
                    );
                    assert_eq!(outcome.stdout, expected);
                }
            }
        });
        h.case(
            format!("explain/lowercase is corrected/{name}"),
            move || {
                let lowered = name.to_lowercase();
                let outcome = inproc(&["explain", &lowered]);
                assert_eq!(outcome.code, EXIT_USAGE, "{outcome:?}");
                assert_eq!(outcome.stdout, "");
                assert_eq!(suggested(&outcome.stderr), Some(name), "{}", outcome.stderr);
            },
        );
        h.case(
            format!("explain/a wrong digit is corrected/{name}"),
            move || {
                let wrong = format!("{}x", &name[..name.len() - 1]);
                let outcome = inproc(&["explain", &wrong]);
                assert_eq!(outcome.code, EXIT_USAGE, "{outcome:?}");
                let close = suggested(&outcome.stderr).expect("a suggestion");
                let found = Code::from_name(close).expect("the suggestion is a real code");
                assert_eq!(close[..close.len() - 1], name[..name.len() - 1], "{found}");
            },
        );
    }

    for &code in Code::ALL {
        let Some(page) = explain(code) else { continue };
        if code.fixture() == FixtureKind::Compile {
            continue;
        }
        h.case(
            format!("explain/{code}/its failing transcript is what the command does"),
            move || {
                let directory = project();
                let (ran, shown) = run_transcript_command(page.failing, directory.path());
                assert_eq!(ran.code, i32::from(EXIT_USAGE), "{ran:?}");
                assert_eq!(ran.stderr.trim_end(), shown);
                assert_eq!(ran.stdout, "");
                assert!(shown.contains(&format!("error[{code}]")), "{shown}");
            },
        );
        h.case(
            format!("explain/{code}/its fixed transcript succeeds today"),
            move || {
                let directory = project();
                let (ran, shown) = run_transcript_command(page.fixed, directory.path());
                assert_eq!(ran.code, 0, "{}: {ran:?}", page.fixed);
                assert_eq!(shown, "", "a fixed transcript shows only its command");
            },
        );
    }
    h.case("explain/EN1301's page matches what reports it", || {
        let rule = explain(Code::EN1301).expect("a page").rule;
        for command in enrang_cli::DEFERRED {
            let stderr = inproc(&[command]).stderr;
            assert!(stderr.contains("[EN1301]"), "{stderr}");
            assert!(rule.contains(&format!("`{command}`")), "{command}");
        }
        for command in enrang_cli::LATER {
            let stderr = inproc(&[command.name]).stderr;
            assert!(!stderr.contains("EN1301"), "{stderr}");
            assert!(!rule.contains(&format!("`{}`", command.name)), "{rule}");
        }
    });
    h.case("explain/a page and only a page has these sections", || {
        let page = inproc(&["explain", "EN1301"]).stdout;
        for heading in ["Failing:", "Fixed:", "From TypeScript:"] {
            assert!(page.contains(heading), "{heading}");
        }
        let title = inproc(&["explain", "EN0414"]).stdout;
        for heading in ["Failing:", "Fixed:", "From TypeScript:"] {
            assert!(!title.contains(heading), "{heading}");
        }
    });
    h.case("explain/the milestone named is the row's own", || {
        let rows: &[(&str, &str)] = &[
            ("EN0414", "M4"),
            ("EN0821", "M4"),
            ("EN1101", "M4"),
            ("EN1108", "M4"),
            ("T0005", "M4"),
            ("EN1211", "M6"),
            ("EN0310", "M4"),
            ("EN0901", "M5"),
            ("EN1210", "M6"),
            ("EN1212", "M6"),
            ("EN0809", "M9"),
            ("T0001", "M4"),
            ("T0008", "M5"),
        ];
        for (code, milestone) in rows {
            let text = inproc(&["explain", code]).stdout;
            let expected = format!("it arrives with milestone {milestone},");
            assert!(text.contains(&expected), "{code}: {text}");
        }
    });
    for (code, why) in RETIRED {
        h.case(
            format!("explain/the retired code {code} names why it went"),
            move || {
                assert_eq!(Code::from_name(code), None, "a retired code has no row");
                let outcome = inproc(&["explain", code]);
                assert_eq!(outcome.code, EXIT_USAGE);
                assert_eq!(outcome.stdout, "");
                assert_eq!(
                    outcome.stderr,
                    format!("error: `{code}` is retired: {why}\n")
                );
            },
        );
    }
    h.case("explain/a suggestion is always the closest", || {
        let rows: &[(&str, &str)] = &[
            ("EN1031x", "EN1031"),
            ("E1301", "EN1301"),
            ("NE1301", "EN1301"),
            ("T001", "T0001"),
            ("T00011", "T0001"),
            // Equally close to several: the alphabetically first wins.
            ("EN130", "EN1030"),
            ("EN3101", "EN0101"),
            ("EN1300", "EN1030"),
        ];
        for (typed, wanted) in rows {
            let outcome = inproc(&["explain", typed]);
            assert_eq!(
                suggested(&outcome.stderr),
                Some(*wanted),
                "{typed}: {}",
                outcome.stderr
            );
        }
    });
    h.case("explain/a name near no code gets the shape of a code", || {
        for typed in ["frobnicate", "", "x", "EN", "01234567890123456789"] {
            let names: Vec<&str> = Code::ALL.iter().map(|code| code.name()).collect();
            assert_eq!(did_you_mean(typed, &names), None, "{typed}");
            let outcome = inproc(&["explain", typed]);
            assert_eq!(outcome.code, EXIT_USAGE, "{typed}");
            assert_eq!(
                outcome.stderr,
                format!(
                    "error: `{typed}` is not a diagnostic code\nhelp: codes look like `EN0601` and `T0001`\n"
                )
            );
        }
    });
    h.case("explain/a code is matched exactly, not by prefix", || {
        for typed in ["EN130", "EN13011", " EN1301", "EN1301 ", "EN1301\n"] {
            let outcome = inproc(&["explain", typed]);
            assert_eq!(outcome.code, EXIT_USAGE, "{typed:?}");
            assert_eq!(outcome.stdout, "", "{typed:?}");
        }
    });
    h.case(
        "explain/control characters never reach the terminal",
        || {
            for typed in [
                "a\x1bb",
                "\x07",
                "a\nb",
                "a\rb",
                "\u{9b}31m",
                "\u{202e}evil",
                "a\u{2028}b",
                "a\u{2069}b",
            ] {
                let outcome = inproc(&["explain", typed]);
                assert_eq!(outcome.code, EXIT_USAGE, "{typed:?}");
                let message = outcome.stderr.lines().next().expect("a message");
                assert!(!message.chars().any(char::is_control), "{message:?}");
                for hidden in ['\u{202e}', '\u{2028}', '\u{2069}'] {
                    assert!(!message.contains(hidden), "{message:?}");
                }
                assert_eq!(outcome.stderr.lines().count(), 2, "{:?}", outcome.stderr);
            }
        },
    );
}
