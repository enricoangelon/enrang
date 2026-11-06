//! `explain` over every row of the registry, and over everything that is not a row.

use enrang_cli::{EXIT_USAGE, Outcome};
use enrang_diag::{CURRENT_MILESTONE, Code, did_you_mean, explain};
use enrang_testkit::Harness;

use crate::support::{inproc, strings};

/// Runs the command a transcript shows on its first line.
fn run_transcript_command(transcript: &str) -> (Outcome, &str) {
    let (command, output) = transcript.split_once('\n').unwrap_or((transcript, ""));
    let words: Vec<&str> = command
        .strip_prefix("$ enrang ")
        .expect("a transcript opens with a command")
        .split(' ')
        .collect();
    (enrang_cli::run(&strings(&words), false), output)
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
        h.case(
            format!("explain/{code}/its failing transcript is what the command does"),
            move || {
                let (outcome, shown) = run_transcript_command(page.failing);
                assert_eq!(outcome.code, EXIT_USAGE, "{outcome:?}");
                assert_eq!(outcome.stderr.trim_end(), shown);
                assert!(shown.contains(&format!("error[{code}]")), "{shown}");
            },
        );
        h.case(
            format!("explain/{code}/its fixed transcript succeeds today"),
            move || {
                let (outcome, shown) = run_transcript_command(page.fixed);
                assert_eq!(outcome.code, 0, "{}: {outcome:?}", page.fixed);
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
        let title = inproc(&["explain", "EN0601"]).stdout;
        for heading in ["Failing:", "Fixed:", "From TypeScript:"] {
            assert!(!title.contains(heading), "{heading}");
        }
    });
    h.case("explain/the milestone named is the row's own", || {
        let rows: &[(&str, &str)] = &[
            ("EN0001", "M1"),
            ("EN0301", "M2"),
            ("EN0601", "M3"),
            ("EN0310", "M4"),
            ("EN0901", "M5"),
            ("EN1210", "M6"),
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
    h.case("explain/the retired code names what covers it", || {
        let outcome = inproc(&["explain", "EN0704"]);
        assert_eq!(outcome.code, EXIT_USAGE);
        assert_eq!(
            outcome.stderr,
            "error: `EN0704` is retired: R3's rule 4 with EN0710 and EN0712 covers what it named\n"
        );
    });
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
