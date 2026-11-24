//! `--help` tells the truth about what works.

use enrang_cli::{ALIASES, DEFERRED, LATER, WORKING};
use enrang_diag::CURRENT_MILESTONE;
use enrang_testkit::Harness;

use crate::support::inproc;

fn help() -> String {
    inproc(&["--help"]).stdout
}

/// The lines of the section whose heading starts with `start`.
fn section(start: &str) -> Vec<String> {
    help()
        .lines()
        .skip_while(|line| !line.starts_with(start))
        .skip(1)
        .take_while(|line| !line.is_empty())
        .map(str::to_owned)
        .collect()
}

pub fn register(h: &mut Harness) {
    h.case(
        "help/says what cannot be done yet before anything else",
        || {
            let text = help();
            let cannot = text
                .find("it cannot yet\ncompile or run a program")
                .expect("it says so");
            let commands = text.find("Commands that work").expect("it lists them");
            assert!(cannot < commands);
            assert!(text.contains("it checks syntax and formats code"));
        },
    );
    h.case(
        "help/the working section is exactly the working commands",
        || {
            let lines = section("Commands that work today:");
            assert_eq!(lines.len(), WORKING.len());
            for (line, command) in lines.iter().zip(WORKING) {
                assert!(line.starts_with(&format!("  {} ", command.usage)), "{line}");
                assert!(line.ends_with(command.summary), "{line}");
            }
        },
    );
    h.case(
        "help/the later section is exactly the later commands",
        || {
            let lines = section("Commands that later milestones deliver");
            assert_eq!(lines.len(), LATER.len());
            for (line, command) in lines.iter().zip(LATER) {
                assert!(line.starts_with(&format!("  {} ", command.usage)), "{line}");
                assert!(line.ends_with(command.delivers), "{line}");
            }
        },
    );
    h.case(
        "help/the deferred section is exactly the deferred commands",
        || {
            let lines = section("Outside the prototype");
            assert_eq!(lines, [format!("  {}", DEFERRED.join(" "))]);
        },
    );
    h.case("help/the later section does not say EN1301", || {
        let heading = help()
            .lines()
            .find(|line| line.starts_with("Commands that later milestones deliver"))
            .expect("the heading")
            .to_owned();
        assert!(!heading.contains("EN1301"), "{heading}");
        let later = inproc(&["build"]).stderr;
        assert!(!later.contains("EN1301"), "{later}");
    });
    h.case("help/no alias is advertised as a command", || {
        let text = help();
        for alias in ALIASES {
            let advertised = format!("  {} ", alias.name);
            assert!(!text.contains(&advertised), "{}", alias.name);
        }
    });
    h.case("help/the exit statuses are those of SPEC 13.2", || {
        assert!(
            help().contains(
                "Exit status: 0 success, 1 compile errors, failed tests, lost output or a file that\n`fmt --check` would change, 2 usage, 3 internal compiler error.\n"
            )
        );
    });
    h.case("help/both top-level flags are listed", || {
        let lines = section("Flags:");
        assert_eq!(lines.len(), 2, "{lines:?}");
        assert!(lines[0].starts_with("  -h, --help "), "{lines:?}");
        assert!(lines[1].starts_with("  -V, --version "), "{lines:?}");
    });
    h.case("help/each flag is accepted", || {
        let flags: &[&[&str]] = &[
            &["--help"],
            &["-h"],
            &["--version"],
            &["-V"],
            &["check", "--help"],
            &["check", "-h"],
            &["fmt", "--help"],
            &["fmt", "-h"],
            &["explain", "--help"],
            &["explain", "-h"],
            &["init", "--help"],
            &["init", "-h"],
            &["targets", "--help"],
            &["targets", "-h"],
            &["targets", "--evidence"],
        ];
        for args in flags {
            let outcome = inproc(args);
            assert_eq!(outcome.code, 0, "{args:?}: {outcome:?}");
            assert_eq!(outcome.stderr, "", "{args:?}");
            assert!(!outcome.stdout.is_empty(), "{args:?}");
        }
    });
    h.case("help/the two spellings of a top-level flag agree", || {
        assert_eq!(inproc(&["--help"]), inproc(&["-h"]));
        assert_eq!(inproc(&["--version"]), inproc(&["-V"]));
        assert_eq!(inproc(&["explain", "--help"]), inproc(&["explain", "-h"]));
        assert_eq!(inproc(&["targets", "--help"]), inproc(&["targets", "-h"]));
        assert_eq!(inproc(&["check", "--help"]), inproc(&["check", "-h"]));
        assert_eq!(inproc(&["fmt", "--help"]), inproc(&["fmt", "-h"]));
        assert_eq!(inproc(&["init", "--help"]), inproc(&["init", "-h"]));
    });
    h.case(
        "help/a working command's help opens with its summary",
        || {
            for command in WORKING {
                let outcome = inproc(&[command.name, "--help"]);
                let first = outcome.stdout.lines().next().expect("a line");
                assert_eq!(first, format!("{}.", command.summary));
                assert!(
                    outcome
                        .stdout
                        .contains(&format!("Usage: enrang {}", command.name)),
                    "{}",
                    outcome.stdout
                );
            }
        },
    );
    h.case(
        "help/no line of a command's help is over 100 columns",
        || {
            for command in WORKING {
                for line in inproc(&[command.name, "--help"]).stdout.lines() {
                    assert!(line.chars().count() <= 100, "{line}");
                }
            }
        },
    );
    h.case("help/the version is the workspace's, one line", || {
        let outcome = inproc(&["--version"]);
        assert_eq!(
            outcome.stdout,
            format!(
                "enrang {} (milestone {CURRENT_MILESTONE})\n",
                env!("CARGO_PKG_VERSION")
            )
        );
    });
    h.case("help/no line of the help is over 100 columns", || {
        for line in help().lines() {
            assert!(line.chars().count() <= 100, "{line}");
        }
    });
}
