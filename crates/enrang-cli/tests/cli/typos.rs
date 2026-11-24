//! Did-you-mean, over generated typos of every name it can correct to.

use enrang_cli::{ALIASES, DEFERRED, LATER, WORKING};
use enrang_testkit::Harness;

use crate::support::inproc;

/// The one-edit typos of `name`: a letter dropped, a pair swapped, a letter doubled,
/// a letter replaced. Each row is `(what happened, the typo)`.
fn typos(name: &str) -> Vec<(String, String)> {
    let chars: Vec<char> = name.chars().collect();
    let text = |chars: &[char]| chars.iter().collect::<String>();
    let mut found = Vec::new();
    for at in 0..chars.len() {
        let mut dropped = chars.clone();
        dropped.remove(at);
        found.push((format!("drop {at}"), text(&dropped)));

        let mut doubled = chars.clone();
        doubled.insert(at, chars[at]);
        found.push((format!("double {at}"), text(&doubled)));

        let mut replaced = chars.clone();
        replaced[at] = 'z';
        found.push((format!("replace {at}"), text(&replaced)));

        if at + 1 < chars.len() && chars[at] != chars[at + 1] {
            let mut swapped = chars.clone();
            swapped.swap(at, at + 1);
            found.push((format!("swap {at}"), text(&swapped)));
        }
    }
    found
}

/// A typo that is itself a name the command line knows is no typo. Single edits of
/// the commands never produce one today, and a test below keeps that true.
fn is_known(name: &str) -> bool {
    WORKING.iter().any(|command| command.name == name)
        || LATER.iter().any(|command| command.name == name)
        || DEFERRED.contains(&name)
        || ALIASES.iter().any(|alias| alias.name == name)
}

fn command_names() -> Vec<&'static str> {
    let working = WORKING.iter().map(|command| command.name);
    working
        .chain(LATER.iter().map(|command| command.name))
        .collect()
}

pub fn register(h: &mut Harness) {
    for name in command_names() {
        for (what, typo) in typos(name) {
            h.case(format!("typo/{name}/{what}: {typo}"), move || {
                assert!(!is_known(&typo), "{typo} is a real name");
                let outcome = inproc(&[&typo]);
                assert_eq!(outcome.code, 2, "{outcome:?}");
                assert_eq!(outcome.stdout, "");
                assert_eq!(
                    outcome.stderr,
                    format!(
                        "error[EN1302]: `{typo}` is not an `enrang` command\nhelp: did you mean `enrang {name}`?\n  = explain: run `enrang explain EN1302`\n\nerror: aborting due to 1 previous error\n"
                    )
                );
            });
        }
    }
    for flag in ["--help", "--version"] {
        for (what, typo) in typos(flag) {
            if !typo.starts_with('-') {
                continue;
            }
            h.case(format!("typo/{flag}/{what}: {typo}"), move || {
                let outcome = inproc(&[&typo]);
                assert_eq!(outcome.code, 2, "{outcome:?}");
                assert!(
                    outcome
                        .stderr
                        .contains(&format!("help: did you mean `{flag}`?\n")),
                    "{}",
                    outcome.stderr
                );
            });
        }
    }
    for (name, flag, parent) in [
        ("--evidence", "--evidence", "targets"),
        ("--help", "--help", "targets"),
        ("--help", "--help", "explain"),
    ] {
        for (what, typo) in typos(name) {
            if !typo.starts_with('-') || typo == "-h" {
                continue;
            }
            h.case(format!("typo/{parent} {flag}/{what}: {typo}"), move || {
                let outcome = inproc(&[parent, &typo]);
                assert_eq!(outcome.code, 2, "{outcome:?}");
                let expected = format!(
                    "error: `{typo}` is not a flag of `enrang {parent}`\nhelp: did you mean `{flag}`?\nusage: "
                );
                assert!(outcome.stderr.starts_with(&expected), "{}", outcome.stderr);
            });
        }
    }
    let command_flags: &[(&str, &[&str])] = &[
        (
            "check",
            &[
                "--target",
                "--cpu",
                "--float",
                "--color",
                "--error-format",
                "--debug-info",
                "--multiboot",
                "--coverage",
                "--help",
            ],
        ),
        ("fmt", &["--check", "--help"]),
        ("init", &["--kernel", "--help"]),
    ];
    for (parent, flags) in command_flags {
        let (parent, flags) = (*parent, *flags);
        for flag in flags {
            let flag = *flag;
            for (what, typo) in typos(flag) {
                let known = flags.contains(&typo.as_str());
                if !typo.starts_with('-') || typo == "-" || typo == "-h" || known {
                    continue;
                }
                h.case(format!("typo/{parent} {flag}/{what}: {typo}"), move || {
                    let outcome = inproc(&[parent, &typo]);
                    assert_eq!(outcome.code, 2, "{outcome:?}");
                    let expected = format!(
                        "error: `{typo}` is not a flag of `enrang {parent}`\nhelp: did you mean `{flag}`?\nusage: enrang {parent} "
                    );
                    assert!(outcome.stderr.starts_with(&expected), "{}", outcome.stderr);
                });
            }
        }
    }
    h.case(
        "typo/a deferred or alias name is not a correction target",
        || {
            for name in DEFERRED
                .iter()
                .copied()
                .chain(ALIASES.iter().map(|a| a.name))
            {
                let typo = format!("{name}{name}");
                let stderr = inproc(&[&typo]).stderr;
                assert!(
                    !stderr.contains(&format!("did you mean `enrang {name}`")),
                    "{stderr}"
                );
            }
        },
    );
    h.case(
        "typo/a name that is far from all gets the way to the list",
        || {
            for name in ["frobnicate", "xyzzy", "kubernetes", "q"] {
                let stderr = inproc(&[name]).stderr;
                assert!(
                    stderr.contains("help: run `enrang --help` to see the commands\n"),
                    "{name}: {stderr}"
                );
                assert!(!stderr.contains("did you mean"), "{name}: {stderr}");
            }
        },
    );
    h.case(
        "typo/a flag far from all is a usage message with no code",
        || {
            for flag in ["--bogus", "-x"] {
                assert_eq!(
                    inproc(&[flag]).stderr,
                    format!(
                        "error: `{flag}` is not a flag of `enrang`\nusage: enrang <command> [arguments]\n"
                    )
                );
            }
        },
    );
    h.case(
        "typo/a flag is never corrected to a command, nor a word to a flag",
        || {
            for (typed, wrong) in [
                ("--buil", "enrang build"),
                ("help", "--help"),
                ("version", "--version"),
            ] {
                let stderr = inproc(&[typed]).stderr;
                assert!(!stderr.contains(&format!("`{wrong}`")), "{typed}: {stderr}");
            }
        },
    );
    h.case("typo/an unknown name is echoed safely", || {
        for (typed, shown) in [
            ("a\x1b[2Jb", "a\\u{1b}[2Jb"),
            ("\x07", "\\u{7}"),
            ("a\nb", "a\\nb"),
            ("a\tb", "a\\tb"),
            ("\u{9b}", "\\u{9b}"),
            ("\u{202e}evil", "\\u{202e}evil"),
            ("a\u{2066}b", "a\\u{2066}b"),
            ("a\u{2028}b", "a\\u{2028}b"),
            ("a\u{2029}b", "a\\u{2029}b"),
        ] {
            let stderr = inproc(&[typed]).stderr;
            assert!(
                stderr.starts_with(&format!(
                    "error[EN1302]: `{shown}` is not an `enrang` command\n"
                )),
                "{typed:?}: {stderr:?}"
            );
            let before_explain = stderr.lines().take(2).collect::<String>();
            assert!(!before_explain.chars().any(char::is_control), "{stderr:?}");
        }
    });
    h.case("typo/a huge name is handled and echoed whole", || {
        let huge = "x".repeat(100_000);
        let outcome = inproc(&[&huge]);
        assert_eq!(outcome.code, 2);
        assert!(outcome.stderr.contains(&huge));
    });
    h.case("typo/typos reach every position of a name", || {
        let found = typos("run");
        let names: Vec<&str> = found.iter().map(|(_, typo)| typo.as_str()).collect();
        for expected in [
            "un", "rn", "ru", "rrun", "ruun", "runn", "zun", "rzn", "ruz", "urn", "rnu",
        ] {
            assert!(names.contains(&expected), "{expected} in {names:?}");
        }
    });
}
