//! What follows a command that cannot run changes nothing, and it never acts.

use enrang_cli::{ALIASES, DEFERRED, LATER, WORKING};
use enrang_diag::CURRENT_MILESTONE;
use enrang_testkit::{Harness, TempDir};

use crate::support::{enrang_in, inproc, strings};

/// Arguments a user might give. Each could trigger a different path in a command
/// that really parsed them, and none may here.
const ARGUMENT_VARIANTS: &[&[&str]] = &[
    &["main.en"],
    &["--help"],
    &["-h"],
    &["--version"],
    &["--target=i386-none"],
    &["--color=always"],
    &["--error-format=json"],
    &["a", "b", "c"],
    &["--", "x"],
    &[""],
];

fn every_stopped_name() -> Vec<&'static str> {
    let later = LATER.iter().map(|command| command.name);
    let aliases = ALIASES.iter().map(|alias| alias.name);
    later
        .chain(DEFERRED.iter().copied())
        .chain(aliases)
        .chain(["frobnicate"])
        .collect()
}

fn directory_entries(directory: &TempDir) -> Vec<String> {
    let entries = std::fs::read_dir(directory.path()).expect("the directory exists");
    entries
        .map(|entry| {
            entry
                .expect("an entry")
                .file_name()
                .to_string_lossy()
                .into_owned()
        })
        .collect()
}

pub fn register(h: &mut Harness) {
    for name in every_stopped_name() {
        for (index, variant) in ARGUMENT_VARIANTS.iter().enumerate() {
            h.case(
                format!("arguments/{name} ignores variant {index}: {variant:?}"),
                move || {
                    let mut args = vec![name];
                    args.extend_from_slice(variant);
                    let with = inproc(&args);
                    let without = inproc(&[name]);
                    assert_eq!(with, without);
                    assert_eq!(with.code, 2);
                    assert_eq!(with.stdout, "");
                    let is_later = LATER.iter().any(|command| command.name == name);
                    let head = if is_later {
                        "error: `enrang "
                    } else {
                        "error[EN130"
                    };
                    assert!(with.stderr.starts_with(head), "{}", with.stderr);
                },
            );
        }
        h.case(
            format!("arguments/{name} leaves the directory untouched"),
            move || {
                let directory = TempDir::new("untouched");
                let ran = enrang_in(directory.path(), &strings(&[name, "main.en"]));
                assert_eq!(ran.code, 2, "{ran:?}");
                assert_eq!(directory_entries(&directory), Vec::<String>::new());
            },
        );
        h.case(
            format!("arguments/{name} leaves the project untouched"),
            move || {
                let directory = TempDir::new("project");
                let source = "function main(): void {}\n";
                let main = directory.write("main.en", source);
                let manifest = directory.write("enrang.json", "{\"name\":\"hello\"}\n");
                let ran = enrang_in(directory.path(), &strings(&[name, "main.en"]));
                assert_eq!(ran.code, 2, "{ran:?}");
                let mut entries = directory_entries(&directory);
                entries.sort();
                assert_eq!(entries, ["enrang.json", "main.en"]);
                assert_eq!(std::fs::read_to_string(main).expect("kept"), source);
                let kept = std::fs::read_to_string(manifest).expect("kept");
                assert_eq!(kept, "{\"name\":\"hello\"}\n");
            },
        );
    }

    for command in LATER {
        let name = command.name;
        let since = command.since;
        h.case(
            format!("later/{name} names its milestone in the head"),
            move || {
                let outcome = inproc(&[name]);
                let head = outcome.stderr.lines().next().expect("a head");
                assert_eq!(
                    head,
                    format!("error: `enrang {name}` arrives with milestone {since}")
                );
                assert!(
                    outcome.stderr.ends_with(&format!(
                        "note: this is milestone {CURRENT_MILESTONE}, so nothing was done\n"
                    )),
                    "{}",
                    outcome.stderr
                );
            },
        );
        // SPEC 13.2 and 16 give EN1301 to nine other commands, and the page it would
        // point to says nothing of these.
        h.case(format!("later/{name} reports no code"), move || {
            let stderr = inproc(&[name]).stderr;
            assert!(!stderr.contains("EN13"), "{stderr}");
            assert!(!stderr.contains("= explain"), "{stderr}");
            assert!(!stderr.contains("aborting"), "{stderr}");
        });
        let delivers = command.delivers;
        h.case(format!("later/{name} says what arrives when"), move || {
            let stderr = inproc(&[name]).stderr;
            assert!(stderr.contains(&format!("note: {delivers}\n")), "{stderr}");
            assert!(delivers.starts_with(&since.to_string()), "{delivers}");
        });
    }
    h.case(
        "working/the commands and milestones are those of ARCHITECTURE 11, by hand",
        || {
            let expected: &[(&str, &str)] = &[
                ("check", "M1"),
                ("fmt", "M1"),
                ("explain", "M0"),
                ("init", "M1"),
                ("targets", "M0"),
            ];
            let found: Vec<(&str, String)> = WORKING
                .iter()
                .map(|command| (command.name, command.since.to_string()))
                .collect();
            let wanted: Vec<(&str, String)> = expected
                .iter()
                .map(|(name, since)| (*name, (*since).to_owned()))
                .collect();
            assert_eq!(found, wanted);
        },
    );
    h.case(
        "later/the milestones are those of ARCHITECTURE 11, by hand",
        || {
            let expected: &[(&str, &str)] = &[
                ("build", "M5"),
                ("run", "M4"),
                ("dev", "M6"),
                ("test", "M4"),
            ];
            assert_eq!(LATER.len(), expected.len());
            for ((name, milestone), command) in expected.iter().zip(LATER) {
                assert_eq!(command.name, *name);
                assert_eq!(command.since.to_string(), *milestone, "{name}");
            }
        },
    );

    for &name in DEFERRED {
        h.case(format!("deferred/{name} is the transcript's shape"), move || {
            let outcome = inproc(&[name]);
            assert_eq!(outcome.code, 2);
            assert_eq!(
                outcome.stderr,
                format!(
                    "error[EN1301]: `enrang {name}` is not part of the prototype\n  = explain: run `enrang explain EN1301`\n\nerror: aborting due to 1 previous error\n"
                )
            );
        });
    }
    h.case(
        "deferred/exactly the nine commands of SPEC 16, by hand",
        || {
            assert_eq!(
                DEFERRED,
                [
                    "install", "add", "publish", "doc", "lsp", "repl", "bench", "debug", "upgrade",
                ]
            );
        },
    );

    let alias_helps: &[(&str, &str)] = &[
        ("tsc", "the command for this is `enrang check`"),
        ("lint", "the command for this is `enrang check`"),
        (
            "compile",
            "the command for this is `enrang build`, which arrives with milestone M5",
        ),
        (
            "start",
            "the command for this is `enrang run`, which arrives with milestone M4",
        ),
    ];
    for (name, help) in alias_helps {
        let (name, help) = (*name, *help);
        h.case(format!("alias/{name} is the transcript's shape"), move || {
            let outcome = inproc(&[name]);
            assert_eq!(outcome.code, 2);
            assert_eq!(
                outcome.stderr,
                format!(
                    "error[EN1302]: `{name}` is not an `enrang` command\nhelp: {help}\n  = explain: run `enrang explain EN1302`\n\nerror: aborting due to 1 previous error\n"
                )
            );
        });
    }
    h.case("alias/the four pairs of SPEC 13.2, by hand", || {
        let pairs: Vec<(&str, &str)> = ALIASES.iter().map(|a| (a.name, a.target)).collect();
        assert_eq!(
            pairs,
            [
                ("tsc", "check"),
                ("lint", "check"),
                ("compile", "build"),
                ("start", "run")
            ]
        );
    });
    h.case("alias/each one points at a command that exists", || {
        for alias in ALIASES {
            assert!(
                LATER.iter().any(|command| command.name == alias.target)
                    || WORKING.iter().any(|command| command.name == alias.target),
                "{}",
                alias.name
            );
        }
    });
    h.case("names/no name is in two tables", || {
        let mut names: Vec<&str> = WORKING.iter().map(|command| command.name).collect();
        names.extend(LATER.iter().map(|command| command.name));
        names.extend(DEFERRED.iter().copied());
        names.extend(ALIASES.iter().map(|alias| alias.name));
        let total = names.len();
        names.sort_unstable();
        names.dedup();
        assert_eq!(names.len(), total);
        assert_eq!(total, 5 + 4 + 9 + 4);
    });
    let usage_errors: &[&[&str]] = &[
        &["check", "--bogus"],
        &["check", "a.en", "b.en"],
        &["check", "--target"],
        &["check", "--cpu=i386", "--cpu=i386"],
        &["check", "--help", "main.en"],
        &["fmt", "--bogus", "main.en"],
        &["fmt", "-", "main.en"],
        &["fmt", "--check", "--check", "main.en"],
        &["init", "a", "b"],
        &["init", ""],
        &["init", "--bogus"],
        &["init", "hello", "--kernel"],
        &["init", "--kernel"],
    ];
    for args in usage_errors {
        let args = *args;
        h.case(
            format!("arguments/{args:?} is a usage message that touches nothing"),
            move || {
                let directory = TempDir::new("usage");
                let main = directory.write("main.en", "const   x=1;\n");
                let ran = enrang_in(directory.path(), &strings(args));
                assert_eq!(ran.code, 2, "{ran:?}");
                assert_eq!(ran.stdout, "");
                assert!(ran.stderr.starts_with("error: "), "{}", ran.stderr);
                assert!(!ran.stderr.contains("error["), "{}", ran.stderr);
                assert_eq!(directory_entries(&directory), ["main.en"]);
                assert_eq!(
                    std::fs::read_to_string(main).expect("kept"),
                    "const   x=1;\n"
                );
            },
        );
    }
    h.case("names/commands are case sensitive", || {
        for name in ["BUILD", "Explain", "TARGETS", "FMT", "TSC"] {
            let outcome = inproc(&[name]);
            assert_eq!(outcome.code, 2, "{name}");
            let expected = format!("error[EN1302]: `{name}` is not an `enrang` command");
            assert_eq!(outcome.stderr.lines().next(), Some(expected.as_str()));
        }
    });
    h.case("names/a command is only ever the first argument", || {
        for (args, expected) in [
            (&["x", "explain"][..], "`x` is not an `enrang` command"),
            (&["x", "--help"][..], "`x` is not an `enrang` command"),
            (
                &["--bogus", "--help"][..],
                "`--bogus` is not a flag of `enrang`",
            ),
        ] {
            let outcome = inproc(args);
            assert_eq!(outcome.code, 2, "{args:?}");
            assert!(
                outcome.stderr.contains(expected),
                "{args:?}: {}",
                outcome.stderr
            );
        }
    });
}
