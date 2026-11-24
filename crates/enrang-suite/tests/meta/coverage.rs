//! Each CLI command, flag and message has a golden (TESTING 18).

use std::collections::BTreeSet;
use std::fs;

use enrang_cli::{ALIASES, DEFERRED, LATER, WORKING};
use enrang_testkit::{Harness, workspace_root};

use crate::support::{
    Golden, PROJECT_TRANSCRIPTS, files_under, golden_args, goldens_in, transcripts,
};

/// Every flag the command line accepts, each with the arguments that show it. The
/// `flags in the source` case below keeps this list complete.
const FLAGS: &[(&str, &[&str])] = &[
    ("--help", &["--help"]),
    ("-h", &["-h"]),
    ("--version", &["--version"]),
    ("-V", &["-V"]),
    ("explain --help", &["explain", "--help"]),
    ("explain -h", &["explain", "-h"]),
    ("targets --help", &["targets", "--help"]),
    ("targets -h", &["targets", "-h"]),
    ("targets --evidence", &["targets", "--evidence"]),
    ("check --help", &["check", "--help"]),
    ("check -h", &["check", "-h"]),
    ("check --target", &["check", "--target=bogus", "main.en"]),
    ("check --cpu", &["check", "--cpu=native", "main.en"]),
    ("check --float", &["check", "--float=quad", "main.en"]),
    ("check --color", &["check", "--color=never", "g01.en"]),
    (
        "check --error-format",
        &["check", "--error-format=json", "g01.en"],
    ),
    (
        "check --debug-info",
        &["check", "--debug-info=dwarf", "main.en"],
    ),
    ("check --multiboot", &["check", "--multiboot", "main.en"]),
    ("check --coverage", &["check", "--coverage", "main.en"]),
    ("check --library", &["check", "--library", "lib.en"]),
    ("check --emit", &["check", "--emit=mir", "main.en"]),
    ("fmt --help", &["fmt", "--help"]),
    ("fmt -h", &["fmt", "-h"]),
    ("fmt --check", &["fmt", "--check"]),
    ("init --help", &["init", "--help"]),
    ("init -h", &["init", "-h"]),
    ("init --kernel", &["init", "--kernel"]),
];

/// The transcripts of `cli` and of `cli-project`. A flag or message shown in
/// `cli-project` has a golden as much as one shown in `cli`, though those need files
/// or standard input that only the CLI suite sets up.
fn every_transcript() -> Vec<Golden> {
    let mut goldens = transcripts();
    goldens.extend(goldens_in(PROJECT_TRANSCRIPTS));
    goldens
}

/// The golden with exactly these arguments, by name.
fn golden_with(goldens: &[Golden], wanted: &[&str]) -> Option<String> {
    goldens
        .iter()
        .find(|golden| {
            golden_args(golden).is_ok_and(|args| {
                args.len() == wanted.len() && args.iter().zip(wanted).all(|(a, b)| a == b)
            })
        })
        .map(|golden| golden.name.clone())
}

/// The string literals of Rust source that are not the message of an `.expect`, with
/// their escapes decoded. A panic message reaches a user only through the report of
/// an internal error, which has its own golden, and what follows `#[cfg(test)]` is
/// no message at all.
pub fn messages_in_source(source: &str) -> Vec<String> {
    let mut messages = Vec::new();
    let source = source.split("#[cfg(test)]").next().unwrap_or(source);
    let bytes = source.as_bytes();
    let mut at = 0;
    while at < bytes.len() {
        match bytes[at] {
            b'/' if bytes.get(at + 1) == Some(&b'/') => {
                while at < bytes.len() && bytes[at] != b'\n' {
                    at += 1;
                }
            }
            b'\'' => {
                // A character literal, or a lifetime, which ends at the next word.
                if bytes.get(at + 1) == Some(&b'\\') {
                    at += 2;
                    while at < bytes.len() && bytes[at] != b'\'' {
                        at += 1;
                    }
                    at += 1;
                } else if bytes.get(at + 2) == Some(&b'\'') {
                    at += 3;
                } else {
                    at += 1;
                }
            }
            b'"' => {
                let start = at;
                at += 1;
                let mut text = Vec::new();
                while at < bytes.len() && bytes[at] != b'"' {
                    if bytes[at] == b'\\' {
                        at += 1;
                        match bytes.get(at) {
                            Some(b'n') => text.push(b'\n'),
                            Some(b't') => text.push(b'\t'),
                            Some(b'\n') => {
                                while bytes.get(at + 1).is_some_and(u8::is_ascii_whitespace) {
                                    at += 1;
                                }
                            }
                            Some(&other) => text.push(other),
                            None => {}
                        }
                    } else {
                        text.push(bytes[at]);
                    }
                    at += 1;
                }
                at += 1;
                let before = source[..start].trim_end();
                if !before.ends_with(".expect(") {
                    messages.push(String::from_utf8_lossy(&text).into_owned());
                }
            }
            _ => at += 1,
        }
    }
    messages
}

/// The pieces of a message that its placeholders leave fixed, one per line. Pieces
/// with no space are names and flags, which the command and flag gates cover.
pub fn fixed_pieces(message: &str) -> Vec<String> {
    let mut pieces = Vec::new();
    for line in message.lines() {
        let mut rest = line;
        loop {
            let (piece, tail) = match rest.split_once('{') {
                Some((piece, tail)) => (piece, Some(tail)),
                None => (rest, None),
            };
            let piece = piece.trim();
            if piece.contains(' ') && piece.chars().filter(char::is_ascii_alphabetic).count() >= 4 {
                pieces.push(piece.to_owned());
            }
            match tail {
                Some(tail) => rest = tail.split_once('}').map_or("", |(_, after)| after),
                None => break,
            }
        }
    }
    pieces
}

/// The flags a source compares against or suggests: its literals that are one word
/// starting with a dash.
pub fn flags_in_source(source: &str) -> BTreeSet<String> {
    messages_in_source(source)
        .into_iter()
        .filter(|literal| {
            literal.len() > 1 && literal.starts_with('-') && !literal.contains(char::is_whitespace)
        })
        .collect()
}

/// The pieces of `sources` that no text of `corpus` shows, sorted.
pub fn unshown_pieces(sources: &[(String, String)], corpus: &str) -> Vec<String> {
    let mut missing = BTreeSet::new();
    for (file, source) in sources {
        for message in messages_in_source(source) {
            for piece in fixed_pieces(&message) {
                if !corpus.contains(&piece) {
                    missing.insert(format!("{file}: {piece}"));
                }
            }
        }
    }
    missing.into_iter().collect()
}

pub fn register(h: &mut Harness) {
    for command in WORKING {
        let name = command.name;
        h.case(
            format!("coverage/the command {name} has a golden"),
            move || {
                let goldens = transcripts();
                let any = goldens.iter().any(|golden| {
                    golden_args(golden).is_ok_and(|args| args.first().is_some_and(|a| a == name))
                });
                assert!(any, "no golden runs `enrang {name}`");
            },
        );
    }
    let bare = LATER
        .iter()
        .map(|command| command.name)
        .chain(DEFERRED.iter().copied())
        .chain(ALIASES.iter().map(|alias| alias.name));
    for name in bare {
        h.case(
            format!("coverage/the command {name} has a golden"),
            move || {
                let name_golden = golden_with(&transcripts(), &[name]);
                assert!(name_golden.is_some(), "no golden runs `enrang {name}`");
            },
        );
    }
    for (flag, args) in FLAGS {
        let (flag, args) = (*flag, *args);
        h.case(
            format!("coverage/the flag {flag} has a golden"),
            move || {
                assert!(golden_with(&every_transcript(), args).is_some(), "{args:?}");
            },
        );
    }
    h.case(
        "coverage/the flags in the source are exactly the flag table's",
        || {
            let root = workspace_root().join("crates/enrang-cli/src");
            let mut found = BTreeSet::new();
            for name in files_under(&root) {
                let source = fs::read_to_string(root.join(name)).expect("a source file");
                found.extend(flags_in_source(&source));
            }
            let listed: BTreeSet<String> = FLAGS
                .iter()
                .map(|(flag, _)| flag.rsplit(' ').next().expect("a word").to_owned())
                .collect();
            assert_eq!(found, listed);
        },
    );
    h.case("coverage/the flag scan sees a new flag", || {
        let source = r#"match arg { "--secret" | "-s" => 1, "-" => 2, "a b" => 3, "--a b" => 4 }"#;
        let found: Vec<String> = flags_in_source(source).into_iter().collect();
        assert_eq!(found, ["--secret", "-s"]);
    });
    h.case("coverage/every kind of output has its golden", || {
        let goldens = transcripts();
        let rows: &[&[&str]] = &[
            &["--help"],
            &["--version"],
            &[],
            &["explain", "EN1301"],
            &["explain", "EN1302"],
            &["explain", "EN0414"],
            &["explain", "EN9999"],
            &["explain", "EN0704"],
            &["explain"],
            &["targets"],
            &["targets", "--evidence"],
            &["frobnicate"],
            &["buidl"],
            &["--hepl"],
        ];
        for args in rows {
            assert!(golden_with(&goldens, args).is_some(), "{args:?}");
        }
    });
    h.case(
        "coverage/every message in the command line's source is in a golden",
        || {
            let root = workspace_root();
            let source_dir = root.join("crates/enrang-cli/src");
            let sources: Vec<(String, String)> = files_under(&source_dir)
                .into_iter()
                .map(|name| {
                    let text = fs::read_to_string(source_dir.join(&name)).expect("a source file");
                    (name, text)
                })
                .collect();
            assert!(sources.len() >= 2, "no sources found");
            let mut corpus = String::new();
            for dir in [
                "tests/golden/cli",
                "tests/golden/cli-inprocess",
                PROJECT_TRANSCRIPTS,
            ] {
                let golden_dir = root.join(dir);
                for name in files_under(&golden_dir) {
                    corpus.push_str(&fs::read_to_string(golden_dir.join(name)).expect("UTF-8"));
                }
            }
            assert_eq!(unshown_pieces(&sources, &corpus), Vec::<String>::new());
        },
    );
    h.case(
        "coverage/the message check reports a message no golden shows",
        || {
            let sources = vec![(
                "fake.rs".to_owned(),
                r#"
            // "a comment is no message at all"
            fn f() {
                complaint("a message every golden shows", None);
                complaint(&format!("`{name}` is a brand new message"), None);
                let bad = "an unshown message here";
                x.expect("a panic is exempt from this");
                let c = '"'; let d = '\n'; let e: &'static str = "quoted \"text\" here";
            }
            #[cfg(test)]
            mod tests {
                const CELL: &str = "only a test says this";
            }
            "#
                .to_owned(),
            )];
            let corpus = "a message every golden shows\nquoted \"text\" here\n";
            assert_eq!(
                unshown_pieces(&sources, corpus),
                [
                    "fake.rs: ` is a brand new message",
                    "fake.rs: an unshown message here",
                ]
            );
        },
    );
    h.case(
        "coverage/the message check sees the source's real messages",
        || {
            let source =
                fs::read_to_string(workspace_root().join("crates/enrang-cli/src/report.rs"))
                    .expect("the source");
            let messages = messages_in_source(&source);
            assert!(messages.iter().any(|m| m.contains(", so nothing was done")));
            assert!(
                messages
                    .iter()
                    .any(|m| m.contains("is not part of the prototype"))
            );
        },
    );
    let piece_rows: &[(&str, &[&str])] = &[
        ("plain text here", &["plain text here"]),
        ("`{name}` is not it", &["` is not it"]),
        ("{a}", &[]),
        ("--evidence", &[]),
        ("one\ntwo words", &["two words"]),
        ("a {x} b", &[]),
        (
            "long piece of text {x} and another long piece",
            &["long piece of text", "and another long piece"],
        ),
        ("{a:<width$}  ", &[]),
    ];
    for (message, expected) in piece_rows {
        let (message, expected) = (*message, *expected);
        h.case(format!("coverage/fixed pieces of {message:?}"), move || {
            assert_eq!(fixed_pieces(message), expected);
        });
    }
}
