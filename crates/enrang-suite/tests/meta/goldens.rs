//! Goldens as a whole (TESTING 17): orphans fail, each directory has one owner, and
//! nothing in them can vary from one machine or one run to the next.

use std::fs;
use std::path::Path;
use std::sync::Arc;

use enrang_testkit::{BlessMode, GoldenStore, Harness, RunOptions, TempDir, workspace_root};

use crate::support::{TRANSCRIPTS, directories, files_under, transcripts};

/// Runs a harness over a store, one case using each of `used`, and returns the
/// orphans it reported and whether the run passed.
fn run_over(
    store: Arc<GoldenStore>,
    suite: &'static str,
    used: Vec<(String, String)>,
) -> (Vec<String>, bool) {
    let mut harness = Harness::new("orphans");
    harness.goldens_in(Arc::clone(&store), suite);
    harness.case("uses the goldens", move || -> Result<(), String> {
        for (name, text) in used {
            store
                .check(suite, &name, &text)
                .map_err(|e| e.to_string())?;
        }
        Ok(())
    });
    let mut output = Vec::new();
    let report = harness.run_with(&RunOptions::default(), &mut output);
    let printed = String::from_utf8(output).expect("UTF-8");
    for orphan in &report.orphans {
        assert!(
            printed.contains(&format!("FAILED orphaned golden: {orphan}")),
            "{printed}"
        );
    }
    (report.orphans.clone(), report.success())
}

/// Whether a golden holds what TESTING 17 keeps out: an absolute path, a date or
/// time, or a memory address.
pub fn varying_content(text: &str) -> Vec<String> {
    let mut found = Vec::new();
    for needle in [
        "/home/", "/tmp/", "/mnt/", "/usr/", "/root/", "C:\\", "\\\\?\\",
    ] {
        if text.contains(needle) {
            found.push(format!("the absolute path {needle}"));
        }
    }
    let bytes = text.as_bytes();
    for window in bytes.windows(10) {
        let digits = |range: std::ops::Range<usize>| window[range].iter().all(u8::is_ascii_digit);
        if digits(0..4) && window[4] == b'-' && digits(5..7) && window[7] == b'-' && digits(8..10) {
            found.push("a date".to_owned());
            break;
        }
    }
    for window in bytes.windows(8) {
        let digits = |range: std::ops::Range<usize>| window[range].iter().all(u8::is_ascii_digit);
        if digits(0..2) && window[2] == b':' && digits(3..5) && window[5] == b':' && digits(6..8) {
            found.push("a time".to_owned());
            break;
        }
    }
    if text
        .split(|c: char| !c.is_ascii_alphanumeric())
        .any(|word| {
            word.len() >= 10
                && word.starts_with("0x")
                && word[2..].bytes().all(|b| b.is_ascii_hexdigit())
        })
    {
        found.push("a memory address".to_owned());
    }
    found
}

/// The golden directories some test binary registers with `.goldens("name")`.
fn registered_directories(root: &Path) -> Vec<String> {
    let mut names = Vec::new();
    for krate in directories(&root.join("crates")) {
        for file in files_under(&root.join("crates").join(&krate).join("tests")) {
            if !file.ends_with(".rs") {
                continue;
            }
            let path = root.join("crates").join(&krate).join("tests").join(&file);
            let source = fs::read_to_string(path).expect("a source file");
            for (at, _) in source.match_indices(".goldens(") {
                let rest = &source[at + ".goldens(".len()..];
                let argument = rest.split(')').next().unwrap_or("");
                if let Some(name) = argument.strip_prefix('"').and_then(|a| a.strip_suffix('"')) {
                    names.push(name.to_owned());
                } else {
                    names.push(constant_value(&source, root, &krate, argument));
                }
            }
        }
    }
    names.sort();
    names.dedup();
    names
}

/// A golden suite named through a constant, as `support::SUITE`: its `const` in the
/// test directory's `support.rs`, or an empty name the owner check will not match.
fn constant_value(source: &str, root: &Path, krate: &str, argument: &str) -> String {
    let constant = argument.rsplit("::").next().unwrap_or(argument);
    let support = root.join("crates").join(krate).join("tests");
    let mut texts = vec![source.to_owned()];
    for file in files_under(&support) {
        if file.ends_with("support.rs") {
            texts.push(fs::read_to_string(support.join(file)).expect("a source file"));
        }
    }
    let head = format!("pub const {constant}: &str = \"");
    for text in texts {
        if let Some(rest) = text.split(&head).nth(1) {
            return rest.split('"').next().unwrap_or("").to_owned();
        }
    }
    String::new()
}

pub fn register(h: &mut Harness) {
    h.case("orphans/an unused golden fails the run", || {
        let dir = TempDir::new("orphan");
        dir.write("demo/used.txt", "text\n");
        dir.write("demo/nested/unused.txt", "text\n");
        let store = Arc::new(GoldenStore::new(dir.path(), BlessMode::Check));
        let used = vec![("used.txt".to_owned(), "text\n".to_owned())];
        let (orphans, success) = run_over(store, "demo", used);
        assert_eq!(orphans, ["tests/golden/demo/nested/unused.txt"]);
        assert!(!success);
    });
    h.case("orphans/with every golden used the run passes", || {
        let dir = TempDir::new("orphan");
        dir.write("demo/used.txt", "text\n");
        let store = Arc::new(GoldenStore::new(dir.path(), BlessMode::Check));
        let used = vec![("used.txt".to_owned(), "text\n".to_owned())];
        let (orphans, success) = run_over(store, "demo", used);
        assert_eq!(orphans, Vec::<String>::new());
        assert!(success);
    });
    h.case(
        "orphans/one file added to the real goldens is caught",
        || {
            let dir = TempDir::new("orphan");
            let goldens = transcripts();
            let mut used = Vec::new();
            for golden in &goldens {
                dir.write(&format!("cli/{}", golden.name), &golden.text);
                used.push((golden.name.clone(), golden.text.clone()));
            }
            let store = Arc::new(GoldenStore::new(dir.path(), BlessMode::Check));
            let (orphans, success) = run_over(Arc::clone(&store), "cli", used.clone());
            assert_eq!(orphans, Vec::<String>::new());
            assert!(success);

            dir.write("cli/later/stale_command.txt", "$ enrang gone\n");
            let store = Arc::new(GoldenStore::new(dir.path(), BlessMode::Check));
            let (orphans, success) = run_over(store, "cli", used);
            assert_eq!(orphans, ["tests/golden/cli/later/stale_command.txt"]);
            assert!(!success);
        },
    );
    h.case(
        "orphans/a failing golden hides no orphan check silently",
        || {
            let dir = TempDir::new("orphan");
            dir.write("demo/used.txt", "text\n");
            let store = Arc::new(GoldenStore::new(dir.path(), BlessMode::Check));
            let used = vec![("used.txt".to_owned(), "different\n".to_owned())];
            let (_, success) = run_over(store, "demo", used);
            assert!(!success);
        },
    );
    h.case(
        "owners/every golden directory is registered by a test binary",
        || {
            let root = workspace_root();
            let registered = registered_directories(&root);
            for name in directories(&root.join("tests/golden")) {
                assert!(
                    registered.contains(&name),
                    "{name} has no owner in {registered:?}"
                );
            }
        },
    );
    h.case(
        "owners/the command line's two directories are found",
        || {
            let registered = registered_directories(&workspace_root());
            for name in ["cli", "cli-inprocess", "testkit"] {
                assert!(
                    registered.contains(&name.to_owned()),
                    "{name} in {registered:?}"
                );
            }
        },
    );
    h.case("content/there are at least 60 transcripts", || {
        let count = transcripts().len();
        assert!(count >= 60, "only {count}");
    });
    h.case(
        "content/every transcript has the four parts in order",
        || {
            for golden in transcripts() {
                let mut lines = golden.text.lines();
                let first = lines.next().unwrap_or("");
                assert!(first.starts_with("$ enrang"), "{}: {first}", golden.name);
                let second = lines.next().unwrap_or("");
                assert!(
                    second.starts_with("[exit ") && second.ends_with(']'),
                    "{}: {second}",
                    golden.name
                );
                assert_eq!(lines.next(), Some("[stdout]"), "{}", golden.name);
                assert!(golden.text.contains("\n[stderr]\n"), "{}", golden.name);
            }
        },
    );
    h.case("content/every golden is clean text", || {
        let root = workspace_root().join("tests/golden");
        for name in files_under(&root) {
            let text = fs::read_to_string(root.join(&name)).expect("UTF-8");
            assert!(!text.contains('\r'), "{name} has a carriage return");
            assert!(!text.contains('\x1b'), "{name} has a raw escape");
        }
    });
    h.case(
        "content/no command line golden varies with the machine",
        || {
            for dir in [TRANSCRIPTS, "tests/golden/cli-inprocess"] {
                let root = workspace_root().join(dir);
                for name in files_under(&root) {
                    let text = fs::read_to_string(root.join(&name)).expect("UTF-8");
                    assert_eq!(varying_content(&text), Vec::<String>::new(), "{dir}/{name}");
                }
            }
        },
    );
    let rows: &[(&str, &str, &[&str])] = &[
        ("clean", "error[EN1301]: `enrang fmt`\nM0\n", &[]),
        (
            "a relative path",
            "see docs/SPEC.md and crates/x/y.rs\n",
            &[],
        ),
        ("a port", "0x3F8 and 0xB8000\n", &[]),
        (
            "a home path",
            "at /home/enrico/x\n",
            &["the absolute path /home/"],
        ),
        ("a temp path", "in /tmp/x\n", &["the absolute path /tmp/"]),
        (
            "a windows mount",
            "in /mnt/c/x\n",
            &["the absolute path /mnt/"],
        ),
        (
            "a windows path",
            "in C:\\Users\n",
            &["the absolute path C:\\"],
        ),
        ("a date", "built 2026-11-06\n", &["a date"]),
        ("a time", "at 12:34:56\n", &["a time"]),
        ("an address", "at 0x7ffd1234abcd\n", &["a memory address"]),
    ];
    for (name, text, expected) in rows {
        let (text, expected) = (*text, *expected);
        h.case(format!("content/varying content: {name}"), move || {
            assert_eq!(varying_content(text), expected);
        });
    }
}
