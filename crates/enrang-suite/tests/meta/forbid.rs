//! `#![forbid(unsafe_code)]` in every crate except the one exempted (ARCHITECTURE 1).

use std::fs;
use std::path::Path;

use enrang_testkit::{Harness, TempDir, workspace_root};

use crate::support::{directories, files_under};

/// The one crate exempted: a future ptrace stepper needs `unsafe`.
const EXEMPT: &str = "enrang-testkit";

/// Whether a crate root forbids unsafe code. Inner attributes come before any item,
/// so the search stops at the first line that is neither one nor a comment. That
/// also keeps out a line inside a string, and `deny`, which code can override.
pub fn forbids_unsafe(source: &str) -> bool {
    let mut in_block_comment = false;
    for raw in source.lines() {
        let line = raw.trim();
        if in_block_comment {
            in_block_comment = !line.contains("*/");
            continue;
        }
        if line.starts_with("/*") {
            in_block_comment = !line.contains("*/");
            continue;
        }
        if line.is_empty() || line.starts_with("//") {
            continue;
        }
        if !line.starts_with("#!") {
            return false;
        }
        let compact: String = line.chars().filter(|c| !c.is_whitespace()).collect();
        let Some(list) = compact
            .strip_prefix("#![forbid(")
            .and_then(|rest| rest.strip_suffix(")]"))
        else {
            continue;
        };
        if list.split(',').any(|lint| lint == "unsafe_code") {
            return true;
        }
    }
    false
}

/// The library, binary and integration test roots of the crate in `dir`, relative to
/// it. A test is a crate too: `tests/<name>.rs`, or `tests/<name>/main.rs` when it is
/// several files, whose other files are its modules.
pub fn crate_roots(dir: &Path) -> Vec<String> {
    let mut roots = Vec::new();
    for root in ["src/lib.rs", "src/main.rs"] {
        if dir.join(root).is_file() {
            roots.push(root.to_owned());
        }
    }
    for name in files_under(&dir.join("src/bin")) {
        if name.ends_with(".rs") {
            roots.push(format!("src/bin/{name}"));
        }
    }
    for name in files_under(&dir.join("tests")) {
        let is_root = match name.split_once('/') {
            None => name.ends_with(".rs"),
            Some((_, inner)) => inner == "main.rs",
        };
        if is_root {
            roots.push(format!("tests/{name}"));
        }
    }
    roots
}

/// What is wrong in a directory of crates, sorted.
pub fn forbid_problems(crates_dir: &Path) -> Vec<String> {
    let mut problems = Vec::new();
    for name in directories(crates_dir) {
        if name == EXEMPT {
            continue;
        }
        let dir = crates_dir.join(&name);
        let roots = crate_roots(&dir);
        if roots.is_empty() {
            problems.push(format!("{name} has no crate root"));
        }
        for root in roots {
            let source = fs::read_to_string(dir.join(&root)).unwrap_or_default();
            if !forbids_unsafe(&source) {
                problems.push(format!("{name}/{root} does not forbid unsafe code"));
            }
        }
    }
    problems
}

pub fn register(h: &mut Harness) {
    h.case(
        "forbid/every crate root but the exempted crate's has it",
        || {
            let problems = forbid_problems(&workspace_root().join("crates"));
            assert_eq!(problems, Vec::<String>::new());
        },
    );
    h.case(
        "forbid/the check looks at real roots of every crate",
        || {
            let crates_dir = workspace_root().join("crates");
            for name in directories(&crates_dir) {
                assert!(
                    !crate_roots(&crates_dir.join(&name)).is_empty(),
                    "{name} has no root"
                );
            }
            let cli = crate_roots(&crates_dir.join("enrang-cli"));
            assert_eq!(cli, ["src/lib.rs", "src/main.rs", "tests/cli/main.rs"]);
            let suite = crate_roots(&crates_dir.join("enrang-suite"));
            assert_eq!(
                suite,
                [
                    "src/bin/enrang-suite-cli.rs",
                    "src/bin/enrang-suite-ice.rs",
                    "tests/meta/main.rs"
                ]
            );
            let base = crate_roots(&crates_dir.join("enrang-base"));
            assert!(base.contains(&"tests/bit_set.rs".to_owned()), "{base:?}");
        },
    );
    h.case(
        "forbid/the exemption is unused until the stepper exists",
        || {
            let testkit = workspace_root().join("crates").join(EXEMPT);
            if !testkit.join("src/stepper.rs").exists() {
                for root in crate_roots(&testkit) {
                    let source = fs::read_to_string(testkit.join(&root)).expect("the root");
                    assert!(forbids_unsafe(&source), "{root}");
                }
            }
        },
    );
    let rows: &[(&str, &str, bool)] = &[
        ("the attribute", "#![forbid(unsafe_code)]\n", true),
        (
            "after docs",
            "//! Docs.\n\n#![forbid(unsafe_code)]\nfn main() {}\n",
            true,
        ),
        ("in a list", "#![forbid(dead_code, unsafe_code)]\n", true),
        ("with spaces", "#![ forbid( unsafe_code ) ]\n", true),
        (
            "after another attribute",
            "#![warn(missing_docs)]\n#![forbid(unsafe_code)]\n",
            true,
        ),
        (
            "after a block comment",
            "/* one\n two */\n#![forbid(unsafe_code)]\n",
            true,
        ),
        ("missing", "fn main() {}\n", false),
        ("empty", "", false),
        (
            "in a line comment",
            "// #![forbid(unsafe_code)]\nfn main() {}\n",
            false,
        ),
        (
            "in a doc comment",
            "//! #![forbid(unsafe_code)]\nfn main() {}\n",
            false,
        ),
        (
            "in a block comment",
            "/*\n#![forbid(unsafe_code)]\n*/\nfn main() {}\n",
            false,
        ),
        ("deny is weaker", "#![deny(unsafe_code)]\n", false),
        ("allow is the opposite", "#![allow(unsafe_code)]\n", false),
        ("another lint", "#![forbid(dead_code)]\n", false),
        (
            "an outer attribute",
            "#[forbid(unsafe_code)]\nfn main() {}\n",
            false,
        ),
        (
            "only conditional",
            "#![cfg_attr(test, forbid(unsafe_code))]\n",
            false,
        ),
        (
            "after an item",
            "fn main() {}\n#![forbid(unsafe_code)]\n",
            false,
        ),
        (
            "in a raw string",
            "const S: &str = r\"\n#![forbid(unsafe_code)]\n\";\n",
            false,
        ),
    ];
    for (name, source, expected) in rows {
        let (source, expected) = (*source, *expected);
        h.case(format!("forbid/recognises: {name}"), move || {
            assert_eq!(forbids_unsafe(source), expected, "{source:?}");
        });
    }
    h.case("forbid/a fake tree reports each crate at fault", || {
        let tree = TempDir::new("forbid");
        tree.write("good/src/lib.rs", "#![forbid(unsafe_code)]\n");
        tree.write("no-attr/src/lib.rs", "pub fn f() {}\n");
        tree.write("bin-only/src/main.rs", "fn main() {}\n");
        tree.write("mixed/src/lib.rs", "#![forbid(unsafe_code)]\n");
        tree.write("mixed/src/bin/tool.rs", "fn main() {}\n");
        tree.write("no-root/src/other.rs", "\n");
        tree.write("tested/src/lib.rs", "#![forbid(unsafe_code)]\n");
        tree.write("tested/tests/one.rs", "fn main() {}\n");
        tree.write("tested/tests/many/main.rs", "fn main() {}\n");
        tree.write("tested/tests/many/support.rs", "pub fn f() {}\n");
        tree.write("tested/tests/data/deep/main.txt", "text\n");
        tree.write(&format!("{EXEMPT}/src/lib.rs"), "pub fn f() {}\n");
        assert_eq!(
            forbid_problems(tree.path()),
            [
                "bin-only/src/main.rs does not forbid unsafe code",
                "mixed/src/bin/tool.rs does not forbid unsafe code",
                "no-attr/src/lib.rs does not forbid unsafe code",
                "no-root has no crate root",
                "tested/tests/many/main.rs does not forbid unsafe code",
                "tested/tests/one.rs does not forbid unsafe code",
            ]
        );
    });
}
