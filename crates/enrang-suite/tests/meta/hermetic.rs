//! Hermeticity (TESTING 18): nothing outside this repository goes into a build.

use std::collections::BTreeSet;

use enrang_testkit::Harness;

use crate::support::{crates, read};

/// `.gitignore` lines that would also match deeper in the tree. An unanchored
/// `target/` silently drops `crates/enrang-target/tests/target/` from every commit.
pub fn unanchored_ignores(gitignore: &str) -> Vec<String> {
    gitignore
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .filter(|line| !line.starts_with('/'))
        .map(str::to_owned)
        .collect()
}

/// Packages in a `Cargo.lock`: `(name, whether it has a source or a checksum)`.
fn lock_packages(lock: &str) -> Vec<(String, bool)> {
    let mut packages = Vec::new();
    for block in lock.split("[[package]]").skip(1) {
        let name = block
            .lines()
            .find_map(|line| line.strip_prefix("name = \""))
            .and_then(|rest| rest.strip_suffix('"'))
            .unwrap_or("")
            .to_owned();
        let external = block
            .lines()
            .any(|line| line.starts_with("source = ") || line.starts_with("checksum = "));
        packages.push((name, external));
    }
    packages
}

/// What is wrong with a `Cargo.lock`, given the workspace's crates.
pub fn lock_problems(lock: &str, workspace: &BTreeSet<String>) -> Vec<String> {
    let packages = lock_packages(lock);
    if packages.is_empty() {
        return vec!["the lock file lists no package".to_owned()];
    }
    let mut problems = Vec::new();
    for (name, external) in &packages {
        if !workspace.contains(name) {
            problems.push(format!("`{name}` is not a workspace crate"));
        }
        if *external {
            problems.push(format!("`{name}` comes from outside the repository"));
        }
    }
    for block in lock.split("[[package]]").skip(1) {
        for line in block.lines() {
            let entry = line.trim().trim_end_matches(',');
            let Some(dependency) = entry
                .strip_prefix('"')
                .and_then(|rest| rest.strip_suffix('"'))
            else {
                continue;
            };
            let name = dependency.split(' ').next().unwrap_or(dependency);
            if !workspace.contains(name) {
                problems.push(format!("`{name}` is depended on but not in the workspace"));
            }
        }
    }
    let locked: BTreeSet<&str> = packages.iter().map(|(name, _)| name.as_str()).collect();
    for name in workspace {
        if !locked.contains(name.as_str()) {
            problems.push(format!("`{name}` is missing from the lock file"));
        }
    }
    problems
}

/// A dependency in a manifest: its table and its name.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Dependency {
    pub table: String,
    pub name: String,
}

fn is_dependency_table(table: &str) -> bool {
    let tail = table.rsplit('.').next().unwrap_or(table);
    tail == "dependencies" || tail == "dev-dependencies" || tail == "build-dependencies"
}

/// A TOML line without its comment. A `#` in a string is not one.
fn without_comment(line: &str) -> &str {
    let mut in_string = false;
    for (at, c) in line.char_indices() {
        match c {
            '"' => in_string = !in_string,
            '#' if !in_string => return &line[..at],
            _ => {}
        }
    }
    line
}

/// Reads a manifest: its dependencies and what is wrong with them. The only form
/// allowed is `name = { path = "../name" }`, so nothing can come from a registry, a
/// git repository or anywhere outside `crates/`.
pub fn read_manifest(text: &str) -> (Vec<Dependency>, Vec<String>) {
    let mut dependencies = Vec::new();
    let mut problems = Vec::new();
    let mut table = String::new();
    for raw in text.lines() {
        let line = without_comment(raw).trim();
        if line.is_empty() {
            continue;
        }
        if let Some(header) = line.strip_prefix('[') {
            table = header.trim_matches(['[', ']']).to_owned();
            if table.starts_with("patch") || table == "replace" {
                problems.push(format!("the `[{table}]` table replaces a crate"));
            }
            // `[dependencies.name]` holds one dependency's keys as lines.
            let parent = table.rsplit_once('.').map(|(parent, _)| parent);
            if parent.is_some_and(is_dependency_table) {
                problems.push(format!("`[{table}]` is not the allowed form"));
            }
            continue;
        }
        if !is_dependency_table(&table) {
            continue;
        }
        let Some((key, value)) = line.split_once('=') else {
            problems.push(format!("`{line}` in `[{table}]` cannot be read"));
            continue;
        };
        let (key, value) = (key.trim(), value.trim());
        let wanted = format!("{{ path = \"../{key}\" }}");
        if value != wanted {
            problems.push(format!(
                "`{key}` in `[{table}]` is `{value}`, not `{wanted}`"
            ));
        }
        dependencies.push(Dependency {
            table: table.clone(),
            name: key.to_owned(),
        });
    }
    (dependencies, problems)
}

fn workspace_set() -> BTreeSet<String> {
    crates().into_iter().collect()
}

pub fn manifest_of(crate_name: &str) -> String {
    read(&format!("crates/{crate_name}/Cargo.toml"))
}

const CLEAN_LOCK: &str = "\
version = 4

[[package]]
name = \"a\"
version = \"0.1.0\"
dependencies = [
 \"b\",
]

[[package]]
name = \"b\"
version = \"0.1.0\"
";

pub fn register(h: &mut Harness) {
    // Cargo rewrites a stale lock before any test can read it, so only a manifest that
    // declares a crate from outside can fail this: a tampered lock is what
    // `cargo test --locked` refuses, and the fake locks below test the checker itself.
    h.case("hermetic/every .gitignore pattern is anchored", || {
        let unanchored = unanchored_ignores(&read(".gitignore"));
        assert_eq!(unanchored, Vec::<String>::new());
    });
    h.case(
        "hermetic/an unanchored .gitignore pattern is reported",
        || {
            let found = unanchored_ignores("# build\n/out/\n\ntarget/\n");
            assert_eq!(found, ["target/"]);
        },
    );
    h.case("hermetic/Cargo.lock lists only workspace crates", || {
        let problems = lock_problems(&read("Cargo.lock"), &workspace_set());
        assert_eq!(problems, Vec::<String>::new());
    });
    let external = "[[package]]\nname = \"b\"\nversion = \"1.0.0\"\nsource = \"registry+https://github.com/rust-lang/crates.io-index\"\nchecksum = \"00\"\n";
    let lock_rows: &[(&str, String, &[&str])] = &[
        ("clean", CLEAN_LOCK.to_owned(), &[]),
        ("empty", String::new(), &["the lock file lists no package"]),
        (
            "unknown crate",
            format!("{CLEAN_LOCK}\n[[package]]\nname = \"serde\"\nversion = \"1.0.0\"\n"),
            &["`serde` is not a workspace crate"],
        ),
        (
            "a workspace name from a registry",
            format!("[[package]]\nname = \"a\"\nversion = \"0.1.0\"\n\n{external}"),
            &["`b` comes from outside the repository"],
        ),
        (
            "a checksum alone",
            "[[package]]\nname = \"a\"\nversion = \"0.1.0\"\nchecksum = \"00\"\n\n[[package]]\nname = \"b\"\nversion = \"0.1.0\"\n".to_owned(),
            &["`a` comes from outside the repository"],
        ),
        (
            "a git source",
            "[[package]]\nname = \"a\"\nversion = \"0.1.0\"\nsource = \"git+https://example.com/a\"\n\n[[package]]\nname = \"b\"\nversion = \"0.1.0\"\n".to_owned(),
            &["`a` comes from outside the repository"],
        ),
        (
            "a dependency on an unknown crate",
            "[[package]]\nname = \"a\"\nversion = \"0.1.0\"\ndependencies = [\n \"libc 0.2.0 (registry+https://x)\",\n]\n\n[[package]]\nname = \"b\"\nversion = \"0.1.0\"\n".to_owned(),
            &["`libc` is depended on but not in the workspace"],
        ),
        (
            "a workspace crate missing",
            "[[package]]\nname = \"a\"\nversion = \"0.1.0\"\n".to_owned(),
            &["`b` is missing from the lock file"],
        ),
    ];
    for (name, lock, expected) in lock_rows {
        let (lock, expected) = (lock.clone(), *expected);
        h.case(format!("hermetic/fake lock: {name}"), move || {
            let workspace: BTreeSet<String> = ["a", "b"].map(str::to_owned).into_iter().collect();
            assert_eq!(lock_problems(&lock, &workspace), expected);
        });
    }

    for name in crates() {
        h.case(
            format!("hermetic/{name} declares no external dependency"),
            move || {
                let (_, problems) = read_manifest(&manifest_of(&name));
                assert_eq!(problems, Vec::<String>::new());
            },
        );
    }
    h.case(
        "hermetic/the root manifest declares no external dependency",
        || {
            let root = read("Cargo.toml");
            let (dependencies, problems) = read_manifest(&root);
            assert_eq!(problems, Vec::<String>::new());
            assert_eq!(dependencies, Vec::<Dependency>::new());
            assert!(root.contains("edition = \"2024\""), "{root}");
        },
    );
    let manifest_rows: &[(&str, &str, Option<&str>)] = &[
        ("a path", "[dependencies]\nx = { path = \"../x\" }\n", None),
        (
            "a comment",
            "[dependencies]\n# serde = \"1\"\nx = { path = \"../x\" } # ok\n",
            None,
        ),
        (
            "no dependency",
            "[package]\nname = \"x\"\nversion = \"1\"\n",
            None,
        ),
        (
            "a version",
            "[dependencies]\nserde = \"1\"\n",
            Some("`serde` in `[dependencies]` is `\"1\"`, not `{ path = \"../serde\" }`"),
        ),
        (
            "a version table",
            "[dependencies]\nserde = { version = \"1\" }\n",
            Some(
                "`serde` in `[dependencies]` is `{ version = \"1\" }`, not `{ path = \"../serde\" }`",
            ),
        ),
        (
            "a git url",
            "[dependencies]\nx = { git = \"https://example.com/x\" }\n",
            Some(
                "`x` in `[dependencies]` is `{ git = \"https://example.com/x\" }`, not `{ path = \"../x\" }`",
            ),
        ),
        (
            "a path outside crates",
            "[dependencies]\nx = { path = \"../../x\" }\n",
            Some("`x` in `[dependencies]` is `{ path = \"../../x\" }`, not `{ path = \"../x\" }`"),
        ),
        (
            "a path and a version",
            "[dependencies]\nx = { path = \"../x\", version = \"1\" }\n",
            Some(
                "`x` in `[dependencies]` is `{ path = \"../x\", version = \"1\" }`, not `{ path = \"../x\" }`",
            ),
        ),
        (
            "a dev-dependency",
            "[dev-dependencies]\nproptest = \"1\"\n",
            Some("`proptest` in `[dev-dependencies]` is `\"1\"`, not `{ path = \"../proptest\" }`"),
        ),
        (
            "a build-dependency",
            "[build-dependencies]\ncc = \"1\"\n",
            Some("`cc` in `[build-dependencies]` is `\"1\"`, not `{ path = \"../cc\" }`"),
        ),
        (
            "a target dependency",
            "[target.'cfg(unix)'.dependencies]\nlibc = \"0.2\"\n",
            Some(
                "`libc` in `[target.'cfg(unix)'.dependencies]` is `\"0.2\"`, not `{ path = \"../libc\" }`",
            ),
        ),
        (
            "a workspace dependency",
            "[workspace.dependencies]\nserde = \"1\"\n",
            Some("`serde` in `[workspace.dependencies]` is `\"1\"`, not `{ path = \"../serde\" }`"),
        ),
        (
            "a dependency table",
            "[dependencies.serde]\nversion = \"1\"\n",
            Some("`[dependencies.serde]` is not the allowed form"),
        ),
        (
            "a patch",
            "[patch.crates-io]\n",
            Some("the `[patch.crates-io]` table replaces a crate"),
        ),
        (
            "a replace",
            "[replace]\n",
            Some("the `[replace]` table replaces a crate"),
        ),
        (
            "a dotted key",
            "[dependencies]\nserde.version = \"1\"\n",
            Some(
                "`serde.version` in `[dependencies]` is `\"1\"`, not `{ path = \"../serde.version\" }`",
            ),
        ),
        (
            "an inherited dependency",
            "[dependencies]\nserde = { workspace = true }\n",
            Some(
                "`serde` in `[dependencies]` is `{ workspace = true }`, not `{ path = \"../serde\" }`",
            ),
        ),
    ];
    for (name, manifest, expected) in manifest_rows {
        let (manifest, expected) = (*manifest, *expected);
        h.case(format!("hermetic/fake manifest: {name}"), move || {
            let (_, problems) = read_manifest(manifest);
            let wanted: Vec<&str> = expected.into_iter().collect();
            assert_eq!(problems, wanted);
        });
    }
    h.case("hermetic/testkit is never a normal dependency", || {
        for name in crates() {
            let (dependencies, _) = read_manifest(&manifest_of(&name));
            for dependency in dependencies {
                assert!(
                    dependency.name != "enrang-testkit" || dependency.table == "dev-dependencies",
                    "{name} has it in [{}]",
                    dependency.table
                );
            }
        }
    });
    h.case(
        "hermetic/every crate takes its edition from the workspace",
        || {
            for name in crates() {
                let manifest = manifest_of(&name);
                assert!(
                    manifest
                        .lines()
                        .any(|line| line == "edition.workspace = true"),
                    "{name}"
                );
            }
        },
    );
}
