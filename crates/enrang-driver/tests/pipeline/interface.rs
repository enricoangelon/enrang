//! Module interface files (M3 plan b.9 and f.1, stage 4M; ARCHITECTURE 6.8, A:1376):
//! the text `check` writes for each user module of a project depends on nothing
//! but the program. Checking it again writes the same bytes; so does checking a
//! copy of the project at another path, since no path of the checkout is stored;
//! shuffling a module's imports changes its own `source` hash and nothing else,
//! in its file or in any other; and the text is the same whichever parse mode
//! loaded the program, since a module's `.test.en` part is never stored.

use std::collections::BTreeMap;
use std::path::Path;
use std::sync::Arc;

use enrang_driver::interface::{self, DIR, FORMAT, Inputs};
use enrang_driver::{CheckOptions, Session, check_with, run_phase3};
use enrang_syntax::ParseMode;
use enrang_target::{TargetOpts, host_target, resolve};
use enrang_testkit::{Harness, TempDir};

use crate::no_panic::front_at;

/// A project of three modules: `main` imports `words` and `util/bag`, `words`
/// imports `util/bag`, and `util/bag` has a test part.
fn project(main_imports: &str) -> Vec<(&'static str, String)> {
    vec![
        (
            "src/util/bag.en",
            "public function fill(xs: &i64[], n: i64): void { let i = 0; while (i < n) { grow(xs, i); i++; } }\n\
             private function grow(xs: &i64[], v: i64): void { xs.push(v); }\n\
             public function first(xs: &Slice<i64>): &i64 { return &xs[0]; }\n"
                .to_owned(),
        ),
        (
            "src/util/bag.test.en",
            "test(\"fills\", () => { let xs: i64[] = []; fill(&xs, 2); expect(xs.length()).toBe(2); });\n"
                .to_owned(),
        ),
        (
            "src/words.en",
            "import { fill } from \"./util/bag\";\n\
             public function extend(zs: &i64[]): void { fill(zs, 2); }\n\
             public final class Lexer {\n  private src: &string;\n  private pos: isize = 0;\n  \
             public constructor(src: &string) { this.src = src; }\n  \
             public next(): &string | null {\n    if (this.pos >= this.src.length()) { return null; }\n    \
             const start = this.pos;\n    this.pos = this.src.length();\n    \
             return this.src.slice(start, this.pos);\n  }\n}\n"
                .to_owned(),
        ),
        (
            "src/main.en",
            format!(
                "{main_imports}let xs: i64[] = [];\nextend(&xs);\n*first(&xs) = 9;\n\
                 const text = \"ab\".toString();\nlet lx = new Lexer(&text);\nconsole.log(xs, lx.next());\n"
            ),
        ),
    ]
}

const IMPORTS: &str =
    "import { extend, Lexer } from \"./words\";\nimport { first } from \"./util/bag\";\n";

/// The same imports, in the other order.
const SHUFFLED: &str =
    "import { first } from \"./util/bag\";\nimport { extend, Lexer } from \"./words\";\n";

/// Writes `files` under a fresh directory, checks `src/main.en` there as a project,
/// and returns every interface file it wrote, by its path under the root.
fn interfaces_of(files: &[(&str, String)]) -> BTreeMap<String, String> {
    let dir = TempDir::new("interface");
    for (path, text) in files {
        dir.write(path, text);
    }
    let mut session = Session::new();
    let target = Arc::new(
        resolve(host_target(), &TargetOpts::default())
            .expect("a target")
            .0,
    );
    let options = CheckOptions {
        library_entry: false,
        project: Some(dir.path().to_path_buf()),
    };
    if let Err(e) = check_with(
        &mut session,
        dir.path(),
        Path::new("src/main.en"),
        target,
        &options,
    ) {
        panic!(
            "{e:?}\n{}",
            session.render(&enrang_diag::RenderOpts::default())
        );
    }
    let root = dir.path().join(DIR);
    let mut found = BTreeMap::new();
    let mut stack = vec![root.clone()];
    while let Some(at) = stack.pop() {
        for entry in std::fs::read_dir(&at)
            .expect("the interface directory")
            .flatten()
        {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else {
                let rel = path
                    .strip_prefix(dir.path())
                    .expect("under the root")
                    .to_string_lossy()
                    .replace('\\', "/");
                let text = std::fs::read_to_string(&path).expect("UTF-8");
                assert!(
                    !text.contains(&*dir.path().to_string_lossy()),
                    "{rel} names the checkout"
                );
                found.insert(rel, text);
            }
        }
    }
    found
}

/// The interface text of the module whose file is `entry`, built in this process
/// from the program loaded in `mode`; the module imports nothing.
fn interface_in_mode(files: &[(&str, &str)], entry: &str, mode: ParseMode) -> String {
    let dir = TempDir::new("interface-mode");
    for (path, text) in files {
        dir.write(path, text);
    }
    let target = Arc::new(
        resolve(host_target(), &TargetOpts::default())
            .expect("a target")
            .0,
    );
    let (mut session, typed) = front_at(dir.path(), Path::new(entry), target, false, mode);
    let typed = typed.unwrap_or_else(|| {
        panic!(
            "{mode:?}: {}",
            session.render(&enrang_diag::RenderOpts::default())
        )
    });
    let out = run_phase3(&mut session, &typed).expect("no internal error");
    assert!(
        session.dcx.take().is_empty(),
        "{mode:?}: phase 3 reports something"
    );
    let cx = Inputs {
        tcx: &typed.tcx,
        map: &session.map,
        contracts: &out.contracts,
        bodies: &out.mir,
    };
    let (module, owners) = &out.modules[0];
    interface::text(&cx, *module, owners, &[]).text
}

/// A text with its `source` line taken out.
fn without_source(text: &str) -> String {
    text.lines()
        .filter(|line| !line.starts_with("source "))
        .map(|line| format!("{line}\n"))
        .collect()
}

pub fn register(h: &mut Harness) {
    h.case(
        "interface/a project's modules each get a file, in order",
        || {
            let files = interfaces_of(&project(IMPORTS));
            let names: Vec<&str> = files.keys().map(String::as_str).collect();
            assert_eq!(
                names,
                [
                    "out/interfaces/src/main.eni",
                    "out/interfaces/src/util/bag.eni",
                    "out/interfaces/src/words.eni"
                ]
            );
            for (name, text) in &files {
                assert!(text.starts_with(&format!("{FORMAT}\n")), "{name}");
                // The test part is never stored.
                assert!(!text.contains("fills"), "{name} holds the test part");
            }
            let main = &files["out/interfaces/src/main.eni"];
            let imports: Vec<&str> = main.lines().filter(|l| l.starts_with("import ")).collect();
            assert_eq!(imports.len(), 2, "{main}");
            assert!(
                imports[0].starts_with("import \"src/util/bag\" "),
                "{imports:?}"
            );
            assert!(
                imports[1].starts_with("import \"src/words\" "),
                "{imports:?}"
            );
        },
    );
    h.case("interface/a second check writes the same bytes", || {
        assert_eq!(
            interfaces_of(&project(IMPORTS)),
            interfaces_of(&project(IMPORTS))
        );
    });
    h.case(
        "interface/a checkout at another path writes the same bytes",
        || {
            // Each run is in a directory of its own, so the paths differ; one run
            // nests the project a level deeper still.
            let here = interfaces_of(&project(IMPORTS));
            let deeper: Vec<(String, String)> = project(IMPORTS)
                .into_iter()
                .map(|(path, text)| (format!("checkout/{path}"), text))
                .collect();
            let dir = TempDir::new("interface-deeper");
            for (path, text) in &deeper {
                dir.write(path, text);
            }
            let root = dir.path().join("checkout");
            let mut session = Session::new();
            let target = Arc::new(
                resolve(host_target(), &TargetOpts::default())
                    .expect("a target")
                    .0,
            );
            let options = CheckOptions {
                library_entry: false,
                project: Some(root.clone()),
            };
            check_with(
                &mut session,
                &root,
                Path::new("src/main.en"),
                target,
                &options,
            )
            .unwrap_or_else(|e| panic!("{e:?}"));
            for (name, text) in &here {
                let there = std::fs::read_to_string(root.join(name)).expect("written");
                assert_eq!(&there, text, "{name}");
            }
        },
    );
    h.case(
        "interface/shuffled imports change the module's source hash and nothing else",
        || {
            let first = interfaces_of(&project(IMPORTS));
            let shuffled = interfaces_of(&project(SHUFFLED));
            assert_eq!(first.len(), shuffled.len());
            for (name, text) in &first {
                let other = &shuffled[name];
                if name.ends_with("/main.eni") {
                    assert_ne!(text, other, "main's own source differs");
                    assert_eq!(without_source(text), without_source(other), "{name}");
                } else {
                    assert_eq!(text, other, "{name}");
                }
            }
        },
    );
    h.case(
        "interface/both parse modes give the same text, the test part left out",
        || {
            let files = [
                (
                    "bag.en",
                    "public function fill(xs: &i64[], n: i64): void { let i = 0; while (i < n) { xs.push(i); i++; } }\n\
                     public function first(xs: &Slice<i64>): &i64 { return &xs[0]; }\n",
                ),
                (
                    "bag.test.en",
                    "test(\"fills\", () => { let xs: i64[] = []; fill(&xs, 2); expect(*first(&xs)).toBe(0); });\n",
                ),
            ];
            let build = interface_in_mode(&files, "bag.en", ParseMode::Build);
            let test = interface_in_mode(&files, "bag.en", ParseMode::Test);
            assert_eq!(build, test);
            assert!(build.contains("fn fill("), "{build}");
            assert!(!build.contains("fills"), "{build}");
            // Without the part on disk, the text is still the same.
            let alone = interface_in_mode(&files[..1], "bag.en", ParseMode::Test);
            assert_eq!(alone, test);
        },
    );
}
