//! The module loader and the module graph (plan d.2): load order, test parts,
//! imports, child modules and folder namespaces (SPEC 4.12), the library of the
//! target's layers, EN0305, EN0304, EN0312, and the order modules are checked in.

use std::path::PathBuf;
use std::sync::Arc;

use enrang_base::{FileOrigin, SourceMap};
use enrang_diag::DiagCtx;
use enrang_sema::{ImportTarget, LibSource, LoadError, LoadedProgram, ProgramInput, load};
use enrang_syntax::{NodeIdGen, ParseMode};
use enrang_target::{TargetOpts, resolve};
use enrang_testkit::Harness;

use crate::support::{MINI_LIB, Run, fake_lib, run};

/// The order modules are checked in, by path.
fn order(r: &Run) -> Vec<String> {
    r.program
        .as_ref()
        .expect("checked")
        .modules
        .iter()
        .map(|&m| r.tcx.module(m).path.to_string())
        .collect()
}

fn loaded(
    sources: &[(&str, &str)],
    lib: LibSource,
    target: &str,
    mode: ParseMode,
) -> (LoadedProgram, SourceMap) {
    let (spec, _) = resolve(target, &TargetOpts::default()).expect("a target");
    let input = ProgramInput {
        entry: PathBuf::from(sources[0].0),
        mode,
        overrides: sources
            .iter()
            .map(|(p, t)| (PathBuf::from(p), Arc::from(*t)))
            .collect(),
        dir: PathBuf::from("/nonexistent/enrang-sema-suite"),
        lib,
        library_entry: false,
    };
    let mut map = SourceMap::new();
    let mut dcx = DiagCtx::new();
    let program = load(&input, &spec, &mut map, &mut NodeIdGen::new(), &mut dcx).expect("loads");
    (program, map)
}

fn paths(program: &LoadedProgram) -> Vec<String> {
    program.modules.iter().map(|m| m.path.to_string()).collect()
}

pub fn register(h: &mut Harness) {
    h.case(
        "load/the entry, then imports breadth-first, then the library in key order",
        || {
            let (program, _) = loaded(
                &[
                    (
                        "src/main.en",
                        "import { b } from \"./b\";\nimport { a } from \"./a\";\n",
                    ),
                    (
                        "src/a.en",
                        "import { c } from \"./lib/c\";\npublic const a: i64 = 1;\n",
                    ),
                    ("src/b.en", "public const b: i64 = 1;\n"),
                    ("src/lib/c.en", "public const c: i64 = 1;\n"),
                ],
                fake_lib(MINI_LIB),
                "x86_64-linux",
                ParseMode::Build,
            );
            assert_eq!(
                paths(&program),
                [
                    "src/main",
                    "src/b",
                    "src/a",
                    "src/lib/c",
                    "alloc/prelude",
                    "core/option",
                    "core/prelude",
                    "os/linux_x64/prelude"
                ]
            );
            assert_eq!(program.entry, 0);
            assert!(program.modules[4..].iter().all(|m| m.library));
            assert!(program.modules[..4].iter().all(|m| !m.library));
            assert_eq!(program.modules[0].imports.len(), 2);
            assert_eq!(
                program.modules[0].imports[0].target,
                Some(ImportTarget::Module(1))
            );
            assert_eq!(
                program.modules[0].imports[1].target,
                Some(ImportTarget::Module(2))
            );
        },
    );
    h.case("load/only the target's OS layer is loaded", || {
        let lib = fake_lib(&[
            ("core/prelude", "// c\n"),
            ("alloc/prelude", "// a\n"),
            ("os/linux_x64/prelude", "// l\n"),
            ("os/none/prelude", "// n\n"),
            ("os/none/vga", "// v\n"),
        ]);
        let (program, _) = loaded(
            &[("main.en", "")],
            lib.clone(),
            "i386-none",
            ParseMode::Build,
        );
        assert_eq!(
            paths(&program),
            [
                "main",
                "alloc/prelude",
                "core/prelude",
                "os/none/prelude",
                "os/none/vga"
            ]
        );
        assert_eq!(program.os_folder, "os/none");
        let (program, _) = loaded(&[("main.en", "")], lib, "x86_64-linux", ParseMode::Build);
        assert_eq!(
            paths(&program),
            [
                "main",
                "alloc/prelude",
                "core/prelude",
                "os/linux_x64/prelude"
            ]
        );
    });
    h.case("load/files are added as user or library sources", || {
        let (program, map) = loaded(
            &[("src/main.en", "")],
            fake_lib(MINI_LIB),
            "x86_64-linux",
            ParseMode::Build,
        );
        let entry = map.file(program.modules[0].file);
        assert_eq!(entry.origin, FileOrigin::User);
        assert_eq!(entry.path, PathBuf::from("src/main.en"));
        let lib = map.file(program.modules[1].file);
        assert_eq!(lib.origin, FileOrigin::Library);
        assert_eq!(lib.path, PathBuf::from("lib/alloc/prelude.en"));
    });
    h.case("load/the test part loads in test mode only", || {
        let sources = [
            ("src/main.en", "public function f(): void {}\n"),
            (
                "src/main.test.en",
                "import { g } from \"./helper\";\ntest(\"f\", () => { f(); });\n",
            ),
            ("src/helper.en", "public function g(): void {}\n"),
        ];
        let (program, _) = loaded(
            &sources,
            fake_lib(MINI_LIB),
            "x86_64-linux",
            ParseMode::Test,
        );
        let part = program.modules[0].test_part.as_ref().expect("a test part");
        assert_eq!(part.imports[0].target, Some(ImportTarget::Module(1)));
        assert_eq!(program.modules[1].path.as_str(), "src/helper");
        let (program, _) = loaded(
            &sources,
            fake_lib(MINI_LIB),
            "x86_64-linux",
            ParseMode::Build,
        );
        assert!(program.modules[0].test_part.is_none());
        assert!(
            program
                .modules
                .iter()
                .all(|m| m.path.as_str() != "src/helper")
        );
    });
    h.case("load/library paths: core, alloc, os and folders", || {
        let (program, _) = loaded(
            &[("main.en", "import { string } from \"core/prelude\";\nimport * as os from \"os\";\nimport { x } from \"os/prelude\";\n")],
            fake_lib(MINI_LIB),
            "x86_64-linux",
            ParseMode::Build,
        );
        let edges: Vec<_> = program.modules[0].imports.iter().map(|e| e.target.clone()).collect();
        let core = program.index_of("core/prelude").expect("core");
        let os = program.index_of("os/linux_x64/prelude").expect("os");
        let folder = program.index_of("os/linux_x64").expect("the `os` folder as a namespace");
        assert!(program.modules[folder].folder && program.modules[folder].library);
        assert!(program.modules[folder].ast.items.is_empty());
        assert_eq!(
            edges,
            [
                Some(ImportTarget::Module(core)),
                Some(ImportTarget::Module(folder)),
                Some(ImportTarget::Module(os)),
            ]
        );
    });
    h.case("load/an unreadable entry stops loading", || {
        let (spec, _) = resolve("x86_64-linux", &TargetOpts::default()).expect("a target");
        let input = ProgramInput {
            entry: PathBuf::from("missing.en"),
            mode: ParseMode::Build,
            overrides: Default::default(),
            dir: PathBuf::from("/nonexistent/enrang-sema-suite"),
            lib: fake_lib(MINI_LIB),
            library_entry: false,
        };
        let result = load(
            &input,
            &spec,
            &mut SourceMap::new(),
            &mut NodeIdGen::new(),
            &mut DiagCtx::new(),
        );
        assert!(
            matches!(result, Err(LoadError::Unreadable { .. })),
            "{result:?}"
        );
    });
    h.case("load/a syntax error ends phase 1", || {
        let (spec, _) = resolve("x86_64-linux", &TargetOpts::default()).expect("a target");
        let input = ProgramInput::in_memory(
            "main.en",
            &[("main.en", "public function (\n")],
            ParseMode::Build,
        );
        let mut dcx = DiagCtx::new();
        let result = load(
            &input,
            &spec,
            &mut SourceMap::new(),
            &mut NodeIdGen::new(),
            &mut dcx,
        );
        assert!(matches!(result, Err(LoadError::Aborted(_))), "{result:?}");
        assert!(dcx.has_errors());
    });
    h.case("load/EN0305: an import path that names nothing", || {
        let r = run(&[(
            "src/main.en",
            "import { x } from \"./nowhere\";\nimport { y } from \"bogus\";\n",
        )]);
        assert_eq!(r.codes(), ["EN0305", "EN0305"]);
        assert_eq!(
            r.rendered(),
            "error[EN0305]: import path not found: `./nowhere`
 --> src/main.en:1:19
  |
1 | import { x } from \"./nowhere\";
  |                   ^^^^^^^^^^^ no file, folder or library module has this path
  |
  = explain: run `enrang explain EN0305`

error[EN0305]: import path not found: `bogus`
 --> src/main.en:2:19
  |
2 | import { y } from \"bogus\";
  |                   ^^^^^^^ no file, folder or library module has this path
  |
  = explain: run `enrang explain EN0305`

error: aborting due to 2 previous errors
"
        );
    });
    h.case("load/the embedded library loads for every target", || {
        for target in [
            "x86_64-linux",
            "i386-linux",
            "x86_64-windows",
            "i386-none",
            "x86_64-none",
            "vm64",
        ] {
            let (program, _) = loaded(
                &[("main.en", "")],
                LibSource::Embedded,
                target,
                ParseMode::Build,
            );
            assert!(
                program
                    .modules
                    .iter()
                    .any(|m| m.path.as_str() == "core/prelude"),
                "{target}"
            );
            assert!(
                program
                    .modules
                    .iter()
                    .any(|m| m.path.as_str() == format!("{}/prelude", program.os_folder)),
                "{target}"
            );
        }
    });
    h.case("load/a folder's named children load as modules", || {
        let (program, _) = loaded(
            &[
                (
                    "src/main.en",
                    "import { serial, vga } from \"./drivers\";\n",
                ),
                ("src/drivers/serial.en", "public class Port { }\n"),
                ("src/drivers/vga.en", "public class Screen { }\n"),
                ("src/drivers/unused.en", "public class Other { }\n"),
            ],
            fake_lib(MINI_LIB),
            "x86_64-linux",
            ParseMode::Build,
        );
        let serial = program.index_of("src/drivers/serial").expect("serial");
        let vga = program.index_of("src/drivers/vga").expect("vga");
        assert_eq!(
            program.modules[0].imports[0].target,
            Some(ImportTarget::Folder("src/drivers".to_owned()))
        );
        assert_eq!(program.modules[0].imports[0].children, [serial, vga]);
        assert!(
            program.index_of("src/drivers/unused").is_none(),
            "only the children named are loaded"
        );
    });
    h.case(
        "load/a child module of a file that declares no such name",
        || {
            let (program, _) = loaded(
                &[
                    ("src/main.en", "import { Item, part } from \"./util\";\n"),
                    ("src/util.en", "public class Item { }\n"),
                    ("src/util/part.en", "public class Piece { }\n"),
                    ("src/util/Item.en", "public class Shadowed { }\n"),
                ],
                fake_lib(MINI_LIB),
                "x86_64-linux",
                ParseMode::Build,
            );
            let part = program.index_of("src/util/part").expect("the child module");
            assert_eq!(program.modules[0].imports[0].children, [part]);
            assert!(
                program.index_of("src/util/Item").is_none(),
                "an item of `util` wins over a child module"
            );
        },
    );
    h.case(
        "load/a folder imported as a namespace loads every child",
        || {
            let (program, map) = loaded(
                &[
                    ("src/main.en", "import * as d from \"./drivers\";\n"),
                    ("src/drivers/serial.en", "public class Port { }\n"),
                    ("src/drivers/serial.test.en", "test(\"x\", () => { });\n"),
                    ("src/drivers/net/nic.en", "public class Card { }\n"),
                ],
                fake_lib(MINI_LIB),
                "x86_64-linux",
                ParseMode::Build,
            );
            let folder = program
                .index_of("src/drivers")
                .expect("the folder's module");
            assert!(program.modules[folder].folder && !program.modules[folder].library);
            assert_eq!(
                map.file(program.modules[folder].file).path,
                PathBuf::from("src/drivers/")
            );
            assert_eq!(
                program.modules[0].imports[0].target,
                Some(ImportTarget::Module(folder))
            );
            for path in [
                "src/drivers/serial",
                "src/drivers/net",
                "src/drivers/net/nic",
            ] {
                assert!(program.index_of(path).is_some(), "{path}");
            }
            assert!(program.modules[program.index_of("src/drivers/net").unwrap()].folder);
            assert!(program.index_of("src/drivers/serial.test").is_none());
        },
    );
    h.case("load/order: topological, ties broken by module path (A:884)", || {
        // Loaded as main, c, b, a: the order never follows load order.
        let r = run(&[
            ("src/main.en", "import { C } from \"./c\";\nimport { B } from \"./b\";\nimport { A } from \"./a\";\n"),
            ("src/c.en", "public class C { }\n"),
            ("src/b.en", "public class B { }\n"),
            ("src/a.en", "public class A { }\n"),
        ]);
        r.clean();
        assert_eq!(
            order(&r),
            [
                "core/option",
                "core/prelude",
                "alloc/prelude",
                "os/linux_x64/prelude",
                "src/a",
                "src/b",
                "src/c",
                "src/main"
            ]
        );
        // An import puts its target first, whatever the paths say.
        let r = run(&[
            ("src/main.en", "import { C } from \"./c\";\nimport { B } from \"./b\";\nimport { A } from \"./a\";\n"),
            ("src/c.en", "public class C { }\n"),
            ("src/b.en", "public class B { }\n"),
            ("src/a.en", "import { C } from \"./c\";\npublic class A { }\n"),
        ]);
        r.clean();
        assert_eq!(&order(&r)[4..], ["src/b", "src/c", "src/a", "src/main"]);
    });
    h.case(
        "load/EN0304: an import cycle, at the import closing it in the least module",
        || {
            let r = run(&[
                (
                    "src/main.en",
                    "import { B } from \"./b\";\npublic class M { }\n",
                ),
                (
                    "src/b.en",
                    "import { A } from \"./a\";\npublic class B { }\n",
                ),
                (
                    "src/a.en",
                    "import { B } from \"./b\";\npublic class A { }\n",
                ),
            ]);
            assert_eq!(r.codes(), ["EN0304"]);
            assert_eq!(
                r.rendered(),
                "error[EN0304]: import cycle: `a.en` imports `b.en`, which imports `a.en`
 --> src/a.en:1:19
  |
1 | import { B } from \"./b\";
  |                   ^^^^^ this import closes the cycle
  |
  = explain: run `enrang explain EN0304`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "load/EN0304: a longer cycle follows the shortest way back",
        || {
            let r = run(&[
                ("src/main.en", "import { A } from \"./a\";\n"),
                (
                    "src/a.en",
                    "import { B } from \"./b\";\npublic class A { }\n",
                ),
                (
                    "src/b.en",
                    "import { C } from \"./c\";\npublic class B { }\n",
                ),
                (
                    "src/c.en",
                    "import { A } from \"./a\";\npublic class C { }\n",
                ),
            ]);
            assert_eq!(
                r.messages(),
                ["import cycle: `a.en` imports `b.en`, which imports `c.en`, which imports `a.en`"]
            );
        },
    );
    h.case("load/EN0304: a module importing itself", || {
        let r = run(&[(
            "src/main.en",
            "import * as me from \"./main\";\npublic class X { }\n",
        )]);
        assert_eq!(r.messages(), ["import cycle: `main.en` imports itself"]);
    });
    h.case("load/EN0304: the cycle check follows re-exports", || {
        let r = run(&[
            ("src/main.en", "import { P } from \"./a\";\n"),
            ("src/a.en", "public import { P } from \"./b\";\n"),
            (
                "src/b.en",
                "import { Q } from \"./a\";\npublic class P { }\npublic class Q { }\n",
            ),
        ]);
        assert!(r.codes().contains(&"EN0304".to_owned()), "{}", r.rendered());
        assert!(
            r.messages()
                .contains(&"import cycle: `a.en` imports `b.en`, which imports `a.en`".to_owned())
        );
    });
    h.case(
        "load/EN0304: a cycle through a folder's child module",
        || {
            let r = run(&[
                (
                    "src/main.en",
                    "import { util } from \"./lib\";\npublic class M { }\n",
                ),
                (
                    "src/lib/util.en",
                    "import { M } from \"../main\";\npublic class U { }\n",
                ),
            ]);
            assert_eq!(r.codes(), ["EN0304"]);
            // `src/lib/util` is the least path of the two.
            assert_eq!(
                r.messages(),
                ["import cycle: `util.en` imports `main.en`, which imports `util.en`"]
            );
        },
    );
    h.case(
        "load/a test part's imports are not counted for EN0304",
        || {
            let r = run(&[
                ("src/main.en", "public function f(): i64 { return 1; }\n"),
                (
                    "src/main.test.en",
                    "import { g } from \"./helper\";\ntest(\"f\", () => { g(); });\n",
                ),
                (
                    "src/helper.en",
                    "import { f } from \"./main\";\npublic function g(): i64 { return f(); }\n",
                ),
            ]);
            r.clean();
        },
    );
    h.case(
        "load/EN0312: importing a file with top-level statements",
        || {
            let r = run(&[
                ("src/main.en", "import { f } from \"./util\";\n"),
                (
                    "src/util.en",
                    "console.log(\"hi\");\npublic function f(): void { }\n",
                ),
            ]);
            assert_eq!(r.codes(), ["EN0312"]);
            assert_eq!(
                r.rendered(),
                "error[EN0312]: `util.en` has top-level statements, so it can't be imported
 --> src/main.en:1:19
  |
1 | import { f } from \"./util\";
  |                   ^^^^^^^^ imported here
 --> src/util.en:1:1
  |
1 | console.log(\"hi\");
  | ------------------ the first top-level statement is here
  |
  = explain: run `enrang explain EN0312`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "load/EN0312: a plain top-level `let` gets the help to write `unsafe let`",
        || {
            let r = run(&[
                ("src/main.en", "import { f } from \"./util\";\n"),
                (
                    "src/util.en",
                    "let count = 0;\npublic function f(): void { }\n",
                ),
            ]);
            assert_eq!(r.codes(), ["EN0312"]);
            let diag = &r.diags[0];
            assert_eq!(
                diag.secondary[0].text,
                "a plain top-level `let` is a statement"
            );
            assert_eq!(
                diag.helps[0].message,
                "for static storage, write `unsafe let`"
            );
        },
    );
    h.case(
        "load/EN0312: a child module with statements, named by an import",
        || {
            let r = run(&[
                ("src/main.en", "import { tool } from \"./bin\";\n"),
                ("src/bin/tool.en", "console.log(1);\n"),
            ]);
            assert_eq!(r.codes(), ["EN0312"]);
            assert_eq!(
                r.messages(),
                ["`tool.en` has top-level statements, so it can't be imported"]
            );
            let span = r.diags[0].primary.span;
            assert_eq!(r.map.text(span), "tool");
        },
    );
    h.case("load/the entry's own statements are no EN0312", || {
        let r = run(&[
            ("src/main.en", "import { f } from \"./util\";\nf();\n"),
            ("src/util.en", "public function f(): void { }\n"),
        ]);
        r.clean();
    });
    h.case("load/a folder on disk: its files and sub-folders, links not followed", || {
        let dir = enrang_testkit::TempDir::new("sema-folder");
        for (path, text) in [
            ("src/main.en", "import * as d from \"./drivers\";\npublic function f(p: d.serial.Port, q: d.net.nic.Card): void { }\n"),
            ("src/drivers/serial.en", "public class Port { }\n"),
            ("src/drivers/net/nic.en", "public class Card { }\n"),
            ("src/drivers/notes.txt", "not a module\n"),
        ] {
            let file = dir.join(path);
            std::fs::create_dir_all(file.parent().expect("a parent")).expect("a folder");
            std::fs::write(file, text).expect("a file");
        }
        #[cfg(unix)]
        std::os::unix::fs::symlink(dir.join("src"), dir.join("src/drivers/up")).expect("a link");
        let (spec, _) = resolve("x86_64-linux", &TargetOpts::default()).expect("a target");
        let input = ProgramInput {
            entry: PathBuf::from("src/main.en"),
            mode: ParseMode::Build,
            overrides: Default::default(),
            dir: dir.path().to_path_buf(),
            lib: fake_lib(MINI_LIB),
            library_entry: false,
        };
        let mut map = SourceMap::new();
        let mut dcx = DiagCtx::new();
        let program = load(&input, &spec, &mut map, &mut NodeIdGen::new(), &mut dcx).expect("loads");
        let mut paths: Vec<String> = program
            .modules
            .iter()
            .filter(|m| !m.library)
            .map(|m| m.path.to_string())
            .collect();
        paths.sort();
        assert_eq!(
            paths,
            ["src/drivers", "src/drivers/net", "src/drivers/net/nic", "src/drivers/serial", "src/main"]
        );
    });
    review_cases(h);
}

/// The cases of stage 6's front review (`fix-2`): each fails without its fix.
fn review_cases(h: &mut Harness) {
    h.case(
        "load/a user folder named `core`, `alloc` or `os` is no library module",
        || {
            let r = run(&[
                (
                    "main.en",
                    "import { f } from \"./core/prelude\";\nimport { h } from \"./os/x\";\npublic function g(a: Result<i64, Failure>, b: Box<i64>): void {}\n",
                ),
                ("core/prelude.en", "public function f(): void {}\n"),
                ("os/x.en", "public function h(b: Box<i32>, c: i64[]): void {}\n"),
            ]);
            r.clean();
            let program = r.program.as_ref().expect("checked");
            let mut user: Vec<String> = program
                .modules
                .iter()
                .filter(|&&m| !r.tcx.module(m).library)
                .map(|&m| r.tcx.module(m).path.to_string())
                .collect();
            user.sort();
            assert_eq!(user, ["./core/prelude", "./os/x", "main"]);
            let library: Vec<String> = program
                .modules
                .iter()
                .filter(|&&m| r.tcx.module(m).library)
                .map(|&m| r.tcx.module(m).path.to_string())
                .collect();
            assert!(library.contains(&"core/prelude".to_owned()), "{library:?}");
            r.def("./core/prelude::f");
            r.def("core/prelude::Ok");
            // A user module under `core/` sees every prelude.
            run(&[
                ("main.en", "import { f } from \"./core/util\";\n"),
                ("core/util.en", "import { g } from \"../alloc/b\";\npublic function f(b: Box<i32>): void {}\n"),
                ("alloc/b.en", "public function g(x: i64[]): void {}\n"),
            ])
            .clean();
        },
    );
    h.case(
        "load/an entry spelled with `./` loads as the same module",
        || {
            let r = run(&[
                (
                    "./main.en",
                    "import { g } from \"../x\";\nimport { s } from \"./sub/b\";\ng();\n",
                ),
                ("x.en", "public function f(): void {}\n"),
                ("../x.en", "public function g(): void {}\n"),
                (
                    "sub/b.en",
                    "import { t } from \"./../sub/c\";\npublic const s: i64 = 1;\n",
                ),
                ("sub/c.en", "public const t: i64 = 1;\n"),
            ]);
            r.clean();
            let program = r.program.as_ref().expect("checked");
            let mut user: Vec<String> = program
                .modules
                .iter()
                .filter(|&&m| !r.tcx.module(m).library)
                .map(|&m| r.tcx.module(m).path.to_string())
                .collect();
            user.sort();
            assert_eq!(user, ["../x", "main", "sub/b", "sub/c"]);
            let main = program
                .modules
                .iter()
                .copied()
                .find(|&m| r.tcx.module(m).path.as_str() == "main")
                .expect("the entry");
            assert_eq!(
                r.map
                    .file(r.tcx.module(main).file)
                    .path
                    .display()
                    .to_string(),
                "main.en"
            );
            r.def("../x::g");
        },
    );
    h.case(
        "load/EN0312: a file with statements reached through a folder namespace",
        || {
            let r = run(&[
                (
                    "main.en",
                    "import * as d from \"./drivers\";\nd.demo.f();\n",
                ),
                (
                    "drivers/demo.en",
                    "let x = 1;\npublic function f(): void {}\n",
                ),
                ("drivers/net/raw.en", "f();\nfunction f(): void {}\n"),
                ("drivers/vga.en", "public function f(): void {}\n"),
            ]);
            assert_eq!(
                r.rendered(),
                "error[EN0312]: `demo.en` has top-level statements, so it can't be imported
 --> main.en:1:20
  |
1 | import * as d from \"./drivers\";
  |                    ^^^^^^^^^^^ the folder imported here holds `drivers/demo.en`
 --> drivers/demo.en:1:1
  |
1 | let x = 1;
  | ---------- a plain top-level `let` is a statement
  |
help: for static storage, write `unsafe let`
  = explain: run `enrang explain EN0312`

error: aborting due to 1 previous error
"
            );
            // A sub-folder bound by name holds a file with statements too.
            let r = run(&[
                ("main.en", "import { net, vga } from \"./drivers\";\n"),
                ("drivers/net/raw.en", "f();\nfunction f(): void {}\n"),
                ("drivers/vga.en", "public function f(): void {}\n"),
            ]);
            assert_eq!(r.codes(), ["EN0312"]);
            assert_eq!(r.map.text(r.diags[0].primary.span), "net");
            assert_eq!(
                r.diags[0].primary.text,
                "the folder imported here holds `drivers/net/raw.en`"
            );
            assert_eq!(
                r.diags[0].secondary[0].text,
                "the first top-level statement is here"
            );
            run(&[
                ("main.en", "import * as d from \"./drivers\";\n"),
                ("drivers/vga.en", "public function f(): void {}\n"),
            ])
            .clean();
        },
    );
    h.case(
        "load/a name a file re-exports loads no child module of that name (M24)",
        || {
            run(&[
                (
                    "main.en",
                    "import { X } from \"./p\";\npublic function f(x: X): void {}\n",
                ),
                ("p.en", "public import { X } from \"./q\";\n"),
                ("q.en", "public class X {}\n"),
                ("p/X.en", "this is not Enrang\n"),
            ])
            .clean();
        },
    );
    h.case(
        "load/EN0304: the way back is the shortest one, not the first found (M38)",
        || {
            let r = run(&[
                ("src/main.en", "import * as a from \"./a\";\n"),
                ("src/a.en", "import * as x from \"./x\";\n"),
                (
                    "src/x.en",
                    "import * as p from \"./p\";\nimport * as q from \"./q\";\n",
                ),
                ("src/p.en", "import * as a from \"./a\";\n"),
                ("src/q.en", "import * as r from \"./r\";\n"),
                ("src/r.en", "import * as a from \"./a\";\n"),
            ]);
            assert_eq!(r.codes(), ["EN0304"]);
            assert_eq!(
                r.messages(),
                ["import cycle: `a.en` imports `x.en`, which imports `p.en`, which imports `a.en`"]
            );
        },
    );
}
