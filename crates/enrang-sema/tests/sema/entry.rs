//! The sema suite's cases for where a program starts (owner 4F; plan d.17; SPEC 7,
//! S:1143): the entry module's top-level statements, else `function main` with one
//! of the three signatures (EN0436 for any other), and `main` beside statements,
//! warning EN0314 and not the entry.

use enrang_hir::Entry;
use enrang_testkit::Harness;

use crate::consteval::from_source::{diag, diags, gives, src};
use crate::support::{Run, run};

/// The entry the run's checked program names.
fn entry(r: &Run) -> Entry {
    r.program.as_ref().expect("checked").entry
}

/// The entry module of the run.
fn main_module(r: &Run) -> enrang_hir::ModuleId {
    r.tcx.def(r.def("src/main")).module
}

pub fn register(h: &mut Harness) {
    h.case("entry/a file's top-level statements are its entry", || {
        let r = src("let x = 1;\nconsole.log(x);\n");
        r.clean();
        assert_eq!(entry(&r), Entry::Statements(main_module(&r)));
    });
    for (ret, extra) in [
        ("void", ""),
        ("i32", " return 0;"),
        ("int", " return 0;"),
        ("Result<void>", ""),
        ("Result<void, Bad>", ""),
    ] {
        h.case(
            format!("entry/`function main(): {ret}` is the entry of a file with no statements"),
            move || {
                let text = format!(
                    "public function main(): {ret} {{{extra} }}\nprivate enum Bad {{ Broken }}\n"
                );
                let r = src(&text);
                assert_eq!(diags(&r), Vec::<[String; 4]>::new(), "{}", r.rendered());
                assert_eq!(entry(&r), Entry::Main(r.def("src/main::main")));
            },
        );
    }
    h.case("entry/EN0436: `main` returning anything else", || {
        let r = src("public function main(): i64 { return 0; }\n");
        assert_eq!(
            r.rendered(),
            "error[EN0436]: `main` must return `void`, `i32` or `Result<void, E>`
 --> src/main.en:1:17
  |
1 | public function main(): i64 { return 0; }
  |                 ^^^^ this `main` returns `i64`
  |
  = explain: run `enrang explain EN0436`

error: aborting due to 1 previous error
"
        );
        for (ret, body, shown) in [
            ("string", "return \"\";", "string"),
            ("never", "unreachable();", "never"),
            ("Result<i32>", "return Ok(0);", "Result<int>"),
            ("u8 | null", "return null;", "u8 | null"),
        ] {
            gives(
                &format!("public function main(): {ret} {{ {body} }}\n"),
                &[diag(
                    "EN0436",
                    "1:17",
                    "`main` must return `void`, `i32` or `Result<void, E>`",
                    &format!("this `main` returns `{shown}`"),
                )],
            );
        }
    });
    h.case(
        "entry/EN0436: `main` with parameters or type parameters",
        || {
            let r = src("public function main(args: string[]): void { }\n");
            assert_eq!(
                r.rendered(),
                "error[EN0436]: `main` takes no parameters
 --> src/main.en:1:17
  |
1 | public function main(args: string[]): void { }
  |                 ^^^^ this `main` takes 1 parameter
  |
help: read the command line with `os.args()`
  = explain: run `enrang explain EN0436`

error: aborting due to 1 previous error
"
            );
            gives(
                "public function main(a: i32, b: i32): i32 { return a + b; }\n",
                &[diag(
                    "EN0436",
                    "1:17",
                    "`main` takes no parameters",
                    "this `main` takes 2 parameters",
                )],
            );
            gives(
                "public function main<T>(): void { }\n",
                &[diag(
                    "EN0436",
                    "1:17",
                    "`main` can't be generic",
                    "the entry point is called with no type arguments",
                )],
            );
        },
    );
    h.case(
        "entry/of two overloads of `main`, the valid one is the entry and the other EN0436",
        || {
            let r = src(
                "public function main(): i32 { return 0; }\npublic function main(x: i32): i32 { return x; }\n",
            );
            assert_eq!(
                diags(&r),
                [diag(
                    "EN0436",
                    "2:17",
                    "`main` takes no parameters",
                    "this `main` takes 1 parameter",
                )]
            );
        },
    );
    h.case(
        "entry/EN0314: `function main` beside top-level statements",
        || {
            let r = src("console.log(\"hi\");\npublic function main(): void { }\n");
            assert_eq!(
                r.rendered(),
                "warning[EN0314]: `main` beside top-level statements is not the entry point
 --> src/main.en:2:17
  |
2 | public function main(): void { }
  |                 ^^^^ the top-level statements run instead
  |
help: call `main()` from the statements, or move the statements into `main`
"
            );
            assert_eq!(entry(&r), Entry::Statements(main_module(&r)));
            // A local function named `main` among the statements is beside them too,
            // whatever its signature.
            let r = src("function main(n: i64): i64 { return n; }\nconsole.log(main(1));\n");
            assert_eq!(
                diags(&r),
                [diag(
                    "EN0314",
                    "1:10",
                    "`main` beside top-level statements is not the entry point",
                    "the top-level statements run instead",
                )]
            );
            assert_eq!(entry(&r), Entry::Statements(main_module(&r)));
        },
    );
    h.case(
        "entry/a file with neither statements nor `main` has no entry",
        || {
            let r = src("public function helper(): void { }\n");
            r.clean();
            assert_eq!(entry(&r), Entry::None);
        },
    );
    h.case("entry/only the entry module's `main` counts", || {
        let r = run(&[
            (
                "src/main.en",
                "import { main } from \"./other\";\npublic function start(): void { }\n",
            ),
            (
                "src/other.en",
                "public function main(): i64 { return 0; }\n",
            ),
        ]);
        r.clean();
        assert_eq!(entry(&r), Entry::None);
    });
}
