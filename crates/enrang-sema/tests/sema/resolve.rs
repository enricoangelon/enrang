//! Resolution (plan d.3): item collection and paths, the binding rule of SPEC 4.12,
//! re-exports, child modules and namespaces, the prelude, the names bodies write,
//! top-level variables and local functions, "did you mean", the deferred names of
//! SPEC 16, and the codes: EN0301, EN0302, EN0305, EN0307, EN0311, EN0313, EN1003,
//! EN1004, EN1011, EN1012, EN1019, EN1026-EN1029, EN1033.

use enrang_hir::{DefKind, Entry, LangItem, TestItemKind, Vis};
use enrang_testkit::Harness;

use crate::support::{run, run_with};

/// The codes the front reports (plan h.1, stage 2C).
const FRONT_CODES: &[&str] = &[
    "EN0301", "EN0302", "EN0304", "EN0305", "EN0307", "EN0309", "EN0311", "EN0312", "EN0313",
    "EN0406", "EN0408", "EN0409", "EN0417", "EN0437", "EN0439", "EN0454", "EN0456", "EN0702",
    "EN0705", "EN0802", "EN0806", "EN0808", "EN0814", "EN0815", "EN0816", "EN0817", "EN0819",
    "EN0826", "EN0827", "EN1003", "EN1004", "EN1011", "EN1012", "EN1014", "EN1019", "EN1026",
    "EN1027", "EN1028", "EN1029", "EN1030", "EN1033",
];

pub fn register(h: &mut Harness) {
    h.case("resolve/every item and member has its path", || {
        let r = run(&[(
            "src/main.en",
            "public class Animal {
  public name: string;
  public constructor(n: string) { }
  public speak(): string { return \"\"; }
  public destructor() { }
}
public enum Dir { Up, Down }
public interface Speaker { speak(): string; }
private type Ints = i64[];
public const LIMIT: i64 = 3;
public function main(): void { }
",
        )]);
        r.clean();
        for (path, kind) in [
            ("src/main::Animal::#ctor", DefKind::Ctor),
            ("src/main::Animal::speak", DefKind::Method),
            ("src/main::Animal::#dtor", DefKind::Dtor),
            ("src/main::Speaker::speak", DefKind::Method),
            ("src/main::Ints", DefKind::TypeAlias),
            ("src/main::LIMIT", DefKind::Const),
            ("src/main::main", DefKind::Fn),
        ] {
            assert_eq!(r.tcx.def(r.def(path)).kind, kind, "{path}");
        }
        let animal = r.def("src/main::Animal");
        assert!(matches!(r.tcx.def(animal).kind, DefKind::Adt(_)));
        let speak = r.def("src/main::Animal::speak");
        assert_eq!(r.tcx.def(speak).parent, Some(animal));
        assert_eq!(r.tcx.def(r.def("src/main::Ints")).vis, Vis::Private);
        let program = r.program.as_ref().expect("checked");
        assert_eq!(program.entry, Entry::Main(r.def("src/main::main")));
    });
    h.case("resolve/named imports bind public items, aliases included", || {
        let r = run(&[
            ("src/main.en", "import { Point, origin as zero } from \"./geo\";\npublic function f(p: Point): Point { return zero(); }\n"),
            ("src/geo.en", "public class Point { public x: i64; }\npublic function origin(): Point { return new Point { x: 0 }; }\n"),
        ]);
        r.clean();
        assert_eq!(r.sig("src/main::f"), "(p: Point) => Point");
    });
    h.case("resolve/EN0311: importing a private item", || {
        let r = run(&[
            ("src/main.en", "import { Helper } from \"./user\";\n"),
            ("src/user.en", "private class Helper { }\n"),
        ]);
        assert_eq!(r.codes(), ["EN0311"]);
        assert_eq!(r.messages(), ["`Helper` is private to `user.en`"]);
    });
    h.case(
        "resolve/EN0305: a name that is neither an item nor a child module",
        || {
            let r = run(&[
                ("src/main.en", "import { nothing } from \"./geo\";\n"),
                ("src/geo.en", "public const x: i64 = 1;\n"),
            ]);
            assert_eq!(r.codes(), ["EN0305"]);
            assert_eq!(
                r.messages(),
                ["`nothing` is neither an item nor a module of `./geo`"]
            );
        },
    );
    h.case("resolve/re-exports resolve along a chain", || {
        let r = run(&[
            (
                "src/main.en",
                "import { Point } from \"./a\";\npublic function f(p: Point): void { }\n",
            ),
            ("src/a.en", "public import { Point } from \"./b\";\n"),
            ("src/b.en", "public import { Point } from \"./c\";\n"),
            ("src/c.en", "public class Point { public x: i64; }\n"),
        ]);
        r.clean();
        assert_eq!(r.sig("src/main::f"), "(p: Point) => void");
        let point = r.def("src/c::Point");
        let param = r.tcx.sig(r.def("src/main::f")).params[0].ty;
        assert!(
            matches!(r.tcx.kind(param), enrang_hir::TyKind::Adt(a, _) if r.tcx.adt(a).def == point)
        );
    });
    h.case("resolve/a namespace import names types in paths", || {
        let r = run(&[
            (
                "src/main.en",
                "import * as geo from \"./geo\";\npublic function f(p: geo.Point): void { }\n",
            ),
            (
                "src/geo.en",
                "public class Point { public x: i64; }\nprivate class Hidden { }\n",
            ),
        ]);
        r.clean();
        assert_eq!(r.sig("src/main::f"), "(p: Point) => void");
        let r = run(&[
            (
                "src/main.en",
                "import * as geo from \"./geo\";\npublic function f(p: geo.Hidden): void { }\n",
            ),
            ("src/geo.en", "private class Hidden { }\n"),
        ]);
        assert_eq!(r.codes(), ["EN0311"]);
        assert_eq!(r.messages(), ["`Hidden` is private to `geo.en`"]);
        assert_eq!(r.map.text(r.diags[0].primary.span), "Hidden");
    });
    h.case(
        "resolve/the prelude: core everywhere, alloc outside core",
        || {
            let r = run(&[(
                "src/main.en",
                "public function f(a: string, b: Box<i64>, c: Result<i64>): void { }\n",
            )]);
            r.clean();
            assert_eq!(
                r.sig("src/main::f"),
                "(a: string, b: Box<i64>, c: Result<i64>) => void"
            );
            let string = r.tcx.lang(LangItem::Str);
            assert_eq!(r.tcx.def(string).path.to_string(), "core/prelude::string");
            assert!(r.tcx.lang_opt(LangItem::Boxed).is_some());
        },
    );
    h.case("resolve/own items shadow the prelude", || {
        let r = run(&[(
            "src/main.en",
            "public class Box { }\npublic function f(b: Box): void { }\n",
        )]);
        r.clean();
        assert_eq!(r.sig("src/main::f"), "(b: Box) => void");
        let param = r.tcx.sig(r.def("src/main::f")).params[0].ty;
        assert!(matches!(r.tcx.kind(param), enrang_hir::TyKind::Adt(..)));
    });
    h.case("resolve/EN0307: a name defined twice", || {
        let r = run(&[(
            "src/main.en",
            "public class A { }\npublic const A: i64 = 1;\n",
        )]);
        assert_eq!(r.codes(), ["EN0307"]);
        assert_eq!(
            r.rendered(),
            "error[EN0307]: `A` is defined twice
 --> src/main.en:2:14
  |
1 | public class A { }
  |              - the first `A` is here
2 | public const A: i64 = 1;
  |              ^ defined again here
  |
  = explain: run `enrang explain EN0307`

error: aborting due to 1 previous error
"
        );
    });
    h.case(
        "resolve/EN0307: members of one class, but not overloads",
        || {
            let r = run(&[(
                "src/main.en",
                "public class C {
  public x: i64;
  public x(): void { }
  public m(): void { }
  public m(a: i64): void { }
}
",
            )]);
            assert_eq!(r.codes(), ["EN0307"]);
        },
    );
    h.case("resolve/functions of one name are an overload set", || {
        let r = run(&[(
            "src/main.en",
            "public function describe(x: i64): string { return \"\"; }\npublic function describe(x: string): string { return \"\"; }\n",
        )]);
        r.clean();
        let mut paths: Vec<String> = r
            .tcx
            .defs()
            .filter(|(_, d)| d.kind == DefKind::Fn)
            .map(|(_, d)| d.path.to_string())
            .filter(|p| p.starts_with("src/"))
            .collect();
        paths.sort();
        assert_eq!(paths, ["src/main::describe(i64)", "src/main::describe(string)"]);
    });
    h.case("resolve/test items carry their describe path", || {
        let r = run(&[
            ("src/main.en", "public function greet(): string { return \"hi\"; }\n"),
            (
                "src/main.test.en",
                "describe(\"greet\", () => {\n  test(\"says hi\", () => { });\n  compileFails(\"bad\", raw`x`);\n});\ntest(\"alone\", () => { });\n",
            ),
        ]);
        r.clean();
        let program = r.program.as_ref().expect("checked");
        let ids: Vec<&str> = program.tests.iter().map(|t| t.id.as_str()).collect();
        assert_eq!(ids, ["greet > says hi", "greet > bad", "alone"]);
        assert!(matches!(program.tests[1].kind, TestItemKind::Compile(_)));
        assert!(program.bodies.contains_key(&program.tests[0].def));
        assert!(r.tcx.def(program.tests[0].def).test_part);
    });
    h.case("resolve/local functions and the statements body", || {
        let r = run(&[(
            "src/main.en",
            "let n = 1;\nfunction bump(): void { }\nbump();\n",
        )]);
        r.clean();
        let bump = r.def("src/main::bump");
        assert_eq!(r.tcx.def(bump).kind, DefKind::LocalFn);
        let program = r.program.as_ref().expect("checked");
        assert!(program.statements.is_some());
        assert!(program.bodies.contains_key(&bump));
        assert!(matches!(program.entry, Entry::Statements(_)));
    });
    h.case(
        "resolve/the import closure reaches extend blocks of the library",
        || {
            let r = run(&[("src/main.en", "public function f(): void { }\n")]);
            r.clean();
            let main = r.tcx.module(r.tcx.def(r.def("src/main::f")).module);
            let option = r
                .tcx
                .modules()
                .find(|(_, m)| m.path.as_str() == "core/option")
                .map(|(id, _)| id)
                .expect("core/option");
            assert!(main.closure.contains(option));
            let opt = r.tcx.mk_nullable(r.tcx.common().i64);
            let module = r.tcx.def(r.def("src/main::f")).module;
            assert!(
                r.tcx
                    .member(opt, enrang_base::intern("unwrapOr"), module)
                    .is_some()
            );
        },
    );
    h.case("resolve/G06: did you mean, at a local (byte-exact)", || {
        let r = run_with(
            &[("g06.en", "const total = 10;\nconsole.log(totl);\n")],
            enrang_sema::LibSource::Embedded,
            "x86_64-linux",
        );
        assert_eq!(
            r.rendered(),
            "error[EN0301]: cannot find `totl` in this scope
 --> g06.en:2:13
  |
1 | const total = 10;
  |       ----- a local with a similar name is declared here
2 | console.log(totl);
  |             ^^^^ not found
  |
help: did you mean `total`?
  |
2 | console.log(total);
  |             ~~~~~
  = explain: run `enrang explain EN0301`

error: aborting due to 1 previous error
"
        );
    });
    h.case(
        "resolve/EN0301: no suggestion when nothing is close",
        || {
            let r = run(&[("src/main.en", "console.log(zzzzzz);\n")]);
            assert_eq!(r.codes(), ["EN0301"]);
            assert_eq!(r.messages(), ["cannot find `zzzzzz` in this scope"]);
            assert!(r.diags[0].helps.is_empty() && r.diags[0].secondary.is_empty());
        },
    );
    h.case("resolve/EN0301: the candidate's kind labels the place it is declared", || {
        let cases: &[(&str, &str, &str)] = &[
            ("public function total(): i64 { return 1; }\npublic function g(): i64 { return totl(); }\n", "total", "a function with a similar name is declared here"),
            ("public class Point { }\npublic function g(): void { Pont; }\n", "Point", "a class with a similar name is declared here"),
            ("public const LIMIT: i64 = 3;\npublic function g(): i64 { return LIMT; }\n", "LIMIT", "a constant with a similar name is declared here"),
            ("public function g(count: i64): i64 { return cont; }\n", "count", "a local with a similar name is declared here"),
            ("public function g(): i64 { const items = 1; { return itms; } }\n", "items", "a local with a similar name is declared here"),
        ];
        for (src, found, label) in cases {
            let r = run(&[("src/main.en", src)]);
            assert_eq!(r.codes(), ["EN0301"], "{src}");
            let diag = &r.diags[0];
            assert_eq!(diag.helps[0].message, format!("did you mean `{found}`?"), "{src}");
            assert_eq!(diag.secondary[0].text, *label, "{src}");
            assert_eq!(r.map.text(diag.secondary[0].span), *found, "{src}");
        }
        let r = run(&[
            ("src/main.en", "import { helper } from \"./h\";\npublic function g(): void { helpr(); }\n"),
            ("src/h.en", "public function helper(): void { }\n"),
        ]);
        assert_eq!(r.diags[0].secondary[0].text, "a similar name is imported here");
        assert_eq!(r.map.text(r.diags[0].secondary[0].span), "helper");
        // A form or a library name gets the help alone.
        let r = run(&[("src/main.en", "consle.log(1);\n")]);
        assert_eq!(r.diags[0].helps[0].message, "did you mean `console`?");
        assert!(r.diags[0].secondary.is_empty());
    });
    h.case("resolve/EN0302: did you mean, over the names of types", || {
        let r = run(&[("src/main.en", "public function f(x: strng): void { }\n")]);
        assert_eq!(r.codes(), ["EN0302"]);
        assert_eq!(r.diags[0].helps[0].message, "did you mean `string`?");
        let r = run(&[("src/main.en", "public class Point { }\npublic function f(x: Pont): void { }\npublic function Pnt(): void { }\n")]);
        assert_eq!(r.diags[0].helps[0].message, "did you mean `Point`?");
        assert_eq!(r.diags[0].secondary[0].text, "a class with a similar name is declared here");
        let r = run(&[("src/main.en", "public function f<Item>(x: Itme): void { }\n")]);
        assert_eq!(r.diags[0].helps[0].message, "did you mean `Item`?");
        assert_eq!(r.diags[0].secondary[0].text, "a type parameter with a similar name is declared here");
    });
    h.case("resolve/the deferred names of SPEC 16 get their own codes", || {
        let cases: &[(&str, &str, &str)] = &[
            ("public function f(w: Worker): void { }\n", "EN1003", "threads are not supported yet"),
            ("spawn(1);\n", "EN1003", "threads are not supported yet"),
            ("public function f(r: Rc<i64>): void { }\n", "EN1004", "shared ownership types are not supported yet"),
            ("public function f(c: RefCell<i64>): void { }\n", "EN1004", "shared ownership types are not supported yet"),
            ("public function f(s: &str): void { }\n", "EN1011", "range indexing is not supported yet"),
            ("public function f(m: Map<string, i64>): void { }\n", "EN1012", "`Map` and `Set` are not supported yet"),
            ("public function f(m: Set<i64>): void { }\n", "EN1012", "`Map` and `Set` are not supported yet"),
            ("public function f(c: char): void { }\n", "EN1019", "a character type is not supported yet"),
            ("console.log(Math.max(1, 2));\n", "EN1026", "`Math` does not exist"),
            ("console.log(JSON.parse(\"1\"));\n", "EN1027", "`JSON` is not supported yet"),
            ("fetch(\"x\");\n", "EN1028", "network APIs are not supported yet"),
            ("WebSocket.open();\n", "EN1028", "network APIs are not supported yet"),
            ("Object.keys(1);\n", "EN1029", "reflection is not supported yet"),
            ("Reflect.get(1);\n", "EN1029", "reflection is not supported yet"),
            ("transmute(1);\n", "EN1033", "unchecked reinterpretation is not supported yet"),
        ];
        for (src, code, message) in cases {
            let r = run(&[("src/main.en", src)]);
            assert_eq!(r.codes(), [*code], "{src}");
            assert_eq!(r.messages(), [*message], "{src}");
            assert_eq!(r.diags[0].entries.len(), 1, "one note: {src}");
        }
        let r = run(&[("src/main.en", "console.log(Math.sqrt(2.0));\n")]);
        assert_eq!(
            r.rendered(),
            "error[EN1026]: `Math` does not exist
 --> src/main.en:1:13
  |
1 | console.log(Math.sqrt(2.0));
  |             ^^^^ no such namespace
  |
  = note: the math functions are methods of the number types, and constants such as `PI` are read through the type's name.
help: `x.sqrt()`, `f64.PI`, `a.max(b)`
  = explain: run `enrang explain EN1026`

error: aborting due to 1 previous error
"
        );
    });
    h.case(
        "resolve/a program's own `Map` wins over the deferred name",
        || {
            let r = run(&[(
                "src/main.en",
                "public class Map { }\npublic function f(m: Map): Map { return m; }\n",
            )]);
            r.clean();
        },
    );
    h.case("resolve/a child module binds a namespace, in type paths too", || {
        let r = run(&[
            ("src/main.en", "import { serial } from \"./drivers\";\nimport * as d from \"./drivers\";\npublic function f(p: serial.Port, q: d.vga.Screen): void { }\n"),
            ("src/drivers/serial.en", "public class Port { }\n"),
            ("src/drivers/vga.en", "public class Screen { }\n"),
        ]);
        r.clean();
        assert_eq!(r.sig("src/main::f"), "(p: Port, q: Screen) => void");
        let r = run(&[
            ("src/main.en", "import { nothing } from \"./drivers\";\n"),
            ("src/drivers/serial.en", "public class Port { }\n"),
        ]);
        assert_eq!(r.messages(), ["`nothing` is neither an item nor a module of `./drivers`"]);
    });
    h.case("resolve/a local shadows a namespace and an item", || {
        let r = run(&[
            ("src/main.en", "import * as geo from \"./geo\";\npublic const n: i64 = 1;\npublic function f(): i64 { const geo = 1; const n = 2; return geo + n; }\n"),
            ("src/geo.en", "public class Point { }\n"),
        ]);
        r.clean();
    });
    h.case(
        "resolve/EN0307: one name bound twice by imports, or by an import and an item",
        || {
            let r = run(&[
                (
                    "src/main.en",
                    "import { A } from \"./a\";\nimport { A } from \"./b\";\n",
                ),
                ("src/a.en", "public class A { }\n"),
                ("src/b.en", "public class A { }\n"),
            ]);
            assert_eq!(r.codes(), ["EN0307"]);
            assert_eq!(r.map.loc(r.diags[0].primary.span.lo).line, 2);
            let r = run(&[
                (
                    "src/main.en",
                    "import { A } from \"./a\";\npublic class A { }\n",
                ),
                ("src/a.en", "public class A { }\n"),
            ]);
            assert_eq!(
                r.rendered(),
                "error[EN0307]: `A` is defined twice
 --> src/main.en:2:14
  |
1 | import { A } from \"./a\";
  |          - the first `A` is here
2 | public class A { }
  |              ^ defined again here
  |
  = explain: run `enrang explain EN0307`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case("resolve/EN0307: locals and parameters declared twice in one block", || {
        let r = run(&[("src/main.en", "public function f(a: i64, a: i64): i64 { const b = 1; const b = 2; { const b = 3; } return b; }\n")]);
        assert_eq!(r.codes(), ["EN0307", "EN0307"]);
        assert_eq!(r.messages(), ["`a` is defined twice", "`b` is defined twice"]);
        let r = run(&[("src/main.en", "const x = 1;\nconst x = 2;\n")]);
        assert_eq!(r.codes(), ["EN0307"]);
    });
    h.case("resolve/EN0313: a local function above the variable it reads", || {
        let r = run(&[(
            "src/main.en",
            "function report(): void { console.log(`count = ${count}`); }\nlet count = 0;\nreport();\n",
        )]);
        assert_eq!(
            r.rendered(),
            "error[EN0313]: `count` is a top-level variable, which `report` can't see
 --> src/main.en:1:50
  |
1 | function report(): void { console.log(`count = ${count}`); }
  |                                                  ^^^^^ `count` is declared below `report`
2 | let count = 0;
  |     ----- `count` is declared here
  |
  = explain: run `enrang explain EN0313`

error: aborting due to 1 previous error
"
        );
    });
    h.case("resolve/EN0313: class methods and item functions never see top-level variables", || {
        let r = run(&[(
            "src/main.en",
            "let count = 0;\nconsole.log(count);\npublic class C {\n  public m(): i64 { return count; }\n}\npublic function f(): i64 { return count + 1; }\n",
        )]);
        assert_eq!(r.codes(), ["EN0313", "EN0313"]);
        assert_eq!(
            r.messages(),
            [
                "`count` is a top-level variable, which `C` can't see",
                "`count` is a top-level variable, which `f` can't see"
            ]
        );
        assert_eq!(r.diags[0].primary.text, "only the top-level statements and the local functions below it see it");
        let r = run(&[("src/main.en", "console.log(args);\npublic class C { public m(): void { console.log(args); } }\n")]);
        assert_eq!(r.codes(), ["EN0313"]);
        assert_eq!(r.diags[0].helps[0].message, "`os.args()` gives the arguments anywhere");
    });
    h.case("resolve/a local function sees the top-level variables declared above it", || {
        let r = run(&[(
            "src/main.en",
            "let count = 0;\nfunction inc(): void { count += 1; }\ninc();\nconsole.log(count);\ninc();\nfunction show(): void { console.log(args); }\nshow();\n",
        )]);
        r.clean();
    });
    h.case("resolve/EN0313: a local function with hidden arguments called from a class (MR-4)", || {
        let r = run(&[(
            "src/main.en",
            "let q: i64[] = [];\nfunction grow(): void { for (let i = 0; i < 100; i++) { q.push(i); } }\nfunction relay(): void { grow(); }\nrelay();\nfunction plain(): i64 { return 1; }\npublic class K {\n  public m(): i64 { grow(); relay(); return plain(); }\n}\n",
        )]);
        assert_eq!(r.codes(), ["EN0313", "EN0313"]);
        assert_eq!(
            r.messages(),
            [
                "`grow` uses top-level variables, so only the top-level statements can call it",
                "`relay` uses top-level variables, so only the top-level statements can call it"
            ]
        );
        // `relay` writes no variable: its hidden arguments are `grow`'s.
        assert_eq!(r.diags[1].secondary[0].text, "`relay` uses `q`, a top-level variable");
        assert_eq!(r.map.loc(r.diags[0].primary.span.lo).line, 7);
    });
    h.case("resolve/a `.test.en` part sees neither local functions nor top-level variables", || {
        let r = run(&[
            ("src/main.en", "let count = 0;\nfunction bump(): void { count += 1; }\nbump();\nprivate function helper(): i64 { return 1; }\n"),
            ("src/main.test.en", "test(\"x\", () => { helper(); bump(); console.log(count); });\n"),
        ]);
        assert_eq!(r.codes(), ["EN0301", "EN0301"]);
        assert_eq!(
            r.messages(),
            ["cannot find `bump` in this scope", "cannot find `count` in this scope"]
        );
    });
    h.case("resolve/a compile-time constant is visible everywhere", || {
        let r = run(&[(
            "src/main.en",
            "console.log(LIMIT);\npublic const LIMIT: i64 = 3;\npublic class C { public m(): i64 { return LIMIT; } }\n",
        )]);
        r.clean();
    });
    h.case(
        "resolve/SPEC's programs: the front reports only what their cases expect of it",
        || {
            let doc =
                std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/../../docs/SPEC.md"))
                    .expect("SPEC");
            let cases = enrang_testkit::extract_cases(&doc).expect("the cases extract");
            let ours = |code: &str| FRONT_CODES.contains(&code);
            let mut seen = 0;
            for case in cases {
                if case.files.is_empty() || case.files.iter().any(|f| !f.name.ends_with(".en")) {
                    continue;
                }
                let target = ["i386-none", "i386-linux", "x86_64-none"]
                    .into_iter()
                    .find(|t| case.cmd.contains(t))
                    .unwrap_or("x86_64-linux");
                let files: Vec<(&str, &str)> = case
                    .files
                    .iter()
                    .map(|f| (f.name.as_str(), f.contents.as_str()))
                    .collect();
                let r = run_with(&files, enrang_sema::LibSource::Embedded, target);
                let reported: Vec<String> = r.codes().into_iter().filter(|c| ours(c)).collect();
                let expected: Vec<String> = case
                    .stderr
                    .text
                    .lines()
                    .filter_map(|l| l.split_once('[').and_then(|(_, rest)| rest.split_once(']')))
                    .map(|(code, _)| code.to_owned())
                    .filter(|c| ours(c))
                    .collect();
                assert_eq!(reported, expected, "{}: {}", case.id, r.rendered());
                seen += 1;
            }
            assert!(seen >= 30, "the tour, ownership, G and S cases: {seen}");
        },
    );
    review_cases(h);
}

/// The cases of stage 6's front review (`fix-2`): each fails without its fix.
fn review_cases(h: &mut Harness) {
    h.case(
        "resolve/EN0307 between imports follows source order, not binding rounds",
        || {
            let r = run(&[
                (
                    "main.en",
                    "import { X } from \"./a\";\nimport { X } from \"./c\";\n",
                ),
                ("a.en", "public import { X } from \"./b\";\n"),
                ("b.en", "public class X {}\n"),
                ("c.en", "public class X {}\n"),
            ]);
            assert_eq!(
                r.rendered(),
                "error[EN0307]: `X` is defined twice
 --> main.en:2:10
  |
1 | import { X } from \"./a\";
  |          - the first `X` is here
2 | import { X } from \"./c\";
  |          ^ defined again here
  |
  = explain: run `enrang explain EN0307`

error: aborting due to 1 previous error
"
            );
            // A namespace binds no earlier than a named import before it.
            let r = run(&[
                (
                    "main.en",
                    "import { X } from \"./a\";\nimport * as X from \"./c\";\n",
                ),
                ("a.en", "public import { X } from \"./b\";\n"),
                ("b.en", "public class X {}\n"),
                ("c.en", "public class Y {}\n"),
            ]);
            assert_eq!(r.codes(), ["EN0307"]);
            assert_eq!(r.map.loc(r.diags[0].primary.span.lo).line, 2);
            assert_eq!(r.map.loc(r.diags[0].secondary[0].span.lo).line, 1);
        },
    );
    h.case("resolve/EN0307: a second destructor", || {
        let r = run(&[(
            "main.en",
            "public class A {\n  public destructor() {}\n  public  destructor() {}\n}\n",
        )]);
        assert_eq!(
            r.rendered(),
            "error[EN0307]: `destructor` is defined twice
 --> main.en:3:11
  |
2 |   public destructor() {}
  |          ---------- the first `destructor` is here
3 |   public  destructor() {}
  |           ^^^^^^^^^^ defined again here
  |
  = explain: run `enrang explain EN0307`

error: aborting due to 1 previous error
"
        );
        let class = r.tcx.adt_of(r.def("main::A")).expect("a class");
        let dtor = r
            .tcx
            .adt(class)
            .as_class()
            .expect("a class")
            .dtor
            .expect("one");
        assert_eq!(r.map.loc(r.tcx.def(dtor).name_span.lo).line, 2);
    });
    h.case(
        "resolve/EN0307: a body's own `let` redeclares a parameter",
        || {
            for (src, line) in [
                ("public function f(x: i32): void { let x = 2; }\n", 1),
                (
                    "public function f(): void {\n  const g = (y: i32) => { let y = 2; };\n}\n",
                    2,
                ),
                (
                    "public class C {\n  public m(a: i64): void { const a = 1; }\n}\n",
                    2,
                ),
                (
                    "public class C {\n  public constructor(a: i64) { let a = 1; }\n}\n",
                    2,
                ),
                (
                    "function local(n: i64): void { let n = 1; }\nlocal(1);\n",
                    1,
                ),
            ] {
                let r = run(&[("main.en", src)]);
                assert_eq!(r.codes(), ["EN0307"], "{src}");
                let diag = &r.diags[0];
                assert_eq!(r.map.loc(diag.primary.span.lo).line, line, "{src}");
                assert_eq!(diag.primary.text, "defined again here");
                assert!(diag.secondary[0].span.lo < diag.primary.span.lo, "{src}");
            }
            // A nested block may shadow a parameter, as in TypeScript.
            run(&[(
                "main.en",
                "public function f(x: i32): void { { let x = 2; } for (const x of [1]) { } }\n",
            )])
            .clean();
        },
    );
    h.case(
        "resolve/a type path through a namespace: private members and did-you-mean",
        || {
            let r = run(&[
                ("main.en", "import * as u from \"./u\";\npublic function f(p: u.Helper): void {}\n"),
                ("u.en", "private class Helper {}\n"),
            ]);
            assert_eq!(
                r.rendered(),
                "error[EN0311]: `Helper` is private to `u.en`
 --> main.en:2:24
  |
2 | public function f(p: u.Helper): void {}
  |                        ^^^^^^ a private item
  |
  = explain: run `enrang explain EN0311`

error: aborting due to 1 previous error
"
            );
            let r = run(&[
                ("main.en", "import * as d from \"./drivers\";\npublic function f(r: d.nope.X, s: d.serail.Port, t: d.serial.Prot): void {}\n"),
                ("drivers/serial.en", "public class Port {}\n"),
            ]);
            assert_eq!(r.codes(), ["EN0302", "EN0302", "EN0302"]);
            assert_eq!(
                r.messages(),
                [
                    "cannot find `nope` in `d`",
                    "cannot find `serail` in `d`",
                    "cannot find type `Prot` in `d.serial`"
                ]
            );
            let texts: Vec<&str> = r.diags.iter().map(|d| r.map.text(d.primary.span)).collect();
            assert_eq!(texts, ["nope", "serail", "Prot"]);
            assert!(r.diags[0].helps.is_empty(), "nothing near `nope`");
            assert_eq!(r.diags[1].helps[0].message, "did you mean `serial`?");
            assert_eq!(r.map.text(r.diags[1].helps[0].edits[0].span), "serail");
            assert!(r.diags[1].secondary.is_empty());
            assert_eq!(r.diags[2].helps[0].message, "did you mean `Port`?");
            assert_eq!(r.map.text(r.diags[2].helps[0].edits[0].span), "Prot");
            assert_eq!(r.diags[2].secondary[0].text, "a class with a similar name is declared here");
            // An unknown first segment is reported there, over the namespaces in scope.
            let r = run(&[
                ("main.en", "import { serial } from \"./drivers\";\npublic function f(a: serail.Port, b: nope.X, c: Map.Entry): void {}\n"),
                ("drivers/serial.en", "public class Port {}\n"),
            ]);
            assert_eq!(r.codes(), ["EN0302", "EN0302", "EN1012"]);
            assert_eq!(
                r.messages()[..2],
                ["cannot find `serail` in this scope", "cannot find `nope` in this scope"]
            );
            let texts: Vec<&str> = r.diags.iter().map(|d| r.map.text(d.primary.span)).collect();
            assert_eq!(texts, ["serail", "nope", "Map"]);
            assert_eq!(r.diags[0].helps[0].message, "did you mean `serial`?");
            assert_eq!(r.diags[0].secondary[0].text, "a similar name is imported here");
            assert!(r.diags[1].helps.is_empty());
            // A namespace is never offered as a type.
            let r = run(&[
                ("main.en", "import * as dd from \"./drivers\";\npublic function f(r: d): void {}\n"),
                ("drivers/serial.en", "public class Port {}\n"),
            ]);
            assert_eq!(r.codes(), ["EN0302"]);
            assert!(r.diags[0].helps.is_empty(), "{}", r.rendered());
        },
    );
    h.case(
        "resolve/a namespace member that its module re-exports (M35)",
        || {
            let r = run(&[
                (
                    "main.en",
                    "import * as p from \"./p\";\npublic function f(x: p.X): void {}\n",
                ),
                ("p.en", "public import { X } from \"./q\";\n"),
                ("q.en", "public class X {}\n"),
            ]);
            r.clean();
            let x = r.def("q::X");
            let param = r.tcx.sig(r.def("main::f")).params[0].ty;
            assert!(
                matches!(r.tcx.kind(param), enrang_hir::TyKind::Adt(a, _) if r.tcx.adt(a).def == x)
            );
        },
    );
    h.case(
        "resolve/the nearest prelude wins: `os` over `core` (M27)",
        || {
            let lib = crate::support::fake_lib(&[
                ("core/prelude", "public class Thing {}\n"),
                ("alloc/prelude", "// a\n"),
                ("os/linux_x64/prelude", "public class Thing {}\n"),
            ]);
            let r = run_with(
                &[("main.en", "public function f(t: Thing): void {}\n")],
                lib,
                "x86_64-linux",
            );
            r.clean();
            let param = r.tcx.sig(r.def("main::f")).params[0].ty;
            let enrang_hir::TyKind::Adt(a, _) = r.tcx.kind(param) else {
                panic!("a class");
            };
            assert_eq!(
                r.tcx.def(r.tcx.adt(a).def).path.to_string(),
                "os/linux_x64/prelude::Thing"
            );
        },
    );
}
