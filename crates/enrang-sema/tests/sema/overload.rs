//! Overloads (plan d.9's `overload.rs`; SPEC 4.14 S:829, A:888; owner 4A): a
//! candidate matches when every argument fits its parameter as it is or through a
//! chain of 4.5, never a numeric conversion, a literal keeping its default; among
//! the matches (1) non-generic beats generic, (2) no chain beats a chain, (3) the
//! more specific generic wins; no match or a tie is EN0451 with a note per
//! candidate; overloads one call cannot tell apart are EN0450. `VI-07-overloads`
//! (T:1052) asserts which overload each call runs by the callee's path.

use enrang_hir::{self as hir, Adjust, Callee, ExprKind, StmtKind};
use enrang_sema::LibSource;
use enrang_testkit::{Harness, extract_cases};

use crate::paths::{body, diags, main_en, main_lib};
use crate::support::{Run, run_with};

/// The codes stage 4A reports (plan h.1).
pub const GENERIC_CODES: &[&str] = &[
    "EN0221", "EN0309", "EN0419", "EN0433", "EN0434", "EN0445", "EN0447", "EN0449", "EN0450",
    "EN0451", "EN0703", "EN0805", "EN0908",
];

pub fn register(h: &mut Harness) {
    picks(h);
    ranking(h);
    rejects(h);
    declarations(h);
    spec(h);
    review(h);
}

/// The path of the definition a call runs.
pub fn callee_path(r: &Run, e: &hir::Expr) -> String {
    let def = match &e.kind {
        ExprKind::Call { callee, .. } => match callee {
            Callee::Fn(f) | Callee::Super(f) => f.def,
            Callee::BoundMember { found, .. } => *found,
            other => panic!("{other:?}"),
        },
        ExprKind::New { ctor, .. } => *ctor,
        other => panic!("not a call: {other:?}"),
    };
    r.tcx.def(def).path.to_string()
}

/// Every call that is an expression statement of `b`, in order.
pub fn stmt_calls(b: &hir::Body) -> Vec<&hir::Expr> {
    b.root
        .stmts
        .iter()
        .filter_map(|s| match &s.kind {
            StmtKind::Expr(e) => Some(e),
            _ => None,
        })
        .collect()
}

/// The paths of the calls that are expression statements of `path`'s body.
fn picked(r: &Run, path: &str) -> Vec<String> {
    stmt_calls(body(r, path))
        .into_iter()
        .map(|e| callee_path(r, e))
        .collect()
}

const DESCRIBE: &str = "public function describe(n: int): string { return `number ${n}`; }
public function describe(s: &string): string { return `text ${s}`; }
public function describe(n: i64): string { return `i64`; }
";

fn picks(h: &mut Harness) {
    h.case(
        "overload/S:829: `describe(42)`, `describe(\"hi\")`, and `describe(5)` picks `int`",
        || {
            let r = main_lib(&format!(
                "{DESCRIBE}public function f(n: i64): void {{ describe(42); describe(\"hi\"); describe(5); describe(n); }}\n"
            ));
            r.clean();
            assert_eq!(
                picked(&r, "main::f"),
                [
                    "main::describe(int)",
                    "main::describe(&string)",
                    "main::describe(int)",
                    "main::describe(i64)",
                ]
            );
            // The string literal reaches `&string` by C13, a chain the ranking allows.
            let calls = stmt_calls(body(&r, "main::f"));
            let ExprKind::Call { args, .. } = &calls[1].kind else {
                panic!()
            };
            assert_eq!(args[0].adjust, [Adjust::LiteralDescriptor]);
        },
    );
    h.case(
        "overload/a float literal follows its default too: `f64` over `f32`",
        || {
            let r = main_en(
                "public function g(x: f32): void {}
public function g(x: f64): void {}
public function f(a: f32): void { g(1.5); g(a); }
",
            );
            r.clean();
            assert_eq!(picked(&r, "main::f"), ["main::g(f64)", "main::g(f32)"]);
        },
    );
    h.case(
        "overload/a literal takes another type only when no overload matches it at its default",
        || {
            let r = main_lib(
                "public function g(x: i64): void {}
public function g(x: &string): void {}
public function k(x: i64): void {}
public function k<T>(x: T): void {}
public function f(): void { g(1); k(5); }
",
            );
            r.clean();
            // `k(5)`: the literal at its default matches `k<T>` alone (`T := int`).
            assert_eq!(picked(&r, "main::f"), ["main::g(i64)", "main::k(T)"]);
        },
    );
    h.case(
        "overload/S:829: `sum(&f)` picks `&Slice<i64>` over `&Slice<f64>` by C18 (`SL-06-chain`)",
        || {
            let r = main_lib(
                "public function sum(xs: &Slice<i64>): i64 { return 0; }
public function sum(xs: &Slice<f64>): f64 { return 0.0; }
public function f(): void { const f: i64[3] = [1, 2, 3]; sum(&f); }
",
            );
            r.clean();
            assert_eq!(picked(&r, "main::f"), ["main::sum(&Slice<i64>)"]);
            let calls = stmt_calls(body(&r, "main::f"));
            let ExprKind::Call { args, .. } = &calls[0].kind else {
                panic!()
            };
            assert_eq!(args[0].adjust, [Adjust::FixedToSlice]);
        },
    );
    h.case(
        "overload/methods and constructors are ranked as functions are",
        || {
            let r = main_lib(
                "public class User {
  public constructor(public n: i64) {}
  public constructor(s: &string) { this.n = 0; }
  public say(n: i64): void {}
  public say(s: &string): void {}
}
public function f(): void {
  const a = new User(1);
  const b = new User(\"x\");
  a.say(\"y\");
  a.say(2);
}
",
            );
            r.clean();
            let b = body(&r, "main::f");
            let inits: Vec<String> = b
                .root
                .stmts
                .iter()
                .filter_map(|s| match &s.kind {
                    StmtKind::Let { init: Some(e), .. } => Some(callee_path(&r, e)),
                    _ => None,
                })
                .collect();
            assert_eq!(
                inits,
                ["main::User::#ctor(i64)", "main::User::#ctor(&string)"]
            );
            assert_eq!(
                picked(&r, "main::f"),
                ["main::User::say(&string)", "main::User::say(i64)"]
            );
        },
    );
    h.case(
        "overload/a subclass's overloads add to the inherited ones, with no hiding (S:829)",
        || {
            let r = main_lib(
                "public class A { public m(n: i64): void {} }
public class B extends A { public m(s: &string): void {} }
public function f(b: B): void { b.m(1); b.m(\"x\"); }
",
            );
            r.clean();
            assert_eq!(picked(&r, "main::f"), ["main::A::m", "main::B::m"]);
        },
    );
}

const VI07: &str = "public class Animal { public constructor(public name: string) {} }
public class Dog extends Animal { public constructor(name: string) { super(name); } }
public function describe(a: &Animal): void { console.log(`describe(Animal): ${a.name}`); }
public function describe<T extends Animal>(a: &T): void { console.log(`describe<T>: ${a.name}`); }
public function total(xs: &Slice<i64>): void { console.log(\"total(Slice)\"); }
public function total<T>(x: &T): void { console.log(\"total<T>\"); }
public function show<T>(x: &T): void { console.log(\"any:\", x); }
public function show<T>(x: &Slice<T>): void { console.log(\"view:\", x); }
";

fn ranking(h: &mut Harness) {
    h.case(
        "overload/`VI-07-overloads` (T:1052): which overload each call runs",
        || {
            let r = main_lib(&format!(
                "{VI07}public function main(): void {{
  const rex = new Dog(\"Rex\");
  const arr: i64[3] = [1, 2, 3];
  let sector: u8[4] = [7; 4];
  describe(&rex);
  total(&arr);
  show(sector.slice(0, 2));
  show(&sector);
}}
"
            ));
            r.clean();
            assert_eq!(
                picked(&r, "main::main"),
                [
                    // (1) non-generic beats generic, although it needs C21.
                    "main::describe(&main::Animal)",
                    // (1) again, although it needs C18 and `total<T>` none.
                    "main::total(&Slice<i64>)",
                    // (3) both generic and chain-free: `&Slice<T>` is more specific.
                    "main::show(&Slice<T>)",
                    // (2) only `show<T>(x: &T)` needs no chain.
                    "main::show(&T)",
                ]
            );
            let calls = stmt_calls(body(&r, "main::main"));
            let ExprKind::Call { args, .. } = &calls[0].kind else {
                panic!()
            };
            assert_eq!(args[0].adjust, [Adjust::Upcast]);
            // `show(&sector)` binds `T := u8[4]`, with no chain.
            let ExprKind::Call { args, callee, .. } = &calls[3].kind else {
                panic!()
            };
            assert!(args[0].adjust.is_empty());
            let Callee::Fn(f) = callee else { panic!() };
            assert_eq!(r.tcx.ty_string(r.tcx.list(f.args)[0]), "u8[4]");
        },
    );
    h.case(
        "overload/the ranking never reads the view fact: `sizeOf<T>()` in `show<T>(x: &T)`",
        || {
            let r = main_lib(&format!(
                "{}public function main(): void {{
  let sector: u8[4] = [7; 4];
  show(sector.slice(0, 2));
  show(&sector);
}}
",
                VI07.replace(
                    "console.log(\"any:\", x); }",
                    "console.log(\"any:\", x, sizeOf<T>()); }"
                )
            ));
            r.clean();
            assert_eq!(
                picked(&r, "main::main"),
                ["main::show(&Slice<T>)", "main::show(&T)"]
            );
        },
    );
    h.case(
        "overload/EN0451: `f(&a3, &b3)` ties after the three steps, listing both (T:1052)",
        || {
            let r = main_lib(
                "public function f<T>(a: &T, b: &Slice<i64>): void {}
public function f<T>(a: &Slice<i64>, b: &T): void {}
public function main(): void {
  const a3: i64[3] = [1, 2, 3];
  const b3: i64[3] = [4, 5, 6];
  f(&a3, &b3);
}
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0451]: more than one overload of `f` matches
 --> main.en:6:3
  |
6 |   f(&a3, &b3);
  |   ^^^^^^^^^^^ these arguments match more than one overload equally
  |
  = note: candidate: `f<T>(a: &T, b: &Slice<i64>): void`
  = note: candidate: `f<T>(a: &Slice<i64>, b: &T): void`
  = explain: run `enrang explain EN0451`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "overload/EN0451: `f(v, v)` on a `v: &Slice<i64>` ties with no chain (A:888)",
        || {
            let r = main_lib(
                "public function f<T>(a: &T, b: &Slice<i64>): void {}
public function f<T>(a: &Slice<i64>, b: &T): void {}
public function call(v: &Slice<i64>): void { f(v, v); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0451 3:46 more than one overload of `f` matches [these arguments match more than one overload equally]"]
            );
        },
    );
    h.case(
        "overload/(3) needs `F` more specific than `G` and not the reverse: equal ones tie",
        || {
            let r = main_lib(
                "public function f<T>(x: &T): void {}
public function f<T extends Copy>(x: &T): void {}
public function call(n: i64): void { f(&n); }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0450 2:17 a call can't tell these overloads of `f` apart [this overload]",
                    "EN0451 3:38 more than one overload of `f` matches [these arguments match more than one overload equally]",
                ]
            );
        },
    );
    h.case(
        "overload/(2) among non-generic overloads, no chain beats a chain",
        || {
            let r = main_lib(
                "public class Animal { public n: i64 = 0; }
public class Dog extends Animal {}
public function g(a: &Animal): void {}
public function g(d: &Dog): void {}
public function f(d: &Dog, a: &Animal): void { g(d); g(a); }
",
            );
            r.clean();
            assert_eq!(
                picked(&r, "main::f"),
                ["main::g(&main::Dog)", "main::g(&main::Animal)"]
            );
        },
    );
    h.case(
        "overload/two non-generic overloads that both need a chain tie: EN0451",
        || {
            let r = main_lib(
                "public class Animal { public n: i64 = 0; }
public class Mid extends Animal {}
public class Dog extends Mid {}
public function g(a: &Animal): void {}
public function g(m: &Mid): void {}
public function f(d: &Dog): void { g(d); }
",
            );
            assert_eq!(r.codes(), ["EN0451"], "{}", r.rendered());
            assert_eq!(r.diags[0].entries.len(), 2, "a note per candidate");
        },
    );
}

fn rejects(h: &mut Harness) {
    h.case(
        "overload/EN0451: no overload matches, listing every candidate",
        || {
            let r = main_lib(
                "public function h(a: &string): void {}
public function h(a: i64, b?: bool): void {}
public function main(): void { h(true); }
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0451]: no overload of `h` matches these arguments
 --> main.en:3:32
  |
3 | public function main(): void { h(true); }
  |                                ^^^^^^^ no overload takes these arguments
  |
  = note: candidate: `h(a: &string): void`
  = note: candidate: `h(a: i64, b?: bool | null): void`
  = explain: run `enrang explain EN0451`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "overload/no numeric conversion: an `i32` argument matches no `i64` overload",
        || {
            let r = main_lib(
                "public function g(x: i64): void {}
public function g(x: &string): void {}
public function f(n: i32): void { g(n); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0451 3:35 no overload of `g` matches these arguments [no overload takes these arguments]"]
            );
        },
    );
    h.case(
        "overload/an argument count no overload takes is EN0451",
        || {
            let r = main_lib(
                "public function g(x: i64): void {}
public function g(x: &string): void {}
public function f(): void { g(); g(1, 2); }
",
            );
            assert_eq!(r.codes(), ["EN0451", "EN0451"], "{}", r.rendered());
        },
    );
    h.case(
        "overload/a constructor with no matching overload names the class",
        || {
            let r = main_lib(
                "public class User {
  public constructor(public n: i64) {}
  public constructor(s: &string) { this.n = 0; }
}
public function f(): void { const u = new User(true); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0451 5:39 no constructor of `User` matches these arguments [no overload takes these arguments]"]
            );
            assert_eq!(
                r.diags[0].entries[0].text,
                "candidate: `User(n: i64)`"
            );
        },
    );
    h.case(
        "overload/an argument that fails by itself reports its own error, not EN0451",
        || {
            let r = main_lib(&format!(
                "{DESCRIBE}public function f(): void {{ describe(missing); describe(1, nope); }}\n"
            ));
            assert_eq!(
                diags(&r),
                [
                    "EN0301 4:38 cannot find `missing` in this scope [not found]",
                    "EN0301 4:60 cannot find `nope` in this scope [not found]",
                ]
            );
        },
    );
    h.case(
        "overload/an error inside an argument whose type survives it is its own, not EN0451",
        || {
            // `k(&x.left)?` is `i64` whatever `x.left` is, so its EN0303, which every
            // overload of `Ok` meets, is reported alone (SPEC S3's shape).
            let r = main_lib(
                "public function k(s: &i64): Result<i64> { return Ok(*s); }
public function f(x: i64): Result<i64> { return Ok(k(&x.left)?); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0303 2:57 `i64` has no member `left` [no such member]"]
            );
            // The arrow's EN0409 comes from typing it with no expected type, which
            // the first overload gives it: no overload matches, for the `1`.
            let r = main_lib(
                "public function f(a: (fn(x: i64) => i64)[], y: bool): void {}
public function f(s: &string, y: bool): void {}
public function g(): void { f([(x) => x], 1); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0451 3:29 no overload of `f` matches these arguments [no overload takes these arguments]"]
            );
        },
    );
}

fn declarations(h: &mut Harness) {
    h.case(
        "overload/EN0450: overloads that differ only in their return type",
        || {
            let r = main_lib(
                "public function f(a: i64): void {}
public function f(a: i64): i64 { return a; }
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0450]: a call can't tell these overloads of `f` apart
 --> main.en:2:17
  |
1 | public function f(a: i64): void {}
  |                 - and this one
2 | public function f(a: i64): i64 { return a; }
  |                 ^ this overload
  |
  = note: they differ only in their return type
  = explain: run `enrang explain EN0450`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "overload/EN0450: one call could match two through a default parameter",
        || {
            let r = main_lib(
                "public function g(a: i64, b: i64 = 2): void {}
public function g(a: i64): void {}
public function k(a: &string, b?: bool): void {}
public function k(a: &string, c?: i64): void {}
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0450 2:17 a call can't tell these overloads of `g` apart [this overload]",
                    "EN0450 4:17 a call can't tell these overloads of `k` apart [this overload]",
                ]
            );
            assert_eq!(
                r.diags[0].entries[0].text,
                "a call with 1 argument matches both, through a default parameter"
            );
        },
    );
    h.case(
        "overload/EN0450: same parameters, methods and constructors too",
        || {
            let r = main_lib(
                "public class C {
  public constructor(a: i64) {}
  public constructor(b: i64) {}
  public m(x: &string): void {}
  public m(y: &string): bool { return true; }
}
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0450 3:10 a call can't tell these constructors of `C` apart [this overload]",
                    "EN0450 5:10 a call can't tell these overloads of `m` apart [this overload]",
                ]
            );
            assert_eq!(r.diags[0].entries[0].text, "they take the same parameters");
        },
    );
    h.case(
        "overload/overloads a call tells apart, generic ones included, are no EN0450",
        || {
            let r = main_lib(
                "public function g(a: i64): void {}
public function g(a: &string): void {}
public function g(a: i64, b: i64): void {}
public function s<T>(x: &T): void {}
public function s<T>(x: &Slice<T>): void {}
public class C { public m(a: i64): void {} public static m(a: &string): void {} }
",
            );
            r.clean();
        },
    );
}

fn spec(h: &mut Harness) {
    h.case(
        "overload/SPEC's programs report none of 4A's codes beyond what their cases expect",
        || {
            let doc =
                std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/../../docs/SPEC.md"))
                    .expect("SPEC");
            let cases = extract_cases(&doc).expect("the cases extract");
            let ours = |code: &str| GENERIC_CODES.contains(&code);
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
                let r = run_with(&files, LibSource::Embedded, target);
                let reported: Vec<String> = r
                    .diags
                    .iter()
                    .map(|d| d.code.name().to_owned())
                    .filter(|c| ours(c))
                    .collect();
                let expected: Vec<String> = case
                    .stderr
                    .text
                    .lines()
                    .filter_map(|l| l.strip_prefix("error["))
                    .filter_map(|l| l.split_once(']'))
                    .map(|(code, _)| code.to_owned())
                    .filter(|c| ours(c))
                    .collect();
                assert_eq!(reported, expected, "{}: {}", case.id, r.rendered());
                seen += 1;
            }
            assert!(seen >= 30, "the tour, ownership, G and S cases: {seen}");
        },
    );
}

/// Stage 6's review fixes of overload selection.
fn review(h: &mut Harness) {
    h.case(
        "overload/S:829: an argument that needs an expected type does not hide the EN0451 another one causes",
        || {
            let r = main_en(
                "public function describe(n: int): string { return \"n\"; }
public function describe(s: &string): string { return \"s\"; }
public function apply(f: fn(n: int) => string, x: int): void { }
public function apply(f: fn(s: &string) => string, x: &string): void { }
public function g(): void { apply(describe, true); apply(describe, 1); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0451 5:29 no overload of `apply` matches these arguments [no overload takes these arguments]"]
            );
        },
    );
    h.case(
        "overload/a `static` and an instance method with one parameter list: each call finds its own (mutant M06)",
        || {
            let r = main_en(
                "public class C {
  public static f(a: i64): i64 { return 1; }
  public f(a: i64): string { return \"x\"; }
}
public function g(): void { const a: i64 = C.f(1); const c = new C {}; const b: string = c.f(1); }
",
            );
            r.clean();
        },
    );
}
