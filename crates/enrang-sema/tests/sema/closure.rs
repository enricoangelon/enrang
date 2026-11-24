//! Arrows and function values (plan d.12's `closure.rs`; owner 4C): an arrow typed
//! from its expected type (a closure parameter's, an annotated local's), else from
//! its annotations with its result from its body (no C19, T:902's `V-ME-09-arrow`),
//! EN0409 for a parameter nothing types, captures from the typed body, a local
//! holding a capturing arrow at its `Closure` type; the conversions C11, C12, C14-C17
//! with their adjusts and rejects: EN1007 for a capturing arrow or a closure value at
//! `fn` (S:968), EN0803 for an `unsafe`, `@requires`, `declare`, `@naked` or
//! `@interrupt` function, or a local function with hidden arguments, at a safe `fn`
//! or a closure (T:579-580, T:883), EN1006 for a function with a by-value interface
//! parameter as a function value (S:682).

use enrang_base::intern;
use enrang_hir::{self as hir, Adjust, ArrowBodyKind, ExprKind, TyKind};
use enrang_sema::LibSource;
use enrang_testkit::Harness;

use crate::paths::{body, diags, expr_stmt, init, main_lib, statements, ty};
use crate::support::{Run, run_with};

pub fn register(h: &mut Harness) {
    typing(h);
    captures(h);
    c11(h);
    c12(h);
    c14_c15(h);
    preconditions(h);
    interfaces(h);
    review(h);
}

/// The `n`th argument of the body's `stmt`th expression statement, a call.
fn arg(b: &hir::Body, stmt: usize, n: usize) -> &hir::Expr {
    match &expr_stmt(b, stmt).kind {
        ExprKind::Call { args, .. } => &args[n],
        other => panic!("not a call: {other:?}"),
    }
}

/// The local named `name` in `b`.
fn local<'b>(b: &'b hir::Body, name: &str) -> &'b hir::LocalDecl {
    let name = intern(name);
    b.locals
        .iter()
        .find(|l| l.name == Some(name))
        .unwrap_or_else(|| panic!("no local `{name}`"))
}

/// Checks `src` on `target` with the embedded library.
fn on(target: &str, src: &str) -> Run {
    run_with(&[("main.en", src)], LibSource::Embedded, target)
}

fn typing(h: &mut Harness) {
    h.case(
        "closure/an arrow takes its parameter types from the expected closure type",
        || {
            let r = main_lib(
                "const t = apply(x => x + 1, 2);
const f: fn(x: i64) => i64 = x => x * 2;
private function apply(f: (x: i64) => i64, v: i64): i64 { return f(v); }
",
            );
            r.clean();
            let b = statements(&r);
            for arrow in b.arrows.iter() {
                assert_eq!(ty(&r, b.locals[arrow.params[0]].ty), "i64");
                assert_eq!(ty(&r, arrow.ret), "i64");
            }
            assert_eq!(ty(&r, local(b, "t").ty), "i64");
        },
    );
    h.case(
        "closure/an arrow with no expected type: its annotations, its result from its body",
        || {
            let r = main_lib(
                "const id = (x: i64) => x;
const noop = () => {};
const twice = (s: &string) => { if (s.isEmpty()) { return 0; } return s.length(); };
const n: i64 = id(3);
",
            );
            r.clean();
            let b = statements(&r);
            let rets: Vec<String> = b.arrows.iter().map(|a| ty(&r, a.ret)).collect();
            assert_eq!(rets, ["i64", "void", "isize"]);
            assert_eq!(ty(&r, local(b, "id").ty), "fn(i64) => i64");
        },
    );
    h.case(
        "closure/EN0409: an arrow parameter nothing types (S:724)",
        || {
            let r = main_lib("const k = x => x;\nconst j = (x, y: i64) => y;\n");
            assert_eq!(
                r.rendered(),
                "error[EN0409]: `x` needs a type annotation
 --> main.en:1:11
  |
1 | const k = x => x;
  |           ^ nothing here gives `x` a type
  |
help: annotate it, or pass the arrow where an `fn` or closure type is expected
  = explain: run `enrang explain EN0409`

error[EN0409]: `x` needs a type annotation
 --> main.en:2:12
  |
2 | const j = (x, y: i64) => y;
  |            ^ nothing here gives `x` a type
  |
help: annotate it, or pass the arrow where an `fn` or closure type is expected
  = explain: run `enrang explain EN0409`

error: aborting due to 2 previous errors
"
            );
        },
    );
    h.case(
        "closure/an arrow no expected type fits: EN0401 once (plan choice)",
        || {
            let r = main_lib(
                "const w = apply((x, y) => x, 2);
const v = need(x => x);
const u = apply((x: string) => 1, 2);
private function apply(f: (x: i64) => i64, v: i64): i64 { return f(v); }
private function need(v: i64): i64 { return v; }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0401 1:17 mismatched types: expected `(i64) => i64`, found an arrow with 2 parameters [this arrow takes 2 parameters]",
                    "EN0401 2:16 mismatched types: expected `i64`, found an arrow [this is an arrow]",
                    "EN0401 3:17 mismatched types: expected `(i64) => i64`, found `fn(string) => i64` [this is `fn(string) => i64`]",
                ]
            );
        },
    );
    h.case(
        "closure/V-ME-09-arrow: returns decided by the body unify unwrapped, both orders (T:902)",
        || {
            let r = main_lib(
                "const check = (s: &string) => { if (s.isEmpty()) { return Err(\"empty\"); } return s.length(); };\n",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0401]: mismatched types: expected `Result<_>`, found `isize`
 --> main.en:1:82
  |
1 | const check = (s: &string) => { if (s.isEmpty()) { return Err(\"empty\"); } return s.length(); };
  |                                                                                  ^^^^^^^^^^ this is `isize`
  |                                                           ------------ the arrow's result type comes from here
  |
help: annotate the result, `(s: &string): Result<isize> => ...`, or write `Ok(s.length())`
  = explain: run `enrang explain EN0401`

error: aborting due to 1 previous error
"
            );
            let r = main_lib(
                "const check2 = (s: &string) => { if (!s.isEmpty()) { return s.trim(); } return Err(\"empty\"); };\n",
            );
            assert_eq!(
                diags(&r),
                ["EN0401 1:80 mismatched types: expected `string`, found `Result<_>` [this is `Result<_>`]"]
            );
            assert_eq!(
                r.diags[0].helps[0].message,
                "annotate the result, `(s: &string): Result<string> => ...`, or write `Ok(s.trim())`"
            );
            let r = main_lib(
                "const check3 = (s: &string): Result<isize> => { if (s.isEmpty()) { return Err(\"empty\"); } return s.length(); };\n",
            );
            r.clean();
        },
    );
    h.case(
        "closure/a return already rejected decides nothing, so nothing more is reported",
        || {
            let r = main_lib(
                "const c = (s: &string) => { if (s.isEmpty()) { return Err(\"e\"); } return nope; };\n",
            );
            assert_eq!(
                diags(&r),
                ["EN0301 1:74 cannot find `nope` in this scope [not found]"]
            );
        },
    );
    h.case(
        "closure/an arrow whose block may end where a value is due is EN0427 (plan choice)",
        || {
            let r = main_lib("const k = (x: i64): i64 => { if (x > 0) { return 1; } };\n");
            assert_eq!(
                diags(&r),
                ["EN0427 1:55 this arrow may end without returning an `i64` [the end of the body is reached without a `return`]"]
            );
        },
    );
    h.case("closure/`return` in an arrow ends the arrow", || {
        let r = main_lib(
            "private function f(): i64 { const g = (x: i64): bool => { return x > 0; }; return 1; }\n",
        );
        r.clean();
    });
}

fn captures(h: &mut Harness) {
    h.case(
        "closure/captures: each outer local once, at its first use, nested arrows included",
        || {
            let r = main_lib(
                "private function go(xs: &i64[]): void {
  let n = 0;
  let m = 1;
  each(xs, x => { n += *x; n += m; });
  run(() => { const k = 2; run(() => console.log(n + k)); });
}
private function each(xs: &i64[], f: (x: &i64) => void): void {}
private function run(f: () => void): void { f(); }
",
            );
            r.clean();
            let b = body(&r, "main::go");
            let names = |a: &hir::ArrowBody| -> Vec<String> {
                a.captures
                    .iter()
                    .map(|c| b.locals[c.local].name.expect("named").to_string())
                    .collect()
            };
            let all: Vec<Vec<String>> = b.arrows.iter().map(names).collect();
            assert_eq!(all, [vec!["n", "m"], vec!["n"], vec!["n", "k"]]);
        },
    );
    h.case(
        "closure/a local holding a capturing arrow has its `Closure` type (A:258)",
        || {
            let r = main_lib(
                "let count = 0;
const inc = () => { count += 1; };
inc();
const plain = (a: i64, b: i64) => a + b;
const p: fn(a: i64, b: i64) => i64 = plain;
",
            );
            r.clean();
            let b = statements(&r);
            assert!(matches!(r.tcx.kind(local(b, "inc").ty), TyKind::Closure(_)));
            assert!(matches!(
                r.tcx.kind(local(b, "plain").ty),
                TyKind::FnPtr(..)
            ));
            let captured = &b.arrows.iter().next().expect("an arrow").captures;
            assert_eq!(captured.len(), 1);
            assert_eq!(b.locals[captured[0].local].name, Some(intern("count")));
        },
    );
}

fn c11(h: &mut Harness) {
    h.case(
        "closure/C11: an arrow or a safe function's name at `fn(...)`",
        || {
            let r = main_lib(
                "const f: fn(x: i64) => i64 = (x: i64) => x;
const g: fn(x: i64) => i64 = double;
const s: fn() => void = solo;
function solo(): void {}
private function double(x: i64): i64 { return x * 2; }
",
            );
            r.clean();
            let b = statements(&r);
            for n in 0..3 {
                assert_eq!(init(b, n).adjust, [Adjust::FnToPtr], "declaration {n}");
            }
        },
    );
    h.case(
        "closure/C11: a generic function's name takes its types from the `fn` type",
        || {
            let r = main_lib(
                "const f: fn(x: i64) => i64 = id;\nprivate function id<T>(x: T): T { return x; }\n",
            );
            r.clean();
            let e = init(statements(&r), 0);
            assert_eq!(e.adjust, [Adjust::FnToPtr]);
            assert_eq!(ty(&r, e.ty), "fn(i64) => i64");
        },
    );
    h.case(
        "closure/EN1007: a capturing arrow at `fn(...)` (S:968)",
        || {
            let r = main_lib("let count = 0;\nconst h: fn() => void = () => { count += 1; };\n");
            assert_eq!(
                r.rendered(),
                "error[EN1007]: a function pointer cannot capture variables
 --> main.en:2:25
  |
2 | const h: fn() => void = () => { count += 1; };
  |                         ^^^^^^^^^^^^^^^^^^^^^ this arrow uses `count`
  |                                 ----- `count` is captured here
  |
  = note: an `fn` value holds no variables; only a closure parameter takes an arrow that uses them
help: Keep it in a local or pass it as a closure parameter, or pass the data explicitly
  = explain: run `enrang explain EN1007`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "closure/EN1007: a local holding a capturing arrow, or a closure parameter, at `fn(...)`",
        || {
            let r = main_lib(
                "let count = 0;
const inc = () => { count += 1; };
const g: fn() => void = inc;
private function keep(f: () => void): void { const p: fn() => void = f; }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN1007 3:25 a function pointer cannot capture variables [`inc` holds an arrow that uses `count`]",
                    "EN1007 4:70 a function pointer cannot capture variables [`f` is a closure parameter, which may use outer variables]",
                ]
            );
        },
    );
}

fn c12(h: &mut Harness) {
    h.case(
        "closure/C12: an arrow, a safe function's name or an `fn` value at a closure parameter",
        || {
            let r = main_lib(
                "const xs: i64[] = [1, 2];
xs.forEach(x => console.log(x));
xs.forEach(show);
const p: fn(x: &i64) => void = show;
xs.forEach(p);
private function show(x: &i64): void {}
",
            );
            r.clean();
            let b = statements(&r);
            for n in 0..3 {
                assert_eq!(arg(b, n, 0).adjust, [Adjust::ArrowToClosure], "call {n}");
            }
        },
    );
    h.case(
        "closure/C12 then C06: an arrow at a nullable closure parameter (OQ24-onKey)",
        || {
            let r = main_lib(
                "onKey(65);
onKey(66, k => console.log(k));
pad(); pad(3);
private function onKey(key: u8, handler?: (k: u8) => void): void {}
private function pad(width?: i64 | null): void { const w: i64 = width ?? 8; console.log(w); }
",
            );
            r.clean();
            let b = statements(&r);
            let e = arg(b, 1, 1);
            assert_eq!(e.adjust, [Adjust::ArrowToClosure, Adjust::WrapNull]);
            let ExprKind::Arrow(id) = e.kind else {
                panic!("an arrow");
            };
            assert_eq!(ty(&r, b.locals[b.arrows[id].params[0]].ty), "u8");
        },
    );
    h.case(
        "closure/C12: a local function with hidden arguments at a closure parameter captures them",
        || {
            let r = main_lib(
                "let q: i64[] = [];
run(relay);
function relay(): void { grow(); }
function grow(): void { q.push(1); }
private function run(f: () => void): void { f(); }
",
            );
            r.clean();
            assert_eq!(arg(statements(&r), 0, 0).adjust, [Adjust::ArrowToClosure]);
        },
    );
}

fn c14_c15(h: &mut Harness) {
    h.case(
        "closure/C14: a closure parameter passed on reborrows; another signature is EN0401",
        || {
            let r = main_lib(
                "private function run(f: () => void): void { f(); }
private function relay(f: () => void): void { run(f); }
",
            );
            r.clean();
            assert_eq!(
                arg(body(&r, "main::relay"), 0, 0).adjust,
                [Adjust::ClosureReborrow]
            );
            let r = main_lib(
                "private function other(f: (x: i64) => void): void {}
private function bad(f: () => void): void { other(f); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0401 2:51 mismatched types: expected `(i64) => void`, found `() => void` [this is `() => void`]"]
            );
        },
    );
    h.case(
        "closure/C15: a safe function or `fn` value at `unsafe fn(...)`; back to `fn` is EN0401",
        || {
            let r = main_lib(
                "const u: unsafe fn() => void = s;
const v: fn() => void = s;
const w: unsafe fn() => void = v;
private function s(): void {}
",
            );
            r.clean();
            let b = statements(&r);
            assert_eq!(init(b, 0).adjust, [Adjust::FnToUnsafePtr]);
            assert_eq!(init(b, 2).adjust, [Adjust::FnToUnsafePtr]);
            let r = main_lib(
                "const g: unsafe fn() => void = s;
const h: fn() => void = g;
private function s(): void {}
",
            );
            assert_eq!(
                diags(&r),
                ["EN0401 2:25 mismatched types: expected `fn() => void`, found `unsafe fn() => void` [this is `unsafe fn() => void`]"]
            );
        },
    );
}

fn preconditions(h: &mut Harness) {
    h.case(
        "closure/C16: an `unsafe function`'s name at `unsafe fn`; at a safe `fn` EN0803",
        || {
            let r = main_lib(
                "const g: unsafe fn(x: i64) => void = poke;\nprivate unsafe function poke(x: i64): void {}\n",
            );
            r.clean();
            assert_eq!(init(statements(&r), 0).adjust, [Adjust::FnToUnsafePtr]);
            let r = main_lib(
                "const f: fn(x: i64) => void = poke;\nprivate unsafe function poke(x: i64): void {}\n",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0803]: `poke` is an `unsafe function`, so it can't become a safe `fn`
 --> main.en:1:31
  |
1 | const f: fn(x: i64) => void = poke;
  |                               ^^^^ its callers must uphold what it requires
  |
help: convert it to an `unsafe fn(...)` type, which only `unsafe` code may call
  = explain: run `enrang explain EN0803`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case("closure/EN0803: `mem.set` at a safe `fn` (T:579)", || {
        let r = main_lib("const f: fn(d: *u8, v: u8, n: usize) => void = mem.set;\n");
        assert_eq!(
            diags(&r),
            ["EN0803 1:48 `mem.set` is a `declare function`, so it can't become a safe `fn` [foreign code is called only from `unsafe`]"]
        );
    });
    h.case(
        "closure/EN0803: each kind of precondition as a closure argument (T:580)",
        || {
            let r = main_lib(
                "run(bad);
run(fast);
private unsafe function bad(): void {}
@requires(\"sse2\") private function fast(): void {}
private function run(f: () => void): void { f(); }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0803 1:5 `bad` is an `unsafe function`, so it can't become a closure [its callers must uphold what it requires]",
                    "EN0803 2:5 `fast` has `@requires`, so it can't become a closure [it runs only where the CPU features it requires were checked]",
                ]
            );
            let r = on(
                "x86_64-windows",
                "run(ext);
@dll(\"k.dll\") private declare function ext(): void;
private function run(f: () => void): void { f(); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0803 1:5 `ext` is a `declare function`, so it can't become a closure [foreign code is called only from `unsafe`]"]
            );
            let r = on(
                "i386-none",
                "@naked private unsafe function nk(): void { asm(\"ret\"); }
@interrupt private function onTimer(frame: &InterruptFrame): void {}
private function run(f: () => void): void { f(); }
private function hear(f: (frame: &InterruptFrame) => void): void {}
@entry private function kmain(boot: &BootInfo): never { run(nk); hear(onTimer); for (;;) {} }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0803 5:61 `nk` is `@naked`, so it can't become a closure [a naked function has no frame a safe call could rely on]",
                    "EN0803 5:71 `onTimer` is an `@interrupt` function, so it can only become an `InterruptHandler` [the CPU calls it, never code]",
                ]
            );
        },
    );
    h.case(
        "closure/C17: an `@interrupt` function's name at `InterruptHandler`; at `fn` EN0803",
        || {
            let r = on(
                "i386-none",
                "import { idt } from \"os\";
@interrupt private function onTimer(frame: &InterruptFrame): void {}
@entry private function kmain(boot: &BootInfo): never { idt.set(32, onTimer); for (;;) {} }
",
            );
            r.clean();
            let b = body(&r, "main::kmain");
            assert_eq!(arg(b, 0, 1).adjust, [Adjust::FnToHandler]);
            let r = on(
                "i386-none",
                "@interrupt private function onTimer(frame: &InterruptFrame): void {}
@entry private function kmain(boot: &BootInfo): never { const f: fn(frame: &InterruptFrame) => void = onTimer; for (;;) {} }
",
            );
            assert_eq!(r.codes(), ["EN0803"]);
        },
    );
    h.case(
        "closure/EN0803: a local function with hidden arguments at `fn` (MR-4, T:883)",
        || {
            let r = main_lib(
                "let q: i64[] = [];
function relay(): void { grow(); }
function grow(): void { for (let i = 0; i < 100; i++) { q.push(i); } }
const f: fn() => void = relay;
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0803]: `relay` uses top-level variables, so it can't become an `fn`
 --> main.en:4:25
  |
4 | const f: fn() => void = relay;
  |                         ^^^^^ it takes `q` as a hidden argument
  |
help: pass it where a closure parameter is expected, which may use them
  = explain: run `enrang explain EN0803`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case("closure/the five `unsafe fn` near-misses compile", || {
        let r = main_lib(
            "const a: unsafe fn() => void = bad;
const b: unsafe fn() => void = fast;
const c: unsafe fn(d: *u8, v: u8, n: usize) => void = mem.set;
private unsafe function bad(): void {}
@requires(\"sse2\") private function fast(): void {}
",
        );
        r.clean();
        let r = on(
            "i386-none",
            "@naked private unsafe function nk(): void { asm(\"ret\"); }
@entry private function kmain(boot: &BootInfo): never { const n: unsafe fn() => void = nk; for (;;) {} }
",
        );
        r.clean();
    });
}

fn interfaces(h: &mut Harness) {
    h.case(
        "closure/EN1006: a function with a by-value interface parameter as a function value (S:682)",
        || {
            let r = main_lib(
                "const g: fn(x: Speaker) => void = relay;
run(relay);
private function relay(x: Speaker): void {}
private function run(f: (x: Speaker) => void): void {}
public interface Speaker { speak(): string; }
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN1006]: an interface type by value outside a parameter is not supported yet
 --> main.en:1:35
  |
1 | const g: fn(x: Speaker) => void = relay;
  |                                   ^^^^^ `relay` takes `x`, a `Speaker`, by value
  |
  = note: `relay` has a copy per class passed as `x`, and none an `fn` could name
help: take `x: &Speaker`, which one copy serves through the method table
  = explain: run `enrang explain EN1006`

error[EN1006]: an interface type by value outside a parameter is not supported yet
 --> main.en:2:5
  |
2 | run(relay);
  |     ^^^^^ `relay` takes `x`, a `Speaker`, by value
  |
  = note: `relay` has a copy per class passed as `x`, and none a closure could name
help: take `x: &Speaker`, which one copy serves through the method table
  = explain: run `enrang explain EN1006`

error: aborting due to 2 previous errors
"
            );
        },
    );
    h.case(
        "closure/an `&I` parameter names its two-word copy; one no table can serve is EN1006",
        || {
            let r = main_lib(
                "const f: fn(s: &Speaker) => string = describe;
private function describe(s: &Speaker): string { return s.speak(); }
public interface Speaker { speak(): string; }
",
            );
            r.clean();
            assert_eq!(init(statements(&r), 0).adjust, [Adjust::FnToPtr]);
            let r = main_lib(
                "const f: fn(x: &Clone) => void = look;\nprivate function look(x: &Clone): void {}\n",
            );
            // The written `fn` type's `&Clone` parameter is 4E's EN1006 too (T:1000):
            // its callers pass `x` in two words, which `Clone` has no table for. A
            // local's annotation that a position rule rejects is `Error` (fix-5), so
            // `look` meets nothing there.
            assert_eq!(
                diags(&r),
                ["EN1006 1:10 an interface type by value outside a parameter is not supported yet [this `&Clone` needs its class's table]"]
            );
            // At a parameter's written `fn` type, which stays as written, `look`
            // reports its own conversion.
            let r = main_lib(
                "runIt(look);\nprivate function runIt(f: fn(x: &Clone) => void): void {}\nprivate function look(x: &Clone): void {}\n",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN1006 1:7 an interface type by value outside a parameter is not supported yet [`look` takes `x`, a `&Clone`, which needs its two-word form here]",
                    "EN1006 2:27 an interface type by value outside a parameter is not supported yet [this `&Clone` needs its class's table]",
                ]
            );
            assert!(r.rendered().contains(
                "= note: `Clone.clone` takes or returns `Self` by value, which can't run where the class is unknown"
            ));
            assert_eq!(
                r.diags[0].helps[0].message,
                "make it generic: `look<T extends Clone>(x: &T)`"
            );
        },
    );
    h.case("closure/an arrow body is an `ArrowBodyKind::Expr`", || {
        let r = main_lib("const k = (x: i64): i64 => x;\n");
        r.clean();
        let b = statements(&r);
        assert!(matches!(
            b.arrows.iter().next().expect("an arrow").body,
            ArrowBodyKind::Expr(_)
        ));
    });
}

/// Stage 6's review fixes: EN0409 for arrows nothing types, one report for a
/// refused type argument, and the `?`-decided result.
fn review(h: &mut Harness) {
    h.case(
        "closure/S:724: an arrow argument of a form, a type parameter or `new Box` is EN0409",
        || {
            let r = main_lib(
                "public function g<T>(x: T): void { }
public function a(): void { g((x) => x); console.log((y) => y); const b = new Box((z) => z); }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0409 2:32 `x` needs a type annotation [nothing here gives `x` a type]",
                    "EN0409 2:55 `y` needs a type annotation [nothing here gives `y` a type]",
                    "EN0409 2:84 `z` needs a type annotation [nothing here gives `z` a type]",
                ]
            );
        },
    );
    h.case(
        "closure/an arrow argument of a call that reported its own error is that call's alone (mutant M49)",
        || {
            let r = main_lib(
                "public function one(f: (n: i64) => i64): void { }
public function a(): void { one((x) => x, 2); nope((y) => y); }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0423 2:29 `one` takes 1 argument, but 2 were given [too many arguments]",
                    "EN0301 2:47 cannot find `nope` in this scope [not found]",
                ]
            );
        },
    );
    h.case(
        "closure/S:977: `users.map(u => u)` is EN0703 alone, its result left `Error`",
        || {
            let r = main_lib(
                "public class User { public name: string = \"\"; }
public function a(users: &User[]): void { const same = users.map(u => u); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0703 2:66 `U` can't stand for the reference `&User` [this makes `U` the reference `&User`]"]
            );
        },
    );
    h.case(
        "closure/T:902: a return that misfits the result a `?` decided names the `?`, with the `Ok` help",
        || {
            let r = main_lib(
                "public function g(): Result<i64> { return Ok(1); }
public function f(): void { const k = () => { const x = g()?; return x; }; }
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0401]: mismatched types: expected `Result<_>`, found `i64`
 --> main.en:2:70
  |
2 | public function f(): void { const k = () => { const x = g()?; return x; }; }
  |                                                                      ^ this is `i64`
  |                                                            - the arrow's result type comes from this `?`
  |
help: annotate the result, `(): Result<i64> => ...`, or write `Ok(x)`
  = explain: run `enrang explain EN0401`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "closure/an array of an arrow already reported is no EN0410 as well",
        || {
            let r = main_lib("public function f(): void { const c = [(y) => y]; }\n");
            assert_eq!(
                diags(&r),
                ["EN0409 1:41 `y` needs a type annotation [nothing here gives `y` a type]"]
            );
        },
    );
}
