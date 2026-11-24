//! The sixth review-fix stage's cases (`fix-6`, plan h.1 stage 6), each named after
//! the area it checks: module paths of the input directory (SPEC 4.12), the one
//! reference step at a site (S:656), literal operands of `as` (S:703), compound
//! assignments (S:688), imports of test parts, bounds with type arguments (S:762),
//! position checks of written types in bodies and forms (S:560, S:845), destructuring
//! assignment (S:418), C19 through `match` (S:1139), arrows' missing returns
//! (S:1136), constant lengths and layouts (S:756), and the mutation survivors of the
//! stage-6 reviews.

use enrang_hir::{ExprKind, Pat};
use enrang_sema::LibSource;
use enrang_testkit::{Harness, TempDir};

use crate::paths::{body, diags, expr_stmt, main_lib};
use crate::support::{Run, run_in, run_with};

pub fn register(h: &mut Harness) {
    loading(h);
    engine(h);
    flow(h);
    types(h);
    consts(h);
    types_minor(h);
    types_minor2(h);
    survivors(h);
    survivors_consts(h);
}

/// Checks the program of `sources`, the first the entry, with the embedded library.
fn lib_run(sources: &[(&str, &str)]) -> Run {
    run_with(sources, LibSource::Embedded, "x86_64-linux")
}

/// The help messages of every diagnostic of `r`, in order.
fn all_helps(r: &Run) -> Vec<String> {
    r.diags
        .iter()
        .flat_map(|d| d.helps.iter().map(|h| h.message.clone()))
        .collect()
}

fn loading(h: &mut Harness) {
    h.case(
        "load/fix-6: the input directory imported as a folder from an entry outside it (S:801)",
        || {
            let dir = TempDir::new("review6-dot-folder");
            let drivers = dir.path().join("m6").join("drivers");
            std::fs::create_dir_all(&drivers).unwrap();
            std::fs::write(
                drivers.join("serial.en"),
                "public function write(b: u8): void {}\n",
            )
            .unwrap();
            let m6 = dir.path().join("m6");
            std::fs::write(
                m6.join("named.en"),
                "import { serial } from \"./drivers\";\nserial.write(1);\n",
            )
            .unwrap();
            std::fs::write(
                m6.join("ns.en"),
                "import * as d from \"./drivers\";\nd.serial.write(1);\n",
            )
            .unwrap();
            // Run from inside `drivers`, the folder is the input directory `.`;
            // run from `m6`, it is `drivers`: both name the same modules.
            for entry in ["../named.en", "../ns.en"] {
                run_in(&drivers, entry).clean();
            }
            for entry in ["named.en", "ns.en"] {
                run_in(&m6, entry).clean();
            }
        },
    );
    h.case(
        "load/fix-6: a `.test.en` part is no module, so an import of it is EN0305 (S:799)",
        || {
            let r = lib_run(&[
                (
                    "main.en",
                    "import * as t from \"./calc.test\";\nconsole.log(1);\n",
                ),
                (
                    "calc.en",
                    "public function add(a: i64, b: i64): i64 { return a + b; }\n",
                ),
                (
                    "calc.test.en",
                    "test(\"adds\", () => { expect(add(1, 2)).toBe(3); });\n",
                ),
            ]);
            assert_eq!(
                diags(&r),
                ["EN0305 1:20 import path not found: `./calc.test` [a `.test.en` file is a test part, not a module]"]
            );
        },
    );
    h.case(
        "resolve/fix-6: an import of a file with statements is EN0312 alone (S:799)",
        || {
            let script = "console.log(\"hi\");\nfunction hello(): void {}\n";
            let r = lib_run(&[
                (
                    "main.en",
                    "import { hello } from \"./script\";\nhello();\n",
                ),
                ("script.en", script),
            ]);
            assert_eq!(
                diags(&r),
                ["EN0312 1:23 `script.en` has top-level statements, so it can't be imported [imported here]"]
            );
            let r = lib_run(&[
                (
                    "main.en",
                    "import { nothing } from \"./script\";\nimport * as sc from \"./script\";\nconsole.log(sc.hello);\n",
                ),
                ("script.en", script),
            ]);
            assert_eq!(
                diags(&r),
                [
                    "EN0312 1:25 `script.en` has top-level statements, so it can't be imported [imported here]",
                    "EN0312 2:21 `script.en` has top-level statements, so it can't be imported [imported here]",
                ]
            );
        },
    );
    h.case(
        "resolve/fix-6: EN0307 between an import and a later declaration is at the later one",
        || {
            let r = lib_run(&[
                (
                    "main.en",
                    "import { top } from \"./lib\";\nimport { top } from \"./lib\";\nfunction top(): void {}\ntop();\n",
                ),
                ("lib.en", "public function top(): i64 { return 1; }\n"),
            ]);
            assert_eq!(
                diags(&r),
                [
                    "EN0307 2:10 `top` is defined twice [defined again here]",
                    "EN0307 3:10 `top` is defined twice [defined again here]",
                ]
            );
            let lines: Vec<u32> = r
                .diags
                .iter()
                .map(|d| r.map.loc(d.secondary[0].span.lo).line)
                .collect();
            assert_eq!(lines, [1, 1]);
        },
    );
}

fn engine(h: &mut Harness) {
    h.case(
        "typeck/fix-6: `&Box<C>` at an `&I` parameter is two reference steps, EN0401 (S:656)",
        || {
            let r = main_lib(
                "const bd: Box<Dog> = new Box(new Dog { name: \"R\".toString() });
say(&bd);
const bc: Box<Cat> = new Box(new Cat { n: 1 });
say(&bc);
const d = new Dog { name: \"x\".toString() };
say(&d);
const s: &Speaker = &bd;
function say(s: &Speaker): void {}
public interface Speaker { speak(): string; }
public class Dog implements Speaker { public name: string; public speak(): string { return \"w\"; } }
public class Cat { public n: i64; }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0401 2:5 mismatched types: `Box<Dog>` does not satisfy `Speaker` [this is `Box<Dog>`]",
                    "EN0401 4:5 mismatched types: `Box<Cat>` does not satisfy `Speaker` [this is `Box<Cat>`]",
                    "EN0401 7:21 mismatched types: expected `&Speaker`, found `&Box<Dog>` [this is `&Box<Dog>`]",
                ]
            );
        },
    );
    h.case(
        "typeck/fix-6: a parenthesised literal of `as` takes the target's type (S:703)",
        || {
            let r = main_lib(
                "const a = (0xFFFFFFFFFFFFFFFF) as u64;
const b = (300) as u8;
const c = (-300) as u8;
const c2 = -(300) as u8;
const d = 0xFFFFFFFFFFFFFFFF as u64;
console.log(a, b, c, c2, d);
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0411 2:12 `300` doesn't fit `u8` [`u8` holds 0 to 255]",
                    "EN0411 3:12 `-300` doesn't fit `u8` [`u8` holds 0 to 255]",
                    "EN0411 4:12 `-(300)` doesn't fit `u8` [`u8` holds 0 to 255]",
                ]
            );
        },
    );
    h.case(
        "typeck/fix-6: compound assignments name the bad operand and their operator, and `/=` truncates (S:688)",
        || {
            let r = main_lib(
                "let s = \"a\";
s += 1;
let t: i64 = 0;
t &= 1.5;
let x = 7;
x /= 2;
let z: i64 = 9;
z /= 2;
console.log(s, t, x, z);
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0420 2:6 `+=` needs two numbers or two strings, found `string` and `int` [this is `int`]",
                    "EN0403 4:6 `&=` needs integers, found `f64` [this is `f64`]",
                    "EN0430 6:1 integer division truncates [both sides are integers, so the result is an integer]",
                ]
            );
        },
    );
    h.case(
        "typeck/fix-6: helps that compile: no narrowing of a `?.` chain, `new K { ... }`, a fresh name",
        || {
            let r = main_lib(
                "const v = make()?.secret;
const c = K(3);
Shape.Empty();
Shape.Circle();
const k2 = KC(3);
console.log(v, c, k2);
public function f(a: Outer | null): void { if (a?.b != null) { const bad = a?.b.c; } }
public function g(a: Outer | null): void { const ok = a.b; }
public function make(): Base | null { return null; }
public class Base { public secret: i64; }
public class Inner { public c: i64; }
public class Outer { public b: Inner; }
public class K { public v: i64; }
public class KC { public v: i64; public constructor(v: i64) { this.v = v; } }
public enum Shape { Circle { r: f64 }, Empty }
",
            );
            assert_eq!(
                all_helps(&r),
                [
                    "bind it first: `const value = make();`, then `value?.secret`",
                    "create one by naming its fields: `new K { ... }`",
                    "a case is written `Shape.Empty`",
                    "a case is written `Shape.Circle`, or with its fields, `Shape.Circle { ... }`",
                    "create one with `new KC(...)`",
                    "use `?.c`, which reads it only when the value is not `null`",
                    "use `?.b`, which reads it only when the value is not `null`",
                    "or narrow it first: `if (a != null) { ... }`",
                ]
            );
        },
    );
    h.case(
        "typeck/fix-6: a `&bool` condition is EN0203 with a `*` help (doc gap)",
        || {
            let r = main_lib(
                "public function h(flags: &Slice<bool>, one: &bool): i64 {
  let n = 0;
  for (const done of flags) { if (done) { n += 1; } }
  if (!one) { n += 1; }
  return n;
}
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0203 3:35 a condition must be `bool`, found `&bool` [this is `&bool`]",
                    "EN0203 4:8 a condition must be `bool`, found `&bool` [this is `&bool`]",
                ]
            );
            assert_eq!(
                all_helps(&r),
                [
                    "read the `bool` it points at: `*done`",
                    "read the `bool` it points at: `*one`",
                ]
            );
        },
    );
}

fn survivors(h: &mut Harness) {
    h.case(
        "survivors/fix-6: `||` narrows in its false branch only (N3, S:741)",
        || {
            let r = main_lib(
                "public function n3(p: string | null, c: bool): isize { if (p == null || c) { return p.length(); } return 0; }\n",
            );
            assert_eq!(
                diags(&r),
                ["EN0303 1:87 `string | null` has no member `length` [this value may be `null`]"]
            );
        },
    );
    h.case(
        "survivors/fix-6: `null != p` and `null == p` narrow as `p != null` does (N1, S:741)",
        || {
            main_lib(
                "public function n1(p: string | null): isize { if (null != p) { return p.length(); } return 0; }
public function n1b(p: string | null): isize { if (null == p) { return 0; } return p.length(); }
",
            )
            .clean();
        },
    );
    h.case(
        "survivors/fix-6: the prescan reads arrows nested in a loop body or an arrow argument (N9, S:744)",
        || {
            let r = main_lib(
                "public function n9(p0: string | null, c: bool): isize { let p = p0; let t: isize = 0; if (p != null) { while (c) { t += p.length(); const reset = () => { p = null; }; reset(); } } return t; }
public function n9b(p0: string | null, xs: &i64[]): isize { let p = p0; if (p != null) { each(xs, x => { const g = () => { p = null; }; }); return p.length(); } return 0; }
public function each(xs: &i64[], f: (x: &i64) => void): void {}
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0303 1:123 `string | null` has no member `length` [this value may be `null`]",
                    "EN0303 2:150 `string | null` has no member `length` [this value may be `null`]",
                ]
            );
        },
    );
    h.case(
        "survivors/fix-6: a C19 ternary narrows each branch by its condition (R4, S:741, S:1139)",
        || {
            let r = main_lib(
                "public function r4(p: &string | null): Result<isize> { return p != null ? p.length() : Err(\"none\"); }
public function r4b(p: &string | null): Result<isize> { return p == null ? p.length() : 0; }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0303 2:78 `&string | null` has no member `length` [this value may be `null`]"]
            );
        },
    );
    h.case(
        "survivors/fix-6: a negated literal of `as` is direct, so it must fit (M01, S:703)",
        || {
            let r = main_lib(
                "const a = -1 as u32;\nconst b = -5 as u8;\nconst c = -128 as i8;\nconsole.log(a, b, c);\n",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0411 1:11 `-1` doesn't fit `u32` [`u32` holds 0 to 4294967295]",
                    "EN0411 2:11 `-5` doesn't fit `u8` [`u8` holds 0 to 255]",
                ]
            );
        },
    );
    h.case(
        "survivors/fix-6: a float shift count is EN0403 (M09, S:688)",
        || {
            let r = main_lib(
                "const x: i64 = 1;\nconst y = x << 1.5;\nconst z: f64 = 2.0;\nconst w = x >> z;\nconsole.log(y, w);\n",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0403 2:16 `<<` needs integers, found `f64` [this is `f64`]",
                    "EN0403 4:16 `>>` needs integers, found `f64` [this is `f64`]",
                ]
            );
        },
    );
    h.case(
        "survivors/fix-6: `while ((true))` and `for (;;)` never fall through (M22, S:1136)",
        || {
            main_lib(
                "public function loops(): i64 { while ((true)) {} }\npublic function loops2(): i64 { for (;;) {} }\n",
            )
            .clean();
        },
    );
    h.case(
        "survivors/fix-6: an `f64` condition is EN0203 (M28, S:1131)",
        || {
            let r = main_lib("public function f(x: f64): void { if (x) {} while (1.5) {} }\n");
            assert_eq!(
                diags(&r),
                [
                    "EN0203 1:39 a condition must be `bool`, found `f64` [this is `f64`]",
                    "EN0203 1:52 a condition must be `bool`, found `f64` [this is `f64`]",
                ]
            );
            assert_eq!(
                all_helps(&r),
                ["compare it: `x != 0`", "compare it: `1.5 != 0`"]
            );
        },
    );
    h.case(
        "survivors/fix-6: a local shadows a namespace and a type before `.` (M26, S:801)",
        || {
            let r = lib_run(&[
                (
                    "main.en",
                    "import * as L from \"./lib\";
public function f(): i64 { const L = new Holder { top: 5 }; return L.top; }
public function g(): i64 { const L = new Holder { top: 5 }; return L.get(); }
public function h(Point: i64): i64 { return Point.origin().x; }
public function k(Point: Holder): i64 { return Point.top; }
public class Holder { public top: i64; public get(): i64 { return this.top; } }
public class Point { public x: i64; public static origin(): Point { return new Point { x: 0 }; } }
",
                ),
                ("lib.en", "public function top(): i64 { return 1; }\n"),
            ]);
            assert_eq!(
                diags(&r),
                ["EN0303 4:51 `i64` has no member `origin` [no such member]"]
            );
        },
    );
}

fn flow(h: &mut Harness) {
    h.case(
        "pattern/fix-6: object and place patterns on the left of `=` (S:418, D17)",
        || {
            let r = main_lib(
                "public function f(q: P): i64 { let x: i64 = 0; let y: i64 = 0; ({ x, y } = q); return x + y; }
public function g(q: &P): i64 { let x: i64 = 0; let y: i64 = 0; ({ x, y } = q); return x + y; }
public function h(): i64 { let x: i64 | null = 1; if (x != null) { ({ x } = mk()); return x + 1; } return 0; }
public function k(): i64 { let a: i64 = 0; let b: i64 = 0; ({ x: a, y: b } = mk2()); return a + b; }
public function m(xs: i64[]): void { [xs[0], xs[1]] = [xs[1], xs[0]]; }
public function n(p: P): i64 { let a: i64 = 0; let x: i64 = 0; [a, { x }] = [1, p]; return a + x; }
public function bad(q: P): void { let s: string = \"\"; ({ x: s } = q); }
public function bad2(q: P): void { let s: i64 = 0; ({ z: s } = q); }
public function mk(): { x: i64 | null } { return { x: 2 }; }
public function mk2(): { x: i64, y: i64 } { return { x: 2, y: 3 }; }
public class P { public x: i64 = 0; public y: i64 = 0; }
public class Q { public a: i64 = 1; public b: i64 = 2; public swap(): void { [this.a, this.b] = [this.b, this.a]; } }
public class R { public a: i64 = 1; public s: string = \"\"; public swap(): void { [this.a, this.s] = [this.s, this.a]; } }
",
            );
            assert_eq!(
                diags(&r),
                [
                    // The assignment kills `x`'s fact: `mk()` may give `null`.
                    "EN0420 3:91 `+` needs numbers, found `i64 | null` [this is `i64 | null`]",
                    "EN0401 7:61 mismatched types: expected `string`, found `i64` [this part of the value is `i64`]",
                    "EN0303 8:55 `P` has no member `z` [no such member]",
                    "EN0401 13:102 mismatched types: expected `i64`, found `string` [this is `string`]",
                    "EN0401 13:110 mismatched types: expected `string`, found `i64` [this is `i64`]",
                ]
            );
        },
    );
    h.case(
        "pattern/fix-6: a place part is `Pat::Place`, an object pattern `Pat::Object` (D17)",
        || {
            let r = main_lib(
                "public function k(): i64 { let a: i64 = 0; let b: i64 = 0; ({ x: a, y: b } = mk2()); return a + b; }
public function mk2(): { x: i64, y: i64 } { return { x: 2, y: 3 }; }
public class Q { public a: i64 = 1; public b: i64 = 2; public swap(): void { [this.a, this.b] = [this.b, this.a]; } }
",
            );
            r.clean();
            let swap = expr_stmt(body(&r, "main::Q::swap"), 0);
            let ExprKind::Destructure { pat, .. } = &swap.kind else {
                panic!("{swap:?}");
            };
            let Pat::Tuple(parts) = pat else {
                panic!("{pat:?}");
            };
            assert!(parts.iter().all(|p| matches!(p, Pat::Place(_))), "{pat:?}");
            assert_eq!(pat.places().len(), 2);
            let k = expr_stmt(body(&r, "main::k"), 0);
            let ExprKind::Destructure { pat, .. } = &k.kind else {
                panic!("{k:?}");
            };
            let Pat::Object(fields) = pat else {
                panic!("{pat:?}");
            };
            assert!(fields.iter().all(|(_, p)| matches!(p, Pat::Bind(_))), "{pat:?}");
        },
    );
    h.case(
        "result/fix-6: C19 reaches every expression arm of a `match` with a block arm (S:1139)",
        || {
            let r = main_lib(
                "public function f(d: D, n: i64): Result<i64> { return match (d) { D.A => { return n + 1; }, D.B => n }; }
public function f2(d: D, n: i64): Result<i64> { return match (d) { D.A => { console.log(1); }, D.B => n }; }
public enum D { A, B }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0401 2:56 mismatched types: expected `Result<i64>`, found `void` [this is `void`]"]
            );
        },
    );
    h.case(
        "result/fix-6: C19 is the one wrap: `return x` at `Result<i64 | null>` is EN0401 (S:656, G51)",
        || {
            let r = main_lib(
                "public function r(x: i64): Result<i64 | null> { return x; }
public function r2(x: i64): Result<i64 | null> { return null; }
public function r3(x: i64): Result<i64 | null> { return 5; }
public function r4(x: i64): Result<i64 | null> { return Ok(x); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0401 1:56 mismatched types: expected `Result<i64 | null>`, found `i64` [this is `i64`]"]
            );
            assert_eq!(all_helps(&r), ["wrap it yourself: `Ok(x)`"]);
        },
    );
    h.case(
        "closure/fix-6: an arrow whose number result may be missing is EN0427 (S:1136)",
        || {
            let r = main_lib(
                "public function g(): void { const a = (x: i64) => { if (x > 0) { return 1.5; } }; const h = (x: i64) => { if (x > 0) { return 2; } }; const r: i64 = h(1); }
public function g2(): void { const h = (x: i64) => { if (x > 0) { return 2; } return 3; }; const k = (x: i64) => { if (x > 0) { return; } }; console.log(h(1)); k(1); }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0427 1:80 this arrow may end without returning an `f64` [the end of the body is reached without a `return`]",
                    "EN0427 1:132 this arrow may end without returning an `int` [the end of the body is reached without a `return`]",
                ]
            );
        },
    );
    h.case(
        "narrow/fix-6: a value read through `&(T | null)` sees the fact on its referent (S:739, S:684)",
        || {
            let r = main_lib(
                "public function f(p: &(i64 | null)): i64 { if (p != null) { return p + 1; } return 0; }
public function g(p: &(i64 | null)): bool { if (p != null) { return p > 3; } return false; }
public function h(p: &(i64 | null)): i64 { if (p != null) { const v: i64 = p; return v; } return 0; }
public function k(xs: &(i64 | null)[]): i64 { let t: i64 = 0; for (const x of xs) { if (x != null) { t += x; } } return t; }
public function m(p: &(i64 | null)): i64 { if (p != null) { take(p); } return 0; }
public function n(p: &(i64 | null)): i64 { return p + 1; }
public function take(q: &(i64 | null)): void {}
",
            );
            assert_eq!(
                diags(&r),
                ["EN0420 6:51 `+` needs numbers, found `i64 | null` [this is `i64 | null`]"]
            );
        },
    );
    h.case(
        "narrow/fix-6: `n += v` and `n++` keep `n`'s fact in a loop as in straight code (S:744)",
        || {
            main_lib(
                "public function a(m: i64 | null, c: bool): i64 { let t: i64 = 0; let n = m; if (n != null) { while (c) { t += n; n++; } } return t; }
public function b(start: i64 | null): i64 { let count = start; if (count != null) { count += 1; while (count < 10) { count += 1; } return count; } return 0; }
",
            )
            .clean();
        },
    );
    h.case(
        "closure/fix-6: diagnostics that name the cause: no EN0409 after EN0705, EN1015 helps, EN1007's capture, a killed case",
        || {
            let r = main_lib(
                "public function c(): void { const g: (x: i64) => i64 = x => x + 1; }
public function d(xs: i64[] | null): void { for (const x of xs) { console.log(x); } }
public function e(n: i64): void { for (const x of n) { console.log(x); } }
public function f(): void { let count = 0; const inc = () => { count += 1; }; call(inc); }
public function g(s: Shape, o: Shape): f64 { let t = s; return match (t) { Shape.Circle => { t = o; return t.radius; }, Shape.Square => t.side }; }
public function call(f: fn() => void): void {}
public enum Shape { Circle { radius: f64 }, Square { side: f64 } }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0705 1:38 a closure type can be written only as a parameter's type [not a parameter's type]",
                    "EN1015 2:61 this `for...of` source is not supported yet [this is `i64[] | null`]",
                    "EN1015 3:51 this `for...of` source is not supported yet [this is `i64`]",
                    "EN1007 4:84 a function pointer cannot capture variables [`inc` holds an arrow that uses `count`]",
                    "EN0303 5:110 `Shape` has no member `radius` [no such member]",
                ]
            );
            assert_eq!(
                all_helps(&r)[..2],
                [
                    "narrow it first: `if (xs != null) { ... }`",
                    "to count up to it, loop over a range: `for (const i of 0..n)`",
                ]
            );
            let killed = &r.diags[4];
            assert_eq!(killed.secondary.len(), 1, "{}", r.rendered());
            assert!(
                killed.secondary[0].text.contains("`t` is assigned here"),
                "{}",
                r.rendered()
            );
            assert_eq!(r.diags[3].secondary.len(), 1, "{}", r.rendered());
        },
    );
}

fn types(h: &mut Harness) {
    h.case(
        "generic/fix-6: a bound's type arguments count, and a bound naming a parameter is read at the call (S:762, S:764)",
        || {
            let r = main_lib(r#"const s = new StrCell { v: "x".toString() };
console.log(f(&s) + 1);
const p = new P { x: 1 };
const q = new P { x: 2 };
smaller(&p, &q);
const so = new Sorted<P> { items: [] };
conv(5, &new ToInt {});
const ic = new IntCell { v: 3 };
console.log(f(&ic));
public class Cell<T> { public v: T; }
public class StrCell extends Cell<string> {}
public class IntCell extends Cell<i64> {}
public class Holder<T extends Cell<i64>> { public c: T; }
public function take(h: &Holder<Cell<string>>): void {}
public function f<T extends Cell<i64>>(x: &T): i64 { return x.v; }
public interface Container<T> { get(): &T; }
public function use1<C extends Container<i64>>(c: &C): i64 { return *c.get(); }
public function relay<U extends Container<string>>(u: &U): i64 { return use1(u); }
public function relay2<U extends Container<i64>>(u: &U): i64 { return use1(u); }
public function g<U extends Container<string>>(u: &U): i64 { const c: &Container<i64> = u; return *c.get(); }
public interface Cmp<T> { cmp(o: &T): i32; }
public class P implements Cmp<P> { public x: i64; public cmp(o: &P): i32 { return 0; } }
public function smaller<T extends Cmp<T>>(a: &T, b: &T): &T { return a.cmp(b) < 0 ? a : b; }
public class Sorted<T extends Cmp<T>> { public items: T[]; }
public interface Conv<T> { run(x: T): i64; }
public class ToInt { public run(x: i64): i64 { return x; } }
public function conv<T, U extends Conv<T>>(x: T, u: &U): i64 { return u.run(x); }
"#);
            assert_eq!(
                diags(&r),
                [
                    "EN0419 2:15 `StrCell` does not satisfy `Cell<i64>` [`T` must satisfy `Cell<i64>`]",
                    "EN0419 14:22 `Cell<string>` does not satisfy `Cell<i64>` [`Holder` requires `T extends Cell<i64>`]",
                    "EN0419 18:78 `U` does not satisfy `Container<i64>` [`C` must satisfy `Container<i64>`]",
                    "EN0401 20:89 mismatched types: expected `&Container<i64>`, found `&U` [this is `&U`]",
                ]
            );
        },
    );
    h.case(
        "positions/fix-6: a static path's and a size form's written types are positions (S:560, S:606, S:845)",
        || {
            let r = main_lib(r#"public class Stack<T> { public items: T[]; public static empty(): Stack<T> { return new Stack<T> { items: [] }; } public static count(): i64 { return 0; } }
public class Lexer { private s: &string; public constructor(s: &string) { this.s = s; } }
public interface Speaker { speak(): string; }
public function f(): void { Stack<&i64>.empty(); console.log(Stack<Lexer>.count()); console.log(Stack<Speaker>.count()); console.log(Stack<Slice<u8>>.count()); console.log(Stack<i64>.count()); }
public function g(): usize { return sizeOf<Speaker>() + alignOf<Slice<u8>>(); }
public function h(): void { const a = sizeOf<Box<&i64>>(); const b = alignOf<(&i64)[]>(); const c = sizeOf<i64>(); }
public const N: usize = sizeOf<Speaker>();
"#);
            assert_eq!(
                diags(&r),
                [
                    "EN0701 4:29 a `Stack` can't hold a `&i64`, because `&i64` is a reference [a reference]",
                    "EN0701 4:62 a `Stack` can't hold a `Lexer`, because `Lexer` holds a reference [`Lexer` borrows through its field `s`]",
                    "EN1006 4:103 an interface type by value outside a parameter is not supported yet [`Speaker` by value in a type argument]",
                    "EN0401 4:140 `Slice<u8>` is a view, so it exists only behind `&` [a view by value]",
                    "EN1006 5:44 an interface type by value outside a parameter is not supported yet [`Speaker` by value in a size form]",
                    "EN0401 5:65 `Slice<u8>` is a view, so it exists only behind `&` [a view by value]",
                    "EN0701 6:46 a `Box` can't hold a `&i64`, because `&i64` is a reference [a reference]",
                    "EN0701 6:78 an array can't hold a `&i64`, because `&i64` is a reference [a reference]",
                    "EN1006 7:32 an interface type by value outside a parameter is not supported yet [`Speaker` by value in a size form]",
                ]
            );
        },
    );
    h.case(
        "generic/fix-6: C20 by value takes only a value type (S:678, A:892)",
        || {
            let r = main_lib(r#"const t = "x".toString();
greetv(new View(&t));
const v = new View(&t);
greetr(&v);
const pl = new Plain { name: "p".toString() };
greetv(pl);
public class View { public name: string = "v".toString(); private r: &string; public constructor(r: &string) { this.r = r; } public show(): void {} }
public class Plain { public name: string; }
public function greetv(x: { name: string }): void { console.log(x.name); }
public function greetr(x: &{ name: string }): void { console.log(x.name); }
"#);
            assert_eq!(
                diags(&r),
                ["EN0701 2:8 a `{ name: string }` can't hold a `View`, because `View` holds a reference [only a value type is passed by value as an object type]"]
            );
        },
    );
    h.case(
        "iface/fix-6: an `&I` no table serves is EN1006 at a call chosen at run time (S:631, A:894)",
        || {
            let r = main_lib(r#"public interface Cloner { clone(): Self; }
public interface Taker { take(c: &Cloner): void; }
public interface Speaker { speak(): string; }
public class P { public x: i64; public clone(): P { return new P { x: this.x }; } public speak(): string { return ""; } }
public class Animal { public take(c: &Cloner): void {} public hear(s: &Speaker): void {} }
public final class Fin { public take(c: &Cloner): void {} }
public function f(a: &Animal, p: &P): void { a.take(p); a.hear(p); }
public function viaIface(t: &Taker, p: &P): void { t.take(p); }
public function fin(a: &Fin, p: &P): void { a.take(p); }
"#);
            assert_eq!(
                diags(&r),
                [
                    "EN1006 7:53 an interface type by value outside a parameter is not supported yet [`take` is chosen when the program runs, so `c` needs the two-word form of `&Cloner`]",
                    "EN1006 8:59 an interface type by value outside a parameter is not supported yet [`take` is chosen when the program runs, so `c` needs the two-word form of `&Cloner`]",
                ]
            );
        },
    );
    h.case(
        "satisfy/fix-6: a synthesised `equals` needs `==` on every field (S:640)",
        || {
            let r = main_lib(r#"const w1 = new Wrap { p: new Plain { x: 1 } };
const w2 = new Wrap { p: new Plain { x: 1 } };
console.log(w1 == w2);
public class Plain { public x: i64; }
public class Wrap implements Eq { public p: Plain; }
public class Good implements Eq { public a: i64; public s: string; public c: Color; public n: i64 | null; public q: Pt; }
public class Pt implements Eq { public x: i64; }
public class Manual implements Eq { public p: Plain; public equals(o: &Manual): bool { return true; } }
public enum Color { Red, Green }
"#);
            assert_eq!(
                diags(&r),
                ["EN0416 5:30 `Wrap` does not satisfy `Eq`: `p` is a `Plain`, which has no `==` [required by this `implements`]"]
            );
        },
    );
}

fn consts(h: &mut Harness) {
    h.case(
        "consteval/fix-6: a length lays out a class complete, wherever it is declared (S:756)",
        || {
            for text in [
                r#"// valid: p15 plus an unrelated class with a constant-length field declared first
private const N: usize = 4;
public final class Unrelated { public pad: u8[N]; }
public final class Header { public magic: u32; public len: u16; }
public const RAW: u8[sizeOf<Header>()] = [0; sizeOf<Header>()];
"#,
                r#"// valid: a static buffer sized by a class whose field uses a named constant
private const SLOTS: usize = 8;
public final class Table { public slots: u32[SLOTS]; }
private unsafe let raw: u8[sizeOf<Table>()];
public function main(): void { unsafe { console.log(raw.length()); } }
"#,
                r#"// valid: a field sized by a class declared below it
public final class Packet { public header: u8[sizeOf<Header>()]; public body: u8[64]; }
public final class Header { public magic: u32; public len: u16; }
public function main(): void { console.log(sizeOf<Packet>()); }
"#,
                r#"// valid: a field sized by an enum declared below, value a literal expression
public final class Frame { public data: u8[Size.Big as usize]; }
public enum Size { Small = 4, Big = 4 * 2 }
assert(sizeOf<Frame>() == 8, "eight");
"#,
            ] {
                let r = main_lib(text);
                assert!(r.diags.is_empty(), "{text}\n{}", r.rendered());
            }
        },
    );
    h.case(
        "consteval/fix-6: a cycle through a class's layout is EN0412, with no cascade (S:756)",
        || {
            assert_eq!(
                diags(&main_lib(r#"// a class whose field length reads a constant that reads the class's size
public final class Node { public pad: u8[NODE_SIZE]; }
private const NODE_SIZE: usize = sizeOf<Node>();
assert(NODE_SIZE == 0, "the fixed point chosen");
assert(sizeOf<Node>() == 0, "an empty node");
"#)),
                ["EN0412 2:20 constant cycle: `Node` uses `NODE_SIZE`, which uses `Node` [`Node` depends on its own value]"]
            );
            assert_eq!(
                diags(&main_lib(r#"public final class Node { public tag: u32; public pad: u8[NODE_SIZE]; }
private const NODE_SIZE: usize = sizeOf<Node>();
assert(NODE_SIZE == 4, "the size seen");
assert(sizeOf<Node>() == 4, "node");
public function main(): void { const n = new Node { tag: 1, pad: [0; 4] }; console.log(n); }
"#)),
                ["EN0412 1:20 constant cycle: `Node` uses `NODE_SIZE`, which uses `Node` [`Node` depends on its own value]"]
            );
        },
    );
    h.case(
        "consteval/fix-6: a cycle through an enum value says so; a failed `@repr` fit is reported once",
        || {
            assert_eq!(
                diags(&main_lib(r#"// cycles: through a length, through an enum value, a self-cycle, a three-cycle
private const SELF: i32 = SELF + 1;
private const X: i32 = Y * 2;
private const Y: i32 = Z - 1;
private const Z: i32 = X;
private const LEN: usize = sizeOf<u8[LEN]>();
public enum E { A = K, B }
private const K: i32 = E.B as i32;
"#)),
                [
                    "EN0412 2:15 constant cycle: `SELF` uses `SELF` [`SELF` depends on its own value]",
                    "EN0412 3:15 constant cycle: `X` uses `Y`, which uses `Z`, which uses `X` [`X` depends on its own value]",
                    "EN0412 6:15 constant cycle: `LEN` uses `LEN` [`LEN` depends on its own value]",
                    "EN0412 8:24 constant cycle: `E.A` uses `E.B`, which uses `E.A` [this reads `E.B` while `E.A` is computed]",
                ]
            );
            assert_eq!(
                diags(&main_lib(r#"// a failed enum value: no follow-on errors at its uses
@repr("u8") public enum Op { A = 300, B }
private const X: i32 = Op.B as i32;
public function f(): void { console.log(Op.A as u8, X); }
"#)),
                ["EN0412 2:34 constant evaluation failed: `300` does not fit `u8` [`Op` is `@repr(\"u8\")`, which holds 0 to 255]"]
            );
        },
    );
    h.case(
        "consteval/fix-6: no EN1032 after EN0421, no EN0801 in an `unsafe let`'s initialiser, a parenthesised `&` fix-it",
        || {
            assert_eq!(
                diags(&main_lib(r#"public enum Color { Red, Green }
public final class P { public x: i32; }
private const NAME: &string = "Ada";
private const FAV: Color = Color.Green;
private const NOTHING: i32 | null = null;
private const ORIGIN: P = new P { x: 0 };
assert(NAME == "Ada", "name");
assert(FAV == Color.Green, "fav");
assert(NOTHING == null, "nothing");
assert(ORIGIN == new P { x: 0 }, "origin");
"#)),
                ["EN0421 10:8 `==` needs `P` to implement `Eq` [`P` has no `equals`]"]
            );
            assert_eq!(
                diags(&main_lib(r#"// statics: initialisers are constant expressions; a const can't read a static
public final class Heap { public start: usize; public next: *u8; }
private const BASE: usize = 0x100000;
private unsafe let heap: Heap = new Heap { start: BASE, next: BASE as *u8 };
private unsafe let counter: u64 = 0;
private unsafe let table: u32[4] = [1, 2, 3, 4];
private unsafe let copy: u64 = counter;
private const READS: u64 = counter;
private unsafe let clock: u64 = now();
private function now(): u64 { return 1; }
"#)),
                [
                    "EN0412 7:32 constant evaluation failed: `counter` is not constant [`counter` is an `unsafe let`, which can change at run time]",
                    "EN0412 8:28 constant evaluation failed: `counter` is not constant [`counter` is an `unsafe let`, which can change at run time]",
                    "EN1032 9:33 compile-time function calls are not supported yet [this calls a function]",
                ]
            );
            let r = main_lib(r#"private function show(s: &string): void { console.log(s); }
public function main(): void {
  const a = "x".toString();
  show(a + "y");
}
"#);
            assert_eq!(all_helps(&r), ["write `&(a + \"y\")`"]);
            let edits: Vec<String> = r.diags[0].helps[0]
                .edits
                .iter()
                .map(|e| e.replacement.clone())
                .collect();
            assert_eq!(edits, ["&(", ")"]);
        },
    );
}

fn survivors_consts(h: &mut Harness) {
    h.case(
        "survivors/fix-6: a spread in a constant is reported at its first `...` (M09, S:756)",
        || {
            let r = main_lib("private const X = [1, 2];\nprivate const Y = [...X, ...X];\n");
            assert_eq!(
                diags(&r),
                [
                    "EN0412 1:19 constant evaluation failed: `[1, 2]` is not constant [an `int[]` allocates at run time]",
                    "EN0412 2:20 constant evaluation failed: `...` is not constant [this spread]",
                ]
            );
        },
    );
    h.case(
        "survivors/fix-6: integers of two types compare by their true values (M24, S:688)",
        || {
            main_lib(
                "private const A: i32 = -1;\nprivate const B: u64 = 18446744073709551615;\nassert(A != B, \"true values differ\");\nassert(!(A == B), \"not equal\");\n",
            )
            .clean();
            let r = main_lib(
                "private const A: i32 = -1;\nprivate const B: u64 = 18446744073709551615;\nassert(A == B, \"equal\");\n",
            );
            assert_eq!(r.codes(), ["EN0415"]);
        },
    );
    h.case(
        "survivors/fix-6: a length beyond `usize` on i386 is EN0411, not EN0435 (M25)",
        || {
            let r = run_with(
                &[("main.en", "private unsafe let big: u8[5000000000];\n")],
                LibSource::Embedded,
                "i386-linux",
            );
            assert_eq!(
                diags(&r),
                ["EN0411 1:28 `5000000000` doesn't fit `usize` [`usize` holds 0 to 4294967295]"]
            );
        },
    );
    h.case(
        "survivors/fix-6: a constant tuple or object can't hold a `string` (X12, X13, S:756)",
        || {
            let r = main_lib(
                "private const T: [string, i32] = [\"a\", 1];\nprivate const O: { name: string, n: i32 } = { name: \"a\", n: 1 };\n",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0412 1:15 constant evaluation failed: a constant can't hold a `string` [`string` owns heap memory]",
                    "EN0412 2:15 constant evaluation failed: a constant can't hold a `string` [`string` owns heap memory]",
                ]
            );
        },
    );
    h.case(
        "survivors/fix-6: a constant assert among statements that overflows is EN0412 (X14)",
        || {
            let r = main_lib(
                "assert(LIMIT + 2147483647 > 0, \"limit\");\nconsole.log(\"ok\");\nprivate const LIMIT: i32 = 8;\n",
            );
            assert_eq!(
                diags(&r),
                ["EN0412 1:8 constant evaluation failed: `LIMIT + 2147483647` overflows `int` [integer overflow: 8 + 2147483647]"]
            );
        },
    );
    h.case(
        "survivors/fix-6: a case field too large for i386 is EN0435 at the field (Z06, S:1628)",
        || {
            let r = run_with(
                &[(
                    "main.en",
                    "public enum Msg { Small { x: u8 }, Large { data: u8[3000000000] } }\n",
                )],
                LibSource::Embedded,
                "i386-linux",
            );
            let program = r.program.as_ref().expect("checked");
            let mut dcx = enrang_diag::DiagCtx::new();
            let _ = enrang_sema::check_sizes(program, &r.tcx, &mut dcx);
            let found: Vec<String> = dcx
                .take()
                .iter()
                .map(|d| {
                    let loc = r.map.loc(d.primary.span.lo);
                    format!("{} {}:{}", d.code.name(), loc.line, loc.col)
                })
                .collect();
            assert_eq!(found, ["EN0435 1:44"]);
        },
    );
    h.case(
        "survivors/fix-6: a `Box` field has no default (M17, S:582)",
        || {
            let r = main_lib(
                "const a = new Node();\nconst b = new Node {};\nconsole.log(a, b);\npublic class Node { public next: Box<i64>; }\npublic class Priv { private b: Box<i64>; }\n",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0433 1:11 `new Node()` leaves `next` unset [this field has no default]",
                    "EN0433 2:11 missing field `next` [every field without a default must be set]",
                    "EN0448 5:14 `Priv` needs a constructor: `b` has no default [`b` is `private`, so no named form can set it]",
                ]
            );
        },
    );
}

fn types_minor(h: &mut Harness) {
    h.case(
        "classes/fix-6: helps and labels that can be followed: an overload at an `fn` type, a private abstract, a static base, bounds shown",
        || {
            let r = main_lib(
                "const h: fn(n: bool) => string = describe;
const g = describe;
public function describe(n: int): string { return \"\"; }
public function describe(s: &string): string { return \"\"; }
public abstract class A { private abstract f(): void; }
public class B extends A {}
public class Animal { public static make(): i64 { return 0; } }
public class Cat extends Animal { public override make(): i64 { return 1; } }
public interface Gener { map<U extends Copy>(x: &U): i64; }
public class Bnd implements Gener { public map<U>(x: &U): i64 { return 0; } }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0401 1:34 mismatched types: no overload of `describe` is `fn(bool) => string` [`describe` has 2 overloads]",
                    "EN0410 2:11 cannot infer which overload of `describe` is meant [`describe` has 2 overloads]",
                    "EN0446 6:14 `B` does not implement `A.f` [`B` is not `abstract`]",
                    "EN0443 8:51 `make` overrides nothing in `Animal` [`Animal.make` is `static`, so it has no method-table slot to replace]",
                    "EN0416 10:29 `Bnd` does not satisfy `Gener`: `map` has another signature [required by this `implements`]",
                ]
            );
            assert_eq!(
                all_helps(&r)[..2],
                [
                    "give it an expected type: `const g: fn(n: int) => string = describe;`",
                    "`A.f` is `private`, so no subclass can implement it: declare `B` `abstract`, or make it `protected` in `A`",
                ]
            );
            let notes: Vec<String> = r.diags[4]
                .entries
                .iter()
                .map(|e| e.text.clone())
                .collect();
            assert!(
                notes.iter().any(|n| n.contains("map<U extends Copy>(x: &U): i64")),
                "{notes:?}"
            );
        },
    );
}

fn types_minor2(h: &mut Harness) {
    h.case(
        "overload/fix-6: two bounds declaring one generic member are one member; differing bounds are shown (S:762)",
        || {
            let r = main_lib(
                "public interface G1 { map<U>(x: &U): i64; }
public interface G2 { map<U>(x: &U): i64; }
public interface G3 { map<U extends Copy>(x: &U): i64; }
public function h<T extends G1 & G2>(x: &T): i64 { return x.map(&1); }
public function k<T extends G1 & G3>(x: &T): i64 { return x.map(&1); }
",
            );
            assert_eq!(r.codes(), ["EN0451"]);
            let notes: Vec<String> = r.diags[0]
                .entries
                .iter()
                .map(|e| e.text.clone())
                .collect();
            assert!(
                notes.iter().any(|n| n.contains("map<U extends Copy>(x: &U): i64")),
                "{notes:?}"
            );
        },
    );
    h.case(
        "views/fix-6: the overload a view's help adds keeps the parameters' defaults (S:766)",
        || {
            let r = main_lib(
                "const s: u8[3] = [1, 2, 3];
a(s.slice(0, 2));
public function a<T>(x: &T, n: i64 = 0): void { if (n < 3) { b(x, n + 1); } }
public function b<T>(x: &T, n: i64): void { a(x, n); const p = x as *T; }
",
            );
            assert_eq!(all_helps(&r), ["add `a<T>(x: &Slice<T>, n: i64 = 0)`"]);
        },
    );
}
