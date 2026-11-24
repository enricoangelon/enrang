//! The fifth review-fix stage's cases (`fix-5`, plan h.1 stage 6), each named after
//! the area it checks: `Result<T, E>`'s implied `E extends Error` (S:1140), object
//! shapes that name a generic function's type parameters (S:601), C20 at a
//! reference (S:678), a `move` method's `this` (N7, S:588), C22's value type through
//! `new Box` (F1, T:858), closure types at an arrow's parameter (EN0705, S:968),
//! `@dll`'s ABI (C16, S:674), a borrowed interface temporary (F7, T:862), one
//! EN1006 for `Result<T, Error>`, paths that re-enter the input's directory (G31),
//! S:629's head, the operands of EN0430's note (S:688), EN0413's call, EN1042's
//! note, did-you-mean in a pattern, and an annotation a position rule rejects.

use enrang_hir::{Abi, ExprKind, StmtKind};
use enrang_sema::LibSource;
use enrang_testkit::{Harness, TempDir};

use crate::paths::{body, diags, main_lib};
use crate::support::{Run, run_in, run_with};

pub fn register(h: &mut Harness) {
    generic(h);
    coercions(h);
    receivers(h);
    interfaces(h);
    loading(h);
    wording(h);
}

/// The helps of the only diagnostic of `r`.
fn helps(r: &Run) -> Vec<String> {
    assert_eq!(r.diags.len(), 1, "{}", r.rendered());
    r.diags[0].helps.iter().map(|h| h.message.clone()).collect()
}

fn generic(h: &mut Harness) {
    h.case(
        "generic/fix-5: a written `Result<T, E>` with no error type is EN0454 alone (S:1140)",
        || {
            // The real library's `Result<T, E extends Error>`: its own bound is
            // EN0454's, never also EN0419.
            let r = main_lib(
                "public function f(): Result<i64, string> { unreachable(); }
public function g(r: Result<i64, Plain>): void {}
public class Holder { public r: Result<i64, i64>; }
public class Plain { public code: i64; }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0454 1:34 `string` is not an error type [the error type of this `Result`]",
                    "EN0454 2:34 `Plain` is not an error type [the error type of this `Result`]",
                    "EN0454 3:45 `i64` is not an error type [the error type of this `Result`]",
                ]
            );
        },
    );
    h.case(
        "generic/fix-5: writing `Result<T, E>` implies `E extends Error` (S:1140, S2-32-lift)",
        || {
            // `lift<T, E>` is unbounded, yet its `E` meets `inner`'s `Error` bound,
            // and `r?` turns it into a `Failure`.
            main_lib(
                "const r: Result<u8, Bus> = Err(Bus.Busy);
console.log(outer(r), lift(r));

private function outer<T, E>(r: Result<T, E>): Result<T> {
  return inner(r);
}

private function inner<T, E extends Error>(r: Result<T, E>): Result<T> {
  return r?;
}

private function lift<T, E>(r: Result<T, E>): Result<T> {
  return r?;
}

public enum Bus {
  Busy,
}
",
            )
            .clean();
            // A parameter that no written `Result` takes as its error type gets no
            // bound: `inner` still refuses it.
            let r = main_lib(
                "private function outer<T, E>(r: Result<T, Failure>, e: E): void {
  need(e);
}

private function other<K, V>(p: &Pair<K, V>, v: V): void {
  need(v);
}

private function need<E extends Error>(e: E): void {}

public class Pair<K, V> {
  public k: K;
  public v: V;
}
",
            );
            assert_eq!(r.codes(), ["EN0419", "EN0419"], "{}", r.rendered());
        },
    );
    h.case(
        "generic/fix-5: an object shape that names a type parameter binds it (S:601, EP-06-opt)",
        || {
            let r = main_lib(
                "const a = { v: 5 as i64 };
show<i64>(&a);
show(&a);
first<i64>(a);
first({ v: 8 });
const b = { v: 6 as i64, w: true };
first(b);
put(&a, 9);
const n: i64 = get(&a);
const c = new C { v: 3 };
show(&c);
show(&{ v: 7 });

private function show<T>(o: &{ v: T }): void {
  console.log(o.v);
}

private function first<T>(o: { v: T }): void {
  console.log(o.v);
}

private function put<T>(o: &{ v: T }, x: T): void {
  console.log(o.v, x);
}

private function get<T extends Copy>(o: &{ v: T }): T {
  return o.v;
}

public class C {
  public v: i64;
}
",
            );
            r.clean();
            // A field of another type than the type argument, and an argument after
            // the shape bound the parameter.
            let r = main_lib(
                "const a = { v: \"x\" };
show<i64>(&a);
put(&a, 9);
const k = get(&{ v: 1 as i64 });
const s: string = k;

private function show<T>(o: &{ v: T }): void {
  console.log(o.v);
}

private function put<T>(o: &{ v: T }, x: T): void {
  console.log(o.v, x);
}

private function get<T extends Copy>(o: &{ v: T }): T {
  return o.v;
}
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0401 2:11 mismatched types: expected `{ v: i64 }`, found `{ v: string }` [`v` is `string` here]",
                    "EN0401 3:9 mismatched types: expected `string`, found `int` [this is `int`]",
                    "EN0401 5:19 mismatched types: expected `string`, found `i64` [this is `i64`]",
                ]
            );
            // A field that cannot bind the parameter is a mismatch, though the
            // parameter stays unknown.
            let r = main_lib(
                "const a = { v: 5 as i64 };\nshow(&a);\nprivate function show<T>(o: &{ v: T[] }): void {}\n",
            );
            assert!(
                diags(&r).contains(
                    &"EN0401 2:6 mismatched types: expected `{ v: T[] }`, found `{ v: i64 }` [`v` is `i64` here]"
                        .to_owned()
                ),
                "{}",
                r.rendered()
            );
            // A generic alias of an object type with an optional field (EP-06-opt).
            main_lib(
                "const five: i64 | null = 5;
let a: Opt<i64 | null> = { v: five };
put<i64 | null>(&a, null);
let b: Opt<i64> = { v: 5 };
put<i64>(&b, 6);
put(&b, 7);

private function put<T>(o: &Opt<T>, x: T): void {
  o.v = x;
}

public type Opt<T> = { v?: T };
",
            )
            .clean();
        },
    );
}

fn coercions(h: &mut Harness) {
    h.case(
        "typeck/fix-5: C20 at a reference outside a parameter keeps the real shape (S:678)",
        || {
            let r = main_lib(
                "const p = { name: \"Ada\", age: 36 };
const q: &{ name: string } = &p;
const u = new User { name: \"Bo\", age: 2 };
const r: &{ name: string } | null = &u;
console.log(q.name, r?.name, nameOf(&p));
pass(p);

private function nameOf(x: &{ age: i64, name: string }): &{ name: string } {
  return x;
}

private function pass(x: { name: string, age: i64 }): void {
  const y: &{ name: string } = &x;
  console.log(y.name);
}

public class User {
  public name: string;
  public age: i64;
}
",
            );
            r.clean();
            // No adjust: the reference is the object's own.
            let statements = r.program.as_ref().unwrap().statements.as_ref().unwrap();
            let StmtKind::Let { init: Some(q), .. } = &statements.root.stmts[1].kind else {
                panic!("a `let`");
            };
            assert!(q.adjust.is_empty(), "{:?}", q.adjust);
            assert!(matches!(q.kind, ExprKind::Borrow(_)));
            let StmtKind::Let { init: Some(r_init), .. } = &statements.root.stmts[3].kind else {
                panic!("a `let`");
            };
            assert_eq!(r_init.adjust, [enrang_hir::Adjust::WrapNullRef]);
            // A field it lacks, or a field of another type, is no subset.
            let r = main_lib(
                "const p = { name: \"Ada\", age: 36 };
const q: &{ name: string, city: string } = &p;
const s: &{ name: i64 } = &p;
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0401 2:44 mismatched types: expected `&{ city: string, name: string }`, found `&{ age: int, name: string }` [this is `&{ age: int, name: string }`]",
                    "EN0401 3:27 mismatched types: expected `&{ name: i64 }`, found `&{ age: int, name: string }` [this is `&{ age: int, name: string }`]",
                ]
            );
        },
    );
    h.case(
        "typeck/fix-5: EN0440's `keep a reference` help is for a whole annotated initialiser only (S:601)",
        || {
            let r = main_lib(
                "const p = { name: \"Ada\", age: 36 };
const card = new Card { who: p };
console.log(card.who.name);

public class Card {
  public who: { name: string };
}
",
            );
            assert_eq!(helps(&r), ["build the smaller object: `{ name: p.name }`"]);
            let r = main_lib(
                "const q = { name: \"Bo\", age: 2 };
const list: { name: string }[] = [q];
console.log(list.length());
",
            );
            assert_eq!(helps(&r), ["build the smaller object: `{ name: q.name }`"]);
            let r = main_lib(
                "const p = { name: \"Ada\", age: 36 };
const q: { name: string } = p;
console.log(q.name);
",
            );
            assert_eq!(
                helps(&r),
                [
                    "build the smaller object: `{ name: p.name }`",
                    "or keep a reference: `const q = &p;`"
                ]
            );
        },
    );
    h.case(
        "typeck/fix-5: an object type where an interface of methods is expected is S:629's EN0401",
        || {
            let r = main_lib(
                "const q = { x: 1.0, y: 2.0 };
show(&q);
const r: &Point = &q;
const o: &Point | null = &q;

private function show(p: &Point): void {}

public interface Point {
  x(): &f64;
  y(): &f64;
}
",
            );
            let label = "[this is `{ x: f64, y: f64 }`, which has no methods]";
            let head = "`Point` now has a method, so it is an interface, not an object type";
            assert_eq!(
                diags(&r),
                [
                    format!("EN0401 2:6 {head} {label}"),
                    format!("EN0401 3:19 {head} {label}"),
                    format!("EN0401 4:26 {head} {label}"),
                ]
            );
            assert!(
                r.diags
                    .iter()
                    .all(|d| d.helps.len() == 1 && d.helps[0].message == "make it a class")
            );
            // A fields-only interface is the object type, and an empty interface is
            // satisfied by anything.
            main_lib(
                "const q = { x: 1.0, y: 2.0 };
show(&q);
take(&q);

private function show(p: &Point): void {}

private function take(e: &Empty): void {}

public interface Point {
  x: f64;
  y: f64;
}

public interface Empty {}
",
            )
            .clean();
        },
    );
}

fn receivers(h: &mut Harness) {
    h.case(
        "classes/fix-5: at an expected type `C`, a non-Copy `this` is a move of `*this` (N7)",
        || {
            let r = main_lib(
                "public final class Lexer {
  private src: &string;
  public constructor(s: &string) { this.src = s; }
  public move withSrc(s: &string): Lexer { this.src = s; return this; }
  public move keep(): void { const me: Lexer = this; }
}
",
            );
            r.clean();
            let b = body(&r, "main::Lexer::withSrc");
            let StmtKind::Return(Some(e)) = &b.root.stmts[1].kind else {
                panic!("a `return`: {:?}", b.root.stmts[1].kind);
            };
            let ExprKind::Deref(inner) = &e.kind else {
                panic!("a move of `*this`: {e:?}");
            };
            assert!(matches!(inner.kind, ExprKind::Local(_)));
            assert_eq!(r.tcx.ty_string(e.ty), "Lexer");
            assert!(e.adjust.is_empty());
            // Whether the method may move it is phase 3's (EN0603); a Copy class
            // still reads through (C05), and `&C` stays the reference.
            let r = main_lib(
                "public class Animal {
  public constructor(public name: string) {}
  public into(): Animal { return this; }
  public me(): &Animal { return this; }
}
public class P implements Copy {
  public x: i64;
  public copy(): P { return this; }
}
",
            );
            r.clean();
            let b = body(&r, "main::P::copy");
            let StmtKind::Return(Some(e)) = &b.root.stmts[0].kind else {
                panic!("a `return`");
            };
            assert!(matches!(e.kind, ExprKind::Local(_)), "{e:?}");
            assert_eq!(e.adjust, [enrang_hir::Adjust::ReadThrough]);
        },
    );
}

fn interfaces(h: &mut Harness) {
    h.case(
        "iface/fix-5: `new Box(v)` at `Box<I>` takes only a value type (C22, F1)",
        || {
            let src = |class: &str| {
                format!(
                    "const text = \"hello\";
const b: Box<Speaker> = new Box(new Echo(&text));
console.log(b.speak());

public interface Speaker {{
  speak(): string;
}}

{class}
"
                )
            };
            let r = main_lib(&src(
                "private class Echo implements Speaker {
  private text: &string;
  public constructor(text: &string) { this.text = text; }
  public speak(): string { return `${this.text}`; }
}",
            ));
            assert_eq!(
                diags(&r),
                ["EN0701 2:33 a `Speaker` can't hold an `Echo`, because `Echo` holds a reference [`Echo` holds a reference]"]
            );
            main_lib(&src(
                "private class Echo implements Speaker {
  private text: string;
  public constructor(text: &string) { this.text = text.toString(); }
  public speak(): string { return this.text.clone(); }
}",
            ))
            .clean();
        },
    );
    h.case(
        "iface/fix-5: a borrowed interface temporary is EN1006 (F7, T:862)",
        || {
            let r = main_lib(
                "const b: Box<Speaker> = new Box(new Dog {});
introduce(&b.unbox());
introduce(&*b);

private function introduce(s: &Speaker): void {
  console.log(s.speak());
}

public interface Speaker {
  speak(): string;
}

public final class Dog implements Speaker {
  public speak(): string { return \"woof\"; }
}
",
            );
            assert_eq!(
                diags(&r),
                ["EN1006 2:12 an interface type by value outside a parameter is not supported yet [this is a `Speaker` by value]"]
            );
        },
    );
    h.case(
        "positions/fix-5: `Result<T, Error>` is EN1006 once, and its `E` is `Error` (S:1140)",
        || {
            let r = main_lib(
                "public function load(): Result<i64, Error> {
  return Ok(1);
}
public function keep(r: Result<u8, Error>): Result<u8, Error> { return r; }
public type R = Result<i64, Error>;
",
            );
            let msg = "an interface type by value outside a parameter is not supported yet [`Error` by value in a type argument]";
            assert_eq!(
                diags(&r),
                [
                    format!("EN1006 1:37 {msg}"),
                    format!("EN1006 4:36 {msg}"),
                    format!("EN1006 4:56 {msg}"),
                    format!("EN1006 5:29 {msg}"),
                ]
            );
            assert_eq!(
                r.diags[0].helps[0].message,
                "for errors, `Result<i64>`, because `Error` is a family of types, not a type"
            );
        },
    );
    h.case(
        "positions/fix-5: a local's annotation that a position rule rejects reports once",
        || {
            let r =
                main_lib("const n: i64 = 5;\nconst b: Box<&i64> = new Box(n);\nconsole.log(b);\n");
            assert_eq!(r.codes(), ["EN0701"], "{}", r.rendered());
            let r = main_lib(
                "const s: Point = { x: 1.0 };
public interface Point { x(): &f64; }
",
            );
            assert_eq!(r.codes(), ["EN1006"], "{}", r.rendered());
            // A rejected annotation keeps its own report where nothing else reads it.
            let r = main_lib("const v: Slice<u8>[] = [];\n");
            assert_eq!(r.codes(), ["EN0401"], "{}", r.rendered());
        },
    );
    h.case(
        "closure/fix-5: a closure type at an arrow's parameter is EN0705 (S:968, T:597)",
        || {
            let r = main_lib(
                "const h = (g: (k: u8) => void) => g(1);
const i = (g: ((k: u8) => void) | null) => 1;
const j = (g: ((k: u8) => void)[]) => 1;
",
            );
            let head = "a closure type can be written only as a parameter's type";
            assert_eq!(
                diags(&r),
                [
                    format!("EN0705 1:15 {head} [inside another closure type]"),
                    format!("EN0705 2:16 {head} [inside another closure type]"),
                    format!("EN0705 3:16 {head} [inside another closure type]"),
                ]
            );
            main_lib("const h = (g: fn(k: u8) => void) => g(1);\nconsole.log(h);\n").clean();
        },
    );
    h.case("closure/fix-5: a `@dll` function has `@abi(\"win64\")` (C16, S:674)", || {
        let src = |ty: &str| {
            format!(
                "@dll(\"kernel32\") private declare function Beep(p: *u8, v: u8): void;
public function wire(): void {{
  const c: {ty} = Beep;
}}
"
            )
        };
        let r = run_with(
            &[(
                "main.en",
                &src("@abi(\"win64\") unsafe fn(p: *u8, v: u8) => void"),
            )],
            LibSource::Embedded,
            "x86_64-windows",
        );
        r.clean();
        assert_eq!(r.tcx.sig(r.def("main::Beep")).abi, Abi::Win64);
        let r = run_with(
            &[("main.en", &src("unsafe fn(p: *u8, v: u8) => void"))],
            LibSource::Embedded,
            "x86_64-windows",
        );
        assert_eq!(
            diags(&r),
            ["EN0401 3:47 mismatched types: expected `unsafe fn(*u8, u8) => void`, found `@abi(\"win64\") unsafe fn(*u8, u8) => void` [this is `@abi(\"win64\") unsafe fn(*u8, u8) => void`]"]
        );
    });
}

fn loading(h: &mut Harness) {
    h.case(
        "load/fix-5: a path that leaves the directory and comes back is the same module (G31)",
        || {
            let dir = TempDir::new("review5-reenter");
            let app = dir.path().join("root").join("app");
            std::fs::create_dir_all(&app).unwrap();
            std::fs::write(
                app.join("main.en"),
                "import * as me from \"../app/main\";\npublic function main(): void {}\n",
            )
            .unwrap();
            let r = run_in(&app, "main.en");
            assert_eq!(
                diags(&r),
                ["EN0304 1:21 import cycle: `main.en` imports itself [this import closes the cycle]"]
            );
            assert!(r.rendered().contains(" --> main.en:1:21"), "{}", r.rendered());
            assert!(!r.rendered().contains("--> ../"), "{}", r.rendered());
        },
    );
    h.case(
        "load/fix-5: a folder namespace that holds the input's directory reads its modules once (G31, G34)",
        || {
            let dir = TempDir::new("review5-folder");
            let app = dir.path().join("root").join("app");
            std::fs::create_dir_all(&app).unwrap();
            std::fs::write(
                app.join("main.en"),
                "import * as root from \"../\";\npublic function main(): void {}\n",
            )
            .unwrap();
            // The entry is never a module of the folder (G34), and is loaded once.
            let r = run_in(&app, "main.en");
            r.clean();
            let paths: Vec<String> = r
                .tcx
                .modules()
                .filter(|(_, m)| !m.library)
                .map(|(_, m)| m.path.to_string())
                .collect();
            assert_eq!(paths, ["main", "..", "."], "{paths:?}");
            // A module with statements below it is EN0312 at the import, once: a
            // module of a sibling folder of the directory, reached through `..`.
            let lib = dir.path().join("root").join("lib");
            std::fs::create_dir_all(&lib).unwrap();
            std::fs::write(lib.join("x.en"), "console.log(\"x\");\n").unwrap();
            let r = run_in(&app, "main.en");
            assert_eq!(
                diags(&r),
                ["EN0312 1:23 `x.en` has top-level statements, so it can't be imported [the folder imported here holds `../lib/x.en`]"]
            );
            std::fs::remove_file(lib.join("x.en")).unwrap();
            // A module of the directory itself, below `..` through `.`.
            std::fs::write(app.join("side.en"), "console.log(\"side\");\n").unwrap();
            let r = run_in(&app, "main.en");
            assert_eq!(
                diags(&r),
                ["EN0312 1:23 `side.en` has top-level statements, so it can't be imported [the folder imported here holds `side.en`]"]
            );
            // The directory imported as a namespace by the path that re-enters it.
            std::fs::write(
                app.join("main.en"),
                "import * as here from \"../app\";\npublic function main(): void {}\n",
            )
            .unwrap();
            let r = run_in(&app, "main.en");
            assert_eq!(
                diags(&r),
                ["EN0312 1:23 `side.en` has top-level statements, so it can't be imported [the folder imported here holds `side.en`]"]
            );
        },
    );
}

fn wording(h: &mut Harness) {
    h.case(
        "lower/fix-5: EN1030 names an interface passed by value as one",
        || {
            let r = run_with(
                &[(
                    "main.en",
                    "@dll(\"kernel32.dll\") public declare function Iface(c: Eq): void;\n",
                )],
                LibSource::Embedded,
                "x86_64-windows",
            );
            assert_eq!(
                diags(&r),
                ["EN1030 1:55 this foreign ABI is not supported yet [an interface passed by value]"]
            );
        },
    );
    h.case(
        "typeck/fix-5: EN0430's TypeScript note gives the operands' own values (S:688)",
        || {
            let r = main_lib(
                "const x = 10 / 4;
const y = -7 / 2;
const w = (2 + 8) / 3;
let a = 7;
let b = 2;
const c = a / b;
console.log(x, y, w, c);
",
            );
            let notes: Vec<String> = r
                .diags
                .iter()
                .map(|d| d.entries.last().map(|e| e.text.clone()).unwrap_or_default())
                .collect();
            assert_eq!(
                notes,
                [
                    "TypeScript would give `2.5` for `10 / 4`; here it is `2`.",
                    "TypeScript would give `-3.5` for `-7 / 2`; here it is `-3`.",
                    "TypeScript would give `3.3333333333333335` for `(2 + 8) / 3`; here it is `3`.",
                    "TypeScript would give `3.5` for `7 / 2`; here it is `3`.",
                ],
                "{}",
                r.rendered()
            );
            // `MIN / -1` has no quotient: the note keeps its example.
            let r = main_lib(
                "const m = (-170141183460469231731687303715884105727 - 1) / -1;\nconsole.log(m);\n",
            );
            assert!(
                r.rendered()
                    .contains("TypeScript would give `3.5` for `7 / 2`; here it is `3`."),
                "{}",
                r.rendered()
            );
        },
    );
    h.case(
        "member/fix-5: EN0413's help keeps the call and its arguments",
        || {
            let r = main_lib(
                "const n = find(\"a\")?.length();
const m = find(\"a\")?.slice(0, 1);
console.log(n, m);
private function find(s: &string): string | null { return null; }
",
            );
            let helps: Vec<String> = r.diags.iter().map(|d| d.helps[0].message.clone()).collect();
            assert_eq!(
                helps,
                [
                    "bind it first: `const v = find(\"a\");`, then `v?.length()`",
                    "bind it first: `const v = find(\"a\");`, then `v?.slice(0, 1)`",
                ]
            );
        },
    );
    h.case(
        "pattern/fix-5: EN1042's note fits the array's kind, and did-you-mean skips bound names",
        || {
            let r = main_lib(
                "const xs: i64[] = [1, 2];
const fixed: i64[2] = [4, 5];
const [a, b] = xs;
const [c, d] = &fixed;
",
            );
            let notes: Vec<String> = r.diags.iter().map(|d| d.entries[0].text.clone()).collect();
            assert_eq!(
                notes,
                [
                    "an array's length is known only when the program runs, so a pattern can't name its elements",
                    "only a tuple is destructured by position; a fixed array's elements are read by index",
                ],
                "{}",
                r.rendered()
            );
            let src = |pat: &str| {
                format!(
                    "const p = new P {{ x: 1, y: 2 }};
const {pat} = &p;

public class P {{
  public x: i64;
  public y: i64;
}}
"
                )
            };
            let r = main_lib(&src("{ x, w }"));
            assert_eq!(helps(&r), ["did you mean `y`?"]);
            let r = main_lib(&src("{ w }"));
            assert_eq!(helps(&r), ["did you mean `x`?"]);
        },
    );
}
