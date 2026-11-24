//! Generic calls (plan d.9's `generic.rs`; SPEC 4.7 S:729-732, 4.10, S:323,
//! S:560, S:764; A:888; owner 4A): explicit type arguments all or none (EN0309);
//! the three steps with the hint dropped and retried; `&?T` against a value
//! (EN0612); `?T` against `&U` read through a Copy `U`, else EN0703; an unresolved
//! `T` (EN0410) and `Ok`'s `E` defaulting to `Failure`; each type argument against
//! its bounds (EN0419: class bounds by name, sealed bounds, `where` clauses at the
//! call), a reference (EN0703, with the `== null` and `??` fix-its), an interface
//! (EN1006) or a type holding a reference (EN0701); volatile access outside
//! `VolatileValue` (EN0805, T:614); written types in declarations against their
//! classes' bounds (`dup<T>(a: &Atomic<T>)`, T:612).

use enrang_hir::{Adjust, Callee, ExprKind, StmtKind};
use enrang_sema::LibSource;
use enrang_testkit::Harness;

use crate::paths::{body, diags, main_en, main_lib, ty};
use crate::support::{Run, run_with};

pub fn register(h: &mut Harness) {
    inference(h);
    optional(h);
    hints(h);
    references(h);
    bounds(h);
    sealed(h);
    arguments(h);
    review(h);
}

/// The initialiser of the `n`-th `const`/`let` of `path`'s body.
fn let_init<'r>(r: &'r Run, path: &str, n: usize) -> &'r enrang_hir::Expr {
    body(r, path)
        .root
        .stmts
        .iter()
        .filter_map(|s| match &s.kind {
            StmtKind::Let { init: Some(e), .. } => Some(e),
            _ => None,
        })
        .nth(n)
        .expect("an initialiser")
}

/// The type arguments a call's callee was instantiated with, as strings.
fn inst(r: &Run, e: &enrang_hir::Expr) -> Vec<String> {
    let ExprKind::Call {
        callee: Callee::Fn(f),
        ..
    } = &e.kind
    else {
        panic!("not a call of a function: {e:?}");
    };
    r.tcx
        .list(f.args)
        .iter()
        .map(|&t| r.tcx.ty_string(t))
        .collect()
}

fn i386(src: &str) -> Run {
    run_with(&[("main.en", src)], LibSource::Embedded, "i386-linux")
}

fn inference(h: &mut Harness) {
    h.case(
        "generic/a call binds its type parameters from its arguments and its expected type",
        || {
            let r = main_en(
                "public function id<T>(x: T): T { return x; }
public function pair<A, B>(a: A, b: B): B { return b; }
public function f(n: i64): void {
  const a = id(n);
  const b: i64 = id(5);
  const c = pair(true, n);
  const d = id(7);
}
",
            );
            r.clean();
            assert_eq!(inst(&r, let_init(&r, "main::f", 0)), ["i64"]);
            assert_eq!(inst(&r, let_init(&r, "main::f", 1)), ["i64"]);
            assert_eq!(inst(&r, let_init(&r, "main::f", 2)), ["bool", "i64"]);
            // A literal with nothing else deciding it takes its default.
            assert_eq!(inst(&r, let_init(&r, "main::f", 3)), ["int"]);
            assert_eq!(ty(&r, let_init(&r, "main::f", 2).ty), "i64");
        },
    );
    h.case(
        "generic/explicit type arguments, all given: `id<i64>(5)` makes the literal an `i64`",
        || {
            let r = main_en(
                "public function id<T>(x: T): T { return x; }
public function f(): void { const a = id<i64>(5); const b = id<u8>(300); }
",
            );
            assert_eq!(
                r.codes(),
                ["EN0411"],
                "300 does not fit `u8`: {}",
                r.rendered()
            );
        },
    );
    h.case(
        "generic/EN0309: explicit type arguments are all or none (S:729)",
        || {
            let r = main_en(
                "public function id<T>(x: T): T { return x; }
public function pair<A, B>(a: A, b: B): A { return a; }
public function f(): void { const a = id<i64, i64>(5); const c = pair<i64>(1, 2); }
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0309]: `id` takes 1 type argument, but 2 were given
 --> main.en:3:42
  |
3 | public function f(): void { const a = id<i64, i64>(5); const c = pair<i64>(1, 2); }
  |                                          ^^^^^^^^ expected 1 type argument
  |
  = explain: run `enrang explain EN0309`

error[EN0309]: `pair` takes 2 type arguments, but 1 was given
 --> main.en:3:71
  |
3 | public function f(): void { const a = id<i64, i64>(5); const c = pair<i64>(1, 2); }
  |                                                                       ^^^ expected 2 type arguments
  |
  = explain: run `enrang explain EN0309`

error: aborting due to 2 previous errors
"
            );
        },
    );
    h.case(
        "generic/EN0410: a type parameter nothing decides (S:729)",
        || {
            let r = main_en(
                "public function make<T>(): T[] { unreachable(); }
public function f(): void { const a = make(); const b: i64[] = make(); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0410 2:39 cannot infer the type of `T` in `make(...)` [nothing here decides its type]"]
            );
        },
    );
    h.case(
        "generic/`Ok(5)` with nothing deciding `E` is a `Result<int, Failure>` (S:1139)",
        || {
            let r = main_lib("public function f(): void { const r = Ok(5); }\n");
            r.clean();
            assert_eq!(ty(&r, let_init(&r, "main::f", 0).ty), "Result<int>");
            assert_eq!(inst(&r, let_init(&r, "main::f", 0)), ["int", "Failure"]);
        },
    );
    h.case(
        "generic/a generic method of a generic class: the receiver's arguments, then its own",
        || {
            let r = main_en(
                "public class Stack<T> {
  public xs: T[] = [];
  public map<U>(f: fn(x: &T) => U): Stack<U> { unreachable(); }
  public first(): T { unreachable(); }
}
public function len(s: &string): i64 { return 0; }
public function f(s: &Stack<string>): void { const t = s.map(len); const u = t.first(); }
",
            );
            r.clean();
            assert_eq!(ty(&r, let_init(&r, "main::f", 0).ty), "Stack<i64>");
            assert_eq!(ty(&r, let_init(&r, "main::f", 1).ty), "i64");
        },
    );
}

fn optional(h: &mut Harness) {
    h.case(
        "generic/`b?.get(5)` on a nullable receiver is an optional chain of a nullable result",
        || {
            let r = main_en(
                "public class Bag { public get<T>(x: T): T { return x; } public put<T>(x: T): void {} }
public function f(b: Bag | null): void { const v = b?.get(5); const w = b?.put(1); }
",
            );
            r.clean();
            let v = let_init(&r, "main::f", 0);
            assert!(matches!(v.kind, ExprKind::OptionalChain(_)), "{v:?}");
            assert_eq!(ty(&r, v.ty), "int | null");
            let w = let_init(&r, "main::f", 1);
            let ExprKind::OptionalChain(chain) = &w.kind else {
                panic!("{w:?}")
            };
            assert!(chain.void_result);
            assert_eq!(ty(&r, w.ty), "void");
        },
    );
}

fn hints(h: &mut Harness) {
    h.case(
        "generic/S:730: the hint is dropped and the call typed again: `Box<Dog>` meets C21",
        || {
            let r = main_lib(
                "public class Animal { public constructor(public name: string) {} }
public class Dog extends Animal { public constructor(name: string) { super(name); } }
public function f(): void {
  const pets: Box<Animal>[] = [new Box(new Animal(\"Generic\")), new Box(new Dog(\"Fido\"))];
}
",
            );
            r.clean();
            let ExprKind::ArrayLit(elems) = &let_init(&r, "main::f", 0).kind else {
                panic!()
            };
            assert_eq!(ty(&r, elems[0].ty), "Box<Animal>");
            assert!(elems[0].adjust.is_empty());
            assert_eq!(ty(&r, elems[1].ty), "Box<Dog>");
            assert_eq!(elems[1].adjust, [Adjust::Upcast]);
        },
    );
    h.case(
        "generic/S:730: `Ok(x)` at `Result<i64 | null>` keeps `T := i64 | null` and wraps `x`",
        || {
            let r = main_lib(
                "public function f(x: i64): Result<i64 | null> { const r: Result<i64 | null> = Ok(x); return r; }\n",
            );
            r.clean();
            let call = let_init(&r, "main::f", 0);
            assert_eq!(inst(&r, call), ["i64 | null", "Failure"]);
            let ExprKind::Call { args, .. } = &call.kind else {
                panic!()
            };
            assert_eq!(args[0].adjust, [Adjust::WrapNull]);
        },
    );
    h.case(
        "generic/when both ways fail, the error reported is the hinted way's",
        || {
            let r = main_en(
                "public function id<T>(x: T): T { return x; }
public function f(): void { const a: i64 = id(true); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0401 2:47 mismatched types: expected `i64`, found `bool` [this is `bool`]"]
            );
        },
    );
}

fn references(h: &mut Harness) {
    h.case(
        "generic/S:731: `&?T` against a value binds `T := U` and is EN0612",
        || {
            let r = main_en(
                "public function bump<T>(x: &T): void {}
public function f(n: i64): void { bump(n); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0612 2:40 missing `&`: `bump` takes a reference [expected `&i64`, found `i64`]"]
            );
        },
    );
    h.case(
        "generic/S:731: `&?T` against `&Slice<U>` binds `T := Slice<U>`",
        || {
            let r = main_lib(
                "public function show<T>(x: &T): void {}
public function f(xs: &Slice<u8>): void { show(xs); }
",
            );
            r.clean();
            let b = body(&r, "main::f");
            let StmtKind::Expr(e) = &b.root.stmts[0].kind else {
                panic!()
            };
            assert_eq!(inst(&r, e), ["Slice<u8>"]);
        },
    );
    h.case(
        "generic/S:731: `?T` against `&U` reads through a Copy `U`, else is EN0703",
        || {
            let r = main_lib(
                "public function keep<T>(x: T): T { return x; }
public class User { public name: string; }
public function f(u: User, n: i64): void {
  const a = keep(&n);
  const b = keep(&u);
}
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0703]: `T` can't stand for the reference `&User`
 --> main.en:5:18
  |
5 |   const b = keep(&u);
  |                  ^^ this makes `T` the reference `&User`
  |
  = explain: run `enrang explain EN0703`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "generic/`?T` against `&U` takes another binding first: `T := i64` from the second",
        || {
            let r = main_en(
                "public function same<T>(a: T, b: T): T { return b; }
public function f(n: i64, m: i64): void { const a = same(&n, m); }
",
            );
            r.clean();
            let call = let_init(&r, "main::f", 0);
            assert_eq!(inst(&r, call), ["i64"]);
            let ExprKind::Call { args, .. } = &call.kind else {
                panic!()
            };
            assert_eq!(args[0].adjust, [Adjust::ReadThrough]);
        },
    );
    h.case(
        "generic/T:625: `t.isNull()` on `&User | null` is EN0703 with a `== null` fix-it",
        || {
            let r = main_lib(
                "public class User { public name: string; }
public function f(t: &User | null): bool { return t.isNull(); }
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0703]: `T` can't stand for the reference `&User`
 --> main.en:2:51
  |
2 | public function f(t: &User | null): bool { return t.isNull(); }
  |                                                   ^^^^^^^^^^ this makes `T` the reference `&User`
  |
help: compare with `null`: `t == null`
  |
2 | public function f(t: &User | null): bool { return t == null; }
  |                                                   ~~~~~~~~~
  = explain: run `enrang explain EN0703`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "generic/S:1387: `t.orElse(() => d)` on a nullable reference gets the `??` fix-it",
        || {
            let r = main_lib(
                "public class User { public name: string; }
public function f(t: &User | null, d: &User): void { const u = t.orElse(() => d); }
",
            );
            assert_eq!(r.codes(), ["EN0703"], "{}", r.rendered());
            let help = &r.diags[0].helps[0];
            assert_eq!(help.message, "use `??`: `t ?? d`");
        },
    );
    h.case(
        "generic/an annotated arrow's reference result binds `U := &User`: EN0703 (S:977)",
        || {
            let r = main_lib(
                "public class User { public name: string; }
public function keepIt<U>(f: fn(u: &User) => U): void {}
public function pick(u: &User): &User { return u; }
public function f(): void { keepIt(pick); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0703 4:36 `U` can't stand for the reference `&User` [this makes `U` the reference `&User`]"]
            );
        },
    );
}

const ANIMALS: &str =
    "public class Animal { public constructor(public name: string, public age: i64) {} }
public class Dog extends Animal { public fetch(): string { return `${this.name} fetches`; } }
public final class Cat { public n: i64 = 0; }
public function oldest<T extends Animal>(xs: &Slice<T>): &T { return &xs[0]; }
public function only<T extends Cat>(x: &T): void {}
";

fn bounds(h: &mut Harness) {
    h.case(
        "generic/S:764: `oldest(&dogs).fetch()` compiles; over `&Slice<Animal>` it is EN0303",
        || {
            let r = main_lib(&format!(
                "{ANIMALS}public function main(): void {{
  const dogs = [new Dog(\"Rex\", 3), new Dog(\"Fido\", 7)];
  console.log(oldest(&dogs).fetch());
}}
public function over(xs: &Slice<Animal>): void {{ console.log(xs[0].fetch()); }}
"
            ));
            assert_eq!(
                diags(&r),
                ["EN0303 10:68 `Animal` has no member `fetch` [no such member]"]
            );
        },
    );
    h.case(
        "generic/EN0419: a class bound admits its subclasses by name, a `final` one itself alone",
        || {
            let r = main_lib(&format!(
                "{ANIMALS}public function main(): void {{
  const ints = [1, 2];
  oldest(&ints);
  const c = new Cat();
  only(&c);
  const dogs = [new Dog(\"Rex\", 3)];
  only(&dogs[0]);
}}
"
            ));
            assert_eq!(
                r.rendered(),
                "error[EN0419]: `int` does not satisfy `Animal`
 --> main.en:8:10
  |
4 | public function oldest<T extends Animal>(xs: &Slice<T>): &T { return &xs[0]; }
  |                        - the bound on `T`
...
8 |   oldest(&ints);
  |          ^^^^^ `T` must satisfy `Animal`
  |
  = explain: run `enrang explain EN0419`

error[EN0419]: `Dog` does not satisfy `Cat`
  --> main.en:12:8
   |
 5 | public function only<T extends Cat>(x: &T): void {}
   |                      - the bound on `T`
...
12 |   only(&dogs[0]);
   |        ^^^^^^^^ `T` must satisfy `Cat`
   |
   = explain: run `enrang explain EN0419`

error: aborting due to 2 previous errors
"
            );
        },
    );
    h.case(
        "generic/a type parameter meets a bound through its own bound",
        || {
            let r = main_lib(
                "public function sizes<T extends Copy>(x: &T): void {}
public function g<U>(x: &U): void { sizes(x); }
public function h<U extends Copy>(x: &U): void { sizes(x); }
public class Animal { public n: i64 = 0; }
public class Dog extends Animal {}
public function oldest<T extends Animal>(x: &T): void {}
public function k<D extends Dog>(x: &D): void { oldest(x); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0419 2:43 `U` does not satisfy `Copy` [`T` must satisfy `Copy`]"]
            );
        },
    );
    h.case(
        "generic/S:323: a `where` clause is checked at the call, the clause as the secondary",
        || {
            let r = main_lib(
                "public class Stack<T> { public xs: T[] = []; public dup(): void where T extends Copy {} }
public class C { public s: string; }
public function f(s: &Stack<C>, t: &Stack<i64>): void { s.dup(); t.dup(); }
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0419]: `C` does not satisfy `Copy`
 --> main.en:3:57
  |
1 | public class Stack<T> { public xs: T[] = []; public dup(): void where T extends Copy {} }
  |                                                                       -------------- required by this `where` clause of `dup`
2 | public class C { public s: string; }
3 | public function f(s: &Stack<C>, t: &Stack<i64>): void { s.dup(); t.dup(); }
  |                                                         ^^^^^^^ `T` must satisfy `Copy`
  |
  = explain: run `enrang explain EN0419`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "generic/a class's bounds hold for the instance a construction makes and a written type",
        || {
            let r = main_lib(
                "public class Box2<T extends Copy> { public v: T; }
public class C { public s: string; }
public function f(): void { const b = new Box2 { v: new C { s: \"x\" } }; const k = new Box2 { v: 1 }; }
public function g(b: Box2<C>): void {}
public class D extends Box2<C> {}
public class E extends Box2<i64> {}
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0419 3:39 `C` does not satisfy `Copy` [`T` must satisfy `Copy`]",
                    "EN0419 4:19 `C` does not satisfy `Copy` [`Box2` requires `T extends Copy`]",
                    "EN0419 5:24 `C` does not satisfy `Copy` [`Box2` requires `T extends Copy`]",
                ]
            );
        },
    );
}

fn sealed(h: &mut Harness) {
    h.case(
        "generic/T:612: `new Atomic<string>(...)` and generic `dup<T>(a: &Atomic<T>)` are EN0419",
        || {
            let r = main_lib(
                "import { Atomic } from \"core/atomic\";
public function dup<T>(a: &Atomic<T>): void {}
public function f(): void { const x = new Atomic<string>(\"x\"); const y = new Atomic<u8>(1); }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0419 2:24 `T` does not satisfy `AtomicValue` [`Atomic` requires `T extends AtomicValue`]",
                    "EN0419 3:39 `string` does not satisfy `AtomicValue` [`T` must satisfy `AtomicValue`]",
                ]
            );
        },
    );
    h.case(
        "generic/T:613: `testAndSet` on `Atomic<u8>` is EN0419 with a help to use `exchange`",
        || {
            let r = main_lib(
                "import { Atomic } from \"core/atomic\";
public function f(a: &Atomic<u8>, b: &Atomic<u32>): bool { b.testAndSet(1); return a.testAndSet(1); }
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0419]: `u8` does not satisfy `AtomicBits`
 --> main.en:2:84
  |
2 | public function f(a: &Atomic<u8>, b: &Atomic<u32>): bool { b.testAndSet(1); return a.testAndSet(1); }
  |                                                                                    ^^^^^^^^^^^^^^^ `T` must satisfy `AtomicBits`
  |
  = note: `testAndSet` requires `T extends AtomicBits`
help: use `exchange`: `bts` has no byte form, so `u8` has no `testAndSet`
  = explain: run `enrang explain EN0419`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "generic/T:614: volatile access outside `VolatileValue` is EN0805 at the call",
        || {
            let r = main_lib(
                "public unsafe function w<T extends Copy>(p: *T, v: T): void { p.writeVolatile(v); }
public unsafe function ok<T extends ptr.VolatileValue>(p: *T, v: T): void { p.writeVolatile(v); }
public unsafe function wide(p: *u64, v: u64): void { p.writeVolatile(v); }
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0805]: `T` can't be accessed volatile on `x86_64-linux`
 --> main.en:1:63
  |
1 | public unsafe function w<T extends Copy>(p: *T, v: T): void { p.writeVolatile(v); }
  |                                                               ^^^^^^^^^^^^^^^^^^ `T` is not a `VolatileValue`
  |
  = note: volatile access takes `u8 u16 u32 i8 i16 i32 usize isize bool` and raw pointers, and `u64 i64` on `x86_64-*`
  = explain: run `enrang explain EN0805`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "generic/T:614: `writeVolatile` of a `u64` on `i386` is EN0805; a `u32` compiles",
        || {
            let r = i386(
                "public unsafe function w(p: *u64, v: u64): void { p.writeVolatile(v); }
public unsafe function k(p: *u32, v: u32): void { p.writeVolatile(v); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0805 1:51 `u64` can't be accessed volatile on `i386-linux` [`u64` is not a `VolatileValue`]"]
            );
        },
    );
}

fn arguments(h: &mut Harness) {
    h.case(
        "generic/S:560: an interface type argument is EN1006; a borrowing class is EN0701",
        || {
            let r = main_lib(
                "public interface Speaker { speak(): string; }
public class Lexer { private src: &string; public constructor(src: &string) { this.src = src; } }
public function id<T>(x: T): T { return x; }
public function make<T>(): i64 { return 0; }
public function f(l: Lexer): void { const a = make<Speaker>(); const b = id(l); }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN1006 5:52 an interface type by value outside a parameter is not supported yet [this makes a type parameter the interface `Speaker`]",
                    "EN0701 5:77 `T` can't stand for a `Lexer`, because `Lexer` holds a reference [no generic argument can hold a reference]",
                ]
            );
        },
    );
    h.case(
        "generic/`Box<I>` is the one generic that takes an interface (S:560)",
        || {
            let r = main_lib(
                "public interface Speaker { speak(): string; }
public function f(b: Box<Speaker>): Box<Speaker> { return b; }
",
            );
            r.clean();
            // The construction binds `T := Speaker` by its hint; whether `Dog` then
            // converts is C22's (4C), but `T` itself is never EN1006 there.
            let r = main_lib(
                "public interface Speaker { speak(): string; }
public class Dog implements Speaker { public speak(): string { return \"woof\"; } }
public function f(): void { const b: Box<Speaker> = new Box(new Dog {}); }
",
            );
            assert!(
                !r.codes().contains(&"EN1006".to_owned()),
                "{}",
                r.rendered()
            );
        },
    );
    h.case(
        "generic/an implicit interface parameter's class must meet the interface (D5)",
        || {
            let r = main_lib(
                "public interface Measured { length(): isize; }
public function keep(m: &Measured): void {}
public class View { private s: &string; public constructor(s: &string) { this.s = s; } public length(): isize { return 0; } }
public function f(s: &string, v: &View): void { keep(s); keep(v); }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0401 4:54 a `&string` can't become a `&Measured`, because it may be a part of a string [this is a `&string`, not a `&Measured`]",
                    "EN0701 4:63 a `Measured` can't hold a `View`, because `View` holds a reference [only a value type becomes an interface value]",
                ]
            );
            assert_eq!(
                r.diags[0]
                    .helps
                    .iter()
                    .map(|h| h.message.as_str())
                    .collect::<Vec<_>>(),
                [
                    "take <T extends Measured>(m: &T)",
                    "or keep a copy: s.toString()"
                ]
            );
        },
    );
    h.case(
        "generic/an implicit shape parameter needs every field, public, at its type (S:601)",
        || {
            let r = main_lib(
                "public function greet(x: &{ name: string }): void {}
public class User { public name: string; public age: i64; }
public class Secret { private name: string = \"\"; }
public class Num { public name: i64; }
public function f(u: &User, s: &Secret, n: &Num): void { greet(u); greet(s); greet(n); }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0401 5:74 `Secret` has no public field `name` [this is `Secret`]",
                    "EN0401 5:84 mismatched types: expected `{ name: string }`, found `Num` [`name` is `i64` here]",
                ]
            );
            assert_eq!(r.diags[0].entries[0].text, "`name` is private to `Secret`");
        },
    );
}

/// Stage 6's review fixes of the bound checks, the hint retry and the implicit
/// shape check.
fn review(h: &mut Harness) {
    h.case(
        "generic/S:764: a parameter bounded by a subclass meets a base-class bound in written types; an unbounded one does not",
        || {
            let r = main_lib(
                "public class Animal { public age: i64 = 0; }
public class Dog extends Animal { }
public class Pen<T extends Animal> { public v: i64 = 0; }
public function f<U extends Dog>(x: &Pen<U>): void { }
public class Zoo<U extends Dog> { public pen: Pen<U> | null = null; public put(p: &Pen<U>): void { } }
public function h<U>(x: &Pen<U>): void { }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0419 6:22 `U` does not satisfy `Animal` [`Pen` requires `T extends Animal`]"]
            );
        },
    );
    h.case(
        "generic/S:638: a written instance breaking an `extends Error` bound is EN0419; error types meet it",
        || {
            let r = main_lib(
                "public class H<E extends Error> { public v: i64 = 0; }
public enum Oops { Bad }
public function f(h: &H<string>): void { }
public function g(a: &H<Oops>, b: &H<Failure>): Result<i64, Oops> { return Ok(1); }
public function k<E extends Error>(a: &H<E>): Result<i64, E> { return Ok(1); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0419 3:19 `string` does not satisfy `Error` [`H` requires `E extends Error`]"]
            );
        },
    );
    h.case(
        "generic/plan d.9: the bounds written on type parameters and in `where` clauses are checked too",
        || {
            let r = main_lib(
                "public class Animal { public age: i64 = 0; }
public class Pen<T extends Animal> { public v: i64 = 0; }
public function f<T extends Pen<string>>(x: &T): void { }
public interface Holds<T extends Copy> { get(): i64; }
public function h<U extends Holds<string>>(x: &U): void { }
public class Bag<T> { public m(x: &T): void where T extends Pen<bool> { } }
public function ok<T extends Pen<Animal>>(x: &T): void { }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0419 3:19 `string` does not satisfy `Animal` [`Pen` requires `T extends Animal`]",
                    "EN0419 5:19 `string` does not satisfy `Copy` [`Holds` requires `T extends Copy`]",
                    "EN0419 6:51 `bool` does not satisfy `Animal` [`Pen` requires `T extends Animal`]",
                ]
            );
        },
    );
    h.case(
        "generic/plan e: EN0419 in `extends` and `implements` is at the written type",
        || {
            let r = main_lib(
                "public class Animal { public age: i64 = 0; }
public class Pen<T extends Animal> { public v: i64 = 0; }
public class Bad extends Pen<string> { }
public interface Holder<T extends Copy> { get(): i64; }
public class H implements Holder<string> { public get(): i64 { return 1; } }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0419 3:26 `string` does not satisfy `Animal` [`Pen` requires `T extends Animal`]",
                    "EN0419 5:27 `string` does not satisfy `Copy` [`Holder` requires `T extends Copy`]",
                ]
            );
        },
    );
    h.case(
        "generic/S:730: under C19's hint the hinted error wins, as at an annotation",
        || {
            let r = main_lib(
                "public function h(): Result<string> { return Ok(5); }
public function k(): void { const r: Result<string> = Ok(5); }
public function id<T>(x: T): T { return x; }
public function w(): Result<i64> { return id(5); }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0401 1:49 mismatched types: expected `string`, found `int` [this is `int`]",
                    "EN0401 2:58 mismatched types: expected `string`, found `int` [this is `int`]",
                ]
            );
        },
    );
    h.case(
        "generic/S:560: a nullable reference bound to `T` is EN0703 (mutant M11)",
        || {
            let r = main_lib(
                "public class User { public name: string = \"\"; }
public function keep<T>(x: T): void { }
public function g(u: &User | null): void { keep(u); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0703 3:49 `T` can't stand for the reference `&User | null` [this makes `T` the reference `&User | null`]"]
            );
        },
    );
    h.case(
        "generic/S:600: a variable lacking an optional field at an implicit shape parameter is EN0433",
        || {
            let r = main_lib(
                "public type Book = { title: string, subtitle?: string };
public function show(b: &Book): void { }
public function g(): void {
  const p = { title: \"x\" };
  show(&p);
  show(&{ title: \"y\" });
  const q: { subtitle: string | null } = { subtitle: null };
  show(&q);
}
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0433]: missing `subtitle`
 --> main.en:5:8
  |
5 |   show(&p);
  |        ^^ `{ subtitle?: string | null, title: string }` needs every field it names, optional ones included
  |
help: add `subtitle: null`
  = explain: run `enrang explain EN0433`

error[EN0401]: `{ subtitle: string | null }` has no public field `title`
 --> main.en:8:8
  |
8 |   show(&q);
  |        ^^ this is `{ subtitle: string | null }`
  |
  = explain: run `enrang explain EN0401`

error: aborting due to 2 previous errors
"
            );
        },
    );
}
