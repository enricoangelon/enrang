//! Whole programs as a user writes them, each accepted or rejected with exactly its
//! codes and no cascade, from stage 5A's end-to-end review (owner 5A, plan g.1):
//! the members the compiler synthesises (`clone` of any Clone type, S:639, and
//! `equals` of `implements Eq` with no body, S:640, each a glue form, D12); a member
//! that two bounds of one type parameter share, which is one member (S:764); one
//! error at a class whose `extends` names nothing (EN0302) or whose `implements`
//! fails (EN0416), with its uses silent; `??` reading through a `&T | null` of a
//! Copy `T` (C08, S:750); EN1006 for a by-value interface value wherever it is
//! produced (S:631); a failed import reported once; and the wording of EN0421 for
//! an enum, of "did you mean" ties, of EN0451's candidates and of EN0303's head.

use enrang_hir::{self as hir, Adjust, Callee, ExprKind, FormKind, StmtKind, TyKind};
use enrang_sema::LibSource;
use enrang_testkit::Harness;

use crate::paths::{body, diags, init, statements};
use crate::support::{Run, run_with};

/// Programs and the codes each reports, in order, on both widths.
const PROGRAMS: &[(&str, &str, &[&str])] = &[
    (
        "clone/a class with no written `clone` has one synthesised (G07's help)",
        "function archive(u: User): void { console.log(u.name); }

const u = new User(\"Ada\");
archive(u.clone());
console.log(u.name);

private class User { public constructor(public name: string) {} }
",
        &[],
    ),
    (
        "clone/an anonymous object, a tuple, a fixed array, an enum and a scalar",
        "const p = { name: \"Ada\", age: 36 };
const q = p.clone();
const t: [i64, string] = [1, \"a\"];
const t2 = t.clone();
const f: i64[3] = [1, 2, 3];
const g = f.clone();
const s = Shape.Circle { radius: 1.0 };
const s2 = s.clone();
const x: i64 = 5;
const x2 = x.clone();
const y = 7;
const y2 = y.clone();
console.log(q, t2, g, s2, x2 + 1, y2 + 1);

private enum Shape { Circle { radius: f64 }, Empty }
",
        &[],
    ),
    (
        "clone/`Result`, a Copy class with a raw pointer, a recursive class (T:744)",
        "const n = new Node { v: 1, next: null };
const n2 = n.clone();
const r = new Raw { p: 0 as *u8 };
const r2 = r.clone();
const w: Result<i64> = Ok(1);
const w2 = w.clone();
console.log(n2.v, r2.p, w2);

private class Node { public v: i64; public next: Box<Node> | null; }
private final class Raw implements Copy { public p: *u8; }
",
        &[],
    ),
    (
        "clone/through a reference, a narrowed nullable, `?.` and a Copy bound",
        "const u = new User { name: \"Ada\" };
const m: User | null = u.clone();
if (m != null) {
  const c: User = m.clone();
  console.log(c.name);
}
const o: User | null = m?.clone();
console.log(copyOf(&u).name, twice(3), o == null);

private class User { public name: string; }
private function copyOf(u: &User): User { return u.clone(); }
private function twice<T extends Copy>(x: T): T { return x.clone(); }
",
        &[],
    ),
    (
        "clone/a class with a destructor or a raw pointer field has none synthesised",
        "const h = new Handle { fd: 3 };
const h2 = h.clone();
const p = new Ptr { at: 0 as *u8 };
const p2 = p.clone();

private class Handle {
  public fd: i64;
  public destructor() { console.log(this.fd); }
}
private class Ptr { public at: *u8; }
",
        &["EN0303", "EN0303"],
    ),
    (
        "equals/`implements Eq` with no body synthesises `equals` (S:640)",
        "const a = new P { x: 1, y: 2 };
const b = new P { x: 1, y: 2 };
console.log(a == b, a.equals(&b), a != b);

private class P implements Eq { public x: i64; public y: i64; }
",
        &[],
    ),
    (
        "equals/a class that does not write `implements Eq` has no `equals`",
        "const a = new P { x: 1 };
console.log(a.equals(&a));

private class P { public x: i64; }
",
        &["EN0303"],
    ),
    (
        "bounds/`T extends Animal & Speaker` with `speak()` in both (S:764)",
        "const rex = new Dog(\"Rex\");
speakTwice(&rex);

private interface Speaker {
  speak(): string;
}

private class Animal {
  public constructor(public name: string) {}
  public speak(): string { return `${this.name} makes a sound`; }
}

private class Dog extends Animal implements Speaker {
  public override speak(): string { return `${this.name} barks`; }
}

private function speakTwice<T extends Animal & Speaker>(x: &T): void {
  console.log(x.speak(), x.name);
}
",
        &[],
    ),
    (
        "bounds/the interface bound written first, the class bound second",
        "const rex = new Animal(\"Rex\");
speakTwice(&rex);

private interface Speaker {
  speak(): string;
}

private class Animal implements Speaker {
  public constructor(public name: string) {}
  public speak(): string { return `${this.name} makes a sound`; }
}

private function speakTwice<T extends Speaker & Animal>(x: &T): void {
  console.log(x.speak(), x.name);
}
",
        &[],
    ),
    (
        "bounds/two interface bounds that share a member",
        "const c = new Circle(1.0);
console.log(describe(&c));

private interface Shape { area(): f64; name(): readonly &string; }
private interface Named { name(): readonly &string; }

private class Circle implements Shape, Named {
  public constructor(public r: f64) {}
  public area(): f64 { return 3.0 * this.r * this.r; }
  public name(): &string { return \"circle\"; }
}

private function describe<T extends Shape & Named>(s: &T): string {
  return `${s.name()} with area ${s.area()}`;
}
",
        &[],
    ),
    (
        "bounds/a `where` clause that restates its class's bound",
        "const s = new Sorted<i64>(3);
console.log(s.isAbove(&2));

private class Sorted<T extends Ord> {
  public constructor(public v: T) {}
  public isAbove(o: &T): bool where T extends Ord { return this.v.compare(o) > 0; }
}
",
        &[],
    ),
    (
        "bounds/members of one name and two signatures still tie (EN0451)",
        "private interface A { pick(b: i64): void; }
private interface B { pick(b: i64): i64; }
private function f<T extends A & B>(x: &T): void { x.pick(1); }
",
        &["EN0451"],
    ),
    (
        "cascade/an `extends` that names nothing is one EN0302",
        "const rex = new Dog(\"Rex\");
introduce(&rex);
console.log(rex.name, rex.speak(), rex.walk());
const pup = new Puppy(\"Bo\");
console.log(pup.name);
introduce(&pup);

private class Animal {
  public constructor(public name: string) {}
  public speak(): string { return \"...\"; }
}

private class Dog extends Animl {
  public override speak(): string { return `${this.name} barks`; }
}

private class Puppy extends Dog {
  public override speak(): string { return `${this.name} yips`; }
}

private function introduce(a: &Animal): void { console.log(a.speak()); }
",
        &["EN0302"],
    ),
    (
        "cascade/an unknown base silences what it may give, never the rest",
        "const rex = new Dog();
const d: Dog = &rex;
const n: i64 = rex;
console.log(rex.walk());

private class Dog extends Animl {
  public override name: string = \"x\";
  public walk(): string { return this.name; }
}
private class Quiet extends Animl implements Speaker {
  public constructor() { super(1); }
  public hear(): string { return super.speak(); }
}
private interface Speaker { speak(): string; }
",
        &["EN0401", "EN0401", "EN0302", "EN0302"],
    ),
    (
        "cascade/a failed `implements` is one EN0416, its uses silent",
        "const loud = new Loud(\"hey\");
const quiet = new Quiet();
speakTo(&loud);
speakTo(&quiet);
consume(new Quiet());
const all: Box<Speaker>[] = [new Box(new Loud(\"a\")), new Box(new Quiet())];
for (const s of &all) { console.log(s.speak()); }
const pick: &Speaker = loud.volume() > 3 ? &loud : &quiet;
console.log(pick.speak(), first(&quiet));

private interface Speaker {
  speak(): string;
}

private class Loud implements Speaker {
  public constructor(private word: string) {}
  public speak(): string { return this.word.toUpperCase(); }
  public volume(): i64 { return 10; }
}

private class Quiet implements Speaker {
  private speak(): string { return \"...\"; }
}

private function speakTo(s: &Speaker): void { console.log(s.speak()); }
private function consume(s: Speaker): void { console.log(s.speak()); }
private function first<T extends Speaker>(s: &T): string { return \"x\"; }
",
        &["EN0416"],
    ),
    (
        "cascade/a class that never writes `implements` still fails at its use",
        "speakTo(&new Mute());

private interface Speaker {
  speak(): string;
}

private class Mute {}

private function speakTo(s: &Speaker): void { console.log(s.speak()); }
",
        &["EN0401"],
    ),
    (
        "coalesce/`??` reads through a `&T | null` of a Copy `T` (C08, S:750)",
        "const ys: i64[] = [1, 2];
const f: i64 = ys.first() ?? 0;
const g = ys.find(y => y > 1) ?? 0;
const zs = [1.5, 2.5];
const h = zs.first() ?? 0.0;
let maybeC: Counter | null = new Counter();
console.log(f + 1, g + 1, h * 2.0, maybeC?.n ?? 0);

private class Counter {
  public n: i64 = 0;
}
",
        &[],
    ),
    (
        "coalesce/a `&T | null` of a non-Copy `T` takes a `&T` on the right",
        "const cs: Counter[] = [new Counter()];
const spare = new Counter();
const c = cs.first() ?? &spare;
const d = cs.first() ?? new Counter();
console.log(c.n, d);

private class Counter {
  public n: i64 = 0;
}
",
        &["EN0401"],
    ),
    (
        "iface/a by-value interface value is EN1006 as a receiver and when printed (S:631)",
        "const b: Box<Speaker> = new Box(new Dog());
b.unbox().speak();
console.log(b.unbox());
console.log(`${b.unbox()}`);
console.log(b.speak());

private interface Speaker { speak(): string; }
private class Dog { public speak(): string { return \"woof\"; } }
",
        &["EN1006", "EN1006", "EN1006"],
    ),
    (
        "iface/a place of interface type, reported at its declaration, is a quiet receiver",
        "const b: Box<Speaker> = new Box(new Dog());
for (const s of [b.unbox()]) { console.log(s.speak(), s); }

private interface Speaker { speak(): string; }
private class Dog { public speak(): string { return \"woof\"; } }
",
        &["EN1006"],
    ),
];

/// The run of `source` as `main.en` with the embedded library on `target`.
fn checked(source: &str, target: &str) -> Run {
    run_with(&[("main.en", source)], LibSource::Embedded, target)
}

/// The run on the host's width.
fn main_lib(source: &str) -> Run {
    checked(source, "x86_64-linux")
}

pub fn register(h: &mut Harness) {
    for &(what, source, codes) in PROGRAMS {
        h.case(format!("programs/{what}"), move || {
            for target in ["x86_64-linux", "i386-linux"] {
                let r = checked(source, target);
                assert_eq!(r.codes(), codes, "{what} on {target}:\n{}", r.rendered());
                if codes.is_empty() {
                    assert!(r.program.is_some(), "{what} on {target}");
                }
            }
        });
    }
    glue(h);
    shapes(h);
    wording(h);
    imports(h);
}

/// The callee of a call expression.
fn callee(e: &hir::Expr) -> &Callee {
    match &e.kind {
        ExprKind::Call { callee, .. } => callee,
        other => panic!("not a call: {other:?}"),
    }
}

/// What a synthesised member's call is (D12).
fn glue(h: &mut Harness) {
    h.case(
        "programs/a synthesised `clone` is the glue form, typed as its receiver",
        || {
            let r = main_lib(
                "const u = new User { name: \"Ada\" };
const v = u.clone();
const t: [i64, bool] = [1, true];
const w = t.clone();

private class User { public name: string; }
",
            );
            r.clean();
            let b = statements(&r);
            for (n, shown) in [(1, "User"), (3, "[i64, bool]")] {
                let e = init(b, n);
                assert_eq!(callee(e), &Callee::Form(FormKind::Clone));
                assert_eq!(r.tcx.ty_string(e.ty), shown);
                let ExprKind::Call { receiver, .. } = &e.kind else {
                    unreachable!()
                };
                let receiver = receiver.as_ref().expect("a receiver");
                assert_eq!(receiver.adjust, [Adjust::AutoBorrow]);
            }
        },
    );
    h.case(
        "programs/a synthesised `equals` is the glue form; a written `clone` wins",
        || {
            let r = main_lib(
                "const a = new P { x: 1 };
const e = a.equals(&a);
const k = new K { x: 1 };
const k2 = k.clone();

private class P implements Eq { public x: i64; }
private class K {
  public x: i64;
  public clone(): K { return new K { x: this.x }; }
}
",
            );
            r.clean();
            let b = statements(&r);
            let e = init(b, 1);
            assert_eq!(callee(e), &Callee::Form(FormKind::Equals));
            assert_eq!(r.tcx.ty_string(e.ty), "bool");
            let written = init(b, 3);
            let Callee::Fn(f) = callee(written) else {
                panic!("{:?}", callee(written));
            };
            assert_eq!(r.tcx.def(f.def).path.to_string(), "main::K::clone");
        },
    );
    h.case(
        "programs/a member two bounds share calls the class bound's method",
        || {
            let r = main_lib(
                "private interface Speaker { speak(): string; }
private class Animal implements Speaker { public speak(): string { return \"...\"; } }
private function f<T extends Speaker & Animal>(x: &T): string { return x.speak(); }
",
            );
            r.clean();
            let b = body(&r, "main::f");
            let StmtKind::Return(Some(e)) = &b.root.stmts[0].kind else {
                panic!("{:?}", b.root.stmts[0].kind);
            };
            let Callee::BoundMember { found, .. } = callee(e) else {
                panic!("{:?}", callee(e));
            };
            assert_eq!(r.tcx.def(*found).path.to_string(), "main::Animal::speak");
        },
    );
}

/// The typed shape of `??` reading through (C08).
fn shapes(h: &mut Harness) {
    h.case(
        "programs/`ys.first() ?? 0` reads its left through: `ReadThroughNullable`, an `i64`",
        || {
            let r = main_lib("const ys: i64[] = [1, 2];\nconst f = ys.first() ?? 0;\n");
            r.clean();
            let e = init(statements(&r), 1);
            let ExprKind::Coalesce(a, _) = &e.kind else {
                panic!("{:?}", e.kind);
            };
            assert_eq!(a.adjust, [Adjust::ReadThroughNullable]);
            assert_eq!(r.tcx.ty_string(a.ty), "&i64 | null");
            assert!(
                matches!(r.tcx.kind(e.ty), TyKind::Int(_)),
                "{}",
                r.tcx.ty_string(e.ty)
            );
            assert_eq!(r.tcx.ty_string(e.ty), "i64");
        },
    );
    h.case(
        "programs/a `&string | null` keeps its reference: `names.first() ?? \"none\"`",
        || {
            let r = main_lib(
                "const names: string[] = [\"a\".toString()];\nconst n = names.first() ?? \"none\";\n",
            );
            r.clean();
            let e = init(statements(&r), 1);
            let ExprKind::Coalesce(a, _) = &e.kind else {
                panic!("{:?}", e.kind);
            };
            assert!(a.adjust.is_empty(), "{:?}", a.adjust);
            assert_eq!(r.tcx.ty_string(e.ty), "&string");
        },
    );
}

fn expect(r: &Run, want: &[&str]) {
    assert_eq!(diags(r), want, "{}", r.rendered());
}

/// Messages the review found worded wrong.
fn wording(h: &mut Harness) {
    h.case(
        "programs/EN0421 on an enum says to write `equals`, which an enum can (S:303)",
        || {
            let r = main_lib(
                "const s1 = Shape.Circle { r: 1.0 };
console.log(s1 == Shape.Empty);

private enum Shape { Circle { r: f64 }, Empty }
",
            );
            assert_eq!(r.codes(), ["EN0421"], "{}", r.rendered());
            assert_eq!(
                r.diags[0].helps[0].message,
                "add `public equals(other: &Shape): bool` to `Shape`'s methods, or `match` on its case"
            );
            let class = main_lib(
                "const a = new P { x: 1 };\nconsole.log(a == a);\n\nprivate class P { public x: i64; }\n",
            );
            assert_eq!(
                class.diags[0].helps[0].message,
                "declare `implements Eq` on `P`, or compare its fields"
            );
        },
    );
    h.case(
        "programs/did you mean: a local beats an item at the same distance",
        || {
            let r = main_lib(
                "private function f(): void {
  const todos = 1;
  console.log(todo);
}

private class Todo {}
",
            );
            expect(
                &r,
                &["EN0301 3:15 cannot find `todo` in this scope [not found]"],
            );
            assert_eq!(r.diags[0].helps[0].message, "did you mean `todos`?");
            assert_eq!(
                r.diags[0].secondary[0].text,
                "a local with a similar name is declared here"
            );
            let top = main_lib("let todos = 1;\nconsole.log(todo);\n\nprivate class Todo {}\n");
            assert_eq!(top.diags[0].helps[0].message, "did you mean `todos`?");
        },
    );
    h.case(
        "programs/EN0451's candidates show an interface's `Self` as the receiver's type",
        || {
            let r = main_lib(
                "private interface A { pick(o: &Self): void; }
private interface B { pick(o: &Self): i64; }
private function f<T extends A & B>(x: &T): void { x.pick(x); }
",
            );
            assert_eq!(r.codes(), ["EN0451"], "{}", r.rendered());
            let notes: Vec<&str> = r.diags[0].entries.iter().map(|e| e.text.as_str()).collect();
            assert_eq!(
                notes,
                [
                    "candidate: `pick(o: &T): void`",
                    "candidate: `pick(o: &T): i64`"
                ]
            );
        },
    );
    h.case(
        "programs/EN0303's head shows a literal's type by its default, not `_`",
        || {
            let r = main_lib("const p = { name: \"Ada\", age: 36 };\nconsole.log(p.nope);\n");
            assert_eq!(
                r.messages(),
                ["`{ age: int, name: string }` has no member `nope`"],
                "{}",
                r.rendered()
            );
        },
    );
    h.case(
        "programs/an article fits the name it comes before: `an `AgeError``",
        || {
            let r = main_lib(
                "private enum AgeError { Negative }
private enum OtherError { Bad }
private function age(): Result<i64, AgeError> { return Ok(1); }
private function f(): Result<i64, OtherError> { const a = age()?; return Ok(a); }
",
            );
            assert_eq!(r.codes(), ["EN0425"], "{}", r.rendered());
            assert_eq!(
                r.diags[0].primary.text,
                "this returns an `AgeError` error early"
            );
        },
    );
}

/// A failed import is reported once, at the import (plan d.1).
fn imports(h: &mut Harness) {
    let program = |main: &str| {
        run_with(
            &[
                ("main.en", main),
                (
                    "u.en",
                    "private function helper(x: i64): i64 {\n  return x;\n}\npublic function shown(): i64 {\n  return 1;\n}\n",
                ),
            ],
            LibSource::Embedded,
            "x86_64-linux",
        )
    };
    h.case(
        "programs/an import of a private item is one EN0311, its uses silent",
        move || {
            let r =
                program("import { helper } from \"./u\";\n\nconsole.log(helper(2), helper(3));\n");
            assert_eq!(r.codes(), ["EN0311"], "{}", r.rendered());
        },
    );
    h.case(
        "programs/an import of a name the module lacks is one EN0305",
        move || {
            let r = program("import { nope as n } from \"./u\";\n\nconsole.log(n(2));\n");
            assert_eq!(r.codes(), ["EN0305"], "{}", r.rendered());
        },
    );
    h.case(
        "programs/an import of a path that names nothing is one EN0305",
        move || {
            let r = program(
                "import { twice } from \"./nope\";\nimport * as gone from \"./gone\";\n\nconsole.log(twice(2), gone.f());\nconst t: twice = 1;\n",
            );
            assert_eq!(r.codes(), ["EN0305", "EN0305"], "{}", r.rendered());
        },
    );
    h.case(
        "programs/a failed import is silent in a constant, a type and a deferred name",
        move || {
            let r = program(
                "import { LIMIT } from \"./nope\";\nimport { Map } from \"./gone\";\n\nconst X: i64 = LIMIT * 2;\nconst m = new Map();\nconst k: Map = m;\nconsole.log(X, m);\n",
            );
            assert_eq!(r.codes(), ["EN0305", "EN0305"], "{}", r.rendered());
        },
    );
    h.case(
        "programs/an import of a re-export whose own import failed is silent",
        || {
            let r = run_with(
                &[
                    ("main.en", "import { x } from \"./u\";\n\nconsole.log(x);\n"),
                    ("u.en", "public import { x } from \"./nope\";\n"),
                ],
                LibSource::Embedded,
                "x86_64-linux",
            );
            assert_eq!(r.codes(), ["EN0305"], "{}", r.rendered());
        },
    );
    h.case(
        "programs/a name no import binds is still EN0301 beside a failed import",
        move || {
            let r = program("import { helper } from \"./u\";\n\nconsole.log(shown(), helpr(1));\n");
            assert_eq!(
                r.codes(),
                ["EN0311", "EN0301", "EN0301"],
                "{}",
                r.rendered()
            );
        },
    );
}
