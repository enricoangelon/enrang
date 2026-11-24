//! Construction (plan d.16's `construct.rs`, c.5; SPEC 4.3 S:581-587, S:591,
//! S:600-601; owner 4A): `new C(args)` through the nearest constructor of the
//! chain, a subclass with none reusing its base's (EN0449 for arguments with none,
//! EN0445 for an abstract class, EN0221 for no class); `new C()` with no
//! constructor as all defaults (EN0433 `` `new Team()` leaves `owner` unset ``);
//! the named form, `new C { ... }` or an object literal at a class, listing base and
//! own fields (EN0447 with a constructor, EN0433 missing, EN0434 unknown, EN0308
//! invisible); case literals with defaults for the fields left out; object
//! literals at object types (EN0434 `` `greet` doesn't use the field `age` ``, an
//! optional field left out is `null`) and anonymous ones; a value lacking an
//! optional field (EN0433 `` missing `subtitle` ``); `super(...)` (EN0449, T:987).

use enrang_hir::{Callee, ExprKind, FieldIdx, StmtKind};
use enrang_testkit::Harness;

use crate::paths::{body, diags, main_lib, ty};
use crate::support::Run;

pub fn register(h: &mut Harness) {
    news(h);
    named(h);
    chains(h);
    cases(h);
    objects(h);
    review(h);
}

/// The initialisers of `path`'s body's `const`/`let` statements, in order.
fn inits<'r>(r: &'r Run, path: &str) -> Vec<&'r enrang_hir::Expr> {
    body(r, path)
        .root
        .stmts
        .iter()
        .filter_map(|s| match &s.kind {
            StmtKind::Let { init: Some(e), .. } => Some(e),
            _ => None,
        })
        .collect()
}

fn news(h: &mut Harness) {
    h.case(
        "construct/`new C(args)` runs the constructor: `New`, the class's type",
        || {
            let r = main_lib(
                "public class User { public constructor(public name: string, public age: i64) {} }
public function f(): void { const a = new User(\"Ada\", 36); }
",
            );
            r.clean();
            let e = inits(&r, "main::f")[0];
            let ExprKind::New { ctor, values, .. } = &e.kind else {
                panic!("{e:?}")
            };
            assert_eq!(r.tcx.def(*ctor).path.to_string(), "main::User::#ctor");
            assert_eq!(values.len(), 2);
            assert_eq!(ty(&r, e.ty), "User");
        },
    );
    h.case(
        "construct/a generic class's arguments come from the constructor's and the expected type",
        || {
            let r = main_lib(
                "public class Cell<T> { public constructor(public v: T) {} }
public function f(): void { const a = new Cell(5); const b: Cell<i64> = new Cell(5); const c = new Cell<u8>(1); }
",
            );
            r.clean();
            let types: Vec<String> = inits(&r, "main::f")
                .iter()
                .map(|e| ty(&r, e.ty))
                .collect();
            assert_eq!(types, ["Cell<int>", "Cell<i64>", "Cell<u8>"]);
        },
    );
    h.case(
        "construct/S:582: `new Counter()` means all defaults; `new Team()` is EN0433",
        || {
            let r = main_lib(
                "public class User { public name: string; }
public class Team { public owner: User; public size: i64; }
public class Counter { public n: i64; public label: string; public on: bool; public xs: i64[]; public p: User | null; public q: *u8; }
public function f(): void { const k = new Counter(); const t = new Team(); }
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0433]: `new Team()` leaves `owner` unset
 --> main.en:4:64
  |
4 | public function f(): void { const k = new Counter(); const t = new Team(); }
  |                                                                ^^^^^^^^^^ this field has no default
  |
help: use `new Team { owner: ... }`
  = explain: run `enrang explain EN0433`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "construct/all defaults is a `NewNamed` whose every field comes from its default",
        || {
            let r = main_lib(
                "public class Counter { public n: i64; public label: string = \"x\"; }
public function f(): void { const k = new Counter(); }
",
            );
            r.clean();
            let ExprKind::NewNamed {
                fields,
                default_from,
                ..
            } = &inits(&r, "main::f")[0].kind
            else {
                panic!()
            };
            assert!(fields.is_empty());
            assert_eq!(default_from, &[FieldIdx(0), FieldIdx(1)]);
        },
    );
    h.case(
        "construct/EN0449: arguments to `new` of a chain with no constructor",
        || {
            let r = main_lib(
                "public class User { public name: string = \"\"; }
public function f(): void { const u = new User(\"x\", 1); }
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0449]: `User` has no constructor, so it takes no arguments
 --> main.en:2:48
  |
2 | public function f(): void { const u = new User(\"x\", 1); }
  |                                                ^^^^^^ no constructor takes these
  |
  = explain: run `enrang explain EN0449`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "construct/EN0221: `new` of an enum, an interface, a type parameter or a primitive",
        || {
            let r = main_lib(
                "public enum Color { Red, Green }
public interface Speaker { speak(): string; }
public type Num = i64;
public function g<T>(): void { const x = new T(); }
public function f(): void {
  const a = new Color();
  const b = new Speaker();
  const d = new i64();
  const e = new Num { };
}
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0221 4:46 `new` needs a class, and `T` is a type parameter [not a class]",
                    "EN0221 6:17 `new` needs a class, and `Color` is an enum [not a class]",
                    "EN0221 7:17 `new` needs a class, and `Speaker` is an interface [not a class]",
                    "EN0221 8:17 `new` needs a class, not `i64` [not a class]",
                    "EN0221 9:17 `new` needs a class, not `i64` [not a class]",
                ]
            );
        },
    );
    h.case(
        "construct/EN0445: `new` of an abstract class, by arguments or by name (S:586)",
        || {
            let r = main_lib(
                "public abstract class Shape { public abstract area(): f64; }
public function f(): void { const c = new Shape(); const e = new Shape {}; }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0445 2:43 `Shape` is abstract, so it can't be created [an abstract class]",
                    "EN0445 2:66 `Shape` is abstract, so it can't be created [an abstract class]",
                ]
            );
        },
    );
    h.case(
        "construct/the arguments of a rejected `new` are still typed",
        || {
            let r = main_lib(
                "public enum Color { Red }
public function f(): void { const a = new Color(missing); }
",
            );
            assert_eq!(r.codes(), ["EN0221", "EN0301"], "{}", r.rendered());
        },
    );
}

fn named(h: &mut Harness) {
    h.case(
        "construct/S:581: the named form, its shorthand, an object literal at the class, nesting",
        || {
            let r = main_lib(
                "public class User { public name: string; public age: i64 = 0; }
public class Team { public owner: User; }
public function f(name: string): void {
  const a = new User { name: \"Ada\", age: 36 };
  const b = new User { name };
  const c: User = { name: \"Ada\", age: 36 };
  const t = new Team { owner: new User { name: \"Ada\" } };
  const u: Team = { owner: { name: \"Bo\" } };
}
",
            );
            r.clean();
            let all = inits(&r, "main::f");
            let ExprKind::NewNamed {
                fields,
                default_from,
                ..
            } = &all[1].kind
            else {
                panic!()
            };
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].0, FieldIdx(0));
            assert_eq!(default_from, &[FieldIdx(1)]);
            for e in all {
                assert!(matches!(e.kind, ExprKind::NewNamed { .. }), "{e:?}");
            }
        },
    );
    h.case(
        "construct/EN0447: naming the fields of a class with a constructor",
        || {
            let r = main_lib(
                "public class User { public constructor(public name: string, public age: i64) {} }
public function f(): void {
  const b = new User { name: \"Ada\", age: 36 };
  const c: User = { name: \"Ada\", age: 36 };
}
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0447]: `User` has a constructor: write `new User(...)`
 --> main.en:3:13
  |
3 |   const b = new User { name: \"Ada\", age: 36 };
  |             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ naming the fields skips the constructor
  |
  = explain: run `enrang explain EN0447`

error[EN0447]: `User` has a constructor: write `new User(...)`
 --> main.en:4:19
  |
4 |   const c: User = { name: \"Ada\", age: 36 };
  |                   ^^^^^^^^^^^^^^^^^^^^^^^^ naming the fields skips the constructor
  |
  = explain: run `enrang explain EN0447`

error: aborting due to 2 previous errors
"
            );
        },
    );
    h.case(
        "construct/EN0433 missing fields, EN0434 an unknown one, in one literal",
        || {
            let r = main_lib(
                "public class User { public name: string; public age: i64; }
public class Team { public owner: User; public lead: User; public size: i64; }
public function f(): void {
  const a = new Team { size: 3 };
  const b = new User { name: \"x\", nope: 1 };
}
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0433 4:13 missing fields `owner` and `lead` [every field without a default must be set]",
                    "EN0434 5:35 `User` has no field `nope` [not a field of `User`]",
                ]
            );
        },
    );
    h.case(
        "construct/EN0308: every named field must be visible where the literal is written",
        || {
            let r = main_lib(
                "public class User { public name: string; private secret: i64 = 0; protected tag: i64 = 0; }
public function f(): void { const u = new User { name: \"x\", secret: 3, tag: 1 }; }
",
            );
            assert_eq!(
                r.codes(),
                ["EN0308", "EN0308"],
                "{}",
                r.rendered()
            );
            assert_eq!(
                diags(&r)[0],
                "EN0308 2:61 `secret` is private to `User` [only the body of `User` can use it]"
            );
        },
    );
}

fn chains(h: &mut Harness) {
    h.case(
        "construct/S:587: a chain with no constructor lists base and own fields together",
        || {
            let r = main_lib(
                "public class Base { public color: string = \"x\"; }
public class Square extends Base { public side: i64; }
public function f(): void {
  const s = new Square { color: \"red\", side: 2 };
  const t = new Square(1);
}
",
            );
            assert_eq!(
                diags(&r),
                ["EN0449 5:24 `Square` has no constructor, so it takes no arguments [no constructor takes these]"]
            );
        },
    );
    h.case(
        "construct/S:587: a subclass with no constructor reuses its base's; naming fields is EN0447",
        || {
            let classes = "public class Animal { public constructor(public name: string) {} }
public class Dog extends Animal { public tricks: i64 = 0; }
";
            let r = main_lib(&format!(
                "{classes}public function f(): void {{ const e = new Dog {{ name: \"Rex\" }}; }}\n"
            ));
            assert_eq!(
                diags(&r),
                ["EN0447 3:39 `Dog` has a constructor: write `new Dog(...)` [naming the fields skips the constructor]"]
            );
            let r = main_lib(&format!(
                "{classes}public function f(): void {{ const d = new Dog(\"Rex\"); }}\n"
            ));
            r.clean();
            let ExprKind::New { ctor, .. } = &inits(&r, "main::f")[0].kind else {
                panic!()
            };
            assert_eq!(r.tcx.def(*ctor).path.to_string(), "main::Animal::#ctor");
            assert_eq!(ty(&r, inits(&r, "main::f")[0].ty), "Dog");
        },
    );
    h.case(
        "construct/T:987 `C4-ctorless-base`: `super()` compiles, `super(1)` is EN0449",
        || {
            let shape = "public class Person { public constructor(public name: string) {} }
public class Shape { protected color: string = \"red\"; public owner: Person; public describe(): string { return `${this.color} shape of ${this.owner.name}`; } }
";
            let r = main_lib(&format!(
                "{shape}public class Circle extends Shape {{ public constructor(public r: i64, o: Person) {{ super(); this.owner = o; }} }}
public function main(): void {{ console.log(new Circle(2, new Person(\"Ada\")).describe()); }}
"
            ));
            r.clean();
            let r = main_lib(&format!(
                "{shape}public class Circle extends Shape {{ public constructor(public r: i64, o: Person) {{ super(1); this.owner = o; }} }}
"
            ));
            assert_eq!(
                r.rendered(),
                "error[EN0449]: `Shape` has no constructor, so it takes no arguments
 --> main.en:3:90
  |
3 | public class Circle extends Shape { public constructor(public r: i64, o: Person) { super(1); this.owner = o; } }
  |                                                                                          ^ no constructor takes these
  |
  = explain: run `enrang explain EN0449`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "construct/`super(args)` runs the nearest constructor above, ranked as any call",
        || {
            let r = main_lib(
                "public class A { public constructor(public n: i64) {} public constructor(s: &string) { this.n = 0; } }
public class B extends A {}
public class C extends B { public constructor() { super(\"x\"); } }
",
            );
            r.clean();
            let b = body(&r, "main::C::#ctor");
            let call = b
                .root
                .stmts
                .iter()
                .find_map(|s| match &s.kind {
                    StmtKind::Expr(e) => Some(e),
                    _ => None,
                })
                .expect("`super(...)`");
            let ExprKind::Call {
                callee: Callee::SuperCtor { ctor: Some(ctor), .. },
                ..
            } = &call.kind
            else {
                panic!("{call:?}")
            };
            assert_eq!(r.tcx.def(*ctor).path.to_string(), "main::A::#ctor(&string)");
        },
    );
}

fn cases(h: &mut Harness) {
    h.case(
        "construct/S:591: a case literal fills the fields it leaves out with their defaults",
        || {
            let r = main_lib(
                "public enum Shape { Circle { radius: f64, label: string }, Square { side: f64 }, Empty }
public function f(): void {
  const a = Shape.Circle { radius: 2.5 };
  const d: Result<i64> = Ok { value: 5 };
}
",
            );
            r.clean();
            let ExprKind::VariantLit { fields, .. } = &inits(&r, "main::f")[0].kind else {
                panic!()
            };
            assert_eq!(fields.len(), 2);
            assert_eq!(ty(&r, fields[1].ty), "string");
        },
    );
    h.case(
        "construct/a case literal: an unknown field is EN0434, a case with no default EN0433",
        || {
            let r = main_lib(
                "public class User { public name: string; }
public enum Msg { Hello { to: User, n: i64 } }
public enum Shape { Square { side: f64 } }
public function f(): void {
  const b = Shape.Square { side: 1.0, nope: 2 };
  const c = Msg.Hello { n: 1 };
  const t = Shape.Triangle { x: 1 };
}
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0434 5:39 `Shape.Square` has no field `nope` [not a field of `Shape.Square`]",
                    "EN0433 6:13 missing field `to` [every field without a default must be set]",
                    "EN0303 7:19 `Shape` has no case `Triangle` [no such case]",
                ]
            );
        },
    );
}

fn objects(h: &mut Harness) {
    h.case(
        "construct/S:601: a literal's field the parameter's object type lacks is EN0434",
        || {
            let r = main_lib(
                "public function greet(x: &{ name: string }): void { console.log(`hi ${x.name}`); }
public function f(): void { greet(&{ name: \"Bo\", age: 1 }); const p = { name: \"Ada\", age: 36 }; greet(&p); }
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0434]: `greet` doesn't use the field `age`, so it would be thrown away
 --> main.en:2:50
  |
2 | public function f(): void { greet(&{ name: \"Bo\", age: 1 }); const p = { name: \"Ada\", age: 36 }; greet(&p); }
  |                                                  ^^^ not a field of `{ name: string }`
  |
  = explain: run `enrang explain EN0434`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "construct/S:600: an anonymous object, and an optional field left out of a literal is `null`",
        || {
            let r = main_lib(
                "public type Book = { title: string, subtitle?: string };
public function f(): void { const p = { name: \"Ada\", age: 36 }; const b: Book = { title: \"x\" }; }
",
            );
            r.clean();
            let all = inits(&r, "main::f");
            assert_eq!(ty(&r, all[0].ty), "{ age: int, name: string }");
            let ExprKind::ObjectLit { fields, .. } = &all[1].kind else {
                panic!()
            };
            assert!(fields.iter().any(|f| matches!(f.kind, ExprKind::NullLit)));
        },
    );
    h.case(
        "construct/S:600: a variable lacking an optional field is EN0433 `missing `subtitle``",
        || {
            let r = main_lib(
                "public type Book = { title: string, subtitle?: string };
public function f(): void { const v = { title: \"y\" }; const c: Book = v; }
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0433]: missing `subtitle`
 --> main.en:2:71
  |
2 | public function f(): void { const v = { title: \"y\" }; const c: Book = v; }
  |                                                                       ^ `{ subtitle?: string | null, title: string }` needs every field it names, optional ones included
  |
help: add `subtitle: null`
  = explain: run `enrang explain EN0433`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "construct/a literal at an object type: a missing field is EN0433, a repeated one typed",
        || {
            let r = main_lib(
                "public type P = { x: i64, y: i64 };
public function f(): void { const a: P = { x: 1 }; const b: P = { x: 1, y: 2, z: 3 }; }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0433 2:42 missing field `y` [every field without a default must be set]",
                    "EN0434 2:79 `{ x: i64, y: i64 }` has no field `z` [not a field of `{ x: i64, y: i64 }`]",
                ]
            );
        },
    );
}

/// Stage 6's review fixes: override defaults, constructor visibility, `void`
/// defaults, abstract classes reported alone, and the cases the mutation gate
/// found unpinned.
fn review(h: &mut Harness) {
    h.case(
        "construct/S:585: a field override's new default serves the named form, `new C()`, a literal and a sub-subclass",
        || {
            let r = main_lib(
                "public class Person { public name: string = \"\"; }
public class Animal { public owner: Person; }
public class Dog extends Animal { public override owner: Person = new Person { name: \"nobody\" }; }
public class Puppy extends Dog { }
public function g(): void { const d = new Dog {}; const e = new Dog(); const f: Dog = {}; const p = new Puppy {}; const q = new Puppy(); }
",
            );
            r.clean();
            let all = inits(&r, "main::g");
            let ExprKind::NewNamed { default_from, .. } = &all[1].kind else {
                panic!("{:?}", all[1])
            };
            assert_eq!(default_from, &[FieldIdx(0)]);
        },
    );
    h.case(
        "construct/the base of an override keeps no default of its own",
        || {
            let r = main_lib(
                "public class Person { public name: string = \"\"; }
public class Animal { public owner: Person; }
public class Dog extends Animal { public override owner: Person = new Person { name: \"nobody\" }; }
public function h(): void { const a = new Animal {}; const d = new Dog {}; }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0433 4:39 missing field `owner` [every field without a default must be set]"]
            );
        },
    );
    h.case(
        "construct/S:321, S:580: a `private` constructor outside its class is EN0308",
        || {
            let r = main_lib(
                "public class Single {
  private constructor() {}
  public static make(): Single { return new Single(); }
}
public function g(): void {
  const s = new Single();
}
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0308]: `constructor` is private to `Single`
 --> main.en:6:17
  |
2 |   private constructor() {}
  |           ----------- `constructor` is declared here
...
6 |   const s = new Single();
  |                 ^^^^^^ only the body of `Single` can use it
  |
  = explain: run `enrang explain EN0308`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "construct/a `protected` constructor serves its subclasses' `super(...)` only; a `private` one no `super(...)`",
        || {
            let r = main_lib(
                "public class Base { protected constructor(n: i64) {} }
public class D extends Base { public constructor() { super(1); } public static make(): Base { return new Base(2); } }
public class Hidden { private constructor(n: i64) {} }
public class E extends Hidden { public constructor() { super(1); } }
public function g(): void { const s = new Base(1); const d = new D(); }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0308 4:56 `constructor` is private to `Hidden` [only the body of `Hidden` can use it]",
                    "EN0308 5:43 `constructor` is protected in `Base` [only `Base` and its subclasses can use it]",
                ]
            );
        },
    );
    h.case(
        "construct/one table of defaults: a `void` field has one, for EN0448 and EN0433 alike",
        || {
            let r = main_lib(
                "public class C { private v: void; }
public class Holder<T> { public v: T; }
public function g(): void { const c = new C {}; const d = new C(); const h = new Holder<void> {}; const k = new Holder<C> {}; }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0433 3:109 missing field `v` [every field without a default must be set]"]
            );
        },
    );
    h.case(
        "construct/S:586: `new` of an abstract class is EN0445 alone, its values typed",
        || {
            let r = main_lib(
                "public class Person { public name: string = \"\"; }
public abstract class Shape { public owner: Person; }
public function g(): void { const s = new Shape(); const t = new Shape(1); const u = new Shape { }; const v = new Shape(nope); }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0445 3:43 `Shape` is abstract, so it can't be created [an abstract class]",
                    "EN0445 3:66 `Shape` is abstract, so it can't be created [an abstract class]",
                    "EN0445 3:90 `Shape` is abstract, so it can't be created [an abstract class]",
                    "EN0445 3:115 `Shape` is abstract, so it can't be created [an abstract class]",
                    "EN0301 3:121 cannot find `nope` in this scope [not found]",
                ]
            );
        },
    );
    h.case(
        "construct/an object literal at an abstract class type is EN0445 (mutant M19)",
        || {
            let r = main_lib(
                "public abstract class Shape { public color: string = \"\"; }
public function g(): void { const s: Shape = { color: \"red\" }; }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0445 2:46 `Shape` is abstract, so it can't be created [an abstract class]"]
            );
        },
    );
    h.case(
        "construct/a named form sets the subclass's own field, not a private base field of its name (mutant M21)",
        || {
            let r = main_lib(
                "public class A { private x: i64 = 0; }
public class B extends A { public x: string = \"\"; }
public function g(): void { const b = new B { x: \"s\" }; }
",
            );
            r.clean();
            let ExprKind::NewNamed {
                fields,
                default_from,
                ..
            } = &inits(&r, "main::g")[0].kind
            else {
                panic!()
            };
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].0, FieldIdx(1));
            assert_eq!(ty(&r, fields[0].1.ty), "string");
            assert_eq!(default_from, &[FieldIdx(0)]);
        },
    );
    h.case(
        "construct/S:600: a variable lacking a required field is EN0401, not EN0433 (mutant M24)",
        || {
            let r = main_lib(
                "public function g(): void {
  const p = { a: 1 };
  const q: { a: int, b: int } = p;
}
",
            );
            assert_eq!(
                diags(&r),
                ["EN0401 3:33 mismatched types: expected `{ a: int, b: int }`, found `{ a: int }` [this is `{ a: int }`]"]
            );
        },
    );
}
