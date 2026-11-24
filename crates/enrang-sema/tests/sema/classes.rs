//! Class rules (plan d.16 without construction; owner 4D): `final` (EN0442), field
//! and method overrides (EN0443, EN0444), abstract classes and methods (EN0446,
//! EN0457), `move` methods reached through inheritance or `super` (EN0458,
//! EN0459), methods compiled once per type (EN0460), `implements Copy` (EN0418),
//! classes that need a constructor (EN0448), a `destructor` in an interface
//! (EN0606), and the typing of field initialisers (`hir::FieldInits`); each with
//! SPEC 4.3's examples and TESTING 18's rows (`Q32-field-rules`, `S2-29-fmt`,
//! `D8-super`, `S2-03-into`, `C4-move-inherited`, `VI-04-copy`, `VI-05-override`,
//! `VI-06-tables`), the exact code, position, message and label of each report;
//! then SPEC's programs and M1's near-misses, which report none of 4D's codes
//! beyond what their cases expect.

use enrang_hir::{ConstValue, ExprKind, FieldIdx};
use enrang_testkit::{Harness, extract_cases};

use enrang_sema::LibSource;

use crate::paths::{diags, main_en, main_lib, ty};
use crate::support::{Run, run_with};

pub fn register(h: &mut Harness) {
    visibility(h);
    finals(h);
    field_overrides(h);
    method_overrides(h);
    abstracts(h);
    moves(h);
    once_per_type(h);
    implicit_overloads(h);
    copies(h);
    constructors(h);
    interfaces(h);
    field_inits(h);
    elsewhere(h);
    sweeps(h);
    review(h);
}

/// Asserts the diagnostics of `r`, each as `CODE line:col message [label]`.
fn expect(r: &Run, want: &[&str]) {
    assert_eq!(diags(r), want, "{}", r.rendered());
}

/// The single diagnostic of `r`.
fn only(r: &Run) -> &enrang_diag::Diagnostic {
    assert_eq!(r.diags.len(), 1, "{}", r.rendered());
    &r.diags[0]
}

/// The help messages of a diagnostic.
fn helps(d: &enrang_diag::Diagnostic) -> Vec<&str> {
    d.helps.iter().map(|h| h.message.as_str()).collect()
}

/// Each secondary label as `line:col text`.
fn secondaries(r: &Run, d: &enrang_diag::Diagnostic) -> Vec<String> {
    d.secondary
        .iter()
        .map(|l| {
            let loc = r.map.loc(l.span.lo);
            format!("{}:{} {}", loc.line, loc.col, l.text)
        })
        .collect()
}

fn visibility(h: &mut Harness) {
    h.case("classes/a `private` member is unseen in a subclass, a `protected` one outside (S:580)", || {
        let r = main_lib(
            "public class Animal {
  private name: string = \"\";
  protected age: i64 = 0;
  private hide(): void {}
}
public class Dog extends Animal {
  public n(): string { return this.name; }
  public a(): i64 { return this.age; }
  public h(): void { this.hide(); }
}
public function f(d: &Dog): i64 { return d.age; }
",
        );
        expect(
            &r,
            &[
                "EN0308 7:36 `name` is private to `Animal` [only the body of `Animal` can use it]",
                "EN0308 9:27 `hide` is private to `Animal` [only the body of `Animal` can use it]",
                "EN0308 11:44 `age` is protected in `Animal` [only `Animal` and its subclasses can use it]",
            ],
        );
    });
    h.case("classes/Q37-private and S2-26-test: a test part sees private items, not private members", || {
        let r = run_with(
            &[
                (
                    "main.en",
                    "public class Counter {
  private count: i64 = 0;
  protected step: i64 = 1;
  private reset(): void {}
  public static make(): Counter { unreachable(); }
}
private function clamp(x: i64, lo: i64, hi: i64): i64 { return x; }
",
                ),
                (
                    "main.test.en",
                    "test(\"t\", () => {
  let c = Counter.make();
  const a = c.count;
  c.reset();
  const b = c.step;
  const d = clamp(300, 0, 255);
});
private class Probe extends Counter {
  public get(): i64 { return this.step; }
}
",
                ),
            ],
            LibSource::Embedded,
            "x86_64-linux",
        );
        expect(
            &r,
            &[
                "EN0308 3:15 `count` is private to `Counter` [only the body of `Counter` can use it]",
                "EN0308 4:5 `reset` is private to `Counter` [only the body of `Counter` can use it]",
                "EN0308 5:15 `step` is protected in `Counter` [only `Counter` and its subclasses can use it]",
            ],
        );
    });
    h.case("classes/D8-bound: a class bound gives no `protected` member", || {
        let r = main_lib(
            "public class Labeler {
  protected secret: i64 = 0;
  public label(n: &string): &string { return n; }
}
public function tag<T extends Labeler>(x: &T, n: &string): &string { const s = x.secret; return x.label(n); }
",
        );
        expect(
            &r,
            &["EN0308 5:82 `secret` is protected in `Labeler` [only `Labeler` and its subclasses can use it]"],
        );
    });
}

fn finals(h: &mut Harness) {
    h.case("classes/EN0442: extending a `final` class (S:584)", || {
        let r = main_en("public final class Animal {}\npublic class Dog extends Animal {}\n");
        expect(
            &r,
            &["EN0442 2:26 `Animal` is `final`, so no class can extend it [`Animal` is declared `final`]"],
        );
        assert_eq!(r.map.text(r.diags[0].primary.span), "Animal");
    });
    h.case("classes/EN0442: a class that is not `final` can be extended, abstract or plain", || {
        main_en("public class Animal {}\npublic class Dog extends Animal {}\npublic abstract class Shape {}\npublic final class Sq extends Shape {}\n").clean();
    });
}

/// `Q32-field-override`'s `Animal`, then `rest` (its `Dog`).
fn animal_and(dog: &str) -> String {
    format!(
        "public class Animal {{
  public sound: string = \"...\";
  public constructor() {{}}
}}
{dog}"
    )
}

fn field_overrides(h: &mut Harness) {
    h.case("classes/a field override keeps the base's field (Q32-field-override)", || {
        let r = main_lib(&animal_and(
            "public class Dog extends Animal {\n  public override sound: string = \"woof\";\n}\n",
        ));
        r.clean();
        let dog = r.tcx.adt_of(r.def("main::Dog")).expect("Dog");
        let class = r.tcx.adt(dog).as_class().expect("a class");
        assert_eq!(class.overrides, [FieldIdx(0)]);
        assert_eq!(class.fields.len(), 1, "one `sound`, in one slot");
    });
    h.case("classes/EN0443: an override field of another type (Q32-field-rules)", || {
        let r = main_lib(&animal_and(
            "public class Dog extends Animal {\n  public override sound: i64 = 1;\n}\n",
        ));
        expect(
            &r,
            &["EN0443 6:19 `sound` overrides nothing in `Animal` [`Animal.sound` has type `string`]"],
        );
        let d = only(&r);
        assert_eq!(secondaries(&r, d), ["2:3 `Animal.sound` is declared here"]);
        assert_eq!(
            d.entries[0].text,
            "an `override` keeps the inherited field's type, `readonly` and visibility"
        );
    });
    h.case("classes/EN0443: an override field of another visibility (Q32-field-rules)", || {
        let r = main_lib(&animal_and(
            "public class Dog extends Animal {\n  protected override sound: string = \"woof\";\n}\n",
        ));
        expect(
            &r,
            &["EN0443 6:22 `sound` overrides nothing in `Animal` [`Animal.sound` is `public`]"],
        );
    });
    h.case("classes/EN0443: an override field that drops or adds `readonly`", || {
        let r = main_lib(
            "public class Animal {\n  public readonly sound: string = \"...\";\n}\npublic class Dog extends Animal {\n  public override sound: string = \"woof\";\n}\npublic class Cat extends Dog {\n  public override readonly sound: string = \"meow\";\n}\n",
        );
        // `Dog`'s override replaces nothing, so `Cat` still sees `Animal.sound`,
        // whose `readonly` it keeps.
        expect(
            &r,
            &["EN0443 5:19 `sound` overrides nothing in `Animal` [`Animal.sound` is `readonly`]"],
        );
    });
    h.case("classes/EN0444: a field with a visible base field's name and no `override`", || {
        let r = main_lib(&animal_and(
            "public class Dog extends Animal {\n  public sound: string = \"woof\";\n}\n",
        ));
        expect(
            &r,
            &["EN0444 6:10 `sound` replaces `Animal.sound` without `override` [`Animal` already has a field `sound`]"],
        );
        let d = only(&r);
        assert_eq!(helps(d), ["add `override`"]);
        let edit = &d.helps[0].edits[0];
        assert_eq!(edit.replacement, "override ");
        assert_eq!(r.map.loc(edit.span.lo).col, 10, "after `public `");
        let r = main_lib(&animal_and(
            "public class Dog extends Animal {\n  public readonly sound: string = \"woof\";\n}\n",
        ));
        let d = only(&r);
        assert_eq!(d.code.name(), "EN0444");
        assert_eq!(
            r.map.loc(d.helps[0].edits[0].span.lo).col,
            10,
            "`override` goes before `readonly` (SPEC 3.1)"
        );
    });
    h.case("classes/EN0443: an override field with no field above to replace", || {
        let r = main_lib(&animal_and(
            "public class Dog extends Animal {\n  public override volume: i64 = 3;\n}\n",
        ));
        expect(
            &r,
            &["EN0443 6:19 `volume` overrides nothing in `Animal` [no class above `Dog` has a field `volume`]"],
        );
        let r = main_lib("public class Dog {\n  public override volume: i64 = 3;\n}\n");
        expect(
            &r,
            &["EN0443 2:19 `volume` overrides nothing [`Dog` extends no class]"],
        );
    });
    h.case("classes/a `private` base field is invisible: a same-named field is new (Q32-field-rules)", || {
        let r = main_lib(
            "public class Animal {\n  private sound: string = \"...\";\n}\npublic class Dog extends Animal {\n  private sound: string = \"woof\";\n}\n",
        );
        r.clean();
        let dog = r.tcx.adt_of(r.def("main::Dog")).expect("Dog");
        let names: Vec<&str> = r.tcx.adt(dog).as_class().expect("a class").fields.iter().map(|f| f.name.as_str()).collect();
        assert_eq!(names, ["sound", "sound"], "two fields");
        let r = main_lib(
            "public class Animal {\n  private sound: string = \"...\";\n}\npublic class Dog extends Animal {\n  private override sound: string = \"woof\";\n}\n",
        );
        expect(
            &r,
            &["EN0443 5:20 `sound` overrides nothing in `Animal` [`Animal.sound` is private, so `Dog` can't see it]"],
        );
    });
    h.case("classes/Q32-field-rules: the programs that pass phase 2", || {
        // `this` in an override's default is EN0610, phase 3's.
        main_lib(&animal_and(
            "public class Dog extends Animal {\n  public override sound: string = this.sound.toUpperCase();\n}\n",
        ))
        .clean();
        // A parameter property's field, overridden.
        main_lib("public class Animal {\n  public constructor(public sound: string) {}\n}\npublic class Dog extends Animal {\n  public override sound: string = \"woof\";\n}\npublic function f(m: Dog): void { console.log(m.sound); }\n").clean();
        // No constructor anywhere: the named form uses the new default.
        main_lib("public class Animal {\n  public sound: string = \"...\";\n}\npublic class Dog extends Animal {\n  public override sound: string = \"woof\";\n}\n").clean();
        // A `protected` field overridden with its type, `readonly` and visibility.
        main_lib("public class Animal {\n  protected readonly sound: string = \"...\";\n}\npublic class Dog extends Animal {\n  protected override readonly sound: string = \"woof\";\n}\n").clean();
        // Through a generic base: the field's type at the subclass's arguments.
        main_lib("public class Holder<T> {\n  public v: T[] = [];\n}\npublic class Ints extends Holder<i64> {\n  public override v: i64[] = [1];\n}\n").clean();
    });
    h.case("classes/EN0444: a parameter property named like a visible base field", || {
        let r = main_lib(&animal_and(
            "public class Dog extends Animal {\n  public constructor(public sound: string) { super(); }\n}\n",
        ));
        expect(
            &r,
            &["EN0444 6:29 `sound` replaces `Animal.sound` without `override` [`Animal` already has a field `sound`]"],
        );
        assert_eq!(
            helps(only(&r)),
            ["a parameter property can't override: rename it, or assign `this.sound` in the constructor's body"]
        );
    });
}

/// SPEC 4.3's `Animal`, with members to replace.
const ANIMAL: &str = "public class Animal {
  public name: string = \"x\";
  public speak(): string { return this.name; }
  public hear(n: i64): void {}
  private secret(): void {}
  protected tell(): i64 { return 1; }
  public unsafe poke(): void {}
  public static make(): i64 { return 0; }
}
";

fn method_overrides(h: &mut Harness) {
    h.case(
        "classes/a method override (S:584) and overloads beside it compile",
        || {
            main_lib(&format!(
                "{ANIMAL}public class Dog extends Animal {{
  public override speak(): string {{ return \"woof\"; }}
  public speak(loud: bool): string {{ return \"WOOF\"; }}
  public override hear(n: i64): void {{}}
  public override tell(): i64 {{ return 2; }}
  public override unsafe poke(): void {{}}
  public secret(): void {{}}
  public static make(): i64 {{ return 1; }}
}}
public function introduce(a: &Animal): void {{ console.log(a.speak()); }}
"
            ))
            .clean();
            // A `static` method has no slot: an instance method of its name and
            // parameters is a new method.
            main_lib(&format!(
                "{ANIMAL}public class Dog extends Animal {{\n  public make(): i64 {{ return 1; }}\n}}\n"
            ))
            .clean();
        },
    );
    h.case("classes/EN0444: a method replacing a base method without `override` (S:584)", || {
        let r = main_lib(&format!(
            "{ANIMAL}public class Dog extends Animal {{\n  public speak(): string {{ return \"woof\"; }}\n}}\n"
        ));
        expect(
            &r,
            &["EN0444 11:10 `speak` replaces `Animal.speak` without `override` [`Animal.speak` has the same parameters]"],
        );
        let d = only(&r);
        assert_eq!(secondaries(&r, d), ["3:10 `Animal.speak` is declared here"]);
        assert_eq!(helps(d), ["add `override`"]);
        assert_eq!(r.map.loc(d.helps[0].edits[0].span.lo).col, 10);
        // `override` goes before a receiver mark.
        let r = main_lib(
            "public class A {\n  public move m(): void {}\n}\npublic class B extends A {\n  public move m(): void {}\n}\n",
        );
        let d = only(&r);
        assert_eq!(d.code.name(), "EN0444");
        assert_eq!(r.map.loc(d.helps[0].edits[0].span.lo).col, 10, "before `move`");
        // ... and after `abstract`.
        let r = main_lib(
            "public class A {\n  public m(): void {}\n}\npublic abstract class B extends A {\n  public abstract m(): void;\n}\n",
        );
        let d = only(&r);
        assert_eq!(d.code.name(), "EN0444");
        assert_eq!(r.map.loc(d.helps[0].edits[0].span.lo).col, 19, "after `abstract `");
    });
    h.case("classes/EN0443: an override method that matches no base overload", || {
        let r = main_lib(&format!(
            "{ANIMAL}public class Dog extends Animal {{
  public override bark(): void {{}}
  public override speak(loud: bool): string {{ return \"w\"; }}
  public override speak(): i64 {{ return 1; }}
  public override poke(): void {{}}
  public override secret(): void {{}}
}}
"
        ));
        expect(
            &r,
            &[
                "EN0443 11:19 `bark` overrides nothing in `Animal` [no class above `Dog` has a method `bark`]",
                "EN0443 12:19 `speak` overrides nothing in `Animal` [no `speak` above `Dog` takes these parameters]",
                "EN0443 13:19 `speak` overrides nothing in `Animal` [`Animal.speak` returns `string`]",
                "EN0443 14:19 `poke` overrides nothing in `Animal` [`Animal.poke` is `unsafe`]",
                "EN0443 15:19 `secret` overrides nothing in `Animal` [`Animal.secret` is private, so `Dog` can't see it]",
            ],
        );
        assert_eq!(
            secondaries(&r, &r.diags[1]),
            ["3:10 `Animal.speak` is declared here"]
        );
    });
    h.case("classes/EN0443: `override` on a `static` method or in a class with no base", || {
        let r = main_lib(&format!(
            "{ANIMAL}public class Dog extends Animal {{\n  public static override make(): i64 {{ return 1; }}\n}}\npublic class Cat {{\n  public override speak(): string {{ return \"meow\"; }}\n}}\n"
        ));
        expect(
            &r,
            &[
                "EN0443 11:26 `make` overrides nothing in `Animal` [a `static` method has no method-table slot to replace]",
                "EN0443 14:19 `speak` overrides nothing [`Cat` extends no class]",
            ],
        );
    });
    h.case("classes/an override reaches a method declared two classes up", || {
        let base = "public class A {\n  public m(x: i64): void {}\n}\npublic class B extends A {}\n";
        main_lib(&format!("{base}public class C extends B {{\n  public override m(x: i64): void {{}}\n}}\n")).clean();
        let r = main_lib(&format!("{base}public class C extends B {{\n  public m(x: i64): void {{}}\n}}\n"));
        expect(
            &r,
            &["EN0444 6:10 `m` replaces `A.m` without `override` [`A.m` has the same parameters]"],
        );
        // The nearest declaration is the one replaced.
        let r = main_lib("public class A {\n  public m(): i64 { return 1; }\n}\npublic class B extends A {\n  public override m(): i64 { return 2; }\n}\npublic class C extends B {\n  public m(): i64 { return 3; }\n}\n");
        expect(
            &r,
            &["EN0444 8:10 `m` replaces `B.m` without `override` [`B.m` has the same parameters]"],
        );
    });
    h.case("classes/overrides through a generic base compare at its arguments", || {
        let base = "public class Box2<T> {\n  public put(x: T): void {}\n}\n";
        main_lib(&format!("{base}public class Ints extends Box2<i64> {{\n  public override put(x: i64): void {{}}\n}}\n")).clean();
        let r = main_lib(&format!("{base}public class Ints extends Box2<i64> {{\n  public put(x: i64): void {{}}\n}}\n"));
        expect(
            &r,
            &["EN0444 5:10 `put` replaces `Box2.put` without `override` [`Box2.put` has the same parameters]"],
        );
        main_lib(&format!("{base}public class Ints extends Box2<i64> {{\n  public put(x: string): void {{}}\n}}\n")).clean();
    });
    h.case("classes/S2-29-fmt: the first `fmt` of a chain takes no `override`", || {
        // A written `fmt` is inherited like any method.
        main_lib("public class Animal {\n  public constructor(public name: string) {}\n  public fmt(let f: &Formatter): void {}\n}\npublic class Dog extends Animal {\n  public tricks: i64 = 3;\n}\n").clean();
        // With no `fmt` above, `Dog`'s is the first, written without `override`.
        main_lib("public class Animal {}\npublic class Dog extends Animal {\n  public fmt(let f: &Formatter): void {}\n}\n").clean();
        let r = main_lib("public class Animal {}\npublic class Dog extends Animal {\n  public override fmt(let f: &Formatter): void {}\n}\n");
        expect(
            &r,
            &["EN0443 3:19 `fmt` overrides nothing in `Animal` [no class above `Dog` writes `fmt`: the printer is synthesised, not a member]"],
        );
        // Below a written `fmt`, an override needs `override`.
        let r = main_lib("public class Animal {\n  public fmt(let f: &Formatter): void {}\n}\npublic class Dog extends Animal {\n  public fmt(let f: &Formatter): void {}\n}\n");
        assert_eq!(r.codes(), ["EN0444"], "{}", r.rendered());
    });
}

const SHAPE: &str = "public abstract class Shape {\n  public abstract area(): i64;\n}\n";

fn abstracts(h: &mut Harness) {
    h.case(
        "classes/EN0446: a class that is not abstract lacking an abstract method (S:586)",
        || {
            let r = main_lib(&format!(
                "{SHAPE}public class Sq extends Shape {{\n  public side: i64;\n}}\n"
            ));
            expect(
                &r,
                &["EN0446 4:14 `Sq` does not implement `Shape.area` [`Sq` is not `abstract`]"],
            );
            let d = only(&r);
            assert_eq!(
                secondaries(&r, d),
                ["2:19 `Shape.area` is declared `abstract` here"]
            );
            assert_eq!(
                helps(d),
                ["implement it with `override`, or declare `Sq` `abstract`"]
            );
        },
    );
    h.case("classes/EN0446: every missing method, once, at the class", || {
        let r = main_lib("public abstract class Shape {\n  public abstract area(): i64;\n  public abstract perimeter(): i64;\n  public abstract name(): string;\n}\npublic class Sq extends Shape {\n  public override perimeter(): i64 { return 4; }\n}\n");
        expect(
            &r,
            &["EN0446 6:14 `Sq` does not implement `Shape.area` and `Shape.name` [`Sq` is not `abstract`]"],
        );
        assert_eq!(
            helps(only(&r)),
            ["implement them with `override`, or declare `Sq` `abstract`"]
        );
        // Its own abstract method: the class is made `abstract`, or the method
        // given a body.
        let r = main_lib("public class C {\n  public abstract m(): void;\n}\n");
        expect(
            &r,
            &["EN0446 1:14 `C` does not implement `C.m` [`C` is not `abstract`]"],
        );
        let d = only(&r);
        assert_eq!(secondaries(&r, d), ["2:19 `C.m` is declared `abstract` here"]);
        assert_eq!(helps(d), ["declare `C` `abstract`, or give it a body"]);
    });
    h.case("classes/EN0446: implemented anywhere between, or left to an abstract class", || {
        main_lib(&format!("{SHAPE}public abstract class Mid extends Shape {{}}\npublic class Leaf extends Mid {{\n  public override area(): i64 {{ return 1; }}\n}}\n")).clean();
        main_lib(&format!("{SHAPE}public class Mid extends Shape {{\n  public override area(): i64 {{ return 1; }}\n}}\npublic class Leaf extends Mid {{}}\n")).clean();
        // A `private` abstract method is unseen below, so nothing implements it.
        let r = main_lib("public abstract class A {\n  private abstract m(): void;\n}\npublic class B extends A {\n  public m(): void {}\n}\n");
        expect(
            &r,
            &["EN0446 4:14 `B` does not implement `A.m` [`B` is not `abstract`]"],
        );
        // Implementing without `override` is EN0444, and implements it.
        let r = main_lib(&format!("{SHAPE}public class Sq extends Shape {{\n  public area(): i64 {{ return 1; }}\n}}\n"));
        assert_eq!(r.codes(), ["EN0444"], "{}", r.rendered());
    });
    h.case("classes/D8-super: EN0457 at `super.m()` whose nearest `m` is abstract", || {
        let r = main_lib(&format!(
            "{SHAPE}public class Sq extends Shape {{\n  public side: i64;\n  public override area(): i64 {{ return super.area() + this.side; }}\n}}\n"
        ));
        expect(
            &r,
            &["EN0457 6:40 `Shape.area` is abstract, so it has no body to call [the nearest `area` above `Sq` is abstract]"],
        );
        assert_eq!(r.map.text(r.diags[0].primary.span), "super.area()");
        // The nearest `area` above `Sq` is `Square`'s.
        main_lib(&format!(
            "{SHAPE}public class Square extends Shape {{\n  public side: i64;\n  public override area(): i64 {{ return this.side * this.side; }}\n}}\npublic class Sq extends Square {{\n  public override area(): i64 {{ return super.area() + this.side; }}\n}}\n"
        ))
        .clean();
    });
}

/// `S2-03-into`'s classes.
const INTO: &str = "public class Animal {
  public constructor(public name: string) {}
  public move into(): Animal { return *this; }
  public move takeName(): string { return this.name; }
}
public class Dog extends Animal {
  private tricks: string[] = [];
  public constructor(name: string) { super(name); }
}
";

/// `C4-move-inherited`'s `Builder`.
const BUILDER: &str = "public class Builder {
  private parts: string[];
  public constructor() {}
  public add(s: &string): void { this.parts.push(s.length() == 0 ? \"\" : \"x\"); }
  public move build(): string[] { return this.parts; }
}
";

fn moves(h: &mut Harness) {
    h.case("classes/S2-03-into: EN0458 at an inherited `move` method's call", || {
        let r = main_lib(&format!(
            "{INTO}public function f(rex: Dog): Animal {{ return rex.into(); }}
public function g(an: Animal): Animal {{ return an.into(); }}
public function h(rex: Dog): string {{ return rex.takeName(); }}
private function k<T extends Animal>(x: T): Animal {{ return x.into(); }}
"
        ));
        expect(
            &r,
            &[
                "EN0458 10:46 `move` method not declared in the receiver's class [`Dog` inherits `into` from `Animal`]",
                "EN0458 12:46 `move` method not declared in the receiver's class [`Dog` inherits `takeName` from `Animal`]",
            ],
        );
        assert_eq!(r.map.text(r.diags[0].primary.span), "rex.into()");
        assert_eq!(helps(&r.diags[0]), ["override `into` in `Dog`"]);
        assert_eq!(helps(&r.diags[1]), ["override `takeName` in `Dog`"]);
    });
    h.case("classes/EN0458: `this.m()` in a `move` method, and through `Box`", || {
        let r = main_lib(&format!(
            "{INTO}public class Puppy extends Dog {{\n  public move grow(): Animal {{ return this.into(); }}\n}}\npublic function b(p: Box<Dog>): Animal {{ return p.into(); }}\npublic function c(p: Box<Animal>): Animal {{ return p.into(); }}\n"
        ));
        expect(
            &r,
            &[
                "EN0458 11:39 `move` method not declared in the receiver's class [`Puppy` inherits `into` from `Animal`]",
                "EN0458 13:49 `move` method not declared in the receiver's class [`Dog` inherits `into` from `Animal`]",
            ],
        );
    });
    h.case("classes/EN0458: `Box`'s own `move` method is no inherited one", || {
        // `unbox` is declared by `Box`, not by a base of the boxed class (S6).
        let r = main_lib(&format!(
            "{INTO}public function u(p: Box<Dog>): Dog {{ return p.unbox(); }}\npublic function v(p: Box<Dog>): Animal {{ return p.into(); }}\n"
        ));
        expect(
            &r,
            &["EN0458 11:49 `move` method not declared in the receiver's class [`Dog` inherits `into` from `Animal`]"],
        );
    });
    h.case("classes/C4-move-inherited: EN0458 at `super.build()` with the helper help", || {
        let r = main_lib(&format!(
            "{BUILDER}public class HtmlBuilder extends Builder {{
  public constructor() {{ super(); }}
  public override move build(): string[] {{ return super.build(); }}
}}
public function use(b: HtmlBuilder): string[] {{ return b.build(); }}
"
        ));
        expect(
            &r,
            &["EN0458 9:51 `move` method not declared in the receiver's class [`build` is a `move` method of `Builder`]"],
        );
        assert_eq!(
            helps(only(&r)),
            ["move the state out with a helper the base shares, `protected takeParts(): string[] { return mem.replace(&this.parts, []); }`"]
        );
    });
    h.case("classes/C4-move-inherited: EN0458 at `b.build()` on a class that inherits it", || {
        let r = main_lib(&format!(
            "{BUILDER}public class HtmlBuilder extends Builder {{
  public constructor() {{ super(); }}
}}
public function use(b: HtmlBuilder): string[] {{ return b.build(); }}
"
        ));
        expect(
            &r,
            &["EN0458 10:56 `move` method not declared in the receiver's class [`HtmlBuilder` inherits `build` from `Builder`]"],
        );
        assert_eq!(helps(only(&r)), ["override `build` in `HtmlBuilder`"]);
    });
    h.case(
        "classes/C4-move-inherited: the helper form and an interface receiver compile",
        || {
            main_lib(
                "public class Builder {
  private parts: string[];
  public constructor() {}
  protected takeParts(): string[] { const out: string[] = []; return out; }
  public move build(): string[] { return this.parts; }
}
public class HtmlBuilder extends Builder {
  public constructor() { super(); }
  public override move build(): string[] { return this.takeParts(); }
}
public interface Buildable { move build(): string[]; }
public function consume(b: Buildable): string[] { return b.build(); }
public function use(b: HtmlBuilder): string[] { return b.build(); }
",
            )
            .clean();
        },
    );
    h.case("classes/EN0458: a `super.m()` to a `move` method whose body is no field read", || {
        let r = main_lib("public class A {\n  public move m(): i64 { return 1; }\n}\npublic class B extends A {\n  public override move m(): i64 { return super.m(); }\n}\n");
        assert_eq!(r.codes(), ["EN0458"], "{}", r.rendered());
        assert_eq!(
            helps(only(&r)),
            ["move the state out with a helper the base shares: a `protected` method that is not `move` and takes it with `mem.replace`"]
        );
    });
    h.case("classes/C4-move-inherited: warning EN0459 for a `move` body in an abstract class", || {
        let r = main_lib("public abstract class Task {\n  public move run(): string { return \"done\"; }\n}\n");
        expect(
            &r,
            &["EN0459 2:15 `move` method of an abstract class can never run [no object is ever exactly a `Task`]"],
        );
        assert_eq!(helps(only(&r)), ["declare it `abstract`"]);
        assert!(r.program.is_some(), "a warning does not stop phase 2");
        main_lib("public abstract class Task {\n  public abstract move run(): string;\n}\n").clean();
        main_lib("public class Task {\n  public move run(): string { return \"done\"; }\n}\n").clean();
    });
}

fn once_per_type(h: &mut Harness) {
    let animal = "public class Animal {\n  public show<T>(x: &T): void {}\n}\n";
    h.case("classes/VI-05-override: EN0460 at an override of a generic method", || {
        let r = main_lib(&format!(
            "public class Animal {{\n  public show<T>(x: &T): void {{}}\n}}\npublic class Dog extends Animal {{\n  public override show<T>(x: &T): void {{}}\n}}\n"
        ));
        expect(
            &r,
            &["EN0460 5:19 `show` has its own type parameters, so it can't be overridden [`Animal.show` is compiled once per type, so it has no method-table slot]"],
        );
        let d = only(&r);
        assert_eq!(helps(d), ["give Dog's method another name"]);
        assert_eq!(secondaries(&r, d), ["2:10 `Animal.show` is declared here"]);
    });
    h.case("classes/VI-06-tables: EN0460 with or without `override`, and renamed parameters", move || {
        for dog in [
            "  public show<T>(x: &T): void {}\n",
            "  public show<U>(y: &U): void {}\n",
        ] {
            let r = main_lib(&format!("{animal}public class Dog extends Animal {{\n{dog}}}\n"));
            expect(
                &r,
                &["EN0460 5:10 `show` has its own type parameters, so it can't be overridden [`Animal.show` is compiled once per type, so it has no method-table slot]"],
            );
        }
    });
    h.case("classes/VI-06-tables: another signature is an overload; a `private` one is unseen", move || {
        main_lib(&format!("{animal}public class Dog extends Animal {{\n  public show(x: &i64): void {{}}\n}}\n")).clean();
        main_lib("public class Animal {\n  private show<T>(x: &T): void {}\n}\npublic class Dog extends Animal {\n  public show<T>(x: &T): void {}\n}\n").clean();
        main_lib(&format!("{animal}public class Dog extends Animal {{}}\nprivate function greet(p: &Animal): void {{ const n: i64 = 42; p.show(&n); }}\n")).clean();
    });
    h.case("classes/VI-06-tables: EN0460 at an abstract method compiled once per type", || {
        let r = main_lib("public abstract class Animal {\n  public abstract show<T>(x: &T): void;\n}\n");
        expect(
            &r,
            &["EN0460 2:19 `show` has its own type parameters, so it can't be overridden [no subclass could implement it]"],
        );
        assert_eq!(helps(only(&r)), ["give `show` a body"]);
    });
    h.case("classes/EN0460: a by-value interface or an object-type parameter; `&I` overrides", || {
        let speaker = "public interface Speaker { speak(): string; }\n";
        let r = main_lib(&format!(
            "{speaker}public class Animal {{\n  public hear(s: Speaker): void {{}}\n  public greet(p: &{{ name: string }}): void {{}}\n  public tell(s: &Speaker): string {{ return s.speak(); }}\n}}\npublic class Dog extends Animal {{\n  public override hear(s: Speaker): void {{}}\n  public override greet(p: &{{ name: string }}): void {{}}\n  public override tell(s: &Speaker): string {{ return \"dog\"; }}\n}}\n"
        ));
        expect(
            &r,
            &[
                "EN0460 8:19 `hear` takes an interface by value, so it can't be overridden [`Animal.hear` is compiled once per type, so it has no method-table slot]",
                "EN0460 9:19 `greet` takes an object type, so it can't be overridden [`Animal.greet` is compiled once per type, so it has no method-table slot]",
            ],
        );
    });
}

fn implicit_overloads(h: &mut Harness) {
    h.case("classes/an `&I` parameter of another interface is an overload, not an override", || {
        let ifaces = "public interface Speaker { speak(): string; }\npublic interface Hearer { hear(): string; }\n";
        main_lib(&format!("{ifaces}public class Animal {{\n  public tell(s: &Speaker): void {{}}\n}}\npublic class Dog extends Animal {{\n  public tell(s: &Hearer): void {{}}\n}}\n")).clean();
        let r = main_lib(&format!("{ifaces}public class Animal {{\n  public tell(s: &Speaker): void {{}}\n}}\npublic class Dog extends Animal {{\n  public override tell(s: &Hearer): void {{}}\n}}\n"));
        expect(
            &r,
            &["EN0443 7:19 `tell` overrides nothing in `Animal` [no `tell` above `Dog` takes these parameters]"],
        );
    });
    h.case("classes/object-type parameters compare their shapes at the base's arguments", || {
        let base = "public class Box2<T> {\n  public show(p: &{ v: T }): void {}\n}\n";
        let r = main_lib(&format!("{base}public class Ints extends Box2<i64> {{\n  public show(p: &{{ v: i64 }}): void {{}}\n}}\n"));
        expect(
            &r,
            &["EN0460 5:10 `show` takes an object type, so it can't be overridden [`Box2.show` is compiled once per type, so it has no method-table slot]"],
        );
        main_lib(&format!("{base}public class Ints extends Box2<i64> {{\n  public show(p: &{{ v: string }}): void {{}}\n}}\n")).clean();
    });
}

fn copies(h: &mut Harness) {
    h.case("classes/VI-04-copy: EN0418 at `Snapshot`, for a destructor in the chain (S:589)", || {
        let r = main_lib(
            "public class Region {
  protected base: *u8;
  protected size: usize;
  public constructor(size: usize) { this.size = size; }
  public destructor() {}
}
public class Snapshot extends Region implements Copy {}
",
        );
        expect(
            &r,
            &["EN0418 7:14 `Region`'s destructor runs for every `Snapshot`, so copying one would run it twice [a Copy class can have no destructor]"],
        );
        assert_eq!(
            helps(only(&r)),
            ["remove `implements Copy`; to copy a `Snapshot`, write `clone()`"]
        );
        let r = main_lib("public class R implements Copy {\n  public destructor() {}\n}\n");
        expect(
            &r,
            &["EN0418 1:14 `R`'s destructor runs for every `R`, so copying one would run it twice [a Copy class can have no destructor]"],
        );
    });
    h.case("classes/VI-04-copy: numeric fields over a base with no destructor compile", || {
        main_lib("public class Point2 {\n  public x: i64;\n  public y: i64;\n}\npublic class Point3 extends Point2 implements Copy {\n  public z: i64;\n}\n").clean();
        main_lib("public class P implements Copy {\n  private r: &i64 | null;\n  public t: [i32, bool];\n  public p: *u8;\n  public a: f64[4];\n}\n").clean();
    });
    h.case("classes/EN0418: a field that is not Copy, inherited ones included", || {
        let r = main_lib("public class C implements Copy {\n  public n: i64;\n  public name: string;\n}\n");
        expect(
            &r,
            &["EN0418 1:14 `C` can't be Copy: `name` is a `string` [`name` is not Copy]"],
        );
        let d = only(&r);
        assert_eq!(secondaries(&r, d), ["3:3 `name` is declared here"]);
        assert_eq!(helps(d), ["remove `implements Copy`; to copy a `C`, write `clone()`"]);
        let r = main_lib("public class Base {\n  public tags: i64[] = [];\n}\npublic class D extends Base implements Copy {\n  public n: i64;\n}\n");
        expect(
            &r,
            &["EN0418 4:14 `D` can't be Copy: `tags` is an `i64[]` [`tags` is not Copy]"],
        );
    });
    h.case(
        "classes/EN0418: a type parameter is Copy only when bounded so",
        || {
            let r = main_lib("public class Pair<T> implements Copy {\n  public a: T;\n}\n");
            expect(
                &r,
                &["EN0418 1:14 `Pair` can't be Copy: `a` is a `T` [`a` is not Copy]"],
            );
            main_lib("public class Pair<T extends Copy> implements Copy {\n  public a: T;\n}\n")
                .clean();
        },
    );
    h.case(
        "classes/S2-08-copy: reference fields are Copy; the flag is phase 3's",
        || {
            main_lib(
                "let data: i64[] = [1, 2, 3];
let c = new Cursor(&data);
const c2 = c;
const e = c2.cur();
c.all().push(4);
console.log(*e);
private class Cursor implements Copy {
  private xs: &i64[];
  private i: i64 = 0;
  public constructor(xs: &i64[]) { this.xs = xs; }
  public cur(): &i64 { return &this.xs[this.i]; }
  public all(): &i64[] { return this.xs; }
}
",
            )
            .clean();
        },
    );
}

fn constructors(h: &mut Harness) {
    let person = "public class Person {\n  public constructor() {}\n}\n";
    h.case("classes/EN0448: a `private` field with no default and no constructor (S:582)", move || {
        let r = main_lib(&format!("{person}public class Team {{\n  private owner: Person;\n}}\n"));
        expect(
            &r,
            &["EN0448 4:14 `Team` needs a constructor: `owner` has no default [`owner` is `private`, so no named form can set it]"],
        );
        let d = only(&r);
        assert_eq!(secondaries(&r, d), ["5:3 `owner` has type `Person`, which has no default"]);
        assert_eq!(helps(d), ["give `owner` a default, or write a constructor that sets it"]);
    });
    h.case("classes/EN0448: a default, a type default, a constructor or `public` is enough", move || {
        for team in [
            "  private owner: Person | null;\n",
            "  private count: i64;\n  private name: string;\n  private xs: i64[];\n  private buf: u8[4];\n",
            "  private owner: Person;\n  public constructor(o: Person) { this.owner = o; }\n",
            "  public owner: Person;\n",
            "  private owner?: Person;\n",
        ] {
            main_lib(&format!("{person}public class Team {{\n{team}}}\n")).clean();
        }
    });
    h.case("classes/EN0448: a subclass field with no default and no constructor (S:587)", move || {
        let r = main_lib(&format!(
            "{person}public class Shape {{\n  public color: string = \"red\";\n}}\npublic class Circle extends Shape {{\n  public owner: Person;\n}}\n"
        ));
        expect(
            &r,
            &["EN0448 7:14 `Circle` needs a constructor: `owner` has no default [a subclass with no constructor needs a default for each field of its own]"],
        );
        main_lib("public class Shape {\n  public color: string = \"red\";\n}\npublic class Square extends Shape {\n  public side: i64;\n}\n").clean();
        // S:587's chain: a base with no constructor may leave a field with no
        // default to the subclass's constructor.
        main_lib(&format!(
            "{person}public class Shape {{\n  public color: string = \"red\";\n  public owner: Person;\n}}\npublic class Circle extends Shape {{\n  public constructor(public r: i64, o: Person) {{ super(); this.owner = o; }}\n}}\n"
        ))
        .clean();
        // An override is no field of its own.
        main_lib(&format!(
            "{person}public class Animal {{\n  protected owner: Person;\n  public constructor(o: Person) {{ this.owner = o; }}\n}}\npublic class Dog extends Animal {{\n  protected override owner: Person = new Person();\n}}\n"
        ))
        .clean();
    });
}

fn interfaces(h: &mut Harness) {
    h.case("classes/EN0606: a `destructor` declared in an interface (S:648)", || {
        let r = main_lib("public interface Closer {\n  destructor(): void;\n  close(): void;\n}\npublic class F implements Closer {\n  public close(): void {}\n}\n");
        expect(
            &r,
            &["EN0606 2:3 an interface can't declare a `destructor` [a destructor is never a member]"],
        );
        assert_eq!(
            helps(only(&r)),
            ["remove it: a class's own `destructor` runs by itself, and `dispose(x)` ends a value early"]
        );
    });
}

/// The `FieldInits` of class `name`.
fn inits<'r>(r: &'r Run, name: &str) -> &'r enrang_hir::FieldInits {
    let adt = r.tcx.adt_of(r.def(name)).expect("a class");
    r.program
        .as_ref()
        .unwrap_or_else(|| panic!("not checked: {}", r.rendered()))
        .field_inits
        .get(&adt)
        .unwrap_or_else(|| panic!("no initialisers for {name}"))
}

fn field_inits(h: &mut Harness) {
    h.case("classes/field initialisers: each typed at its field's type (D6)", || {
        let r = main_lib("public class C {\n  public n: i64 = 3;\n  public s: string = \"a\";\n  public t?: string;\n  public u: u8 = 7;\n}\n");
        r.clean();
        let fi = inits(&r, "main::C");
        let fields: Vec<FieldIdx> = fi.inits.iter().map(|(f, _)| *f).collect();
        assert_eq!(fields, [FieldIdx(0), FieldIdx(1), FieldIdx(3)], "no entry for `t?`");
        let tys: Vec<String> = fi.inits.iter().map(|(_, e)| ty(&r, e.ty)).collect();
        assert_eq!(tys, ["i64", "string", "u8"]);
        assert!(matches!(fi.inits[0].1.kind, ExprKind::Const(ConstValue::Int(3, _))), "{:?}", fi.inits[0].1);
        let ids: std::collections::BTreeSet<_> = fi.inits.iter().map(|(_, e)| e.id).collect();
        assert_eq!(ids.len(), 3, "ids are unique within the class");
        // A class with no initialiser has no entry.
        let r = main_lib("public class D {\n  public n: i64;\n}\n");
        r.clean();
        let adt = r.tcx.adt_of(r.def("main::D")).expect("D");
        assert!(!r.program.as_ref().expect("checked").field_inits.contains_key(&adt));
    });
    h.case(
        "classes/field initialisers: EN0401 with the annotation as its secondary",
        || {
            let r = main_lib("public class C {\n  public name: string = 5;\n}\n");
            assert_eq!(r.codes(), ["EN0401"], "{}", r.rendered());
            let d = &r.diags[0];
            assert_eq!(r.map.text(d.primary.span), "5");
            assert_eq!(
                secondaries(&r, d),
                ["2:16 `string` is required by this annotation"]
            );
            let r = main_lib("public class C {\n  public b: u8 = 300;\n}\n");
            assert_eq!(r.codes(), ["EN0411"], "{}", r.rendered());
        },
    );
    h.case("classes/field initialisers: an override's default sets the base's field", || {
        let r = main_lib(&animal_and(
            "public class Dog extends Animal {\n  public override sound: string = \"woof\";\n  public n: i64 = 2;\n}\n",
        ));
        r.clean();
        let fi = inits(&r, "main::Dog");
        let fields: Vec<FieldIdx> = fi.inits.iter().map(|(f, _)| *f).collect();
        assert_eq!(fields, [FieldIdx(0), FieldIdx(1)]);
        // A mismatched override is typed at its own type: EN0443 alone.
        let r = main_lib(&animal_and(
            "public class Dog extends Animal {\n  public override sound: i64 = 1;\n}\n",
        ));
        assert_eq!(r.codes(), ["EN0443"], "{}", r.rendered());
    });
    h.case("classes/field initialisers: constants, functions, generics, `this`", || {
        let r = main_lib("private const K: i64 = 4;\npublic function f(): i64 { return 2; }\npublic class Stack<T> {\n  public items: T[] = [];\n  public k: i64 = K;\n  public j: i64 = f();\n  public w: i64 = this.k;\n}\n");
        r.clean();
        let fi = inits(&r, "main::Stack");
        assert_eq!(ty(&r, fi.inits[0].1.ty), "T[]");
        assert!(matches!(fi.inits[2].1.kind, ExprKind::Call { .. }));
        // Parameter properties come between fields in member order.
        let r = main_lib("public class C {\n  public a: i64 = 1;\n  public constructor(public p: i64) {}\n  public b: i64 = 2;\n}\n");
        r.clean();
        let fields: Vec<FieldIdx> = inits(&r, "main::C").inits.iter().map(|(f, _)| *f).collect();
        assert_eq!(fields, [FieldIdx(0), FieldIdx(2)]);
    });
    h.case("classes/field initialisers: the passes of finished bodies run on them", || {
        let r = main_lib("public enum E { A, B }\npublic class C {\n  public n: i64 = match (E.A) { E.A => 1 };\n}\n");
        expect(&r, &["EN0501 3:26 `match` doesn't handle `E.B` [missing `E.B`]"]);
    });
}

fn elsewhere(h: &mut Harness) {
    h.case("classes/library classes are not checked", || {
        main_lib("").clean();
    });
    h.case("classes/lowering's class programs, given what 4D's rules need, pass", || {
        // `lower.rs`'s cases, each with the change the request of stage 4D makes.
        let r = main_en("public class Animal {\n  protected sound: string = \"...\";\n  private secret: i64 = 0;\n  public constructor(public readonly name: string, n?: i64) { }\n}\npublic final class Dog extends Animal implements Copy {\n  protected override sound: string = \"woof\";\n  public secret: bool = false;\n  public tag?: string;\n}\n");
        assert_eq!(r.codes(), ["EN0418"], "{}", r.rendered());
        main_en("public class View {\n  private src: readonly &Slice<u8>;\n  private pair: [readonly &i64, &i64, readonly &i64];\n  public constructor(src: &Slice<u8>, pair: [&i64, &i64, &i64]) { this.src = src; this.pair = pair; }\n}\n").clean();
        main_en("public class Lexer { private src: &string; public constructor(s: &string) { this.src = s; } }\n").clean();
        let r = main_en("@repr(\"C\") public final class A {\n  public b: B;\n}\npublic final class B {\n  public c: C;\n}\npublic class C {}\n");
        assert_eq!(r.codes(), ["EN0827"], "{}", r.rendered());
        let r = main_en("@packed public final class A {\n  public e: E;\n}\npublic enum E { One { c: C }, Two }\npublic class C {}\n");
        assert_eq!(r.codes(), ["EN0827"], "{}", r.rendered());
        main_en("@repr(\"C\") public final class A {\n  public b: B;\n}\npublic final class B {\n  private c: Box<C> | null;\n}\npublic class C {}\n").clean();
        // An abstract method in a class that is not abstract is EN0446.
        let r = main_en("public class C { public m(): void; public abstract n(): void; }\n");
        assert_eq!(r.codes(), ["EN0446", "EN0806"], "{}", r.rendered());
        let r = main_en("public abstract class C { public m(): void; public abstract n(): void; }\npublic enum E { A; public k(): i64; }\n");
        assert_eq!(r.codes(), ["EN0806", "EN0806"], "{}", r.rendered());
        // The near-miss `EN0214/readonly_reference_field.pass.en` as the request
        // leaves it.
        main_lib("private class View {\n  private items: readonly &i64[];\n  private names: string[] = [];\n  public constructor(items: &i64[]) { this.items = items; }\n}\n").clean();
    });
}

/// The codes only stage 4D reports (plan h.1; EN0419 and EN0606 are shared).
const CLASS_CODES: &[&str] = &[
    "EN0416", "EN0418", "EN0442", "EN0443", "EN0444", "EN0446", "EN0448", "EN0457", "EN0458",
    "EN0459", "EN0460",
];

/// M1's near-misses that a rule of 4D refuses, each with that code: `View` has a
/// `private` reference field with no default and no constructor (EN0448, S:582).
/// The request of stage 4D gives it a constructor.
const AWAITING: &[(&str, &str)] = &[("EN0214/readonly_reference_field.pass.en", "EN0448")];

fn sweeps(h: &mut Harness) {
    h.case(
        "classes/SPEC's programs report none of 4D's codes beyond what their cases expect",
        || {
            let doc =
                std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/../../docs/SPEC.md"))
                    .expect("SPEC");
            let cases = extract_cases(&doc).expect("the cases extract");
            let ours = |code: &str| CLASS_CODES.contains(&code);
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
    h.case(
        "classes/M1's near-misses report none of 4D's codes (plan 0.3)",
        || {
            let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/compile");
            let mut files: Vec<std::path::PathBuf> = Vec::new();
            for dir in std::fs::read_dir(root).expect("tests/compile") {
                let dir = dir.expect("an entry").path();
                for f in std::fs::read_dir(&dir).expect("a code's directory") {
                    let f = f.expect("an entry").path();
                    if f.to_string_lossy().ends_with(".pass.en") {
                        files.push(f);
                    }
                }
            }
            files.sort();
            assert!(files.len() >= 60, "{}", files.len());
            let mut bad = Vec::new();
            for f in &files {
                let text = std::fs::read_to_string(f).expect("a near-miss");
                let r = run_with(&[("main.en", &text)], LibSource::Embedded, "x86_64-linux");
                let ours: Vec<String> = r
                    .diags
                    .iter()
                    .map(|d| d.code.name().to_owned())
                    .filter(|c| CLASS_CODES.contains(&c.as_str()))
                    .collect();
                // A near-miss that breaks a rule of 4D is fixed by the request of
                // stage 4D; until the merge applies it, it reports that code alone.
                let awaiting = AWAITING
                    .iter()
                    .find(|(name, _)| f.ends_with(name))
                    .is_some_and(|&(_, code)| ours == [code]);
                if !ours.is_empty() && !awaiting {
                    bad.push(format!("{}: {}", f.display(), r.rendered()));
                }
            }
            assert!(bad.is_empty(), "{}", bad.join("\n"));
        },
    );
}

/// Stage 6's review: the cases the mutation gate found unpinned.
fn review(h: &mut Harness) {
    h.case(
        "classes/EN0458 through `?.` on a nullable receiver of an inheriting class (mutant M44)",
        || {
            let r = main_lib(
                "public class A { public move into(): string { return \"a\"; } }
public class B extends A { }
public function g(b: B | null): void { const s = b?.into(); }
public function k(a: A | null): void { const s = a?.into(); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0458 3:50 `move` method not declared in the receiver's class [`B` inherits `into` from `A`]"]
            );
        },
    );
}
