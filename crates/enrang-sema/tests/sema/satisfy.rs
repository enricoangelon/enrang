//! Exact satisfaction (plan d.16, g.5; SPEC 4.4 S:609-617; owner 4D) at
//! `implements`, where it is EN0416: one firing program and one near-miss per
//! clause (`public`, same unsafety both ways, no `@requires`, is a method, equal
//! type parameters and bounds, equal parameter types, equal return type), with
//! the exact message, position, label and secondary; then own, inherited and
//! synthesised members, `Self`, generic interfaces, the prelude's nominal
//! interfaces, fields-only interfaces, sealed interfaces (EN0419) and
//! `implements` of what is no interface (EN0401).
//!
//! S:611's "auto-deref never contributes" needs a `Box<V>` standing for the type,
//! which only a bound's argument can be: that clause is 4A's EN0419 at a bound.

use enrang_testkit::Harness;

use crate::paths::{diags, main_lib};
use crate::support::Run;

pub fn register(h: &mut Harness) {
    clauses(h);
    members(h);
    nominal(h);
    shapes(h);
    others(h);
    review(h);
}

fn expect(r: &Run, want: &[&str]) {
    assert_eq!(diags(r), want, "{}", r.rendered());
}

/// The secondaries of `r`'s only diagnostic, as `line:col text`, and its notes.
fn extras(r: &Run) -> (Vec<String>, Vec<String>) {
    assert_eq!(r.diags.len(), 1, "{}", r.rendered());
    let d = &r.diags[0];
    let secondary = d
        .secondary
        .iter()
        .map(|l| {
            let loc = r.map.loc(l.span.lo);
            format!("{}:{} {}", loc.line, loc.col, l.text)
        })
        .collect();
    let notes = d.entries.iter().map(|e| e.text.clone()).collect();
    (secondary, notes)
}

/// `interface` then `class C implements I { body }` on the next line.
fn implementing(iface: &str, body: &str) -> Run {
    main_lib(&format!(
        "{iface}\npublic class C implements I {{ {body} }}\n"
    ))
}

const LABEL: &str = "[required by this `implements`]";

fn clauses(h: &mut Harness) {
    h.case(
        "satisfy/private: a `private` method never satisfies",
        || {
            let r = implementing(
                "public interface I { speak(): string; }",
                "private speak(): string { return \"w\"; }",
            );
            expect(
                &r,
                &[&format!(
                    "EN0416 2:27 `C` does not satisfy `I`: `speak` is private {LABEL}"
                )],
            );
            assert_eq!(extras(&r).0, ["2:39 `C.speak` is `private`"]);
            implementing(
                "public interface I { speak(): string; }",
                "public speak(): string { return \"w\"; }",
            )
            .clean();
        },
    );
    h.case(
        "satisfy/protected: a `protected` method never satisfies",
        || {
            let r = implementing(
                "public interface I { speak(): string; }",
                "protected speak(): string { return \"w\"; }",
            );
            expect(
                &r,
                &[&format!(
                    "EN0416 2:27 `C` does not satisfy `I`: `speak` is protected {LABEL}"
                )],
            );
            assert_eq!(extras(&r).0, ["2:41 `C.speak` is `protected`"]);
        },
    );
    h.case(
        "satisfy/unsafe-member: an `unsafe` member needs an `unsafe` method",
        || {
            let r = implementing(
                "public interface I { unsafe poke(): void; }",
                "public poke(): void {}",
            );
            expect(
                &r,
                &[&format!(
                    "EN0416 2:27 `C` does not satisfy `I`: `poke` is not `unsafe` {LABEL}"
                )],
            );
            assert_eq!(extras(&r).0, ["2:38 `C.poke` is not `unsafe`"]);
            implementing(
                "public interface I { unsafe poke(): void; }",
                "public unsafe poke(): void {}",
            )
            .clean();
        },
    );
    h.case(
        "satisfy/unsafe-method: a safe member needs a safe method",
        || {
            let r = implementing(
                "public interface I { poke(): void; }",
                "public unsafe poke(): void {}",
            );
            expect(
                &r,
                &[&format!(
                    "EN0416 2:27 `C` does not satisfy `I`: `poke` is `unsafe` {LABEL}"
                )],
            );
            assert_eq!(extras(&r).0, ["2:45 `C.poke` is `unsafe`"]);
            implementing(
                "public interface I { poke(): void; }",
                "public poke(): void {}",
            )
            .clean();
        },
    );
    h.case(
        "satisfy/requires: a method with `@requires` never satisfies",
        || {
            let r = implementing(
                "public interface I { count(): i64; }",
                "@requires(\"cmov\") public count(): i64 { return 1; }",
            );
            expect(
                &r,
                &[&format!(
                    "EN0416 2:27 `C` does not satisfy `I`: `count` has `@requires` {LABEL}"
                )],
            );
            assert_eq!(extras(&r).0, ["2:56 `C.count` has `@requires`"]);
            implementing(
                "public interface I { count(): i64; }",
                "public count(): i64 { return 1; }",
            )
            .clean();
        },
    );
    h.case(
        "satisfy/field: a field of the member's name is no method",
        || {
            let r = implementing(
                "public interface I { name(): &string; }",
                "public name: string = \"\";",
            );
            expect(
                &r,
                &[&format!(
                    "EN0416 2:27 `C` does not satisfy `I`: `name` is a field {LABEL}"
                )],
            );
            implementing(
                "public interface I { name(): &string; }",
                "private n: string = \"\"; public name(): &string { return &this.n; }",
            )
            .clean();
        },
    );
    h.case(
        "satisfy/type-params: equal type parameters and bounds",
        || {
            let iface = "public interface I { dump<T>(x: &T): void; }";
            let r = implementing(iface, "public dump(x: &i64): void {}");
            expect(
                &r,
                &[&format!(
                    "EN0416 2:27 `C` does not satisfy `I`: `dump` has another signature {LABEL}"
                )],
            );
            let (secondary, notes) = extras(&r);
            assert_eq!(secondary, ["2:38 `C.dump` is declared here"]);
            assert_eq!(notes, ["`I` declares `dump<T>(x: &T): void`"]);
            let r = implementing(iface, "public dump<T extends Clone>(x: &T): void {}");
            assert_eq!(r.codes(), ["EN0416"], "{}", r.rendered());
            let r = implementing(
                "public interface I { dump<T extends Clone>(x: &T): void; }",
                "public dump<T>(x: &T): void {}",
            );
            assert_eq!(r.codes(), ["EN0416"], "{}", r.rendered());
            implementing(iface, "public dump<U>(x: &U): void {}").clean();
            implementing(
                "public interface I { dump<T extends Clone>(x: &T): void; }",
                "public dump<T extends Clone>(x: &T): void {}",
            )
            .clean();
        },
    );
    h.case("satisfy/param-types: equal parameter types", || {
        let iface = "public interface I { hear(n: i64): void; }";
        let r = implementing(iface, "public hear(n: i32): void {}");
        expect(
            &r,
            &[&format!(
                "EN0416 2:27 `C` does not satisfy `I`: `hear` has another signature {LABEL}"
            )],
        );
        assert_eq!(extras(&r).1, ["`I` declares `hear(n: i64): void`"]);
        let r = implementing(iface, "public hear(n: i64, m: i64): void {}");
        assert_eq!(r.codes(), ["EN0416"], "{}", r.rendered());
        // Parameter names and marks are not compared (N1).
        implementing(iface, "public hear(count: i64): void {}").clean();
        implementing(
            "public interface I { fill(let b: &u8[]): void; }",
            "public fill(b: &u8[]): void {}",
        )
        .clean();
    });
    h.case(
        "satisfy/a `static` method never meets an instance member",
        || {
            let r = implementing(
                "public interface I { make(): i64; }",
                "public static make(): i64 { return 1; }",
            );
            expect(
                &r,
                &[&format!(
                    "EN0416 2:27 `C` does not satisfy `I`: `make` is `static` {LABEL}"
                )],
            );
        },
    );
    h.case("satisfy/return-type: an equal return type", || {
        let iface = "public interface I { speak(): string; }";
        let r = implementing(iface, "public speak(): i64 { return 1; }");
        expect(
            &r,
            &[&format!(
                "EN0416 2:27 `C` does not satisfy `I`: `speak` has another signature {LABEL}"
            )],
        );
        assert_eq!(extras(&r).1, ["`I` declares `speak(): string`"]);
        // `readonly` before the result is a mark, not compared (N1).
        implementing(
            "public interface I { peek(): readonly &string; }",
            "private s: string = \"\"; public peek(): &string { return &this.s; }",
        )
        .clean();
    });
    h.case("satisfy/missing: no member of the name", || {
        let r = implementing("public interface I { speak(): string; }", "");
        expect(
            &r,
            &[&format!(
                "EN0416 2:27 `C` does not satisfy `I`: `speak` is missing {LABEL}"
            )],
        );
        assert_eq!(extras(&r).0, ["1:22 `I.speak` is declared here"]);
    });
    h.case(
        "satisfy/the first member that fails is the one named",
        || {
            let r = implementing(
                "public interface I { a(): void; b(): void; c(): void; }",
                "public a(): void {} private b(): void {}",
            );
            expect(
                &r,
                &[&format!(
                    "EN0416 2:27 `C` does not satisfy `I`: `b` is private {LABEL}"
                )],
            );
        },
    );
    h.case(
        "satisfy/of the methods with the member's signature, one public is enough",
        || {
            implementing(
                "public interface I { m(x: i64): void; }",
                "private m(x: string): void {} public m(x: i64): void {}",
            )
            .clean();
        },
    );
}

fn members(h: &mut Harness) {
    h.case("satisfy/inherited members count; a base's `private` one is unseen", || {
        main_lib("public interface I { speak(): string; }\npublic class Base { public speak(): string { return \"b\"; } }\npublic class C extends Base implements I {}\n").clean();
        let r = main_lib("public interface I { speak(): string; }\npublic class Base { private speak(): string { return \"b\"; } }\npublic class C extends Base implements I {}\n");
        expect(
            &r,
            &[&format!("EN0416 3:40 `C` does not satisfy `I`: `speak` is missing {LABEL}")],
        );
    });
    h.case("satisfy/an abstract class satisfies with an abstract method", || {
        main_lib("public interface I { area(): f64; }\npublic abstract class S implements I { public abstract area(): f64; }\n").clean();
    });
    h.case("satisfy/`Self` is the implementing class", || {
        main_lib("public interface Same { same(other: &Self): bool; }\npublic class C implements Same { public same(other: &C): bool { return true; } }\n").clean();
        let r = main_lib("public interface Same { same(other: &Self): bool; }\npublic class C implements Same { public same(other: &i64): bool { return true; } }\n");
        assert_eq!(
            r.messages(),
            ["`C` does not satisfy `Same`: `same` has another signature"]
        );
        assert_eq!(extras(&r).1, ["`Same` declares `same(other: &C): bool`"]);
        // A subclass inherits `same(other: &C)`, which is not `same(other: &D)`.
        let r = main_lib("public interface Same { same(other: &Self): bool; }\npublic class C { public same(other: &C): bool { return true; } }\npublic class D extends C implements Same {}\n");
        assert_eq!(r.codes(), ["EN0416"], "{}", r.rendered());
    });
    h.case("satisfy/a generic interface at its arguments; a generic class", || {
        main_lib("public interface Get<T> { get(): T; }\npublic class C implements Get<i64> { public get(): i64 { return 1; } }\n").clean();
        let r = main_lib("public interface Get<T> { get(): T; }\npublic class C implements Get<i64> { public get(): string { return \"\"; } }\n");
        expect(
            &r,
            &[&format!("EN0416 2:27 `C` does not satisfy `Get<i64>`: `get` has another signature {LABEL}")],
        );
        main_lib("public interface Get<T> { get(): T; }\npublic class Box2<U> implements Get<U> { private v: U[] = []; public get(): U { unreachable(); } }\n").clean();
    });
    h.case("satisfy/interface-typed parameters match by position and interface", || {
        main_lib("public interface Speaker { speak(): string; }\npublic interface Hearer { hear(s: &Speaker): string; }\npublic class C implements Hearer { public hear(s: &Speaker): string { return s.speak(); } }\n").clean();
        let r = main_lib("public interface Speaker { speak(): string; }\npublic interface Other { other(): string; }\npublic interface Hearer { hear(s: &Speaker): string; }\npublic class C implements Hearer { public hear(s: &Other): string { return s.other(); } }\n");
        assert_eq!(
            r.messages(),
            ["`C` does not satisfy `Hearer`: `hear` has another signature"]
        );
        assert_eq!(extras(&r).1, ["`Hearer` declares `hear(s: &Speaker): string`"]);
    });
    h.case(
        "satisfy/an empty interface is satisfied by anything",
        || {
            main_lib("public interface Marker {}\npublic class C implements Marker {}\n").clean();
        },
    );
}

fn nominal(h: &mut Harness) {
    h.case("satisfy/`Eq`: written, or synthesised with no `equals` (S:640)", || {
        main_lib("public class C implements Eq { public n: i64; }\n").clean();
        main_lib("public class C implements Eq { public equals(other: &C): bool { return true; } }\n").clean();
        let r = main_lib("public class C implements Eq { public equals(other: &i64): bool { return true; } }\n");
        expect(
            &r,
            &[&format!("EN0416 1:27 `C` does not satisfy `Eq`: `equals` has another signature {LABEL}")],
        );
    });
    h.case("satisfy/`Clone`: written, or synthesised unless a destructor stops it", || {
        main_lib("public class C implements Clone { public s: string; }\n").clean();
        main_lib("public class C implements Clone { public destructor() {} public clone(): C { unreachable(); } }\n").clean();
        let r = main_lib("public class C implements Clone { public destructor() {} }\n");
        expect(
            &r,
            &[&format!("EN0416 1:27 `C` does not satisfy `Clone`: `clone` is missing {LABEL}")],
        );
        // A written `clone` wins (S:639) and is checked as any member, inherited
        // ones included.
        let r = main_lib("public class C implements Clone { public s: string; public clone(): i64 { return 1; } }\n");
        expect(
            &r,
            &[&format!("EN0416 1:27 `C` does not satisfy `Clone`: `clone` has another signature {LABEL}")],
        );
        let r = main_lib("public class B { public clone(): B { unreachable(); } }\npublic class C extends B implements Clone {}\n");
        assert_eq!(r.codes(), ["EN0416"], "{}", r.rendered());
        // The library's types keep `is_clone`.
        main_lib("public class C implements Clone { public s: string; public xs: i64[]; public b: Box<i64> | null; }\n").clean();
    });
    h.case("satisfy/`Display`, `Error` and `Ord`", || {
        main_lib("public class C implements Display { public n: i64; }\n").clean();
        main_lib("public class E implements Error { public code: i64; }\n").clean();
        main_lib(
            "public class C implements Ord { public compare(other: &C): i32 { return 0; } }\n",
        )
        .clean();
        let r = main_lib("public class C implements Ord {}\n");
        expect(
            &r,
            &[&format!(
                "EN0416 1:27 `C` does not satisfy `Ord`: `compare` is missing {LABEL}"
            )],
        );
    });
    h.case("satisfy/EN0419: `implements` of a sealed interface (S:650)", || {
        let r = main_lib("import { AtomicValue } from \"core/atomic\";\npublic class C implements AtomicValue {}\n");
        expect(
            &r,
            &["EN0419 2:27 `AtomicValue` is sealed, so `C` can't implement it [a sealed interface]"],
        );
        assert_eq!(
            extras(&r).1,
            ["only the compiler's own list of types implements a sealed interface"]
        );
    });
}

fn shapes(h: &mut Harness) {
    let point = "public interface Point { x: f64; y: f64; }\n";
    h.case("satisfy/a fields-only interface checks public fields (S:629)", move || {
        main_lib(&format!("{point}public class C implements Point {{ public x: f64; public y: f64; public z: f64; }}\n")).clean();
        for (body, reason) in [
            ("public x: f64;", "`y` is missing"),
            ("private x: f64 = 0.0; public y: f64;", "`x` is private"),
            ("protected x: f64; public y: f64;", "`x` is protected"),
            ("public x: i64; public y: f64;", "`x` has another type"),
        ] {
            let r = main_lib(&format!("{point}public class C implements Point {{ {body} }}\n"));
            expect(
                &r,
                &[&format!("EN0416 2:27 `C` does not satisfy `Point`: {reason} {LABEL}")],
            );
        }
        // A base's public field counts.
        main_lib(&format!("{point}public class B {{ public x: f64; }}\npublic class C extends B implements Point {{ public y: f64; }}\n")).clean();
    });
}

fn others(h: &mut Harness) {
    h.case("satisfy/EN0401: `implements` of what is no interface", || {
        let r = main_lib("public class A {}\npublic enum E { X }\npublic class C implements A, E, i64 {}\n");
        expect(
            &r,
            &[
                "EN0401 3:27 mismatched types: expected an interface, found `A` [`implements` takes an interface]",
                "EN0401 3:30 mismatched types: expected an interface, found `E` [`implements` takes an interface]",
                "EN0401 3:33 mismatched types: expected an interface, found `i64` [`implements` takes an interface]",
            ],
        );
    });
    h.case("satisfy/each `implements` of a class is checked", || {
        let r = main_lib("public interface I { a(): void; }\npublic interface J { b(): void; }\npublic class C implements I, J { public a(): void {} }\n");
        expect(
            &r,
            &[&format!("EN0416 3:30 `C` does not satisfy `J`: `b` is missing {LABEL}")],
        );
    });
}

/// Stage 6's review fixes of the clauses.
fn review(h: &mut Harness) {
    h.case(
        "satisfy/a `static` method of the member's signature is reported as `static`, with a label saying so",
        || {
            let r = implementing(
                "public interface I { speak(): string; }",
                "public static speak(): string { return \"s\"; }",
            );
            expect(
                &r,
                &["EN0416 2:27 `C` does not satisfy `I`: `speak` is `static` [required by this `implements`]"],
            );
            let (secondary, notes) = extras(&r);
            assert_eq!(secondary, ["2:45 `C.speak` is `static`, so no value has it"]);
            assert!(notes.is_empty(), "{notes:?}");
        },
    );
    h.case(
        "satisfy/a fields-only interface's field held `private` by a base is missing, by the class itself private (mutant M41)",
        || {
            let r = main_lib(
                "public interface Point { x: f64; y: f64; }
public class A { private x: f64 = 0.0; }
public class B extends A implements Point { public y: f64 = 0.0; }
public class C implements Point { private x: f64 = 0.0; public y: f64 = 0.0; }
",
            );
            expect(
                &r,
                &[
                    "EN0416 3:37 `B` does not satisfy `Point`: `x` is missing [required by this `implements`]",
                    "EN0416 4:27 `C` does not satisfy `Point`: `x` is private [required by this `implements`]",
                ],
            );
        },
    );
}
