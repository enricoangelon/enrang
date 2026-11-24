//! Interface types in bodies (plan d.12's `iface.rs`; owner 4C): each interface
//! parameter and each two-word `&I` value stands for a class of its own (EN0401
//! `` `b` may hold another class than `a` ``, S2-09-self, VI-03-swap); C22 records
//! `RefToInterface` and `BoxToInterface` (S2-17-pick, a `Box<string>` included), never
//! for a borrowing class (EN0701) or a `&string` (EN0401 with S:631's two helps,
//! VI-01-part); a by-value interface value, as `b.unbox()` gives, is EN1006 (F7).

use enrang_hir::{Adjust, ExprKind, StmtKind};
use enrang_testkit::Harness;

use crate::paths::{body, diags, init, main_lib, returned};

const SPEAKER: &str = "public interface Speaker { speak(): string; }
public final class Dog implements Speaker { public name: string; public speak(): string { return \"woof\"; } }
";

/// A second class of `SPEAKER`'s interface (VI-03-branches).
const ROBOT: &str = "public final class Robot implements Speaker { public id: i64; public speak(): string { return \"beep\"; } }
";

pub fn register(h: &mut Harness) {
    own_class(h);
    c22(h);
    strings(h);
    by_value(h);
    review(h);
}

fn own_class(h: &mut Harness) {
    h.case(
        "iface/S2-09-self: `Self` of a member called on an interface parameter is its class",
        || {
            let r = main_lib("private function same(a: &Eq, b: &Eq): bool { return a.equals(b); }\n");
            assert_eq!(
                r.rendered(),
                "error[EN0401]: `b` may hold another class than `a`
 --> main.en:1:63
  |
1 | private function same(a: &Eq, b: &Eq): bool { return a.equals(b); }
  |                                                               ^ each interface value stands for a class of its own
  |
help: use one type for both: same<T extends Eq>(a: &T, b: &T)
  = explain: run `enrang explain EN0401`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "iface/VI-03-swap: a by-value interface parameter is a class of its own too",
        || {
            let r = main_lib(&format!(
                "private function swapIn(let s: Speaker, o: Speaker): void {{ s = o; console.log(s.speak()); }}
{SPEAKER}"
            ));
            assert_eq!(
                diags(&r),
                ["EN0401 1:65 `o` may hold another class than `s` [each interface value stands for a class of its own]"]
            );
            assert_eq!(
                r.diags[0].helps[0].message,
                "use one type for both: swapIn<T extends Speaker>(let s: T, o: T)"
            );
        },
    );
    h.case(
        "iface/each read of a two-word `&I` stands for a class of its own (A:894)",
        || {
            let r = main_lib(
                "private function eqs(a: &Eq): void { const l: &Eq = a; const k: bool = l.equals(a); }\n",
            );
            assert_eq!(
                diags(&r),
                ["EN0401 1:81 `a` may hold another class than `l` [each interface value stands for a class of its own]"]
            );
            assert_eq!(
                r.diags[0].helps[0].message,
                "use one type for both, a type parameter `T extends Eq`"
            );
        },
    );
    h.case(
        "iface/a member with no `Self` is called on a two-word `&I` as on any value",
        || {
            let r = main_lib(&format!(
                "private function t(a: &Speaker, b: Box<Speaker>): string {{ const x: &Speaker = a; const y: &Speaker = &*b; return x.speak() + y.speak(); }}
{SPEAKER}"
            ));
            r.clean();
        },
    );
}

fn c22(h: &mut Harness) {
    h.case(
        "iface/C22: `&C` to `&I` records `RefToInterface`, then `WrapNullRef` (S2-17-pick)",
        || {
            let r = main_lib(&format!(
                "private function pick(a: &Speaker, b: &Speaker, first: bool): &Speaker {{ return first ? a : b; }}
private function swap(a: &Speaker, b: &Speaker): void {{ let t: &Speaker = a; t = b; }}
private function intro(d: &Dog): &Speaker {{ return d; }}
private function introN(d: &Dog): &Speaker | null {{ return d; }}
{SPEAKER}"
            ));
            r.clean();
            assert_eq!(
                returned(body(&r, "main::intro")).adjust,
                [Adjust::RefToInterface]
            );
            assert_eq!(
                returned(body(&r, "main::introN")).adjust,
                [Adjust::RefToInterface, Adjust::WrapNullRef]
            );
            let ExprKind::Ternary(_, a, b) = &returned(body(&r, "main::pick")).kind else {
                panic!("a ternary");
            };
            assert_eq!(a.adjust, [Adjust::RefToInterface]);
            assert_eq!(b.adjust, [Adjust::RefToInterface]);
            assert_eq!(
                init(body(&r, "main::swap"), 0).adjust,
                [Adjust::RefToInterface]
            );
        },
    );
    h.case(
        "iface/C22: `Box<C>` to `Box<I>` records `BoxToInterface`, a `Box<string>` included",
        || {
            let r = main_lib(&format!(
                "private function bx(d: Box<Dog>): Box<Speaker> {{ return d; }}
private function bs(s: Box<string>): Box<Measured> {{ return s; }}
public interface Measured {{ length(): isize; }}
{SPEAKER}"
            ));
            r.clean();
            for f in ["bx", "bs"] {
                assert_eq!(
                    returned(body(&r, &format!("main::{f}"))).adjust,
                    [Adjust::BoxToInterface],
                    "{f}"
                );
            }
        },
    );
    h.case(
        "iface/EN0701: a borrowing class never becomes an interface value (S:631)",
        || {
            let r = main_lib(
                "private function v(view: &View): &Speaker { return view; }
public interface Speaker { speak(): string; }
public final class View implements Speaker { private s: &string; public constructor(s: &string) { this.s = s; } public speak(): string { return \"v\"; } }
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0701]: a `Speaker` can't hold a `View`, because `View` holds a reference
 --> main.en:1:52
  |
1 | private function v(view: &View): &Speaker { return view; }
  |                                                    ^^^^ `View` holds a reference
  |
  = note: an interface declares no loans and no stores, so only a value type becomes one
  = explain: run `enrang explain EN0701`

error: aborting due to 1 previous error
"
            );
        },
    );
}

fn strings(h: &mut Harness) {
    h.case(
        "iface/VI-01-part: a part of a string never becomes an `&I`, with S:631's two helps",
        || {
            let r = main_lib(
                "const s: string = \"hello\";
const m: &Measured = s.slice(1, 3);
public interface Measured { length(): isize; }
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0401]: a `&string` can't become a `&Measured`, because it may be a part of a string
 --> main.en:2:22
  |
2 | const m: &Measured = s.slice(1, 3);
  |                      ^^^^^^^^^^^^^ this is a `&string`
  |
help: take <T extends Measured>(m: &T)
help: or keep a copy: s.slice(1, 3).toString()
  = explain: run `enrang explain EN0401`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "iface/VI-01-part: a whole string, a parameter and a literal are each EN0401 too",
        || {
            let r = main_lib(
                "let s: string = \"hello\";
const w: &Measured = &s;
private function p(t: &string): &Measured { return t; }
private function l(): void { const m: &Measured = \"lit\"; }
public interface Measured { length(): isize; }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0401 2:22 a `&string` can't become a `&Measured`, because it may be a part of a string [this is a `&string`]",
                    "EN0401 3:52 a `&string` can't become a `&Measured`, because it may be a part of a string [this is a `&string`]",
                    "EN0401 4:51 a `&string` can't become a `&Measured`, because it may be a part of a string [this is a `&string`]",
                ]
            );
            let helps: Vec<&str> = r.diags[0].helps.iter().map(|h| h.message.as_str()).collect();
            assert_eq!(
                helps,
                ["take <T extends Measured>(m: &T)", "or keep a copy: s.toString()"]
            );
        },
    );
}

fn by_value(h: &mut Harness) {
    h.case(
        "iface/F7: `b.unbox()` on a `Box<Speaker>` is EN1006 (T:862)",
        || {
            let r = main_lib(&format!(
                "private function un(b: Box<Speaker>): void {{ b.unbox(); }}\n{SPEAKER}"
            ));
            assert_eq!(
                r.rendered(),
                "error[EN1006]: an interface type by value outside a parameter is not supported yet
 --> main.en:1:46
  |
1 | private function un(b: Box<Speaker>): void { b.unbox(); }
  |                                              ^^^^^^^^^ this is a `Speaker` by value
  |
  = note: `Speaker` is an interface, so the size of `b.unbox()` isn't known
help: `&Speaker` to refer to one, `Box<Speaker>` to own one
  = explain: run `enrang explain EN1006`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "iface/a by-value interface value meeting a site of another type, or dropped by `void`, is EN1006",
        || {
            let r = main_lib(&format!(
                "private function un(b: Box<Speaker>): void {{ const r: &Speaker = b.unbox(); }}
private function vo(b: Box<Speaker>): void {{ void b.unbox(); }}
{SPEAKER}"
            ));
            assert_eq!(
                diags(&r),
                [
                    "EN1006 1:66 an interface type by value outside a parameter is not supported yet [this is a `Speaker` by value]",
                    "EN1006 2:51 an interface type by value outside a parameter is not supported yet [this is a `Speaker` by value]",
                ]
            );
        },
    );
    h.case(
        "iface/VI-03-branches: a branch argument of mixed classes at a by-value `I` is EN1006",
        || {
            let r = main_lib(&format!(
                "private function relay(x: Speaker): void {{ console.log(x.speak()); }}
private function a(c: bool, d: Dog, r: Robot): void {{ relay(c ? d : r); }}
private function b(c: bool, s: Speaker, o: Speaker): void {{ relay(c ? s : o); }}
private function m(k: i64, d: Dog, r: Robot): void {{ relay(match (k) {{ 0 => d, default => r }}); }}
private function n(d: Dog | null, r: Robot): void {{ relay(d ?? r); }}
private function e(c: bool, d: Dog, f: Dog): void {{ relay(c ? d : f); }}
{SPEAKER}{ROBOT}"
            ));
            let head = "an interface type by value outside a parameter is not supported yet";
            assert_eq!(
                diags(&r),
                [
                    format!("EN1006 2:61 {head} [its branches may hold different classes]"),
                    format!("EN1006 3:67 {head} [its branches may hold different classes]"),
                    format!("EN1006 4:60 {head} [its branches may hold different classes]"),
                    format!("EN1006 5:59 {head} [its branches may hold different classes]"),
                ]
            );
            let notes: Vec<&str> = r
                .diags
                .iter()
                .map(|d| d.entries[0].text.as_str())
                .collect();
            assert_eq!(
                notes,
                [
                    "this `Speaker` may be a `Dog` or a `Robot`, so its class isn't known",
                    "this `Speaker` may be the class of `s` or the class of `o`, so its class isn't known",
                    "this `Speaker` may be a `Dog` or a `Robot`, so its class isn't known",
                    "this `Speaker` may be a `Dog` or a `Robot`, so its class isn't known",
                ]
            );
            assert!(
                r.diags
                    .iter()
                    .all(|d| d.helps[0].message == "call relay in each branch")
            );
        },
    );
    h.case(
        "iface/S2-10-swap: a type parameter standing for `*b` of a `Box<I>` is EN1006",
        || {
            let r = main_lib(&format!(
                "private function sw(a: Box<Speaker>, b: Box<Speaker>): void {{ mem.swap(&*a, &*b); }}
private function sh(a: Box<Speaker>): void {{ show(&*a); }}
private function ok(let a: Box<Speaker>, let b: Box<Speaker>): void {{ mem.swap(&a, &b); show(&a); }}
public function show<T>(x: &T): void {{ console.log(x); }}
{SPEAKER}"
            ));
            let head = "an interface type by value outside a parameter is not supported yet";
            assert_eq!(
                diags(&r),
                [
                    format!("EN1006 1:72 {head} [`*a` is a `Speaker` by value]"),
                    format!("EN1006 2:51 {head} [`*a` is a `Speaker` by value]"),
                ]
            );
            assert_eq!(
                r.diags[0].entries[0].text,
                "`Speaker` is an interface, so the size of `*a` isn't known"
            );
            assert_eq!(r.diags[0].helps[0].message, "swap the boxes: mem.swap(&a, &b)");
            assert_eq!(r.diags[1].helps[0].message, "show(&a)");
        },
    );
    h.case(
        "iface/a by-value interface at a by-value interface parameter is EN1006 (S:631)",
        || {
            let r = main_lib(&format!(
                "private function relay(x: Speaker): void {{ console.log(x.speak()); }}
private function u(b: Box<Speaker>): void {{ relay(b.unbox()); }}
private function w(b: &Speaker): void {{ look(b); }}
private function look(x: &Speaker): void {{ console.log(x.speak()); }}
{SPEAKER}"
            ));
            assert_eq!(
                diags(&r),
                ["EN1006 2:51 an interface type by value outside a parameter is not supported yet [this is a `Speaker` by value]"]
            );
            assert_eq!(
                r.diags[0].entries[0].text,
                "`Speaker` is an interface, so the size of `b.unbox()` isn't known"
            );
        },
    );
    h.case(
        "iface/an `&I` taken out of a `Box<I>` is two words and compiles (F7)",
        || {
            let r = main_lib(&format!(
                "private function d(b: Box<Speaker>): string {{ const r: &Speaker = &*b; return r.speak(); }}\n{SPEAKER}"
            ));
            r.clean();
            let b = body(&r, "main::d");
            assert!(matches!(b.root.stmts[0].kind, StmtKind::Let { .. }));
        },
    );
}

/// Stage 6's review: one EN1006 help, and C22 needs a bound.
fn review(h: &mut Harness) {
    h.case(
        "iface/SPEC 16: every EN1006 in one run carries the row's help",
        || {
            let r = main_lib(
                "public interface Speaker { speak(): string; }
public function a(b: Box<Speaker>): void { b.unbox(); const s = b.unbox(); }
",
            );
            let helps: Vec<&str> = r
                .diags
                .iter()
                .map(|d| d.helps[0].message.as_str())
                .collect();
            assert_eq!(
                helps,
                [
                    "`&Speaker` to refer to one, `Box<Speaker>` to own one",
                    "`&Speaker` to refer to one, `Box<Speaker>` to own one",
                ],
                "{}",
                r.rendered()
            );
        },
    );
    h.case(
        "iface/C22: an unbounded `&T` never becomes an `&I`; a bounded one does (mutant M37)",
        || {
            let r = main_lib(
                "public interface Speaker { speak(): string; }
public function f<T>(x: &T): void { const s: &Speaker = x; }
public function g<T extends Speaker>(x: &T): void { const s: &Speaker = x; }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0401 2:57 mismatched types: expected `&Speaker`, found `&T` [this is `&T`]"]
            );
        },
    );
}
