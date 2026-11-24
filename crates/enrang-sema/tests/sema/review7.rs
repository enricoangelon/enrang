//! The seventh review-fix stage's cases (`fix-7`, the M2 gate's findings), each
//! named after the area it checks: C13 at `??` through a variable bound to
//! `string` (S:752), EN0402's `as` fix-it on a compound operand (S:502), EN1015's
//! narrowing help (S:739), EN0420's label and helps, EN0441's receiver, the
//! truthiness habit's recovery (S:741), EN0303's `?.` only where it checks
//! (S:607), and a matcher's value against the actual (SPEC 12.2). A help with
//! edits is applied, and the fixed program must check clean.

use enrang_diag::{Applicability, Edit, apply_fixes};
use enrang_sema::LibSource;
use enrang_testkit::Harness;

use crate::paths::{diags, main_lib};
use crate::support::{Run, run_with};

pub fn register(h: &mut Harness) {
    coalesce(h);
    widen(h);
    for_of(h);
    not_numbers(h);
    length(h);
    truthiness(h);
    optional(h);
    matchers(h);
}

/// The help messages of every diagnostic of `r`, in order.
fn all_helps(r: &Run) -> Vec<String> {
    r.diags
        .iter()
        .flat_map(|d| d.helps.iter().map(|h| h.message.clone()))
        .collect()
}

/// `main.en` of `r` with `edits` applied.
fn applied(r: &Run, edits: &[Edit]) -> String {
    let file = r.map.file_of(edits[0].span.lo);
    apply_fixes(&file.text, file.start, edits).expect("the edits apply")
}

/// The edits of help `n` of the only diagnostic of `r`, applied to `main.en`, which
/// must then check clean.
fn fixed_checks(r: &Run, n: usize) -> String {
    assert_eq!(r.diags.len(), 1, "{}", r.rendered());
    let help = &r.diags[0].helps[n];
    assert!(!help.edits.is_empty(), "{}", r.rendered());
    let fixed = applied(r, &help.edits);
    main_lib(&fixed).clean();
    fixed
}

fn coalesce(h: &mut Harness) {
    h.case(
        "typeck/fix-7: a text after `??` on a `&T | null` whose `T` became `string` is its descriptor (C13, S:752)",
        || {
            // `find` on an array whose element type is inferred from texts.
            main_lib(
                "const names = [\"ann\", \"bob\"];
const b = names.find(n => n.startsWith(\"b\")) ?? \"nobody\";
console.log(b);
",
            )
            .clean();
            // A generic `&T | null` result, plain and with a bound.
            main_lib(
                "const words: string[] = [\"a\", \"b\"];
const w = first(&words);
const x: &string = w ?? \"none\";
const m = maxOf(&words) ?? \"none\";
console.log(x, m);
private function first<T>(xs: &T[]): &T | null { return xs.first(); }
private function maxOf<T extends Ord>(xs: &T[]): &T | null { return xs.first(); }
",
            )
            .clean();
            // A payload that is no string still refuses a text, and a number.
            let r = main_lib(
                "const names = [\"ann\"];
const k = names.find(n => n.startsWith(\"b\")) ?? 5;
const ns = [1, 2];
const j = ns.find(n => n > 1) ?? \"none\";
",
            );
            assert_eq!(r.codes(), ["EN0401", "EN0401"], "{}", r.rendered());
        },
    );
}

fn widen(h: &mut Harness) {
    h.case(
        "ops/fix-7: EN0402's `as` fix-it parenthesises an operand `as` would split (S:502)",
        || {
            let rows = [
                // The user's own parentheses are kept, inside the conversion's.
                (
                    "public function avg(total: i64, xs: &i64[]): i64 {\n  return total / (xs.length() - 1);\n}\n",
                    "convert it, which never fails: `((xs.length() - 1) as i64)`",
                    "  return total / ((xs.length() - 1) as i64);",
                ),
                // An operand with none gets them.
                (
                    "public function g(total: i64, n: isize): i64 {\n  return total + n * 2;\n}\n",
                    "convert it, which never fails: `((n * 2) as i64)`",
                    "  return total + ((n * 2) as i64);",
                ),
                // A name, a call and a prefix operator bind tighter than `as`.
                (
                    "public function k(total: i64, n: isize): i64 {\n  return total + n;\n}\n",
                    "convert it, which never fails: `(n as i64)`",
                    "  return total + (n as i64);",
                ),
                (
                    "public function m(total: i64, xs: &i64[]): i64 {\n  return total - xs.length();\n}\n",
                    "convert it, which never fails: `(xs.length() as i64)`",
                    "  return total - (xs.length() as i64);",
                ),
                (
                    "public function p(total: i64, n: isize): i64 {\n  return total - -n;\n}\n",
                    "convert it, which never fails: `(-n as i64)`",
                    "  return total - (-n as i64);",
                ),
            ];
            for (source, message, line) in rows {
                let r = main_lib(source);
                assert_eq!(r.codes(), ["EN0402"], "{}", r.rendered());
                let help = &r.diags[0].helps[0];
                assert_eq!(help.message, message);
                assert_eq!(help.applicability, Applicability::MachineApplicable);
                let fixed = fixed_checks(&r, 0);
                assert_eq!(fixed.lines().nth(1), Some(line), "{fixed}");
            }
        },
    );
}

fn for_of(h: &mut Harness) {
    h.case(
        "forof/fix-7: EN1015's narrowing help names the source without its `&` (S:739)",
        || {
            let r = main_lib(
                "public function f(tags: string[] | null): void {
  for (const t of &tags) { console.log(t); }
}
public function g(p: P): void {
  for (const t of &p.tags) { console.log(t); }
}
public function k(tags: string[] | null): void {
  for (const t of &(tags)) { console.log(t); }
}
public class P { public tags: string[] | null = null; }
",
            );
            assert_eq!(
                r.codes(),
                ["EN1015", "EN1015", "EN1015"],
                "{}",
                r.rendered()
            );
            assert_eq!(
                all_helps(&r),
                [
                    "narrow it first: `if (tags != null) { ... }`",
                    "narrow it first: `if (p.tags != null) { ... }`",
                    "narrow it first: `if (tags != null) { ... }`",
                ]
            );
            let notes: Vec<&str> = r
                .diags
                .iter()
                .flat_map(|d| d.entries.iter().map(|e| e.text.as_str()))
                .collect();
            assert_eq!(
                notes,
                [
                    "`tags` may be `null`, and a loop needs the array itself",
                    "`p.tags` may be `null`, and a loop needs the array itself",
                    "`tags` may be `null`, and a loop needs the array itself",
                ]
            );
            // The help followed checks clean.
            main_lib(
                "public function f(tags: string[] | null): void {
  if (tags != null) { for (const t of &tags) { console.log(t); } }
}
public function g(p: P): void {
  if (p.tags != null) { for (const t of &p.tags) { console.log(t); } }
}
public class P { public tags: string[] | null = null; }
",
            )
            .clean();
        },
    );
}

fn not_numbers(h: &mut Harness) {
    h.case(
        "ops/fix-7: EN0420 marks the operand that is no number, with a default or a template (S:1131)",
        || {
            let nullable = main_lib(
                "public function f(a: i64 | null, b: i64): i64 { const x = b + a; return x; }\n",
            );
            assert_eq!(
                diags(&nullable),
                ["EN0420 1:63 `+` needs numbers, found `i64 | null` [this is `i64 | null`]"]
            );
            assert_eq!(
                all_helps(&nullable),
                [
                    "give it a default for `null`: `(a ?? 0)`",
                    "or narrow it first: `if (a != null) { ... }`",
                ]
            );
            fixed_checks(&nullable, 0);
            let float = main_lib("public function h(r: f64 | null): f64 { return r * 2.0; }\n");
            assert_eq!(
                all_helps(&float)[0],
                "give it a default for `null`: `(r ?? 0.0)`"
            );
            fixed_checks(&float, 0);
            // A call is no path: a default, and no narrowing.
            let call = main_lib(
                "public function k(): i64 { return 1 + m(); }\nprivate function m(): i64 | null { return null; }\n",
            );
            assert_eq!(
                all_helps(&call),
                ["give it a default for `null`: `(m() ?? 0)`"]
            );
            let text = main_lib(
                "public function g(count: i64): string { const msg = \"items: \" + count; return msg; }\n",
            );
            assert_eq!(
                diags(&text),
                ["EN0420 1:53 `+` needs two numbers or two strings, found `string` and `i64` [this is `string`]"]
            );
            assert_eq!(text.diags[0].secondary.len(), 1);
            assert_eq!(text.diags[0].secondary[0].text, "this is `i64`");
            assert_eq!(
                all_helps(&text),
                ["use a template, which formats the number"]
            );
            let fixed = fixed_checks(&text, 0);
            assert!(fixed.contains("const msg = `items: ${count}`;"), "{fixed}");
            // The number first, and a text with an escape kept as a hole.
            let first = main_lib(
                "public function g(n: i64): string { return n + \" left\"; }\n",
            );
            assert!(fixed_checks(&first, 0).contains("return `${n} left`;"));
            let escaped = main_lib(
                "public function g(n: i64): string { return \"a\\tb\" + n; }\n",
            );
            assert!(fixed_checks(&escaped, 0).contains("return `${\"a\\tb\"}${n}`;"));
            // A `bool` operand is marked, with no help.
            let flag = main_lib("const yes = true;\nconsole.log(yes + 1);\n");
            assert_eq!(
                diags(&flag),
                ["EN0420 2:13 `+` needs numbers, found `bool` [this is `bool`]"]
            );
            assert!(all_helps(&flag).is_empty());
        },
    );
}

fn length(h: &mut Harness) {
    h.case(
        "member/fix-7: EN0441 names the receiver's type as far as it is known, never `_`",
        || {
            let r = main_lib(
                "const names = [\"ann\", \"bo\"];
for (let i = 0; i < names.length; i++) { console.log(names[i]); }
const nums = [1, 2];
console.log(nums.length);
const s = names[0];
console.log(s.length);
",
            );
            assert_eq!(
                r.messages(),
                [
                    "`length` is a method on `string[]`",
                    "`length` is a method on `int[]`",
                    "`length` is a method on `string`",
                ]
            );
            assert_eq!(
                all_helps(&r)[2],
                "`s.length()` counts bytes; `s.charCount()` counts characters"
            );
        },
    );
}

fn truthiness(h: &mut Harness) {
    h.case(
        "narrow/fix-7: a nullable reported as a condition (EN0203) narrows as its help reads (S:741)",
        || {
            let r = main_lib(
                "const user = findUser(3);
if (user) { console.log(user.name); }
if (!user) { console.log(\"none\"); } else { console.log(user.name); }
while (user && user.name == \"a\") { break; }
console.log(user.name);
private class User { public constructor(public name: string) {} }
private function findUser(id: i64): User | null { return id == 1 ? new User(\"a\") : null; }
",
            );
            // One EN0203 per mistake, no EN0303 where the help's test would narrow,
            // and the EN0303 of a use no test covers is still there.
            assert_eq!(
                r.codes(),
                ["EN0203", "EN0203", "EN0203", "EN0303"],
                "{}",
                r.rendered()
            );
            assert_eq!(diags(&r)[3], "EN0303 5:18 `User | null` has no member `name` [this value may be `null`]");
            assert_eq!(all_helps(&r)[0], "test it: `user != null`");
            // A number as a condition still recovers as an error, not a test.
            let n = main_lib("const n = 3;\nif (n) { console.log(n); }\n");
            assert_eq!(n.codes(), ["EN0203"]);
        },
    );
}

fn optional(h: &mut Harness) {
    h.case(
        "member/fix-7: EN0303 offers `?.` only where a `null` in the chain's place still checks (S:607)",
        || {
            let r = main_lib(
                "public function a(addr: Addr): void { if (addr.zip.length() > 0) { console.log(\"z\"); } }
public function b(s: string | null): string { return s.toUpperCase(); }
public function c(): isize { return find().name.length(); }
public function d(u: User | null): isize { return (u.name).length() + 1; }
public function e(u: User | null): isize { return -u.age; }
public function g(u: User | null): void { u.name.length(); }
public function h(u: User | null): string | null { return u.name; }
private function find(): User | null { return null; }
public class Addr { public zip: string | null = null; }
public class User { public name: string = \"\"; public age: isize = 0; }
",
            );
            assert_eq!(r.codes(), ["EN0303"; 7], "{}", r.rendered());
            assert_eq!(
                all_helps(&r),
                [
                    "narrow it first: `if (addr.zip != null) { ... }`",
                    "narrow it first: `if (s != null) { ... }`",
                    "keep it in a constant and narrow that: `const v = find(); if (v != null) { ... }`",
                    "narrow it first: `if (u != null) { ... }`",
                    "narrow it first: `if (u != null) { ... }`",
                    // A receiver of `.`: `u?.name.length()` would miss `length`.
                    "narrow it first: `if (u != null) { ... }`",
                    // `u?.name` is a `&string | null`, no `string | null`.
                    "narrow it first: `if (u != null) { ... }`",
                ]
            );
            // Where `null` may stand, the `?.` comes first, and applied it checks.
            for (source, help) in [
                (
                    "public function b(u: User | null): void { u.greet(); }\npublic class User { public greet(): void {} }\n",
                    "use `?.greet`, which reads it only when the value is not `null`",
                ),
                (
                    "public function c(u: User | null): void { console.log(u.name); }\npublic class User { public name: string = \"\"; }\n",
                    "use `?.name`, which reads it only when the value is not `null`",
                ),
                (
                    "public function d(u: User | null): void { const n = u.name; console.log(n); }\npublic class User { public name: string = \"\"; }\n",
                    "use `?.name`, which reads it only when the value is not `null`",
                ),
                (
                    "public function f(u: User | null): i64 | null { return u.age; }\npublic class User { public age: i64 = 0; }\n",
                    "use `?.age`, which reads it only when the value is not `null`",
                ),
                (
                    "public function h(u: User | null): string | null { return u.shout(); }\npublic class User { public shout(): string { return \"A\"; } }\n",
                    "use `?.shout`, which reads it only when the value is not `null`",
                ),
                (
                    "public function g(u: User | null): void { u.name?.length(); }\npublic class User { public name: string = \"\"; }\n",
                    "use `?.name`, which reads it only when the value is not `null`",
                ),
            ] {
                let r = main_lib(source);
                assert_eq!(all_helps(&r)[0], help, "{}", r.rendered());
                assert_eq!(
                    all_helps(&r)[1],
                    "or narrow it first: `if (u != null) { ... }`"
                );
                fixed_checks(&r, 0);
            }
        },
    );
}

fn matchers(h: &mut Harness) {
    h.case(
        "stmt/fix-7: a matcher's value of another type than the actual is EN0401 (SPEC 12.2)",
        || {
            let module = "private function discount(total: i64, percent: i64): i64 { return total - total * percent / 100; }
private function names(): string[] { return [\"ann\", \"bob\"]; }
private function greet(n: &string): string { return `hi ${n}`; }
private function maybe(x: i64): i64 | null { return x > 0 ? x : null; }
private function half(x: f64): f64 { return x / 2.0; }
";
            let test = |body: &str| {
                run_with(
                    &[
                        ("cart.en", module),
                        ("cart.test.en", &format!("test(\"t\", () => {{\n{body}}});\n")),
                    ],
                    LibSource::Embedded,
                    "x86_64-linux",
                )
            };
            let r = test(
                "  expect(discount(1000, 10)).toBe(\"900\");
  expect(names().length()).toBeGreaterThan(\"1\");
  expect(greet(\"Ada\")).not.toBe(3);
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0401 2:35 mismatched types: expected `i64`, found `string` [this is `string`]",
                    "EN0401 3:44 mismatched types: expected `isize`, found `string` [this is `string`]",
                    "EN0401 4:33 mismatched types: expected `string`, found `int` [this is `int`]",
                ]
            );
            assert_eq!(
                r.diags[0].secondary[0].text,
                "`toBe` compares it with this `i64`"
            );
            // What peels, adapts or compares by value checks clean.
            test(
                "  const ns = names();
  expect(ns.find(n => n.startsWith(\"b\"))).toBe(\"bob\");
  expect(greet(\"Ada\")).toBe(\"hi Ada\");
  const who: &string = \"hi Ada\";
  expect(greet(\"Ada\")).toBe(who);
  expect(half(3.0)).toBe(1.5);
  expect(half(2.0)).toBe(1);
  expect(maybe(2)).toBe(2);
  expect(maybe(0)).toBe(null);
  expect(ns.length()).toBe(2);
  const n: i64 = 1;
  expect(ns.length()).toBeGreaterThan(n);
  expect(discount(1000, 10)).not.toBe(899);
",
            )
            .clean();
        },
    );
}
