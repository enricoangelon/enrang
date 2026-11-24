//! Stage 3's programs (M3 plan g.1): what turning phase 3 on for every `check`
//! found in the M2 corpus, each pinned here where it was fixed. A logical
//! operator stores a `const` once on each path; a tag read after a payload's part
//! moved out is shallow; the verifier takes a safe `fn` where an `unsafe fn` is due
//! and an object or class where C20 takes a shape; a failed `?` among a program's
//! statements prints the error and makes the status 1.

use enrang_testkit::Harness;

use crate::support::{build, phase3};

/// Programs phase 3 must accept, as the M2 fixtures and pages they come from do.
const CLEAN: &[(&str, &str)] = &[
    (
        "`&&` and `||` into a `const` (EN0106, EN0107, EN0203, EN0908 near-misses)",
        "let x = true;\nlet y = false;\nconst s: bool | null = null;\nconst a = x && y;\nconst o = x || y;\nconst n = (s ?? false) || (o && x);\nconsole.log(a, o, n);\n",
    ),
    (
        "a tag read after a part of the payload moved out (EN0506's fixed example)",
        "const found = find(\"ada\");
if (found != null) {
  const { name, age } = found;
  console.log(name, age);
}

private function find(name: &string): Person | null {
  if (name == \"ada\") { return new Person { name: \"Ada\", age: 36 }; }
  return null;
}

private class Person {
  public name: string;
  public age: i64;
}
",
    ),
    (
        "a safe `fn` value where an `unsafe fn` is due (C15)",
        "const f: fn() => void = tick;\nconst h: unsafe fn() => void = f;\nunsafe { h(); }\n\nprivate function tick(): void { console.log(\"tick\"); }\n",
    ),
    (
        "an object and a class where a shape is due (C20)",
        "const p = { name: \"Ada\", age: 36 };
const u = new User { name: \"Ada\", age: 36 };
const q: &{ name: string } = &p;
const r: &{ name: string } = &u;
console.log(q.name, r.name);
console.log(nameOf(u));

public function nameOf(x: { name: string }): string { return x.name.clone(); }

public class User {
  public name: string;
  public age: i64;
}
",
    ),
    (
        "a failed `?` among a program's statements (S7)",
        "sumAges(\"1\", \"-1\")?;\nconsole.log(\"not reached\");\n\nprivate function sumAges(a: &string, b: &string): Result<i64> {\n  if (a == b) { return Err(\"same\"); }\n  return 1;\n}\n",
    ),
];

/// The programs phase 3 must accept, by case name: hosts of `mutants`' violations
/// (TESTING 14).
pub fn accepted() -> Vec<(String, String)> {
    (CLEAN.iter())
        .map(|&(name, source)| (format!("integrate/{name}"), source.to_owned()))
        .collect()
}

pub fn register(h: &mut Harness) {
    for &(name, source) in CLEAN {
        h.case(format!("integrate/{name}: phase 3 accepts it"), move || {
            assert_eq!(phase3(source), Vec::<(String, u32)>::new());
        });
    }
    h.case(
        "integrate/a logical operator stores its destination once on each path",
        || {
            let text = build("let x = true;\nconst a = x && false;\nconsole.log(a);\n").text();
            let stores = text
                .lines()
                .filter(|l| l.trim_start().starts_with("_3 = "))
                .count();
            assert_eq!(stores, 2, "{text}");
            assert!(text.contains("_3 = copy _4;"), "{text}");
        },
    );
    h.case(
        "integrate/a failed `?` among the statements prints the error and exits 1",
        || {
            let source = "f()?;\n\nprivate function f(): Result<i64> { return 1; }\n";
            let text = build(source).text();
            assert!(
                text.contains("form error(const \"error: \": &string, move "),
                "{text}"
            );
            assert!(text.contains("_0 = const 1: int;"), "{text}");
        },
    );
}
