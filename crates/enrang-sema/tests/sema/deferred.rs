//! Deferred features in expressions (plan d.17; SPEC 16 S:3455-3482; owner 4E):
//! every SPEC 16 name an expression can hold, `Worker` and `spawn` (EN1003), `Math`
//! (EN1026), `JSON` (EN1027), `fetch` and `WebSocket` (EN1028), `Object` and
//! `Reflect` (EN1029), `union` and `transmute` (EN1033), with SPEC 16's head, one
//! note and the row's help, wherever the expression stands (a call, a member's
//! base, a `new`, a value), and only when the name resolves to nothing else.

use enrang_testkit::Harness;

use crate::positions::{check, compiles, renders, shown};

/// `(name, code, a program using the name in an expression)`.
const NAMES: &[(&str, &str, &str)] = &[
    ("Worker", "EN1003", "const w = new Worker();\n"),
    ("spawn", "EN1003", "spawn(1);\n"),
    ("Math", "EN1026", "const x = Math.floor(2.5);\n"),
    ("JSON", "EN1027", "const s = JSON.stringify(1);\n"),
    ("fetch", "EN1028", "fetch(\"https://example.com\");\n"),
    (
        "WebSocket",
        "EN1028",
        "const ws = new WebSocket(\"ws://example.com\");\n",
    ),
    ("Object", "EN1029", "const k = Object.keys(1);\n"),
    ("Reflect", "EN1029", "const v = Reflect.get(1, 2);\n"),
    ("union", "EN1033", "const u = union(1);\n"),
    ("transmute", "EN1033", "const t = transmute(1);\n"),
];

/// SPEC 16's head of each code.
fn head(code: &str) -> &'static str {
    match code {
        "EN1003" => "threads are not supported yet",
        "EN1026" => "`Math` does not exist",
        "EN1027" => "`JSON` is not supported yet",
        "EN1028" => "network APIs are not supported yet",
        "EN1029" => "reflection is not supported yet",
        "EN1033" => "unchecked reinterpretation is not supported yet",
        _ => unreachable!("{code}"),
    }
}

pub fn register(h: &mut Harness) {
    for &(name, code, src) in NAMES {
        h.case(
            format!("deferred/`{name}` in an expression is {code} with SPEC 16's head"),
            move || {
                let r = check(src);
                // `Math` is no deferred feature: Enrang never has it (fix-5).
                let label = match code {
                    "EN1026" => "no such namespace",
                    _ => "not supported yet",
                };
                assert_eq!(
                    shown(&r),
                    [format!("{code} `{name}` {} [{label}]", head(code))],
                    "{}",
                    r.rendered()
                );
                let d = &r.diags[0];
                assert_eq!(d.entries.len(), 1, "one note");
                assert!(d.helps.len() <= 1, "at most one help");
            },
        );
        h.case(
            format!("deferred/`{name}` inside a function body is {code} too"),
            move || {
                let body = src.trim_end().replace('\n', " ");
                let r = check(&format!("private function f(): void {{ {body} }}\n"));
                assert_eq!(r.codes(), [code], "{}", r.rendered());
            },
        );
    }
    rendered(h);
    near_misses(h);
}

/// Each code's note and help, as `enrang check` prints them.
fn rendered(h: &mut Harness) {
    h.case("deferred/EN1003 renders its note and help", || {
        renders(
            "spawn(1);\n",
            "error[EN1003]: threads are not supported yet
 --> main.en:1:1
  |
1 | spawn(1);
  | ^^^^^ not supported yet
  |
  = note: a program runs on one thread; there is no thread or worker to start yet.
help: `Atomic` exists only for interrupt sharing
  = explain: run `enrang explain EN1003`

error: aborting due to 1 previous error
",
        );
    });
    h.case("deferred/EN1026 renders its note and help", || {
        renders(
            "const x = Math.sqrt(2.0);\n",
            "error[EN1026]: `Math` does not exist
 --> main.en:1:11
  |
1 | const x = Math.sqrt(2.0);
  |           ^^^^ no such namespace
  |
  = note: the math functions are methods of the number types, and constants such as `PI` are read through the type's name.
help: `x.sqrt()`, `f64.PI`, `a.max(b)`
  = explain: run `enrang explain EN1026`

error: aborting due to 1 previous error
",
        );
    });
    h.case("deferred/EN1028 at a `new` names the class", || {
        renders(
            "const ws = new WebSocket(\"ws://a\");\n",
            "error[EN1028]: network APIs are not supported yet
 --> main.en:1:16
  |
1 | const ws = new WebSocket(\"ws://a\");
  |                ^^^^^^^^^ not supported yet
  |
  = note: the standard library has no sockets or HTTP yet.
  = explain: run `enrang explain EN1028`

error: aborting due to 1 previous error
",
        );
    });
    h.case("deferred/EN1033 renders its help", || {
        let r = check("const t = transmute(1);\n");
        assert_eq!(
            r.diags[0].helps[0].message,
            "`toBits`, `wrap`, raw-pointer casts in `unsafe`"
        );
    });
    h.case(
        "deferred/one diagnostic per use, each where it is written",
        || {
            let r = check("const a = Math.floor(1.5);\nconst b = Math.ceil(1.5);\n");
            let lines: Vec<u32> = r
                .diags
                .iter()
                .map(|d| r.map.loc(d.primary.span.lo).line)
                .collect();
            assert_eq!(r.codes(), ["EN1026", "EN1026"], "{}", r.rendered());
            assert_eq!(lines, [1, 2]);
        },
    );
}

/// A deferred name the program itself declares is the program's.
fn near_misses(h: &mut Harness) {
    h.case("deferred/a program's own `Math` class wins over SPEC 16", || {
        compiles(
            "const x = Math.half(3.0);\nprivate class Math { public static half(x: f64): f64 { return x / 2.0; } }\n",
        );
    });
    h.case(
        "deferred/a program's own `Worker` class can be built",
        || {
            compiles("const w = new Worker();\nprivate class Worker {}\n");
        },
    );
    h.case(
        "deferred/a local or a parameter named `JSON` or `fetch` wins",
        || {
            compiles(
                "private function f(fetch: i64): i64 { const JSON = 2; return fetch + JSON; }\n",
            );
        },
    );
    h.case("deferred/a member named like a deferred name is no deferred name", || {
        compiles(
            "private class C { public spawn: i64 = 0; public Math(): i64 { return this.spawn; } }\nprivate function f(c: &C): i64 { return c.Math() + c.spawn; }\n",
        );
    });
}
