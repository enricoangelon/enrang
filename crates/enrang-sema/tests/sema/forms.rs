//! Compiler forms (plan d.17's `forms.rs`; SPEC 6 S:1177-1191, S:1574; owner 4A):
//! `console.log` and `console.error` over any values, `x.toString()`, `panic`,
//! `assert`, `unreachable`, `dispose`, `mem.forget`, `writeTo`, `sizeOf`,
//! `alignOf`, `offsetOf` (EN0303 for a field the type lacks), `cpu.has` (EN0908),
//! each typed into a `Callee::Form` at the type the table gives, with EN0423 for a
//! wrong number of arguments.

use enrang_hir::{Callee, ExprKind, FormKind, StmtKind};
use enrang_target::Feature;
use enrang_testkit::Harness;

use crate::paths::{body, diags, main_lib, ty};
use crate::support::Run;

pub fn register(h: &mut Harness) {
    printing(h);
    control(h);
    sizes(h);
    features(h);
    review(h);
}

/// The form and type of every expression statement and `const` initialiser of
/// `path`'s body, in order.
fn forms(r: &Run, path: &str) -> Vec<(FormKind, String)> {
    body(r, path)
        .root
        .stmts
        .iter()
        .filter_map(|s| match &s.kind {
            StmtKind::Expr(e) | StmtKind::Let { init: Some(e), .. } => Some(e),
            _ => None,
        })
        .filter_map(|e| match &e.kind {
            ExprKind::Call {
                callee: Callee::Form(kind),
                ..
            } => Some((kind.clone(), ty(r, e.ty))),
            _ => None,
        })
        .collect()
}

fn printing(h: &mut Harness) {
    h.case(
        "forms/`console.log` and `console.error` take any values and are `void`",
        || {
            let r = main_lib(
                "public class P { public x: i64 = 0; }
public function f(n: i64, s: &string, p: P, xs: &i64[]): void {
  console.log(n, s, \"x\", p, xs, { a: 1 }, 2.5);
  console.error(n);
  console.log();
}
",
            );
            r.clean();
            assert_eq!(
                forms(&r, "main::f"),
                [
                    (FormKind::ConsoleLog, "void".to_owned()),
                    (FormKind::ConsoleError, "void".to_owned()),
                    (FormKind::ConsoleLog, "void".to_owned()),
                ]
            );
        },
    );
    h.case(
        "forms/another member of `console` is EN0303; `console` itself is not callable",
        || {
            let r = main_lib("public function f(n: i64): void { console.warn(n); console(n); }\n");
            assert_eq!(
                diags(&r),
                [
                    "EN0303 1:43 `console` has no member `warn` [no such member]",
                    "EN0428 1:52 `console` is not callable [a compiler form, called as `console.log(...)` or `console.error(...)`]",
                ]
            );
        },
    );
    h.case(
        "forms/S:1182: `x.toString()` is a `string` from any value; a class's own method wins",
        || {
            let r = main_lib(
                "public class P { public x: i64 = 0; }
public class Q { public toString(): i64 { return 1; } }
public function f(n: i64, p: &P, q: Q, xs: i64[]): void {
  const a = n.toString();
  const b = p.toString();
  const c = xs.toString();
  const d = q.toString();
}
",
            );
            r.clean();
            assert_eq!(
                forms(&r, "main::f"),
                [
                    (FormKind::ToString, "string".to_owned()),
                    (FormKind::ToString, "string".to_owned()),
                    (FormKind::ToString, "string".to_owned()),
                ]
            );
            let d = body(&r, "main::f")
                .root
                .stmts
                .iter()
                .filter_map(|s| match &s.kind {
                    StmtKind::Let { init: Some(e), .. } => Some(e),
                    _ => None,
                })
                .nth(3)
                .expect("`d`");
            assert_eq!(ty(&r, d.ty), "i64");
        },
    );
    h.case("forms/`toString` takes no arguments: EN0423", || {
        let r = main_lib("public function f(n: i64): void { const v = n.toString(3); }\n");
        assert_eq!(
            diags(&r),
            ["EN0423 1:45 `toString` takes no arguments, but 1 was given [too many arguments]"]
        );
    });
    h.case(
        "forms/`writeTo(f, t)`: a `&Formatter` and a text or template, `void`",
        || {
            let r = main_lib(
                "public function w(f: &Formatter, n: i64): void { writeTo(f, `n=${n}`); writeTo(f, \"lit\"); }
public function bad(n: i64): void { writeTo(n, \"x\"); writeTo(); }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0401 2:45 mismatched types: expected `&Formatter`, found `i64` [this is `i64`]",
                    "EN0423 2:54 `writeTo` takes 2 arguments, but none were given [too few arguments]",
                ]
            );
        },
    );
}

fn control(h: &mut Harness) {
    h.case(
        "forms/`panic` and `unreachable` are `never`; `assert` and `dispose` are `void`",
        || {
            let r = main_lib(
                "public class P { public x: i64 = 0; }
public function g(): never { panic(\"x\"); }
public function h(n: i64): i64 { if (n > 0) { panic(`bad ${n}`); } unreachable(); }
public function k(n: i64, p: P, q: P): void { assert(n > 0); assert(n > 0, \"positive\"); dispose(p); mem.forget(q); }
",
            );
            r.clean();
            assert_eq!(forms(&r, "main::g"), [(FormKind::Panic, "never".to_owned())]);
            assert_eq!(
                forms(&r, "main::h"),
                [(FormKind::Unreachable, "never".to_owned())]
            );
            assert_eq!(
                forms(&r, "main::k"),
                [
                    (FormKind::Assert, "void".to_owned()),
                    (FormKind::Assert, "void".to_owned()),
                    (FormKind::Dispose, "void".to_owned()),
                    (FormKind::MemForget, "void".to_owned()),
                ]
            );
        },
    );
    h.case(
        "forms/a message is a `&string` or a template; a condition a `bool`; counts are EN0423",
        || {
            let r = main_lib(
                "public function f(n: i64): void {
  assert(n);
  assert();
  panic(5);
}
public function k(): i64 { unreachable(1); }
public function d(): void { dispose(); }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0203 2:10 a condition must be `bool`, found `i64` [this is `i64`]",
                    "EN0423 3:3 `assert` takes 1 to 2 arguments, but none were given [too few arguments]",
                    "EN0401 4:9 mismatched types: expected `&string`, found `int` [this is `int`]",
                    "EN0423 6:28 `unreachable` takes no arguments, but 1 was given [too many arguments]",
                    "EN0423 7:29 `dispose` takes 1 argument, but none were given [too few arguments]",
                ]
            );
        },
    );
}

fn sizes(h: &mut Harness) {
    h.case(
        "forms/`sizeOf`, `alignOf` and `offsetOf` are `usize`; `offsetOf` finds the field",
        || {
            let r = main_lib(
                "public class P { public x: i64 = 0; public y: i32 = 0; }
public type Q = { a: u8, b: u16 };
public function f(): void {
  const a = sizeOf<P>();
  const b = alignOf<P>();
  const c = offsetOf<P>(\"y\");
  const d = offsetOf<Q>(\"b\");
}
",
            );
            r.clean();
            let got = forms(&r, "main::f");
            assert_eq!(got.len(), 4);
            assert!(got.iter().all(|(_, t)| t == "usize"), "{got:?}");
            assert!(matches!(got[0].0, FormKind::SizeOf(_)));
            assert!(matches!(got[1].0, FormKind::AlignOf(_)));
            assert!(
                matches!(got[2].0, FormKind::OffsetOf(_, idx) if idx.0 == 1),
                "{:?}",
                got[2]
            );
            assert!(matches!(got[3].0, FormKind::OffsetOf(_, idx) if idx.0 == 1));
        },
    );
    h.case(
        "forms/`offsetOf` of a field the type lacks is EN0303",
        || {
            let r = main_lib(
                "public class P { public x: i64 = 0; }
public function f(): void { const d = offsetOf<P>(\"z\"); const e = offsetOf<i64>(\"x\"); }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0303 2:51 `P` has no field `z` [no such field]",
                    "EN0303 2:81 `i64` has no field `x` [no such field]",
                ]
            );
        },
    );
}

fn features(h: &mut Harness) {
    h.case(
        "forms/S:1574: `cpu.has(\"f\")` with a listed literal is a `bool`",
        || {
            let r = main_lib(
                "import { cpu } from \"core\";
public function f(): bool { return cpu.has(\"sse2\") && cpu.has(\"sse4.1\") && cpu.has(\"3dnow\"); }
",
            );
            r.clean();
            let b = body(&r, "main::f");
            let mut seen = Vec::new();
            fn walk(e: &enrang_hir::Expr, seen: &mut Vec<Feature>) {
                match &e.kind {
                    ExprKind::Call {
                        callee: Callee::Form(FormKind::CpuHas(f)),
                        ..
                    } => seen.push(*f),
                    ExprKind::Logical(_, a, b) => {
                        walk(a, seen);
                        walk(b, seen);
                    }
                    _ => {}
                }
            }
            for s in &b.root.stmts {
                if let StmtKind::Return(Some(e)) = &s.kind {
                    walk(e, &mut seen);
                }
            }
            assert_eq!(seen.len(), 3, "{:?}", b.root.stmts);
        },
    );
    h.case(
        "forms/EN0908: a name not in S:1574's list, or no literal at all",
        || {
            let r = main_lib(
                "import { cpu } from \"core\";
public function f(name: &string): void { cpu.has(\"sse9\"); cpu.has(name); }
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0908]: unknown feature name `sse9`
 --> main.en:2:50
  |
2 | public function f(name: &string): void { cpu.has(\"sse9\"); cpu.has(name); }
  |                                                  ^^^^^^ a feature name, written as a string literal
  |
  = explain: run `enrang explain EN0908`

error[EN0908]: a feature name must be a string literal
 --> main.en:2:67
  |
2 | public function f(name: &string): void { cpu.has(\"sse9\"); cpu.has(name); }
  |                                                                   ^^^^ a feature name, written as a string literal
  |
  = explain: run `enrang explain EN0908`

error: aborting due to 2 previous errors
"
            );
        },
    );
}

/// Stage 6's review: `toString` on a `Box` whose class has its own.
fn review(h: &mut Harness) {
    h.case(
        "forms/S:607: `b.toString()` on a `Box<D>` whose `D` declares `toString` calls that member",
        || {
            let r = main_lib(
                "public class D { public x: i64 = 0; public toString(): i64 { return 1; } }
public class E { public x: i64 = 0; }
public function g(): void { const d = new D {}; const t: i64 = d.toString(); const b = new Box(new D {}); const w: i64 = b.toString(); const e = new Box(new E {}); const s: string = e.toString(); }
",
            );
            r.clean();
        },
    );
}
