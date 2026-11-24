//! The typing engine (owner 3A; plan d.5-d.7, g.2 "Types, coercions, numerics"):
//! inference and its defaults, literals, operators, casts, the coercion table as
//! `Adjust` chains, arrays and spreads, `match`, statements and missing returns.
//!
//! Each case is a program run through `load` and `analyze` with the suite's fake
//! library; a rejecting case checks the exact code, primary line and column and
//! message (and labels, notes and helps where the plan gives them), an accepting
//! one that nothing is reported and, where the rule is about HIR, the typed body:
//! the `adjust` vector of a coercion site, a literal's constant at its final type, a
//! cast's kind, a `match`'s arm values. Calls are 3B's, so the coercion chains of
//! A:888 are checked at initialisers, which are coercion sites as arguments are.
//! G22 is checked byte for byte against SPEC's block, with the embedded library.

#[path = "../../src/passes/walk.rs"]
mod walk;

use std::sync::Arc;

use enrang_hir::{
    Adjust, ArmValue, Body, CastKind, ConstValue, Expr, ExprKind, LocalKind, LoopId, StmtKind,
    TopVar, Ty, TyKind, VariantIdx,
};
use enrang_sema::LibSource;
use enrang_testkit::{Harness, extract_cases, line_diff, workspace_root};

use crate::support::{Run, run, run_with};

pub fn register(h: &mut Harness) {
    inference(h);
    literals(h);
    operators(h);
    comparisons(h);
    casts(h);
    coercions(h);
    references(h);
    arrays(h);
    spreads(h);
    matches(h);
    statements(h);
    bodies(h);
    reachability(h);
    deferred_numerics(h);
    constant_order(h);
    literal_references(h);
    arm_names(h);
    deferred_casts(h);
    shape_parameters(h);
    places(h);
    bare_returns(h);
    pinned(h);
    g22(h);
}

// ---------------------------------------------------------------------------------
// Helpers.

/// Checks `src` as `src/main.en`.
fn check(src: &str) -> Run {
    run(&[("src/main.en", src)])
}

/// The one diagnostic `src` gives: its code, `line:col` of its primary span, and
/// message.
fn one(src: &str) -> (String, String, String) {
    let r = check(src);
    assert_eq!(r.diags.len(), 1, "{}", r.rendered());
    let d = &r.diags[0];
    let loc = r.map.loc(d.primary.span.lo);
    (
        d.code.name().to_owned(),
        format!("{}:{}", loc.line, loc.col),
        d.message.clone(),
    )
}

/// Asserts `src` gives exactly one diagnostic, `code` at `at` (`line:col`) with
/// `message`.
fn rejects(src: &str, code: &str, at: &str, message: &str) {
    let (c, a, m) = one(src);
    assert_eq!(
        (c.as_str(), a.as_str(), m.as_str()),
        (code, at, message),
        "{src}"
    );
}

/// Every diagnostic of `src`: its code, `line:col` of its primary span, and
/// message, in order.
fn all(src: &str) -> Vec<(String, String, String)> {
    let r = check(src);
    r.diags
        .iter()
        .map(|d| {
            let loc = r.map.loc(d.primary.span.lo);
            (
                d.code.name().to_owned(),
                format!("{}:{}", loc.line, loc.col),
                d.message.clone(),
            )
        })
        .collect()
}

/// `(code, at, message)` as [`all`] gives it.
fn diag(code: &str, at: &str, message: &str) -> (String, String, String) {
    (code.to_owned(), at.to_owned(), message.to_owned())
}

/// Asserts `src` checks clean and returns the run.
fn accepts(src: &str) -> Run {
    let r = check(src);
    r.clean();
    r
}

/// The body of function `name` of `src/main`.
fn body(r: &Run, name: &str) -> Arc<Body> {
    let def = r.def(&format!("src/main::{name}"));
    let program = r.program.as_ref().expect("checked");
    Arc::clone(program.bodies.get(&def).expect("a body"))
}

/// Every expression of `b`, parents first.
fn exprs(b: &Body) -> Vec<Expr> {
    let mut out = Vec::new();
    walk::for_each_expr(b, &mut |e| out.push(e.clone()));
    out
}

/// The first expression of `b` whose source text is `text` (outermost first).
fn expr_at(r: &Run, b: &Body, text: &str) -> Expr {
    exprs(b)
        .into_iter()
        .find(|e| !e.span.is_dummy() && r.map.text(e.span) == text)
        .unwrap_or_else(|| panic!("no expression `{text}`"))
}

/// The adjusts of the expression `text` in function `f` of the accepted `src`.
fn adjusts(src: &str, text: &str) -> Vec<Adjust> {
    let r = accepts(src);
    let b = body(&r, "f");
    expr_at(&r, &b, text).adjust
}

/// The type of local `name` in function `f`, as messages print it.
fn local_ty(r: &Run, f: &str, name: &str) -> String {
    let b = body(r, f);
    let local = b
        .locals
        .iter()
        .find(|l| l.name.map(|n| n.as_str() == name).unwrap_or(false))
        .unwrap_or_else(|| panic!("no local `{name}`"));
    r.tcx.ty_string(local.ty)
}

/// The helps of the one diagnostic of `src`: message and each edit's replacement.
fn helps(src: &str) -> Vec<(String, Vec<String>)> {
    let r = check(src);
    assert_eq!(r.diags.len(), 1, "{}", r.rendered());
    r.diags[0]
        .helps
        .iter()
        .map(|h| {
            (
                h.message.clone(),
                h.edits.iter().map(|e| e.replacement.clone()).collect(),
            )
        })
        .collect()
}

/// `src` with every edit of every diagnostic applied.
fn fixed(src: &str) -> String {
    let r = check(src);
    let start = r.map.file_of(r.diags[0].primary.span.lo).start;
    let mut edits: Vec<_> = r
        .diags
        .iter()
        .flat_map(|d| &d.helps)
        .flat_map(|h| &h.edits)
        .cloned()
        .collect();
    edits.sort_by_key(|e| std::cmp::Reverse(e.span.lo));
    let mut text = src.to_owned();
    for e in edits {
        let lo = (e.span.lo.0 - start.0) as usize;
        let hi = (e.span.hi.0 - start.0) as usize;
        text.replace_range(lo..hi, &e.replacement);
    }
    text
}

fn ty_of(r: &Run, t: Ty) -> String {
    r.tcx.ty_string(t)
}

// ---------------------------------------------------------------------------------
// Inference (S:722-735, A:888).

fn inference(h: &mut Harness) {
    h.case(
        "typeck/an integer literal defaults to `int`, a float to `f64`",
        || {
            let r = accepts("public function f(): void { const a = 5; const b = 1.5; }\n");
            assert_eq!(local_ty(&r, "f", "a"), "int");
            assert_eq!(local_ty(&r, "f", "b"), "f64");
        },
    );
    h.case(
        "typeck/a variable unifies across the body: a later use decides it",
        || {
            let r = accepts("public function f(): void { let a = 5; const b: i64 = a; }\n");
            assert_eq!(local_ty(&r, "f", "a"), "i64");
        },
    );
    h.case(
        "typeck/an integer variable used as an index defaults to `isize`",
        || {
            let r = accepts("public function f(xs: i64[]): i64 { let i = 0; return xs[i]; }\n");
            assert_eq!(local_ty(&r, "f", "i"), "isize");
        },
    );
    h.case(
        "typeck/in a comparison a variable takes the other operand's type",
        || {
            let r = accepts(
                "public function f(n: u8): bool { let i = 0; const b = i < n; return b; }\n",
            );
            assert_eq!(local_ty(&r, "f", "i"), "u8");
        },
    );
    h.case(
        "typeck/an integer variable unifies with a float type",
        || {
            let r = accepts("public function f(): void { let a = 5; const b: f64 = a; }\n");
            assert_eq!(local_ty(&r, "f", "a"), "f64");
        },
    );
    h.case("typeck/a float variable never becomes an integer", || {
        rejects(
            "public function f(): void { const x: i64 = 1.5; }\n",
            "EN0401",
            "1:44",
            "mismatched types: expected `i64`, found `f64`",
        );
    });
    h.case(
        "typeck/`let q;` that nothing decides is EN0410 at `q`",
        || {
            rejects(
                "public function f(): void { let q; }\n",
                "EN0410",
                "1:33",
                "cannot infer the type of `q`",
            );
        },
    );
    h.case(
        "typeck/`let q;` a later assignment decides compiles",
        || {
            let r = accepts("public function f(): void { let q; q = 5; }\n");
            assert_eq!(local_ty(&r, "f", "q"), "int");
        },
    );
    h.case(
        "typeck/`[]` with no expected type and no later use is EN0410",
        || {
            rejects(
                "public function f(): void { const xs = []; }\n",
                "EN0410",
                "1:40",
                "cannot infer the type of `[]`",
            );
        },
    );
    h.case("typeck/`[]` a later assignment decides compiles", || {
        let r = accepts("public function f(): void { let xs = []; xs = [1]; }\n");
        assert_eq!(local_ty(&r, "f", "xs"), "int[]");
    });
    h.case(
        "typeck/`null` with no expected type is EN0410 (S:734)",
        || {
            rejects(
                "public function f(): void { const n = null; }\n",
                "EN0410",
                "1:39",
                "cannot infer the type of `null`",
            );
        },
    );
    h.case(
        "typeck/`null` at an expected nullable is typed at it",
        || {
            let r = accepts("public function f(): void { const n: i64 | null = null; }\n");
            let b = body(&r, "f");
            let null = expr_at(&r, &b, "null");
            assert_eq!(null.kind, ExprKind::NullLit);
            assert_eq!(ty_of(&r, null.ty), "i64 | null");
            assert!(null.adjust.is_empty());
        },
    );
    h.case(
        "typeck/`null` where the type is never null is EN0401",
        || {
            rejects(
                "public function f(): void { const n: i64 = null; }\n",
                "EN0401",
                "1:44",
                "mismatched types: expected `i64`, found `null`",
            );
        },
    );
    h.case(
        "typeck/a member access on an unknown type is EN0410 at once",
        || {
            rejects(
                "public function f(): void { let xs = []; const n = xs[0].name; }\n",
                "EN0410",
                "1:52",
                "cannot infer the type of `xs[0]`",
            );
        },
    );
    h.case("typeck/a finished body holds no inference variable", || {
        let r = accepts(
            "public function f(xs: i64[]): void { let i = 0; let q = []; q = [i]; const t = [1, 2]; const v = xs[i]; }\n",
        );
        let b = body(&r, "f");
        for e in exprs(&b) {
            assert!(!r.tcx.has_infer(e.ty), "{}", r.map.text(e.span));
        }
        for l in b.locals.iter() {
            assert!(!r.tcx.has_infer(l.ty));
        }
        assert_eq!(b.expr_count as usize, exprs(&b).len());
    });
}

// ---------------------------------------------------------------------------------
// Literals (S:728).

fn literals(h: &mut Harness) {
    h.case(
        "typeck/a literal takes the annotation's type and its constant",
        || {
            let r = accepts("public function f(): void { const b: u8 = 200; }\n");
            let b = body(&r, "f");
            let lit = expr_at(&r, &b, "200");
            assert_eq!(
                lit.kind,
                ExprKind::Const(ConstValue::Int(200, r.tcx.common().u8))
            );
        },
    );
    h.case(
        "typeck/`-` before a literal folds before the range check",
        || {
            let r = accepts("public function f(): void { const m: i64 = -9223372036854775808; }\n");
            let b = body(&r, "f");
            let lit = expr_at(&r, &b, "-9223372036854775808");
            assert_eq!(
                lit.kind,
                ExprKind::Const(ConstValue::Int(1u128 << 63, r.tcx.common().i64))
            );
        },
    );
    h.case(
        "typeck/a negative literal keeps two's-complement bits at its width",
        || {
            let r = accepts("public function f(): void { const m: i8 = -1; }\n");
            let b = body(&r, "f");
            let lit = expr_at(&r, &b, "-1");
            assert_eq!(
                lit.kind,
                ExprKind::Const(ConstValue::Int(0xFF, r.tcx.common().i8))
            );
        },
    );
    h.case(
        "typeck/`3_000_000_000` at the `int` default is EN0411 with `: i64`",
        || {
            let src = "public function f(): void { const big = 3_000_000_000; }\n";
            rejects(src, "EN0411", "1:41", "`3_000_000_000` doesn't fit `int`");
            assert_eq!(
                helps(src),
                vec![(
                    "give it a wider type: `: i64`".to_owned(),
                    vec![": i64".to_owned()]
                )]
            );
            assert_eq!(
                fixed(src),
                "public function f(): void { const big: i64 = 3_000_000_000; }\n"
            );
        },
    );
    h.case(
        "typeck/a literal out of an annotated type is EN0411 with no fix-it",
        || {
            let src = "public function f(): void { const x: u8 = -1; }\n";
            rejects(src, "EN0411", "1:43", "`-1` doesn't fit `u8`");
            assert!(helps(src).is_empty());
            let r = check(src);
            assert_eq!(r.diags[0].primary.text, "`u8` holds 0 to 255");
        },
    );
    h.case(
        "typeck/an `f32` literal is parsed once at its width, correctly rounded",
        || {
            let text = "1.00000017881393432617187499";
            let r = accepts(&format!(
                "public function f(): void {{ const x: f32 = {text}; }}\n"
            ));
            let b = body(&r, "f");
            let lit = expr_at(&r, &b, text);
            let bits = u64::from(text.parse::<f32>().expect("an f32").to_bits());
            assert_eq!(
                lit.kind,
                ExprKind::Const(ConstValue::Float(bits, r.tcx.common().f32))
            );
        },
    );
    h.case(
        "typeck/an integer literal at a float type is that float",
        || {
            let r = accepts("public function f(): void { const y: f64 = 2; }\n");
            let b = body(&r, "f");
            let lit = expr_at(&r, &b, "2");
            assert_eq!(
                lit.kind,
                ExprKind::Const(ConstValue::Float(2.0f64.to_bits(), r.tcx.common().f64))
            );
        },
    );
    h.case("typeck/a string literal is a `string` (S:962)", || {
        let r =
            accepts("public function f(): void { const s = \"Ada\"; const t: string = \"Bo\"; }\n");
        assert_eq!(local_ty(&r, "f", "s"), "string");
    });
    h.case(
        "typeck/a template is a `string` and its holes take any value",
        || {
            let r = accepts("public function f(n: i64): void { const s = `n = ${n}`; }\n");
            assert_eq!(local_ty(&r, "f", "s"), "string");
        },
    );
    h.case("typeck/a text not in a string-literal union is EN0401 with did-you-mean", || {
        let src = "private type Direction = \"left\" | \"right\";\npublic function f(): void { const d: Direction = \"lft\"; }\n";
        rejects(src, "EN0401", "2:50", "`\"lft\"` is not a `Direction`");
        assert_eq!(
            helps(src),
            vec![(
                "did you mean `\"left\"`?".to_owned(),
                vec!["\"left\"".to_owned()]
            )]
        );
    });
    h.case("typeck/a text of a string-literal union is its case", || {
        let r = accepts(
            "private type Direction = \"left\" | \"right\";\npublic function f(): void { const d: Direction = \"right\"; }\n",
        );
        let b = body(&r, "f");
        let e = expr_at(&r, &b, "\"right\"");
        assert!(
            matches!(e.kind, ExprKind::VariantLit { variant: VariantIdx(1), .. }),
            "{:?}",
            e.kind
        );
    });
}

// ---------------------------------------------------------------------------------
// Operators (S:686-720).

fn operators(h: &mut Harness) {
    h.case(
        "typeck/arithmetic on two numeric types is EN0402 with a widening fix-it",
        || {
            let src = "public function f(a: isize, b: int): isize { return a - b; }\n";
            rejects(src, "EN0402", "1:53", "cannot subtract `int` from `isize`");
            assert_eq!(
                fixed(src),
                "public function f(a: isize, b: int): isize { return a - (b as isize); }\n"
            );
        },
    );
    h.case("typeck/EN0402's verb follows the operator", || {
        for (op, message) in [
            ("+", "cannot add `i32` to `i64`"),
            ("*", "cannot multiply `i64` by `i32`"),
            ("/", "cannot divide `i64` by `i32`"),
            ("%", "cannot take the remainder of `i64` divided by `i32`"),
        ] {
            let src =
                format!("public function f(a: i64, b: i16): i64 {{ return a {op} (b as i32); }}\n");
            let (code, _, m) = one(&src);
            assert_eq!(code, "EN0402");
            assert_eq!(m, message.replace("`i32`", "`int`"));
        }
    });
    h.case(
        "typeck/no widening exists between `i64` and `u64`: no fix-it",
        || {
            let src = "public function f(a: i64, b: u64): i64 { return a + b; }\n";
            rejects(src, "EN0402", "1:49", "cannot add `u64` to `i64`");
            assert!(helps(src).is_empty());
        },
    );
    h.case("typeck/`+` on two strings builds a `string`", || {
        let r = accepts("public function f(a: &string, b: string): void { const s = a + b; }\n");
        assert_eq!(local_ty(&r, "f", "s"), "string");
    });
    h.case(
        "typeck/operators read through one reference to a Copy type",
        || {
            let r = accepts("public function f(r: &i64): void { const s = r + 1; }\n");
            assert_eq!(local_ty(&r, "f", "s"), "i64");
        },
    );
    h.case("typeck/arithmetic on `bool` is EN0420", || {
        rejects(
            "public function f(): void { const x = true + 1; }\n",
            "EN0420",
            "1:39",
            "`+` needs numbers, found `bool`",
        );
    });
    h.case("typeck/bitwise operators need integers (EN0403)", || {
        rejects(
            "public function f(x: f64): void { const y = x & 1.0; }\n",
            "EN0403",
            "1:45",
            "`&` needs integers, found `f64`",
        );
        rejects(
            "public function f(x: f64): void { const y = ~x; }\n",
            "EN0403",
            "1:46",
            "`~` needs integers, found `f64`",
        );
    });
    h.case("typeck/a shift count may have any integer type", || {
        let r = accepts("public function f(x: u32, n: u8): void { const y = x << n; }\n");
        assert_eq!(local_ty(&r, "f", "y"), "u32");
    });
    h.case(
        "typeck/`a & b == c` is EN0420 with a parenthesise fix-it (S:508)",
        || {
            let src = "public function f(a: i64, b: i64, c: i64): bool { return a & b == c; }\n";
            rejects(src, "EN0420", "1:58", "`&` binds looser than `==`");
            assert_eq!(
                fixed(src),
                "public function f(a: i64, b: i64, c: i64): bool { return (a & b) == c; }\n"
            );
        },
    );
    h.case("typeck/`-` needs a signed number (EN0420)", || {
        rejects(
            "public function f(x: u32): void { const y = -x; }\n",
            "EN0420",
            "1:45",
            "`-` needs a signed number, found `u32`",
        );
    });
    h.case("typeck/`!`, `&&` and `||` take conditions (EN0203)", || {
        rejects(
            "public function f(x: i64): void { const y = !x; }\n",
            "EN0203",
            "1:46",
            "a condition must be `bool`, found `i64`",
        );
        rejects(
            "public function f(a: bool, x: i64): void { const y = a && x; }\n",
            "EN0203",
            "1:59",
            "a condition must be `bool`, found `i64`",
        );
    });
    h.case(
        "typeck/integer `/` of literal-default operands is warning EN0430",
        || {
            let src = "public function f(): void { const q = 7 / 2; }\n";
            let r = check(src);
            assert_eq!(r.codes(), vec!["EN0430"]);
            assert!(r.program.is_some(), "a warning does not stop the phase");
            assert_eq!(r.messages(), vec!["integer division truncates"]);
            assert_eq!(
                fixed(src),
                "public function f(): void { const q = 7.0 / 2.0; }\n"
            );
        },
    );
    h.case(
        "typeck/a division of two literals warns whatever its integer type (EN0430, S:688)",
        || {
            assert_eq!(
                all("public function f(): void { const q: i64 = 7 / 2; const r = 7.0 / 2.0; }\n"),
                vec![diag("EN0430", "1:44", "integer division truncates")]
            );
            assert_eq!(
                all("public function f(): void { let a = 7 / 2; const b: i64 = a; }\n"),
                vec![diag("EN0430", "1:37", "integer division truncates")]
            );
        },
    );
    h.case(
        "typeck/variables a later annotation decides give no EN0430",
        || {
            accepts("public function f(): void { let a = 7; let b = 2; const q: i64 = a / b; }\n");
        },
    );
    h.case(
        "typeck/a division whose operands are typed variables gives no EN0430",
        || {
            accepts("public function f(): void { let a: i64 = 7; const q = a / 2; const r = 7.0 / 2.0; }\n");
        },
    );
    h.case(
        "typeck/literals that divide exactly truncate nothing: no EN0430",
        || {
            accepts(
                "public function f(): void { const half = 10 / 2 / 1; const q = (6 + 2) / 4; }\n",
            );
            let r = check("public function f(): void { const q = (6 + 1) / 4; }\n");
            assert_eq!(r.codes(), vec!["EN0430"]);
        },
    );
    h.case(
        "typeck/EN0430 for variables whose type came from the default",
        || {
            let src = "public function f(): void { let a = 7; let b = 2; const q = a / b; }\n";
            let r = check(src);
            assert_eq!(r.codes(), vec!["EN0430"]);
            assert_eq!(
                r.diags[0].helps[0].message,
                "for a fraction, divide floats, as in `7.0 / 2.0`"
            );
            assert!(r.diags[0].helps[0].edits.is_empty());
        },
    );
    h.case("typeck/`??` gives the payload's type; `b` may be `never`", || {
        let r = accepts(
            "public function f(a: i64 | null, c: bool): i64 { const x = a ?? 8; const y = a ?? match (c) { default => return 1 }; return x + y; }\n",
        );
        assert_eq!(local_ty(&r, "f", "x"), "i64");
        assert_eq!(local_ty(&r, "f", "y"), "i64");
    });
    h.case("typeck/`a ?? b ?? c` compiles", || {
        accepts("public function f(a: i64 | null, b: i64 | null): i64 { return a ?? b ?? 3; }\n");
    });
    h.case(
        "typeck/`??` on a value that is never null is EN0420",
        || {
            rejects(
                "public function f(a: i64): i64 { return a ?? 3; }\n",
                "EN0420",
                "1:41",
                "`??` needs a `T | null` on its left, found `i64`",
            );
        },
    );
}

// ---------------------------------------------------------------------------------
// Comparisons (S:692-701, row by row).

fn comparisons(h: &mut Harness) {
    h.case("typeck/compare: `p == null` on any nullable", || {
        accepts("public function f(p: i64 | null, q: &string | null): bool { return p == null && q != null; }\n");
    });
    h.case(
        "typeck/compare: `x == null` on a value that is never null is EN0401",
        || {
            rejects(
                "public function f(x: i64): bool { return x == null; }\n",
                "EN0401",
                "1:42",
                "mismatched types: expected `i64 | null`, found `i64`",
            );
        },
    );
    h.case("typeck/compare: one numeric type, `bool`, `string`, a payload-free enum", || {
        accepts(
            "public enum Color { Red, Green }\npublic function f(a: f64, b: bool, s: &string, t: string, c: Color): bool { return a == 1.5 && b != true && s == t && c == Color.Red; }\n",
        );
    });
    h.case("typeck/compare: two integer types by value", || {
        accepts("public function f(pos: int, len: isize): bool { return pos >= len; }\n");
    });
    h.case("typeck/compare: an integer and a float is EN0402", || {
        rejects(
            "public function f(a: int, b: f64): bool { return a < b; }\n",
            "EN0402",
            "1:50",
            "cannot compare `int` with `f64`",
        );
    });
    h.case("typeck/compare: raw pointers by address", || {
        accepts("public function f(p: *u8, q: *u8): bool { return p == q; }\n");
    });
    h.case("typeck/compare: a class without `Eq` is EN0421", || {
        rejects(
            "public class P { public x: i64; }\npublic function f(a: &P, b: &P): bool { return a == b; }\n",
            "EN0421",
            "2:48",
            "`==` needs `P` to implement `Eq`",
        );
    });
    h.case("typeck/compare: a payload enum without `Eq` is EN0421", || {
        rejects(
            "public enum S { A { x: i64 }, B }\npublic function f(a: S, b: S): bool { return a == b; }\n",
            "EN0421",
            "2:46",
            "`==` needs `S` to implement `Eq`",
        );
    });
    h.case("typeck/compare: `T | null == T | null` needs `T` comparable", || {
        accepts("public function f(a: i64 | null, b: i64 | null): bool { return a == b; }\n");
        rejects(
            "public class P { public x: i64; }\npublic function f(a: P | null, b: P | null): bool { return a == b; }\n",
            "EN0421",
            "2:60",
            "`==` needs `P | null` to implement `Eq`",
        );
    });
    h.case(
        "typeck/compare: `T | null == T` is EN0401 with a narrowing help",
        || {
            let src = "public function f(a: i64 | null, b: i64): bool { return a == b; }\n";
            rejects(
                src,
                "EN0401",
                "1:62",
                "mismatched types: expected `i64 | null`, found `i64`",
            );
            assert_eq!(
                helps(src)[0].0,
                "test `a` first: `a != null && ...` narrows it to its payload"
            );
        },
    );
    h.case(
        "typeck/compare: `<` on strings is EN0420 with a `.compare` fix-it",
        || {
            let src = "public function f(a: string, b: string): bool { return a < b; }\n";
            rejects(src, "EN0420", "1:56", "`<` can't compare `string`s");
            assert_eq!(
                fixed(src),
                "public function f(a: string, b: string): bool { return a.compare(&b) < 0; }\n"
            );
        },
    );
    h.case("typeck/compare: `<` on booleans is EN0420", || {
        rejects(
            "public function f(a: bool, b: bool): bool { return a < b; }\n",
            "EN0420",
            "1:52",
            "`<` can't compare `bool`s",
        );
    });
    h.case("typeck/compare: a text enum against a string is EN0401 (S:591)", || {
        rejects(
            "public enum AgeError { Negative = \"negative age\", Big = \"too big\" }\npublic function f(e: AgeError): bool { return e == \"negative age\"; }\n",
            "EN0401",
            "2:52",
            "mismatched types: expected `AgeError`, found `string`",
        );
    });
}

// ---------------------------------------------------------------------------------
// Casts (S:703-716, row by row).

fn cast_kind(src: &str) -> CastKind {
    let r = accepts(src);
    let b = body(&r, "f");
    exprs(&b)
        .into_iter()
        .find_map(|e| match e.kind {
            ExprKind::Cast(_, kind) => Some(kind),
            _ => None,
        })
        .expect("a cast")
}

fn casts(h: &mut Harness) {
    h.case("typeck/cast: the table's rows and their kinds", || {
        let rows = [
            ("x: i64", "x as u16", CastKind::IntToInt),
            ("x: i64", "x as f32", CastKind::IntToFloat),
            ("x: f32", "x as f64", CastKind::FloatToFloat),
            ("x: f64", "x as i32", CastKind::FloatToInt),
            ("x: Color", "x as u8", CastKind::EnumToInt),
            ("x: bool", "x as u8", CastKind::BoolToInt),
            ("x: usize", "x as *u16", CastKind::UsizeToRaw),
            ("x: *u16", "x as usize", CastKind::RawToUsize),
            ("x: &u16", "x as *u16", CastKind::RefToRaw),
            ("x: *u16", "x as *u8", CastKind::RawToRaw),
        ];
        for (param, cast, kind) in rows {
            let src = format!(
                "public enum Color {{ Red, Green }}\npublic function f({param}): void {{ const y = {cast}; }}\n"
            );
            assert_eq!(cast_kind(&src), kind, "{cast}");
        }
    });
    h.case(
        "typeck/cast: a literal takes the target's type; a raw target makes it `usize`",
        || {
            assert_eq!(
                cast_kind("public function f(): void { const y = 0xFFFFFFFFFFFFFFFF as u64; }\n"),
                CastKind::IntToInt
            );
            assert_eq!(
                cast_kind("public function f(): void { const y = 0xB8000 as *u16; }\n"),
                CastKind::UsizeToRaw
            );
        },
    );
    h.case("typeck/cast: `300 as u8` is EN0411 at the literal", || {
        rejects(
            "public function f(): void { const y = 300 as u8; }\n",
            "EN0411",
            "1:39",
            "`300` doesn't fit `u8`",
        );
    });
    h.case(
        "typeck/cast: a variable operand does not unify with the target",
        || {
            let r = accepts("public function f(): void { let x = 5; const y = x as i64; }\n");
            assert_eq!(local_ty(&r, "f", "x"), "int");
            assert_eq!(
                cast_kind("public function f(): void { let x = 5; const y = x as f64; }\n"),
                CastKind::IntToFloat
            );
        },
    );
    h.case("typeck/cast: what the table lacks is EN0404", || {
        for (param, cast, from, to) in [
            ("x: i64", "x as Color", "i64", "Color"),
            ("x: i64", "x as bool", "i64", "bool"),
            ("x: AgeError", "x as u8", "AgeError", "u8"),
            ("x: string", "x as i64", "string", "i64"),
        ] {
            let src = format!(
                "public enum Color {{ Red }}\npublic enum AgeError {{ Negative = \"negative\" }}\npublic function f({param}): void {{ const y = {cast}; }}\n"
            );
            let (code, at, message) = one(&src);
            assert_eq!(code, "EN0404");
            let col = "public function f(".len() + param.len() + "): void { const y = ".len() + 1;
            assert_eq!(at, format!("3:{col}"));
            assert_eq!(message, format!("`{from}` can't be converted to `{to}` with `as`"));
        }
    });
}

// ---------------------------------------------------------------------------------
// The coercion table (S:654-684), each row with an accept and a reject, and A:888's
// chains as `adjust` vectors.

fn coercions(h: &mut Harness) {
    h.case("typeck/C04: `&Box<T>` to `&T` records `BoxDeref`", || {
        assert_eq!(
            adjusts(
                "public function f(b: Box<u8[]>): void { const v: &u8[] = &b; }\n",
                "&b"
            ),
            vec![Adjust::BoxDeref]
        );
        rejects(
            "public function f(b: Box<i64>): void { const x: i64 = b; }\n",
            "EN0401",
            "1:55",
            "mismatched types: expected `i64`, found `Box<i64>`",
        );
    });
    h.case(
        "typeck/A:888: `fill(&b, 7)`'s chain is `BoxDeref` then `ArrayToSlice`",
        || {
            assert_eq!(
                adjusts(
                    "public function f(b: Box<u8[]>): void { const v: &Slice<u8> = &b; }\n",
                    "&b"
                ),
                vec![Adjust::BoxDeref, Adjust::ArrayToSlice]
            );
        },
    );
    h.case(
        "typeck/C05: `&T` to a Copy `T` records `ReadThrough`",
        || {
            assert_eq!(
                adjusts(
                    "public function f(r: &i64): void { const v: i64 = r; }\n",
                    "r"
                ),
                vec![Adjust::ReadThrough]
            );
            rejects(
                "public function f(r: &string): void { const v: string = r; }\n",
                "EN0401",
                "1:57",
                "mismatched types: expected `string`, found `&string`",
            );
        },
    );
    h.case("typeck/C06: `T` to `T | null` records `WrapNull`", || {
        assert_eq!(
            adjusts(
                "public function f(): void { const n: i64 | null = 5; }\n",
                "5"
            ),
            vec![Adjust::WrapNull]
        );
        rejects(
            "public function f(ys: i64[]): void { const xs: (i64 | null)[] = ys; }\n",
            "EN0401",
            "1:65",
            "mismatched types: expected `(i64 | null)[]`, found `i64[]`",
        );
    });
    h.case(
        "typeck/C07: `&T` to `&T | null` records `WrapNullRef`",
        || {
            assert_eq!(
                adjusts(
                    "public function f(r: &i64): void { const v: &i64 | null = r; }\n",
                    "r"
                ),
                vec![Adjust::WrapNullRef]
            );
            rejects(
                "public function f(x: i64): void { const r: &(i64 | null) = &x; }\n",
                "EN0401",
                "1:60",
                "mismatched types: expected `&(i64 | null)`, found `&i64`",
            );
        },
    );
    h.case(
        "typeck/C08: `&T | null` to `T | null` records `ReadThroughNullable`",
        || {
            assert_eq!(
                adjusts(
                    "public function f(p: &i64 | null): void { const v: i64 | null = p; }\n",
                    "p"
                ),
                vec![Adjust::ReadThroughNullable]
            );
            rejects(
                "public function f(p: &string | null): void { const v: string | null = p; }\n",
                "EN0401",
                "1:71",
                "mismatched types: expected `string | null`, found `&string | null`",
            );
        },
    );
    h.case("typeck/C09: `never` to any type records `NeverToAny` alone", || {
        let src = "public function f(c: bool): i64 { const x: i64 = match (c) { default => return 1 }; return x; }\n";
        assert_eq!(
            adjusts(src, "match (c) { default => return 1 }"),
            vec![Adjust::NeverToAny]
        );
    });
    h.case(
        "typeck/C10: a literal's variable meets the concrete type, no adjust",
        || {
            assert!(
                adjusts("public function f(): void { const b: u8 = 200; }\n", "200").is_empty()
            );
            rejects(
                "public function f(): void { const b: u8 = 1.5; }\n",
                "EN0401",
                "1:43",
                "mismatched types: expected `u8`, found `f64`",
            );
        },
    );
    h.case(
        "typeck/C13: a string literal at `&string` records `LiteralDescriptor`",
        || {
            assert_eq!(
                adjusts(
                    "public function f(): void { const s: &string = \"Ada\"; }\n",
                    "\"Ada\""
                ),
                vec![Adjust::LiteralDescriptor]
            );
            assert_eq!(
                adjusts(
                    "public function f(): void { const s: &string | null = \"Ada\"; }\n",
                    "\"Ada\""
                ),
                vec![Adjust::LiteralDescriptor, Adjust::WrapNullRef]
            );
            rejects(
                "public function f(): void { const s: &i64 = \"Ada\"; }\n",
                "EN0401",
                "1:45",
                "mismatched types: expected `&i64`, found `string`",
            );
        },
    );
    h.case(
        "typeck/C18: `&T[N]` and a whole `&T[]` to `&Slice<T>`",
        || {
            assert_eq!(
                adjusts(
                    "public function f(s: u8[4]): void { const v: &Slice<u8> = &s; }\n",
                    "&s"
                ),
                vec![Adjust::FixedToSlice]
            );
            assert_eq!(
                adjusts(
                    "public function f(s: u8[]): void { const v: &Slice<u8> = &s; }\n",
                    "&s"
                ),
                vec![Adjust::ArrayToSlice]
            );
        },
    );
    h.case("typeck/A:888: `read(0, &sector)`'s chain is `FixedToSlice` then `WrapNullRef`", || {
        assert_eq!(
            adjusts(
                "public function f(sector: u8[512]): void { const buf: &Slice<u8> | null = &sector; }\n",
                "&sector"
            ),
            vec![Adjust::FixedToSlice, Adjust::WrapNullRef]
        );
    });
    h.case("typeck/C18 never runs backwards: a fixed array can't grow", || {
        let src = "public function f(sector: u8[4]): void { const w: &u8[] = &sector; }\n";
        rejects(src, "EN0401", "1:59", "a fixed array can't grow");
        let r = check(src);
        assert_eq!(r.diags[0].primary.text, "expected `&u8[]`, found `&u8[4]`");
        assert_eq!(
            r.diags[0].helps[0].message,
            "if only elements are read or set, use `&Slice<u8>`; to let it grow, make `sector` a `u8[]`"
        );
    });
    h.case(
        "typeck/C18 never runs backwards: a part of an array can't grow",
        || {
            rejects(
                "public function f(s: &Slice<u8>): void { const w: &u8[] = s; }\n",
                "EN0401",
                "1:59",
                "a part of an array can't grow",
            );
        },
    );
    h.case(
        "typeck/a bracket literal behind `&` at `&Slice<T>` is a `T[N]` and C18",
        || {
            let r = accepts("public function f(): void { const r: &Slice<i64> = &[3, 1, 4]; }\n");
            let b = body(&r, "f");
            let borrow = expr_at(&r, &b, "&[3, 1, 4]");
            assert_eq!(borrow.adjust, vec![Adjust::FixedToSlice]);
            assert_eq!(ty_of(&r, borrow.ty), "&i64[3]");
            let ExprKind::Borrow(lit) = &borrow.kind else {
                panic!("a borrow")
            };
            assert!(matches!(lit.kind, ExprKind::ArrayLit(_)));
        },
    );
    h.case("typeck/C21: `&D` and `Box<D>` to a base record `Upcast`", || {
        let classes = "public class Animal { public name: string; }\npublic class Dog extends Animal { public age: i64; }\n";
        assert_eq!(
            adjusts(&format!("{classes}public function f(rex: &Dog): void {{ const a: &Animal = rex; }}\n"), "rex"),
            vec![Adjust::Upcast]
        );
        assert_eq!(
            adjusts(&format!("{classes}public function f(b: Box<Dog>): void {{ const a: Box<Animal> = b; }}\n"), "b"),
            vec![Adjust::Upcast]
        );
        rejects(
            &format!("{classes}public function f(d: Dog): void {{ const a: Animal = d; }}\n"),
            "EN0401",
            "3:53",
            "mismatched types: expected `Animal`, found `Dog`",
        );
    });
    h.case("typeck/C20 elsewhere than a parameter: extra fields are EN0440", || {
        let src = "public class User { public name: string; public age: i64; }\npublic function f(u: User): void { const q: { name: string } = u; }\n";
        rejects(
            src,
            "EN0440",
            "2:64",
            "`u` has a field `age` that `{ name: string }` does not have",
        );
        let helps: Vec<String> = helps(src).into_iter().map(|(m, _)| m).collect();
        assert_eq!(
            helps,
            vec![
                "build the smaller object: `{ name: u.name }`".to_owned(),
                "or keep a reference: `const q = &u;`".to_owned(),
            ]
        );
    });
    h.case(
        "typeck/G05's EN0401 at an annotation, byte for byte",
        || {
            let src =
                "public function f(): void {\n  const n: i64 = 5;\n  const a: string = n;\n}\n";
            let expected = "error[EN0401]: mismatched types: expected `string`, found `i64`
 --> src/main.en:3:21
  |
3 |   const a: string = n;
  |                     ^ this is `i64`
  |            ------ `string` is required by this annotation
  |
  = note: Enrang never converts between numbers and strings implicitly.
help: convert it explicitly
  |
3 |   const a: string = n.toString();
  |                      +++++++++++
  = explain: run `enrang explain EN0401`

error: aborting due to 1 previous error
";
            let actual = check(src).rendered();
            assert!(actual == expected, "{}", line_diff(expected, &actual));
        },
    );
    h.case("typeck/EN0401 at a `return` names the return type", || {
        let src = "public function f(): string { const n: i64 = 5; return n; }\n";
        let r = check(src);
        assert_eq!(r.codes(), vec!["EN0401"]);
        let d = &r.diags[0];
        assert_eq!(d.secondary.len(), 1);
        assert_eq!(r.map.text(d.secondary[0].span), "string");
        assert_eq!(
            d.secondary[0].text,
            "`string` is required by the return type"
        );
    });
}

// ---------------------------------------------------------------------------------
// References: EN0612 and EN0422 (S:656, S:684, S:775).

fn references(h: &mut Harness) {
    h.case("typeck/EN0612: a value at an annotated `&T`, with the `&` fix-it", || {
        let src = "public function f(xs: i64[]): void { const r: &i64[] = xs; }\n";
        rejects(src, "EN0612", "1:56", "missing `&`: a reference is expected here");
        let r = check(src);
        assert_eq!(r.diags[0].primary.text, "expected `&i64[]`, found `i64[]`");
        assert_eq!(
            r.diags[0].entries[0].text,
            "a reference is only ever made by writing `&`; with no `&`, a value is moved or copied."
        );
        assert_eq!(fixed(src), "public function f(xs: i64[]): void { const r: &i64[] = &xs; }\n");
    });
    h.case(
        "typeck/EN0612: a `return` at `&T` names the function",
        || {
            let src = "public function f(xs: &i64[]): &i64 { return xs[0]; }\n";
            rejects(
                src,
                "EN0612",
                "1:46",
                "missing `&`: `f` returns a reference",
            );
            assert_eq!(
                fixed(src),
                "public function f(xs: &i64[]): &i64 { return &xs[0]; }\n"
            );
        },
    );
    h.case("typeck/`&r` with `r: &T` is `r` itself", || {
        let r = accepts("public function f(r: &i64): void { const s: &i64 = &r; }\n");
        let b = body(&r, "f");
        let e = expr_at(&r, &b, "r");
        assert!(matches!(e.kind, ExprKind::Local(_)));
        assert!(
            !exprs(&b)
                .iter()
                .any(|e| matches!(e.kind, ExprKind::Borrow(_))),
            "no borrow of a reference"
        );
    });
    h.case(
        "typeck/EN0422: `r = v` on a reference variable, with both fix-its",
        || {
            let src = "public function f(r: &i64): void { r = 5; }\n";
            rejects(
                src,
                "EN0422",
                "1:36",
                "`r` is a reference: write through it with `*r`",
            );
            assert_eq!(
                helps(src),
                vec![
                    ("write through it: `*r`".to_owned(), vec!["*".to_owned()]),
                    (
                        "or point it at another place: `&5`".to_owned(),
                        vec!["&".to_owned()]
                    ),
                ]
            );
        },
    );
    h.case(
        "typeck/EN0422: `r += 1` and `r++` on a reference variable",
        || {
            rejects(
                "public function f(r: &i64): void { r += 1; }\n",
                "EN0422",
                "1:36",
                "`r` is a reference: write through it with `*r`",
            );
            let src = "public function f(r: &i64): void { r++; }\n";
            rejects(
                src,
                "EN0422",
                "1:36",
                "`r` is a reference: write through it with `*r`",
            );
            assert_eq!(fixed(src), "public function f(r: &i64): void { (*r)++; }\n");
        },
    );
    h.case("typeck/a reference variable is repointed by a reference or a literal", || {
        accepts(
            "public function f(r: &i64, s: &i64, t: &string): void { let a = r; a = s; let b = t; b = \"x\"; *a = 3; }\n",
        );
    });
    h.case("typeck/assignment coerces its right side; compound assignment does not", || {
        let r = accepts("public function f(): void { let x: i64 | null = null; x = 5; let y: i64 = 1; y += 2; }\n");
        let b = body(&r, "f");
        assert_eq!(expr_at(&r, &b, "5").adjust, vec![Adjust::WrapNull]);
        assert!(expr_at(&r, &b, "2").adjust.is_empty());
    });
    h.case(
        "typeck/a compound assignment keeps its operator's rules",
        || {
            rejects(
                "public function f(a: i64, b: i32): void { let x = a; x += b; }\n",
                "EN0402",
                "1:54",
                "cannot add `int` to `i64`",
            );
            accepts("public function f(s: string, t: &string): void { let x = s; x += t; }\n");
        },
    );
}

// ---------------------------------------------------------------------------------
// Bracket literals, tuples and indexing (S:735, S:602, S:720).

fn arrays(h: &mut Harness) {
    h.case(
        "typeck/a bracket literal at a tuple type is a tuple",
        || {
            let r = accepts("public function f(): void { const t: [i64, string] = [1, \"a\"]; }\n");
            let b = body(&r, "f");
            let t = expr_at(&r, &b, "[1, \"a\"]");
            assert!(matches!(t.kind, ExprKind::TupleLit(_)));
            assert_eq!(ty_of(&r, t.ty), "[i64, string]");
        },
    );
    h.case(
        "typeck/a bracket literal at `T[N]` is a fixed array",
        || {
            let r = accepts("public function f(): void { const b: i64[3] = [1, 2, 3]; }\n");
            let b = body(&r, "f");
            let lit = expr_at(&r, &b, "[1, 2, 3]");
            assert!(matches!(lit.kind, ExprKind::ArrayLit(_)));
            assert_eq!(ty_of(&r, lit.ty), "i64[3]");
        },
    );
    h.case("typeck/a fixed array of the wrong length is EN0401", || {
        rejects(
            "public function f(): void { const b: i64[3] = [1, 2]; }\n",
            "EN0401",
            "1:47",
            "mismatched types: expected `i64[3]`, found `i64[2]`",
        );
    });
    h.case(
        "typeck/with no expected type a bracket literal is a growable array",
        || {
            let r = accepts("public function f(): void { const a = [1, 2]; }\n");
            assert_eq!(local_ty(&r, "f", "a"), "int[]");
        },
    );
    h.case("typeck/`[1, \"a\"]` is EN0401 with a tuple help (S:735)", || {
        let src = "public function f(): void { const d = [1, \"a\"]; }\n";
        rejects(src, "EN0401", "1:43", "mismatched types: expected `int`, found `string`");
        assert_eq!(
            helps(src)[0].0,
            "for values of different types, annotate a tuple type, as in `const x: [int, string] = [1, \"a\"];`"
        );
    });
    h.case("typeck/an array element is a coercion site", || {
        let r = accepts("public function f(): void { const a: (i64 | null)[] = [1, null]; }\n");
        let b = body(&r, "f");
        assert_eq!(expr_at(&r, &b, "1").adjust, vec![Adjust::WrapNull]);
    });
    h.case(
        "typeck/a tuple pattern gives its right side a tuple type (S:735)",
        || {
            let r = accepts("public function f(): void { const [p, q] = [1, 2]; }\n");
            let b = body(&r, "f");
            let t = expr_at(&r, &b, "[1, 2]");
            assert!(matches!(t.kind, ExprKind::TupleLit(_)), "{:?}", t.kind);
            assert_eq!(ty_of(&r, t.ty), "[int, int]");
        },
    );
    h.case(
        "typeck/`[a, b] = [b, a];` swaps through a tuple (D9)",
        || {
            let r =
                accepts("public function f(): void { let a = 1; let b = 2; [a, b] = [b, a]; }\n");
            let b = body(&r, "f");
            let swap = expr_at(&r, &b, "[a, b] = [b, a]");
            let ExprKind::Destructure { value, .. } = &swap.kind else {
                panic!("a destructuring assignment")
            };
            assert!(matches!(value.kind, ExprKind::TupleLit(_)));
        },
    );
    h.case(
        "typeck/an index of any integer type; a float index is EN0405",
        || {
            accepts("public function f(xs: i64[], a: u8, b: i64): i64 { return xs[a] + xs[b]; }\n");
            rejects(
                "public function f(xs: i64[]): i64 { return xs[1.5]; }\n",
                "EN0405",
                "1:47",
                "an index must be an integer, found `f64`",
            );
        },
    );
    h.case(
        "typeck/a tuple index is a constant within range (EN0452)",
        || {
            let r = accepts("public function f(t: [i64, string]): i64 { return t[0]; }\n");
            let b = body(&r, "f");
            assert!(matches!(expr_at(&r, &b, "t[0]").kind, ExprKind::Field(..)));
            rejects(
                "public function f(t: [int, int]): int { return t[2]; }\n",
                "EN0452",
                "1:50",
                "`[int, int]` has no element 2",
            );
            rejects(
                "public function f(t: [int, int], i: isize): int { return t[i]; }\n",
                "EN0452",
                "1:60",
                "a tuple index must be a constant",
            );
        },
    );
    h.case("typeck/indexing what has no elements is EN0420", || {
        rejects(
            "public function f(x: i64): i64 { return x[0]; }\n",
            "EN0420",
            "1:41",
            "`i64` can't be indexed",
        );
    });
}

// ---------------------------------------------------------------------------------
// Spreads (S:803-823, A:890; TESTING 18's spread rows).

fn spread_operand(src: &str, text: &str) -> Vec<Adjust> {
    let r = accepts(src);
    let b = body(&r, "f");
    let built = exprs(&b)
        .into_iter()
        .find(|e| matches!(e.kind, ExprKind::ArrayBuild { .. }))
        .expect("an ArrayBuild");
    let ExprKind::ArrayBuild { parts, .. } = &built.kind else {
        unreachable!()
    };
    parts
        .iter()
        .find_map(|p| match p {
            enrang_hir::ArrayPart::Spread(e, _) if r.map.text(e.span) == text => {
                Some(e.adjust.clone())
            }
            _ => None,
        })
        .expect("the operand")
}

fn spreads(h: &mut Harness) {
    h.case(
        "typeck/spread: a place borrows, a reference reborrows, then C18",
        || {
            assert_eq!(
                spread_operand(
                    "public function f(f: i32[3]): void { const c = [...f]; }\n",
                    "f"
                ),
                vec![Adjust::AutoBorrow, Adjust::FixedToSlice]
            );
            assert_eq!(
                spread_operand(
                    "public function f(a: &i32[3]): i32[] { return [...a]; }\n",
                    "a"
                ),
                vec![Adjust::Reborrow, Adjust::FixedToSlice]
            );
            assert_eq!(
                spread_operand(
                    "public function f(r: &i64[]): void { const c = [...r]; }\n",
                    "r"
                ),
                vec![Adjust::Reborrow, Adjust::ArrayToSlice]
            );
            assert_eq!(
                spread_operand(
                    "public function f(s: &Slice<i64>): void { const c = [...s]; }\n",
                    "s"
                ),
                vec![Adjust::Reborrow]
            );
        },
    );
    h.case("typeck/spread: `[...&f]` and `[...xs]` build growable arrays", || {
        let r = accepts("public function f(f: i32[3], xs: i64[]): void { const c = [...&f]; const d = [0, ...xs]; }\n");
        assert_eq!(local_ty(&r, "f", "c"), "int[]");
        assert_eq!(local_ty(&r, "f", "d"), "i64[]");
    });
    h.case(
        "typeck/spread: a non-array is EN0438, a box with the `...*b` help",
        || {
            rejects(
                "public function f(): void { const a = [...5]; }\n",
                "EN0438",
                "1:40",
                "`...` needs an array, found `int`",
            );
            rejects(
                "public function f(): void { const a = [...\"abc\"]; }\n",
                "EN0438",
                "1:40",
                "`...` needs an array, found `string`",
            );
            rejects(
                "public function f(o: i64[] | null): void { const a = [...o]; }\n",
                "EN0438",
                "1:55",
                "`...` needs an array, found `i64[] | null`",
            );
            let src = "public function f(b: Box<i64[]>): void { const a = [...b]; }\n";
            rejects(
                src,
                "EN0438",
                "1:53",
                "`...` needs an array, found `Box<i64[]>`",
            );
            assert_eq!(
                fixed(src),
                "public function f(b: Box<i64[]>): void { const a = [...*b]; }\n"
            );
        },
    );
    h.case(
        "typeck/spread: at `T[N]` EN0401 with the growable note",
        || {
            let src = "public function f(b: i64[]): void { const a: i64[3] = [...b]; }\n";
            rejects(
                src,
                "EN0401",
                "1:55",
                "mismatched types: expected `i64[3]`, found `i64[]`",
            );
            let r = check(src);
            assert_eq!(
                r.diags[0].entries[0].text,
                "a spread builds a growable array, never a fixed one"
            );
        },
    );
    h.case(
        "typeck/spread: no coercion, so `(i64 | null)[]` is EN0401 with a `.map` help",
        || {
            let src = "public function f(xs: i64[]): void { const n: (i64 | null)[] = [...xs]; }\n";
            rejects(
                src,
                "EN0401",
                "1:65",
                "mismatched types: expected `(i64 | null)[]`, found `i64[]`",
            );
            assert_eq!(
                helps(src)[0].0,
                "spread a converted copy: `...xs.map((x): i64 | null => x)`"
            );
            let src =
                "public function f(xs: i64[]): void { const n: (i64 | null)[] = [0, ...xs]; }\n";
            let (code, _, _) = one(src);
            assert_eq!(code, "EN0401");
        },
    );
    h.case("typeck/spread: two element types are EN0401", || {
        rejects(
            "public function f(a: i32[], b: i64[]): void { const c = [...a, ...b]; }\n",
            "EN0401",
            "1:64",
            "mismatched types: expected `int[]`, found `i64[]`",
        );
    });
    h.case(
        "typeck/spread: an unknown operand is EN0410 at once",
        || {
            rejects(
                "public function f(): void { let q; const c = [...q]; q = [1]; }\n",
                "EN0410",
                "1:50",
                "cannot infer the type of `q`",
            );
            accepts("public function f(): void { let q = []; const c = [...q]; q = [1]; }\n");
            let (code, _, _) = one("public function f(): void { const c = [...[]]; }\n");
            assert_eq!(code, "EN0410");
        },
    );
    h.case("typeck/spread: `Clone` after inference; bounded parameters compile", || {
        accepts("public function f<T extends Clone>(xs: &T[]): T[] { return [...xs]; }\n");
        accepts("public function f<T extends Copy>(xs: &T[]): T[] { return [...xs]; }\n");
        accepts(
            "public class Node { public next: Box<Node> | null = null; }\npublic function f(a: Node[], b: (*u8)[], c: (i64 | null)[], d: i64[2][], e: Box<i64>[], g: Result<i64>[]): void { const x = [...a]; const y = [...b]; const z = [...c]; const w = [...d]; const v = [...e]; const u = [...g]; }\n",
        );
    });
    h.case("typeck/spread: a class with a destructor and no `clone` is EN0438", || {
        rejects(
            "public class R { public x: i64 = 0; public destructor() {} }\npublic function f(xs: &R[]): void { const c = [...xs]; }\n",
            "EN0438",
            "2:48",
            "`...` clones each element, and `R` is not `Clone`",
        );
        rejects(
            "public class P { public p: *u8; }\npublic function f(xs: &P[]): void { const c = [...xs]; }\n",
            "EN0438",
            "2:48",
            "`...` clones each element, and `P` is not `Clone`",
        );
        accepts(
            "public class R { public x: i64 = 0; public destructor() {} public clone(): R { return new R(); } }\npublic function f(xs: &R[]): void { const c = [...xs]; }\n",
        );
    });
}

// ---------------------------------------------------------------------------------
// `match` (S:1132-1136, plan d.5, 2D's handover).

fn arms(r: &Run, b: &Body, text: &str) -> Vec<enrang_hir::Arm> {
    match expr_at(r, b, text).kind {
        ExprKind::Match { arms, .. } => arms,
        other => panic!("not a match: {other:?}"),
    }
}

const SHAPE: &str = "public enum Shape { Circle { radius: f64 }, Square { side: f64 }, Empty }\npublic enum Color { Red, Green }\n";

fn matches(h: &mut Harness) {
    h.case("typeck/match: a bare case of the subject's enum is EN0502 with a fix-it", || {
        let src = format!(
            "{SHAPE}public function f(s: &Shape): i64 {{ return match (s) {{ Shape.Circle => 1, Square => 2, default => 3 }}; }}\n"
        );
        rejects(&src, "EN0502", "3:75", "`Square` is a case of `Shape`: write `Shape.Square`");
        assert!(fixed(&src).contains("Shape.Square => 2"));
    });
    h.case("typeck/match: a case of another enum is EN0504", || {
        rejects(
            &format!("{SHAPE}public function f(c: Color): i64 {{ return match (c) {{ Shape.Empty => 1, default => 2 }}; }}\n"),
            "EN0504",
            "3:55",
            "`Shape.Empty` can't match a `Color`",
        );
    });
    h.case("typeck/match: a qualified name that is no case is EN0303", || {
        let src = format!(
            "{SHAPE}public function f(s: &Shape): i64 {{ return match (s) {{ Shape.Foo => 1, default => 2 }}; }}\n"
        );
        let col = "public function f(s: &Shape): i64 { return match (s) { Shape.".len() + 1;
        rejects(&src, "EN0303", &format!("3:{col}"), "`Shape` has no member `Foo`");
    });
    h.case("typeck/match: a literal of another type is EN0504", || {
        rejects(
            "public function f(s: &string): i64 { return match (s) { 1 => 1, default => 2 }; }\n",
            "EN0504",
            "1:57",
            "`1` can't match a `string`",
        );
        rejects(
            "public function f(x: i64): i64 { return match (x) { null => 1, default => 2 }; }\n",
            "EN0504",
            "1:53",
            "`null` can't match an `i64`",
        );
    });
    h.case("typeck/match: cases, literals, ranges, negative literals, `null`", || {
        let src = format!(
            "{SHAPE}public function f(s: &Shape, code: i64, x: i64 | null): i64 {{\n  const a = match (s) {{ Shape.Circle => 1, Shape.Square, Shape.Empty => 2 }};\n  const b = match (code) {{ 200, 201 => 1, 300..400 => 2, -1 => 3, default => 4 }};\n  const c = match (x) {{ null => 0, 1 => 1, default => 2 }};\n  return a + b + c;\n}}\n"
        );
        let r = accepts(&src);
        let b = body(&r, "f");
        let i64_ty = r.tcx.common().i64;
        let a = arms(&r, &b, "match (s) { Shape.Circle => 1, Shape.Square, Shape.Empty => 2 }");
        assert_eq!(a[0].values, vec![ArmValue::Case(VariantIdx(0))]);
        assert_eq!(
            a[1].values,
            vec![ArmValue::Case(VariantIdx(1)), ArmValue::Case(VariantIdx(2))]
        );
        assert_eq!(r.map.text(a[1].span), "Shape.Square, Shape.Empty => 2");
        assert_eq!(
            a[1].value_spans.iter().map(|s| r.map.text(*s)).collect::<Vec<_>>(),
            vec!["Shape.Square", "Shape.Empty"]
        );
        let codes = arms(
            &r,
            &b,
            "match (code) { 200, 201 => 1, 300..400 => 2, -1 => 3, default => 4 }",
        );
        assert_eq!(
            codes[0].values,
            vec![
                ArmValue::Const(ConstValue::Int(200, i64_ty)),
                ArmValue::Const(ConstValue::Int(201, i64_ty))
            ]
        );
        assert_eq!(
            codes[1].values,
            vec![ArmValue::Range(
                ConstValue::Int(300, i64_ty),
                ConstValue::Int(400, i64_ty)
            )]
        );
        assert_eq!(
            codes[2].values,
            vec![ArmValue::Const(ConstValue::Int(u128::from(u64::MAX), i64_ty))]
        );
        assert!(codes[3].values.is_empty());
        let x = arms(&r, &b, "match (x) { null => 0, 1 => 1, default => 2 }");
        assert_eq!(x[0].values, vec![ArmValue::Null]);
    });
    h.case("typeck/match: `match (true)` has conditions as `Cond`", || {
        let r = accepts(
            "public function f(age: i64): &string { return match (true) { age < 13 => \"child\", age < 20 => \"teen\", default => \"adult\" }; }\n",
        );
        let b = body(&r, "f");
        let m = expr_at(&r, &b, "match (true) { age < 13 => \"child\", age < 20 => \"teen\", default => \"adult\" }");
        let ExprKind::Match { subject, arms } = &m.kind else {
            unreachable!()
        };
        assert_eq!(subject.kind, ExprKind::Const(ConstValue::Bool(true)));
        assert!(matches!(arms[0].values[0], ArmValue::Cond(_)));
        assert_eq!(arms[0].values.len(), 1);
    });
    h.case("typeck/match: `Ok` and `Err` arms on a `Result`", || {
        let r = accepts(
            "public function f(r: &Result<i64, Failure>): i64 { return match (r) { Ok => 1, Err => 2 }; }\n",
        );
        let b = body(&r, "f");
        let a = arms(&r, &b, "match (r) { Ok => 1, Err => 2 }");
        assert_eq!(a[0].values, vec![ArmValue::Case(VariantIdx(0))]);
        assert_eq!(a[1].values, vec![ArmValue::Case(VariantIdx(1))]);
    });
    h.case("typeck/match: a string-literal union's texts are its cases", || {
        let r = accepts(
            "private type Direction = \"left\" | \"right\";\npublic function f(d: Direction): i64 { return match (d) { \"left\" => 1, \"right\" => 2 }; }\n",
        );
        let b = body(&r, "f");
        let a = arms(&r, &b, "match (d) { \"left\" => 1, \"right\" => 2 }");
        assert_eq!(a[1].values, vec![ArmValue::Case(VariantIdx(1))]);
    });
    h.case("typeck/match: arms unify with no expected type (EN0432)", || {
        rejects(
            "public function f(x: i64): void { const y = match (x) { 1 => 1, default => \"no\" }; }\n",
            "EN0432",
            "1:76",
            "the branches have different types: `int` and `string`",
        );
    });
    h.case("typeck/match: with an expected type each arm coerces", || {
        let r = accepts(
            "public function f(x: i64): void { const y: i64 | null = match (x) { 1 => 5, default => null }; }\n",
        );
        let b = body(&r, "f");
        assert_eq!(expr_at(&r, &b, "5").adjust, vec![Adjust::WrapNull]);
    });
    h.case("typeck/match: a block arm that ends meets the expected type", || {
        rejects(
            "public function f(c: bool): void { const x: i64 = match (c) { default => {} }; }\n",
            "EN0401",
            "1:74",
            "mismatched types: expected `i64`, found `void`",
        );
    });
    h.case("typeck/match: as a statement its arms need not agree", || {
        accepts("public function f(x: i64, s: string): void { match (x) { 1 => s.length(), default => {} } }\n");
    });
    h.case("typeck/match: a guard is a condition", || {
        rejects(
            &format!("{SHAPE}public function f(s: &Shape, n: i64): i64 {{ return match (s) {{ Shape.Circle if n => 1, default => 2 }}; }}\n"),
            "EN0203",
            "3:80",
            "a condition must be `bool`, found `i64`",
        );
    });
}

// ---------------------------------------------------------------------------------
// Statements (S:1131, S:1137).

fn statements(h: &mut Harness) {
    h.case("typeck/conditions must be `bool` (EN0203)", || {
        for (stmt, col) in [
            ("if (count) {}", 43),
            ("while (count) {}", 46),
            ("for (; count; ) {}", 46),
            ("const y = count ? 1 : 2;", 49),
        ] {
            let src = format!("public function f(count: i64): void {{ {stmt} }}\n");
            let (code, at, message) = one(&src);
            assert_eq!(code, "EN0203", "{stmt}");
            assert_eq!(at, format!("1:{col}"), "{stmt}");
            assert_eq!(message, "a condition must be `bool`, found `i64`");
        }
    });
    h.case("typeck/EN0203's help compares a number with 0", || {
        let src = "public function f(count: i64): void { if (count) {} }\n";
        assert_eq!(helps(src)[0].0, "compare it: `count != 0`");
    });
    h.case(
        "typeck/a body that can end without a value is EN0427",
        || {
            let src = "public function f(c: bool): i64 {\n  if (c) { return 1; }\n}\n";
            rejects(
                src,
                "EN0427",
                "3:1",
                "`f` may end without returning an `i64`",
            );
        },
    );
    h.case(
        "typeck/no EN0427 when every path returns or loops forever",
        || {
            accepts(
                "public function f(c: bool): i64 { if (c) { return 1; } else { return 2; } }\n",
            );
            accepts("public function f(): i64 { while (true) {} }\n");
            accepts("public function f(): i64 { for (;;) {} }\n");
            accepts("public function f(c: bool): i64 { return match (c) { default => 1 }; }\n");
            accepts("public function f(): void {}\n");
        },
    );
    h.case("typeck/a `break` makes a `while (true)` end", || {
        rejects(
            "public function f(): i64 { while (true) { break; } }\n",
            "EN0427",
            "1:52",
            "`f` may end without returning an `i64`",
        );
    });
    h.case(
        "typeck/an arrow's `return` does not end the enclosing body",
        || {
            rejects(
                "public function f(): i64 { const g = (): i64 => { return 1; }; }\n",
                "EN0427",
                "1:64",
                "`f` may end without returning an `i64`",
            );
        },
    );
    h.case(
        "typeck/falling off a `Result<void, E>` body is `return Ok();`",
        || {
            accepts("public function f(): Result<void, Failure> {}\n");
        },
    );
    h.case("typeck/`break outer` names the labelled loop", || {
        let r = accepts(
            "public function f(): void { outer: while (true) { while (true) { break outer; } } }\n",
        );
        let b = body(&r, "f");
        let StmtKind::While {
            id,
            body: outer_body,
            ..
        } = &b.root.stmts[0].kind
        else {
            panic!("a while")
        };
        assert_eq!(*id, LoopId(0));
        let StmtKind::While {
            id: inner,
            body: inner_body,
            ..
        } = &outer_body.stmts[0].kind
        else {
            panic!("an inner while")
        };
        assert_eq!(*inner, LoopId(1));
        assert_eq!(inner_body.stmts[0].kind, StmtKind::Break(LoopId(0)));
    });
    h.case(
        "typeck/an `if` with a `return` in one branch leaves the other reachable",
        || {
            rejects(
                "public function f(c: bool): i64 { if (c) { return 1; } else { } }\n",
                "EN0427",
                "1:65",
                "`f` may end without returning an `i64`",
            );
        },
    );
}

// ---------------------------------------------------------------------------------
// What a body is (plan c.1, c.4, D6).

fn bodies(h: &mut Harness) {
    h.case(
        "typeck/statements: `args` and the top-level variables are `TopVar`s",
        || {
            let r = accepts("let count = 1;\nconst name = \"Ada\";\nconsole.log(count);\n");
            let program = r.program.as_ref().expect("checked");
            let b = program.statements.as_ref().expect("a statements body");
            let kinds: Vec<(String, LocalKind)> = b
                .locals
                .iter()
                .map(|l| (l.name.map(|n| n.to_string()).unwrap_or_default(), l.kind))
                .collect();
            assert_eq!(
                kinds,
                vec![
                    ("args".to_owned(), LocalKind::TopVar(TopVar(0))),
                    ("count".to_owned(), LocalKind::TopVar(TopVar(1))),
                    ("name".to_owned(), LocalKind::TopVar(TopVar(2))),
                ]
            );
            assert_eq!(
                r.tcx.ty_string(b.locals.iter().next().expect("args").ty),
                "string[]"
            );
        },
    );
    h.case("typeck/statements: `return 3;` sets the exit code", || {
        accepts("console.log(1);\nreturn 3;\n");
    });
    h.case(
        "typeck/an unannotated constant takes its initialiser's type",
        || {
            let r = accepts("public const N = 3;\npublic const M: u8 = 4;\n");
            assert_eq!(
                r.tcx.item_ty(r.def("src/main::N")),
                Some(r.tcx.common().i32)
            );
            rejects(
                "public const M: u8 = 300;\n",
                "EN0411",
                "1:22",
                "`300` doesn't fit `u8`",
            );
        },
    );
    h.case(
        "typeck/a parameter default is typed at its parameter (D6)",
        || {
            let r = accepts("public function f(x: i64 = 3, y?: i64): i64 { return x; }\n");
            let b = body(&r, "f");
            // `y?: i64` is `y: i64 | null = null` (S:829): its default is explicit.
            assert_eq!(b.param_defaults.len(), 2);
            let (local, value) = &b.param_defaults[0];
            assert_eq!(*local, b.params[0]);
            assert_eq!(
                value.kind,
                ExprKind::Const(ConstValue::Int(3, r.tcx.common().i64))
            );
            let (local, value) = &b.param_defaults[1];
            assert_eq!(*local, b.params[1]);
            assert_eq!(value.kind, ExprKind::NullLit);
            assert!(matches!(
                r.tcx.kind(value.ty),
                enrang_hir::TyKind::Nullable(_)
            ));
        },
    );
    h.case("typeck/a parameter property is stored before the written body (S:583)", || {
        let r = accepts(
            "public class User {\n  public constructor(public name: string, n: i64) { const k = n; }\n}\n",
        );
        let def = r.def("src/main::User::#ctor");
        let program = r.program.as_ref().expect("checked");
        let b = &program.bodies[&def];
        let StmtKind::Expr(store) = &b.root.stmts[0].kind else {
            panic!("a store first")
        };
        let ExprKind::Assign { target, value, op: None } = &store.kind else {
            panic!("an assignment")
        };
        assert!(matches!(target.kind, ExprKind::Field(..)));
        assert!(matches!(value.kind, ExprKind::Local(_)));
        assert!(matches!(b.root.stmts[1].kind, StmtKind::Let { .. }));
    });
    h.case("typeck/a test body's annotation is `void` or `Result<void, E>`", || {
        let r = run(&[
            ("src/main.en", "public function g(): i64 { return 1; }\n"),
            (
                "src/main.test.en",
                "test(\"bad\", (): i64 => { return 1; });\ntest(\"good\", (): Result<void, Failure> => {});\n",
            ),
        ]);
        assert_eq!(r.codes(), vec!["EN0401"], "{}", r.rendered());
        assert_eq!(
            r.messages(),
            vec!["a test returns `void` or `Result<void, E>`, not `i64`"]
        );
    });
    h.case(
        "typeck/a type written in a body is lowered there (EN0302)",
        || {
            let r = check("public function f(): void { const x: Strng = 1; }\n");
            assert_eq!(r.codes(), vec!["EN0302"], "{}", r.rendered());
        },
    );
}

// ---------------------------------------------------------------------------------
// Reachability: `continue` and loops in dead code (S:1137).

fn reachability(h: &mut Harness) {
    h.case(
        "typeck/a `continue` reaches a do-while's condition: EN0427 when it may be false",
        || {
            rejects(
                "public function f(x: bool, c: bool): i32 { do { if (x) { continue; } return 1; } while (c); }\n",
                "EN0427",
                "1:93",
                "`f` may end without returning an `int`",
            );
        },
    );
    h.case(
        "typeck/a labelled `continue` reaches its do-while's condition too",
        || {
            rejects(
                "public function f(x: bool, c: bool): i32 { outer: do { while (x) { continue outer; } return 1; } while (c); }\n",
                "EN0427",
                "1:109",
                "`f` may end without returning an `int`",
            );
        },
    );
    h.case(
        "typeck/a `continue` arm reaches a do-while's condition",
        || {
            rejects(
                "public function f(x: i64, c: bool): i32 { do { match (x) { 1 => continue, default => {} } return 1; } while (c); }\n",
                "EN0427",
                "1:114",
                "`f` may end without returning an `int`",
            );
        },
    );
    h.case(
        "typeck/a do-while whose body always returns ends the function",
        || {
            accepts("public function a(c: bool): i64 { do { return 1; } while (c); }\n");
            accepts(
                "public function b(x: bool): i64 { do { if (x) { continue; } return 1; } while (true); }\n",
            );
        },
    );
    h.case(
        "typeck/a loop after a `return` is never reached: no EN0427",
        || {
            accepts("public function a(c: bool): i32 { return 1; while (c) { } }\n");
            accepts("public function b(c: bool): i32 { return 1; for (; c; ) { } }\n");
            accepts("public function d(c: bool): i32 { return 1; do { } while (c); }\n");
            accepts("public function e(xs: &i64[]): i32 { return 1; for (const x of xs) { } }\n");
        },
    );
}

// ---------------------------------------------------------------------------------
// An operand still an `Int` variable at an integer-only or signed use (S:726).

fn deferred_numerics(h: &mut Harness) {
    h.case(
        "typeck/a variable a later use makes a float is EN0403 at each bitwise use",
        || {
            assert_eq!(
                all("public function f(): void { let a = 5; const b = a & 1; const s = a << 2; const n = ~a; const c: f64 = a; }\n"),
                vec![
                    diag("EN0403", "1:50", "`&` needs integers, found `f64`"),
                    diag("EN0403", "1:67", "`<<` needs integers, found `f64`"),
                    diag("EN0403", "1:86", "`~` needs integers, found `f64`"),
                ]
            );
        },
    );
    h.case(
        "typeck/EN0403 is the same whichever statement decides the float first",
        || {
            rejects(
                "public function f(): void { let a = 5; const c: f64 = a; const b = a & 1; }\n",
                "EN0403",
                "1:68",
                "`&` needs integers, found `f64`",
            );
            rejects(
                "public function f(): void { let a = 5; const b = a & 1; const c: f64 = a; }\n",
                "EN0403",
                "1:50",
                "`&` needs integers, found `f64`",
            );
            rejects(
                "public function f(): void { let a = 5; a &= 1; const c: f64 = a; }\n",
                "EN0403",
                "1:40",
                "`&` needs integers, found `f64`",
            );
        },
    );
    h.case(
        "typeck/an index a later use makes a float is EN0405",
        || {
            rejects(
                "public function f(xs: i64[]): i64 { let i = 0; const v = xs[i]; const g: f64 = i; return v; }\n",
                "EN0405",
                "1:61",
                "an index must be an integer, found `f64`",
            );
        },
    );
    h.case(
        "typeck/a variable that stays an integer passes its integer-only uses",
        || {
            let r = accepts(
                "public function f(xs: i64[]): void { let a = 5; const b = a & 1; const c: i64 = a; let i = 0; const v = xs[i]; }\n",
            );
            assert_eq!(local_ty(&r, "f", "b"), "i64");
            assert_eq!(local_ty(&r, "f", "i"), "isize");
        },
    );
    h.case(
        "typeck/`-` of a variable a later use makes unsigned is EN0420, in either order",
        || {
            for src in [
                "public function f(): void { let a = 5; const b = -a; const c: u8 = a; }\n",
                "public function f(): void { let a = 5; const c: u8 = a; const b = -a; }\n",
            ] {
                let (code, _, message) = one(src);
                assert_eq!(
                    (code.as_str(), message.as_str()),
                    ("EN0420", "`-` needs a signed number, found `u8`"),
                    "{src}"
                );
            }
            let (_, at, _) =
                one("public function f(): void { let a = 5; const b = -a; const c: u8 = a; }\n");
            assert_eq!(at, "1:50");
        },
    );
}

// ---------------------------------------------------------------------------------
// An unannotated constant read before its own turn (S:756).

fn constant_order(h: &mut Harness) {
    h.case(
        "typeck/a constant read before its declaration has its initialiser's type",
        || {
            rejects(
                "public function f(): i64 { const x: string = C; return 1; }\npublic const C = 7;\n",
                "EN0401",
                "1:46",
                "mismatched types: expected `string`, found `int`",
            );
            rejects(
                "public const B = A + 1;\npublic const A = 5;\npublic function f(): void { const x: string = B; }\n",
                "EN0401",
                "3:47",
                "mismatched types: expected `string`, found `int`",
            );
        },
    );
    h.case(
        "typeck/an early-typed constant keeps one body, in the program",
        || {
            let r = accepts("public const B = A + 1;\npublic const A = 5;\npublic function f(): void { const x = B; }\n");
            assert_eq!(local_ty(&r, "f", "x"), "int");
            let program = r.program.as_ref().expect("checked");
            for name in ["A", "B"] {
                let def = r.def(&format!("src/main::{name}"));
                assert!(program.bodies.contains_key(&def), "{name}");
                assert_eq!(r.tcx.ty_string(r.tcx.item_ty(def).expect("typed")), "int");
            }
        },
    );
    h.case(
        "typeck/unannotated constants that read each other are EN0412 once",
        || {
            let r = check("public const A = B;\npublic const B = A;\n");
            assert_eq!(
                r.rendered(),
                "error[EN0412]: constant cycle: `A` uses `B`, which uses `A`
 --> src/main.en:1:14
  |
1 | public const A = B;
  |              ^ `A` depends on its own value
  |
  = explain: run `enrang explain EN0412`

error: aborting due to 1 previous error
"
            );
            rejects(
                "public const A = A + 1;\n",
                "EN0412",
                "1:14",
                "constant cycle: `A` uses `A`",
            );
        },
    );
}

// ---------------------------------------------------------------------------------
// A string literal where a `&string` is met with no coercion site (S:827, S:962).

fn literal_references(h: &mut Harness) {
    h.case(
        "typeck/SPEC's `greeting ?? \"hello\"` takes the literal's descriptor (S:827)",
        || {
            let src = "private function greet(name: &string, greeting?: &string): string { return `${greeting ?? \"hello\"}, ${name}!`; }\n";
            let r = run_with(&[("src/main.en", src)], LibSource::Embedded, "x86_64-linux");
            r.clean();
            let b = body(&r, "greet");
            let hello = expr_at(&r, &b, "\"hello\"");
            assert_eq!(hello.adjust, vec![Adjust::LiteralDescriptor]);
            let coalesce = expr_at(&r, &b, "greeting ?? \"hello\"");
            assert_eq!(ty_of(&r, coalesce.ty), "&string");
        },
    );
    h.case(
        "typeck/a ternary or `match` of a `&string` and a literal is a `&string`",
        || {
            for src in [
                "public function f(c: bool, name: &string): void { const label = c ? name : \"none\"; }\n",
                "public function f(c: bool, name: &string): void { const label = c ? \"none\" : name; }\n",
                "public function f(c: i64, name: &string): void { const label = match (c) { 1 => name, default => \"none\" }; }\n",
            ] {
                let r = accepts(src);
                assert_eq!(local_ty(&r, "f", "label"), "&string", "{src}");
                let b = body(&r, "f");
                assert_eq!(expr_at(&r, &b, "\"none\"").adjust, vec![Adjust::LiteralDescriptor]);
            }
        },
    );
    h.case(
        "typeck/a literal beside a `&string | null` branch is wrapped too",
        || {
            let r = accepts("public function f(c: bool, name: &string | null): void { const label = c ? name : \"none\"; }\n");
            assert_eq!(local_ty(&r, "f", "label"), "&string | null");
            let b = body(&r, "f");
            assert_eq!(
                expr_at(&r, &b, "\"none\"").adjust,
                vec![Adjust::LiteralDescriptor, Adjust::WrapNullRef]
            );
        },
    );
    h.case("typeck/two literal branches stay a `string`", || {
        let r = accepts("public function f(c: bool): void { const t = c ? \"a\" : \"b\"; }\n");
        assert_eq!(local_ty(&r, "f", "t"), "string");
        let b = body(&r, "f");
        assert!(expr_at(&r, &b, "\"a\"").adjust.is_empty());
    });
}

// ---------------------------------------------------------------------------------
// Names as arm values (S:1132-1133).

fn arm_names(h: &mut Harness) {
    h.case("typeck/a local as an arm value is EN0504", || {
        let r = check("public function f(x: i64, y: i64): i64 { return match (x) { y => 1, default => 2 }; }\n");
        assert_eq!(r.codes(), vec!["EN0504"], "{}", r.rendered());
        assert_eq!(r.messages(), vec!["`y` can't match an `i64`"]);
        assert_eq!(
            r.diags[0].helps[0].message,
            "to test conditions, write `match (true)` with a condition in each arm"
        );
    });
    h.case("typeck/a name in no scope as an arm value is EN0301", || {
        rejects(
            "public function f(x: i64): i64 { return match (x) { nope => 1, default => 2 }; }\n",
            "EN0301",
            "1:53",
            "cannot find `nope` in this scope",
        );
    });
    h.case(
        "typeck/under `match (true)` a name or a path is a condition",
        || {
            let r = accepts(
                "public class P { public ok: bool; }\npublic function f(flag: bool, p: &P): i64 { const a = match (true) { flag => 1, default => 2 }; return match (true) { p.ok => 1, default => a }; }\n",
            );
            let b = body(&r, "f");
            let conds: Vec<ExprKind> = exprs(&b)
                .into_iter()
                .filter_map(|e| match e.kind {
                    ExprKind::Match { arms, .. } => match &arms[0].values[0] {
                        ArmValue::Cond(c) => Some(c.kind.clone()),
                        other => panic!("{other:?}"),
                    },
                    _ => None,
                })
                .collect();
            assert!(matches!(conds[0], ExprKind::Local(_)), "{:?}", conds[0]);
            assert!(matches!(conds[1], ExprKind::Field(..)), "{:?}", conds[1]);
            rejects(
                "public function f(): i64 { return match (true) { nope => 1, default => 2 }; }\n",
                "EN0301",
                "1:50",
                "cannot find `nope` in this scope",
            );
        },
    );
}

// ---------------------------------------------------------------------------------
// Casts whose operand holds a variable (S:703).

fn deferred_casts(h: &mut Harness) {
    h.case(
        "typeck/a variable cast to a pointer defaults first: `int` has no row (EN0404)",
        || {
            rejects(
                "public function f(): void { let a = 0xB8000; const p = a as *u16; }\n",
                "EN0404",
                "1:56",
                "`int` can't be converted to `*u16` with `as`",
            );
        },
    );
    h.case("typeck/`&x as *T` waits for `x`'s type", || {
        for (src, x) in [
            (
                "public function f(): void { let x = 5; const p = &x as *i32; }\n",
                "int",
            ),
            (
                "public function f(): void { let x = 5; const p = &x as *u8; const y: u8 = x; }\n",
                "u8",
            ),
        ] {
            let r = accepts(src);
            assert_eq!(local_ty(&r, "f", "x"), x);
            let b = body(&r, "f");
            let cast = exprs(&b)
                .into_iter()
                .find(|e| matches!(e.kind, ExprKind::Cast(..)))
                .expect("a cast");
            assert!(matches!(cast.kind, ExprKind::Cast(_, CastKind::RefToRaw)));
        }
    });
    h.case(
        "typeck/a cast's kind is chosen once its variable is a float",
        || {
            let r = accepts(
                "public function f(): void { let x = 5; const y = x as i64; const z: f64 = x; }\n",
            );
            let b = body(&r, "f");
            let cast = expr_at(&r, &b, "x as i64");
            assert!(
                matches!(cast.kind, ExprKind::Cast(_, CastKind::FloatToInt)),
                "{:?}",
                cast.kind
            );
        },
    );
    h.case("typeck/a literal cast to a pointer is a `usize`", || {
        let r = accepts("public function f(): void { const p = 0xB8000 as *u16; }\n");
        let b = body(&r, "f");
        let ExprKind::Cast(operand, kind) = expr_at(&r, &b, "0xB8000 as *u16").kind else {
            panic!("a cast");
        };
        assert_eq!(kind, CastKind::UsizeToRaw);
        assert_eq!(
            operand.kind,
            ExprKind::Const(ConstValue::Int(0xB8000, r.tcx.common().usize))
        );
    });
    h.case("typeck/a variable cast to `bool` keeps its help", || {
        let r = check("public function f(): void { let a = 5; const b = a as bool; }\n");
        assert_eq!(r.codes(), vec!["EN0404"]);
        assert_eq!(
            r.messages(),
            vec!["`int` can't be converted to `bool` with `as`"]
        );
        assert_eq!(r.diags[0].helps[0].message, "compare it instead: `a != 0`");
    });
}

// ---------------------------------------------------------------------------------
// By-value object parameters (S:601, T:861 F5).

fn shape_parameters(h: &mut Harness) {
    h.case(
        "typeck/a by-value object parameter returned is EN0440 `may have more fields`",
        || {
            let src =
                "public function keepName(x: { name: string }): { name: string } { return x; }\n";
            rejects(
                src,
                "EN0440",
                "1:74",
                "`x` may have more fields than `{ name: string }`",
            );
            assert_eq!(
                helps(src),
                vec![(
                    "build the smaller object: `{ name: x.name }`".to_owned(),
                    vec![]
                )]
            );
        },
    );
    h.case(
        "typeck/two by-value object parameters are two types (EN0401)",
        || {
            rejects(
                "public function rename(let a: { name: string }, b: { name: string }): void { a = b; }\n",
                "EN0401",
                "1:82",
                "`b` may hold another class than `a`",
            );
        },
    );
}

// ---------------------------------------------------------------------------------
// One `&` stripped as a `Deref` node before a projection (plan d.8).

fn places(h: &mut Harness) {
    h.case(
        "typeck/a tuple part, an element and a parameter property go through `Deref`",
        || {
            let r = accepts(
                "public class P { public constructor(public x: i64) {} }\npublic function f(rt: &[i64, string], r: &i64[]): i64 { return rt[0] + r[0]; }\n",
            );
            let b = body(&r, "f");
            let ExprKind::Field(base, _) = expr_at(&r, &b, "rt[0]").kind else {
                panic!("a field");
            };
            assert!(matches!(base.kind, ExprKind::Deref(_)), "{:?}", base.kind);
            assert_eq!(ty_of(&r, base.ty), "[i64, string]");
            let ExprKind::Index(base, _) = expr_at(&r, &b, "r[0]").kind else {
                panic!("an index");
            };
            assert!(matches!(base.kind, ExprKind::Deref(_)), "{:?}", base.kind);
            assert_eq!(ty_of(&r, base.ty), "i64[]");
            let def = r.def("src/main::P::#ctor");
            let ctor = Arc::clone(r.program.as_ref().unwrap().bodies.get(&def).unwrap());
            let target = exprs(&ctor)
                .into_iter()
                .find_map(|e| match e.kind {
                    ExprKind::Assign { target, .. } => Some(*target),
                    _ => None,
                })
                .expect("the parameter property's store");
            let ExprKind::Field(base, _) = target.kind else {
                panic!("a field");
            };
            assert!(matches!(base.kind, ExprKind::Deref(_)), "{:?}", base.kind);
            assert_eq!(ty_of(&r, base.ty), "P");
        },
    );
}

// ---------------------------------------------------------------------------------
// `return;` (S:677, S:1137, S:1143).

fn bare_returns(h: &mut Harness) {
    h.case(
        "typeck/`return;` where a value is due is EN0401 at the `return`",
        || {
            let r = check("public function f(): i64 { return; }\n");
            assert_eq!(
                r.rendered(),
                "error[EN0401]: mismatched types: expected `i64`, found `void`
 --> src/main.en:1:28
  |
1 | public function f(): i64 { return; }
  |                            ^^^^^^ this `return` gives no value
  |                      --- `i64` is required by the return type
  |
  = explain: run `enrang explain EN0401`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "typeck/`return;` in a `void` function and among statements compiles",
        || {
            accepts("public function f(c: bool): void { if (c) { return; } }\n");
            accepts("let a: i64 = 1;\nif (a == 1) { return; }\n");
        },
    );
}

// ---------------------------------------------------------------------------------
// Behaviour the mutation gate showed untested.

fn pinned(h: &mut Harness) {
    h.case("typeck/`n ?? n` keeps `n`'s nullable type", || {
        let r = accepts("public function f(n: i64 | null): void { const b = n ?? n; }\n");
        assert_eq!(local_ty(&r, "f", "b"), "i64 | null");
    });
    h.case(
        "typeck/a `never` branch with no expected type leaves the other's type",
        || {
            let r = accepts(
                "public function f(c: bool): void { const a = c ? 1 : panic(\"x\"); const b = match (c) { true => 2, default => panic(\"y\") }; }\n",
            );
            assert_eq!(local_ty(&r, "f", "a"), "int");
            assert_eq!(local_ty(&r, "f", "b"), "int");
        },
    );
    h.case(
        "typeck/C21 reaches a base two levels up, through `&` and `Box`",
        || {
            let src = "public class A { public constructor() {} }
public class B extends A { public constructor() { super(); } }
public class C extends B { public constructor() { super(); } }
public function f(c: &C, bx: Box<C>): void { const a: &A = c; const b: Box<A> = bx; }
";
            let r = accepts(src);
            let b = body(&r, "f");
            assert_eq!(expr_at(&r, &b, "c").adjust, vec![Adjust::Upcast]);
            assert_eq!(expr_at(&r, &b, "bx").adjust, vec![Adjust::Upcast]);
        },
    );
    h.case(
        "typeck/EN0401 at an argument names the parameter that set the type",
        || {
            let r = check(
                "public function g(x: i64): void {}\npublic function f(): void { g(true); }\n",
            );
            assert_eq!(r.codes(), vec!["EN0401"]);
            assert_eq!(
                r.messages(),
                vec!["mismatched types: expected `i64`, found `bool`"]
            );
            let secondary = &r.diags[0].secondary[0];
            assert_eq!(secondary.text, "`i64` is required by this parameter");
            assert_eq!(r.map.text(secondary.span), "x: i64");
        },
    );
    h.case(
        "typeck/EN0411 offers `: u64` for a literal only `u64` holds",
        || {
            let src = "public function f(): void { const huge = 10_000_000_000_000_000_000; }\n";
            rejects(
                src,
                "EN0411",
                "1:42",
                "`10_000_000_000_000_000_000` doesn't fit `int`",
            );
            assert_eq!(
                fixed(src),
                "public function f(): void { const huge: u64 = 10_000_000_000_000_000_000; }\n"
            );
        },
    );
    h.case(
        "typeck/a nullable value or `null` into a non-null reference variable is EN0401",
        || {
            assert_eq!(
                all("public function f(r: &i64, m: &i64 | null): void { let q = r; q = null; q = m; }\n"),
                vec![
                    diag("EN0401", "1:67", "mismatched types: expected `&i64`, found `null`"),
                    diag("EN0401", "1:77", "mismatched types: expected `&i64`, found `&i64 | null`"),
                ]
            );
        },
    );
    h.case(
        "typeck/a value into a nullable reference variable is EN0422",
        || {
            let src = "public function f(r: &i64 | null, v: i64): void { let q: &i64 | null = r; q = v; }\n";
            rejects(
                src,
                "EN0422",
                "1:75",
                "`q` is a reference: write through it with `*q`",
            );
            let messages: Vec<String> = helps(src).into_iter().map(|(m, _)| m).collect();
            assert_eq!(
                messages,
                vec![
                    "write through it once it is not `null`: `*q`",
                    "or point it at another place: `&v`",
                ]
            );
        },
    );
    h.case(
        "typeck/a bracket literal longer than its tuple is EN0401",
        || {
            rejects(
                "public function f(): void { const g: [i64, i64] = [1, 2, 3]; }\n",
                "EN0401",
                "1:51",
                "mismatched types: expected `[i64, i64]`, found `[int, int, int]`",
            );
        },
    );
    h.case(
        "typeck/EN0427 names the result type it is required by",
        || {
            let r = check("public function f(c: bool): i64 { if (c) { return 1; } }\n");
            assert_eq!(r.codes(), vec!["EN0427"]);
            let secondary = &r.diags[0].secondary[0];
            assert_eq!(secondary.text, "`i64` is required by the return type");
            assert_eq!(r.map.text(secondary.span), "i64");
        },
    );
    h.case(
        "typeck/a fixed array at a `&T[]` parameter names the parameter (S:606)",
        || {
            let r = check("public function checksum(data: &u8[]): u32 { return 0; }\npublic function f(): void { let sector: u8[8] = [0, 0, 0, 0, 0, 0, 0, 0]; checksum(&sector); }\n");
            assert_eq!(r.codes(), vec!["EN0401"]);
            assert_eq!(r.messages(), vec!["a fixed array can't grow"]);
            assert_eq!(
                r.diags[0].helps[0].message,
                "if `checksum` only reads or sets elements, take `data: &Slice<u8>`; to let it grow, make `sector` a `u8[]`"
            );
        },
    );
    h.case("typeck/`-0` fits an unsigned type", || {
        let r = accepts("public function f(): void { const p: u8 = -0; }\n");
        let b = body(&r, "f");
        assert_eq!(
            expr_at(&r, &b, "-0").kind,
            ExprKind::Const(ConstValue::Int(0, r.tcx.common().u8))
        );
    });
    h.case(
        "typeck/a literal compared with a nullable takes its payload's type",
        || {
            rejects(
                "public function f(n: i64 | null): bool { return n == 5; }\n",
                "EN0401",
                "1:54",
                "mismatched types: expected `i64 | null`, found `i64`",
            );
        },
    );
    h.case(
        "typeck/an integer literal at `f32` is rounded once, from the integer",
        || {
            let r = accepts("public function f(): void { const d: f32 = 1152921573326323713; }\n");
            let b = body(&r, "f");
            assert_eq!(
                expr_at(&r, &b, "1152921573326323713").kind,
                ExprKind::Const(ConstValue::Float(0x5D80_0001, r.tcx.common().f32))
            );
        },
    );
    h.case("typeck/a literal on the left of a string-literal union", || {
        let r = accepts(
            "public type Direction = \"left\" | \"right\";\npublic function f(d: Direction): bool { return \"left\" == d; }\n",
        );
        let b = body(&r, "f");
        assert!(matches!(
            expr_at(&r, &b, "\"left\"").kind,
            ExprKind::VariantLit { variant: VariantIdx(0), .. }
        ));
    });
    h.case(
        "typeck/G05's `.toString()` help parenthesises an operation",
        || {
            let src = "public function f(a: i64): void { const s: string = a + 1; }\n";
            assert_eq!(
                fixed(src),
                "public function f(a: i64): void { const s: string = (a + 1).toString(); }\n"
            );
            let src = "public function f(a: i64): void { const s: string = a; }\n";
            assert_eq!(
                fixed(src),
                "public function f(a: i64): void { const s: string = a.toString(); }\n"
            );
        },
    );
    h.case(
        "typeck/a mismatch between two types that print alike says so",
        || {
            let r = run(&[
                (
                    "src/main.en",
                    "import * as u from \"./u\";\npublic class Point { public x: i64; }\npublic function f(q: &u.Point): void { const p: &Point = q; }\n",
                ),
                ("src/u.en", "public class Point { public x: i64; }\n"),
            ]);
            assert_eq!(r.codes(), vec!["EN0401"], "{}", r.rendered());
            assert_eq!(
                r.messages(),
                vec!["mismatched types: expected `&Point`, found `&Point`"]
            );
            let notes: Vec<&str> = r.diags[0].entries.iter().map(|e| e.text.as_str()).collect();
            assert_eq!(
                notes,
                vec!["these are two different types, both written `&Point` here"]
            );
        },
    );
    h.case("typeck/one rejection reports EN0410 once", || {
        assert_eq!(
            all("public function f(): void { let q; q = null; }\n"),
            vec![diag("EN0410", "1:40", "cannot infer the type of `null`")]
        );
        assert_eq!(
            all("public function f(): void { const [p, q] = [null, 1]; }\n"),
            vec![diag("EN0410", "1:45", "cannot infer the type of `null`")]
        );
    });
}

// ---------------------------------------------------------------------------------
// G22 (SPEC 14), byte for byte.

fn g22(h: &mut Harness) {
    h.case("typeck/G22 byte-exact through load and analyze", || {
        let spec = std::fs::read_to_string(workspace_root().join("docs/SPEC.md")).expect("SPEC");
        let cases = extract_cases(&spec).expect("SPEC's cases extract");
        let case = cases.iter().find(|c| c.id == "G22").expect("G22");
        let file = &case.files[0];
        let r = run_with(
            &[(file.name.as_str(), file.contents.as_str())],
            LibSource::Embedded,
            enrang_target::host_target(),
        );
        let actual = r.rendered();
        assert!(
            actual == case.stderr.text,
            "{}",
            line_diff(&case.stderr.text, &actual)
        );
        assert_eq!(case.exit, 1);
        assert!(r.diags.iter().any(|d| d.severity.fails()));
    });
    h.case("typeck/G22's fix-it compiles", || {
        accepts("public function snapshot<T extends Clone>(xs: &T[]): T[] { return [...xs]; }\n");
        let r = check("public function snapshot<T>(xs: &T[]): T[] { return [...xs]; }\n");
        assert_eq!(r.codes(), vec!["EN0438"]);
        assert!(matches!(r.tcx.kind(r.tcx.common().i32), TyKind::Int(_)));
    });
}
