//! Narrowing as flow state (owner 4B; plan d.10, g.2 "Narrowing and `for...of`";
//! SPEC 4.8, 6; A:898-900): facts from conditions and `match` arms, kills only on a
//! visible change (N2), records of every other reference to a proper prefix of a
//! fact's path or to the path at its nullable type, O6 order at calls and
//! assignments, and the prescans of loops and arrows.
//!
//! Each case is a program run through `load` and `analyze`; a rejecting case checks
//! every diagnostic's code, primary line and column, the primary span's text and the
//! message, an accepting one that nothing is reported and, where the rule is about
//! the HIR, the typed body: its `NarrowedPayload`s, facts and records. The helpers
//! here are shared with `forof.rs` and `pattern.rs`.

#[path = "../../src/passes/walk.rs"]
mod walk;

use std::sync::Arc;

use enrang_hir::{Block, Body, Expr, ExprKind, Fact, ForSource, RecordKind, StmtKind, VariantIdx};
use enrang_sema::LibSource;
use enrang_testkit::Harness;

use crate::support::{Run, run, run_with};

// ---------------------------------------------------------------------------------
// Helpers.

/// Checks `src` as `src/main.en` with the suite's fake library.
pub fn check(src: &str) -> Run {
    run(&[("src/main.en", src)])
}

/// Checks `src` as `src/main.en` with the embedded library.
pub fn check_lib(src: &str) -> Run {
    run_with(&[("src/main.en", src)], LibSource::Embedded, "x86_64-linux")
}

/// One diagnostic as the cases write it: code, `line:col` of the primary span, the
/// primary span's text and the message.
pub type Found = (String, String, String, String);

/// Every diagnostic of `r`, in order.
pub fn found(r: &Run) -> Vec<Found> {
    r.diags
        .iter()
        .map(|d| {
            let loc = r.map.loc(d.primary.span.lo);
            (
                d.code.name().to_owned(),
                format!("{}:{}", loc.line, loc.col),
                r.map.text(d.primary.span).to_owned(),
                d.message.clone(),
            )
        })
        .collect()
}

/// `(code, at, text, message)` as [`found`] gives it.
pub fn d(code: &str, at: &str, text: &str, message: &str) -> Found {
    (
        code.to_owned(),
        at.to_owned(),
        text.to_owned(),
        message.to_owned(),
    )
}

/// Asserts `r` reported exactly `expected`, in order.
pub fn expect(r: &Run, expected: &[Found]) {
    assert_eq!(found(r), expected, "{}", r.rendered());
}

/// Asserts `src` reports exactly `expected` with the fake library.
pub fn rejects(src: &str, expected: &[Found]) -> Run {
    let r = check(src);
    expect(&r, expected);
    r
}

/// Asserts `src` checks clean with the fake library.
pub fn accepts(src: &str) -> Run {
    let r = check(src);
    r.clean();
    r
}

/// Asserts `src` checks clean with the embedded library.
pub fn accepts_lib(src: &str) -> Run {
    let r = check_lib(src);
    r.clean();
    r
}

/// The body of function `name` of `src/main`.
pub fn body(r: &Run, name: &str) -> Arc<Body> {
    let def = r.def(&format!("src/main::{name}"));
    let program = r.program.as_ref().expect("checked");
    Arc::clone(program.bodies.get(&def).expect("a body"))
}

/// Every statement of `b`, nested blocks included, outer first.
pub fn stmts(b: &Block) -> Vec<&StmtKind> {
    let mut out = Vec::new();
    collect_stmts(b, &mut out);
    out
}

fn collect_stmts<'b>(b: &'b Block, out: &mut Vec<&'b StmtKind>) {
    for s in &b.stmts {
        out.push(&s.kind);
        match &s.kind {
            StmtKind::If { then_, else_, .. } => {
                collect_stmts(then_, out);
                if let Some(e) = else_ {
                    collect_stmts(e, out);
                }
            }
            StmtKind::While { body, .. }
            | StmtKind::DoWhile { body, .. }
            | StmtKind::For { body, .. }
            | StmtKind::ForOf { body, .. }
            | StmtKind::Block(body)
            | StmtKind::Unsafe(body) => collect_stmts(body, out),
            _ => {}
        }
    }
}

/// Every `for...of` source of `b`, in order.
pub fn for_sources(b: &Body) -> Vec<&ForSource> {
    stmts(&b.root)
        .into_iter()
        .filter_map(|s| match s {
            StmtKind::ForOf { source, .. } => Some(source),
            _ => None,
        })
        .collect()
}

/// The type of the local `name` of `b`, as messages print it (the first one of that
/// name).
pub fn local_ty(r: &Run, b: &Body, name: &str) -> String {
    let local = b
        .locals
        .iter()
        .find(|l| l.name.is_some_and(|n| n.as_str() == name))
        .unwrap_or_else(|| panic!("no local `{name}`"));
    r.tcx.ty_string(local.ty)
}

/// Every expression of `b`, parents first.
pub fn exprs(b: &Body) -> Vec<Expr> {
    let mut out = Vec::new();
    walk::for_each_expr(b, &mut |e| out.push(e.clone()));
    out
}

/// The records of `b` as `(kind, the reference's text, the text of the test that
/// made its fact)`.
pub fn records(r: &Run, b: &Body) -> Vec<(RecordKind, String, String)> {
    b.records
        .iter()
        .map(|rec| {
            (
                rec.kind,
                r.map.text(rec.span).to_owned(),
                r.map.text(b.facts[rec.fact].span).to_owned(),
            )
        })
        .collect()
}

/// `(kind, reference, test)` as [`records`] gives it.
pub fn rec(kind: RecordKind, at: &str, test: &str) -> (RecordKind, String, String) {
    (kind, at.to_owned(), test.to_owned())
}

/// The message of EN0303 for `name` on a `ty` that may be `null`.
pub fn no_member(ty: &str, name: &str) -> String {
    format!("`{ty}` has no member `{name}`")
}

pub fn register(h: &mut Harness) {
    creation(h);
    arms(h);
    kills(h);
    records_cases(h);
    order(h);
    loops(h);
    arrows(h);
    shapes(h);
    review(h);
}

// ---------------------------------------------------------------------------------
// Where facts come from (S:741).

fn creation(h: &mut Harness) {
    h.case(
        "narrow/a loop's prescan kills on a move in its body",
        || {
            rejects(
                "public function f(p: string | null, c: bool): void {
  if (p != null) { while (c) { p.length(); const r = p; } }
  if (p != null) { for (const i of 0..3) { p.length(); const q = p; } }
}
",
                &[
                    d(
                        "EN0303",
                        "2:34",
                        "length",
                        &no_member("string | null", "length"),
                    ),
                    d(
                        "EN0303",
                        "3:46",
                        "length",
                        &no_member("string | null", "length"),
                    ),
                ],
            );
        },
    );
    h.case(
        "narrow/`p != null` narrows its then branch and `p == null` its else branch",
        || {
            accepts(
                "public function f(p: string | null): isize {
  if (p != null) { return p.length(); }
  return 0;
}
public function g(p: string | null): isize {
  if (p == null) { return 0; } else { return p.length(); }
}
",
            );
        },
    );
    h.case("narrow/a test narrows only the branch it holds in", || {
        let len = no_member("string | null", "length");
        rejects(
            "public function f(p: string | null): void {
  if (p != null) { } else { p.length(); }
  if (p == null) { p.length(); }
  p.length();
}
",
            &[
                d("EN0303", "2:31", "length", &len),
                d("EN0303", "3:22", "length", &len),
                d("EN0303", "4:5", "length", &len),
            ],
        );
    });
    h.case("narrow/`!` swaps a test's branches", || {
        rejects(
            "public function f(p: string | null): void {
  if (!(p == null)) { p.length(); }
  if (!(p != null)) { p.length(); }
}
",
            &[d(
                "EN0303",
                "3:25",
                "length",
                &no_member("string | null", "length"),
            )],
        );
    });
    h.case(
        "narrow/`&&` narrows left to right and `||` in its false branch",
        || {
            let len = no_member("string | null", "length");
            rejects(
                "public function f(p: string | null): isize {
  if (p != null && p.length() > 0) { p.length(); }
  if (p.length() > 0 && p != null) { }
  if (p != null || p.length() == 0) { }
  if (p == null || p.length() == 0) { return 0; }
  return p.length();
}
",
                &[
                    d("EN0303", "3:9", "length", &len),
                    d("EN0303", "4:22", "length", &len),
                ],
            );
            // `a && b` is false when `a` is, or when `b` is with `a` true; `a || b`
            // is true when `a` is, or when `b` is with `a` false.
            rejects(
                "public function f(p: string | null, c: bool): isize {
  if (p == null && c) { return 0; }
  if (p != null || c) { return p.length(); }
  return p.length();
}
",
                &[
                    d("EN0303", "3:34", "length", &len),
                    d("EN0303", "4:12", "length", &len),
                ],
            );
        },
    );
    h.case("narrow/an early exit in one branch narrows after the `if`", || {
        accepts(
            "public function f(p: string | null): isize { if (p == null) { return 0; } return p.length(); }
public function g(p: string | null): isize { if (p == null) { panic(\"no\"); } return p.length(); }
public function h(p: string | null, c: bool): void { while (c) { if (p == null) { break; } p.length(); } }
public function k(p: string | null, c: bool): void { while (c) { if (p == null) { continue; } p.length(); } }
",
        );
        rejects(
            "public function f(p: string | null): isize { if (p == null) { console.log(1); } return p.length(); }
",
            &[d(
                "EN0303",
                "1:90",
                "length",
                &no_member("string | null", "length"),
            )],
        );
    });
    h.case("narrow/a ternary narrows each branch", || {
        rejects(
            "public function f(p: string | null): void {
  const n = p != null ? p.length() : 0;
  const m = p == null ? p.length() : 0;
}
",
            &[d(
                "EN0303",
                "3:27",
                "length",
                &no_member("string | null", "length"),
            )],
        );
    });
    h.case(
        "narrow/an assignment tested in place narrows its target (S:741, A:898)",
        || {
            accepts(
                "public function readLine(): string | null { return null; }
public function f(): void {
  let line: string | null = null;
  while ((line = readLine()) != null) { console.log(line.length()); }
  if ((line = readLine()) != null) { line.length(); }
}
",
            );
        },
    );
    h.case(
        "narrow/branches join by intersection of their facts",
        || {
            accepts(
                "public function f(p: string | null, c: bool): isize {
  if (c) { if (p == null) { return 0; } } else { if (p == null) { return 1; } }
  return p.length();
}
",
            );
            rejects(
                "public function f(p: string | null, c: bool): isize {
  if (c) { if (p == null) { return 0; } }
  return p.length();
}
",
                &[d(
                    "EN0303",
                    "3:12",
                    "length",
                    &no_member("string | null", "length"),
                )],
            );
        },
    );
    h.case(
        "narrow/a field is narrowed through `this`, a reference and a `Box`",
        || {
            accepts(
                "public class H {
  public items: string | null = null;
  public size(): isize { if (this.items != null) { return this.items.length(); } return 0; }
}
public function f(h: &H, b: Box<H>): void {
  if (h.items != null) { h.items.length(); }
  if (b.items != null) { b.items.length(); }
}
",
            );
        },
    );
    h.case(
        "narrow/elements and call results are never narrowed (S:739)",
        || {
            let len = no_member("string | null", "length");
            rejects(
                "public function get(): string | null { return null; }
public function f(xs: (string | null)[]): void {
  if (xs[0] != null) { xs[0].length(); }
  if (get() != null) { get().length(); }
}
",
                &[
                    d("EN0303", "3:30", "length", &len),
                    d("EN0303", "4:30", "length", &len),
                ],
            );
        },
    );
    h.case(
        "narrow/a nullable `&T` is narrowed to the reference",
        || {
            accepts(
                "public function f(r: &string | null): isize {
  if (r != null) { return r.length(); }
  return 0;
}
",
            );
        },
    );
}

// ---------------------------------------------------------------------------------
// `match` arms (S:1133-1135).

const SHAPE: &str = "public enum Shape { Circle { r: f64 }, Named { name: string }, Empty }\n";

fn arms(h: &mut Harness) {
    h.case("narrow/an enum arm narrows its subject in the arm and its guard", || {
        accepts(&format!(
            "{SHAPE}public function f(s: Shape): f64 {{
  return match (s) {{ Shape.Circle if s.r > 1.0 => s.r, Shape.Circle => 0.5, Shape.Named => 0.0, Shape.Empty => 1.0 }};
}}
"
        ));
    });
    h.case("narrow/a case's field is read only in its own arm", || {
        let r = check(&format!(
            "{SHAPE}public function f(s: Shape): f64 {{
  const a = match (s) {{ Shape.Named => s.r, default => 0.0 }};
  return s.r;
}}
"
        ));
        let codes: Vec<(String, String)> = found(&r)
            .into_iter()
            .map(|(code, at, _, _)| (code, at))
            .collect();
        assert_eq!(
            codes,
            [
                ("EN0303".to_owned(), "3:42".to_owned()),
                ("EN0303".to_owned(), "4:12".to_owned()),
            ],
            "{}",
            r.rendered()
        );
    });
    h.case(
        "narrow/a case arm on a nullable enum makes it present and that case",
        || {
            accepts(&format!(
                "{SHAPE}public function f(s: Shape | null): f64 {{
  return match (s) {{ null => 2.0, Shape.Circle => s.r, default => 0.0 }};
}}
"
            ));
        },
    );
    h.case("narrow/the arms after a `null` arm see the subject without `null` (S:1135)", || {
        accepts(
            "public function f(name: string | null): string {
  return match (name) { null => \"anonymous\", \"admin\" => \"administrator\", default => `user ${name} (${name.length()} bytes)` };
}
",
        );
        rejects(
            "public function f(name: string | null): string {
  return match (name) { \"admin\" => \"a\", default => `${name.length()}` };
}
",
            &[d(
                "EN0303",
                "2:60",
                "length",
                &no_member("string | null", "length"),
            )],
        );
    });
    h.case(
        "narrow/a guarded `null` arm narrows nothing after it",
        || {
            rejects(
                "public function f(name: string | null, c: bool): isize {
  return match (name) { null if c => 0, default => name.length() };
}
",
                &[d(
                    "EN0303",
                    "2:57",
                    "length",
                    &no_member("string | null", "length"),
                )],
            );
        },
    );
    h.case(
        "narrow/`Ok` and `Err` arms read `value` and `error`",
        || {
            accepts(
                "public function f(r: Result<i64>): i64 {
  return match (r) { Ok => r.value, Err => 0 };
}
",
            );
        },
    );
    h.case(
        "narrow/a `match (true)` condition narrows its own arm",
        || {
            accepts(
                "public function f(p: string | null): isize {
  return match (true) { p != null => p.length(), default => 0 };
}
",
            );
        },
    );
    h.case("narrow/a case fact ends with its arm", || {
        let r = check(&format!(
            "{SHAPE}public function f(s: Shape): void {{
  match (s) {{ Shape.Circle => {{ }}, default => {{ }} }}
  const x = s.r;
}}
"
        ));
        assert_eq!(r.codes(), ["EN0303"], "{}", r.rendered());
    });
}

// ---------------------------------------------------------------------------------
// Kills (S:742, N2).

fn kills(h: &mut Harness) {
    h.case("narrow/an assignment to the path kills its fact", || {
        rejects(
            "public function f(p: string | null): void {
  if (p != null) { p = null; p.length(); }
  if (p != null) { p = \"x\"; p.length(); }
}
",
            &[
                d(
                    "EN0303",
                    "2:32",
                    "length",
                    &no_member("string | null", "length"),
                ),
                d(
                    "EN0303",
                    "3:31",
                    "length",
                    &no_member("string | null", "length"),
                ),
            ],
        );
    });
    h.case(
        "narrow/an assignment to a prefix kills the facts below it",
        || {
            rejects(
                "public class H { public items: string | null = null; }
public function f(h: H, other: H): void {
  if (h.items != null) { h = other; h.items.length(); }
  if (h.items != null) { h.items = null; h.items.length(); }
}
",
                &[
                    d(
                        "EN0303",
                        "3:45",
                        "length",
                        &no_member("string | null", "length"),
                    ),
                    d(
                        "EN0303",
                        "4:50",
                        "length",
                        &no_member("string | null", "length"),
                    ),
                ],
            );
        },
    );
    h.case(
        "narrow/writes to a proper extension and calls keep the fact (T:601)",
        || {
            accepts(
                "public class N { public x: i64 = 0; public bump(): void { this.x += 1; } }
public function f(n: N | null): void { if (n != null) { n.x = 1; n.x = 2; } }
public function g(n: N | null): void { if (n != null) { n.bump(); n.bump(); } }
",
            );
        },
    );
    h.case(
        "narrow/a compound assignment to the payload keeps the fact",
        || {
            accepts(
                "public function f(q: i64 | null): i64 {
  if (q != null) { q += 1; q++; return q * 2; }
  return 0;
}
",
            );
        },
    );
    h.case(
        "narrow/a move of the path, its payload or a prefix kills its fact",
        || {
            let len = no_member("string | null", "length");
            rejects(
                "public class H { public items: string | null = null; }
public function take(s: string): void { }
public function drop(h: H): void { }
public function f(p: string | null, h: H): void {
  if (p != null) { take(p); p.length(); }
  if (h.items != null) { drop(h); h.items.length(); }
}
",
                &[
                    d("EN0303", "5:31", "length", &len),
                    d("EN0303", "6:43", "length", &len),
                ],
            );
        },
    );
    h.case("narrow/a move of a proper extension kills only the facts on it", || {
        rejects(
            "public class H { public items: string | null = null; public name: string | null = null; }
public function take(s: string): void { }
public function f(h: H): void {
  if (h.items != null && h.name != null) { take(h.name); h.items.length(); h.name.length(); }
}
",
            &[d(
                "EN0303",
                "4:83",
                "length",
                &no_member("string | null", "length"),
            )],
        );
    });
    h.case(
        "narrow/a compound assignment reads its right side, which keeps its fact",
        || {
            accepts(
                "public function f(p: string | null): isize {
  let s = \"a\" + \"\";
  if (p != null) { s += p; return p.length(); }
  return 0;
}
",
            );
        },
    );
    h.case("narrow/a Copy payload read by value keeps its fact", || {
        accepts(
            "public function f(q: i64 | null): i64 {
  if (q != null) { const a = q; const b = q + 1; return a + b + q; }
  return 0;
}
",
        );
    });
    h.case(
        "narrow/a borrow and a call kill nothing while typing (S:742)",
        || {
            accepts(
                "public class O { public n: i64 = 0; public add(v: i64): void { } }
public function clear(o: &(O | null)): i64 { return 1; }
public function show(o: &O): void { }
public function f(o: O | null): void {
  if (o != null) { clear(&o); o.add(1); show(&o); o.add(2); }
}
",
            );
        },
    );
}

// ---------------------------------------------------------------------------------
// Records (S:742, A:898).

const RECORDED: &str = "public class O { public n: i64 = 0; public add(v: i64): void { } }
public class H { public items: string | null = null; public reset(): void { } }
public function clear(o: &(O | null)): i64 { return 1; }
public function wipe(h: &H): void { }
public function show(o: &O): void { }
";

fn records_cases(h: &mut Harness) {
    h.case(
        "narrow/a reference to the path at its nullable type is a `CallArg` record",
        || {
            let r = accepts(&format!(
                "{RECORDED}public function f(o: O | null): void {{
  if (o != null) {{ clear(&o); }}
}}
"
            ));
            let b = body(&r, "f");
            assert_eq!(
                records(&r, &b),
                [rec(RecordKind::CallArg, "&o", "o != null")]
            );
        },
    );
    h.case(
        "narrow/passing the path at a non-null `&T` records nothing (A:898)",
        || {
            let r = accepts(&format!(
                "{RECORDED}public function f(o: O | null): void {{
  if (o != null) {{ show(&o); o.add(1); }}
}}
"
            ));
            assert_eq!(records(&r, &body(&r, "f")), []);
        },
    );
    h.case(
        "narrow/a use at the nullable type records nothing (A:898)",
        || {
            let r = accepts(
                "public function f(q: i64 | null): void {
  if (q != null) { const z: i64 | null = q; }
}
",
            );
            assert_eq!(records(&r, &body(&r, "f")), []);
        },
    );
    h.case(
        "narrow/references to a proper prefix are recorded: argument, receiver, binding, copy",
        || {
            let r = accepts(&format!(
                "{RECORDED}public function f(h: &H, k: &H): void {{
  let g: &H = k;
  if (h.items != null) {{ wipe(h); h.reset(); const j = h; g = h; }}
}}
"
            ));
            assert_eq!(
                records(&r, &body(&r, "f")),
                [
                    rec(RecordKind::CallArg, "h", "h.items != null"),
                    rec(RecordKind::Receiver, "h", "h.items != null"),
                    rec(RecordKind::Binding, "h", "h.items != null"),
                    rec(RecordKind::Copy, "h", "h.items != null"),
                ]
            );
        },
    );
    h.case(
        "narrow/a field read through a prefix records nothing",
        || {
            let r = accepts(&format!(
                "{RECORDED}public function f(h: &H): isize {{
  if (h.items != null) {{ return h.items.length(); }}
  return 0;
}}
"
            ));
            assert_eq!(records(&r, &body(&r, "f")), []);
        },
    );
    h.case(
        "narrow/a call of a local function records its hidden arguments",
        || {
            let r = check(
                "let count: i64 | null = 0;
function report(): void { console.log(count); }
if (count != null) { report(); }
",
            );
            r.clean();
            let program = r.program.as_ref().expect("checked");
            let st = program.statements.as_ref().expect("statements");
            assert_eq!(
                records(&r, st),
                [rec(RecordKind::HiddenArg, "report()", "count != null")]
            );
        },
    );
    h.case(
        "narrow/each capture an arrow lists is recorded against its local's facts",
        || {
            let r = accepts(&format!(
                "{RECORDED}public function f(h: &H): void {{
  if (h.items != null) {{ const k = () => h.reset(); }}
}}
"
            ));
            let b = body(&r, "f");
            // Captures are 4C's (`ArrowBody.captures`); each one listed is recorded.
            for arrow in b.arrows.iter() {
                for capture in &arrow.captures {
                    assert!(
                        b.records.iter().any(|x| x.kind == RecordKind::Capture
                            && b.facts[x.fact].path.root == capture.local),
                        "capture of {:?} not recorded",
                        capture.local
                    );
                }
            }
        },
    );
    h.case(
        "narrow/a copy or a destructuring of a prefix, then a write through it, pass typing (T:722)",
        || {
            let r = accepts(
                "public class H { public items: string | null = null; }
public function f(h: &H): isize {
  if (h.items != null) { const g = h; g.items = null; return h.items.length(); }
  return 0;
}
public function g(h: &H): isize {
  if (h.items != null) { const { items } = h; *items = null; return h.items.length(); }
  return 0;
}
",
            );
            for f in ["f", "g"] {
                assert_eq!(
                    records(&r, &body(&r, f)),
                    [rec(RecordKind::Binding, "h", "h.items != null")],
                    "{f}"
                );
            }
        },
    );
    h.case(
        "narrow/`&p` where `&(T | null)` is needed keeps that type and records",
        || {
            let r = accepts(
                "public function f(p: string[] | null): void {
  if (p != null) { const r: &(string[] | null) = &p; const s = &p; }
}
",
            );
            let b = body(&r, "f");
            assert_eq!(local_ty(&r, &b, "r"), "&(string[] | null)");
            assert_eq!(local_ty(&r, &b, "s"), "&string[]");
            assert_eq!(
                records(&r, &b),
                [rec(RecordKind::Binding, "&p", "p != null")]
            );
        },
    );
}

// ---------------------------------------------------------------------------------
// O6 order at calls and assignments (S:743, A:898, T:600).

fn order(h: &mut Harness) {
    h.case(
        "narrow/an argument that visibly kills the receiver's fact is EN0401 with a note",
        || {
            let r = rejects(
                "public class O { public n: i64 = 0; public add(v: i64): void { } }
public function run(f: () => void): i64 { return 1; }
public function f(o: O | null): void {
  if (o != null) { o.add(run(() => { o = null; })); }
}
",
                &[d(
                    "EN0401",
                    "4:20",
                    "o",
                    "mismatched types: expected `O`, found `O | null`",
                )],
            );
            let diag = &r.diags[0];
            assert_eq!(diag.primary.text, "this is `O | null` here");
            let notes: Vec<&str> = diag.entries.iter().map(|e| e.text.as_str()).collect();
            assert_eq!(
                notes,
                ["the argument `run(() => { o = null; })` changes `o` before this use"]
            );
        },
    );
    h.case(
        "narrow/a right side that visibly kills the place's fact is EN0401 with a note",
        || {
            let r = rejects(
                "public class O { public n: i64 = 0; }
public function run(f: () => void): i64 { return 1; }
public function f(o: O | null): void {
  if (o != null) { o.n = run(() => { o = null; }); }
}
",
                &[d(
                    "EN0401",
                    "4:20",
                    "o",
                    "mismatched types: expected `O`, found `O | null`",
                )],
            );
            let notes: Vec<&str> = r.diags[0].entries.iter().map(|e| e.text.as_str()).collect();
            assert_eq!(
                notes,
                ["the right-hand side `run(() => { o = null; })` changes `o` before this use"]
            );
        },
    );
    h.case(
        "narrow/`o.add(clear(&o))` and `o.n = clear(&o)` pass typing with a record (T:600)",
        || {
            let r = accepts(
                "public class O { public n: i64 = 0; public add(v: i64): void { } }
public function clear(o: &(O | null)): i64 { return 1; }
public function f(o: O | null): void {
  if (o != null) { o.add(clear(&o)); o.n = clear(&o); }
}
",
            );
            assert_eq!(
                records(&r, &body(&r, "f")),
                [
                    rec(RecordKind::CallArg, "&o", "o != null"),
                    rec(RecordKind::CallArg, "&o", "o != null"),
                ]
            );
        },
    );
}

// ---------------------------------------------------------------------------------
// Loops (S:744, A:900).

const MAKE: &str = "public function make(): string | null { return null; }\n";

fn loops(h: &mut Harness) {
    h.case("narrow/a loop's prescan kills before its condition", || {
        rejects(
            "public function f(p: string | null, c: bool): void {
  if (p != null) { while (c) { p.length(); p = null; } }
  if (p != null) { do { p.length(); } while ((p = null) == null); }
  if (p != null) { for (let i = 0; i < 3; p = null) { p.length(); } }
}
",
            &[
                d(
                    "EN0303",
                    "2:34",
                    "length",
                    &no_member("string | null", "length"),
                ),
                d(
                    "EN0303",
                    "3:27",
                    "length",
                    &no_member("string | null", "length"),
                ),
                d(
                    "EN0303",
                    "4:57",
                    "length",
                    &no_member("string | null", "length"),
                ),
            ],
        );
    });
    h.case(
        "narrow/a loop's condition narrows its body, and its false branch the exit",
        || {
            accepts(&format!(
                "{MAKE}public function f(): isize {{
  let p: string | null = null;
  while (p == null) {{ p = make(); }}
  return p.length();
}}
public function g(): isize {{
  let p: string | null = make();
  for (; p != null; p = make()) {{ p.length(); }}
  let q: string | null = null;
  do {{ q = make(); }} while (q == null);
  return q.length();
}}
"
            ));
        },
    );
    h.case(
        "narrow/the state after a loop is joined over its `break`s",
        || {
            rejects(
                &format!(
                    "{MAKE}public function f(c: bool): isize {{
  let p: string | null = null;
  while (p == null) {{ if (c) {{ break; }} p = make(); }}
  return p.length();
}}
"
                ),
                &[d(
                    "EN0303",
                    "5:12",
                    "length",
                    &no_member("string | null", "length"),
                )],
            );
            accepts(&format!(
                "{MAKE}public function f(): isize {{
  let p: string | null = null;
  while (true) {{ p = make(); if (p != null) {{ break; }} }}
  return p.length();
}}
"
            ));
        },
    );
    h.case("narrow/a `break outer` counts for `outer`", || {
        rejects(
            &format!(
                "{MAKE}public function f(c: bool): isize {{
  let p: string | null = make();
  if (p == null) {{ return 0; }}
  outer: while (c) {{ while (c) {{ p = null; break outer; }} }}
  return p.length();
}}
"
            ),
            &[d(
                "EN0303",
                "6:12",
                "length",
                &no_member("string | null", "length"),
            )],
        );
    });
}

// ---------------------------------------------------------------------------------
// Arrows (S:746, A:900).

fn arrows(h: &mut Harness) {
    h.case(
        "narrow/an arrow argument that changes a path kills its fact at the call (S:746)",
        || {
            let r = check_lib(
                "public function f(xs: &i64[], p: string | null): void {
  if (p != null) { xs.forEach(x => { p = null; }); console.log(p.length()); }
}
",
            );
            expect(
                &r,
                &[d(
                    "EN0303",
                    "2:66",
                    "length",
                    &no_member("string | null", "length"),
                )],
            );
        },
    );
    h.case(
        "narrow/an arrow inherits the facts on paths it does not change",
        || {
            accepts_lib(
                "public function f(xs: &i64[], p: string | null): void {
  if (p != null) { xs.forEach(x => console.log(p.length())); p.length(); }
}
",
            );
        },
    );
    h.case(
        "narrow/no arrow of the call sees a fact another arrow of it changes",
        || {
            rejects(
                "public function both(f: () => void, g: () => void): void { }
public function f(p: string | null): void {
  if (p != null) { both(() => { p.length(); }, () => { p = null; }); }
}
",
                &[d(
                    "EN0303",
                    "3:35",
                    "length",
                    &no_member("string | null", "length"),
                )],
            );
        },
    );
    h.case(
        "narrow/an arrow's body loses the facts it changes, and only its body",
        || {
            rejects(
                "public function f(p: string | null): void {
  if (p != null) { const k = () => { p.length(); p = null; }; p.length(); }
}
",
                &[d(
                    "EN0303",
                    "2:40",
                    "length",
                    &no_member("string | null", "length"),
                )],
            );
        },
    );
}

// ---------------------------------------------------------------------------------
// The HIR of a narrowed read (S:747, A:914).

fn shapes(h: &mut Harness) {
    h.case(
        "narrow/a narrowed read is `NarrowedPayload(p, Present, fact)`",
        || {
            let r = accepts(
                "public function f(p: string | null): isize {
  if (p != null) { return p.length(); }
  return 0;
}
",
            );
            let b = body(&r, "f");
            let narrowed: Vec<(VariantIdx, String, Fact)> = exprs(&b)
                .into_iter()
                .filter_map(|e| match e.kind {
                    ExprKind::NarrowedPayload(inner, variant, fact) => {
                        assert!(matches!(inner.kind, ExprKind::Local(_)));
                        assert_eq!(r.tcx.ty_string(inner.ty), "string | null");
                        assert_eq!(r.tcx.ty_string(e.ty), "string");
                        Some((
                            variant,
                            r.map.text(b.facts[fact].span).to_owned(),
                            b.facts[fact].fact,
                        ))
                    }
                    _ => None,
                })
                .collect();
            assert_eq!(
                narrowed,
                [(VariantIdx(1), "p != null".to_owned(), Fact::NonNull)]
            );
        },
    );
    h.case(
        "narrow/a read in an enum arm is `NarrowedPayload(s, case, fact)`",
        || {
            let r = accepts(&format!(
                "{SHAPE}public function f(s: Shape): f64 {{
  return match (s) {{ Shape.Circle => s.r, default => 0.0 }};
}}
"
            ));
            let b = body(&r, "f");
            let cases: Vec<(VariantIdx, Fact)> = exprs(&b)
                .into_iter()
                .filter_map(|e| match e.kind {
                    ExprKind::NarrowedPayload(_, variant, fact) => {
                        Some((variant, b.facts[fact].fact))
                    }
                    _ => None,
                })
                .collect();
            assert_eq!(cases, [(VariantIdx(0), Fact::Case(VariantIdx(0)))]);
        },
    );
    h.case(
        "narrow/the facts of a condition read twice have one identity",
        || {
            let r = accepts(
                "public function f(p: string | null): isize {
  if (p != null && p.length() > 0) { return p.length(); }
  return 0;
}
",
            );
            let b = body(&r, "f");
            assert_eq!(b.facts.len(), 1);
        },
    );
    h.case(
        "narrow/a test whose right side kills the left's fact narrows nothing",
        || {
            rejects(
                "public function f(p: string | null): void {
  if (p != null && (p = null) == null) { p.length(); }
}
",
                &[d(
                    "EN0303",
                    "2:44",
                    "length",
                    &no_member("string | null", "length"),
                )],
            );
        },
    );
}

/// Stage 6's review fixes of narrowing, and the cases the mutation gate found
/// unpinned.
fn review(h: &mut Harness) {
    let mismatch = "mismatched types: expected `i64`, found `i64 | null`";
    h.case(
        "narrow/S:744: the loop prescan kills each target of a destructuring assignment",
        move || {
            rejects(
                "public function f(c: bool): void {
  let a: i64 | null = 1;
  let b: i64 | null = 2;
  if (a != null) {
    while (c) {
      const n: i64 = a;
      [a, b] = [null, 3];
    }
  }
}
",
                &[d("EN0401", "6:22", "a", mismatch)],
            );
        },
    );
    h.case(
        "narrow/S:746: an arrow argument's destructuring assignment kills at the call",
        move || {
            rejects(
                "public function run(f: () => void): void { f(); }
public function f(): void {
  let a: i64 | null = 1;
  let b: i64 | null = 2;
  if (a != null) {
    run(() => { [a, b] = [null, 3]; });
    const n: i64 = a;
  }
}
",
                &[d("EN0401", "7:20", "a", mismatch)],
            );
        },
    );
    h.case(
        "narrow/S:742: a kill in an arm's guard or `match (true)` condition reaches the later arms",
        || {
            rejects(
                "public function f(k: i64, p: string | null): isize {
  if (p != null) {
    return match (k) {
      0 if (p = null) == null => 1,
      default => p.length(),
    };
  }
  return 0;
}
public function g(p: string | null): isize {
  if (p != null) {
    return match (true) { (p = null) == null => 1, default => p.length() };
  }
  return 0;
}
",
                &[
                    d(
                        "EN0303",
                        "5:20",
                        "length",
                        &no_member("string | null", "length"),
                    ),
                    d(
                        "EN0303",
                        "12:65",
                        "length",
                        &no_member("string | null", "length"),
                    ),
                ],
            );
        },
    );
    h.case(
        "narrow/S:743: a generic or overloaded method's argument that kills the receiver is EN0401",
        || {
            let r = check(
                "public class O { public put<T>(x: T): void { } public add(x: i64): void { } public add(x: bool): void { } }
public function f(o: O | null): void { if (o != null) { o.put((o = null) == null ? 1 : 2); } }
public function g(o: O | null): void { if (o != null) { o.add((o = null) == null ? 1 : 2); } }
",
            );
            expect(
                &r,
                &[
                    d("EN0401", "2:57", "o", "mismatched types: expected `O`, found `O | null`"),
                    d("EN0401", "3:57", "o", "mismatched types: expected `O`, found `O | null`"),
                ],
            );
        },
    );
    h.case(
        "narrow/S:742: an owned destructuring that copies a reference field records a `Binding`",
        || {
            let r = accepts(
                "public class Big { public s: string | null = null; }
public class H {
  private r: &Big; private k: i64 = 0;
  public constructor(r: &Big) { this.r = r; }
  public static f(h: H): void { if (h.r.s != null) { const { r, k } = h; } }
  public static g(h: H): void { if (h.r.s != null) { const { r: q } = h; } }
}
",
            );
            for m in ["H::f", "H::g"] {
                let b = body(&r, m);
                assert_eq!(
                    records(&r, &b),
                    [rec(RecordKind::Binding, "h", "h.r.s != null")],
                    "{m}"
                );
            }
        },
    );
    h.case(
        "narrow/S:1007: `*r` is a narrowing path, read through its fact",
        || {
            accepts(
                "public function f(r: &(i64 | null)): i64 {
  if (*r != null) { return *r; }
  return 0;
}
",
            );
        },
    );
    h.case(
        "narrow/S:746: a parenthesised arrow, or one in a ternary, is prescanned at the call",
        || {
            rejects(
                "public function run(f: () => void): void { f(); }
public function f(p: string | null): isize { if (p != null) { run((() => { p = null; })); return p.length(); } return 0; }
public function g(c: bool, p: string | null): isize { if (p != null) { run(c ? () => { p = null; } : () => { }); return p.length(); } return 0; }
",
                &[
                    d("EN0303", "2:100", "length", &no_member("string | null", "length")),
                    d("EN0303", "3:123", "length", &no_member("string | null", "length")),
                ],
            );
        },
    );
    h.case(
        "narrow/S:742: moving a path into an array literal or a named form kills its fact",
        || {
            rejects(
                "public class D { public s: string = \"\"; }
public function g(p: string | null): isize { if (p != null) { const d = new D { s: p }; return p.length(); } return 0; }
public function h(p: string | null): isize { if (p != null) { const a = [p]; return p.length(); } return 0; }
public function k(p: string | null): isize { if (p != null) { const o = { s: p }; return p.length(); } return 0; }
",
                &[
                    d("EN0303", "2:98", "length", &no_member("string | null", "length")),
                    d("EN0303", "3:87", "length", &no_member("string | null", "length")),
                    d("EN0303", "4:92", "length", &no_member("string | null", "length")),
                ],
            );
        },
    );
    h.case(
        "narrow/after a `match` over different cases no case fact survives (mutant M01)",
        || {
            rejects(
                "public enum Shape { Circle { r: f64 }, Rect { w: f64 } }
public function f(s: Shape): f64 {
  match (s) { Shape.Circle => { const a = s.r; }, Shape.Rect => { const b = s.w; } }
  return s.r;
}
",
                &[d("EN0303", "4:12", "r", "`Shape` has no member `r`")],
            );
        },
    );
    h.case(
        "narrow/an arrow parameter named like an outer narrowed path does not kill it (mutant M09)",
        || {
            accepts(
                "public function run(f: (p: string | null) => void): void { }
public function f(p: string | null): isize { if (p != null) { run((p: string | null) => { p = null; }); return p.length(); } return 0; }
",
            );
        },
    );
    h.case(
        "narrow/S:1133: a case arm on a nullable subject makes it non-null (mutant M12)",
        || {
            accepts(
                "public enum Shape { Circle { r: f64 }, Rect { w: f64 } }
public function f(s: Shape | null): f64 { return match (s) { Shape.Circle => s.r, default => 0.0 }; }
",
            );
        },
    );
    h.case(
        "narrow/a `continue` state reaches a `for` step and a `do` condition (mutant M14)",
        || {
            rejects(
                "public function f(p: string | null, n: isize): void {
  for (let i: isize = 0; i < n; i = i + p.length()) { if (p == null) { continue; } }
}
public function g(p: string | null): void {
  do { if (p == null) { continue; } } while (p.length() > 0);
}
",
                &[
                    d(
                        "EN0303",
                        "2:43",
                        "length",
                        &no_member("string | null", "length"),
                    ),
                    d(
                        "EN0303",
                        "5:48",
                        "length",
                        &no_member("string | null", "length"),
                    ),
                ],
            );
        },
    );
    h.case(
        "narrow/a `for...of` binding hides an outer name in the prescans (mutant M45)",
        || {
            accepts(
                "public function take(s: string): void { }
public function f(x: string | null, ys: string[], c: bool): isize {
  if (x != null) {
    while (c) {
      for (const x of ys) { take(x); }
      return x.length();
    }
  }
  return 0;
}
",
            );
        },
    );
}
