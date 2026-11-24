//! `Result`, `Err`, `?` and unused results (plan d.12's `result.rs`; owner 4C): C19
//! at a `return`, an arrow's expression body and the ternary branches and `match`
//! arms that flow there (`WrapOk`, EN0455 with S:1139's three heads and the
//! no-move-place help), `return;` and the end of a `Result<void, E>` body; `Err(e)`
//! and its `ErrForm` at `Failure`, at a literal-union `E`, at another `E` and with no
//! expected type (EN0401); `e?` and its `TryKind` (EN0424, EN0425, EN0429); an
//! unused `Result` (EN0426, G20 byte-exact) and an unused `@mustUse` result
//! (EN0453, G23's warning), both silenced by `void`.

use enrang_hir::{
    self as hir, Adjust, ArmBody, Callee, ErrForm, ExprKind, FormKind, StmtKind, TryKind,
};
use enrang_sema::LibSource;
use enrang_testkit::{Case, Harness, extract_cases, line_diff, workspace_root};

use crate::paths::{body, diags, expr_stmt, init, main_lib, returned, ty};
use crate::support::run_with;

pub fn register(h: &mut Harness) {
    c19(h);
    either(h);
    errs(h);
    tries(h);
    unused(h);
    goldens(h);
    review(h);
}

/// The `Err(...)` form `e` is, with its operand.
fn err_form(e: &hir::Expr) -> (ErrForm, &hir::Expr) {
    match &e.kind {
        ExprKind::Call {
            callee: Callee::Form(FormKind::Err(form)),
            args,
            ..
        } => (*form, &args[0]),
        other => panic!("not an `Err`: {other:?}"),
    }
}

/// Every `return`'s value in `b`, in order, arms included.
fn returns(b: &hir::Body) -> Vec<&hir::Expr> {
    fn block<'b>(blk: &'b hir::Block, out: &mut Vec<&'b hir::Expr>) {
        for s in &blk.stmts {
            match &s.kind {
                StmtKind::Return(Some(e)) => out.push(e),
                StmtKind::If { then_, else_, .. } => {
                    block(then_, out);
                    if let Some(e) = else_ {
                        block(e, out);
                    }
                }
                StmtKind::Block(b) => block(b, out),
                StmtKind::Expr(e) => expr(e, out),
                _ => {}
            }
        }
    }
    fn expr<'b>(e: &'b hir::Expr, out: &mut Vec<&'b hir::Expr>) {
        if let ExprKind::Match { arms, .. } = &e.kind {
            for arm in arms {
                if let ArmBody::Return(Some(v)) = &arm.body {
                    out.push(v);
                }
            }
        }
    }
    let mut out = Vec::new();
    block(&b.root, &mut out);
    out
}

fn c19(h: &mut Harness) {
    h.case(
        "result/C19: `return n;` in a `Result<i64>` function is `return Ok(n);`",
        || {
            let r = main_lib(
                "private function f(n: i64): Result<i64> { return n; }
private function g(): Result<Token> { return Token.End; }
private enum Token { End }
",
            );
            r.clean();
            let e = returned(body(&r, "main::f"));
            assert_eq!(e.adjust, [Adjust::WrapOk]);
            assert_eq!(ty(&r, e.ty), "i64");
            // A value of another error type is a success: `Err` would first turn it
            // into its text (S:1139, EF-03).
            let e = returned(body(&r, "main::g"));
            assert_eq!(e.adjust, [Adjust::WrapOk]);
            assert_eq!(ty(&r, e.ty), "Token");
        },
    );
    h.case(
        "result/C19: an operand typed from context is checked against `T`, then wrapped",
        || {
            let r = main_lib(
                "private function pair(lo: i64, hi: i64): Result<[i64, i64]> { return [lo, hi]; }
private function none(): Result<Node | null> { return null; }
private function byte(): Result<u8> { return 200; }
private function dir(): Result<Direction, Token> { return \"left\"; }
private enum Token { End }
private type Direction = \"left\" | \"right\";
public class Node { public v: i64; }
",
            );
            r.clean();
            for f in ["pair", "none", "byte", "dir"] {
                let e = returned(body(&r, &format!("main::{f}")));
                assert_eq!(e.adjust.last(), Some(&Adjust::WrapOk), "{f}: {e:?}");
            }
            assert!(matches!(
                returned(body(&r, "main::pair")).kind,
                ExprKind::TupleLit(_)
            ));
            assert_eq!(ty(&r, returned(body(&r, "main::byte")).ty), "u8");
            assert_eq!(
                returned(body(&r, "main::none")).adjust,
                [Adjust::WrapOk],
                "`null` is typed at the nullable it meets (D11)"
            );
        },
    );
    h.case(
        "result/C19: a number literal that does not fit `T` is EN0411",
        || {
            let r = main_lib("private function k(): Result<u8> { return -1; }\n");
            assert_eq!(
                diags(&r),
                ["EN0411 1:43 `-1` doesn't fit `u8` [`u8` holds 0 to 255]"]
            );
        },
    );
    h.case(
        "result/C19: an operand of another type is EN0401 at `T`",
        || {
            let r = main_lib("private function h(msg: &string): Result<string> { return msg; }\n");
            assert_eq!(
                r.rendered(),
                "error[EN0401]: mismatched types: expected `string`, found `&string`
 --> main.en:1:59
  |
1 | private function h(msg: &string): Result<string> { return msg; }
  |                                                           ^^^ this is `&string`
  |                                   -------------- `string` is required by the return type
  |
  = explain: run `enrang explain EN0401`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "result/C19: a `Result` operand and `Err(...)` are returned as they are",
        || {
            let r = main_lib(
                "private function a(): Result<i64> { return 1; }
private function b(): Result<i64> { return a(); }
private function c(): Result<i64> { return Err(\"no\"); }
private function d(): Result<i64> { return panic(\"never\"); }
",
            );
            r.clean();
            assert!(returned(body(&r, "main::b")).adjust.is_empty());
            let c = returned(body(&r, "main::c"));
            assert!(c.adjust.is_empty());
            assert_eq!(ty(&r, c.ty), "Result<i64>");
            assert_eq!(err_form(c).0, ErrForm::Text);
        },
    );
    h.case("result/C19 reaches each ternary branch", || {
        let r = main_lib(
            "private function f(c: bool, a: i64): Result<i64> { return c ? a : Err(\"no\"); }
private function g(c: bool): Result<i64> { return c ? 1 : 2; }
",
        );
        r.clean();
        let ExprKind::Ternary(_, then_, else_) = &returned(body(&r, "main::f")).kind else {
            panic!("a ternary");
        };
        assert_eq!(then_.adjust, [Adjust::WrapOk]);
        assert!(else_.adjust.is_empty());
        assert_eq!(err_form(else_).0, ErrForm::Text);
        let ExprKind::Ternary(_, then_, else_) = &returned(body(&r, "main::g")).kind else {
            panic!("a ternary");
        };
        assert_eq!(then_.adjust, [Adjust::WrapOk]);
        assert_eq!(else_.adjust, [Adjust::WrapOk]);
    });
    h.case(
        "result/C19 reaches each `match` arm, typed as a `return` of its value",
        || {
            let r = main_lib(
                "private function m(x: i64): Result<i64> { return match (x) { 0 => Err(\"zero\"), default => x }; }\n",
            );
            r.clean();
            let b = body(&r, "main::m");
            let values = returns(b);
            assert_eq!(values.len(), 2);
            assert_eq!(err_form(values[0]).0, ErrForm::Text);
            assert_eq!(values[1].adjust, [Adjust::WrapOk]);
        },
    );
    h.case(
        "result/C19 in an arrow's expression body at a written or expected result",
        || {
            let r = main_lib(
                "private function f(c: bool): Result<i64> {
  const g = (): Result<i64> => c ? 1 : Err(\"no\");
  const k = (x: i64): Result<i64> => x;
  return run(x => x);
}
private function run(f: (x: i64) => Result<i64>): Result<i64> { return f(1); }
",
            );
            r.clean();
            let b = body(&r, "main::f");
            for arrow in b.arrows.iter() {
                let hir::ArrowBodyKind::Expr(e) = &arrow.body else {
                    panic!("an expression body");
                };
                let wrapped = match &e.kind {
                    ExprKind::Ternary(_, then_, _) => &then_.adjust,
                    _ => &e.adjust,
                };
                assert_eq!(wrapped, &[Adjust::WrapOk]);
            }
        },
    );
    h.case(
        "result/no C19 where the arrow's body decides its result (A:920)",
        || {
            let r = main_lib(
                "const g = (x: i64) => x;
const h = (x: i64) => { return x; };
",
            );
            r.clean();
            let b = crate::paths::statements(&r);
            for arrow in b.arrows.iter() {
                assert_eq!(ty(&r, arrow.ret), "i64");
            }
            let hir::ArrowBodyKind::Expr(e) = &b.arrows.iter().next().expect("an arrow").body
            else {
                panic!("an expression body");
            };
            assert!(e.adjust.is_empty());
        },
    );
    h.case(
        "result/`return;` and the end of a `Result<void, E>` body are `return Ok();` (S:677)",
        || {
            let r = main_lib(
                "private function v(): Result<void> { return; }
private function w(): Result<void> {}
private function z(): Result<void, IoErr> { if (true) { return; } }
private enum IoErr { Lost }
",
            );
            r.clean();
        },
    );
    h.case(
        "result/`return;` where a success value is due is EN0401",
        || {
            let r = main_lib("private function x(): Result<i64> { return; }\n");
            assert_eq!(
                r.rendered(),
                "error[EN0401]: mismatched types: expected `Result<i64>`, found `void`
 --> main.en:1:37
  |
1 | private function x(): Result<i64> { return; }
  |                                     ^^^^^^ this `return` gives no value
  |                       ----------- `Result<i64>` is required by the return type
  |
  = explain: run `enrang explain EN0401`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "result/SPEC 6's example of both `Result` forms type-checks (S:1139)",
        || {
            let src = |err: &str, fail: &str| {
                format!(
                    "import {{ fs }} from \"os\";

public function parseAge(s: &string): Result<i64{err}> {{
  const n: i64 = s.parseInt() ?? -1;
  if (n < -1) {{ return Err({fail}); }}
  if (n < 0) {{ return Err(AgeError.Negative); }}
  return n;
}}

public function loadAge(path: &string): Result<i64> {{
  const text = fs.readFile(path)?;
  return parseAge(&text)?;
}}

public enum AgeError {{ NotANumber = \"not a number\", Negative = \"negative age\" }}
"
                )
            };
            let r = main_lib(&src(", AgeError", "AgeError.NotANumber"));
            r.clean();
            let parse = body(&r, "main::parseAge");
            let values = returns(parse);
            assert_eq!(err_form(values[0]).0, ErrForm::Value);
            assert_eq!(values[2].adjust, [Adjust::WrapOk]);
            let load = body(&r, "main::loadAge");
            let kinds: Vec<TryKind> = [init(load, 0), returned(load)]
                .iter()
                .map(|e| match &e.kind {
                    ExprKind::Try(_, kind) => *kind,
                    other => panic!("{other:?}"),
                })
                .collect();
            // `IoError` and `AgeError` both turn into their text in `Result<i64>`.
            assert_eq!(
                kinds,
                [TryKind::ResultIntoFailure, TryKind::ResultIntoFailure]
            );
            assert_eq!(returned(load).adjust, [Adjust::WrapOk]);
            let r = main_lib(&src("", "`not a number: ${s}`"));
            r.clean();
            let values = returns(body(&r, "main::parseAge"));
            assert_eq!(err_form(values[0]).0, ErrForm::Text);
            assert_eq!(err_form(values[1]).0, ErrForm::IntoFailure);
        },
    );
}

fn either(h: &mut Harness) {
    h.case(
        "result/EN0455: a fixed text in a `Result<string>` function (S:1139)",
        || {
            let r = main_lib("private function f(): Result<string> { return \"file missing\"; }\n");
            assert_eq!(
                r.rendered(),
                "error[EN0455]: `\"file missing\"` could be a success or an error here
 --> main.en:1:47
  |
1 | private function f(): Result<string> { return \"file missing\"; }
  |                                               ^^^^^^^^^^^^^^ `Err` would take this as it is
  |
help: write `Ok(\"file missing\")` or `Err(\"file missing\")`
  = explain: run `enrang explain EN0455`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "result/EN0455: a `string` variable, a template and a `&string` at `Result<&string>`",
        || {
            let r = main_lib(
                "private function g(msg: string): Result<string> { return msg; }
private function t(n: i64): Result<string> { return `n=${n}`; }
private function r(s: &string): Result<&string> { return s; }
",
            );
            // `Result<&string>` holds a reference in a case's field, which is 4E's
            // EN0701 at the written type (A:892); the return is still checked.
            assert_eq!(
                diags(&r),
                [
                    "EN0455 1:58 `msg` could be a success or an error here [`Err` would take this as it is]",
                    "EN0455 2:53 ``n=${n}`` could be a success or an error here [`Err` would take this as it is]",
                    "EN0701 3:33 a `Result` can't hold a `&string`, because `&string` is a reference [a reference]",
                    "EN0455 3:58 `s` could be a success or an error here [`Err` would take this as it is]",
                ]
            );
            assert_eq!(r.diags[0].helps[0].message, "write `Ok(msg)` or `Err(msg)`");
        },
    );
    h.case(
        "result/EN0455: a place no move may leave gets the forms that compile (V-ME-06-err)",
        || {
            let r = main_lib(
                "public class User {
  public constructor(private name: string) {}
  public label(): Result<string> { return this.name; }
  public check(): Result<isize> { if (this.name.isEmpty()) { return Err(&this.name); } return this.name.length(); }
}
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0455]: `this.name` could be a success or an error here
 --> main.en:3:43
  |
3 |   public label(): Result<string> { return this.name; }
  |                                           ^^^^^^^^^ `Err` would take this as it is
  |
help: write `Ok(this.name.clone())` or `Err(&this.name)`
  = explain: run `enrang explain EN0455`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case("result/EN0455: an indexed `string` is a place no move may leave", || {
        let r = main_lib(
            "public function first(names: &Slice<string>): Result<string> { return names[0]; }\n",
        );
        assert_eq!(
            diags(&r),
            ["EN0455 1:71 `names[0]` could be a success or an error here [`Err` would take this as it is]"]
        );
        assert_eq!(
            r.diags[0].helps[0].message,
            "write `Ok(names[0].clone())` or `Err(&names[0])`"
        );
    });
    h.case(
        "result/EN0455: a value whose own type is `E`, and a fixed text of a literal-union `E`",
        || {
            let r = main_lib(
                "private function g(): Result<Token, Token> { return Token.End; }
private function d(): Result<string, Direction> { return \"left\"; }
private function e(): Result<string, Direction> { return \"up\"; }
private enum Token { End }
private type Direction = \"left\" | \"right\";
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0455 1:53 `Token.End` could be a success or an error here [`Err` would take this as it is]",
                    "EN0455 2:58 `\"left\"` could be a success or an error here [`Err` would take this as it is]",
                ]
            );
            // `"up"` is no `Direction`, so only a success could hold it.
            let r = main_lib(
                "private function e(): Result<string, Direction> { return \"up\"; }
private type Direction = \"left\" | \"right\";
",
            );
            r.clean();
            assert_eq!(returned(body(&r, "main::e")).adjust, [Adjust::WrapOk]);
        },
    );
    h.case(
        "result/EN0455: a text at `E = Failure`, even where a literal-union `T` takes it (plan choice)",
        || {
            let r = main_lib(
                "private function dir(): Result<Direction> { return \"left\"; }\nprivate type Direction = \"left\" | \"right\";\n",
            );
            assert_eq!(
                diags(&r),
                ["EN0455 1:52 `\"left\"` could be a success or an error here [`Err` would take this as it is]"]
            );
        },
    );
    h.case("result/EN0455 at each ternary branch it reaches", || {
        let r = main_lib(
            "private function f(c: bool, s: string): Result<string> { return c ? s : Err(\"none\"); }\n",
        );
        assert_eq!(
            diags(&r),
            ["EN0455 1:69 `s` could be a success or an error here [`Err` would take this as it is]"]
        );
    });
}

fn errs(h: &mut Harness) {
    h.case(
        "result/`Err` at `Failure`: each operand's `ErrForm` (A:888)",
        || {
            let r = main_lib(
                "private function a(): Result<i64> { return Err(\"fixed\"); }
private function b(n: i64): Result<i64> { return Err(`n is ${n}`); }
private function c(msg: string): Result<i64> { return Err(msg); }
private function d(why: &string): Result<u8> { return Err(why); }
private function e(f: Failure): Result<i64> { return Err(f); }
private function g(): Result<i64> { return Err(AgeError.NotANumber); }
public function firstErr(names: &Slice<string>): Result<i64> { return Err(names[0]); }
private enum AgeError { NotANumber = \"not a number\" }
",
            );
            r.clean();
            let forms: Vec<ErrForm> = ["a", "b", "c", "d", "e", "g", "firstErr"]
                .iter()
                .map(|f| err_form(returned(body(&r, &format!("main::{f}")))).0)
                .collect();
            assert_eq!(
                forms,
                [
                    ErrForm::Text,
                    ErrForm::Text,
                    ErrForm::TextMove,
                    ErrForm::TextCopy,
                    ErrForm::Value,
                    ErrForm::IntoFailure,
                    // A place no move may leave moves too: phase 3's EN0604 (A:888).
                    ErrForm::TextMove,
                ]
            );
        },
    );
    h.case("result/`Err` at a literal-union `E` (EF-03)", || {
        let r = main_lib(
            "private function f(): Result<i64, Direction> { return Err(\"left\"); }
private function g(d: Direction): Result<i64, Direction> { return Err(d); }
private type Direction = \"left\" | \"right\";
",
        );
        r.clean();
        assert_eq!(err_form(returned(body(&r, "main::f"))).0, ErrForm::Text);
        assert_eq!(err_form(returned(body(&r, "main::g"))).0, ErrForm::Value);
        let r = main_lib(
            "private function h(): Result<i64, Direction> { return Err(\"up\"); }
private type Direction = \"left\" | \"right\";
",
        );
        assert_eq!(
            diags(&r),
            ["EN0401 1:59 `\"up\"` is not a `Direction` [not one of `Direction`'s values]"]
        );
    });
    h.case(
        "result/`Err` at a named `E` needs that `E`: a text or another error is EN0401 (EF-03, OQ20-age)",
        || {
            let r = main_lib(
                "private function f(): Result<i64, AgeError> { return Err(\"no\"); }
private function h(): Result<i64, AgeError> { return Err(DiskError.Timeout); }
private enum AgeError { NotANumber = \"not a number\", Negative = \"negative age\" }
private enum DiskError { Timeout }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0401 1:58 mismatched types: expected `AgeError`, found `string` [this is `string`]",
                    "EN0401 2:58 mismatched types: expected `AgeError`, found `DiskError` [this is `DiskError`]",
                ]
            );
            let r = main_lib(
                "private function b(): Result<i64, AgeError> { return Err(AgeError.Negative); }
private enum AgeError { NotANumber = \"not a number\", Negative = \"negative age\" }
",
            );
            r.clean();
            assert_eq!(err_form(returned(body(&r, "main::b"))).0, ErrForm::Value);
        },
    );
    h.case(
        "result/`Err` at `Failure` takes a text or an error value, else EN0401",
        || {
            let r = main_lib("private function d(): Result<i64> { return Err(5); }\n");
            assert_eq!(
                r.rendered(),
                "error[EN0401]: `Err` takes a text or an error value here, found `int`
 --> main.en:1:48
  |
1 | private function d(): Result<i64> { return Err(5); }
  |                                                ^ this is `int`
  |
  = explain: run `enrang explain EN0401`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "result/`Err` with no expected type: `E` from the operand, `Failure` for a text (S:1183)",
        || {
            let r = main_lib(
                "const e: Result<i64> = Err(\"boom\");
const a = (n: i64) => { if (n < 0) { return Err(AgeError.Negative); } return age(); };
const b = (n: i64) => { if (n < 0) { return Err(\"negative\"); } return text(); };
private function age(): Result<i64, AgeError> { return 1; }
private function text(): Result<i64> { return 1; }
private enum AgeError { Negative }
",
            );
            r.clean();
            let b = crate::paths::statements(&r);
            let rets: Vec<String> = b.arrows.iter().map(|a| ty(&r, a.ret)).collect();
            assert_eq!(rets, ["Result<i64, AgeError>", "Result<i64>"]);
            let firsts: Vec<ErrForm> = b
                .arrows
                .iter()
                .map(|a| {
                    let hir::ArrowBodyKind::Block(blk) = &a.body else {
                        panic!("a block");
                    };
                    let StmtKind::If { then_, .. } = &blk.stmts[0].kind else {
                        panic!("an `if`");
                    };
                    let StmtKind::Return(Some(e)) = &then_.stmts[0].kind else {
                        panic!("a `return`");
                    };
                    err_form(e).0
                })
                .collect();
            assert_eq!(firsts, [ErrForm::Value, ErrForm::Text]);
            // At an expected result, `Err` reads its `E` from there.
            let r = main_lib(
                "const b = run(() => Err(\"x\"));
private function run(f: () => Result<i64, AgeError>): i64 { return 0; }
private enum AgeError { Negative }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0401 1:25 mismatched types: expected `AgeError`, found `string` [this is `string`]"]
            );
            let r = main_lib("const e = Err(5);\n");
            assert_eq!(
                diags(&r),
                ["EN0401 1:15 `Err` takes a text or an error value here, found `int` [this is `int`]"],
                "a rejected operand reports nothing more"
            );
        },
    );
    h.case("result/`Err` takes one argument (EN0423)", || {
        let r = main_lib(
            "private function f(): Result<i64> { return Err(); }
private function g(): Result<i64> { return Err(\"a\", \"b\"); }
",
        );
        assert_eq!(
            diags(&r),
            [
                "EN0423 1:44 `Err` takes 1 argument, but none were given [too few arguments]",
                "EN0423 2:44 `Err` takes 1 argument, but 2 were given [too many arguments]",
            ]
        );
    });
}

fn tries(h: &mut Harness) {
    h.case(
        "result/`?`: `TryKind` by the function's result (S:1141)",
        || {
            let r = main_lib(
                "private function a(): Result<i64, DiskError> { return 1; }
private function c(): Result<i64> { return a()?; }
private function d(): Result<i64, DiskError> { return a()?; }
private function n(): i64 | null { return null; }
private function m(): i64 | null { const y = n()?; return y; }
private enum DiskError { Timeout }
",
            );
            r.clean();
            let kind = |f: &str, e: &hir::Expr| match &e.kind {
                ExprKind::Try(_, kind) => *kind,
                other => panic!("{f}: {other:?}"),
            };
            assert_eq!(
                kind("c", returned(body(&r, "main::c"))),
                TryKind::ResultIntoFailure
            );
            assert_eq!(kind("d", returned(body(&r, "main::d"))), TryKind::Result);
            let m = init(body(&r, "main::m"), 0);
            assert_eq!(kind("m", m), TryKind::Nullable);
            assert_eq!(ty(&r, m.ty), "i64");
        },
    );
    h.case(
        "result/EN0425: `?` of another error type, with the `Result<T>` help",
        || {
            let r = main_lib(
                "private function a(): Result<i64, DiskError> { return 1; }
private function b(): Result<i64, AgeError> { return a()?; }
private enum AgeError { Negative }
private enum DiskError { Timeout }
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0425]: `?` returns `DiskError`, but the function returns `AgeError`
 --> main.en:2:57
  |
2 | private function b(): Result<i64, AgeError> { return a()?; }
  |                                                         ^ this returns a `DiskError` error early
  |
help: return `Result<i64>`, which takes any error as its text
  = explain: run `enrang explain EN0425`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case("result/EN0424: `?` in a function returning neither", || {
        let r = main_lib(
            "private function f(): i64 { const x = g()?; return x; }
private function g(): Result<i64> { return 1; }
",
        );
        assert_eq!(
            r.rendered(),
            "error[EN0424]: `?` needs the function to return `Result` or `T | null`
 --> main.en:1:42
  |
1 | private function f(): i64 { const x = g()?; return x; }
  |                                          ^ `f` returns `i64`
  |                       --- `i64` is the return type
  |
  = explain: run `enrang explain EN0424`

error: aborting due to 1 previous error
"
        );
    });
    h.case(
        "result/EN0424: `?` on a nullable in a `Result<T | null>` function, and in an arrow",
        || {
            let r = main_lib(
                "private function g(): i64 | null { return null; }
private function f(): Result<i64 | null> { const x = g()?; return x; }
private function k(): void { const a = (n: i64): i64 => { const y = g()?; return y; }; }
private function z(): i64 | null { const q = h()?; return q; }
private function h(): Result<i64> { return 1; }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0424 2:57 `?` needs the function to return `Result` or `T | null` [`f` returns `Result<i64 | null>`]",
                    "EN0424 3:72 `?` needs the function to return `Result` or `T | null` [this arrow returns `i64`]",
                    "EN0424 4:49 `?` needs the function to return `Result` or `T | null` [`z` returns `i64 | null`]",
                ]
            );
            let note = &r.diags[0].entries;
            assert_eq!(note.len(), 1, "{}", r.rendered());
            assert!(r.rendered().contains(
                "= note: the early return of `?` is never wrapped as a success, so it can't return `null` here"
            ));
        },
    );
    h.case(
        "result/EN0429: `?` on neither `Result` nor a nullable",
        || {
            let r =
                main_lib("private function z(): Result<i64> { const n: i64 = 3; return n?; }\n");
            assert_eq!(
                r.rendered(),
                "error[EN0429]: `?` needs a `Result` or `T | null`, found `i64`
 --> main.en:1:63
  |
1 | private function z(): Result<i64> { const n: i64 = 3; return n?; }
  |                                                               ^ `n` is `i64`
  |
  = explain: run `enrang explain EN0429`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "result/`?` among a program's statements takes any error type (S:1143)",
        || {
            let r = main_lib(
                "import { fs } from \"os\";
const text = fs.readFile(\"a.txt\")?;
console.log(text);
",
            );
            r.clean();
        },
    );
    h.case(
        "result/`?` in an arrow whose body decides its result decides it",
        || {
            let r = main_lib(
                "import { fs } from \"os\";
const r = (s: &string) => { const n = s.parseInt()?; return s.parseInt(); };
const k = (s: &string) => { const t = fs.readFile(s)?; return fs.readFile(s); };
",
            );
            r.clean();
            let b = crate::paths::statements(&r);
            let rets: Vec<String> = b.arrows.iter().map(|a| ty(&r, a.ret)).collect();
            assert_eq!(rets, ["i64 | null", "Result<string, IoError>"]);
        },
    );
}

fn unused(h: &mut Harness) {
    h.case("result/EN0426: an unused `Result`; `void` and an assignment use it", || {
        let r = main_lib(
            "private function save(): Result<void> { return; }
private function f(): void {
  save();
  void save();
  let r: Result<void> = save();
  r = save();
}
",
        );
        assert_eq!(
            diags(&r),
            ["EN0426 3:3 this `Result` is not used, so an error would be lost silently [returns `Result<void>`]"]
        );
    });
    h.case(
        "result/EN0453: an unused `@mustUse` result, with `keep it` for an assignable receiver",
        || {
            let r = main_lib(
                "private function f(name: &string, let other: string): void {
  name.trim();
  other.trim();
  void other.trim();
  other = other.trim();
}
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0453 2:3 the result of `trim` is not used [`trim` returns a new string and leaves `name` as it was]",
                    "EN0453 3:3 the result of `trim` is not used [`trim` returns a new string and leaves `other` as it was]",
                ]
            );
            assert_eq!(
                r.diags[0].helps[0].message,
                "keep the result, or discard it deliberately with `void`"
            );
            assert_eq!(r.diags[1].helps[0].message, "keep it");
            assert!(r.program.is_some(), "a warning stops nothing");
        },
    );
    h.case("result/EN0453 for a user function marked `@mustUse` (S:1142)", || {
        let r = main_lib(
            "@mustUse private function checksum(x: i64): u32 { return 0; }
private function g(): void { checksum(1); void checksum(2); const c = checksum(3); }
",
        );
        assert_eq!(
            diags(&r),
            ["EN0453 2:30 the result of `checksum` is not used [`checksum` is marked `@mustUse`]"]
        );
    });
    h.case("result/other values drop silently (S:1142)", || {
        let r = main_lib(
            "private function f(let q: i64[]): void { q.pop(); g(); 1 + 2; }
private function g(): i64 { return 1; }
",
        );
        r.clean();
        let b = body(&r, "main::f");
        assert!(matches!(expr_stmt(b, 0).kind, ExprKind::Call { .. }));
    });
}

/// G20 and G23's first diagnostic, through `load` and `analyze` on the host target.
fn goldens(h: &mut Harness) {
    h.case("result/G20 byte-exact through load and analyze", || {
        let case = case("G20");
        let file = &case.files[0];
        let r = run_with(
            &[(file.name.as_str(), file.contents.as_str())],
            LibSource::Embedded,
            enrang_target::host_target(),
        );
        let actual = r.rendered();
        assert!(
            actual == case.stderr.text,
            "G20: {}",
            line_diff(&case.stderr.text, &actual)
        );
        assert_eq!(case.exit, 1);
        assert!(r.diags.iter().any(|d| d.severity.fails()));
    });
    h.case(
        "result/G23's warning is the hand-built EN0453 (its EN0706 is phase 3)",
        || {
            let case = case("G23");
            let file = &case.files[0];
            let r = run_with(
                &[(file.name.as_str(), file.contents.as_str())],
                LibSource::Embedded,
                enrang_target::host_target(),
            );
            let rendered = r.rendered();
            let warning = rendered
                .split("\n\n")
                .next()
                .expect("a diagnostic")
                .to_owned();
            let expected = case
                .stderr
                .text
                .split("\n\n")
                .next()
                .expect("G23's warning")
                .to_owned();
            assert_eq!(warning.trim_end(), expected.trim_end());
            assert_eq!(r.diags.len(), 1, "{rendered}");
        },
    );
}

/// The SPEC case `id`.
fn case(id: &str) -> Case {
    let spec = std::fs::read_to_string(workspace_root().join("docs/SPEC.md")).expect("SPEC");
    extract_cases(&spec)
        .expect("SPEC's cases extract")
        .into_iter()
        .find(|c| c.id == id)
        .unwrap_or_else(|| panic!("no case {id}"))
}

/// Stage 6's review fixes of unused results and `?`'s owner.
fn review(h: &mut Harness) {
    h.case(
        "result/S:1142: the `void` fix-it parenthesises a ternary or `??` statement (SPEC 3.5)",
        || {
            let r = main_lib(
                "public function save(n: &string): Result<void> { return Err(\"x\"); }
public function a(c: bool, x: Result<void> | null): void { c ? save(\"a\") : save(\"b\"); x ?? save(\"b\"); (c ? save(\"a\") : save(\"b\")); save(\"c\"); }
",
            );
            let edits: Vec<Vec<(u32, String)>> = r
                .diags
                .iter()
                .map(|d| {
                    d.helps[0]
                        .edits
                        .iter()
                        .map(|e| (r.map.loc(e.span.lo).col, e.replacement.clone()))
                        .collect()
                })
                .collect();
            assert_eq!(
                edits,
                [
                    vec![(60, "void (".to_owned()), (85, ")".to_owned())],
                    vec![(87, "void (".to_owned()), (101, ")".to_owned())],
                    vec![(104, "void (".to_owned()), (129, ")".to_owned())],
                    vec![(132, "void ".to_owned())],
                ],
                "{}",
                r.rendered()
            );
        },
    );
    h.case(
        "result/S:1142: a statement `match` drops each arm's value: a `Result` arm is EN0426",
        || {
            let r = main_lib(
                "public function save(n: &string): Result<void> { return Err(\"x\"); }
public function a(k: i64): void { match (k) { 0 => save(\"a\"), default => save(\"b\") }; }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0426 2:52 this `Result` is not used, so an error would be lost silently [returns `Result<void>`]",
                    "EN0426 2:74 this `Result` is not used, so an error would be lost silently [returns `Result<void>`]",
                ]
            );
        },
    );
    h.case(
        "result/EN0424 among the program's statements: they `return`",
        || {
            let r = main_lib("const z = n()?;\npublic function n(): i64 | null { return 1; }\n");
            assert_eq!(
                diags(&r),
                ["EN0424 1:14 `?` needs the function to return `Result` or `T | null` [the program's statements return `int`]"]
            );
        },
    );
}
