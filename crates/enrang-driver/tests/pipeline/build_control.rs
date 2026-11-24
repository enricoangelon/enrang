//! Stage 2C's pipeline tests of the control constructs (M3 plan c.11-c.20).
//!
//! Until stage 2B's statements and expressions land, nothing in a built program
//! reaches 2C's entry points, so each case here checks a program through phases 1
//! and 2, finds the construct in its typed HIR, and calls the entry point on a
//! fresh `Builder` of that body (`drive`, the one place a builder is made here);
//! the body must pass the verifier. A golden is byte-exact only where every
//! sub-expression is a constant or a Copy local, which the skeleton lowers as the
//! real lowering does; elsewhere the cases assert the structure.

use std::path::Path;
use std::sync::Arc;

use enrang_base::Span;
use enrang_diag::RenderOpts;
use enrang_driver::{Session, check_types};
use enrang_hir::{self as hir, CheckedProgram, Tcx};
use enrang_mir::{Body, CaptureKind, Local, LocalKind, Operand, Place, Rvalue, print_body, verify};
use enrang_mirbuild::{
    BuildCx, Builder, ScopeKind, build_arrow_body, lower_array_build, lower_arrow_value,
    lower_coalesce, lower_const_read, lower_destructure, lower_err, lower_expect, lower_for_of,
    lower_literal_view, lower_match, lower_non_null, lower_opt_chain, lower_try,
};
use enrang_target::{TargetOpts, host_target, resolve};
use enrang_testkit::{Harness, TempDir, golden};

struct Program {
    tcx: Tcx,
    program: CheckedProgram,
}

fn checked(source: &str) -> Program {
    let dir = TempDir::new("pipeline-control");
    dir.write("main.en", source);
    checked_in(&dir)
}

fn checked_in(dir: &TempDir) -> Program {
    let mut session = Session::new();
    let target = Arc::new(
        resolve(host_target(), &TargetOpts::default())
            .expect("a target")
            .0,
    );
    match check_types(&mut session, dir.path(), Path::new("main.en"), target) {
        Ok(c) => Program {
            tcx: c.tcx,
            program: c.program,
        },
        Err(e) => panic!("{e:?}\n{}", session.render(&RenderOpts::default())),
    }
}

impl Program {
    /// The body of the function named `name`, the statements for `""`, the first
    /// test for `"#test"`.
    fn body(&self, name: &str) -> Arc<hir::Body> {
        if name.is_empty() {
            return self.program.statements.clone().expect("statements");
        }
        if name == "#test" {
            return self.program.bodies[&self.program.tests[0].def].clone();
        }
        let found = self
            .program
            .bodies
            .iter()
            .find(|(d, _)| self.tcx.def(**d).name().is_some_and(|n| n.as_str() == name));
        found.expect("a body of that name").1.clone()
    }

    /// Builds `name`'s body by `f` on a fresh builder; verifies it and prints it.
    fn drive(&self, name: &str, f: impl FnOnce(&mut Builder, &hir::Body)) -> (Body, String) {
        let hir = self.body(name);
        let cx = BuildCx {
            tcx: &self.tcx,
            program: &self.program,
        };
        let mut b = Builder::new(&cx, &hir);
        b.push_scope(ScopeKind::Body);
        f(&mut b, &hir);
        b.pop_scope();
        if b.cursor.is_some() {
            b.terminate(enrang_mir::TerminatorKind::Return, hir.span);
        }
        b.finish();
        let body = b.body;
        let text = print_body(&self.tcx, &body);
        if let Err(e) = verify(&self.tcx, &body) {
            panic!("{text}\n{e:#?}");
        }
        (body, text)
    }
}

/// Every expression of `b` in source order, outermost first.
fn exprs(b: &hir::Body) -> Vec<&hir::Expr> {
    let mut out = Vec::new();
    block_exprs(&b.root, &mut out);
    out
}

fn block_exprs<'a>(b: &'a hir::Block, out: &mut Vec<&'a hir::Expr>) {
    for s in &b.stmts {
        stmt_exprs(s, out);
    }
}

fn stmt_exprs<'a>(s: &'a hir::Stmt, out: &mut Vec<&'a hir::Expr>) {
    use hir::StmtKind as S;
    match &s.kind {
        S::Let { init, .. } => init.iter().for_each(|e| expr_rec(e, out)),
        S::Destructure { init, .. } => expr_rec(init, out),
        S::If { cond, then_, else_ } => {
            expr_rec(cond, out);
            block_exprs(then_, out);
            else_.iter().for_each(|b| block_exprs(b, out));
        }
        S::While { cond, body, .. } | S::DoWhile { cond, body, .. } => {
            expr_rec(cond, out);
            block_exprs(body, out);
        }
        S::ForOf { body, .. } | S::Block(body) | S::Unsafe(body) => block_exprs(body, out),
        S::Return(Some(e)) | S::Expr(e) => expr_rec(e, out),
        _ => {}
    }
}

fn expr_rec<'a>(e: &'a hir::Expr, out: &mut Vec<&'a hir::Expr>) {
    out.push(e);
    use hir::ExprKind as K;
    match &e.kind {
        K::Match { subject, arms } => {
            expr_rec(subject, out);
            for a in arms {
                if let hir::ArmBody::Expr(x) | hir::ArmBody::Return(Some(x)) = &a.body {
                    expr_rec(x, out);
                }
            }
        }
        K::Try(x, _) | K::NonNull(x) | K::Borrow(x) | K::VoidOp(x) => expr_rec(x, out),
        K::Coalesce(x, y) | K::Binary(_, x, y) => {
            expr_rec(x, out);
            expr_rec(y, out);
        }
        K::Call { args, .. } => args.iter().for_each(|a| expr_rec(a, out)),
        K::Assign { value, .. } => expr_rec(value, out),
        _ => {}
    }
}

fn check_golden(name: &str, text: &str) {
    if let Err(e) = golden("pipeline", &format!("mir/control/{name}.mir"), text) {
        panic!("{e}");
    }
}

/// The first expression of `name`'s body that `pick` accepts.
fn find<'a>(b: &'a hir::Body, pick: impl Fn(&hir::ExprKind) -> bool) -> &'a hir::Expr {
    exprs(b)
        .into_iter()
        .find(|e| pick(&e.kind))
        .expect("the construct")
}

/// The first statement of `b`, at any depth of its blocks, that `pick` accepts.
fn find_stmt<'a>(
    b: &'a hir::Block,
    pick: &dyn Fn(&hir::StmtKind) -> bool,
) -> Option<&'a hir::Stmt> {
    b.stmts.iter().find_map(|s| {
        if pick(&s.kind) {
            return Some(s);
        }
        match &s.kind {
            hir::StmtKind::If { then_, .. } => find_stmt(then_, pick),
            hir::StmtKind::Block(x) | hir::StmtKind::While { body: x, .. } => find_stmt(x, pick),
            _ => None,
        }
    })
}

fn ret() -> Place {
    Place::local(Local::RETURN)
}

/// A temporary of `t` for an entry point's destination.
fn dest(b: &mut Builder, t: hir::Ty) -> Place {
    Place::local(b.new_temp(t, Span::DUMMY))
}

/// Drives `lower_match` on the first `match` of `name`, into `_0` when it is the
/// returned value and into a temporary otherwise.
fn drive_match(p: &Program, name: &str) -> (Body, String) {
    p.drive(name, |b, hir| {
        let e = find(hir, |k| matches!(k, hir::ExprKind::Match { .. }));
        let hir::ExprKind::Match { subject, arms } = &e.kind else {
            unreachable!()
        };
        let d = match b.cx.tcx.kind(e.ty) {
            hir::TyKind::Void => dest(b, e.ty),
            _ => ret(),
        };
        lower_match(b, subject, arms, d, e.span);
    })
}

/// Drives the first `for...of` of `name`.
fn drive_for(p: &Program, name: &str) -> (Body, String) {
    p.drive(name, |b, hir| {
        let s =
            find_stmt(&hir.root, &|k| matches!(k, hir::StmtKind::ForOf { .. })).expect("a loop");
        let hir::StmtKind::ForOf {
            id,
            pat,
            source,
            body,
        } = &s.kind
        else {
            unreachable!()
        };
        lower_for_of(b, *id, pat, source, body, s.span);
    })
}

/// Drives the first destructuring statement of `name`; the locals a pattern
/// assigns are declared first, as their `let` would.
fn drive_destructure(p: &Program, name: &str) -> (Body, String) {
    p.drive(name, |b, hir| {
        let s = find_stmt(&hir.root, &|k| {
            matches!(k, hir::StmtKind::Destructure { .. })
                || matches!(k, hir::StmtKind::Expr(e) if matches!(e.kind, hir::ExprKind::Destructure { .. }))
        })
        .expect("a pattern");
        match &s.kind {
            hir::StmtKind::Destructure { pat, mode, init } => lower_destructure(b, pat, *mode, init),
            hir::StmtKind::Expr(e) => {
                let hir::ExprKind::Destructure { pat, value } = &e.kind else { unreachable!() };
                declare(b, pat);
                lower_destructure(b, pat, hir::BindingMode::Owned, value);
            }
            _ => unreachable!(),
        }
    })
}

fn declare(b: &mut Builder, pat: &hir::Pat) {
    match pat {
        hir::Pat::Bind(l) => {
            b.local(*l);
        }
        hir::Pat::Object(fs) => fs.iter().for_each(|(_, p)| declare(b, p)),
        hir::Pat::Tuple(ps) => ps.iter().for_each(|p| declare(b, p)),
        hir::Pat::Place(_) => {}
    }
}

/// Drives the first expression of `name` that `pick` accepts with `f`, into a
/// temporary of its type.
fn drive_expr(
    p: &Program,
    name: &str,
    pick: impl Fn(&hir::ExprKind) -> bool,
    f: impl FnOnce(&mut Builder, &hir::Expr, Place),
) -> (Body, String) {
    p.drive(name, |b, hir| {
        let e = find(hir, pick);
        let d = dest(b, e.ty);
        f(b, e, d);
    })
}

const SHAPE: &str = "private enum Shape { Circle { r: i64 }, Square, Tri }\n";
const ERR: &str = "private enum E { A }\n";

fn fun(decls: &str, sig: &str, body: &str) -> Program {
    checked(&format!("{decls}private function f({sig} {{\n{body}\n}}\n"))
}

fn has(text: &str, piece: &str) {
    assert!(text.contains(piece), "no `{piece}` in\n{text}");
}

pub fn register(h: &mut Harness) {
    match_cases(h);
    coalesce_chain(h);
    try_err(h);
    for_of(h);
    destructure(h);
    spread_consts(h);
    closures(h);
    narrowing(h);
}

fn match_cases(h: &mut Harness) {
    h.case(
        "control/match/cases share one switch, several values one target",
        || {
            let p = fun(
                SHAPE,
                "s: Shape): i64",
                "  return match (s) { Shape.Circle => 1, Shape.Square, Shape.Tri => 2 };",
            );
            check_golden("match_cases", &drive_match(&p, "f").1);
        },
    );
    h.case("control/match/a value repeated in a later arm keeps its first target", || {
        let p = fun(
            SHAPE,
            "s: Shape): i64",
            "  return match (s) { Shape.Circle => 1, Shape.Circle, Shape.Square => 2, Shape.Tri => 3 };",
        );
        has(&drive_match(&p, "f").1, "[0: bb2, 1: bb3, 2: bb4, otherwise: bb5];");
    });
    h.case("control/match/null on the outer level, a guard falls through", || {
        let p = fun(
            SHAPE,
            "s: Shape | null, flag: bool): i64",
            "  return match (s) { null => 0, Shape.Circle if flag => 1, Shape.Square => 2, default => 3 };",
        );
        check_golden("match_nullable_guard", &drive_match(&p, "f").1);
    });
    h.case(
        "control/match/literals and half-open ranges by compares",
        || {
            let p = fun(
                "",
                "n: i64): i64",
                "  return match (n) { 1, 2 => 10, 3..7 => 20, default => 30 };",
            );
            check_golden("match_literals", &drive_match(&p, "f").1);
        },
    );
    h.case(
        "control/match/a literal on a nullable tests null first, then the payload",
        || {
            let p = fun(
                "",
                "x: i64 | null): i64",
                "  return match (x) { null, 1 => 10, 2 => 20, default => 30 };",
            );
            check_golden("match_nullable_literal", &drive_match(&p, "f").1);
        },
    );
    h.case(
        "control/match/match (true) evaluates each condition in turn",
        || {
            let p = fun(
                "",
                "a: bool, c: bool): i64",
                "  return match (true) { a => 1, c => 2, default => 3 };",
            );
            check_golden("match_true", &drive_match(&p, "f").1);
        },
    );
    h.case("control/match/a string literal through Eq.equals", || {
        let p = fun(
            "",
            "s: string): i64",
            "  return match (s) { \"a\" => 1, default => 2 };",
        );
        let (_, text) = p.drive("f", |b, hir| {
            let e = find(hir, |k| matches!(k, hir::ExprKind::Match { .. }));
            let hir::ExprKind::Match { subject, arms } = &e.kind else {
                unreachable!()
            };
            lower_match(b, subject, arms, ret(), e.span);
        });
        has(&text, "string::equals(move _3, const \"a\": &string) -> bb");
        has(&text, "_3 = &_1 [auto-borrow];");
    });
    h.case("control/match/Ok and Err by the tag, a return arm", || {
        let p = fun(
            ERR,
            "r: Result<i64, E>): i64",
            "  match (r) { Ok => return 1, Err => {} }\n  return 0;",
        );
        check_golden("match_result", &drive_match(&p, "f").1);
    });
}

fn coalesce_chain(h: &mut Harness) {
    h.case("control/coalesce/the payload or the default", || {
        let p = fun("", "x: i64 | null): i64", "  return x ?? 5;");
        let (_, text) = drive_expr(
            &p,
            "f",
            |k| matches!(k, hir::ExprKind::Coalesce(..)),
            |b, e, _| {
                let hir::ExprKind::Coalesce(a, d) = &e.kind else {
                    unreachable!()
                };
                lower_coalesce(b, a, d, ret());
            },
        );
        check_golden("coalesce", &text);
    });
    h.case(
        "control/opt-chain/a field borrowed under the null test",
        || {
            let p = fun(
                "private class Node { public v: i64 = 0; }\n",
                "n: Node | null): &i64 | null",
                "  return n?.v;",
            );
            let (_, text) = drive_expr(
                &p,
                "f",
                |k| matches!(k, hir::ExprKind::OptionalChain(_)),
                |b, e, _| {
                    let hir::ExprKind::OptionalChain(c) = &e.kind else {
                        unreachable!()
                    };
                    lower_opt_chain(b, c, ret(), e.span);
                },
            );
            check_golden("opt_field", &text);
        },
    );
    h.case(
        "control/opt-chain/a call's result made present, null otherwise",
        || {
            let decls =
                "private class Node { public v: i64 = 0; public get(): i64 { return this.v; } }\n";
            let p = fun(decls, "n: &Node | null): i64 | null", "  return n?.get();");
            let (_, text) = drive_expr(
                &p,
                "f",
                |k| matches!(k, hir::ExprKind::OptionalChain(_)),
                |b, e, _| {
                    let hir::ExprKind::OptionalChain(c) = &e.kind else {
                        unreachable!()
                    };
                    lower_opt_chain(b, c, ret(), e.span);
                },
            );
            has(&text, "_0 = present(");
            has(&text, "_0 = null;");
            has(&text, "= discriminant(_1);");
        },
    );
    h.case(
        "control/opt-chain/a call that returns a nullable is the chain itself",
        || {
            let decls = "private class Node { public get(): i64 | null { return null; } }\n";
            let p = fun(decls, "n: Node | null): i64 | null", "  return n?.get();");
            let (_, text) = drive_expr(
                &p,
                "f",
                |k| matches!(k, hir::ExprKind::OptionalChain(_)),
                |b, e, _| {
                    let hir::ExprKind::OptionalChain(c) = &e.kind else {
                        unreachable!()
                    };
                    lower_opt_chain(b, c, ret(), e.span);
                },
            );
            assert!(!text.contains("present("), "{text}");
            has(&text, "_0 = null;");
        },
    );
    h.case(
        "control/non-null/a tag check right before the payload's use",
        || {
            let p = fun("", "x: i64 | null): i64", "  return x!;");
            let (_, text) = drive_expr(
                &p,
                "f",
                |k| matches!(k, hir::ExprKind::NonNull(_)),
                |b, e, _| {
                    let hir::ExprKind::NonNull(x) = &e.kind else {
                        unreachable!()
                    };
                    // The user of the payload's place emits its run (c.5).
                    let at = lower_non_null(b, x);
                    b.guard(at, e.span);
                    b.assign(ret(), Rvalue::Use(Operand::Copy(at)), e.span);
                },
            );
            check_golden("non_null", &text);
        },
    );
}

fn drive_try(p: &Program) -> String {
    drive_expr(
        p,
        "f",
        |k| matches!(k, hir::ExprKind::Try(..)),
        |b, e, d| {
            let hir::ExprKind::Try(x, kind) = &e.kind else {
                unreachable!()
            };
            let v = lower_try(b, x, *kind);
            b.assign(d, Rvalue::Use(v), e.span);
        },
    )
    .1
}

fn drive_err(p: &Program) -> String {
    let is_err = |k: &hir::ExprKind| {
        matches!(
            k,
            hir::ExprKind::Call {
                callee: hir::Callee::Form(hir::FormKind::Err(_)),
                ..
            }
        )
    };
    drive_expr(p, "f", is_err, |b, e, d| {
        let hir::ExprKind::Call {
            callee: hir::Callee::Form(hir::FormKind::Err(form)),
            args,
            ..
        } = &e.kind
        else {
            unreachable!()
        };
        lower_err(b, *form, &args[0], d, e.span);
    })
    .1
}

fn try_err(h: &mut Harness) {
    h.case(
        "control/try/the error moves into _0, the value into a temporary",
        || {
            let p = fun(
                ERR,
                "r: Result<i64, E>): Result<i64, E>",
                "  const v = r?;\n  return v;",
            );
            check_golden("try_result", &drive_try(&p));
        },
    );
    h.case(
        "control/try/another error type becomes a Failure first",
        || {
            let p = fun(
                "private enum E { A }\n",
                "r: Result<i64, E>): Result<i64>",
                "  const v = r?;\n  return v;",
            );
            check_golden("try_into_failure", &drive_try(&p));
        },
    );
    h.case("control/try/null returns null", || {
        let p = fun(
            "",
            "x: i64 | null): i64 | null",
            "  const v = x?;\n  return v;",
        );
        check_golden("try_nullable", &drive_try(&p));
    });
    h.case("control/err/a value is the error", || {
        let p = fun(ERR, "e: E): Result<i64, E>", "  return Err(e);");
        check_golden("err_value", &drive_err(&p));
    });
    h.case("control/err/a fixed text through FailureText", || {
        let p = fun("", "n: i64): Result<i64>", "  return Err(\"bad\");");
        let text = drive_err(&p);
        has(&text, "_3 = form failure_text(");
        has(&text, "::Err { error: move _3 };");
    });
    h.case("control/err/a text at a literal union is its case", || {
        let p = fun(
            "private type Level = \"low\" | \"high\";\n",
            "n: i64): Result<i64, Level>",
            "  return Err(\"high\");",
        );
        let text = drive_err(&p);
        assert!(!text.contains("form"), "{text}");
        has(&text, "::Err { error: ");
    });
    h.case(
        "control/err/text moves, text copies, another error converts",
        || {
            for (sig, form) in [
                ("s: string): Result<i64>", "failure_move"),
                ("s: &string): Result<i64>", "failure_copy"),
            ] {
                let p = fun("", sig, "  return Err(s);");
                has(&drive_err(&p), &format!("form {form}("));
            }
            let p = fun(
                "private enum E { A }\n",
                "e: E): Result<i64>",
                "  return Err(e);",
            );
            has(&drive_err(&p), "form into_failure(");
        },
    );
}

fn for_of(h: &mut Harness) {
    h.case("control/for-of/a path: head, bind, latch, recorded", || {
        let p = fun("", "xs: i64[]): void", "  for (const x of &xs) {}");
        let (body, text) = drive_for(&p, "f");
        check_golden("for_path", &text);
        assert_eq!(body.meta.loops.len(), 1);
    });
    h.case(
        "control/for-of/a range counts a cursor up to its end",
        || {
            let p = fun("", "n: i64): void", "  for (const i of 0..n) {}");
            let (body, text) = drive_for(&p, "f");
            check_golden("for_range", &text);
            assert!(body.meta.loops.is_empty());
        },
    );
    h.case(
        "control/for-of/an owned fixed array is copied element by element",
        || {
            let p = fun("", "a: i64[3]): void", "  for (const x of a) {}");
            let (body, text) = drive_for(&p, "f");
            check_golden("for_fixed", &text);
            assert!(body.meta.loops.is_empty());
        },
    );
    h.case(
        "control/for-of/an owned array moves into #iter, dropped at the end",
        || {
            let p = fun("", "xs: string[]): void", "  for (const x of xs) {}");
            let (body, text) = drive_for(&p, "f");
            has(&text, "#iter");
            has(&text, "= move _2[_");
            has(&text, "drop(_2);");
            assert!(body.meta.loops.is_empty());
        },
    );
    h.case(
        "control/for-of/a pattern binds its parts from the element",
        || {
            let p = fun(
                "",
                "ps: [i64, i64][]): void",
                "  for (const [a, b] of &ps) {}",
            );
            check_golden("for_pattern", &drive_for(&p, "f").1);
        },
    );
    h.case(
        "control/for-of/a borrowed non-path is a once source",
        || {
            let p = fun("", "m: &i64[][]): void", "  for (const x of &m[0]) {}");
            let (body, text) = drive_for(&p, "f");
            has(&text, "#src");
            has(&text, "[for-of-hidden]");
            assert!(matches!(
                body.meta.loops[0].source,
                enrang_mir::LoopSource::Once(_)
            ));
        },
    );
}

fn destructure(h: &mut Harness) {
    h.case(
        "control/destructure/an owned tuple: copies and moves",
        || {
            let p = fun("", "t: [i64, string]): void", "  const [a, b] = t;");
            check_golden("destructure_owned", &drive_destructure(&p, "f").1);
        },
    );
    h.case(
        "control/destructure/through a borrow: references to the parts",
        || {
            let decls = "private class Point { public x: i64 = 0; public y: i64 = 0; }\n";
            let p = fun(decls, "p: Point): void", "  const { x, y } = &p;");
            check_golden("destructure_ref", &drive_destructure(&p, "f").1);
        },
    );
    h.case(
        "control/destructure/an assignment stores each part in order",
        || {
            let p = fun(
                "",
                "s: string, t: string): void",
                "  let a = s;\n  let b = t;\n  [a, b] = [b, a];",
            );
            let (_, text) = drive_destructure(&p, "f");
            has(&text, "drop(_3) [assign];");
            has(&text, "drop(_4) [assign];");
            let first = text.find("_3 = move").expect("a store to a");
            let second = text.find("_4 = move").expect("a store to b");
            assert!(first < second, "{text}");
        },
    );
}

fn spread_consts(h: &mut Harness) {
    h.case(
        "control/spread/items push, spreads extend through a view",
        || {
            let p = fun("", "r: &i64[]): i64[]", "  return [...r, 1];");
            let (_, text) = p.drive("f", |b, hir| {
                let e = find(hir, |k| matches!(k, hir::ExprKind::ArrayBuild { .. }));
                let hir::ExprKind::ArrayBuild { elem, parts } = &e.kind else {
                    unreachable!()
                };
                lower_array_build(b, *elem, parts, ret(), e.span);
            });
            has(&text, "_2 = intrinsic AllocArray<i64>();");
            // `r` reborrowed (O7), converted, then `&_out` last (c.14).
            has(
                &text,
                "_3 = &*_1 [reborrow];\n    _4 = convert(array_to_slice, move _3);\n    _5 = &_2 [auto-borrow];",
            );
            has(&text, "Array<i64>::extendCloned(move _5, move _4) -> bb1;");
            has(&text, "_7 = const 1: i64;\n    _8 = &_2 [auto-borrow];");
            has(&text, "Array<i64>::push(move _8, copy _7) -> bb2;");
            has(&text, "_0 = move _2;");
        },
    );
    h.case("control/consts/a scalar, an aggregate, a reference constant", || {
        let decls = "private const K: i64 = 5;\nprivate const A: i64[2][2] = [[1, 2], [3, 4]];\nprivate const S: &string = \"hi\";\n";
        let p = fun(decls, "): void", "  const k = K;\n  const a = A;\n  const s = S;");
        let (_, text) = p.drive("f", |b, hir| {
            for e in exprs(hir) {
                if let hir::ExprKind::Static(def) = e.kind {
                    let d = dest(b, e.ty);
                    lower_const_read(b, def, e.ty, d, e.span);
                }
            }
        });
        check_golden("consts", &text);
    });
    h.case(
        "control/consts/a literal view borrows a statement temporary",
        || {
            let p = fun("", "): void", "  const v: &Slice<i64> = &[1, 2, 3];");
            let (_, text) = drive_expr(
                &p,
                "f",
                |k| matches!(k, hir::ExprKind::Borrow(_)),
                |b, e, _| {
                    let op = lower_literal_view(b, e);
                    let tcx = b.cx.tcx;
                    let t = tcx.mk_ref(tcx.mk_slice(tcx.common().i64));
                    let d = dest(b, t);
                    b.assign(d, Rvalue::Use(op), e.span);
                },
            );
            has(&text, "[literal-view];");
            has(&text, "= convert(fixed_to_slice, move _");
        },
    );
    h.case(
        "control/expect/shared borrows of the values, constants as they are",
        || {
            let dir = TempDir::new("pipeline-control");
            dir.write("main.en", "public function one(): i64 { return 1; }\n");
            dir.write(
                "main.test.en",
                "test(\"one\", () => {\n  const n = one();\n  expect(n).not.toBe(2);\n});\n",
            );
            let p = checked_in(&dir);
            let (_, text) = p.drive("#test", |b, hir| {
                let s = find_stmt(&hir.root, &|k| matches!(k, hir::StmtKind::Expect(_)))
                    .expect("an expect");
                let hir::StmtKind::Expect(f) = &s.kind else {
                    unreachable!()
                };
                lower_expect(b, f);
            });
            check_golden("expect", &text);
        },
    );
}

fn closures(h: &mut Harness) {
    h.case(
        "control/closures/captures by kind, the env, the closure value",
        || {
            let p = fun(
                "",
                "n: i64, r: &i64, g: () => void): void",
                "  const c = () => { g(); console.log(n, r); };\n  c();",
            );
            let (_, text) = drive_expr(
                &p,
                "f",
                |k| matches!(k, hir::ExprKind::Arrow(_)),
                |b, e, d| {
                    let hir::ExprKind::Arrow(a) = e.kind else {
                        unreachable!()
                    };
                    lower_arrow_value(b, a, d, e.span);
                },
            );
            check_golden("arrow_value", &text);
        },
    );
    h.case(
        "control/closures/an arrow body takes its env, then its parameters",
        || {
            let p = fun(
                "",
                "n: i64, r: &i64): i64",
                "  const c = (k: i64) => n + k + *r;\n  return c(1);",
            );
            let cx = BuildCx {
                tcx: &p.tcx,
                program: &p.program,
            };
            let owner = p.body("f").owner;
            let body = build_arrow_body(&cx, owner, hir::ArrowId(0));
            verify(&p.tcx, &body).expect("verified");
            let text = print_body(&p.tcx, &body);
            assert_eq!(body.arg_count, 2);
            assert_eq!(body.locals[Local(1)].kind, LocalKind::ClosureEnv);
            let kinds: Vec<CaptureKind> = body.captures.iter().map(|c| c.kind).collect();
            assert_eq!(
                kinds,
                [CaptureKind::Path, CaptureKind::ThroughRef],
                "{text}"
            );
            assert_eq!(p.tcx.ty_string(body.locals[Local(1)].ty), "&[&i64, &i64]");
        },
    );
    h.case(
        "control/closures/a non-capturing arrow at an fn type is arrow_fn",
        || {
            let p = fun("", "): void", "  const c = () => 1;\n  c();");
            let (_, text) = p.drive("f", |b, hir| {
                let e = find(hir, |k| matches!(k, hir::ExprKind::Arrow(_)));
                let hir::ExprKind::Arrow(a) = e.kind else {
                    unreachable!()
                };
                let tcx = b.cx.tcx;
                let sig = hir::FnPtrSig {
                    unsafety: false,
                    params: vec![],
                    ret: tcx.common().i64,
                    ret_readonly: false,
                };
                let d = dest(b, tcx.mk_fn_ptr(hir::Abi::Enrang, sig));
                lower_arrow_value(b, a, d, e.span);
            });
            has(&text, "= arrow_fn#0;");
        },
    );
}

fn narrowing(h: &mut Harness) {
    h.case(
        "control/narrowing/a capture's record and the facts rooted at locals",
        || {
            let p = fun(
                "",
                "n: i64 | null): void",
                "  if (n != null) {\n    const c = () => n;\n    c();\n  }",
            );
            let (body, text) = drive_expr(
                &p,
                "f",
                |k| matches!(k, hir::ExprKind::Arrow(_)),
                |b, e, d| {
                    let hir::ExprKind::Arrow(a) = e.kind else {
                        unreachable!()
                    };
                    lower_arrow_value(b, a, d, e.span);
                },
            );
            assert_eq!(body.meta.records.len(), 1, "{text}");
            has(&text, " capture;");
            has(&text, "fact f0: _1 nonnull;");
        },
    );
}
