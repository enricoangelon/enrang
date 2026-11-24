//! Exhaustiveness and redundancy (owner 2D; plan d.13, g.2; SPEC 6 S:1134-1135; A:916)
//! on hand-built `hir::Match` expressions.
//!
//! The engine needs nothing of sema but `Tcx`, so this suite includes
//! `src/exhaust/` as it is (module `engine`). Each case is a program: its
//! declarations are loaded and lowered by `support::run`, and its first `match` is
//! built as typing builds it (plan c.5) from the parsed tree, with the spans the
//! parser gave: subject typed by its parameter's declared type, arm values as
//! constants, cases, `null`, ranges and conditions, `Arm.value_spans` per value.
//! Typing's own `match` arrives with stage 3A; until then this is the HIR the pass
//! is run on. G12 is compared byte for byte with SPEC's block.

#[path = "../../src/exhaust/mod.rs"]
pub(crate) mod engine;

#[path = "../../src/passes/walk.rs"]
mod walk;

use enrang_base::{BytePos, Span, intern};
use enrang_diag::{DiagCtx, Diagnostic, RenderOpts, render_text};
use enrang_hir::{
    Arm, ArmBody, ArmValue, ConstValue, Expr, ExprId, ExprKind, Tcx, Ty, TyKind, VariantIdx,
};
use enrang_syntax::{NodeIdGen, ParseMode, ast, parse_file};
use enrang_testkit::{Harness, extract_cases, line_diff, workspace_root};

use crate::support::{Run, run};

/// A program whose first `match` has been built as HIR.
pub struct Built {
    pub run: Run,
    pub file: String,
    pub text: String,
    /// Where the file starts in the run's source map.
    pub start: BytePos,
    pub expr: Expr,
}

impl Built {
    /// The diagnostics the engine gives the `match`.
    pub fn diags(&self) -> Vec<Diagnostic> {
        engine::check_match(&self.run.tcx, &self.expr)
    }

    /// Those diagnostics as `enrang check` prints them.
    pub fn rendered(&self) -> String {
        render_text(&self.diags(), &self.run.map, &RenderOpts { color: false })
    }

    /// The span of the `nth` occurrence of `needle` in the file.
    pub fn span(&self, needle: &str, nth: usize) -> Span {
        let at = self
            .text
            .match_indices(needle)
            .nth(nth)
            .unwrap_or_else(|| panic!("no occurrence {nth} of {needle:?}"))
            .0;
        let lo = self.start + at as u32;
        Span {
            lo,
            hi: lo + needle.len() as u32,
        }
    }

    /// The arms of the `match`.
    pub fn arms(&self) -> &[Arm] {
        match &self.expr.kind {
            ExprKind::Match { arms, .. } => arms,
            _ => unreachable!("a match"),
        }
    }

    /// `text` with every edit of every help of `diags` applied.
    pub fn fixed(&self, diags: &[Diagnostic]) -> String {
        let mut edits: Vec<_> = diags
            .iter()
            .flat_map(|d| &d.helps)
            .flat_map(|h| &h.edits)
            .collect();
        edits.sort_by_key(|e| std::cmp::Reverse(e.span.lo));
        let mut text = self.text.clone();
        for e in edits {
            let lo = (e.span.lo.0 - self.start.0) as usize;
            let hi = (e.span.hi.0 - self.start.0) as usize;
            text.replace_range(lo..hi, &e.replacement);
        }
        text
    }
}

/// Loads `text` as `file` with the suite's fake library and builds its first
/// `match`, which must sit in a function whose parameters type its subject.
pub fn build(file: &str, text: &str) -> Built {
    let run = run(&[(file, text)]);
    // `analyze` types the body too since stage 3A, so its match pass already reports
    // what this hand-built `match` will; any other diagnostic is a broken case.
    assert!(
        run.diags
            .iter()
            .all(|d| matches!(d.code.name(), "EN0501" | "EN0503")),
        "{}",
        run.rendered()
    );
    let module = file.strip_suffix(".en").expect("an .en file");
    let start = run
        .tcx
        .defs()
        .find(|(_, d)| d.path.module.as_str() == module && !d.span.is_dummy())
        .map(|(_, d)| run.map.file_of(d.span.lo).start)
        .expect("a declaration in the file");
    let source = run.map.file_of(start).clone();
    let mut dcx = DiagCtx::new();
    let tree = parse_file(&source, &mut NodeIdGen::new(), ParseMode::Build, &mut dcx);
    assert!(!dcx.has_errors(), "the case parses");
    let (function, subject, arms, span) = tree
        .items
        .iter()
        .find_map(|item| match &item.kind {
            ast::ItemKind::Function(f) => {
                find_match_in_block(&f.body).map(|(s, a, sp)| (f.name.name, s, a, sp))
            }
            _ => None,
        })
        .expect("a function with a match");
    let sig = run.tcx.sig(run.def(&format!("{module}::{function}")));
    let params: Vec<(String, Ty)> = sig
        .params
        .iter()
        .map(|p| (p.name.to_string(), p.ty))
        .collect();
    let expr = lower_match(&run.tcx, &params, subject, arms, span);
    Built {
        file: file.to_owned(),
        text: text.to_owned(),
        start,
        expr,
        run,
    }
}

type Found<'a> = (&'a ast::Expr, &'a [ast::MatchArm], Span);

fn find_match_in_block(b: &ast::Block) -> Option<Found<'_>> {
    b.stmts.iter().find_map(|s| match &s.kind {
        ast::StmtKind::Return(Some(e)) | ast::StmtKind::Expr(e) => find_match(e),
        ast::StmtKind::VarDecl(v) => v.init.as_ref().and_then(find_match),
        ast::StmtKind::Block(b) => find_match_in_block(b),
        _ => None,
    })
}

fn find_match(e: &ast::Expr) -> Option<Found<'_>> {
    match &e.kind {
        ast::ExprKind::Match { subject, arms } => Some((subject, arms, e.span)),
        ast::ExprKind::Paren(inner) => find_match(inner),
        _ => None,
    }
}

fn hexpr(ty: Ty, span: Span, kind: ExprKind) -> Expr {
    Expr::new(ExprId(0), ty, span, kind)
}

/// `t` with references, boxes and `| null` looked through.
fn innermost(tcx: &Tcx, mut t: Ty) -> Ty {
    loop {
        match tcx.kind(t) {
            TyKind::Ref(inner) | TyKind::Boxed(inner) | TyKind::Nullable(inner) => t = inner,
            _ => return t,
        }
    }
}

/// An integer constant of type `ty` (an integer type, else `i64`).
fn int_const(tcx: &Tcx, ty: Ty, v: i128) -> ConstValue {
    let ty = match tcx.kind(ty) {
        TyKind::Int(_) => ty,
        _ => tcx.common().i64,
    };
    let TyKind::Int(int) = tcx.kind(ty) else {
        unreachable!()
    };
    let width = int.bits(u32::from(tcx.target().layout.ptr_bytes) * 8);
    let mask = if width == 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    };
    ConstValue::Int((v as u128) & mask, ty)
}

fn int_of(e: &ast::Expr) -> Option<i128> {
    match &e.kind {
        ast::ExprKind::Int { value, .. } => Some(*value as i128),
        ast::ExprKind::Unary(ast::UnOp::Neg, inner) => int_of(inner).map(|v| -v),
        ast::ExprKind::Paren(inner) => int_of(inner),
        _ => None,
    }
}

/// The `match` as typing builds it (plan c.5), for a subject that is a parameter
/// or `true`.
fn lower_match(
    tcx: &Tcx,
    params: &[(String, Ty)],
    subject: &ast::Expr,
    arms: &[ast::MatchArm],
    span: Span,
) -> Expr {
    let common = *tcx.common();
    let subject = match &subject.kind {
        ast::ExprKind::Ident(name) => {
            let ty = params
                .iter()
                .find(|(p, _)| p == name.as_str())
                .map(|(_, t)| *t)
                .unwrap_or_else(|| panic!("no parameter `{name}`"));
            hexpr(ty, subject.span, ExprKind::Never)
        }
        ast::ExprKind::Bool(b) => hexpr(
            common.bool,
            subject.span,
            ExprKind::Const(ConstValue::Bool(*b)),
        ),
        other => panic!("unsupported subject {other:?}"),
    };
    let base = innermost(tcx, subject.ty);
    let condition = matches!(subject.kind, ExprKind::Const(_));
    let enum_case = |name: &str| -> VariantIdx {
        let TyKind::Adt(adt, _) = tcx.kind(base) else {
            panic!("a case on a subject that is no enum")
        };
        let e = tcx.adt(adt).as_enum().expect("an enum");
        e.variant_named(intern(name))
            .map(|(v, _)| v)
            .unwrap_or_else(|| panic!("no case `{name}`"))
    };
    let lower_value = |v: &ast::ArmValue| -> (ArmValue, Span) {
        match v {
            ast::ArmValue::Null(s) => (ArmValue::Null, *s),
            ast::ArmValue::Ok(s) => (ArmValue::Case(VariantIdx::OK), *s),
            ast::ArmValue::Err(s) => (ArmValue::Case(VariantIdx::ERR), *s),
            ast::ArmValue::Case(path) => {
                let last = path.last().expect("a path");
                let s = path[0].span.to(last.span);
                (ArmValue::Case(enum_case(last.name.as_str())), s)
            }
            ast::ArmValue::Range(a, b) => {
                let lo = int_const(tcx, base, int_of(a).expect("an integer"));
                let hi = int_const(tcx, base, int_of(b).expect("an integer"));
                (ArmValue::Range(lo, hi), a.span.to(b.span))
            }
            ast::ArmValue::Value(e) if condition && !matches!(e.kind, ast::ExprKind::Bool(_)) => (
                ArmValue::Cond(hexpr(common.bool, e.span, ExprKind::Never)),
                e.span,
            ),
            ast::ArmValue::Value(e) => {
                let value = match &e.kind {
                    ast::ExprKind::Bool(b) => ConstValue::Bool(*b),
                    ast::ExprKind::Str(s) => ConstValue::Str(tcx.intern_str(s.as_str())),
                    ast::ExprKind::Float(f) => {
                        let v: f64 = f.as_str().parse().expect("a float");
                        float_const(tcx, base, v)
                    }
                    ast::ExprKind::Unary(ast::UnOp::Neg, inner)
                        if matches!(inner.kind, ast::ExprKind::Float(_)) =>
                    {
                        let ast::ExprKind::Float(f) = &inner.kind else {
                            unreachable!()
                        };
                        let v: f64 = f.as_str().parse().expect("a float");
                        float_const(tcx, base, -v)
                    }
                    _ => int_const(tcx, base, int_of(e).expect("a literal")),
                };
                (ArmValue::Const(value), e.span)
            }
        }
    };
    let arms = arms
        .iter()
        .map(|arm| {
            let (values, value_spans) = arm.values.iter().map(lower_value).unzip();
            Arm {
                values,
                guard: arm
                    .guard
                    .as_ref()
                    .map(|g| hexpr(common.bool, g.span, ExprKind::Never)),
                body: ArmBody::Expr(hexpr(common.void, arm.span, ExprKind::Never)),
                span: arm.span,
                value_spans,
            }
        })
        .collect();
    hexpr(
        common.void,
        span,
        ExprKind::Match {
            subject: Box::new(subject),
            arms,
        },
    )
}

/// `Shape` of SPEC 6 and G12.
const SHAPE: &str = "public enum Shape {
  Circle { radius: f64 },
  Square { side: f64 },
  Empty,
}
";

/// A program of `SHAPE` and `function f(<params>)` whose body returns `body`.
fn shape_program(params: &str, body: &str) -> String {
    format!("{SHAPE}\npublic function f({params}): i64 {{\n  return {body};\n}}\n")
}

/// Asserts the rendered diagnostics of `text`'s first `match`.
fn expect_rendered(text: &str, expected: &str) {
    let built = build("src/main.en", text);
    let actual = built.rendered();
    assert!(actual == expected, "{}", line_diff(expected, &actual));
}

/// Asserts the `match` of `text` gets no diagnostic.
fn expect_clean(text: &str) {
    let built = build("src/main.en", text);
    let actual = built.rendered();
    assert!(actual.is_empty(), "{actual}");
}

/// The codes and messages of `text`'s first `match`, in order.
fn heads(text: &str) -> Vec<String> {
    build("src/main.en", text)
        .diags()
        .iter()
        .map(|d| format!("{}: {}", d.code.name(), d.message))
        .collect()
}

/// A float literal at the subject's float type, as typing gives it: `f32` bits for
/// an `f32` subject, else `f64`.
fn float_const(tcx: &Tcx, base: Ty, v: f64) -> ConstValue {
    let common = tcx.common();
    match tcx.kind(base) {
        TyKind::Float(enrang_hir::FloatTy::F32) => {
            ConstValue::Float(u64::from((v as f32).to_bits()), common.f32)
        }
        _ => ConstValue::Float(v.to_bits(), common.f64),
    }
}

pub fn register(h: &mut Harness) {
    g12(h);
    exhaustiveness(h);
    redundancy(h);
    layouts(h);
    skipped(h);
    review(h);
}

/// The cases of stage 6's review of 2D (`fix-2`): each fails without its fix or
/// kills a mutant that survived the review.
fn review(h: &mut Harness) {
    h.case(
        "exhaust/a comma inside a comment after the last arm is no comma",
        || {
            for tail in [
                "Shape.Square => 2 // squares, too\n  }",
                "Shape.Square => 2 /* a, b */\n  }",
                "Shape.Square => 2 /* a */ // b, c\n  }",
            ] {
                let text = shape_program(
                    "s: Shape",
                    &format!("match (s) {{\n    Shape.Circle => 1,\n    {tail}"),
                );
                let built = build("src/main.en", &text);
                let diags = built.diags();
                assert_eq!(diags[0].helps[0].edits.len(), 2, "{tail}");
                let fixed = built.fixed(&diags);
                assert!(fixed.contains("    Shape.Square => 2,"), "{fixed}");
                assert!(build("src/main.en", &fixed).diags().is_empty(), "{fixed}");
            }
            // A comma after the comment is the last arm's own.
            let text = shape_program(
                "s: Shape",
                "match (s) {\n    Shape.Circle => 1,\n    Shape.Square => 2 /* a */ ,\n  }",
            );
            let built = build("src/main.en", &text);
            assert_eq!(built.diags()[0].helps[0].edits.len(), 1);
        },
    );
    h.case(
        "exhaust/the passes' walk reaches a `match` inside a `match (true)` condition",
        || {
            let built = build(
                "src/main.en",
                &shape_program("s: Shape", "match (s) {\n    Shape.Circle => 1,\n  }"),
            );
            let tcx = &built.run.tcx;
            let common = *tcx.common();
            let inner = built.expr.clone();
            // The outer `match` has no place in a source, so it gets no fix-it.
            let span = Span::DUMMY;
            let subject = hexpr(common.bool, span, ExprKind::Const(ConstValue::Bool(true)));
            let arm = Arm {
                values: vec![ArmValue::Cond(inner)],
                guard: None,
                body: ArmBody::Expr(hexpr(common.void, span, ExprKind::Never)),
                span,
                value_spans: vec![span],
            };
            let outer = hexpr(
                common.void,
                span,
                ExprKind::Match {
                    subject: Box::new(subject),
                    arms: vec![arm],
                },
            );
            let module = tcx.modules().next().expect("a module").0;
            let mut body = enrang_hir::Body::empty(
                enrang_hir::BodyOwner::Statements(module),
                common.void,
                span,
            );
            body.root.stmts.push(enrang_hir::Stmt {
                kind: enrang_hir::StmtKind::Expr(outer),
                span,
            });
            let mut found = Vec::new();
            walk::for_each_expr(&body, &mut |e| {
                if matches!(e.kind, ExprKind::Match { .. }) {
                    found.extend(engine::check_match(tcx, e));
                }
            });
            let messages: Vec<&str> = found.iter().map(|d| d.message.as_str()).collect();
            assert_eq!(
                messages,
                [
                    "`match (true)` needs a `default` arm",
                    "`match` doesn't handle `Shape.Square`"
                ]
            );
        },
    );
    h.case(
        "exhaust/a bool match with no arm: `true`, then `false` (X04)",
        || {
            let text = "public function f(b: bool): i64 {\n  return match (b) {\n  };\n}\n";
            let built = build("src/main.en", text);
            let diags = built.diags();
            assert_eq!(diags[0].message, "`match` doesn't handle `true`");
            let fixed = built.fixed(&diags);
            assert!(
                fixed.contains(
                    "    true => panic(\"unhandled\"),\n    false => panic(\"unhandled\"),\n  };"
                ),
                "{fixed}"
            );
        },
    );
    h.case(
        "exhaust/EN0503 names the first value that covers it (X06)",
        || {
            let text = shape_program(
                "s: Shape",
                "match (s) {\n    Shape.Circle => 1,\n    Shape.Circle => 2,\n    Shape.Circle => 3,\n    Shape.Square => 4,\n    Shape.Empty => 5,\n  }",
            );
            let built = build("src/main.en", &text);
            let diags = built.diags();
            assert_eq!(diags.len(), 2);
            let first = built.span("Shape.Circle", 0);
            for (d, nth) in diags.iter().zip([1, 2]) {
                assert_eq!(d.primary.span, built.span("Shape.Circle", nth));
                assert_eq!(d.secondary[0].span, first, "{nth}");
                assert_eq!(d.secondary[0].text, "already handled here");
            }
        },
    );
    h.case(
        "exhaust/`match (true)` with no condition names the value (X15)",
        || {
            assert_eq!(
                heads("public function f(): i64 {\n  return match (true) {\n    false => 1,\n  };\n}\n"),
                [
                    "EN0501: `match` doesn't handle `true`",
                    "EN0503: this arm is never reached"
                ]
            );
        },
    );
    h.case(
        "exhaust/only the guards of the arms matching the first missing value (X16)",
        || {
            let text = shape_program(
                "s: &Shape, g: bool, h: bool",
                "match (s) {\n    Shape.Circle if g => 1,\n    Shape.Square if h => 2,\n    Shape.Empty => 3,\n  }",
            );
            let built = build("src/main.en", &text);
            let diags = built.diags();
            assert_eq!(diags.len(), 1);
            assert_eq!(diags[0].message, "`match` doesn't handle every `Shape.Circle`");
            let labels: Vec<(&str, &str)> = diags[0]
                .secondary
                .iter()
                .map(|l| (built.run.map.text(l.span), l.text.as_str()))
                .collect();
            assert_eq!(labels, [("g", "only when this is true")]);
        },
    );
    h.case("exhaust/an `f32` subject compares its literals as `f32` (X25)", || {
        let text = "public function f(x: f32): i64 {\n  return match (x) {\n    1.5 => 1,\n    0.0 => 2,\n    -0.0 => 3,\n    default => 4,\n  };\n}\n";
        let built = build("src/main.en", text);
        let diags = built.diags();
        assert_eq!(diags.len(), 1, "{}", built.rendered());
        assert_eq!(diags[0].code.name(), "EN0503");
        assert_eq!(diags[0].primary.span, built.span("-0.0", 0));
        assert_eq!(diags[0].secondary[0].span, built.span("0.0", 0));
    });
}

fn g12(h: &mut Harness) {
    h.case("exhaust/G12 byte-exact from a hand-built match", || {
        let spec = std::fs::read_to_string(workspace_root().join("docs/SPEC.md")).expect("SPEC");
        let cases = extract_cases(&spec).expect("SPEC's cases extract");
        let case = cases.iter().find(|c| c.id == "G12").expect("G12");
        assert_eq!(case.files.len(), 1);
        let file = &case.files[0];
        let built = build(&file.name, &file.contents);
        let actual = built.rendered();
        assert!(
            actual == case.stderr.text,
            "{}",
            line_diff(&case.stderr.text, &actual)
        );
        assert_eq!(case.exit, 1);
        assert!(built.diags().iter().any(|d| d.severity.fails()));
    });
    h.case("exhaust/G12's fix-it makes the match exhaustive", || {
        let spec = std::fs::read_to_string(workspace_root().join("docs/SPEC.md")).expect("SPEC");
        let cases = extract_cases(&spec).expect("SPEC's cases extract");
        let file = &cases.iter().find(|c| c.id == "G12").expect("G12").files[0];
        let built = build(&file.name, &file.contents);
        let fixed = built.fixed(&built.diags());
        assert!(
            fixed.contains("    Shape.Empty => panic(\"unhandled\"),\n  };"),
            "{fixed}"
        );
        assert!(build(&file.name, &fixed).diags().is_empty());
    });
}

fn exhaustiveness(h: &mut Harness) {
    h.case("exhaust/every case listed: no diagnostic", || {
        expect_clean(&shape_program(
            "s: &Shape",
            "match (s) {\n    Shape.Circle => 1,\n    Shape.Square => 2,\n    Shape.Empty => 3,\n  }",
        ));
    });
    h.case("exhaust/a default covers the missing cases", || {
        expect_clean(&shape_program(
            "s: Shape",
            "match (s) {\n    Shape.Circle => 1,\n    default => 0,\n  }",
        ));
    });
    h.case(
        "exhaust/a case only guarded arms list: every `Shape.Circle` (S:1134)",
        || {
            expect_rendered(
                &shape_program(
                    "s: &Shape",
                    "match (s) {\n    Shape.Circle if s.radius > 10.0 => 1,\n    Shape.Square => 2,\n    Shape.Empty => 3,\n  }",
                ),
                "error[EN0501]: `match` doesn't handle every `Shape.Circle`
  --> src/main.en:8:17
   |
 8 |   return match (s) {
   |                 ^ missing other `Shape.Circle` values
 9 |     Shape.Circle if s.radius > 10.0 => 1,
   |                     --------------- only when this is true
   |
help: add an arm for the other circles: `Shape.Circle => ...,`
   |
12 +     Shape.Circle => panic(\"unhandled\"),
   = explain: run `enrang explain EN0501`

error: aborting due to 1 previous error
",
            );
        },
    );
    h.case("exhaust/two guarded arms: a label under each guard", || {
        let text = shape_program(
            "s: &Shape, a: bool, b: bool",
            "match (s) {\n    Shape.Circle if a => 1,\n    Shape.Circle if b => 2,\n    Shape.Square => 2,\n    Shape.Empty => 3,\n  }",
        );
        let built = build("src/main.en", &text);
        let diags = built.diags();
        assert_eq!(diags.len(), 1);
        let labels: Vec<(Span, &str)> = diags[0]
            .secondary
            .iter()
            .map(|l| (l.span, l.text.as_str()))
            .collect();
        let guard = |a: usize| built.arms()[a].guard.as_ref().expect("a guard").span;
        assert_eq!(built.run.map.text(guard(0)), "a");
        assert_eq!(built.run.map.text(guard(1)), "b");
        assert_eq!(
            labels,
            vec![
                (guard(0), "only when this is true"),
                (guard(1), "only when this is true"),
            ]
        );
    });
    h.case("exhaust/a guarded case beside a plain one is handled", || {
        expect_clean(&shape_program(
            "s: &Shape, big: bool",
            "match (s) {\n    Shape.Circle if big => 1,\n    Shape.Circle => 0,\n    Shape.Square => 2,\n    Shape.Empty => 3,\n  }",
        ));
    });
    h.case("exhaust/a nullable enum without `null` (S:1135)", || {
        expect_rendered(
            &shape_program(
                "s: Shape | null",
                "match (s) {\n    Shape.Circle => 1,\n    Shape.Square => 2,\n    Shape.Empty => 3,\n  }",
            ),
            "error[EN0501]: `match` doesn't handle `null`
  --> src/main.en:8:17
   |
 8 |   return match (s) {
   |                 ^ missing `null`
   |
help: add `null => ...,`
   |
12 +     null => panic(\"unhandled\"),
   = explain: run `enrang explain EN0501`

error: aborting due to 1 previous error
",
        );
    });
    h.case("exhaust/a nullable enum with `null` and every case", || {
        expect_clean(&shape_program(
            "s: &Shape | null",
            "match (s) {\n    null => 0,\n    Shape.Circle => 1,\n    Shape.Square => 2,\n    Shape.Empty => 3,\n  }",
        ));
    });
    h.case("exhaust/an inner null is a present null (S:1134)", || {
        expect_rendered(
            &shape_program(
                "s: (Shape | null) | null",
                "match (s) {\n    null => 0,\n    Shape.Circle => 1,\n    Shape.Square => 2,\n    Shape.Empty => 3,\n  }",
            ),
            "error[EN0501]: `match` doesn't handle a present null
  --> src/main.en:8:17
   |
 8 |   return match (s) {
   |                 ^ missing a present null
   |
help: add `default => ...,`
   |
13 +     default => panic(\"unhandled\"),
   = explain: run `enrang explain EN0501`

error: aborting due to 1 previous error
",
        );
    });
    h.case(
        "exhaust/a present null needs a default, not a `null` arm",
        || {
            expect_clean(&shape_program(
                "s: (Shape | null) | null",
                "match (s) {\n    null => 0,\n    Shape.Circle => 1,\n    default => 3,\n  }",
            ));
        },
    );
    h.case(
        "exhaust/present values come before `null`, cases in declaration order",
        || {
            let text = shape_program("s: Shape | null", "match (s) {\n    Shape.Square => 1,\n  }");
            let built = build("src/main.en", &text);
            let diags = built.diags();
            assert_eq!(diags.len(), 1);
            assert_eq!(diags[0].message, "`match` doesn't handle `Shape.Circle`");
            assert_eq!(
                diags[0].helps[0].message,
                "add `Shape.Circle => ...`, `Shape.Empty => ...`, `null => ...`, or a `default` arm"
            );
            assert!(
                built.fixed(&diags).contains(
                    "    Shape.Square => 1,\n    Shape.Circle => panic(\"unhandled\"),\n    Shape.Empty => panic(\"unhandled\"),\n    null => panic(\"unhandled\"),\n  };"
                ),
                "{}",
                built.fixed(&diags)
            );
        },
    );
    h.case(
        "exhaust/several missing cases: the first named, every one inserted",
        || {
            expect_rendered(
                &shape_program("s: &Shape", "match (s) {\n    Shape.Circle => 1,\n  }"),
                "error[EN0501]: `match` doesn't handle `Shape.Square`
  --> src/main.en:8:17
   |
 3 |   Square { side: f64 },
   |   ------ `Shape.Square` is declared here
...
 8 |   return match (s) {
   |                 ^ missing `Shape.Square`
   |
help: add `Shape.Square => ...`, `Shape.Empty => ...`, or a `default` arm
   |
10 +     Shape.Square => panic(\"unhandled\"),
11 +     Shape.Empty => panic(\"unhandled\"),
   = explain: run `enrang explain EN0501`

error: aborting due to 1 previous error
",
            );
        },
    );
    h.case("exhaust/a string-literal union with every value needs no default", || {
        expect_clean(
            "public type Dir = \"left\" | \"right\";\npublic function f(d: Dir): i64 {\n  return match (d) {\n    \"left\" => 1,\n    \"right\" => 2,\n  };\n}\n",
        );
    });
    h.case("exhaust/a string-literal union's value prints as its literal", || {
        let text = "public type Q = \"say \\\"hi\\\"\" | \"x\";\npublic function f(q: Q): i64 {\n  return match (q) {\n    \"x\" => 1,\n  };\n}\n";
        let built = build("src/main.en", text);
        let diags = built.diags();
        assert_eq!(diags[0].message, "`match` doesn't handle `\"say \\\"hi\\\"\"`");
        assert_eq!(
            built.run.map.text(diags[0].secondary[0].span),
            "\"say \\\"hi\\\"\""
        );
    });
    h.case("exhaust/a case's declaration label skips its decorator", || {
        let text = "public enum Shape {\n  Circle { radius: f64 },\n  @was(\"Empty\") Empty,\n  @was(\"OldVacant\") Vacant,\n}\npublic function f(s: Shape): i64 {\n  return match (s) {\n    Shape.Circle => 1,\n  };\n}\n";
        let built = build("src/main.en", text);
        let diags = built.diags();
        assert_eq!(diags[0].message, "`match` doesn't handle `Shape.Empty`");
        assert_eq!(diags[0].secondary[0].span, built.span("Empty", 1));
        assert_eq!(diags[0].helps[0].edits.len(), 1);
        let fixed = built.fixed(&diags);
        assert!(build("src/main.en", &fixed).diags().is_empty(), "{fixed}");
    });
    h.case("exhaust/a case's label is the whole name, not part of a word", || {
        let text = "public enum E {\n  A,\n  @was(\"t\") s,\n}\npublic function f(e: E): i64 {\n  return match (e) {\n    E.A => 1,\n  };\n}\n";
        let built = build("src/main.en", text);
        let diags = built.diags();
        assert_eq!(diags[0].message, "`match` doesn't handle `E.s`");
        let name = built.span(") s", 0);
        assert_eq!(
            diags[0].secondary[0].span,
            Span {
                lo: name.lo + 2,
                hi: name.hi
            }
        );
    });
    h.case("exhaust/a string-literal union missing a value", || {
        expect_rendered(
            "public type Dir = \"left\" | \"right\";\npublic function f(d: Dir): i64 {\n  return match (d) {\n    \"left\" => 1,\n  };\n}\n",
            "error[EN0501]: `match` doesn't handle `\"right\"`
 --> src/main.en:3:17
  |
1 | public type Dir = \"left\" | \"right\";
  |                            ------- `\"right\"` is declared here
2 | public function f(d: Dir): i64 {
3 |   return match (d) {
  |                 ^ missing `\"right\"`
  |
help: add `\"right\" => ...`, or a `default` arm
  |
5 +     \"right\" => panic(\"unhandled\"),
  = explain: run `enrang explain EN0501`

error: aborting due to 1 previous error
",
        );
    });
    h.case("exhaust/numbers always need default (SPEC 6)", || {
        expect_rendered(
            "public function f(x: i64): i64 {\n  return match (x) {\n    200, 201 => 1,\n    404 => 2,\n  };\n}\n",
            "error[EN0501]: `match` doesn't handle every `i64`
 --> src/main.en:2:17
  |
2 |   return match (x) {
  |                 ^ only a `default` arm handles every `i64`
  |
help: add `default => ...,`
  |
5 +     default => panic(\"unhandled\"),
  = explain: run `enrang explain EN0501`

error: aborting due to 1 previous error
",
        );
    });
    h.case("exhaust/arms over every u8 still need default", || {
        assert_eq!(
            heads(
                "public function f(x: u8): i64 {\n  return match (x) {\n    0..128 => 1,\n    128..255 => 2,\n    255 => 3,\n  };\n}\n"
            ),
            ["EN0501: `match` doesn't handle every `u8`"]
        );
    });
    h.case("exhaust/numbers with a default", || {
        expect_clean(
            "public function f(x: i64): i64 {\n  return match (x) {\n    200..300 => 1,\n    404 => 2,\n    default => 3,\n  };\n}\n",
        );
    });
    h.case("exhaust/strings always need default (SPEC 6)", || {
        assert_eq!(
            heads("public function f(s: &string): i64 {\n  return match (s) {\n    \"left\" => 1,\n    \"right\" => 2,\n  };\n}\n"),
            ["EN0501: `match` doesn't handle every `string`"]
        );
        expect_clean(
            "public function f(s: string): i64 {\n  return match (s) {\n    \"left\" => 1,\n    default => 2,\n  };\n}\n",
        );
    });
    h.case("exhaust/floats always need default", || {
        assert_eq!(
            heads(
                "public function f(x: f64): i64 {\n  return match (x) {\n    1.5 => 1,\n  };\n}\n"
            ),
            ["EN0501: `match` doesn't handle every `f64`"]
        );
    });
    h.case("exhaust/a nullable number: `null`, then every number", || {
        assert_eq!(
            heads("public function f(x: i64 | null): i64 {\n  return match (x) {\n    null => 0,\n    1 => 1,\n  };\n}\n"),
            ["EN0501: `match` doesn't handle every `i64`"]
        );
        expect_clean(
            "public function f(x: &string | null): i64 {\n  return match (x) {\n    null => 0,\n    \"admin\" => 1,\n    default => 2,\n  };\n}\n",
        );
    });
    h.case("exhaust/a class subject needs default", || {
        assert_eq!(
            heads("public final class User { }\npublic function f(u: User | null): i64 {\n  return match (u) {\n    null => 0,\n  };\n}\n"),
            ["EN0501: `match` doesn't handle every `User`"]
        );
    });
    h.case("exhaust/`Result` arms are bare `Ok` and `Err`", || {
        let text = "public function f(r: Result<i64, Failure>): i64 {\n  return match (r) {\n    Ok => 1,\n  };\n}\n";
        let built = build("src/main.en", text);
        let diags = built.diags();
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].message, "`match` doesn't handle `Err`");
        assert_eq!(diags[0].primary.text, "missing `Err`");
        assert!(diags[0].secondary.is_empty(), "no label in the library");
        assert_eq!(
            diags[0].helps[0].message,
            "add `Err => ...`, or a `default` arm"
        );
        expect_clean(
            "public function f(r: Result<i64, Failure>): i64 {\n  return match (r) {\n    Ok => 1,\n    Err => 2,\n  };\n}\n",
        );
    });
    h.case("exhaust/booleans: `true` and `false`", || {
        assert_eq!(
            heads("public function f(b: bool): i64 {\n  return match (b) {\n    true => 1,\n  };\n}\n"),
            ["EN0501: `match` doesn't handle `false`"]
        );
        expect_clean(
            "public function f(b: bool): i64 {\n  return match (b) {\n    false => 0,\n    true => 1,\n  };\n}\n",
        );
    });
    h.case("exhaust/`match (true)`: conditions cover nothing but default", || {
        expect_rendered(
            "public function f(age: i64): i64 {\n  return match (true) {\n    age < 13 => 1,\n    age < 20 => 2,\n  };\n}\n",
            "error[EN0501]: `match (true)` needs a `default` arm
 --> src/main.en:2:17
  |
2 |   return match (true) {
  |                 ^^^^ no arm runs when every condition is false
  |
help: add `default => ...,`
  |
5 +     default => panic(\"unhandled\"),
  = explain: run `enrang explain EN0501`

error: aborting due to 1 previous error
",
        );
        expect_clean(
            "public function f(age: i64): i64 {\n  return match (true) {\n    age < 13 => 1,\n    age < 20 => 2,\n    default => 3,\n  };\n}\n",
        );
    });
    h.case("exhaust/a subject behind a box is looked through", || {
        assert_eq!(
            heads(&shape_program(
                "s: Box<Shape>",
                "match (s) {\n    Shape.Circle => 1,\n    Shape.Square => 2,\n  }"
            )),
            ["EN0501: `match` doesn't handle `Shape.Empty`"]
        );
    });
    h.case("exhaust/a guarded default covers nothing", || {
        let text = shape_program(
            "s: Shape, g: bool",
            "match (s) {\n    Shape.Circle => 1,\n    Shape.Square => 2,\n    default if g => 3,\n  }",
        );
        let built = build("src/main.en", &text);
        let diags = built.diags();
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].message, "`match` doesn't handle every `Shape.Empty`");
        assert_eq!(diags[0].secondary.len(), 1);
        assert_eq!(built.run.map.text(diags[0].secondary[0].span), "g");
        assert_eq!(
            diags[0].helps[0].message,
            "add an arm for the other empties: `Shape.Empty => ...,`"
        );
    });
    h.case("exhaust/a match with no arm", || {
        let text = shape_program("s: Shape", "match (s) {\n  }");
        let built = build("src/main.en", &text);
        let diags = built.diags();
        assert_eq!(diags[0].message, "`match` doesn't handle `Shape.Circle`");
        let fixed = built.fixed(&diags);
        assert!(
            fixed.contains("match (s) {\n    Shape.Circle => panic(\"unhandled\"),\n    Shape.Square => panic(\"unhandled\"),\n    Shape.Empty => panic(\"unhandled\"),\n  };"),
            "{fixed}"
        );
        assert!(build("src/main.en", &fixed).diags().is_empty());
    });
    h.case("exhaust/plural of a case name for S:1134's help", || {
        let cases = [
            ("Circle", "circles"),
            ("Empty", "empties"),
            ("Day", "days"),
            ("Box", "boxes"),
            ("Match", "matches"),
            ("BadSector", "bad sectors"),
            ("HTTPError", "http errors"),
            ("Not_Found", "not founds"),
            ("V2", "v2s"),
        ];
        for (name, plural) in cases {
            assert_eq!(engine::report::plural(name), plural, "{name}");
        }
    });
}

fn redundancy(h: &mut Harness) {
    h.case("exhaust/EN0503 on a duplicate case", || {
        expect_rendered(
            &shape_program(
                "s: &Shape",
                "match (s) {\n    Shape.Circle => 1,\n    Shape.Circle => 2,\n    Shape.Square => 3,\n    Shape.Empty => 4,\n  }",
            ),
            "warning[EN0503]: this arm is never reached
  --> src/main.en:10:5
   |
 9 |     Shape.Circle => 1,
   |     ------------ already handled here
10 |     Shape.Circle => 2,
   |     ^^^^^^^^^^^^ every value it matches is handled above
",
        );
    });
    h.case("exhaust/EN0503 on an arm after default", || {
        let text = shape_program(
            "s: Shape",
            "match (s) {\n    default => 0,\n    Shape.Circle => 1,\n  }",
        );
        let built = build("src/main.en", &text);
        let diags = built.diags();
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].message, "this arm is never reached");
        assert_eq!(diags[0].primary.span, built.span("Shape.Circle", 0));
        assert_eq!(diags[0].secondary[0].span, built.span("default", 0));
        assert_eq!(diags[0].secondary[0].text, "already handled here");
    });
    h.case("exhaust/EN0503 on a default no value reaches", || {
        let text = shape_program(
            "s: Shape",
            "match (s) {\n    Shape.Circle, Shape.Square => 1,\n    Shape.Empty => 2,\n    default => 0,\n  }",
        );
        let built = build("src/main.en", &text);
        let diags = built.diags();
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].message, "this arm is never reached");
        assert_eq!(diags[0].primary.span, built.span("default", 0));
        assert_eq!(diags[0].primary.text, "every value it matches is handled above");
        assert!(diags[0].secondary.is_empty(), "no single arm covers it");
    });
    h.case("exhaust/EN0503 on a range inside an earlier range", || {
        expect_rendered(
            "public function f(x: i64): i64 {\n  return match (x) {\n    0..10 => 1,\n    3..5 => 2,\n    default => 3,\n  };\n}\n",
            "warning[EN0503]: this arm is never reached
 --> src/main.en:4:5
  |
3 |     0..10 => 1,
  |     ----- already handled here
4 |     3..5 => 2,
  |     ^^^^ every value it matches is handled above
",
        );
    });
    h.case("exhaust/EN0503 on a range two earlier ranges cover", || {
        let text = "public function f(x: i64): i64 {\n  return match (x) {\n    0..5 => 1,\n    5..10 => 2,\n    2..8 => 3,\n    8..11 => 4,\n    default => 5,\n  };\n}\n";
        let built = build("src/main.en", text);
        let diags = built.diags();
        assert_eq!(diags.len(), 1, "8..11 still reaches 10");
        assert_eq!(diags[0].primary.span, built.span("2..8", 0));
        assert!(diags[0].secondary.is_empty());
    });
    h.case("exhaust/EN0503 on a negative literal inside a range", || {
        let text = "public function f(x: i64): i64 {\n  return match (x) {\n    -10..0 => 1,\n    -5 => 2,\n    0 => 3,\n    default => 4,\n  };\n}\n";
        let built = build("src/main.en", text);
        let diags = built.diags();
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].primary.span, built.span("-5", 0));
    });
    h.case("exhaust/EN0503 on a literal at a range's last value", || {
        let text = "public function f(x: i64): i64 {\n  return match (x) {\n    0..10 => 1,\n    9 => 2,\n    10 => 3,\n    default => 4,\n  };\n}\n";
        let built = build("src/main.en", text);
        let diags = built.diags();
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].primary.span, built.span("9", 0));
        assert_eq!(diags[0].secondary[0].span, built.span("0..10", 0));
    });
    h.case("exhaust/an empty range after other arms has no covering arm", || {
        let text = "public function f(x: i64): i64 {\n  return match (x) {\n    1 => 1,\n    7..3 => 2,\n    default => 4,\n  };\n}\n";
        let built = build("src/main.en", text);
        let diags = built.diags();
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].primary.span, built.span("7..3", 0));
        assert_eq!(diags[0].primary.text, "no value can match this");
        assert!(diags[0].secondary.is_empty());
    });
    h.case("exhaust/EN0503 names the very value that covers it", || {
        let text = shape_program(
            "s: Shape",
            "match (s) {\n    Shape.Square, Shape.Circle => 1,\n    Shape.Circle => 2,\n    default => 3,\n  }",
        );
        let built = build("src/main.en", &text);
        let diags = built.diags();
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].primary.span, built.span("Shape.Circle", 1));
        assert_eq!(diags[0].secondary[0].span, built.span("Shape.Circle", 0));
    });
    h.case("exhaust/EN0503 on an empty range", || {
        let text = "public function f(x: i64): i64 {\n  return match (x) {\n    5..5 => 1,\n    default => 4,\n  };\n}\n";
        let built = build("src/main.en", text);
        let diags = built.diags();
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].message, "this arm is never reached");
        assert_eq!(diags[0].primary.text, "no value can match this");
        assert!(diags[0].secondary.is_empty());
    });
    h.case(
        "exhaust/EN0503 on a duplicate value of a reachable arm",
        || {
            let text = shape_program(
                "s: Shape",
                "match (s) {\n    Shape.Circle, Shape.Square, Shape.Circle => 1,\n    Shape.Empty => 2,\n  }",
            );
            let built = build("src/main.en", &text);
            let diags = built.diags();
            assert_eq!(diags.len(), 1);
            assert_eq!(diags[0].message, "this value is never reached");
            assert_eq!(diags[0].primary.span, built.span("Shape.Circle", 1));
            assert_eq!(diags[0].secondary[0].span, built.span("Shape.Circle", 0));
        },
    );
    h.case("exhaust/EN0503 on duplicate literals and strings", || {
        assert_eq!(
            heads("public function f(x: i64): i64 {\n  return match (x) {\n    1, 2 => 1,\n    2 => 2,\n    default => 3,\n  };\n}\n"),
            ["EN0503: this arm is never reached"]
        );
        assert_eq!(
            heads("public function f(s: string): i64 {\n  return match (s) {\n    \"a\" => 1,\n    \"b\", \"a\" => 2,\n    default => 3,\n  };\n}\n"),
            ["EN0503: this value is never reached"]
        );
        assert_eq!(
            heads("public function f(x: f64): i64 {\n  return match (x) {\n    0.0 => 1,\n    -0.0 => 2,\n    default => 3,\n  };\n}\n"),
            ["EN0503: this arm is never reached"]
        );
    });
    h.case("exhaust/a guarded arm covers nothing, so a later arm is reached", || {
        expect_clean(&shape_program(
            "s: Shape, g: bool",
            "match (s) {\n    Shape.Circle if g => 1,\n    Shape.Circle => 2,\n    Shape.Square => 3,\n    Shape.Empty => 4,\n  }",
        ));
    });
    h.case("exhaust/EN0503 on a guarded arm after its case", || {
        let text = shape_program(
            "s: Shape, g: bool",
            "match (s) {\n    Shape.Circle => 1,\n    Shape.Circle if g => 2,\n    default => 4,\n  }",
        );
        let built = build("src/main.en", &text);
        let diags = built.diags();
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].primary.span, built.span("Shape.Circle", 1));
    });
    h.case("exhaust/EN0503 on a condition after default", || {
        let text = "public function f(age: i64): i64 {\n  return match (true) {\n    default => 3,\n    age < 13 => 1,\n  };\n}\n";
        let built = build("src/main.en", text);
        let diags = built.diags();
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].message, "this arm is never reached");
        assert_eq!(diags[0].primary.span, built.span("age < 13", 0));
    });
    h.case("exhaust/conditions of one arm do not cover each other", || {
        expect_clean(
            "public function f(age: i64): i64 {\n  return match (true) {\n    age < 13, age < 13 => 1,\n    default => 3,\n  };\n}\n",
        );
    });
    h.case(
        "exhaust/values of a guarded arm cover its later values",
        || {
            let text = shape_program(
                "s: Shape, g: bool",
                "match (s) {\n    Shape.Circle, Shape.Circle if g => 1,\n    default => 4,\n  }",
            );
            let built = build("src/main.en", &text);
            let diags = built.diags();
            assert_eq!(diags.len(), 1);
            assert_eq!(diags[0].message, "this value is never reached");
            assert_eq!(diags[0].primary.span, built.span("Shape.Circle", 1));
        },
    );
    h.case("exhaust/`null` after `null` and a constant subject's other value", || {
        assert_eq!(
            heads("public function f(x: i64 | null): i64 {\n  return match (x) {\n    null => 0,\n    null => 1,\n    default => 2,\n  };\n}\n"),
            ["EN0503: this arm is never reached"]
        );
        let text = "public function f(): i64 {\n  return match (true) {\n    false => 0,\n    default => 2,\n  };\n}\n";
        let built = build("src/main.en", text);
        let diags = built.diags();
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].primary.text, "no value can match this");
    });
    h.case("exhaust/EN0501 and EN0503 together", || {
        assert_eq!(
            heads(&shape_program(
                "s: Shape",
                "match (s) {\n    Shape.Circle => 1,\n    Shape.Circle => 2,\n  }"
            )),
            [
                "EN0501: `match` doesn't handle `Shape.Square`",
                "EN0503: this arm is never reached"
            ]
        );
    });
}

fn layouts(h: &mut Harness) {
    h.case("exhaust/a one-line match gets its arm before `}`", || {
        let text = shape_program(
            "s: Shape",
            "match (s) { Shape.Circle => 1, Shape.Square => 2 }",
        );
        let built = build("src/main.en", &text);
        let diags = built.diags();
        let fixed = built.fixed(&diags);
        assert!(
            fixed.contains(
                "match (s) { Shape.Circle => 1, Shape.Square => 2, Shape.Empty => panic(\"unhandled\"), }"
            ),
            "{fixed}"
        );
        assert!(build("src/main.en", &fixed).diags().is_empty());
    });
    h.case("exhaust/a one-line match with a trailing comma", || {
        let text = shape_program("s: Shape", "match (s) { Shape.Circle => 1, }");
        let built = build("src/main.en", &text);
        let fixed = built.fixed(&built.diags());
        assert!(
            fixed.contains("match (s) { Shape.Circle => 1, Shape.Square => panic(\"unhandled\"), Shape.Empty => panic(\"unhandled\"), }"),
            "{fixed}"
        );
        assert!(build("src/main.en", &fixed).diags().is_empty());
    });
    h.case("exhaust/an empty one-line match", || {
        let text = shape_program("s: Shape", "match (s) {}");
        let built = build("src/main.en", &text);
        let fixed = built.fixed(&built.diags());
        assert!(
            fixed.contains("match (s) { default => panic(\"unhandled\"), }")
                || fixed.contains("match (s) { Shape.Circle => panic(\"unhandled\"), Shape.Square => panic(\"unhandled\"), Shape.Empty => panic(\"unhandled\"), }"),
            "{fixed}"
        );
        assert!(build("src/main.en", &fixed).diags().is_empty());
    });
    h.case("exhaust/a last arm with no comma gets one", || {
        let text = shape_program(
            "s: Shape",
            "match (s) {\n    Shape.Circle => 1,\n    Shape.Square => 2\n  }",
        );
        let built = build("src/main.en", &text);
        let diags = built.diags();
        assert_eq!(diags[0].helps[0].edits.len(), 2);
        let fixed = built.fixed(&diags);
        assert!(
            fixed
                .contains("    Shape.Square => 2,\n    Shape.Empty => panic(\"unhandled\"),\n  };"),
            "{fixed}"
        );
        assert!(build("src/main.en", &fixed).diags().is_empty());
    });
    h.case("exhaust/a statement match in a nested block keeps its indentation", || {
        let text = format!(
            "{SHAPE}\npublic function f(s: Shape): void {{\n  {{\n      match (s) {{\n\t  Shape.Circle => {{}},\n      }}\n  }}\n}}\n"
        );
        let built = build("src/main.en", &text);
        let fixed = built.fixed(&built.diags());
        assert!(
            fixed.contains("\t  Shape.Circle => {},\n\t  Shape.Square => panic(\"unhandled\"),\n\t  Shape.Empty => panic(\"unhandled\"),\n      }"),
            "{fixed}"
        );
    });
}

fn skipped(h: &mut Harness) {
    h.case("exhaust/a subject typing rejected is not checked", || {
        let text = shape_program("s: Shape", "match (s) {\n    Shape.Circle => 1,\n  }");
        let mut built = build("src/main.en", &text);
        let error = built.run.tcx.common().error;
        if let ExprKind::Match { subject, .. } = &mut built.expr.kind {
            subject.ty = error;
        }
        assert!(built.diags().is_empty());
        let nullable_error = built.run.tcx.mk_nullable(error);
        if let ExprKind::Match { subject, .. } = &mut built.expr.kind {
            subject.ty = nullable_error;
        }
        assert!(built.diags().is_empty());
    });
    h.case(
        "exhaust/an arm value that does not fit the subject is not checked",
        || {
            let text = shape_program("s: Shape", "match (s) {\n    Shape.Circle => 1,\n  }");
            let mut built = build("src/main.en", &text);
            if let ExprKind::Match { arms, .. } = &mut built.expr.kind {
                arms[0].values = vec![ArmValue::Null];
            }
            assert!(built.diags().is_empty(), "`null` on a non-nullable subject");
            if let ExprKind::Match { arms, .. } = &mut built.expr.kind {
                arms[0].values = vec![ArmValue::Case(VariantIdx(7))];
            }
            assert!(built.diags().is_empty(), "a case the enum does not have");
            if let ExprKind::Match { arms, .. } = &mut built.expr.kind {
                arms[0].values = vec![ArmValue::Const(ConstValue::Bool(true))];
            }
            assert!(built.diags().is_empty(), "a boolean on an enum");
        },
    );
    h.case("exhaust/a `never` subject is not checked", || {
        let text = shape_program("s: Shape", "match (s) {\n    Shape.Circle => 1,\n  }");
        let mut built = build("src/main.en", &text);
        let never = built.run.tcx.common().never;
        if let ExprKind::Match { subject, .. } = &mut built.expr.kind {
            subject.ty = never;
        }
        assert!(built.diags().is_empty());
    });
    h.case(
        "exhaust/an expression that is no match gives nothing",
        || {
            let text = shape_program("s: Shape", "match (s) {\n    default => 1,\n  }");
            let built = build("src/main.en", &text);
            let ExprKind::Match { subject, .. } = &built.expr.kind else {
                unreachable!()
            };
            assert!(engine::check_match(&built.run.tcx, subject).is_empty());
            assert_eq!(built.arms().len(), 1);
            let _ = &built.file;
        },
    );
    h.case(
        "exhaust/a hand-built match with no source still reports",
        || {
            let text = shape_program("s: Shape", "match (s) {\n    Shape.Circle => 1,\n  }");
            let mut built = build("src/main.en", &text);
            built.expr.span = Span::DUMMY;
            if let ExprKind::Match { arms, .. } = &mut built.expr.kind {
                for arm in arms {
                    arm.span = Span::DUMMY;
                    arm.value_spans.clear();
                }
            }
            let diags = built.diags();
            assert_eq!(diags[0].message, "`match` doesn't handle `Shape.Square`");
            assert!(diags[0].helps[0].edits.is_empty());
        },
    );
}
