//! What `analyze` returns beside the bodies for phase 3 (M3 plan 0.3, K5-K8): the
//! recorded satisfactions, deduplicated and in path order; each local function's
//! hidden arguments with the top-level variables they name; the spans of `this` in
//! field initialisers; and the nullable's present case on narrowed payloads.

use enrang_diag::Milestone;
use enrang_hir::{ExprKind, LangItem, StmtKind, TopVar, VariantIdx};
use enrang_testkit::Harness;

use crate::paths::main_lib;
use crate::support::Run;

fn program(r: &Run) -> &enrang_hir::CheckedProgram {
    r.program.as_ref().expect("checked")
}

/// The recorded satisfactions as `found <- member`, in order.
fn satisfactions(r: &Run) -> Vec<String> {
    program(r)
        .satisfactions
        .iter()
        .map(|s| {
            format!(
                "{} <- {}",
                r.tcx.def(s.found).path,
                r.tcx.def(s.member).path
            )
        })
        .collect()
}

pub fn register(h: &mut Harness) {
    h.case(
        "program/each lang item of M3 is declared once in the library, in its layer (K9)",
        || {
            let r = main_lib("");
            r.clean();
            let m3: Vec<LangItem> = LangItem::ALL
                .iter()
                .copied()
                .filter(|i| i.since() == Milestone::M3)
                .collect();
            assert_eq!(
                m3.len(),
                8,
                "K9's six and `mem_replace`, `mem_swap` (A:943)"
            );
            for item in m3 {
                let declaring: Vec<String> = r
                    .tcx
                    .defs()
                    .filter(|(_, d)| d.attrs.lang == Some(item))
                    .map(|(_, d)| d.path.to_string())
                    .collect();
                assert_eq!(declaring.len(), 1, "{item}: {declaring:?}");
                let folder = item.layer().folder();
                assert!(
                    declaring[0].starts_with(&format!("{folder}/")),
                    "{item}: {declaring:?}"
                );
                assert!(r.tcx.lang_opt(item).is_some(), "{item}");
            }
            let push = r.tcx.lang(LangItem::ArrayPush);
            assert_eq!(r.tcx.def(push).path.to_string(), "alloc/array::Array::push");
            let start = r.tcx.lang(LangItem::Start);
            let never = r.tcx.common().never;
            assert_eq!(r.tcx.sig(start).ret, never);
        },
    );
    h.case(
        "program/satisfactions: one per member found and interface member, in path order (K6)",
        || {
            let r = main_lib(
                "const c = new C();\n\
                 show(&c);\n\
                 show(&c);\n\
                 public interface Named { name(): i64; size(): i64; }\n\
                 public class C implements Named { public name(): i64 { return 1; } public size(): i64 { return 2; } }\n\
                 public function show(n: &Named): i64 { return n.name(); }\n",
            );
            r.clean();
            assert_eq!(
                satisfactions(&r),
                [
                    "main::C::name <- main::Named::name",
                    "main::C::size <- main::Named::size",
                ]
            );
            // The first by site: the first call, on line 2, before the `implements`
            // clause on line 5 and the second call.
            for s in &program(&r).satisfactions {
                assert_eq!(r.map.loc(s.site.lo).line, 2, "{s:?}");
                assert_eq!(r.tcx.ty_string(s.ty), "C");
                assert_eq!(r.tcx.ty_string(s.iface), "Named");
            }
        },
    );
    h.case(
        "program/no interface used, no satisfaction recorded",
        || {
            let r = main_lib("public class C { public f(): i64 { return 1; } }\n");
            r.clean();
            assert!(program(&r).satisfactions.is_empty());
        },
    );
    h.case(
        "program/a local function's hidden arguments and the top variables (K7)",
        || {
            let r = main_lib(
                "let n = 1;\nconst s = \"a\";\nfunction bump(): void { n = n + 1; }\nfunction twice(): void { bump(); bump(); }\nfunction quiet(): i64 { return 3; }\ntwice();\nquiet();\n",
            );
            r.clean();
            let p = program(&r);
            let names: Vec<(&str, String, bool)> = p
                .top_vars
                .iter()
                .map(|v| (v.name.as_str(), r.tcx.ty_string(v.ty), v.mutable))
                .collect();
            assert_eq!(
                names,
                [
                    ("args", "string[]".to_owned(), false),
                    ("n", "int".to_owned(), true),
                    ("s", "string".to_owned(), false),
                ]
            );
            let hidden = |path: &str| p.hidden_args.get(&r.def(path)).cloned().unwrap_or_default();
            assert_eq!(hidden("main::bump"), [TopVar(1)]);
            assert_eq!(hidden("main::twice"), [TopVar(1)], "through `bump`");
            assert!(hidden("main::quiet").is_empty());
        },
    );
    h.case(
        "program/a program with no statements has no top variables",
        || {
            let r = main_lib("public function f(): void { }\n");
            r.clean();
            assert!(program(&r).top_vars.is_empty());
            assert!(program(&r).hidden_args.is_empty());
        },
    );
    h.case(
        "program/each `this` of a field initialiser is kept, with no report (K8)",
        || {
            let r = main_lib(
                "public class A { public x: i64 = 1; public y: i64 = this.x; }\n\
                 public class B extends A { public override y: i64 = this.x + this.x; }\n\
                 public class D { public x: i64 = 1; }\n",
            );
            r.clean();
            let p = program(&r);
            let spans = |class: &str| {
                let adt = r.tcx.adt_of(r.def(class)).expect("a class");
                p.field_inits[&adt]
                    .this_spans
                    .iter()
                    .map(|s| {
                        let loc = r.map.loc(s.lo);
                        (loc.line, loc.col, r.map.text(*s).to_owned())
                    })
                    .collect::<Vec<_>>()
            };
            assert_eq!(spans("main::A"), [(1, 53, "this".to_owned())]);
            assert_eq!(
                spans("main::B"),
                [(2, 53, "this".to_owned()), (2, 62, "this".to_owned())]
            );
            assert!(spans("main::D").is_empty());
        },
    );
    h.case(
        "program/a narrowed payload names the present case, VariantIdx::PRESENT (K5)",
        || {
            let r = main_lib(
                "public function f(x: i64 | null): i64 { if (x != null) { return x; } return 0; }\n",
            );
            r.clean();
            let body = &program(&r).bodies[&r.def("main::f")];
            let StmtKind::If { then_, .. } = &body.root.stmts[0].kind else {
                panic!("{:?}", body.root.stmts[0].kind);
            };
            let StmtKind::Return(Some(e)) = &then_.stmts[0].kind else {
                panic!("{:?}", then_.stmts[0].kind);
            };
            let mut found = false;
            let mut stack = vec![e];
            while let Some(e) = stack.pop() {
                if let ExprKind::NarrowedPayload(inner, v, _) = &e.kind {
                    assert_eq!(*v, VariantIdx::PRESENT);
                    found = true;
                    stack.push(inner);
                }
            }
            assert!(found, "{e:?}");
        },
    );
}
