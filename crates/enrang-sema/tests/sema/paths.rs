//! Names and members in expressions (plan c.5, d.3, d.8; owner 3B): locals,
//! constants and statics, function names as `fn` values and overload sets by their
//! expected type, hidden arguments and `args`, `this` (EN0219), a type, namespace or
//! form in value position (EN0301), a name in no scope (EN0301, G06), paths through
//! types (cases, primitive constants, `static` methods) and namespaces (EN0311,
//! EN0301), and member lookup: auto-deref through `&` and `Box`, unnarrowed
//! nullables (EN0303 with the `?.` fix-it), `?.` (EN0413, `&F | null`),
//! visibility (EN0308), class bounds, anonymous objects, misses with "did you
//! mean" (EN0303), `length` read as a property (EN0441).

use enrang_base::Idx;
use enrang_hir::{
    self as hir, Adjust, ConstValue, ExprKind, FieldIdx, LocalKind, StmtKind, TopVar, TyKind,
    VariantIdx,
};
use enrang_sema::LibSource;
use enrang_testkit::{Harness, extract_cases};

use crate::support::{Run, run, run_with};

/// Checks `src` as the entry `main.en` with the fake library.
pub fn main_en(src: &str) -> Run {
    run(&[("main.en", src)])
}

/// Checks `src` as the entry `main.en` with the embedded library.
pub fn main_lib(src: &str) -> Run {
    run_with(&[("main.en", src)], LibSource::Embedded, "x86_64-linux")
}

/// Each diagnostic as `CODE line:col message [label]`.
pub fn diags(r: &Run) -> Vec<String> {
    r.diags
        .iter()
        .map(|d| {
            let loc = r.map.loc(d.primary.span.lo);
            format!(
                "{} {}:{} {} [{}]",
                d.code.name(),
                loc.line,
                loc.col,
                d.message,
                d.primary.text
            )
        })
        .collect()
}

/// The typed body of the definition whose path prints as `path`.
pub fn body<'r>(r: &'r Run, path: &str) -> &'r hir::Body {
    let def = r.def(path);
    r.program
        .as_ref()
        .unwrap_or_else(|| panic!("not checked: {}", r.rendered()))
        .bodies
        .get(&def)
        .unwrap_or_else(|| panic!("no body for {path}"))
}

/// The program's top-level statements.
pub fn statements(r: &Run) -> &hir::Body {
    r.program
        .as_ref()
        .unwrap_or_else(|| panic!("not checked: {}", r.rendered()))
        .statements
        .as_ref()
        .expect("statements")
}

/// The value of the body's first `return`.
pub fn returned(b: &hir::Body) -> &hir::Expr {
    b.root
        .stmts
        .iter()
        .find_map(|s| match &s.kind {
            StmtKind::Return(Some(e)) => Some(e),
            _ => None,
        })
        .expect("a return with a value")
}

/// The initialiser of the body's `n`th `let` or `const`.
pub fn init(b: &hir::Body, n: usize) -> &hir::Expr {
    b.root
        .stmts
        .iter()
        .filter_map(|s| match &s.kind {
            StmtKind::Let { init, .. } => Some(init.as_ref().expect("an initialiser")),
            _ => None,
        })
        .nth(n)
        .expect("a declaration")
}

/// The body's `n`th expression statement.
pub fn expr_stmt(b: &hir::Body, n: usize) -> &hir::Expr {
    b.root
        .stmts
        .iter()
        .filter_map(|s| match &s.kind {
            StmtKind::Expr(e) => Some(e),
            _ => None,
        })
        .nth(n)
        .expect("an expression statement")
}

/// `t` as messages print it.
pub fn ty(r: &Run, t: hir::Ty) -> String {
    r.tcx.ty_string(t)
}

const POINT: &str = "public class Point { public x: i64; public y: i64; }\n";

pub fn register(h: &mut Harness) {
    names(h);
    this_and_values(h);
    type_paths(h);
    namespaces(h);
    members(h);
    nullables(h);
    visibility(h);
    chains(h);
    pinned(h);
    goldens(h);
}

fn names(h: &mut Harness) {
    h.case("paths/a parameter reads as its local at its type", || {
        let r = main_en("public function f(a: i64): i64 { const b: i64 = a; return b; }\n");
        r.clean();
        let b = body(&r, "main::f");
        let e = init(b, 0);
        assert!(matches!(e.kind, ExprKind::Local(l) if b.locals[l].name.map(|n| n.as_str()) == Some("a")));
        assert_eq!(ty(&r, e.ty), "i64");
        assert!(e.adjust.is_empty());
        assert!(matches!(returned(b).kind, ExprKind::Local(_)));
    });
    h.case(
        "paths/a constant and an `unsafe let` read as `Static`",
        || {
            let r = main_en(
                "public const LIMIT: i64 = 3;\npublic function f(): i64 { return LIMIT; }\n",
            );
            r.clean();
            let e = returned(body(&r, "main::f"));
            assert_eq!(e.kind, ExprKind::Static(r.def("main::LIMIT")));
            assert_eq!(ty(&r, e.ty), "i64");
        },
    );
    h.case(
        "paths/a function named as a value is its address at its `fn` type",
        || {
            let r = main_en(
                "public function g(x: i64): i64 { return x; }
public function f(): void { const h: fn(x: i64) => i64 = g; }
",
            );
            r.clean();
            let e = init(body(&r, "main::f"), 0);
            let ExprKind::Const(ConstValue::FnAddr(f)) = e.kind else {
                panic!("{e:?}");
            };
            assert_eq!(f.def, r.def("main::g"));
            assert_eq!(ty(&r, e.ty), "fn(i64) => i64");
        },
    );
    h.case(
        "paths/an overload set named as a value picks the overload its `fn` type expects",
        || {
            let r = main_en(
                "public function d(n: i64): i64 { return n; }
public function d(s: &string): i64 { return 0; }
public function f(): void { const g: fn(s: &string) => i64 = d; }
",
            );
            r.clean();
            let e = init(body(&r, "main::f"), 0);
            let ExprKind::Const(ConstValue::FnAddr(f)) = e.kind else {
                panic!("{e:?}");
            };
            assert_eq!(r.tcx.def(f.def).path.to_string(), "main::d(&string)");
        },
    );
    h.case(
        "paths/EN0410: an overload set with no expected `fn` type",
        || {
            let r = main_en(
                "public function d(n: i64): i64 { return n; }
public function d(s: &string): i64 { return 0; }
public function f(): void { const g = d; }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0410 3:39 cannot infer which overload of `d` is meant [`d` has 2 overloads]"]
            );
            assert_eq!(
                r.diags[0].helps[0].message,
                "give it an expected type: `const g: fn(n: i64) => i64 = d;`"
            );
        },
    );
    h.case(
        "paths/EN0301: a name in no scope, with a local in scope to suggest",
        || {
            let r = main_en("public function f(count: i64): i64 { return cuont; }\n");
            assert_eq!(
                r.rendered(),
                "error[EN0301]: cannot find `cuont` in this scope
 --> main.en:1:45
  |
1 | public function f(count: i64): i64 { return cuont; }
  |                                             ^^^^^ not found
  |                   ----- a local with a similar name is declared here
  |
help: did you mean `count`?
  |
1 | public function f(count: i64): i64 { return count; }
  |                                             ~~~~~
  = explain: run `enrang explain EN0301`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case("paths/EN0301: a name typing reaches, with a block's local suggested", || {
        let r = main_en("public function f(): void { if (true) { const total: i64 = 1; console.log(totl); } }\n");
        assert_eq!(diags(&r), ["EN0301 1:75 cannot find `totl` in this scope [not found]"]);
        assert_eq!(r.diags[0].helps[0].message, "did you mean `total`?");
        assert_eq!(
            r.diags[0].secondary[0].text,
            "a local with a similar name is declared here"
        );
    });
    h.case(
        "paths/a local function reads a top-level variable as its hidden argument",
        || {
            let r = main_en(
                "let count: i64 = 0;
function report(): i64 { return count; }
console.log(report());
",
            );
            r.clean();
            let b = body(&r, "main::report");
            let e = returned(b);
            let ExprKind::Local(local) = e.kind else {
                panic!("{e:?}");
            };
            assert_eq!(b.locals[local].kind, LocalKind::Hidden(TopVar(1)));
            assert_eq!(b.locals[local].name.map(|n| n.as_str()), Some("count"));
            assert!(b.locals[local].mutable);
            assert_eq!(ty(&r, e.ty), "i64");
            assert!(!b.params.contains(&local));
        },
    );
    h.case(
        "paths/two reads of one hidden argument share one local",
        || {
            let r = main_en(
                "let count: i64 = 0;
function twice(): i64 { const a: i64 = count; return count; }
console.log(twice());
",
            );
            r.clean();
            let b = body(&r, "main::twice");
            assert_eq!(init(b, 0).kind, returned(b).kind);
            let hidden = b
                .locals
                .iter()
                .filter(|l| matches!(l.kind, LocalKind::Hidden(_)))
                .count();
            assert_eq!(hidden, 1);
        },
    );
    h.case(
        "paths/`args` in the statements is a top-level variable of type `string[]`",
        || {
            let r = main_en("console.log(args);\n");
            r.clean();
            let b = statements(&r);
            let StmtKind::Expr(call) = &b.root.stmts[0].kind else {
                panic!("{:?}", b.root.stmts[0]);
            };
            let ExprKind::Call { args, .. } = &call.kind else {
                panic!("{call:?}");
            };
            let ExprKind::Local(local) = args[0].kind else {
                panic!("{:?}", args[0]);
            };
            assert_eq!(b.locals[local].kind, LocalKind::TopVar(TopVar(0)));
            assert_eq!(ty(&r, args[0].ty), "string[]");
        },
    );
}

fn this_and_values(h: &mut Harness) {
    h.case("paths/`this` in a method is its receiver local", || {
        let r = main_en("public class C { public n: i64; public me(): &C { return this; } }\n");
        r.clean();
        let b = body(&r, "main::C::me");
        let e = returned(b);
        let ExprKind::Local(local) = e.kind else {
            panic!("{e:?}");
        };
        assert_eq!(b.locals[local].kind, LocalKind::This);
        assert_eq!(ty(&r, e.ty), "&C");
    });
    h.case(
        "paths/EN0219: `this` in a function, the statements, a constant and an arrow",
        || {
            let r = main_en(
                "const g = () => this;
console.log(this);
public const K: i64 = this;
public function f(): void { console.log(this); }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0219 1:17 `this` outside a method [there is no object here]",
                    "EN0219 2:13 `this` outside a method [there is no object here]",
                    "EN0219 3:23 `this` outside a method [there is no object here]",
                    "EN0219 4:41 `this` outside a method [there is no object here]",
                ]
            );
        },
    );
    h.case("paths/EN0219: `this` in a `static` method", || {
        let r = main_en(
            "public class C { public n: i64; public static make(): void { console.log(this); } }\n",
        );
        assert_eq!(
            diags(&r),
            ["EN0219 1:74 `this` outside a method [a `static` method has no `this`]"]
        );
    });
    h.case(
        "paths/an arrow in a method sees the method's `this`",
        || {
            let r = main_en(
                "public class C { public n: i64; public m(): void { const g = () => this.n; } }\n",
            );
            r.clean();
        },
    );
    h.case("paths/EN0219: `super.n` read as a value", || {
        let r = main_en(
            "public class A { public n: i64; }
public class B extends A { public m(): void { const s = super.n; } }
",
        );
        assert_eq!(
            diags(&r),
            ["EN0219 2:57 `super` outside a call [`super` is called, as `super(...)` or `super.m()`]"]
        );
    });
    h.case(
        "paths/EN0301: a type, a namespace and a form in value position",
        || {
            let r = run(&[
                (
                    "main.en",
                    "import * as u from \"./u\";
const a = Point;
const b = u;
const c = console;
const d = i64;
public class Point { public x: i64; }
",
                ),
                ("u.en", "public const K: i64 = 1;\n"),
            ]);
            assert_eq!(
                diags(&r),
                [
                    "EN0301 2:11 `Point` is a type, not a value [used as a value here]",
                    "EN0301 3:11 `u` is a namespace, not a value [used as a value here]",
                    "EN0301 4:11 `console` is a compiler form, not a value [used as a value here]",
                    "EN0301 5:11 `i64` is a type, not a value [used as a value here]",
                ]
            );
        },
    );
}

fn type_paths(h: &mut Harness) {
    h.case("paths/an enum case is a `VariantLit` of its enum", || {
        let r = main_en(
            "public enum Color { Red, Green }
public function f(): Color { const c: Color = Color.Green; return c; }
",
        );
        r.clean();
        let e = init(body(&r, "main::f"), 0);
        let ExprKind::VariantLit {
            variant, fields, ..
        } = &e.kind
        else {
            panic!("{e:?}");
        };
        assert_eq!(*variant, VariantIdx::new(1));
        assert!(fields.is_empty());
        assert_eq!(ty(&r, e.ty), "Color");
    });
    h.case(
        "paths/a generic enum's case takes its arguments from the expected type",
        || {
            let r = main_en(
                "public enum Opt<T> { None, Some { v: T } }
public function f(): void { const o: Opt<i64> = Opt.None; }
",
            );
            r.clean();
            let e = init(body(&r, "main::f"), 0);
            assert!(matches!(e.kind, ExprKind::VariantLit { .. }));
            assert_eq!(ty(&r, e.ty), "Opt<i64>");
        },
    );
    h.case(
        "paths/a case written with type arguments: `E<i64>.V`",
        || {
            let r = main_en(
                "public enum Opt<T> { None, Some { v: T } }
public function f(): void { const o: Opt<i64> = Opt<i64>.None; }
",
            );
            r.clean();
            let e = init(body(&r, "main::f"), 0);
            assert!(matches!(e.kind, ExprKind::VariantLit { .. }));
            assert_eq!(ty(&r, e.ty), "Opt<i64>");
        },
    );
    h.case(
        "paths/EN0433: a case with a field that has no default, named bare",
        || {
            let r = main_en(
                "public enum Shape { Empty, Circle { radius: f64 } }
public function f(): void { const s: Shape = Shape.Circle; }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0433 2:46 `Shape.Circle` leaves `radius` unset [`radius` has no default]"]
            );
            assert_eq!(
                r.diags[0].helps[0].message,
                "use `Shape.Circle { radius: ... }`"
            );
        },
    );
    h.case(
        "paths/EN0303: a case the enum lacks, with the case to suggest",
        || {
            let r = main_en(
                "public enum Color { Red, Green }
public function f(): void { const c: Color = Color.Gren; }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0303 2:52 `Color` has no member `Gren` [no such member]"]
            );
            assert_eq!(r.diags[0].helps[0].message, "did you mean `Green`?");
        },
    );
    h.case(
        "paths/the primitive constants are built in, `isize` at the target's width",
        || {
            let src = "public function f(): void {
  const a: i64 = i64.MAX;
  const b: i8 = i8.MIN;
  const c: u8 = u8.MAX;
  const d: isize = isize.MAX;
  const e: f64 = f64.PI;
  const g: f32 = f32.INFINITY;
}
";
            for (target, isize_max) in [
                ("x86_64-linux", i64::MAX as u128),
                ("i386-linux", i32::MAX as u128),
            ] {
                let r = run_with(
                    &[("main.en", src)],
                    crate::support::fake_lib(crate::support::MINI_LIB),
                    target,
                );
                r.clean();
                let b = body(&r, "main::f");
                let value = |n: usize| match init(b, n).kind {
                    ExprKind::Const(v) => v,
                    ref other => panic!("{other:?}"),
                };
                let common = *r.tcx.common();
                assert_eq!(value(0), ConstValue::Int(i64::MAX as u128, common.i64));
                assert_eq!(value(1), ConstValue::Int(0x80, common.i8));
                assert_eq!(value(2), ConstValue::Int(0xFF, common.u8));
                assert_eq!(
                    value(3),
                    ConstValue::Int(isize_max, common.isize),
                    "{target}"
                );
                assert_eq!(
                    value(4),
                    ConstValue::Float(std::f64::consts::PI.to_bits(), common.f64)
                );
                assert_eq!(
                    value(5),
                    ConstValue::Float(u64::from(f32::INFINITY.to_bits()), common.f32)
                );
            }
        },
    );
    h.case("paths/EN0303: a constant no primitive has", || {
        let r = main_en("public function f(): void { const a: i64 = i64.TOP; }\n");
        assert_eq!(
            diags(&r),
            ["EN0303 1:48 `i64` has no member `TOP` [no such member]"]
        );
    });
    h.case("paths/a `static` method named through its type is an `fn` value", || {
        let r = main_en(
            "public class Stack<T> { private items: T[]; public static empty(): Stack<T> { unreachable(); } }
public function f(): void { const e: fn() => Stack<i64> = Stack<i64>.empty; }
",
        );
        r.clean();
        let e = init(body(&r, "main::f"), 0);
        let ExprKind::Const(ConstValue::FnAddr(f)) = e.kind else {
            panic!("{e:?}");
        };
        assert_eq!(f.def, r.def("main::Stack::empty"));
        assert_eq!(ty(&r, e.ty), "fn() => Stack<i64>");
    });
}

fn namespaces(h: &mut Harness) {
    let lib = "public const LIMIT: i64 = 3;
public function helper(n: i64): i64 { return n; }
private function hidden(): i64 { return 1; }
";
    h.case("paths/a namespace's public constant and function read as values", move || {
        let r = run(&[
            (
                "main.en",
                "import * as u from \"./u\";
public function f(): void { const a: i64 = u.LIMIT; const h: fn(n: i64) => i64 = u.helper; }
",
            ),
            ("u.en", lib),
        ]);
        r.clean();
        let b = body(&r, "main::f");
        assert_eq!(init(b, 0).kind, ExprKind::Static(r.def("u::LIMIT")));
        assert!(matches!(init(b, 1).kind, ExprKind::Const(ConstValue::FnAddr(f)) if f.def == r.def("u::helper")));
    });
    h.case(
        "paths/EN0311 and EN0301: a namespace's private and missing members",
        move || {
            let r = run(&[
                (
                    "main.en",
                    "import * as u from \"./u\";
public function f(): void { const a = u.hidden; const b = u.LIMT; }
",
                ),
                ("u.en", lib),
            ]);
            assert_eq!(
                diags(&r),
                [
                    "EN0311 2:41 `hidden` is private to `u.en` [a private item]",
                    "EN0301 2:61 cannot find `LIMT` in `u` [not found]",
                ]
            );
            assert_eq!(r.diags[1].helps[0].message, "did you mean `LIMIT`?");
        },
    );
}

fn members(h: &mut Harness) {
    h.case(
        "paths/a field through `&` reads through a `Deref` of the reference",
        || {
            let r = main_en(&format!(
                "{POINT}public function f(p: &Point): i64 {{ return p.y; }}\n"
            ));
            r.clean();
            let e = returned(body(&r, "main::f"));
            let ExprKind::Field(base, field) = &e.kind else {
                panic!("{e:?}");
            };
            assert_eq!(*field, FieldIdx::new(1));
            assert_eq!(ty(&r, e.ty), "i64");
            let ExprKind::Deref(inner) = &base.kind else {
                panic!("{base:?}");
            };
            assert_eq!(ty(&r, base.ty), "Point");
            assert!(matches!(inner.kind, ExprKind::Local(_)));
            assert!(base.adjust.is_empty());
        },
    );
    h.case(
        "paths/a field through `Box` auto-derefs once per box (`BoxDeref`)",
        || {
            let r = main_en(&format!(
                "{POINT}public function f(b: Box<Box<Point>>): i64 {{ return b.x; }}\n"
            ));
            r.clean();
            let e = returned(body(&r, "main::f"));
            let ExprKind::Field(base, field) = &e.kind else {
                panic!("{e:?}");
            };
            assert_eq!(*field, FieldIdx::new(0));
            assert_eq!(base.adjust, [Adjust::BoxDeref, Adjust::BoxDeref]);
            assert!(matches!(base.kind, ExprKind::Local(_)));
        },
    );
    h.case("paths/a field of `this`", || {
        let r =
            main_en("public class C { private n: i64; public get(): i64 { return this.n; } }\n");
        r.clean();
        let e = returned(body(&r, "main::C::get"));
        assert!(
            matches!(&e.kind, ExprKind::Field(base, _) if matches!(base.kind, ExprKind::Deref(_)))
        );
    });
    h.case(
        "paths/an inherited field and a generic class's field at its arguments",
        || {
            let r = main_en(
                "public class Base<T> { public v: T; }
public class D extends Base<i64> { public w: bool; }
public function f(d: &D): i64 { return d.v; }
public function g(b: &Base<string>): string { return b.v; }
",
            );
            r.clean();
            assert_eq!(ty(&r, returned(body(&r, "main::f")).ty), "i64");
            assert_eq!(ty(&r, returned(body(&r, "main::g")).ty), "string");
        },
    );
    h.case(
        "paths/an anonymous object's field, and an object parameter's",
        || {
            let r = main_en(
                "public function f(p: &{ name: string, age: i64 }): i64 { return p.age; }
public function g(p: { name: string, age: i64 }): i64 { return p.age; }
",
            );
            r.clean();
            for f in ["main::f", "main::g"] {
                let e = returned(body(&r, f));
                assert!(
                    matches!(e.kind, ExprKind::Field(_, field) if field == FieldIdx::new(0)),
                    "{f}: {e:?}"
                );
                assert_eq!(ty(&r, e.ty), "i64");
            }
        },
    );
    h.case("paths/EN0303: a field an anonymous object lacks", || {
        let r = main_en("public function f(p: &{ name: string }): void { console.log(p.nmae); }\n");
        assert_eq!(
            diags(&r),
            ["EN0303 1:63 `{ name: string }` has no member `nmae` [no such member]"]
        );
        assert_eq!(r.diags[0].helps[0].message, "did you mean `name`?");
    });
    h.case(
        "paths/EN0303: a missing member, with \"did you mean\" over the members",
        || {
            let r = main_en(
                "public class User { public name: string; public greet(): void {} }
public function f(u: &User): void { console.log(u.nmae); }
",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0303]: `User` has no member `nmae`
 --> main.en:2:51
  |
2 | public function f(u: &User): void { console.log(u.nmae); }
  |                                                   ^^^^ no such member
  |
help: did you mean `name`?
  |
2 | public function f(u: &User): void { console.log(u.name); }
  |                                                   ~~~~
  = explain: run `enrang explain EN0303`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "paths/EN0303: a case's field read where no arm narrows to the case",
        || {
            let r = main_en(
                "public enum Shape { Empty, Circle { radius: f64 } }
public function f(s: &Shape): f64 { return s.radius; }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0303 2:46 `Shape` has no member `radius` [no such member]"]
            );
            assert_eq!(
                r.diags[0].entries[0].text,
                "`radius` is a field of the case `Circle`: read it in that case's `match` arm"
            );
        },
    );
    h.case("paths/EN0303: a `Slice` has no `push` (T:875)", || {
        let r = main_en("public function f(s: &Slice<u8>, v: u8): void { s.push(v); }\n");
        assert_eq!(
            diags(&r),
            ["EN0303 1:51 `Slice<u8>` has no member `push` [no such member]"]
        );
    });
    h.case(
        "paths/EN0303: a member of a subclass through a base reference",
        || {
            let r = main_en(
                "public class Animal { public name: string; }
public class Dog extends Animal { public fetch(): void {} }
public function f(a: &Animal): void { a.fetch(); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0303 3:41 `Animal` has no member `fetch` [no such member]"]
            );
        },
    );
    h.case(
        "paths/EN0441: `length` read as a property, with S:1383's helps",
        || {
            let r = main_lib(
                "public function f(s: &string, xs: &i64[]): void {
  console.log(s.length);
  console.log(xs.length);
}
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0441 2:17 `length` is a method on `string` [a method, called as `length()`]",
                    "EN0441 3:18 `length` is a method on `i64[]` [a method, called as `length()`]",
                ]
            );
            assert_eq!(
                r.diags[0].helps[0].message,
                "`s.length()` counts bytes; `s.charCount()` counts characters"
            );
            assert_eq!(r.diags[1].helps[0].message, "`xs.length()`");
        },
    );
    h.case(
        "paths/EN0441: on a string literal the help gives its counts (S:1383)",
        || {
            let r = main_lib(
                "public function f(): void {
  console.log(\"città\".length);
}
",
            );
            assert_eq!(
                diags(&r),
                ["EN0441 2:23 `length` is a method on `string` [a method, called as `length()`]"]
            );
            assert_eq!(
                r.diags[0].helps[0].message,
                "`\"città\".length()` counts bytes (6 here); `\"città\".charCount()` counts characters (5 here)"
            );
        },
    );
    h.case("paths/EN0303: any other method read as a value", || {
        let r = main_en(
            "public class User { public name: string; public greet(): void {} }
public function f(u: &User): void { const g = u.greet; }
",
        );
        assert_eq!(
            diags(&r),
            ["EN0303 2:49 `User` has no field `greet` [a method, not a field]"]
        );
        assert_eq!(
            r.diags[0].entries[0].text,
            "`greet` is a method: call it, `u.greet()`"
        );
    });
    h.case("paths/EN0606: a destructor named as a member", || {
        let r = main_en(
            "public class R { private n: i64; public destructor() {} }
public function f(r: &R): void { const d = r.destructor; }
",
        );
        assert_eq!(
            diags(&r),
            ["EN0606 2:46 a destructor runs by itself: call `dispose(r)` [a destructor is never called by name]"]
        );
    });
    h.case(
        "paths/`node.type` and other keywords as member names compile (T:641)",
        || {
            let r = main_en(
                "public class Token { public type: string; }
public function f(node: &Token): string { return node.type; }
",
            );
            r.clean();
        },
    );
}

fn nullables(h: &mut Harness) {
    h.case(
        "paths/EN0303: a member of an unnarrowed nullable, with the `?.` fix-it",
        || {
            let r = main_en(&format!(
                "{POINT}public function f(p: Point | null): void {{ console.log(p.x); }}\n"
            ));
            assert_eq!(
                r.rendered(),
                "error[EN0303]: `Point | null` has no member `x`
 --> main.en:2:58
  |
2 | public function f(p: Point | null): void { console.log(p.x); }
  |                                                          ^ this value may be `null`
  |
help: use `?.x`, which reads it only when the value is not `null`
  |
2 | public function f(p: Point | null): void { console.log(p?.x); }
  |                                                         +
help: or narrow it first: `if (p != null) { ... }`
  = explain: run `enrang explain EN0303`

error: aborting due to 1 previous error
"
            );
        },
    );
    h.case(
        "paths/EN0303: `a?.b.c`, with a `?.c` fix-it (T:635)",
        || {
            let r = main_en(
                "public class B { public c: i64; }
public class A { public b: B; }
public function f(a: A | null): void { console.log(a?.b.c); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0303 3:57 `&B | null` has no member `c` [this value may be `null`]"]
            );
            let help = &r.diags[0].helps[0];
            assert_eq!(
                help.message,
                "use `?.c`, which reads it only when the value is not `null`"
            );
            assert_eq!(help.edits[0].replacement, "?");
        },
    );
    h.case(
        "paths/`a?.b?.c` compiles; `?.` gives `&F | null` (S:750)",
        || {
            let r = main_en(
                "public class B { public c: i64; }
public class A { public b: B; }
public function f(a: A | null): void { const x: &i64 | null = a?.b?.c; const y: &B | null = a?.b; }
",
            );
            r.clean();
            let b = body(&r, "main::f");
            let e = init(b, 0);
            assert_eq!(ty(&r, e.ty), "&i64 | null");
            let ExprKind::OptionalChain(chain) = &e.kind else {
                panic!("{e:?}");
            };
            assert_eq!(ty(&r, chain.base.ty), "&B | null");
            assert_eq!(chain.member, hir::OptMember::Field(FieldIdx::new(0)));
            assert_eq!(ty(&r, init(b, 1).ty), "&B | null");
        },
    );
    h.case("paths/EN0413: `?.` on an owned nullable rvalue (S:750)", || {
        let r = main_en(&format!(
            "{POINT}public function make(): Point | null {{ return null; }}
public function f(): void {{ console.log(make()?.x); }}
"
        ));
        assert_eq!(
            diags(&r),
            ["EN0413 3:47 `?.` on an owned value: bind it first [this `Point | null` is a temporary]"]
        );
        assert_eq!(
            r.diags[0].helps[0].message,
            "bind it first: `const v = make();`, then `v?.x`"
        );
    });
    h.case(
        "paths/`?.` on a nullable place or on a nullable reference rvalue compiles",
        || {
            let r = main_en(&format!(
                "{POINT}public function find(): &Point | null {{ return null; }}
public function f(p: Point | null): void {{ console.log(p?.x); console.log(find()?.y); }}
"
            ));
            r.clean();
        },
    );
    h.case(
        "paths/a member of the nullable type itself is found on it",
        || {
            let r = main_en(
                "public function f(p: i64 | null, d: i64): i64 { return p.unwrapOr(d); }\n",
            );
            r.clean();
            assert_eq!(ty(&r, returned(body(&r, "main::f")).ty), "i64");
        },
    );
}

fn visibility(h: &mut Harness) {
    h.case("paths/EN0308: a private field outside its class", || {
        let r = main_en(
            "public class C { private n: i64; }
public function f(c: &C): void { console.log(c.n); }
",
        );
        assert_eq!(
            r.rendered(),
            "error[EN0308]: `n` is private to `C`
 --> main.en:2:48
  |
1 | public class C { private n: i64; }
  |                  --------------- `n` is declared here
2 | public function f(c: &C): void { console.log(c.n); }
  |                                                ^ only the body of `C` can use it
  |
  = explain: run `enrang explain EN0308`

error: aborting due to 1 previous error
"
        );
    });
    h.case(
        "paths/EN0308: a base's private field and method from a subclass",
        || {
            let r = main_en(
                "public class A { private s: i64; private t(): void {} }
public class B extends A { public m(): void { console.log(this.s); this.t(); } }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0308 2:64 `s` is private to `A` [only the body of `A` can use it]",
                    "EN0308 2:73 `t` is private to `A` [only the body of `A` can use it]",
                ]
            );
        },
    );
    h.case("paths/a protected member: visible in subclasses, EN0308 outside", || {
        let r = main_en(
            "public class Counter { protected step: i64; protected bump(): void {} }
public class Probe extends Counter { public m(): i64 { this.bump(); return this.step; } }
public function f(c: &Counter): void { console.log(c.step); c.bump(); }
",
        );
        assert_eq!(
            diags(&r),
            [
                "EN0308 3:54 `step` is protected in `Counter` [only `Counter` and its subclasses can use it]",
                "EN0308 3:63 `bump` is protected in `Counter` [only `Counter` and its subclasses can use it]",
            ]
        );
    });
    h.case(
        "paths/a private member inside its own class, its methods' arrows included",
        || {
            let r = main_en(
                "public class C { private n: i64; private t(): i64 { return 1; }
  public m(other: &C): i64 { const g = () => this.n; this.t(); return other.n; } }
",
            );
            r.clean();
        },
    );
    h.case("paths/Q37-private: a test part reaches no private member (T:957)", || {
        let r = run(&[
            (
                "math.en",
                "public class Counter {
  private count: i64;
  protected step: i64;
  private reset(): void {}
  public static make(): Counter { unreachable(); }
}
private function clamp(x: i64, lo: i64, hi: i64): i64 { return x; }
",
            ),
            (
                "math.test.en",
                "private class Probe extends Counter { public peek(): i64 { return this.step; } }
test(\"reaches\", () => {
  let c: Counter = Counter.make();
  expect(clamp(300, 0, 255)).toBe(255);
  expect(c.count).toBe(0);
  c.reset();
  expect(c.step).toBe(0);
});
",
            ),
        ]);
        assert_eq!(
            diags(&r),
            [
                "EN0308 5:12 `count` is private to `Counter` [only the body of `Counter` can use it]",
                "EN0308 6:5 `reset` is private to `Counter` [only the body of `Counter` can use it]",
                "EN0308 7:12 `step` is protected in `Counter` [only `Counter` and its subclasses can use it]",
            ]
        );
    });
    h.case("paths/D8-bound: a class-bounded `T` sees only the bound's public members", || {
        let r = main_en(
            "public class Labeler { protected secret: i64; public label(): i64 { return 1; } }
public function tag<T extends Labeler>(x: &T): i64 { console.log(x.label()); return x.secret; }
",
        );
        assert_eq!(
            diags(&r),
            ["EN0308 2:87 `secret` is protected in `Labeler` [only `Labeler` and its subclasses can use it]"]
        );
    });
}

// `?.` through a reference, on nullable fields, and on inferred receivers; private
// members seen from their own class; one diagnostic per misuse.
fn chains(h: &mut Harness) {
    h.case(
        "paths/`?.` on a `&(T | null)` reads the payload through a `Deref` (S:607)",
        || {
            let r = main_en(
                "public class Point { public x: i64; public sum(): i64 { return this.x; } }
public function f(r: &(Point | null)): void { const v = r?.x; const s = r?.sum(); }
",
            );
            r.clean();
            let b = body(&r, "main::f");
            let v = init(b, 0);
            assert_eq!(ty(&r, v.ty), "&i64 | null");
            let ExprKind::OptionalChain(chain) = &v.kind else {
                panic!("{v:?}");
            };
            assert!(
                matches!(chain.base.kind, ExprKind::Deref(_)),
                "{:?}",
                chain.base
            );
            assert_eq!(ty(&r, chain.base.ty), "Point | null");
            assert_eq!(ty(&r, init(b, 1).ty), "i64 | null");
        },
    );
    h.case(
        "paths/`a?.b?.c` looks through a nullable `b` (`n?.next?.value`)",
        || {
            let r = main_en(
                "public class Node { public value: i64; public next: Box<Node> | null; }
public class Inner { public c: i64; }
public class Mid { public bn: Inner | null; }
public function g(n: &Node | null, a: Mid | null): i64 | null { const y = a?.bn?.c; return n?.next?.value; }
",
            );
            r.clean();
            let b = body(&r, "main::g");
            assert_eq!(ty(&r, init(b, 0).ty), "&i64 | null");
            let e = returned(b);
            assert_eq!(ty(&r, e.ty), "&i64 | null");
            assert_eq!(e.adjust, vec![Adjust::ReadThroughNullable]);
        },
    );
    h.case(
        "paths/`?.` on a variable a later assignment made nullable",
        || {
            let r = main_en(&format!(
                "{POINT}public function find(): Point | null {{ return null; }}
public function f(): void {{ let p; p = find(); const v = p?.x; }}
"
            ));
            r.clean();
            let b = body(&r, "main::f");
            let v = b
                .root
                .stmts
                .iter()
                .find_map(|s| match &s.kind {
                    StmtKind::Let { init: Some(e), .. } => Some(e),
                    _ => None,
                })
                .expect("`const v`");
            assert_eq!(ty(&r, v.ty), "&i64 | null");
        },
    );
    h.case(
        "paths/an interface member through `Box` takes one `Self`, by `.` and by `?.`",
        || {
            let r = main_en(
                "public interface Dup { dup(): &Self; }
public class H { public b: Box<Dup>; public o: Box<Dup> | null; public f(): void { const d = this.b.dup(); const e = this.o?.dup(); } }
",
            );
            // `&Self`, not `Self`: a `Box<I>` of an interface with a by-value `Self`
            // member is EN1006, since no table can serve it (T:1000).
            r.clean();
            let b = body(&r, "main::H::f");
            assert_eq!(ty(&r, init(b, 0).ty), "&Dup");
            assert_eq!(ty(&r, init(b, 1).ty), "&Dup | null");
        },
    );
    h.case(
        "paths/a base's private member is seen through a subclass value in its own body",
        || {
            let r = main_en(
                "public class A { private s: i64; private m(): i64 { return 1; } public f(o: &B): i64 { return o.s + o.m(); } }
public class B extends A { }
public function g(o: &B): i64 { return o.s; }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0308 3:42 `s` is private to `A` [only the body of `A` can use it]"]
            );
        },
    );
    h.case(
        "paths/a private member named the wrong way gets one diagnostic",
        || {
            let r = main_en(
                "public class C { private m(): void { } private static s(): void { } }
public function f(c: &C): void { C.m(); c.s(); }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0303 2:36 `C` has no static member `m` [a member of each value, not of the type]",
                    "EN0303 2:43 `C` has no member `s` [a `static` method, not a member of each value]",
                ]
            );
        },
    );
    h.case("paths/EN0441's help keeps a written `?.`", || {
        let r = main_en("public function f(s: string | null): void { const a = s?.length; }\n");
        assert_eq!(
            diags(&r),
            ["EN0441 1:58 `length` is a method on `string` [a method, called as `length()`]"]
        );
        assert_eq!(
            r.diags[0].helps[0].message,
            "`s?.length()` counts bytes; `s?.charCount()` counts characters"
        );
    });
}

// Behaviour the mutation gate showed untested.
fn pinned(h: &mut Harness) {
    h.case("paths/an `unsafe let` reads as `Static` of its type", || {
        let r = main_en(
            "private unsafe let counter: i64 = 0;\npublic function f(): i64 { unsafe { return counter; } }\n",
        );
        r.clean();
        let b = body(&r, "main::f");
        let StmtKind::Unsafe(block) = &b.root.stmts[0].kind else {
            panic!("{:?}", b.root.stmts[0]);
        };
        let StmtKind::Return(Some(e)) = &block.stmts[0].kind else {
            panic!("{:?}", block.stmts[0]);
        };
        assert_eq!(e.kind, ExprKind::Static(r.def("main::counter")));
        assert_eq!(ty(&r, e.ty), "i64");
    });
    h.case(
        "paths/an overload set at a nullable `fn` type picks by the payload",
        || {
            let r = main_en(
                "public function d(n: i64): void { }
public function d(s: &string): void { }
public function f(): void { const h: (fn(x: i64) => void) | null = d; }
",
            );
            r.clean();
            let e = init(body(&r, "main::f"), 0);
            let ExprKind::Const(ConstValue::FnAddr(f)) = e.kind else {
                panic!("{e:?}");
            };
            assert_eq!(r.tcx.def(f.def).path.to_string(), "main::d(i64)");
        },
    );
    h.case("paths/a namespace's value covers the whole path", || {
        let r = run(&[
            (
                "main.en",
                "import * as u from \"./u\";\npublic function f(): i64 { return u.LIMIT; }\n",
            ),
            ("u.en", "public const LIMIT: i64 = 3;\n"),
        ]);
        r.clean();
        let e = returned(body(&r, "main::f"));
        assert_eq!(r.map.text(e.span), "u.LIMIT");
    });
    h.case(
        "paths/a namespace's \"did you mean\" knows its re-exports and child modules",
        || {
            let r = run(&[
                (
                    "main.en",
                    "import * as u from \"./u\";\npublic function f(): void { const h = u.helpr; }\n",
                ),
                ("u.en", "public import { helper } from \"./more\";\n"),
                ("more.en", "public function helper(): i64 { return 1; }\n"),
            ]);
            assert_eq!(diags(&r), ["EN0301 2:41 cannot find `helpr` in `u` [not found]"]);
            assert_eq!(r.diags[0].helps[0].message, "did you mean `helper`?");
            let r = run(&[
                (
                    "src/main.en",
                    "import * as d from \"./drivers\";\npublic function f(): void { const x = d.seral; }\n",
                ),
                ("src/drivers/serial.en", "public class Port { }\n"),
            ]);
            assert_eq!(diags(&r), ["EN0301 2:41 cannot find `seral` in `d` [not found]"]);
            assert_eq!(r.diags[0].helps[0].message, "did you mean `serial`?");
        },
    );
    h.case(
        "paths/a type's \"did you mean\" offers `static` methods only",
        || {
            let r = main_en(
                "public class C { public static make(): C { unreachable(); } public bake(): void { } }
public function f(): void { const m = C.mak; }
",
            );
            assert_eq!(diags(&r), ["EN0303 2:41 `C` has no member `mak` [no such member]"]);
            assert_eq!(r.diags[0].helps[0].message, "did you mean `make`?");
        },
    );
    h.case(
        "paths/an array's \"did you mean\" knows the members of `Slice<T>`",
        || {
            let r = main_lib("public function f(xs: &i64[]): void { const a = xs.frist(); }\n");
            assert_eq!(r.codes(), vec!["EN0303"], "{}", r.rendered());
            assert_eq!(r.diags[0].helps[0].message, "did you mean `first`?");
        },
    );
    h.case(
        "paths/`?.` on a nullable constant or element compiles",
        || {
            let r = main_en(&format!(
                "{POINT}public const P: Point | null = null;
public function f(xs: (Point | null)[]): void {{ const a = P?.x; const b = xs[0]?.y; }}
"
            ));
            r.clean();
        },
    );
    h.case(
        "paths/`?.` of a reference field is `&F | null`, not `&&F | null`",
        || {
            let r = main_en(
                "public class H {\n  private r: &i64;\n  public constructor(r: &i64) { this.r = r; }\n  public static f(h: &H | null): void { const v = h?.r; }\n}\n",
            );
            assert!(
                r.codes().iter().all(|c| !matches!(c.as_str(), "EN0303" | "EN0401")),
                "{}",
                r.rendered()
            );
            let b = body(&r, "main::H::f");
            assert_eq!(ty(&r, init(b, 0).ty), "&i64 | null");
        },
    );
    h.case(
        "paths/`?.` on a value that is never `null` is a plain field",
        || {
            let r = main_en(&format!(
                "{POINT}public function f(p: &Point): i64 {{ return p?.x; }}\n"
            ));
            r.clean();
            let e = returned(body(&r, "main::f"));
            assert!(matches!(e.kind, ExprKind::Field(..)), "{e:?}");
            assert_eq!(ty(&r, e.ty), "i64");
        },
    );
    h.case("paths/`Color?.Red` is no path: a type is no value", || {
        let r = main_en(
            "public enum Color { Red }\npublic function f(): void { const c = Color?.Red; }\n",
        );
        assert_eq!(
            diags(&r),
            ["EN0301 2:39 `Color` is a type, not a value [used as a value here]"]
        );
    });
    h.case(
        "paths/of overloads some visible, a call outside sees only those",
        || {
            let r = main_en(
                "public class C { private m(x: i64): void { } public m(s: &string): void { } }
public function f(c: &C, s: &string): void { c.m(s); }
",
            );
            r.clean();
            let ExprKind::Call {
                callee: hir::Callee::Fn(f),
                ..
            } = &expr_stmt(body(&r, "main::f"), 0).kind
            else {
                panic!("a call");
            };
            assert_eq!(r.tcx.def(f.def).path.to_string(), "main::C::m(&string)");
        },
    );
    h.case(
        "paths/an enum's private method is seen from its own methods",
        || {
            let r = main_en(
                "public enum E { A; private h(): i64 { return 1; } public g(): i64 { return this.h(); } }\n",
            );
            r.clean();
        },
    );
    h.case(
        "paths/EN0308 on a library member names no declaration",
        || {
            let r = main_en("public function f(s: &string): usize { return s.ptr; }\n");
            assert_eq!(
                diags(&r),
                ["EN0308 1:49 `ptr` is private to `string` [only the body of `string` can use it]"]
            );
            assert!(r.diags[0].secondary.is_empty());
        },
    );
    h.case(
        "paths/a `Box<T> | null` member gets the `?.` fix-it",
        || {
            let r = main_en(&format!(
                "{POINT}public function f(b: Box<Point> | null): void {{ console.log(b.x); }}\n"
            ));
            assert_eq!(
                diags(&r),
                ["EN0303 2:63 `Box<Point> | null` has no member `x` [this value may be `null`]"]
            );
            assert_eq!(
                r.diags[0].helps[0].message,
                "use `?.x`, which reads it only when the value is not `null`"
            );
        },
    );
    h.case(
        "paths/a private field three classes up names its own class",
        || {
            let r = main_en(
                "public class A { private s: i64; }
public class B extends A { }
public class C extends B { }
public function f(c: &C): i64 { return c.s; }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0308 4:42 `s` is private to `A` [only the body of `A` can use it]"]
            );
        },
    );
}

fn goldens(h: &mut Harness) {
    h.case("paths/G06 byte-exact in process", || {
        let doc =
            std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/../../docs/SPEC.md"))
                .expect("SPEC");
        let cases = extract_cases(&doc).expect("the cases extract");
        let case = cases.iter().find(|c| c.id == "G06").expect("G06");
        let files: Vec<(&str, &str)> = case
            .files
            .iter()
            .map(|f| (f.name.as_str(), f.contents.as_str()))
            .collect();
        let r = run_with(&files, LibSource::Embedded, "x86_64-linux");
        assert_eq!(r.rendered(), case.stderr.text);
        assert_eq!(case.exit, 1);
        assert!(r.program.is_none());
    });
    h.case("paths/G06's program with the name fixed compiles", || {
        let r = main_en("const total = 10;\nconsole.log(total);\n");
        r.clean();
        let _ = TyKind::Error;
    });
}
