//! Declaration lowering (plan c, d.4): types, signatures, ADTs, the implicit
//! parameters of D5, decorators, statics, `extend`, and the codes it reports:
//! EN0302, EN0307, EN0309, EN0401 (`extends`), EN0406, EN0408, EN0417, EN0437,
//! EN0439, EN0454, EN0456, EN0702, EN0705, EN0802, EN0806, EN0808, EN0814-EN0817,
//! EN0819, EN0826, EN0827, EN1014, EN1030.

use enrang_base::intern;
use enrang_hir::{
    AdtKind, ClassModifier, EnumValues, FieldIdx, Implicit, Mark, Receiver, TyKind, VariantValue,
    Vis,
};
use enrang_testkit::Harness;

use crate::support::{MINI_LIB, Run, fake_lib, run, run_with};

/// The program of one user file `src/main.en` with the fake library.
fn main_en(src: &str) -> Run {
    run(&[("src/main.en", src)])
}

/// `(code, message)` of every diagnostic.
fn reported(r: &Run) -> Vec<(String, String)> {
    r.codes().into_iter().zip(r.messages()).collect()
}

/// One expected diagnostic.
fn one(code: &str, message: &str) -> Vec<(String, String)> {
    vec![(code.to_owned(), message.to_owned())]
}

/// The fake library's three preludes, with `core/prelude` replaced by `core`.
fn lib_with_core(core: &'static str) -> enrang_sema::LibSource {
    fake_lib(&[
        ("core/prelude", core),
        ("alloc/prelude", "// a\n"),
        ("os/linux_x64/prelude", "// o\n"),
        ("os/vm/prelude", "// v\n"),
    ])
}

/// The type of the single parameter of `src/main::f`, as `ty_string` prints it.
fn param_type(decl: &str) -> String {
    let r = run(&[(
        "src/main.en",
        &format!("public function f(x: {decl}): void {{ }}\n"),
    )]);
    r.clean();
    let sig = r.tcx.sig(r.def("src/main::f"));
    r.tcx.ty_string(sig.params[0].ty)
}

pub fn register(h: &mut Harness) {
    let spellings: &[(&str, &str)] = &[
        ("i64", "i64"),
        ("int", "int"),
        ("i32", "int"),
        ("u8", "u8"),
        ("bool", "bool"),
        ("string", "string"),
        ("&string", "&string"),
        ("i64 | null", "i64 | null"),
        ("&i64 | null", "&i64 | null"),
        ("(i64 | null)[]", "(i64 | null)[]"),
        ("&i64[]", "&i64[]"),
        ("u8[4]", "u8[4]"),
        ("int[3][4]", "int[3][4]"),
        ("&Slice<u8>", "&Slice<u8>"),
        ("Box<i64>", "Box<i64>"),
        ("Array<i64>", "i64[]"),
        ("[int, string]", "[int, string]"),
        ("*u8", "*u8"),
        ("fn(let x: &i64) => void", "fn(let &i64) => void"),
        ("unsafe fn() => void", "unsafe fn() => void"),
        (
            "fn(xs: &Slice<i64>) => readonly &i64",
            "fn(&Slice<i64>) => readonly &i64",
        ),
        ("(k: u8) => void", "(u8) => void"),
        ("((k: u8) => void) | null", "((u8) => void) | null"),
        ("Result<i64>", "Result<i64>"),
        ("Result<i64, Failure>", "Result<i64>"),
        ("Result<void, Failure>", "Result<void>"),
        ("(i64)", "i64"),
    ];
    for (written, printed) in spellings {
        let (written, printed) = (*written, *printed);
        h.case(format!("lower/types: {written}"), move || {
            assert_eq!(param_type(written), printed);
        });
    }
    h.case("lower/lang classes become their kinds", || {
        let r = run(&[(
            "src/main.en",
            "public function f(a: string, b: &Slice<u8>, c: Array<u8>, d: Box<u8>): void { }\n",
        )]);
        r.clean();
        let sig = r.tcx.sig(r.def("src/main::f"));
        // A view stands only behind `&` (S:606, EN0401), so `b`'s referent is read.
        let kinds: Vec<TyKind> = sig
            .params
            .iter()
            .map(|p| match r.tcx.kind(p.ty) {
                TyKind::Ref(inner) => r.tcx.kind(inner),
                kind => kind,
            })
            .collect();
        let u8 = r.tcx.common().u8;
        assert_eq!(
            kinds,
            [
                TyKind::Str,
                TyKind::Slice(u8),
                TyKind::Array(u8),
                TyKind::Boxed(u8)
            ]
        );
    });
    h.case("lower/signatures: marks, defaults, `?`, results", || {
        let r = run(&[(
            "src/main.en",
            "public function f(let a: &i64[], const b: &string, c?: i32, d: i64 = 3, e?: i64 | null): readonly &i64 { return &a[0]; }
public unsafe function g(): void { }
",
        )]);
        r.clean();
        assert_eq!(
            r.sig("src/main::f"),
            "(let a: &i64[], const b: &string, c?: int | null, d?: i64, e?: i64 | null) => readonly &i64"
        );
        let f = r.tcx.sig(r.def("src/main::f"));
        assert_eq!(f.required_params(), 2);
        assert!(r.tcx.sig(r.def("src/main::g")).unsafety);
        assert_eq!(r.sig("src/main::g"), "() => void");
    });
    h.case(
        "lower/methods: receivers, generics linked to the class",
        || {
            let r = run(&[(
                "src/main.en",
                "public class Stack<T> {
  private items: T[];
  public let push(x: T): void { }
  public pop(): T | null { return null; }
  public move into(): T[] { return this.items; }
  public static empty(): Stack<T> { return new Stack<T> { items: [] }; }
  public map<U>(f: (x: &T) => U): Stack<U> { return Stack<U>.empty(); }
}
",
            )]);
            r.clean();
            assert_eq!(r.sig("src/main::Stack::push"), "(let this, x: T) => void");
            assert_eq!(r.sig("src/main::Stack::pop"), "(this) => T | null");
            assert_eq!(r.sig("src/main::Stack::into"), "(move this) => T[]");
            assert_eq!(r.sig("src/main::Stack::empty"), "(static) => Stack<T>");
            assert_eq!(
                r.sig("src/main::Stack::map"),
                "(this, f: (&T) => U) => Stack<U>"
            );
            let stack = r.tcx.adt_of(r.def("src/main::Stack")).expect("an ADT");
            let class_generics = r.tcx.adt(stack).generics;
            let map = r.tcx.sig(r.def("src/main::Stack::map"));
            assert_eq!(r.tcx.generics(map.generics).parent, Some(class_generics));
            assert_eq!(r.tcx.all_params(map.generics).len(), 2);
            let class = r.tcx.adt(stack).as_class().expect("a class");
            assert_eq!(class.fields.len(), 1);
            assert_eq!(r.tcx.ty_string(class.fields[0].ty), "T[]");
            assert_eq!(class.fields[0].vis, Vis::Private);
            assert_eq!(class.methods.len(), 5);
            assert!(
                class.hidden_table,
                "a class that is not final can be extended"
            );
        },
    );
    h.case(
        "lower/classes: flattened fields, overrides, constructors, tables",
        || {
            let r = run(&[(
                "src/main.en",
                "public class Animal {
  protected sound: string = \"...\";
  private secret: i64 = 0;
  public constructor(public readonly name: string, n?: i64) { }
}
public final class Dog extends Animal implements Copy {
  protected override sound: string = \"woof\";
  public secret: bool = false;
  public tag?: string;
}
",
            )]);
            // `sound` is a `string`, so `implements Copy` is EN0418 (stage 4D).
            assert_eq!(r.codes(), ["EN0418"], "{}", r.rendered());
            let dog = r.tcx.adt_of(r.def("src/main::Dog")).expect("Dog");
            let animal = r.tcx.adt_of(r.def("src/main::Animal")).expect("Animal");
            let class = r.tcx.adt(dog).as_class().expect("a class");
            let names: Vec<&str> = class.fields.iter().map(|f| f.name.as_str()).collect();
            assert_eq!(names, ["sound", "secret", "name", "secret", "tag"]);
            assert_eq!(class.own_from, 3);
            assert_eq!(class.overrides, [FieldIdx(0)]);
            assert_eq!(class.fields[2].declared_in, animal);
            assert!(class.fields[2].readonly);
            assert_eq!(class.fields[2].vis, Vis::Public);
            assert_eq!(r.tcx.ty_string(class.fields[4].ty), "string | null");
            assert!(class.fields[4].optional && class.fields[4].has_default);
            assert_eq!(class.modifier, ClassModifier::Final);
            assert!(class.copy);
            assert!(class.hidden_table, "its base has a table");
            assert_eq!(
                r.sig("src/main::Animal::#ctor"),
                "(name: string, n?: i64 | null) => void"
            );
            let found = r.tcx.member(
                r.tcx.mk_adt(dog, &[]),
                intern("secret"),
                r.tcx.def(r.def("src/main::Dog")).module,
            );
            assert_eq!(
                found.map(|m| m.kind),
                Some(enrang_hir::MemberKind::Field {
                    adt: dog,
                    field: FieldIdx(3)
                })
            );
        },
    );
    h.case(
        "lower/a generic base's fields are at the subclass's arguments",
        || {
            let r = run(&[(
                "src/main.en",
                "public class Holder<T> { public v: T; public w: T[] | null; }
public class Ints extends Holder<i64> { public own: bool; }
public class Twice<U> extends Holder<[U, U]> { }
",
            )]);
            r.clean();
            let ints = r.tcx.adt_of(r.def("src/main::Ints")).expect("Ints");
            let class = r.tcx.adt(ints).as_class().expect("a class");
            let tys: Vec<String> = class.fields.iter().map(|f| r.tcx.ty_string(f.ty)).collect();
            assert_eq!(tys, ["i64", "i64[] | null", "bool"]);
            let twice = r.tcx.adt_of(r.def("src/main::Twice")).expect("Twice");
            let class = r.tcx.adt(twice).as_class().expect("a class");
            assert_eq!(r.tcx.ty_string(class.fields[0].ty), "[U, U]");
            let args = r.tcx.intern_list(&[r.tcx.common().str]);
            assert_eq!(
                r.tcx
                    .ty_string(r.tcx.field_ty(twice, None, FieldIdx(0), args)),
                "[string, string]"
            );
        },
    );
    h.case("lower/a final class with no base has no table", || {
        let r = run(&[("src/main.en", "public final class P { public x: i64; }\n")]);
        let p = r.tcx.adt_of(r.def("src/main::P")).expect("P");
        assert!(!r.tcx.adt(p).as_class().expect("a class").hidden_table);
    });
    h.case("lower/readonly reference parts of a field", || {
        let r = run(&[(
            "src/main.en",
            "public class View {
  private src: readonly &Slice<u8>;
  private pair: [readonly &i64, &i64, readonly &i64];
  public constructor(src: &Slice<u8>, pair: [&i64, &i64, &i64]) { this.src = src; this.pair = pair; }
}
",
        )]);
        r.clean();
        let view = r.tcx.adt_of(r.def("src/main::View")).expect("View");
        let class = r.tcx.adt(view).as_class().expect("a class");
        assert_eq!(class.fields[0].readonly_refs, [Vec::<u32>::new()]);
        assert_eq!(class.fields[1].readonly_refs, [vec![0], vec![2]]);
        assert_eq!(r.tcx.ty_string(class.fields[1].ty), "[&i64, &i64, &i64]");
    });
    h.case("lower/enums: cases, fields, values, string unions", || {
        let r = run(&[(
            "src/main.en",
            "public enum Shape<T> { Circle { radius: T }, Square { side: T, label: string }, Empty }
public enum Code { Ok = 0, Bad = -2 }
public type Dir = \"up\" | \"down\";
public function f(s: Shape<f64>, d: Dir): void { }
",
        )]);
        r.clean();
        let shape = r.tcx.adt_of(r.def("src/main::Shape")).expect("Shape");
        let e = r.tcx.adt(shape).as_enum().expect("an enum");
        assert_eq!(e.variants.len(), 3);
        assert_eq!(r.tcx.ty_string(e.variants[1].fields[0].ty), "T");
        assert_eq!(r.tcx.ty_string(e.variants[1].fields[1].ty), "string");
        assert!(!e.is_payload_free());
        let code = r.tcx.adt_of(r.def("src/main::Code")).expect("Code");
        let e = r.tcx.adt(code).as_enum().expect("an enum");
        assert_eq!(e.values, EnumValues::Ints);
        assert_eq!(e.variants[1].value, Some(VariantValue::Int(-2)));
        let dir = r.tcx.adt_of(r.def("src/main::Dir")).expect("Dir");
        let e = r.tcx.adt(dir).as_enum().expect("an enum");
        assert!(e.str_union);
        assert_eq!(e.values, EnumValues::Texts);
        assert_eq!(r.sig("src/main::f"), "(s: Shape<f64>, d: Dir) => void");
    });
    h.case(
        "lower/interfaces: Self, fields-only aliases, implicit parameters (D5)",
        || {
            let r = run(&[(
                "src/main.en",
                "public interface Speaker { speak(): string; same(other: &Self): bool; }
public interface Named { name: string; nick?: string; }
public function a(s: Speaker): void { }
public function b(s: &Speaker): void { }
public function c(s: &Speaker | null): void { }
public function d(n: Named): void { }
public function e(n: &Named): void { }
public function f(o: { x: i64 }): void { }
public function g(o: &{ x: i64 }): void { }
public function h(o: &{ x: i64 } | null): void { }
",
            )]);
            r.clean();
            let speaker = r.tcx.adt_of(r.def("src/main::Speaker")).expect("Speaker");
            let AdtKind::Interface(iface) = &r.tcx.adt(speaker).kind else {
                panic!("an interface")
            };
            let same = r.tcx.sig(r.def("src/main::Speaker::same"));
            assert_eq!(
                same.params[0].ty,
                r.tcx.mk_ref(r.tcx.mk_param(iface.self_param))
            );
            assert_eq!(
                r.sig("src/main::Speaker::same"),
                "(this, other: &Self) => bool"
            );
            // `a` and `b` take a class of their own, bounded by `Speaker`.
            for name in ["a", "b"] {
                let sig = r.tcx.sig(r.def(&format!("src/main::{name}")));
                let params = r.tcx.generics(sig.generics).params.clone();
                assert_eq!(params.len(), 1, "{name}");
                assert_eq!(
                    r.tcx.param(params[0]).implicit,
                    Some(Implicit::Interface(speaker))
                );
            }
            assert_eq!(r.sig("src/main::a"), "(s: Speaker) => void");
            assert_eq!(r.sig("src/main::b"), "(s: &Speaker) => void");
            let c = r.tcx.sig(r.def("src/main::c"));
            assert!(
                r.tcx.generics(c.generics).params.is_empty(),
                "`&I | null` is no class of its own (A:599)"
            );
            // A fields-only interface is an object type; by value it is a shape parameter.
            let d = r.tcx.sig(r.def("src/main::d"));
            let p = r.tcx.generics(d.generics).params[0];
            assert!(matches!(r.tcx.param(p).implicit, Some(Implicit::Shape(_))));
            assert_eq!(
                r.sig("src/main::d"),
                "(n: { name: string, nick?: string | null }) => void"
            );
            assert_eq!(
                r.sig("src/main::e"),
                "(n: &{ name: string, nick?: string | null }) => void"
            );
            // By value or behind `&`, an object type is a shape of its own: one copy
            // per shape passed (SPEC 4.5 C20, S:601, A:599).
            let x_shape = match r
                .tcx
                .kind(r.tcx.mk_object(vec![(intern("x"), r.tcx.common().i64)]))
            {
                TyKind::Object(shape) => shape,
                other => panic!("an object type: {other:?}"),
            };
            for (name, behind_ref) in [("e", true), ("f", false), ("g", true)] {
                let sig = r.tcx.sig(r.def(&format!("src/main::{name}")));
                let params = r.tcx.generics(sig.generics).params.clone();
                assert_eq!(params.len(), 1, "{name}");
                assert!(
                    matches!(r.tcx.param(params[0]).implicit, Some(Implicit::Shape(_))),
                    "{name}"
                );
                let param = r.tcx.mk_param(params[0]);
                let expected = if behind_ref {
                    r.tcx.mk_ref(param)
                } else {
                    param
                };
                assert_eq!(sig.params[0].ty, expected, "{name}");
            }
            let g = r.tcx.sig(r.def("src/main::g"));
            let p = r.tcx.generics(g.generics).params[0];
            assert_eq!(r.tcx.param(p).implicit, Some(Implicit::Shape(x_shape)));
            assert_eq!(r.sig("src/main::g"), "(o: &{ x: i64 }) => void");
            let h = r.tcx.sig(r.def("src/main::h"));
            assert!(
                r.tcx.generics(h.generics).params.is_empty(),
                "`&{{ .. }} | null` is no shape of its own, as `&I | null` is not (A:599)"
            );
        },
    );
    h.case(
        "lower/an object type records which fields a literal may leave out (D13)",
        || {
            let r = run(&[(
                "src/main.en",
                "public type Opt<T> = { v?: T };
public function g(x: { v?: i64 | null }): void { }
public function k(x: { v: i64 | null }): void { }
public function o(x: Opt<i64 | null>): void { }
",
            )]);
            r.clean();
            let shape_of = |path: &str| {
                let sig = r.tcx.sig(r.def(path));
                let p = r.tcx.generics(sig.generics).params[0];
                match r.tcx.param(p).implicit {
                    Some(Implicit::Shape(shape)) => shape,
                    other => panic!("{path}: {other:?}"),
                }
            };
            let (g, k) = (shape_of("src/main::g"), shape_of("src/main::k"));
            assert_ne!(g, k, "only `v?` may be left out by a literal (S:600)");
            assert!(r.tcx.shape(g).is_optional(intern("v")));
            assert!(!r.tcx.shape(k).is_optional(intern("v")));
            assert_eq!(r.tcx.shape(g).fields, r.tcx.shape(k).fields);
            assert_eq!(r.sig("src/main::g"), "(x: { v?: i64 | null }) => void");
            assert_eq!(r.sig("src/main::k"), "(x: { v: i64 | null }) => void");
            assert_eq!(
                r.sig("src/main::o"),
                "(x: { v?: (i64 | null) | null }) => void",
                "`x?: T` collapses on the type as written (A:888)"
            );
        },
    );
    h.case(
        "lower/a written function type keeps its parameter names outside the type (D14)",
        || {
            let r = run(&[(
                "src/main.en",
                "public function run(f: fn(let s: &string) => void, g: ((k: u8) => void) | null, n: i64): fn(s: &string) => void { return f; }
public type Cb = fn(x: i64) => void;
public function viaAlias(c: Cb): void { }
",
            )]);
            r.clean();
            let run_sig = r.tcx.sig(r.def("src/main::run"));
            let names = |list: &Option<Vec<enrang_base::Symbol>>| {
                list.as_ref()
                    .map(|l| l.iter().map(|n| n.as_str()).collect::<Vec<_>>())
            };
            assert_eq!(names(&run_sig.params[0].fn_names), Some(vec!["s"]));
            assert_eq!(names(&run_sig.params[1].fn_names), Some(vec!["k"]));
            assert_eq!(names(&run_sig.params[2].fn_names), None);
            assert_eq!(names(&run_sig.ret_fn_names), Some(vec!["s"]));
            let f = &run_sig.params[0];
            assert_eq!(
                r.tcx.fn_ty_string(f.ty, f.fn_names.as_deref()),
                "fn(let s: &string) => void",
                "as SPEC 4.5's EN0615 prints it"
            );
            assert_eq!(r.tcx.ty_string(f.ty), "fn(let &string) => void");
            let g = &run_sig.params[1];
            assert_eq!(
                r.tcx.fn_ty_string(g.ty, g.fn_names.as_deref()),
                "((k: u8) => void) | null"
            );
            let alias = r.tcx.sig(r.def("src/main::viaAlias"));
            assert_eq!(alias.params[0].fn_names, None, "an alias keeps its own names");
        },
    );
    h.case(
        "lower/overloads over same-named classes of two modules get two paths",
        || {
            let r = run(&[
                (
                    "src/main.en",
                    "import { Node as N2 } from \"./b\";
public class Node { }
public function f(x: &Node): void { }
public function f(x: &N2): void { }
",
                ),
                ("src/b.en", "public class Node { }\n"),
            ]);
            r.clean();
            let mut paths: Vec<String> = r
                .tcx
                .defs()
                .filter(|(_, d)| {
                    d.path.module.as_str() == "src/main" && d.name() == Some(intern("f"))
                })
                .map(|(_, d)| d.path.to_string())
                .collect();
            paths.sort();
            assert_eq!(
                paths,
                ["src/main::f(&src/b::Node)", "src/main::f(&src/main::Node)"]
            );
        },
    );
    h.case(
        "lower/a fixed array's length is a constant expression",
        || {
            let r = run(&[(
                "src/main.en",
                "public const N: isize = 4;\npublic function f(x: u8[N], y: u8[(3)]): void { }\n",
            )]);
            r.clean();
            assert_eq!(r.sig("src/main::f"), "(x: u8[4], y: u8[3]) => void");
        },
    );
    h.case("lower/bounds and where clauses", || {
        let r = run(&[(
            "src/main.en",
            "public class Animal { }
public class Pen<T> {
  public show<U extends Clone & Animal>(u: U): void { }
  public copyAll(): void where T extends Copy { }
}
",
        )]);
        r.clean();
        let show = r.tcx.sig(r.def("src/main::Pen::show"));
        let u = *r.tcx.generics(show.generics).params.last().expect("U");
        let bounds: Vec<bool> = r
            .tcx
            .param(u)
            .bounds
            .iter()
            .map(|&b| matches!(r.tcx.bound(b), enrang_hir::Bound::Class { .. }))
            .collect();
        assert_eq!(bounds, [false, true]);
        let copy_all = r.tcx.sig(r.def("src/main::Pen::copyAll"));
        assert_eq!(copy_all.where_bounds.len(), 1);
        assert_eq!(r.tcx.param(copy_all.where_bounds[0].0).name.as_str(), "T");
    });
    h.case("lower/aliases expand at their arguments", || {
        let r = run(&[(
            "src/main.en",
            "public type Pair<T> = [T, T];
public type Later = Earlier;
public type Earlier = i64 | null;
public function f(p: Pair<string>, l: Later): void { }
",
        )]);
        r.clean();
        assert_eq!(
            r.sig("src/main::f"),
            "(p: [string, string], l: i64 | null) => void"
        );
    });
    h.case("lower/constants and statics take their written types", || {
        let r = run(&[("src/main.en", "public const MAX: u32 = 10;\nprivate unsafe let counter: usize = 0;\npublic const INFERRED = 3;\n")]);
        r.clean();
        assert_eq!(r.tcx.item_ty(r.def("src/main::MAX")), Some(r.tcx.common().u32));
        assert_eq!(r.tcx.item_ty(r.def("src/main::counter")), Some(r.tcx.common().usize));
        assert_eq!(r.tcx.item_ty(r.def("src/main::INFERRED")), Some(r.tcx.common().i32));
    });
    h.case("lower/declare functions are unsafe", || {
        let r = run(&[(
            "src/main.en",
            "@dll(\"kernel32\") public declare function Beep(f: u32, d: u32): bool;\n",
        )]);
        let beep = r.def("src/main::Beep");
        assert!(r.tcx.sig(beep).unsafety);
        assert_eq!(
            r.tcx.def(beep).attrs.dll.map(|s| s.as_str()),
            Some("kernel32")
        );
    });
    h.case("lower/decorators: lang, requires, mustUse, intrinsic, repr", || {
        let r = run_with(
            &[("src/main.en", "public function f(x: Atom): void { }\n")],
            fake_lib(&[
                ("core/prelude", "@lang(\"int\") public interface __Int {}\n@repr(\"u8\") public enum Atom { A, B }\n@mustUse @requires(\"sse2\") public function g(): void { unreachable(); }\n@intrinsic(\"MemCopy\") public declare function memCopy<T>(d: *T, s: *T, n: usize): void;\n"),
                ("alloc/prelude", "// a\n"),
                ("os/linux_x64/prelude", "// o\n"),
            ]),
            "x86_64-linux",
        );
        r.clean();
        let int = r.tcx.lang_adt(enrang_hir::LangItem::Int).expect("__Int");
        assert_eq!(r.tcx.adt(int).as_interface().and_then(|i| i.sealed), Some(enrang_hir::LangItem::Int));
        let atom = r.tcx.adt_of(r.def("core/prelude::Atom")).expect("Atom");
        assert_eq!(r.tcx.adt(atom).as_enum().and_then(|e| e.repr), Some(enrang_hir::Repr::U8));
        let g = r.def("core/prelude::g");
        assert!(r.tcx.def(g).attrs.must_use);
        assert!(!r.tcx.sig(g).requires.is_empty());
        let mem = r.def("core/prelude::memCopy");
        assert_eq!(r.tcx.def(mem).attrs.intrinsic, Some(enrang_hir::IntrinsicName::MemCopy));
    });
    h.case(
        "lower/extend blocks are recorded with their pattern",
        || {
            let r = run(&[("src/main.en", "")]);
            r.clean();
            let ext = r.tcx.extends().first().expect("the fake library's extend");
            assert_eq!(r.tcx.ty_string(ext.ty), "T | null");
            let sig = r.tcx.sig(ext.members[0]);
            assert_eq!(r.tcx.generics(sig.generics).parent, Some(ext.generics));
            assert_eq!(sig.receiver, Some(Receiver::Ref(Mark::None)));
        },
    );
    h.case("lower/library bodies are never typed", || {
        let r = run(&[("src/main.en", "public function f(): void { }\n")]);
        let program = r.program.as_ref().expect("checked");
        assert_eq!(program.bodies.len(), 1);
        assert!(program.bodies.contains_key(&r.def("src/main::f")));
    });
    h.case("lower/EN0302: a type name in no scope", || {
        let r = run(&[("src/main.en", "public function f(x: Strng): void { }\n")]);
        assert_eq!(
            r.rendered(),
            "error[EN0302]: cannot find type `Strng` in this scope
 --> src/main.en:1:22
  |
1 | public function f(x: Strng): void { }
  |                      ^^^^^ not found
  |
  = explain: run `enrang explain EN0302`

error: aborting due to 1 previous error
"
        );
        assert!(r.program.is_none());
    });
    h.case("lower/EN0309: the number of type arguments", || {
        let r = run(&[("src/main.en", "public class Pair<A, B> { }\npublic function f(x: Pair<i64>, y: Box<i64, i64>, z: i64<u8>): void { }\n")]);
        assert_eq!(r.codes(), ["EN0309", "EN0309", "EN0309"]);
        assert_eq!(
            r.messages(),
            [
                "`Pair` takes 2 type arguments, but 1 was given",
                "`Box` takes 1 type argument, but 2 were given",
                "`i64` takes 0 type arguments, but 1 was given",
            ]
        );
    });
    h.case("lower/EN0406: a union other than T | null", || {
        let r = run(&[(
            "src/main.en",
            "public function f(x: i64 | string): void { }\n",
        )]);
        assert_eq!(r.codes(), ["EN0406"]);
    });
    h.case("lower/EN0437: an alias that reaches itself, reported once", || {
        let r = run(&[("src/main.en", "public type A = B[];\npublic type B = A | null;\npublic function f(a: A): void { }\n")]);
        assert_eq!(r.codes(), ["EN0437"]);
        assert_eq!(r.messages(), ["type alias `A` refers to itself"]);
    });
    h.case("lower/EN0417: an interface with fields and methods", || {
        let r = run(&[(
            "src/main.en",
            "public interface Point { x: i64; norm(): f64; }\n",
        )]);
        assert_eq!(r.codes(), ["EN0417"]);
        assert_eq!(r.messages(), ["interface `Point` mixes fields and methods"]);
    });
    h.case("lower/the same input lowers the same way twice", || {
        let sources = [
            ("src/main.en", "import { Point } from \"./geo\";\npublic function f(p: Point, q: Box<Point>): Result<Point> { return Ok(p); }\n"),
            ("src/geo.en", "public class Point { public x: i64; }\n"),
        ];
        let one = run(&sources);
        let two = run(&sources);
        assert_eq!(one.sig("src/main::f"), two.sig("src/main::f"));
        assert_eq!(one.rendered(), two.rendered());
        assert_eq!(one.tcx.def_count(), two.tcx.def_count());
    });
    h.case(
        "lower/the embedded library: a program with no library names lowers",
        || {
            let r = run_with(
                &[(
                    "main.en",
                    "public function f(a: i64, b: &i64[]): bool { return true; }\n",
                )],
                enrang_sema::LibSource::Embedded,
                "i386-none",
            );
            r.clean();
            assert_eq!(r.sig("main::f"), "(a: i64, b: &i64[]) => bool");
        },
    );
    h.case("lower/EN0702: a reference to a reference", || {
        let r = main_en("public function f(x: &&i64): void { }\n");
        assert_eq!(
            reported(&r),
            one("EN0702", "a reference can't point to a reference")
        );
        assert_eq!(r.map.text(r.diags[0].primary.span), "&&i64");
        assert_eq!(r.diags[0].primary.text, "this points to `&i64`");
        let r = main_en("public function f(x: &(&i64 | null)): void { }\n");
        assert_eq!(r.diags[0].primary.text, "this points to `&i64 | null`");
        let r = main_en("public type R = &i64;\npublic function f(x: &R): void { }\n");
        assert_eq!(r.codes(), ["EN0702"]);
        main_en("public function f(x: &i64 | null, y: Box<Box<i64>>, z: **u8): void { }\n").clean();
    });
    h.case("lower/EN0705: a closure type outside a parameter, or nested", || {
        let cases: &[(&str, &str)] = &[
            ("public class C { public f: (x: i64) => void; }\n", "not a parameter's type"),
            ("public function f(): (x: i64) => void { unreachable(); }\n", "not a parameter's type"),
            ("public type Cb = (x: i64) => void;\n", "not a parameter's type"),
            ("public function f(x: ((k: u8) => void)[]): void { }\n", "not a parameter's type"),
            ("public function f(g: (h: (k: u8) => void) => void): void { }\n", "inside another closure type"),
            ("public function f(g: (h: ((k: u8) => void) | null) => void): void { }\n", "inside another closure type"),
            ("public function f(g: fn(h: (k: u8) => void) => void): void { }\n", "not a parameter's type"),
        ];
        for (src, label) in cases {
            let r = main_en(src);
            assert_eq!(reported(&r), one("EN0705", "a closure type can be written only as a parameter's type"), "{src}");
            assert_eq!(r.diags[0].primary.text, *label, "{src}");
        }
        // `| null` at the top of a closure parameter's type is no nesting (OQ24-nested).
        main_en("public function f(h2: ((k: u8) => void) | null, h3: ((x: &i64) => bool), handler?: (k: u8) => void): void { }\npublic class C { public m(f: (x: &i64) => void): void { } }\n").clean();
    });
    h.case(
        "lower/EN1014: type arguments on a type parameter, or a member of one",
        || {
            for src in [
                "public function f<T>(x: T<i64>): void { }\n",
                "public function f<T>(x: T.Item): void { }\n",
            ] {
                let r = main_en(src);
                assert_eq!(
                    reported(&r),
                    one("EN1014", "this generic feature is not supported yet"),
                    "{src}"
                );
                assert_eq!(r.diags[0].entries.len(), 1, "a note: {src}");
                assert!(r.diags[0].helps.is_empty(), "the row has no help: {src}");
            }
        },
    );
    h.case("lower/EN0454: `Result`'s error argument is no error type", || {
        let r = main_en("public function f(): Result<i64, string> { unreachable(); }\n");
        assert_eq!(
            r.rendered(),
            "error[EN0454]: `string` is not an error type
 --> src/main.en:1:34
  |
1 | public function f(): Result<i64, string> { unreachable(); }
  |                                  ^^^^^^ the error type of this `Result`
  |
help: return `Result<i64>` and write the text in `Err(\"...\")`
  = explain: run `enrang explain EN0454`

error: aborting due to 1 previous error
"
        );
        for (decl, shown) in [
            ("Result<i64, i64>", "i64"),
            ("Result<i64, Plain>", "Plain"),
            ("Result<i64, Box<AgeError>>", "Box<AgeError>"),
            ("Result<i64, i64[]>", "i64[]"),
        ] {
            let r = main_en(&format!(
                "public enum AgeError {{ Neg }}\npublic class Plain {{ }}\npublic function f(x: {decl}): void {{ }}\n"
            ));
            assert_eq!(reported(&r), one("EN0454", &format!("`{shown}` is not an error type")), "{decl}");
            assert_eq!(
                r.diags[0].helps[0].message,
                "an error type is an enum, `Failure`, or a class that `implements Error`"
            );
        }
        // A reference or a borrowing class is EN0701's, not also EN0454 (EF-08).
        let r = main_en(
            "public enum AgeError { Neg }
public class Lexer { private src: &string; public constructor(s: &string) { this.src = s; } }
public function f(e: Result<i64, &AgeError>, g: Result<i64, Lexer>): void { }
",
        );
        assert_eq!(r.codes(), ["EN0701", "EN0701"], "{}", r.rendered());
        // An enum, `Failure`, a class implementing `Error`, a type parameter.
        main_en(
            "public enum AgeError { Neg }
public class Disk implements Error { public code: i64; }
public function f<E>(a: Result<i64, AgeError>, b: Result<i64, Failure>, c: Result<i64, Disk>, d: Result<i64, E>): void { }
public class Holder { public r: Result<i64, AgeError>; }
public type Later = Result<i64, Late>;
public enum Late { X }
",
        )
        .clean();
    });
    h.case("lower/EN0408: a class or enum that holds itself without `Box`", || {
        let r = main_en("public class Node { public next: Node | null; }\n");
        assert_eq!(reported(&r), one("EN0408", "recursive type `Node` needs `Box`"));
        let diag = &r.diags[0];
        assert_eq!(r.map.text(diag.primary.span), "Node | null");
        assert_eq!(diag.primary.text, "this holds a `Node` inline");
        assert_eq!(diag.helps[0].message, "write `Box<Node> | null`");
        assert_eq!(diag.helps[0].edits[0].replacement, "Box<Node> | null");
        assert_eq!(diag.helps[0].edits[0].span, diag.primary.span);
        let r = main_en("public enum List { Cons { head: i64, tail: List }, Nil }\n");
        assert_eq!(reported(&r), one("EN0408", "recursive type `List` needs `Box`"));
        // One cycle through two classes is reported once, at the first.
        let r = main_en("public class A { public b: B; }\npublic class B { public a: A | null; }\n");
        assert_eq!(reported(&r), one("EN0408", "recursive type `A` needs `Box`"));
        let r = main_en("public class Wrap<T> { public v: T; }\npublic class N { public w: Wrap<N> | null; }\n");
        assert_eq!(reported(&r), one("EN0408", "recursive type `N` needs `Box`"));
        let r = main_en("public class T2 { public pair: [T2, i64] | null; }\n");
        assert_eq!(r.codes(), ["EN0408"]);
        // A reference field breaks the recursion too, though it makes its class
        // borrowing, which no `Box` or array may hold (EN0701, A:892).
        main_en("public class Node { public next: Box<Node> | null; public kids: Node[]; }\npublic class Up { private up: &Up | null = null; }\npublic enum Tree { Leaf, Branch { kids: Tree[] } }\n").clean();
    });
    h.case(
        "lower/EN0456: an enum's values mix numbers and texts",
        || {
            let r = main_en("public enum E { A = 1, B = \"b\", C = 2 }\n");
            assert_eq!(
                reported(&r),
                one("EN0456", "`E` mixes number and text values")
            );
            assert_eq!(r.map.text(r.diags[0].primary.span), "\"b\"");
            assert_eq!(r.diags[0].primary.text, "a text after number values");
            assert_eq!(r.diags[0].secondary[0].text, "the first value is a number");
            let r = main_en("public enum E { A = \"a\", B = -1 }\n");
            assert_eq!(r.diags[0].primary.text, "a number after text values");
            main_en("public enum E { A = 1, B = 2 }\npublic enum F { A = \"a\", B = \"b\" }\n")
                .clean();
        },
    );
    h.case(
        "lower/EN0439: `extend` on an object type or a tuple, in a library",
        || {
            let r = run_with(
                &[("main.en", "")],
                lib_with_core(
                    "public type P = { x: i64 };
extend ({ x: i64 }) { public f(): void; }
extend [i64, i64] { public g(): void; }
extend P { public h(): void; }
",
                ),
                "x86_64-linux",
            );
            assert_eq!(r.codes(), ["EN0439", "EN0439", "EN0439"]);
            assert_eq!(
                r.messages()[0],
                "an anonymous object type or a tuple can't have methods"
            );
            assert!(r.tcx.extends().is_empty());
        },
    );
    h.case("lower/EN0806: `extend` and bodyless methods are library-only forms", || {
        let r = main_en("extend<T> T | null {\n  public m(): void { }\n}\n");
        assert_eq!(reported(&r), one("EN0806", "`extend` is a library-only form"));
        assert_eq!(r.map.text(r.diags[0].primary.span), "extend<T> T | null");
        assert_eq!(r.diags[0].helps[0].message, "make it a class");
        let r = main_en("public abstract class C { public m(): void; public abstract n(): void; }\npublic enum E { A; public k(): i64; }\n");
        assert_eq!(r.codes(), ["EN0806", "EN0806"]);
        assert_eq!(r.messages()[0], "a method without a body is a library-only form");
        assert_eq!(r.diags[0].primary.text, "write its body, or make it `abstract`");
        assert_eq!(r.diags[1].primary.text, "write its body");
    });
    h.case("lower/EN0806: unknown, misplaced, repeated and malformed decorators", || {
        let cases: &[(&str, &str)] = &[
            ("@inline public function f(): void { }\n", "unknown decorator `@inline`"),
            ("public class C { @entry public m(): void { } }\n", "`@entry` can't be used on a method"),
            ("@dll(\"k\") public function f(): void { }\n", "`@dll` can't be used on a function"),
            ("@globalAllocator public const N: i64 = 1;\n", "`@globalAllocator` can't be used on a constant"),
            ("@mustUse public class C { }\n", "`@mustUse` can't be used on a class"),
            ("public enum E { @at(1) A }\n", "`@at` can't be used on an enum case"),
            ("@naked public function f(): void { }\n", "`@naked` can be used only on an `unsafe function`"),
            ("@mustUse @mustUse public function f(): i64 { return 1; }\n", "`@mustUse` is written twice"),
            ("@entry(1) public function f(): void { }\n", "`@entry` takes no arguments"),
            ("@align(3) public final class C { }\n", "`@align` takes a power of two up to 4096"),
            ("@align(8192) public final class C { }\n", "`@align` takes a power of two up to 4096"),
            ("@requires(\"warp\") public function f(): void { }\n", "unknown CPU feature `warp`"),
            ("@bits(8) public unsafe function f(): void { }\n", "`@bits` takes 16, 32 or 64"),
            ("@repr(\"u8\") public final class C { }\n", "`@repr(\"u8\")` can't be used on a class"),
            ("@repr(\"i8\") public enum E { A }\n", "`@repr` takes `\"C\"`, `\"u8\"`, `\"u16\"` or `\"u32\"`"),
            ("@interrupt(1) public function f(): void { }\n", "`@interrupt` takes `{ errorCode: true }` or nothing"),
            ("@lang(\"string\") public final class S { }\n", "`@lang` is a library-only form"),
            ("@owner public function f(): void { }\n", "`@owner` is a library-only form"),
            ("@intrinsic(\"MemCopy\") public declare function f(): void;\n", "`@intrinsic` is a library-only form"),
            ("@hostCall(\"x\") public declare function f(): void;\n", "`@hostCall` is a library-only form"),
            ("@devMigrate public function f(x: i64): void { }\n", "`@devMigrate` needs a function with an object-typed parameter"),
        ];
        for (src, message) in cases {
            let r = main_en(src);
            let ours: Vec<String> = r
                .diags
                .iter()
                .filter(|d| d.code.name() == "EN0806")
                .map(|d| d.message.clone())
                .collect();
            assert_eq!(ours, [*message], "{src}\n{}", r.rendered());
        }
        let r = main_en("@mustuse public function f(): i64 { return 1; }\n");
        assert_eq!(r.diags[0].helps[0].message, "did you mean `@mustUse`?");
        assert_eq!(r.diags[0].primary.text, "not a decorator");
        // A user `@lang` registers nothing.
        let r = main_en("@lang(\"string\") public final class S { }\n");
        assert_eq!(r.tcx.def(r.tcx.lang(enrang_hir::LangItem::Str)).path.to_string(), "core/prelude::string");
        // What the table allows compiles.
        main_en(
            "@mustUse @requires(\"cmov\", \"sse2\") @was(\"old\") public function f(): i64 { return 1; }
@section(\".text.hot\") public function g(): void { }
@naked @bits(32) public unsafe function h(): void { }
@abi(\"win64\") public function i(): void { }
@devMigrate public function j(old: { name: string }): void { }
@packed public final class P { public a: u8; }
@repr(\"C\") @align(16) public final class R { @was(\"x\") public b: u32; }
@repr(\"u8\") public enum E { @was(\"Z\") A, B }
@align(8) @at(4096) private unsafe let s: u8[8];
",
        )
        .clean();
    });
    h.case("lower/EN0806: the library's own forms, and their places", || {
        let r = run_with(
            &[("main.en", "")],
            lib_with_core(
                "@intrinsic(\"Bogus\") public declare function f(): void;
@hostCall(\"fs.open\") public declare function g(): void;
@owner public function o(): void { unreachable(); }
@intrinsic(\"MemCopy\") public declare function copy<T>(d: *T, s: *T, n: usize): void;
public final class S { @intrinsic(\"SliceFromRaw\") public static unsafe fromRaw(p: *u8, n: isize): &S; public m(): void; }
",
            ),
            "x86_64-linux",
        );
        assert_eq!(
            r.messages(),
            [
                "unknown intrinsic `Bogus`",
                "`@hostCall` can be used only in `os/vm`",
                "`@owner` can be used only in `alloc`"
            ]
        );
        let r = run_with(
            &[("main.en", "")],
            fake_lib(&[
                ("core/prelude", "// c\n"),
                ("alloc/prelude", "@owner public function o(): void { unreachable(); }\n"),
                ("os/vm/prelude", "@hostCall(\"fs.open\") public declare function open(p: &u8): i32;\n"),
            ]),
            "vm64",
        );
        r.clean();
    });
    h.case("lower/EN0806: a caller-making decorator on a function with hidden arguments (MR-5)", || {
        let r = main_en(
            "let log: string[] = [];
@devMigrate function migratePlayer(old: { name: string, hp: i32 }): i32 { log.push(old.name); return old.hp; }
@abi(\"sysv\") function callback(): void { log.push(\"x\"); }
@mustUse function kept(): i64 { log.push(\"y\"); return 1; }
@devMigrate function fresh(old: { name: string }): i64 { return 1; }
console.log(kept());
",
        );
        assert_eq!(r.codes(), ["EN0806", "EN0806"]);
        assert_eq!(
            r.messages(),
            [
                "`@devMigrate` can't be used on a function that uses top-level variables",
                "`@abi` can't be used on a function that uses top-level variables"
            ]
        );
        assert_eq!(r.diags[0].secondary[0].text, "`migratePlayer` uses `log`, a top-level variable");
    });
    h.case("lower/EN0808: an interrupt handler's signature", || {
        let ok = "@interrupt private function onTimer(frame: &InterruptFrame): void { }
@interrupt({ errorCode: true }) private function onFault(frame: &InterruptFrame, code: usize): never { unreachable(); }
";
        run_with(&[("main.en", ok)], enrang_sema::LibSource::Embedded, "i386-none").clean();
        for (src, shape) in [
            ("@interrupt private function bad(frame: &InterruptFrame, code: usize): void { }\n", "`(frame: &InterruptFrame)`"),
            ("@interrupt private function bad(frame: &InterruptFrame): i32 { return 0; }\n", "`(frame: &InterruptFrame)`"),
            ("@interrupt private function bad(frame: InterruptFrame): void { }\n", "`(frame: &InterruptFrame)`"),
            ("@interrupt({ errorCode: true }) private function bad(frame: &InterruptFrame): void { }\n", "`(frame: &InterruptFrame, code: usize)`"),
        ] {
            let r = run_with(&[("main.en", src)], enrang_sema::LibSource::Embedded, "i386-none");
            assert_eq!(reported(&r), one("EN0808", "invalid interrupt signature"), "{src}");
            assert_eq!(
                r.diags[0].primary.text,
                format!("an interrupt handler takes {shape} and returns `void` or `never`")
            );
            assert!(r.map.text(r.diags[0].primary.span).starts_with("bad("));
        }
    });
    h.case("lower/EN0814: a section the target refuses, or the reserved one", || {
        let r = main_en("@section(\".boot\") public function f(): void { }\n");
        assert_eq!(reported(&r), one("EN0814", "section `.boot` is not allowed on `x86_64-linux`"));
        assert_eq!(r.map.text(r.diags[0].primary.span), "\".boot\"");
        let r = run_with(
            &[("main.en", "@section(\".bss.stack\") private unsafe let s: u8[16];\n")],
            enrang_sema::LibSource::Embedded,
            "i386-none",
        );
        assert_eq!(reported(&r), one("EN0814", "section `.bss.stack` is reserved"));
        run_with(
            &[("main.en", "@section(\".boot\") private function f(): void { }\n@section(\".bss.kstack\") private unsafe let k: u8[16];\n")],
            enrang_sema::LibSource::Embedded,
            "i386-none",
        )
        .clean();
        main_en("@section(\".data.tables\") private unsafe let t: u8[4];\n").clean();
    });
    h.case("lower/EN0815: a `declare function` without `@dll`", || {
        let r = main_en("public declare function exit(code: i32): never;\n");
        assert_eq!(
            reported(&r),
            one("EN0815", "`declare function` without `@dll`")
        );
        assert_eq!(
            r.diags[0].entries.len(),
            1,
            "the note about inline assembly"
        );
        assert!(r.diags[0].entries[0].text.contains("inline assembly"));
        main_en("@dll(\"kernel32.dll\") public declare function ExitProcess(code: u32): never;\n")
            .clean();
    });
    h.case("lower/EN0816 and EN1030: what may cross into foreign code", || {
        for (src, message) in [
            ("@dll(\"k\") public declare function w(s: &string): void;\n", "`&string` can't cross into foreign code"),
            ("@dll(\"k\") public declare function w(s: u8[]): void;\n", "`u8[]` can't cross into foreign code"),
            ("@dll(\"k\") public declare function w(): string;\n", "`string` can't cross into foreign code"),
            ("public type Cb = @abi(\"win64\") unsafe fn(p: &u8) => void;\n", "`&u8` can't cross into foreign code"),
        ] {
            let r = main_en(src);
            assert_eq!(reported(&r), one("EN0816", message), "{src}");
        }
        let r = main_en("public final class P { public x: i64; }\n@dll(\"k\") public declare function g(p: P): void;\n");
        assert_eq!(reported(&r), one("EN1030", "this foreign ABI is not supported yet"));
        let r = main_en("@abi(\"cdecl\") public function f(): void { }\n");
        assert_eq!(reported(&r), one("EN1030", "this foreign ABI is not supported yet"));
        assert_eq!(r.map.text(r.diags[0].primary.span), "\"cdecl\"");
        assert_eq!(r.diags[0].helps[0].message, "Use scalars and pointers");
        main_en("@dll(\"k\") public declare function ok(p: *u8, n: u32, f: fn(x: i32) => void): u32;\npublic type EfiPrint = @abi(\"win64\") unsafe fn(self: *u8, s: *u16) => usize;\n").clean();
    });
    h.case("lower/EN0819: an unknown ABI", || {
        let r = main_en("@abi(\"fastcall\") public function f(): void { }\n");
        assert_eq!(reported(&r), one("EN0819", "unknown ABI `fastcall`"));
        assert_eq!(r.diags[0].primary.text, "`win64` or `sysv`");
    });
    h.case("lower/EN0817: conflicting layout attributes", || {
        let r = main_en("@packed @align(4) public final class P { public a: u8; }\n");
        assert_eq!(reported(&r), one("EN0817", "conflicting layout attributes"));
        assert_eq!(
            r.diags[0].primary.text,
            "`@align(4)` conflicts with `@packed`"
        );
        assert_eq!(r.diags[0].secondary[0].text, "`@packed` is here");
        let r = main_en("@repr(\"C\") @packed public final class P { public a: u8; }\n");
        assert_eq!(r.codes(), ["EN0817"]);
        let r = main_en("@align(4) @align(8) private unsafe let s: u8[4];\n");
        assert_eq!(r.codes(), ["EN0817"]);
    });
    h.case(
        "lower/EN0826: a `@packed` field that is not Copy or is generic",
        || {
            let r = main_en("@packed public final class P { public s: string; }\n");
            assert_eq!(
                reported(&r),
                one("EN0826", "`@packed` field must be Copy and non-generic")
            );
            assert_eq!(r.diags[0].primary.text, "`string` is not Copy");
            let r = main_en("@packed public final class G<T> { public v: T; }\n");
            assert_eq!(r.diags[0].primary.text, "`T` is generic");
        },
    );
    h.case("lower/EN0827: a layout decorator on a class that can carry a hidden pointer", || {
        let r = main_en("@packed public class P { public a: u8; }\n");
        assert_eq!(reported(&r), one("EN0827", "a `@packed` class must be `final`"));
        assert_eq!(
            r.diags[0].primary.text,
            "promises an exact layout, but a class that can be extended carries a hidden pointer"
        );
        assert_eq!(r.diags[0].helps[0].message, "write `@packed public final class P`");
        let r = main_en("public class Base { }\n@packed public final class P extends Base { public a: u8; }\n");
        assert_eq!(reported(&r), one("EN0827", "a `@packed` class can't extend another class"));
        assert_eq!(r.diags[0].primary.text, "`Base` gives it a hidden method-table pointer");
        assert_eq!(r.diags[0].helps[0].message, "remove `extends Base`");
        let r = main_en("public class Animal implements Copy { public n: i64; }\n@repr(\"C\") public final class Regs { public inner: Animal; }\n");
        assert_eq!(reported(&r), one("EN0827", "a `@repr(\"C\")` class can't hold `Animal` inline"));
        main_en("public final class Leaf { public n: i64; }\n@repr(\"C\") public final class Regs { public inner: Leaf; public p: *u8; }\n").clean();
    });
    h.case("lower/EN0802: what an `unsafe let` can't hold", || {
        for (src, message, label) in [
            ("private unsafe let s: string;\n", "an `unsafe let` can't hold a `string`", "`string` owns heap memory"),
            ("private unsafe let v: void;\n", "an `unsafe let` can't hold `void`", "`void` holds nothing"),
            ("private unsafe let r: &i64;\n", "an `unsafe let` can't hold a `&i64`", "`&i64` is a reference"),
            ("public final class D { public x: i64; public destructor() { } }\nprivate unsafe let d: D = new D { x: 1 };\n", "an `unsafe let` can't hold a `D`", "`D` has a destructor"),
            ("public final class L { public xs: i64[]; }\nprivate unsafe let l: L;\n", "an `unsafe let` can't hold a `L`", "`i64[]` owns heap memory"),
            ("public enum E { A, B }\nprivate unsafe let e: E;\n", "an `unsafe let` can't hold an `E`", "`E` has no all-zero value"),
        ] {
            let r = main_en(src);
            assert_eq!(reported(&r), one("EN0802", message), "{src}");
            assert_eq!(r.diags[0].primary.text, label, "{src}");
        }
    });
    h.case("lower/EN0802: a class that can be extended needs a value (F9)", || {
        let r = main_en("public class Stats { public n: i64; }\nprivate unsafe let stats: Stats;\n");
        assert_eq!(reported(&r), one("EN0802", "an `unsafe let` can't hold a `Stats`"));
        let helps: Vec<&str> = r.diags[0].helps.iter().map(|h| h.message.as_str()).collect();
        assert_eq!(
            helps,
            ["write `public final class Stats`", "or give it a value: `= new Stats {}`"]
        );
        let r = main_en("public class Stats { public n: i64; }\n@at(0xB8000) private unsafe let stats: Stats = new Stats { n: 0 };\n");
        assert_eq!(r.codes(), ["EN0802"], "`@at` storage is never filled");
        main_en("public final class Stats { public n: i64; private p: *u8; }\nprivate unsafe let stats: Stats;\n@at(0xB8000) private unsafe let screen: u16[2000];\n").clean();
        main_en("public class Stats { public n: i64; }\nprivate unsafe let stats: Stats = new Stats { n: 0 };\n").clean();
    });
    h.case("lower/EN0307: names given twice in one list", || {
        for src in [
            "public function f<T, T>(x: T): void { }\n",
            "public function f(o: { a: i64, a: i64 }): void { }\n",
            "public enum E { C { r: f64, r: f64 } }\n",
            "public interface P { x: i64; x: i64; }\n",
            "public class C { public a: i64; public constructor(public a: i64) { } }\n",
            "public interface I { m(a: i64, a: i64): void; }\n",
        ] {
            let r = main_en(src);
            assert_eq!(r.codes(), ["EN0307"], "{src}\n{}", r.rendered());
        }
    });
    h.case("lower/EN0401: `extends` names no class", || {
        let r = main_en("public interface I { m(): void; }\npublic class C extends I { }\n");
        assert_eq!(
            reported(&r),
            one("EN0401", "mismatched types: expected a class, found `I`")
        );
        assert_eq!(r.diags[0].primary.text, "`extends` takes a class");
    });
    review_cases(h);
    let _ = MINI_LIB;
}

/// The cases of stage 6's front review (`fix-2`): each fails without its fix.
fn review_cases(h: &mut Harness) {
    h.case(
        "lower/EN0401: a class that extends itself, directly or through others",
        || {
            let r = main_en("public final class A extends A {}\nprivate unsafe let s: A = new A {};\n");
            assert_eq!(reported(&r), one("EN0401", "`A` can't extend itself"));
            let span = r.diags[0].primary.span;
            assert_eq!(r.map.text(span), "A");
            assert_eq!(r.map.loc(span.lo).col, 30);
            assert_eq!(r.diags[0].primary.text, "this makes `A` a base of itself");
            let a = r.tcx.adt_of(r.def("src/main::A")).expect("a class");
            assert_eq!(r.tcx.adt(a).as_class().expect("a class").base, None);
            // Two classes: reported once, at the first class in source order, which
            // loses its base; the other keeps its own.
            for tail in [
                "private unsafe let s: A = new A {};\n",
                "private unsafe let s: B;\n",
                "@at(0xB8000) private unsafe let s: A[2];\n",
                "",
            ] {
                let src = format!("public class A extends B {{}}\npublic class B extends A {{}}\n{tail}");
                let r = main_en(&src);
                assert_eq!(r.codes()[0], "EN0401", "{src}");
                assert_eq!(r.messages()[0], "`A` can't extend itself", "{src}");
                assert_eq!(r.map.loc(r.diags[0].primary.span.lo).line, 1, "{src}");
                let a = r.tcx.adt_of(r.def("src/main::A")).expect("a class");
                let b = r.tcx.adt_of(r.def("src/main::B")).expect("a class");
                assert_eq!(r.tcx.adt(a).as_class().expect("a class").base, None);
                let base = r.tcx.adt(b).as_class().expect("a class").base;
                assert!(matches!(base.map(|t| r.tcx.kind(t)), Some(TyKind::Adt(x, _)) if x == a));
            }
            // A class below a cycle is not part of it.
            let r = main_en("public class C extends A {}\npublic class A extends B {}\npublic class B extends A {}\n");
            assert_eq!(reported(&r), one("EN0401", "`A` can't extend itself"));
            assert_eq!(r.map.loc(r.diags[0].primary.span.lo).line, 2);
        },
    );
    h.case("lower/EN0408: a class that holds itself through an inherited field", || {
        // `B` holds `x: B | null` inline, which `A` declares.
        let r = main_en("public class A {\n  public x: B | null = null;\n}\npublic final class B extends A {}\n");
        assert_eq!(reported(&r), one("EN0408", "recursive type `B` needs `Box`"));
        assert_eq!(r.map.text(r.diags[0].primary.span), "B | null");
        assert_eq!(r.map.loc(r.diags[0].primary.span.lo).line, 2);
        assert_eq!(r.diags[0].primary.text, "this holds a `B` inline");
        assert_eq!(r.diags[0].helps[0].edits[0].replacement, "Box<B> | null");
        let r = main_en("public class A {\n  public x: B[1];\n}\npublic final class B extends A {}\n");
        assert_eq!(r.codes(), ["EN0408"]);
        // Through a fixed array of the class itself (M17).
        let r = main_en("public class Q { public t: Q[2]; }\n");
        assert_eq!(reported(&r), one("EN0408", "recursive type `Q` needs `Box`"));
        assert_eq!(r.map.text(r.diags[0].primary.span), "Q[2]");
        main_en("public class A {\n  public x: Box<B> | null = null;\n}\npublic final class B extends A {}\n").clean();
    });
    h.case(
        "lower/EN0456: reported once, however often the kinds alternate",
        || {
            let r = main_en("public enum E { A = 1, B = \"b\", C = 3, D = \"d\" }\n");
            assert_eq!(
                reported(&r),
                one("EN0456", "`E` mixes number and text values")
            );
            assert_eq!(r.map.text(r.diags[0].primary.span), "\"b\"");
        },
    );
    h.case(
        "lower/EN0437: the alias that reaches itself becomes an error type",
        || {
            let r = main_en("public type A = A[];\n");
            assert_eq!(r.codes(), ["EN0437"]);
            let def = r.def("src/main::A");
            let alias = r.tcx.alias(def).expect("lowered");
            assert_eq!(r.tcx.kind(alias.ty), TyKind::Error);
        },
    );
    h.case(
        "lower/EN0417: the fix-it turns the field into a method",
        || {
            let r = main_en("public interface Shape {\n  name: string;\n  area(): f64;\n}\n");
            assert_eq!(r.codes(), ["EN0417"]);
            assert_eq!(
                r.rendered(),
                "error[EN0417]: interface `Shape` mixes fields and methods
 --> src/main.en:2:3
  |
2 |   name: string;
  |   ^^^^^^^^^^^^ a field in an interface with methods
  |
help: make it a method: `name(): &string`
  |
2 |   name(): &string;
  |   ~~~~~~~~~~~~~~~
  = explain: run `enrang explain EN0417`

error: aborting due to 1 previous error
"
            );
            for (field, method) in [
                ("x?: i64", "x(): &i64 | null"),
                ("next: Node | null", "next(): &Node | null"),
                ("r: &u8", "r(): &u8"),
                ("t: [i64, u8]", "t(): &[i64, u8]"),
                ("f: (x: i64) => void", "f(): &((x: i64) => void)"),
            ] {
                let src = format!(
                    "public class Node {{ }}\npublic interface I {{\n  {field};\n  m(): void;\n}}\n"
                );
                let r = main_en(&src);
                assert_eq!(r.codes(), ["EN0417"], "{src}");
                let edit = &r.diags[0].helps[0].edits[0];
                assert_eq!(r.map.text(edit.span), field, "{src}");
                assert_eq!(edit.replacement, method, "{src}");
            }
        },
    );
    h.case("lower/EN0816 and EN1030: only scalars, raw and `fn` pointers cross", || {
        let class = "this foreign ABI is not supported yet";
        for (param, code, message) in [
            ("b: Box<i32>", "EN1030", class.to_owned()),
            ("p: { x: i32 }", "EN1030", class.to_owned()),
            ("s: Shape", "EN1030", class.to_owned()),
            ("t: [i32, u8]", "EN1030", class.to_owned()),
            ("e: Payload", "EN1030", class.to_owned()),
            ("cb: (x: i32) => void", "EN0816", "`(int) => void` can't cross into foreign code".to_owned()),
            ("n: i32 | null", "EN0816", "`int | null` can't cross into foreign code".to_owned()),
            ("a: u8[4]", "EN0816", "`u8[4]` can't cross into foreign code".to_owned()),
            ("v: Slice<u8>", "EN0816", "`Slice<u8>` can't cross into foreign code".to_owned()),
        ] {
            let src = format!(
                "public interface Shape {{ area(): f64; }}\npublic enum Payload {{ A {{ x: i32 }} }}\n@dll(\"k.dll\") public declare function f({param}): void;\n"
            );
            let r = main_en(&src);
            assert_eq!(reported(&r), one(code, &message), "{src}");
            let span = r.diags[0].primary.span;
            assert_eq!(Some(r.map.text(span)), param.split_once(": ").map(|p| p.1), "{src}");
        }
        // A `declare` gets no implicit type parameter (D5).
        let r = main_en("public interface Shape { area(): f64; }\n@dll(\"k.dll\") public declare function d(s: &Shape): void;\n");
        assert_eq!(r.codes(), ["EN0816"]);
        let sig = r.tcx.sig(r.def("src/main::d"));
        assert!(r.tcx.generics(sig.generics).params.is_empty());
        let r = main_en("@dll(\"k.dll\") public declare function f(): { x: i32 };\n");
        assert_eq!(reported(&r), one("EN1030", class));
        let r = main_en("public type F = @abi(\"sysv\") fn(b: Box<i32>, o: { x: i32 }, n: i32 | null) => void;\n");
        assert_eq!(r.codes(), ["EN1030", "EN1030", "EN0816"]);
        main_en("public enum Mode { A, B = 2 }\n@dll(\"k.dll\") public declare function ok(m: Mode, p: *u8 | null, f: (fn(x: i32) => void) | null, b: bool, x: f64): void;\n").clean();
    });
    h.case(
        "lower/EN0827: a hidden pointer held through classes and enum cases",
        || {
            let r = main_en("@repr(\"C\") public final class A {\n  public b: B;\n}\npublic final class B {\n  public c: C;\n}\npublic class C {}\n");
            assert_eq!(
                reported(&r),
                one("EN0827", "a `@repr(\"C\")` class can't hold `C` inline")
            );
            assert_eq!(r.map.text(r.diags[0].primary.span), "B");
            assert_eq!(r.diags[0].primary.text, "`C` carries a hidden method-table pointer");
            let r = main_en("@packed public final class A {\n  public e: E;\n}\npublic enum E { One { c: C }, Two }\npublic class C {}\n");
            assert_eq!(
                reported(&r),
                one("EN0827", "a `@packed` class can't hold `C` inline")
            );
            main_en("@repr(\"C\") public final class A {\n  public b: B;\n}\npublic final class B {\n  private c: Box<C> | null;\n}\npublic class C {}\n").clean();
        },
    );
    h.case("lower/EN0419: a bound that is no interface or class", || {
        let r = main_en("public enum E { A }\npublic type N = i64;\npublic function f<T extends i64, U extends E, V extends N>(x: T, y: U, z: V): void {}\n");
        assert_eq!(r.codes(), ["EN0419", "EN0419", "EN0419"]);
        assert_eq!(
            r.messages(),
            ["`i64` can't be a bound", "`E` can't be a bound", "`i64` can't be a bound"]
        );
        assert_eq!(r.map.text(r.diags[1].primary.span), "E");
        assert_eq!(r.diags[0].primary.text, "a bound names an interface or a class");
        main_en("public interface I { m(): void; }\npublic class C { }\npublic function f<T extends I, U extends C>(x: &T, y: &U): void {}\n").clean();
    });
    h.case("lower/EN0802: a `Box` owns heap memory (M36)", || {
        let r = main_en("private unsafe let b: Box<i64>;\n");
        assert_eq!(
            reported(&r),
            one("EN0802", "an `unsafe let` can't hold a `Box<i64>`")
        );
        assert_eq!(r.diags[0].primary.text, "`Box<i64>` owns heap memory");
    });
}
