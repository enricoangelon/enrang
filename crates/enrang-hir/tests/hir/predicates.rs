//! The predicates: SPEC 4.1's `V` and `S` row by row (A:266-279), Copy (SPEC O4),
//! Clone (SPEC 4.4, coinductive) and drop.

use enrang_base::intern;
use enrang_hir::{
    Abi, ClassModifier, FnPtrSig, LangItem, ParamEnv, Ty, Vis, is_slot_type, is_value_type,
};
use enrang_testkit::Harness;

use crate::support::{F, World};

/// A world with a plain class `Point { x: i64 }`, a borrowing class `View { private
/// r: &i64 }`, an interface `Speaker`, the lang `Copy` and `Clone` interfaces and the
/// lang `Result<T, E>`.
struct Fixture {
    w: World,
    point: Ty,
    view: Ty,
    speaker: Ty,
    copy: enrang_hir::AdtId,
    clone: enrang_hir::AdtId,
    result: enrang_hir::AdtId,
}

fn fixture() -> Fixture {
    let mut w = World::new();
    let i64 = w.tcx.common().i64;
    let (point, _) = w.class("Point", ClassModifier::Final, &[]);
    w.field(point, "x", i64, Vis::Public);
    let (view, _) = w.class("View", ClassModifier::Final, &[]);
    let r = w.tcx.mk_ref(i64);
    w.field(view, "r", r, Vis::Private);
    let (speaker, _) = w.interface("Speaker", &[], None);
    let (copy, _) = w.interface("Copy", &[], None);
    w.lang(LangItem::Copy, copy);
    let (clone, _) = w.interface("Clone", &[], None);
    w.lang(LangItem::Clone, clone);
    let (result, _) = w.enumeration(
        "Result",
        &["T", "E"],
        &[
            ("Ok", &[("value", F::P(0))]),
            ("Err", &[("error", F::P(1))]),
        ],
    );
    w.lang(LangItem::Result, result);
    let point = w.tcx.mk_adt(point, &[]);
    let view = w.tcx.mk_adt(view, &[]);
    let speaker = w.tcx.mk_adt(speaker, &[]);
    Fixture {
        w,
        point,
        view,
        speaker,
        copy,
        clone,
        result,
    }
}

type Row = (&'static str, bool, bool, fn(&mut Fixture) -> Ty);

/// `(type, in V, in S, make)`, one row per constructor of SPEC 4.1.
const VALUE_ROWS: &[Row] = &[
    ("bool", true, true, |f| f.w.tcx.common().bool),
    ("i8", true, true, |f| f.w.tcx.common().i8),
    ("u64", true, true, |f| f.w.tcx.common().u64),
    ("usize", true, true, |f| f.w.tcx.common().usize),
    ("f32", true, true, |f| f.w.tcx.common().f32),
    ("void", true, true, |f| f.w.tcx.common().void),
    ("never", true, true, |f| f.w.tcx.common().never),
    ("string", true, true, |f| f.w.tcx.common().str),
    ("i64[]", true, true, |f| {
        f.w.tcx.mk_array(f.w.tcx.common().i64)
    }),
    ("i64[4]", true, true, |f| {
        f.w.tcx.mk_fixed(f.w.tcx.common().i64, 4)
    }),
    ("[i64, string]", true, true, |f| {
        f.w.tcx
            .mk_tuple(&[f.w.tcx.common().i64, f.w.tcx.common().str])
    }),
    ("{ name: string }", true, true, |f| {
        f.w.tcx
            .mk_object(vec![(intern("name"), f.w.tcx.common().str)])
    }),
    ("Box<Point>", true, true, |f| f.w.tcx.mk_box(f.point)),
    ("Box<Speaker>", true, true, |f| f.w.tcx.mk_box(f.speaker)),
    ("Point | null", true, true, |f| f.w.tcx.mk_nullable(f.point)),
    ("Result<i64, i64>", true, true, |f| {
        let i64 = f.w.tcx.common().i64;
        f.w.tcx.mk_adt(f.result, &[i64, i64])
    }),
    ("Point", true, true, |f| f.point),
    ("*u8", true, true, |f| f.w.tcx.mk_raw(f.w.tcx.common().u8)),
    ("fn(&string) => void", true, true, |f| {
        let r = f.w.tcx.mk_ref(f.w.tcx.common().str);
        f.w.tcx
            .mk_fn_ptr(Abi::Enrang, FnPtrSig::new(&[r], f.w.tcx.common().void))
    }),
    ("T", true, true, |f| f.w.bounded_param("T", &[]).1),
    // R
    ("&i64", false, true, |f| {
        f.w.tcx.mk_ref(f.w.tcx.common().i64)
    }),
    ("&Slice<u8>", false, true, |f| {
        f.w.tcx.mk_ref(f.w.tcx.mk_slice(f.w.tcx.common().u8))
    }),
    ("&View", false, true, |f| f.w.tcx.mk_ref(f.view)),
    ("&Speaker", false, true, |f| f.w.tcx.mk_ref(f.speaker)),
    ("&i64 | null", false, true, |f| {
        f.w.tcx.mk_nullable(f.w.tcx.mk_ref(f.w.tcx.common().i64))
    }),
    ("&Speaker | null", false, true, |f| {
        f.w.tcx.mk_nullable(f.w.tcx.mk_ref(f.speaker))
    }),
    // B
    ("View", false, true, |f| f.view),
    ("View | null", false, true, |f| f.w.tcx.mk_nullable(f.view)),
    ("[&i64[], int]", false, true, |f| {
        let r = f.w.tcx.mk_ref(f.w.tcx.mk_array(f.w.tcx.common().i64));
        f.w.tcx.mk_tuple(&[r, f.w.tcx.common().i32])
    }),
    // Neither
    ("Slice<u8>", false, false, |f| {
        f.w.tcx.mk_slice(f.w.tcx.common().u8)
    }),
    ("Speaker", false, false, |f| f.speaker),
    ("(&i64)[]", false, false, |f| {
        f.w.tcx.mk_array(f.w.tcx.mk_ref(f.w.tcx.common().i64))
    }),
    ("View[]", false, false, |f| f.w.tcx.mk_array(f.view)),
    ("Box<View>", false, false, |f| f.w.tcx.mk_box(f.view)),
    ("Box<&i64>", false, false, |f| {
        f.w.tcx.mk_box(f.w.tcx.mk_ref(f.w.tcx.common().i64))
    }),
    ("{ r: &i64 }", false, false, |f| {
        f.w.tcx
            .mk_object(vec![(intern("r"), f.w.tcx.mk_ref(f.w.tcx.common().i64))])
    }),
    ("&&i64", false, false, |f| {
        f.w.tcx.mk_ref(f.w.tcx.mk_ref(f.w.tcx.common().i64))
    }),
    ("&(&i64 | null)", false, false, |f| {
        let inner = f.w.tcx.mk_nullable(f.w.tcx.mk_ref(f.w.tcx.common().i64));
        f.w.tcx.mk_ref(inner)
    }),
    ("(u8) => void", false, false, |f| {
        f.w.tcx
            .mk_closure(FnPtrSig::new(&[f.w.tcx.common().u8], f.w.tcx.common().void))
    }),
    ("Result<&i64, i64>", false, false, |f| {
        let r = f.w.tcx.mk_ref(f.w.tcx.common().i64);
        let i64 = f.w.tcx.common().i64;
        f.w.tcx.mk_adt(f.result, &[r, i64])
    }),
];

/// `(type, Copy, make)`.
type CopyRow = (&'static str, bool, fn(&mut Fixture) -> Ty);

/// `(type, Copy, make)` over SPEC O4.
const COPY_ROWS: &[CopyRow] = &[
    ("i32", true, |f| f.w.tcx.common().i32),
    ("f64", true, |f| f.w.tcx.common().f64),
    ("bool", true, |f| f.w.tcx.common().bool),
    ("void", true, |f| f.w.tcx.common().void),
    ("never", true, |f| f.w.tcx.common().never),
    ("&string", true, |f| f.w.tcx.mk_ref(f.w.tcx.common().str)),
    ("*u8", true, |f| f.w.tcx.mk_raw(f.w.tcx.common().u8)),
    ("fn() => void", true, |f| {
        f.w.tcx
            .mk_fn_ptr(Abi::Enrang, FnPtrSig::new(&[], f.w.tcx.common().void))
    }),
    ("payload-free enum", true, |f| {
        let (e, _) = f.w.enumeration("Dir", &[], &[("Up", &[]), ("Down", &[])]);
        f.w.tcx.mk_adt(e, &[])
    }),
    ("i64[3]", true, |f| {
        f.w.tcx.mk_fixed(f.w.tcx.common().i64, 3)
    }),
    ("i64 | null", true, |f| {
        f.w.tcx.mk_nullable(f.w.tcx.common().i64)
    }),
    ("[i64, bool]", true, |f| {
        f.w.tcx
            .mk_tuple(&[f.w.tcx.common().i64, f.w.tcx.common().bool])
    }),
    ("{ x: i64 }", true, |f| {
        f.w.tcx.mk_object(vec![(intern("x"), f.w.tcx.common().i64)])
    }),
    ("class implements Copy", true, |f| {
        let (c, _) = f.w.class("P", ClassModifier::Final, &[]);
        f.w.set_copy(c);
        f.w.tcx.mk_adt(c, &[])
    }),
    ("Result<i64, Dir>", true, |f| {
        let (e, _) = f.w.enumeration("Dir", &[], &[("Up", &[])]);
        let e = f.w.tcx.mk_adt(e, &[]);
        let i64 = f.w.tcx.common().i64;
        f.w.tcx.mk_adt(f.result, &[i64, e])
    }),
    ("T extends Copy", true, |f| {
        let copy = f.copy;
        f.w.bounded_param("T", &[copy]).1
    }),
    ("string", false, |f| f.w.tcx.common().str),
    ("i64[]", false, |f| f.w.tcx.mk_array(f.w.tcx.common().i64)),
    ("Box<i64>", false, |f| f.w.tcx.mk_box(f.w.tcx.common().i64)),
    ("class without implements Copy", false, |f| f.point),
    ("subclass of a Copy class", false, |f| {
        let (base, _) = f.w.class("Base", ClassModifier::Plain, &[]);
        f.w.set_copy(base);
        let (sub, _) = f.w.class("Sub", ClassModifier::Plain, &[]);
        let base = f.w.tcx.mk_adt(base, &[]);
        f.w.extends(sub, base);
        f.w.tcx.mk_adt(sub, &[])
    }),
    ("enum with a payload", false, |f| {
        let i64 = f.w.tcx.common().i64;
        let (e, _) =
            f.w.enumeration("Shape", &[], &[("Circle", &[("r", F::T(i64))])]);
        f.w.tcx.mk_adt(e, &[])
    }),
    ("string | null", false, |f| {
        f.w.tcx.mk_nullable(f.w.tcx.common().str)
    }),
    ("[i64, string]", false, |f| {
        f.w.tcx
            .mk_tuple(&[f.w.tcx.common().i64, f.w.tcx.common().str])
    }),
    ("Result<string, i64>", false, |f| {
        let (s, i) = (f.w.tcx.common().str, f.w.tcx.common().i64);
        f.w.tcx.mk_adt(f.result, &[s, i])
    }),
    ("unbounded T", false, |f| f.w.bounded_param("T", &[]).1),
];

pub fn register(h: &mut Harness) {
    for (name, value, slot, make) in VALUE_ROWS {
        let (value, slot, make) = (*value, *slot, *make);
        h.case(format!("predicates/V and S: {name}"), move || {
            let mut f = fixture();
            let ty = make(&mut f);
            assert_eq!(
                is_value_type(&f.w.tcx, ty),
                value,
                "V of {}",
                f.w.tcx.ty_string(ty)
            );
            assert_eq!(
                is_slot_type(&f.w.tcx, ty),
                slot,
                "S of {}",
                f.w.tcx.ty_string(ty)
            );
        });
    }
    for (name, copy, make) in COPY_ROWS {
        let (copy, make) = (*copy, *make);
        h.case(format!("predicates/Copy: {name}"), move || {
            let mut f = fixture();
            let ty = make(&mut f);
            assert_eq!(f.w.tcx.is_copy(ty, &ParamEnv::empty()), copy);
        });
    }
    h.case("predicates/a where clause adds a Copy bound", || {
        let mut f = fixture();
        let (p, t) = f.w.bounded_param("T", &[]);
        assert!(!f.w.tcx.is_copy(t, &ParamEnv::empty()));
        let args = f.w.tcx.empty_list();
        let b =
            f.w.tcx
                .define_bound(enrang_hir::Bound::Iface { adt: f.copy, args });
        let env = ParamEnv {
            bounds: vec![(p, vec![b])],
        };
        assert!(f.w.tcx.is_copy(t, &env));
        assert!(f.w.tcx.is_clone(t, &env), "`T extends Copy` implies Clone");
    });
    h.case(
        "predicates/a borrowing class is borrowing, a plain one is not",
        || {
            let f = fixture();
            assert!(f.w.tcx.is_borrowing(f.view));
            assert!(!f.w.tcx.is_borrowing(f.point));
            let enrang_hir::TyKind::Adt(view, _) = f.w.tcx.kind(f.view) else {
                panic!("an ADT")
            };
            assert!(f.w.tcx.is_borrowing_class(view));
        },
    );
    h.case(
        "predicates/Clone: a Box<Node> | null field of Node is Clone (coinductive)",
        || {
            let mut f = fixture();
            let (node, _) = f.w.class("Node", ClassModifier::Final, &[]);
            let node_ty = f.w.tcx.mk_adt(node, &[]);
            let next = f.w.tcx.mk_nullable(f.w.tcx.mk_box(node_ty));
            f.w.field(node, "value", f.w.tcx.common().i64, Vis::Public);
            f.w.field(node, "next", next, Vis::Public);
            assert!(f.w.tcx.is_clone(node_ty, &ParamEnv::empty()));
            assert!(f.w.tcx.needs_drop(node_ty));
        },
    );
    h.case(
        "predicates/Clone: a destructor without a written clone is not Clone",
        || {
            let mut f = fixture();
            let (region, _) = f.w.class("Region", ClassModifier::Final, &[]);
            f.w.dtor(region);
            let region = f.w.tcx.mk_adt(region, &[]);
            assert!(!f.w.tcx.is_clone(region, &ParamEnv::empty()));
            assert!(f.w.tcx.needs_drop(region));
        },
    );
    h.case("predicates/Clone: a written clone always wins", || {
        let mut f = fixture();
        let (region, _) = f.w.class("Region", ClassModifier::Final, &[]);
        f.w.dtor(region);
        let ty = f.w.tcx.mk_adt(region, &[]);
        f.w.method(region, "clone", &[], ty, Vis::Public);
        assert!(f.w.tcx.is_clone(ty, &ParamEnv::empty()));
    });
    h.case(
        "predicates/Clone: a raw pointer field stops synthesis",
        || {
            let mut f = fixture();
            let (c, _) = f.w.class("Buf", ClassModifier::Final, &[]);
            let raw = f.w.tcx.mk_raw(f.w.tcx.common().u8);
            f.w.field(c, "p", raw, Vis::Private);
            let c = f.w.tcx.mk_adt(c, &[]);
            assert!(!f.w.tcx.is_clone(c, &ParamEnv::empty()));
        },
    );
    h.case("predicates/Clone: the structural rows", || {
        let mut f = fixture();
        let env = ParamEnv::empty();
        let t = &f.w.tcx;
        let s = t.common().str;
        for ty in [
            s,
            t.mk_array(s),
            t.mk_nullable(s),
            t.mk_fixed(s, 2),
            t.mk_tuple(&[s, t.common().i64]),
            t.mk_object(vec![(intern("s"), s)]),
            t.mk_box(s),
            t.mk_adt(f.result, &[s, s]),
            f.point,
        ] {
            assert!(t.is_clone(ty, &env), "{}", t.ty_string(ty));
        }
        for ty in [t.mk_ref(s), t.mk_slice(s), f.speaker] {
            assert!(!t.is_clone(ty, &env), "{}", t.ty_string(ty));
        }
        let clone = f.clone;
        let bounded = f.w.bounded_param("T", &[clone]).1;
        assert!(f.w.tcx.is_clone(bounded, &env));
        let unbounded = f.w.bounded_param("U", &[]).1;
        assert!(!f.w.tcx.is_clone(unbounded, &env));
    });
    h.case("predicates/needs_drop", || {
        let mut f = fixture();
        let t = &f.w.tcx;
        assert!(!t.needs_drop(t.common().i64));
        assert!(!t.needs_drop(t.mk_ref(t.common().str)));
        assert!(t.needs_drop(t.common().str));
        assert!(t.needs_drop(t.mk_nullable(t.mk_array(t.common().i64))));
        assert!(!t.needs_drop(f.point));
        let (holder, ps) = f.w.class("Holder", ClassModifier::Final, &["T"]);
        f.w.field(holder, "v", ps[0], Vis::Public);
        let t = &f.w.tcx;
        assert!(!t.needs_drop(t.mk_adt(holder, &[t.common().i64])));
        assert!(t.needs_drop(t.mk_adt(holder, &[t.common().str])));
        let (base, _) = f.w.class("Base", ClassModifier::Plain, &[]);
        f.w.dtor(base);
        let (sub, _) = f.w.class("Sub", ClassModifier::Plain, &[]);
        let base_ty = f.w.tcx.mk_adt(base, &[]);
        f.w.extends(sub, base_ty);
        let sub_ty = f.w.tcx.mk_adt(sub, &[]);
        assert!(
            f.w.tcx.needs_drop(sub_ty),
            "a base's destructor runs for a subclass"
        );
        // A cyclic chain, which sema reports and breaks, still ends.
        let (a, _) = f.w.class("A", ClassModifier::Plain, &[]);
        let (b, _) = f.w.class("B", ClassModifier::Plain, &[]);
        let (a_ty, b_ty) = (f.w.tcx.mk_adt(a, &[]), f.w.tcx.mk_adt(b, &[]));
        f.w.extends(a, b_ty);
        f.w.extends(b, a_ty);
        let none = f.w.tcx.empty_list();
        assert_eq!(f.w.tcx.class_dtor(a, none), None);
        assert!(!f.w.tcx.needs_drop(a_ty));
        f.w.dtor(b);
        assert!(f.w.tcx.class_dtor(a, none).is_some());
    });
}
