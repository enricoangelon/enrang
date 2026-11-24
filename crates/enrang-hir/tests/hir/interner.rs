//! The interner: structural equality is identity (A:252), rows are part of a
//! signature's identity and ignored by `same_ignoring_rows` (A:288-291, N1).

use enrang_base::intern;
use enrang_hir::{Abi, FnPtrSig, Mark, Shape, TyKind};
use enrang_testkit::Harness;

use crate::support::World;

pub fn register(h: &mut Harness) {
    h.case("interner/equal kinds are one type", || {
        let w = World::new();
        let t = &w.tcx;
        let i64 = t.common().i64;
        assert_eq!(t.intern_ty(TyKind::Int(enrang_hir::IntTy::I64)), i64);
        assert_eq!(t.mk_ref(t.mk_array(i64)), t.mk_ref(t.mk_array(i64)));
        assert_ne!(t.mk_ref(t.mk_array(i64)), t.mk_array(t.mk_ref(i64)));
        assert_eq!(
            t.mk_tuple(&[i64, t.common().str]),
            t.mk_tuple(&[i64, t.common().str])
        );
        assert_ne!(
            t.mk_tuple(&[i64, t.common().str]),
            t.mk_tuple(&[t.common().str, i64])
        );
        assert_eq!(t.kind(t.mk_nullable(i64)), TyKind::Nullable(i64));
    });
    h.case("interner/the common types are interned once", || {
        let w = World::new();
        let t = &w.tcx;
        let before = t.ty_count();
        for kind in [
            TyKind::Bool,
            TyKind::Void,
            TyKind::Never,
            TyKind::Str,
            TyKind::Error,
        ] {
            t.intern_ty(kind);
        }
        assert_eq!(t.ty_count(), before);
    });
    h.case("interner/lists and shapes are interned by content", || {
        let w = World::new();
        let t = &w.tcx;
        let (a, b) = (t.common().i32, t.common().bool);
        assert_eq!(t.intern_list(&[a, b]), t.intern_list(&[a, b]));
        assert_eq!(&*t.list(t.intern_list(&[a, b])), &[a, b]);
        assert_eq!(t.list(t.empty_list()).len(), 0);
        let one = t.mk_object(vec![(intern("name"), t.common().str), (intern("age"), a)]);
        let two = t.mk_object(vec![(intern("age"), a), (intern("name"), t.common().str)]);
        assert_eq!(one, two, "field order is irrelevant (SPEC 4.3)");
        let TyKind::Object(shape) = t.kind(one) else {
            panic!("an object")
        };
        let names: Vec<&str> = t
            .shape(shape)
            .fields
            .iter()
            .map(|(n, _)| n.as_str())
            .collect();
        assert_eq!(names, ["age", "name"]);
        assert_eq!(t.shape(shape).position(intern("name")), Some(1));
        let direct = t.intern_shape(Shape {
            fields: vec![(intern("name"), t.common().str), (intern("age"), a)],
            optional: Vec::new(),
        });
        assert_eq!(direct, shape, "intern_shape sorts what it is given");
    });
    h.case(
        "interner/a field written `x?: T` is part of a shape's identity (D13)",
        || {
            let w = World::new();
            let t = &w.tcx;
            let v = t.mk_nullable(t.common().i64);
            let fields = vec![(intern("v"), v), (intern("w"), t.common().bool)];
            let required = t.mk_object(fields.clone());
            let optional =
                t.mk_object_shape(Shape::with_optional(fields.clone(), vec![intern("v")]));
            assert_ne!(required, optional, "a literal may leave out only `v?`");
            assert!(
                t.same_ignoring_rows(required, optional),
                "typing's one type"
            );
            let TyKind::Object(shape) = t.kind(optional) else {
                panic!("an object")
            };
            let shape = t.shape(shape);
            assert!(shape.is_optional(intern("v")));
            assert!(!shape.is_optional(intern("w")));
            let again = t.mk_object_shape(Shape {
                fields: fields.into_iter().rev().collect(),
                optional: vec![intern("v"), intern("v"), intern("nope")],
            });
            assert_eq!(
                again, optional,
                "sorted, deduplicated, unknown names dropped"
            );
            let swapped = t.map_ty(optional, &mut |tcx, inner| {
                (inner == tcx.common().bool).then(|| tcx.common().u8)
            });
            let TyKind::Object(swapped) = t.kind(swapped) else {
                panic!("an object")
            };
            assert_eq!(t.shape(swapped).optional, [intern("v")], "map_ty keeps it");
        },
    );
    h.case("interner/rows are part of a signature's identity", || {
        let w = World::new();
        let t = &w.tcx;
        let r = t.mk_ref(t.common().i64);
        let plain = t.mk_fn_ptr(Abi::Enrang, FnPtrSig::new(&[r], t.common().void));
        let mut marked = FnPtrSig::new(&[r], t.common().void);
        marked.params[0].1 = Mark::Let;
        let marked = t.mk_fn_ptr(Abi::Enrang, marked);
        assert_ne!(plain, marked);
        assert!(t.same_ignoring_rows(plain, marked));
        let mut readonly = FnPtrSig::new(&[r], r);
        readonly.ret_readonly = true;
        let readonly = t.mk_fn_ptr(Abi::Enrang, readonly);
        let writable = t.mk_fn_ptr(Abi::Enrang, FnPtrSig::new(&[r], r));
        assert_ne!(readonly, writable);
        assert!(t.same_ignoring_rows(readonly, writable));
        assert!(
            t.same_ignoring_rows(t.mk_array(readonly), t.mk_array(writable)),
            "rows are ignored at any depth"
        );
    });
    h.case(
        "interner/same_ignoring_rows keeps every other difference",
        || {
            let w = World::new();
            let t = &w.tcx;
            let r = t.mk_ref(t.common().i64);
            let safe = t.mk_fn_ptr(Abi::Enrang, FnPtrSig::new(&[r], t.common().void));
            let mut unsafe_sig = FnPtrSig::new(&[r], t.common().void);
            unsafe_sig.unsafety = true;
            let unsafe_fn = t.mk_fn_ptr(Abi::Enrang, unsafe_sig);
            let foreign = t.mk_fn_ptr(Abi::Win64, FnPtrSig::new(&[r], t.common().void));
            let closure = t.mk_closure(FnPtrSig::new(&[r], t.common().void));
            assert!(!t.same_ignoring_rows(safe, unsafe_fn));
            assert!(!t.same_ignoring_rows(safe, foreign));
            assert!(!t.same_ignoring_rows(safe, closure));
            assert!(!t.same_ignoring_rows(t.common().i64, t.common().i32));
            assert!(
                !t.same_ignoring_rows(t.mk_fixed(t.common().u8, 4), t.mk_fixed(t.common().u8, 5))
            );
        },
    );
    h.case("interner/subst replaces parameters at any depth", || {
        let mut w = World::new();
        let owner = w.bounded_param("T", &[]).0;
        let t = &w.tcx;
        let p = t.mk_param(owner);
        let shape = t.mk_ref(t.mk_nullable(t.mk_array(p)));
        let done = t.subst(shape, &[owner], &[t.common().str]);
        assert_eq!(done, t.mk_ref(t.mk_nullable(t.mk_array(t.common().str))));
        assert!(t.has_params(shape));
        assert!(!t.has_params(done));
        let sig = t.mk_fn_ptr(Abi::Enrang, FnPtrSig::new(&[p], p));
        let done = t.subst(sig, &[owner], &[t.common().i64]);
        let i64 = t.common().i64;
        assert_eq!(done, t.mk_fn_ptr(Abi::Enrang, FnPtrSig::new(&[i64], i64)));
    });
    h.case("interner/literal texts are interned in order", || {
        let w = World::new();
        let t = &w.tcx;
        let a = t.intern_str("hello");
        let b = t.intern_str("world");
        assert_eq!(t.intern_str("hello"), a);
        assert_ne!(a, b);
        assert_eq!(&*t.str(b), "world");
        let texts: Vec<String> = t.strings().iter().map(|(_, s)| s.to_owned()).collect();
        assert_eq!(texts, ["hello", "world"]);
    });
    h.case("interner/a Tcx can move to another thread", || {
        fn is_send<T: Send>() {}
        is_send::<enrang_hir::Tcx>();
    });
}
