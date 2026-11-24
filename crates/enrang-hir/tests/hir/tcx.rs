//! The `Tcx` API a MIR fixture builds a program with (A:753-754), and its lookups.

use enrang_base::{Span, intern};
use enrang_hir::{
    AdtDecl, AdtKind, AliasDef, ClassModifier, ConstTree, ConstValue, DefData, DefKind, EnumDef,
    FieldIdx, FnDecl, FnSig, ItemPath, LangItem, ModulePath, ParamSig, TyKind, VariantDef,
    VariantIdx, Vis,
};
use enrang_testkit::Harness;

use crate::support::World;

pub fn register(h: &mut Harness) {
    h.case(
        "tcx/define_fn makes a definition with its signature",
        || {
            let mut w = World::new();
            let i64 = w.tcx.common().i64;
            let empty = w.tcx.empty_generics();
            let path = ItemPath::item(ModulePath::new("src/main"), intern("add"));
            let sig = FnSig::new(
                empty,
                vec![
                    ParamSig::new(intern("a"), i64),
                    ParamSig::new(intern("b"), i64),
                ],
                i64,
            );
            let f = w.tcx.define_fn(FnDecl {
                path: path.clone(),
                kind: DefKind::Fn,
                module: w.module,
                vis: Vis::Private,
                span: Span::DUMMY,
                parent: None,
                attrs: Default::default(),
                sig: sig.clone(),
            });
            assert_eq!(w.tcx.def(f).path, path);
            assert_eq!(w.tcx.def(f).vis, Vis::Private);
            assert_eq!(w.tcx.def(f).name(), Some(intern("add")));
            assert_eq!(w.tcx.sig(f), &sig);
            assert_eq!(w.tcx.sig(f).required_params(), 2);
            assert!(DefKind::Fn.has_sig());
            assert!(!DefKind::Const.has_sig());
        },
    );
    h.case("tcx/define_adt sets the definition's kind", || {
        let mut w = World::new();
        let empty = w.tcx.empty_generics();
        let data = DefData::new(
            ItemPath::item(ModulePath::new("src/main"), intern("Dir")),
            DefKind::Fn,
            w.module,
            Span::DUMMY,
        );
        let mut e = EnumDef::new(vec![
            VariantDef::new(intern("up")),
            VariantDef::new(intern("down")),
        ]);
        e.str_union = true;
        let adt = w.tcx.define_adt(AdtDecl {
            data,
            name: intern("Dir"),
            generics: empty,
            kind: AdtKind::Enum(e),
        });
        let def = w.tcx.adt(adt).def;
        assert_eq!(w.tcx.def(def).kind, DefKind::StrUnion(adt));
        assert_eq!(w.tcx.adt_of(def), Some(adt));
        let (class, _) = w.class("C", ClassModifier::Plain, &[]);
        let def = w.tcx.adt(class).def;
        assert_eq!(w.tcx.def(def).kind, DefKind::Adt(class));
        let e = w.tcx.adt(adt).as_enum().expect("an enum");
        assert_eq!(
            e.variant_named(intern("down")).map(|(v, _)| v),
            Some(VariantIdx(1))
        );
        assert!(e.is_payload_free());
    });
    h.case(
        "tcx/generics: parent first, identity arguments, field types at arguments",
        || {
            let mut w = World::new();
            let (pair, ps) = w.class("Pair", ClassModifier::Final, &["A", "B"]);
            w.field(pair, "first", ps[0], Vis::Public);
            let second = w.tcx.mk_nullable(ps[1]);
            w.field(pair, "second", second, Vis::Public);
            let m = w.method(pair, "swap", &[], w.tcx.common().void, Vis::Public);
            let sig_generics = w.tcx.sig(m).generics;
            let class_generics = w.tcx.adt(pair).generics;
            assert_eq!(
                w.tcx.all_params(sig_generics),
                w.tcx.all_params(class_generics)
            );
            let identity = w.tcx.adt_identity(pair);
            assert_eq!(w.tcx.ty_string(identity), "Pair<A, B>");
            let t = &w.tcx;
            let args = t.intern_list(&[t.common().i64, t.common().str]);
            assert_eq!(t.field_ty(pair, None, FieldIdx(0), args), t.common().i64);
            assert_eq!(
                t.field_ty(pair, None, FieldIdx(1), args),
                t.mk_nullable(t.common().str)
            );
            let class = t.adt(pair).as_class().expect("a class");
            assert_eq!(
                class.field_named(intern("second")).map(|(i, _)| i),
                Some(FieldIdx(1))
            );
            assert_eq!(class.own_fields().count(), 2);
        },
    );
    h.case(
        "tcx/lang items map normalised kinds back to their classes",
        || {
            let mut w = World::new();
            assert_eq!(w.tcx.lang_opt(LangItem::Boxed), None);
            let (boxed, _) = w.class("Box", ClassModifier::Final, &["T"]);
            w.lang(LangItem::Boxed, boxed);
            let def = w.tcx.adt(boxed).def;
            assert_eq!(w.tcx.lang(LangItem::Boxed), def);
            assert_eq!(w.tcx.lang_adt(LangItem::Boxed), Some(boxed));
            assert_eq!(w.tcx.lang_item_of(def), Some(LangItem::Boxed));
            let t = &w.tcx;
            let b = t.mk_box(t.common().i64);
            let (adt, args) = t.lang_class_of(b).expect("Box");
            assert_eq!(adt, boxed);
            assert_eq!(&*t.list(args), &[t.common().i64]);
            assert!(
                t.mk_result(t.common().i64, t.common().i64).is_none(),
                "no Result declared"
            );
        },
    );
    h.case("tcx/constants, statics, aliases and host calls", || {
        let mut w = World::new();
        let path = ItemPath::item(ModulePath::new("src/main"), intern("LIMIT"));
        let c = w
            .tcx
            .define_def(DefData::new(path, DefKind::Const, w.module, Span::DUMMY));
        let i64 = w.tcx.common().i64;
        w.tcx.set_item_ty(c, i64);
        w.tcx
            .set_const(c, ConstTree::Scalar(ConstValue::Int(10, i64)));
        assert_eq!(w.tcx.item_ty(c), Some(i64));
        assert_eq!(
            w.tcx.const_value(c).and_then(|v| v.as_scalar()),
            Some(ConstValue::Int(10, i64))
        );
        let path = ItemPath::item(ModulePath::new("src/main"), intern("Ints"));
        let a = w.tcx.define_def(DefData::new(
            path,
            DefKind::TypeAlias,
            w.module,
            Span::DUMMY,
        ));
        let empty = w.tcx.empty_generics();
        let arr = w.tcx.mk_array(i64);
        w.tcx.set_alias(
            a,
            AliasDef {
                generics: empty,
                ty: arr,
            },
        );
        assert_eq!(w.tcx.alias(a).map(|a| a.ty), Some(arr));
        let open = w.tcx.intern_host_call(intern("fs.open"));
        assert_eq!(w.tcx.intern_host_call(intern("fs.open")), open);
        assert_eq!(w.tcx.host_call_name(open).as_str(), "fs.open");
    });
    h.case("tcx/children, map_ty and references_error", || {
        let w = World::new();
        let t = &w.tcx;
        let ty = t.mk_tuple(&[t.common().i64, t.mk_ref(t.common().str)]);
        assert_eq!(
            t.children(ty),
            vec![t.common().i64, t.mk_ref(t.common().str)]
        );
        let swapped = t.map_ty(ty, &mut |tcx, inner| {
            (inner == tcx.common().str).then(|| tcx.common().bool)
        });
        assert_eq!(
            swapped,
            t.mk_tuple(&[t.common().i64, t.mk_ref(t.common().bool)])
        );
        assert!(!t.references_error(ty));
        assert!(t.references_error(t.mk_array(t.common().error)));
        assert!(matches!(t.kind(swapped), TyKind::Tuple(_)));
    });
}
