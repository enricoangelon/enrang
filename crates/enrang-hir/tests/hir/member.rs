//! `Tcx::member` on one type (A:760): own, inherited, `extend` blocks of the import
//! closure, sealed patterns, and the C18 fallback from `T[]` and `T[N]` to
//! `Slice<T>` (S:1378).

use enrang_base::intern;
use enrang_hir::{
    Adjust, ClassModifier, FieldIdx, LangItem, MemberKind, MemberRef, Ty, TyKind, Vis,
};
use enrang_testkit::Harness;

use crate::support::World;

fn methods(found: &MemberRef) -> Vec<enrang_hir::DefId> {
    match &found.kind {
        MemberKind::Methods(ms) => ms.iter().map(|m| m.def).collect(),
        MemberKind::Field { .. } => panic!("a field, not methods"),
    }
}

/// `Animal { protected name: string; private secret: i64; speak(); }` and
/// `Dog extends Animal { speak() (override); fetch(); }`.
struct Zoo {
    w: World,
    animal: enrang_hir::AdtId,
    dog: enrang_hir::AdtId,
    animal_speak: enrang_hir::DefId,
    animal_hidden: enrang_hir::DefId,
    dog_speak: enrang_hir::DefId,
    dog_fetch: enrang_hir::DefId,
}

fn zoo() -> Zoo {
    let mut w = World::new();
    let (animal, _) = w.class("Animal", ClassModifier::Plain, &[]);
    let str = w.tcx.common().str;
    let i64 = w.tcx.common().i64;
    let void = w.tcx.common().void;
    w.field(animal, "name", str, Vis::Protected);
    w.field(animal, "secret", i64, Vis::Private);
    let animal_speak = w.method(animal, "speak", &[], str, Vis::Public);
    let animal_hidden = w.method(animal, "hidden", &[], void, Vis::Private);
    let (dog, _) = w.class("Dog", ClassModifier::Final, &[]);
    let animal_ty = w.tcx.mk_adt(animal, &[]);
    w.extends(dog, animal_ty);
    let dog_speak = w.method(dog, "speak", &[], str, Vis::Public);
    let dog_fetch = w.method(dog, "fetch", &[i64], void, Vis::Public);
    Zoo {
        w,
        animal,
        dog,
        animal_speak,
        animal_hidden,
        dog_speak,
        dog_fetch,
    }
}

pub fn register(h: &mut Harness) {
    h.case("member/own field and method", || {
        let z = zoo();
        let t = &z.w.tcx;
        let animal = t.mk_adt(z.animal, &[]);
        let found = t.member(animal, intern("name"), z.w.module).expect("name");
        assert_eq!(
            found.kind,
            MemberKind::Field {
                adt: z.animal,
                field: FieldIdx(0)
            }
        );
        assert_eq!(found.owner, t.adt(z.animal).def);
        let found = t
            .member(animal, intern("speak"), z.w.module)
            .expect("speak");
        assert_eq!(methods(&found), [z.animal_speak]);
        assert!(t.member(animal, intern("bark"), z.w.module).is_none());
    });
    h.case("member/inherited fields keep the base's FieldIdx", || {
        let z = zoo();
        let t = &z.w.tcx;
        let dog = t.mk_adt(z.dog, &[]);
        let found = t.member(dog, intern("name"), z.w.module).expect("name");
        assert_eq!(
            found.kind,
            MemberKind::Field {
                adt: z.dog,
                field: FieldIdx(0)
            }
        );
    });
    h.case(
        "member/a base's private members are never found from a subclass",
        || {
            let z = zoo();
            let t = &z.w.tcx;
            let dog = t.mk_adt(z.dog, &[]);
            assert!(t.member(dog, intern("secret"), z.w.module).is_none());
            assert!(t.member(dog, intern("hidden"), z.w.module).is_none());
            let animal = t.mk_adt(z.animal, &[]);
            assert!(t.member(animal, intern("secret"), z.w.module).is_some());
            let found = t
                .member(animal, intern("hidden"), z.w.module)
                .expect("hidden");
            assert_eq!(methods(&found), [z.animal_hidden]);
        },
    );
    h.case(
        "member/an override hides the base's method of the same parameters",
        || {
            let z = zoo();
            let t = &z.w.tcx;
            let dog = t.mk_adt(z.dog, &[]);
            let found = t.member(dog, intern("speak"), z.w.module).expect("speak");
            assert_eq!(methods(&found), [z.dog_speak]);
            let found = t.member(dog, intern("fetch"), z.w.module).expect("fetch");
            assert_eq!(methods(&found), [z.dog_fetch]);
        },
    );
    h.case(
        "member/a subclass's overloads add to the inherited ones",
        || {
            let mut z = zoo();
            let i64 = z.w.tcx.common().i64;
            let str = z.w.tcx.common().str;
            let loud = z.w.method(z.dog, "speak", &[i64], str, Vis::Public);
            let t = &z.w.tcx;
            let dog = t.mk_adt(z.dog, &[]);
            let found = t.member(dog, intern("speak"), z.w.module).expect("speak");
            assert_eq!(methods(&found), [z.dog_speak, loud]);
        },
    );
    h.case(
        "member/a generic base is seen at the subclass's arguments",
        || {
            let mut w = World::new();
            let (holder, ps) = w.class("Holder", ClassModifier::Plain, &["T"]);
            let get = w.method(holder, "get", &[], ps[0], Vis::Public);
            let (ints, _) = w.class("Ints", ClassModifier::Final, &[]);
            let i64 = w.tcx.common().i64;
            let base = w.tcx.mk_adt(holder, &[i64]);
            w.extends(ints, base);
            let t = &w.tcx;
            let found = t
                .member(t.mk_adt(ints, &[]), intern("get"), w.module)
                .expect("get");
            assert_eq!(methods(&found), [get]);
            assert_eq!(&*t.list(found.args), &[i64]);
        },
    );
    h.case("member/extend blocks in the import closure only", || {
        let mut w = World::new();
        let lib = w.other_module("core/option", &[]);
        let members = w.extend_block(
            lib,
            &[("T", &[])],
            &|tcx: &enrang_hir::Tcx, ps: &[Ty]| tcx.mk_nullable(ps[0]),
            &["unwrapOr"],
        );
        let seeing = w.other_module("src/a", &[lib]);
        let blind = w.other_module("src/b", &[]);
        let t = &w.tcx;
        let opt = t.mk_nullable(t.common().i64);
        let found = t
            .member(opt, intern("unwrapOr"), seeing)
            .expect("in the closure");
        assert_eq!(methods(&found), members);
        assert_eq!(&*t.list(found.args), &[t.common().i64]);
        assert!(t.member(opt, intern("unwrapOr"), blind).is_none());
        assert!(
            t.member(t.common().i64, intern("unwrapOr"), seeing)
                .is_none()
        );
        assert!(
            t.member(opt, intern("unwrapOr"), lib).is_some(),
            "a module sees its own blocks"
        );
    });
    h.case(
        "member/sealed patterns follow the implementer table",
        || {
            let mut w = World::new();
            let (int, _) = w.interface("__Int", &[], Some(LangItem::Int));
            w.lang(LangItem::Int, int);
            let (bits, _) = w.interface("AtomicBits", &[], Some(LangItem::AtomicBits));
            w.lang(LangItem::AtomicBits, bits);
            let module = w.module;
            w.extend_block(
                module,
                &[("I", &[int])],
                &|_: &enrang_hir::Tcx, ps: &[Ty]| ps[0],
                &["wrappingAdd"],
            );
            w.extend_block(
                module,
                &[("B", &[bits])],
                &|_: &enrang_hir::Tcx, ps: &[Ty]| ps[0],
                &["testAndSet"],
            );
            let (bounded, p) = w.bounded_param("N", &[int]);
            let _ = bounded;
            let t = &w.tcx;
            let name = intern("wrappingAdd");
            for int in [t.common().i8, t.common().u64, t.common().usize] {
                assert!(
                    t.member(int, name, module).is_some(),
                    "{}",
                    t.ty_string(int)
                );
            }
            for other in [
                t.common().f64,
                t.common().bool,
                t.common().str,
                t.mk_nullable(t.common().i64),
            ] {
                assert!(
                    t.member(other, name, module).is_none(),
                    "{}",
                    t.ty_string(other)
                );
            }
            assert!(
                t.member(p, name, module).is_some(),
                "`N extends __Int` meets `__Int`"
            );
            let set = intern("testAndSet");
            assert!(t.member(t.common().u32, set, module).is_some());
            assert!(
                t.member(t.common().u8, set, module).is_none(),
                "`bts` has no byte form (S:1593)"
            );
            assert!(t.member(t.common().bool, set, module).is_none());
        },
    );
    h.case(
        "member/VolatileValue takes 64-bit integers on x86_64 only",
        || {
            for (target, wide) in [("x86_64-linux", true), ("i386-linux", false)] {
                let w = World::for_target(target);
                let t = &w.tcx;
                for ty in [
                    t.common().u8,
                    t.common().usize,
                    t.common().bool,
                    t.mk_raw(t.common().u8),
                ] {
                    assert!(
                        t.sealed_implements(LangItem::VolatileValue, ty),
                        "{target} {}",
                        t.ty_string(ty)
                    );
                }
                assert_eq!(
                    t.sealed_implements(LangItem::VolatileValue, t.common().u64),
                    wide,
                    "{target}"
                );
                assert!(!t.sealed_implements(LangItem::VolatileValue, t.common().f64));
                assert!(t.sealed_implements(LangItem::AtomicValue, t.common().i32));
                assert!(!t.sealed_implements(LangItem::AtomicValue, t.common().i64));
            }
        },
    );
    h.case(
        "member/T[] and T[N] reach Slice<T>'s members through C18",
        || {
            let mut w = World::new();
            let (slice, sps) = w.class("Slice", ClassModifier::Final, &["T"]);
            w.lang(LangItem::Slice, slice);
            let len = w.tcx.common().isize;
            let length = w.method(slice, "length", &[], len, Vis::Public);
            let _ = sps;
            let (array, _) = w.class("Array", ClassModifier::Final, &["T"]);
            w.lang(LangItem::Array, array);
            let void = w.tcx.common().void;
            let push = w.method(array, "push", &[], void, Vis::Public);
            let t = &w.tcx;
            let u8 = t.common().u8;
            let found = t
                .member(t.mk_array(u8), intern("push"), w.module)
                .expect("push");
            assert_eq!(methods(&found), [push]);
            assert_eq!(found.via_slice, None);
            let found = t
                .member(t.mk_array(u8), intern("length"), w.module)
                .expect("length");
            assert_eq!(methods(&found), [length]);
            assert_eq!(found.via_slice, Some(Adjust::ArrayToSlice));
            assert_eq!(&*t.list(found.args), &[u8]);
            let found = t
                .member(t.mk_fixed(u8, 4), intern("length"), w.module)
                .expect("length");
            assert_eq!(found.via_slice, Some(Adjust::FixedToSlice));
            assert!(
                t.member(t.mk_fixed(u8, 4), intern("push"), w.module)
                    .is_none()
            );
            assert!(
                t.member(t.mk_slice(u8), intern("push"), w.module).is_none(),
                "`Slice` has no `push`"
            );
        },
    );
    h.case("member/string reaches its lang class", || {
        let mut w = World::new();
        let (string, _) = w.class("string", ClassModifier::Final, &[]);
        w.lang(LangItem::Str, string);
        let isize = w.tcx.common().isize;
        let length = w.method(string, "length", &[], isize, Vis::Public);
        let t = &w.tcx;
        let found = t
            .member(t.common().str, intern("length"), w.module)
            .expect("length");
        assert_eq!(methods(&found), [length]);
        assert_eq!(
            t.lang_class_of(t.common().str).map(|(a, _)| a),
            Some(string)
        );
    });
    h.case(
        "member/a bounded parameter sees its bounds' members",
        || {
            let mut w = World::new();
            let (speaker, _) = w.interface("Speaker", &[], None);
            let str = w.tcx.common().str;
            let speak = w.method(speaker, "speak", &[], str, Vis::Public);
            let (animal, _) = w.class("Animal", ClassModifier::Plain, &[]);
            w.field(animal, "name", str, Vis::Public);
            w.field(animal, "sound", str, Vis::Protected);
            let walk = w.method(animal, "walk", &[], str, Vis::Public);
            w.method(animal, "rest", &[], str, Vis::Protected);
            let (p, t_ty) = w.bounded_param("T", &[speaker]);
            let _ = p;
            let (q, a_ty) = w.bounded_param("A", &[]);
            w.bound(q, animal, true);
            let t = &w.tcx;
            let found = t.member(t_ty, intern("speak"), w.module).expect("speak");
            assert_eq!(methods(&found), [speak]);
            assert!(matches!(
                t.member(a_ty, intern("name"), w.module).map(|m| m.kind),
                Some(MemberKind::Field { .. })
            ));
            assert!(
                t.member(a_ty, intern("sound"), w.module).is_none(),
                "protected: the function is no subclass"
            );
            assert_eq!(
                methods(&t.member(a_ty, intern("walk"), w.module).expect("walk")),
                [walk]
            );
            assert!(t.member(a_ty, intern("rest"), w.module).is_none());
            assert!(matches!(t.kind(a_ty), TyKind::Param(_)));
        },
    );
    h.case("member/a destructor is never a member", || {
        let mut w = World::new();
        let (region, _) = w.class("Region", ClassModifier::Final, &[]);
        w.dtor(region);
        let t = &w.tcx;
        let region = t.mk_adt(region, &[]);
        assert!(t.member(region, intern("destructor"), w.module).is_none());
        assert!(t.member(region, intern("#dtor"), w.module).is_none());
    });
}
