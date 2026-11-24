//! `Tcx::ty_string`: types as SPEC writes them, with the parentheses SPEC 4.1's
//! reading rules need (`&T[]` is `&(T[])`, `&T | null` is `(&T) | null`).

use enrang_base::intern;
use enrang_hir::{Abi, ClassModifier, FnPtrSig, LangItem, Mark, Shape};
use enrang_testkit::Harness;

use crate::support::{F, World};

/// A row: the spelling, and how to make the type.
type Row = (&'static str, fn(&mut World) -> enrang_hir::Ty);

pub fn register(h: &mut Harness) {
    let rows: &[Row] = &[
        ("i64", |w| w.tcx.common().i64),
        ("int", |w| w.tcx.common().i32),
        ("u8", |w| w.tcx.common().u8),
        ("usize", |w| w.tcx.common().usize),
        ("f64", |w| w.tcx.common().f64),
        ("bool", |w| w.tcx.common().bool),
        ("void", |w| w.tcx.common().void),
        ("never", |w| w.tcx.common().never),
        ("string", |w| w.tcx.common().str),
        ("&i64", |w| w.tcx.mk_ref(w.tcx.common().i64)),
        ("&i64[]", |w| {
            w.tcx.mk_ref(w.tcx.mk_array(w.tcx.common().i64))
        }),
        ("(&i64)[]", |w| {
            w.tcx.mk_array(w.tcx.mk_ref(w.tcx.common().i64))
        }),
        ("i64 | null", |w| w.tcx.mk_nullable(w.tcx.common().i64)),
        ("&i64 | null", |w| {
            w.tcx.mk_nullable(w.tcx.mk_ref(w.tcx.common().i64))
        }),
        ("&(i64 | null)", |w| {
            w.tcx.mk_ref(w.tcx.mk_nullable(w.tcx.common().i64))
        }),
        ("(i64 | null) | null", |w| {
            w.tcx.mk_nullable(w.tcx.mk_nullable(w.tcx.common().i64))
        }),
        ("(&i64 | null) | null", |w| {
            w.tcx
                .mk_nullable(w.tcx.mk_nullable(w.tcx.mk_ref(w.tcx.common().i64)))
        }),
        ("(i64 | null)[]", |w| {
            w.tcx.mk_array(w.tcx.mk_nullable(w.tcx.common().i64))
        }),
        ("i64[] | null", |w| {
            w.tcx.mk_nullable(w.tcx.mk_array(w.tcx.common().i64))
        }),
        ("int[2]", |w| w.tcx.mk_fixed(w.tcx.common().i32, 2)),
        ("int[3][4]", |w| {
            w.tcx.mk_fixed(w.tcx.mk_fixed(w.tcx.common().i32, 3), 4)
        }),
        ("*u8", |w| w.tcx.mk_raw(w.tcx.common().u8)),
        ("[int, string]", |w| {
            w.tcx.mk_tuple(&[w.tcx.common().i32, w.tcx.common().str])
        }),
        ("[&i64[], int]", |w| {
            let r = w.tcx.mk_ref(w.tcx.mk_array(w.tcx.common().i64));
            w.tcx.mk_tuple(&[r, w.tcx.common().i32])
        }),
        ("{ age: int, name: string }", |w| {
            w.tcx.mk_object(vec![
                (intern("name"), w.tcx.common().str),
                (intern("age"), w.tcx.common().i32),
            ])
        }),
        ("{}", |w| w.tcx.mk_object(Vec::new())),
        ("{ name: string, nick?: string | null }", |w| {
            let nick = w.tcx.mk_nullable(w.tcx.common().str);
            w.tcx.mk_object_shape(Shape::with_optional(
                vec![(intern("nick"), nick), (intern("name"), w.tcx.common().str)],
                vec![intern("nick")],
            ))
        }),
        ("{ v?: (i64 | null) | null }", |w| {
            let v = w.tcx.mk_nullable(w.tcx.mk_nullable(w.tcx.common().i64));
            w.tcx.mk_object_shape(Shape::with_optional(
                vec![(intern("v"), v)],
                vec![intern("v")],
            ))
        }),
        ("Slice<u8>", |w| w.tcx.mk_slice(w.tcx.common().u8)),
        ("&Slice<u8>", |w| {
            w.tcx.mk_ref(w.tcx.mk_slice(w.tcx.common().u8))
        }),
        ("Box<Animal>", |w| {
            let (animal, _) = w.class("Animal", ClassModifier::Plain, &[]);
            w.tcx.mk_box(w.tcx.mk_adt(animal, &[]))
        }),
        ("Stack<i64>", |w| {
            let (stack, _) = w.class("Stack", ClassModifier::Plain, &["T"]);
            w.tcx.mk_adt(stack, &[w.tcx.common().i64])
        }),
        ("T", |w| w.bounded_param("T", &[]).1),
        ("&T[]", |w| {
            let t = w.bounded_param("T", &[]).1;
            w.tcx.mk_ref(w.tcx.mk_array(t))
        }),
        ("fn(&i64) => void", |w| {
            let r = w.tcx.mk_ref(w.tcx.common().i64);
            w.tcx
                .mk_fn_ptr(Abi::Enrang, FnPtrSig::new(&[r], w.tcx.common().void))
        }),
        ("fn(let &Slice<u8>) => usize", |w| {
            let r = w.tcx.mk_ref(w.tcx.mk_slice(w.tcx.common().u8));
            let mut sig = FnPtrSig::new(&[r], w.tcx.common().usize);
            sig.params[0].1 = Mark::Let;
            w.tcx.mk_fn_ptr(Abi::Enrang, sig)
        }),
        ("fn(&Slice<i64>) => readonly &i64", |w| {
            let r = w.tcx.mk_ref(w.tcx.mk_slice(w.tcx.common().i64));
            let mut sig = FnPtrSig::new(&[r], w.tcx.mk_ref(w.tcx.common().i64));
            sig.ret_readonly = true;
            w.tcx.mk_fn_ptr(Abi::Enrang, sig)
        }),
        ("unsafe fn() => void", |w| {
            let mut sig = FnPtrSig::new(&[], w.tcx.common().void);
            sig.unsafety = true;
            w.tcx.mk_fn_ptr(Abi::Enrang, sig)
        }),
        ("@abi(\"win64\") fn(u32) => u32", |w| {
            let u32 = w.tcx.common().u32;
            w.tcx.mk_fn_ptr(Abi::Win64, FnPtrSig::new(&[u32], u32))
        }),
        ("(u8) => void", |w| {
            let sig = FnPtrSig::new(&[w.tcx.common().u8], w.tcx.common().void);
            w.tcx.mk_closure(sig)
        }),
        ("((u8) => void) | null", |w| {
            let sig = FnPtrSig::new(&[w.tcx.common().u8], w.tcx.common().void);
            w.tcx.mk_nullable(w.tcx.mk_closure(sig))
        }),
        ("(fn() => void)[]", |w| {
            let f = w
                .tcx
                .mk_fn_ptr(Abi::Enrang, FnPtrSig::new(&[], w.tcx.common().void));
            w.tcx.mk_array(f)
        }),
        ("Result<void>", |w| {
            let (result, failure) = result_and_failure(w);
            let failure = w.tcx.mk_adt(failure, &[]);
            w.tcx.mk_adt(result, &[w.tcx.common().void, failure])
        }),
        ("Result<i64, ParseError>", |w| {
            let (result, _) = result_and_failure(w);
            let (error, _) = w.enumeration("ParseError", &[], &[("Empty", &[])]);
            let error = w.tcx.mk_adt(error, &[]);
            w.tcx.mk_adt(result, &[w.tcx.common().i64, error])
        }),
        ("_", |w| w.tcx.common().error),
    ];
    for (expected, make) in rows {
        let (expected, make) = (*expected, *make);
        h.case(format!("display/{expected}"), move || {
            let mut w = World::new();
            let ty = make(&mut w);
            assert_eq!(w.tcx.ty_string(ty), expected);
        });
    }
    h.case(
        "display/a function type with the names its declaration kept (D14)",
        || {
            let w = World::new();
            let t = &w.tcx;
            let s = t.mk_ref(t.common().str);
            let mut sig = FnPtrSig::new(&[s, t.common().i64], t.common().void);
            sig.params[0].1 = Mark::Let;
            let f = t.mk_fn_ptr(Abi::Enrang, sig.clone());
            let names = [intern("s"), intern("n")];
            assert_eq!(
                t.fn_ty_string(f, Some(&names)),
                "fn(let s: &string, n: i64) => void"
            );
            assert_eq!(t.fn_ty_string(f, None), "fn(let &string, i64) => void");
            assert_eq!(
                t.fn_ty_string(f, Some(&names[..1])),
                "fn(let &string, i64) => void",
                "a list of the wrong length is ignored"
            );
            let nullable = t.mk_nullable(t.mk_closure(sig));
            assert_eq!(
                t.fn_ty_string(nullable, Some(&names)),
                "((let s: &string, n: i64) => void) | null"
            );
            let inner = t.mk_array(f);
            assert_eq!(
                t.fn_ty_string(inner, Some(&names)),
                "(fn(let &string, i64) => void)[]",
                "names belong to the type at the top only"
            );
        },
    );
    h.case(
        "display/an overload's path spells classes by their own paths",
        || {
            let mut w = World::new();
            let (main_node, _) = w.class("Node", ClassModifier::Plain, &[]);
            let other = w.other_module("src/b", &[]);
            let saved = w.module;
            w.module = other;
            let (b_node, _) = w.class("Node", ClassModifier::Plain, &[]);
            let (speaker, _) = w.interface("Speaker", &[], None);
            w.module = saved;
            let main_ref = w.tcx.mk_ref(w.tcx.mk_adt(main_node, &[]));
            let b_ref = w.tcx.mk_ref(w.tcx.mk_adt(b_node, &[]));
            assert_eq!(w.tcx.ty_string(main_ref), w.tcx.ty_string(b_ref));
            assert_eq!(w.tcx.ty_path_string(main_ref), "&src/main::Node");
            assert_eq!(w.tcx.ty_path_string(b_ref), "&src/b::Node");
            // An implicit parameter is spelled by the interface it stands for.
            let (p, ty) = w.bounded_param("Speaker", &[speaker]);
            w.tcx.param_mut(p).implicit = Some(enrang_hir::Implicit::Interface(speaker));
            assert_eq!(w.tcx.ty_string(ty), "Speaker");
            assert_eq!(w.tcx.ty_path_string(ty), "src/b::Speaker");
            let self_param = w
                .tcx
                .adt(speaker)
                .as_interface()
                .expect("an interface")
                .self_param;
            assert_eq!(w.tcx.ty_path_string(w.tcx.mk_param(self_param)), "Self");
            let (result, failure) = result_and_failure(&mut w);
            let failure = w.tcx.mk_adt(failure, &[]);
            let res = w.tcx.mk_adt(result, &[w.tcx.common().i32, failure]);
            assert_eq!(w.tcx.ty_string(res), "Result<int>");
            assert_eq!(
                w.tcx.ty_path_string(res),
                "src/main::Result<int, src/main::Failure>"
            );
        },
    );
}

/// The lang `Result<T, E>` enum and the `Failure` class.
fn result_and_failure(w: &mut World) -> (enrang_hir::AdtId, enrang_hir::AdtId) {
    let (result, _) = w.enumeration(
        "Result",
        &["T", "E"],
        &[
            ("Ok", &[("value", F::P(0))]),
            ("Err", &[("error", F::P(1))]),
        ],
    );
    w.lang(LangItem::Result, result);
    let (failure, _) = w.class("Failure", ClassModifier::Final, &[]);
    w.lang(LangItem::Failure, failure);
    (result, failure)
}
