//! References, pointers, boxes and closures beside the table, and the types with no
//! layout: what follows contracts (a `&string`, a borrowing class or tuple), what
//! follows mono (a type parameter where its layout matters), what is never a value
//! by itself (a view, an interface), what holds itself, and `Error`.

use enrang_hir::{Attrs, ClassModifier, InferVar, TyKind};
use enrang_layout::{LayoutCx, LayoutError, TagLayout};
use enrang_testkit::Harness;

use crate::support::{TARGETS, World};

fn world(target: &str) -> World {
    let mut w = World::new(target);
    for declaration in [
        "public final class Point { public x: i32; public y: i32; }",
        "public interface Speaker { }",
        "public final class Lexer { private src: &string; }",
        "public final class Sink { private out: &i64[]; }",
        "public final class Parser { private lx: Lexer; }",
        "public final class Stack<T> { public items: T[]; public top: T; }",
    ] {
        w.declare(declaration);
    }
    w
}

pub fn register(h: &mut Harness) {
    for target in TARGETS {
        h.case(
            format!("forms/a &string waits for contracts on {target}"),
            move || {
                let mut w = world(target);
                let s = w.ty("&string");
                assert_eq!(w.layout(s), Err(LayoutError::DependsOnContracts { ty: s }));
                // A nullable one, or one inside a tuple, too.
                let nullable = w.ty("&string | null");
                assert_eq!(
                    w.layout(nullable),
                    Err(LayoutError::DependsOnContracts { ty: s })
                );
                let tuple = w.ty("[&string, i32]");
                assert_eq!(
                    w.layout(tuple),
                    Err(LayoutError::DependsOnContracts { ty: tuple })
                );
                // A pointer to a whole nullable string is one pointer; a string by value
                // and a raw pointer to one have their own layouts.
                let p = w.p();
                for spelling in ["&(string | null)", "*string", "&string[]", "Box<string>"] {
                    let ty = w.ty(spelling);
                    assert_eq!(w.size_align(ty), (p, p as u32), "{spelling}");
                }
            },
        );

        h.case(
            format!("forms/a borrowing class waits for contracts on {target}"),
            move || {
                let mut w = world(target);
                for name in ["Lexer", "Sink", "Parser"] {
                    let ty = w.named(name);
                    assert_eq!(
                        w.layout(ty),
                        Err(LayoutError::DependsOnContracts { ty }),
                        "{name}"
                    );
                    assert_eq!(
                        LayoutCx::new(&w.tcx).offset_of(ty, "src"),
                        Err(LayoutError::DependsOnContracts { ty })
                    );
                }
                let lexer = w.named("Lexer");
                let nullable = w.ty("Lexer | null");
                assert_eq!(
                    w.layout(nullable),
                    Err(LayoutError::DependsOnContracts { ty: lexer })
                );
                // A reference to one is one pointer.
                let p = w.p();
                let r = w.ty("&Lexer");
                assert_eq!(w.size_align(r), (p, p as u32));
            },
        );

        h.case(
            format!("forms/a borrowing tuple waits for contracts on {target}"),
            move || {
                let mut w = world(target);
                for spelling in [
                    "[&i64, i32]",
                    "[&i64[], i32]",
                    "[Lexer, u8]",
                    "[&Speaker, bool]",
                ] {
                    let ty = w.ty(spelling);
                    assert_eq!(
                        w.layout(ty),
                        Err(LayoutError::DependsOnContracts { ty }),
                        "{spelling}"
                    );
                }
            },
        );

        h.case(
            format!("forms/a type parameter waits for mono on {target}"),
            move || {
                let mut w = world(target);
                let p = w.p();
                let t = w.param("T");
                let r = w.tcx.mk_ref(t);
                let fixed = w.tcx.mk_fixed(t, 4);
                let pair = w.tcx.mk_tuple(&[t, w.tcx.common().i32]);
                let nullable = w.tcx.mk_nullable(t);
                let stack = w.named("Stack");
                let TyKind::Adt(_, own) = w.tcx.kind(stack) else {
                    panic!("a class");
                };
                let own = w.tcx.list(own)[0];
                for (ty, about) in [
                    (t, t),
                    (r, r),
                    (fixed, t),
                    (pair, t),
                    (nullable, t),
                    (stack, own),
                ] {
                    assert_eq!(
                        w.layout(ty),
                        Err(LayoutError::Generic { ty: about }),
                        "{}",
                        w.tcx.ty_string(ty)
                    );
                }
                // Where its layout does not matter, a parameter is no obstacle: a box
                // never holds an interface through one (ARCHITECTURE 2.4).
                let boxed = w.tcx.mk_box(t);
                let raw = w.tcx.mk_raw(t);
                let array = w.tcx.mk_array(t);
                assert_eq!(w.size_align(boxed), (p, p as u32));
                assert_eq!(w.size_align(raw), (p, p as u32));
                assert_eq!(w.size_align(array), (3 * p, p as u32));
                // An instance has a layout: `Stack<i64>` is `{ items: i64[], top: i64 }`.
                let instance = w.ty("Stack<i64>");
                let i64_align = w.tcx.target().layout.i64_align;
                assert_eq!(w.ok(instance).fields, [0, 3 * p]);
                assert_eq!(w.size_align(instance), (3 * p + 8, i64_align.max(p as u32)));
            },
        );

        h.case(
            format!("forms/an inference variable has no layout on {target}"),
            move || {
                let w = world(target);
                let var = w.tcx.intern_ty(TyKind::Infer(InferVar(0)));
                assert_eq!(w.layout(var), Err(LayoutError::Generic { ty: var }));
                let r = w.tcx.mk_ref(var);
                assert_eq!(w.layout(r), Err(LayoutError::Generic { ty: r }));
                let b = w.tcx.mk_box(var);
                assert_eq!(w.layout(b), Err(LayoutError::Generic { ty: b }));
            },
        );

        h.case(
            format!("forms/a view and an interface are never values on {target}"),
            move || {
                let mut w = world(target);
                for spelling in [
                    "Slice<u8>",
                    "Speaker",
                    "Speaker | null",
                    "[Speaker, u8]",
                    "Speaker[2]",
                ] {
                    let ty = w.ty(spelling);
                    let about = if spelling.starts_with("Slice") {
                        ty
                    } else {
                        w.named("Speaker")
                    };
                    assert_eq!(
                        w.layout(ty),
                        Err(LayoutError::Unsized { ty: about }),
                        "{spelling}"
                    );
                }
            },
        );

        h.case(
            format!("forms/Error has no layout on {target}"),
            move || {
                let w = world(target);
                let error = w.tcx.common().error;
                let p = w.p();
                assert_eq!(w.layout(error), Err(LayoutError::ErrorType { ty: error }));
                for ty in [
                    w.tcx.mk_ref(error),
                    w.tcx.mk_box(error),
                    w.tcx.mk_nullable(error),
                    w.tcx.mk_fixed(error, 2),
                ] {
                    assert_eq!(w.layout(ty), Err(LayoutError::ErrorType { ty: error }));
                }
                // An array of it is still a descriptor, which never looks at its element.
                let array = w.tcx.mk_array(error);
                assert_eq!(w.size_align(array), (3 * p, p as u32));
            },
        );

        h.case(
            format!("forms/a type that holds itself on {target}"),
            move || {
                let mut w = world(target);
                let p = w.p();
                let node = w.declare(
                    "public final class Node { public value: i64; public next: Node | null; }",
                );
                assert_eq!(w.layout(node), Err(LayoutError::Recursive { ty: node }));
                let tree = w.declare("public enum Tree { Leaf, Fork { left: Tree, right: u8 } }");
                assert_eq!(w.layout(tree), Err(LayoutError::Recursive { ty: tree }));
                // Two classes that hold each other, one through a fixed array.
                let (a_adt, _) = w.class("A", ClassModifier::Final, Attrs::default(), &[]);
                let (b_adt, _) = w.class("B", ClassModifier::Final, Attrs::default(), &[]);
                let (a, b) = (w.named("A"), w.named("B"));
                w.field(a_adt, "b", b);
                let one_a = w.tcx.mk_fixed(a, 1);
                w.field(b_adt, "a", one_a);
                assert_eq!(w.layout(a), Err(LayoutError::Recursive { ty: a }));
                assert_eq!(w.layout(b), Err(LayoutError::Recursive { ty: b }));
                // Through a box, a list is fine: a tagged one-word pointer.
                let list = w.declare("public final class List { public next: Box<List> | null; }");
                assert_eq!(w.size_align(list), (2 * p, p as u32));
            },
        );

        h.case(
            format!("forms/closures, function and raw pointers on {target}"),
            move || {
                let mut w = world(target);
                let p = w.p();
                let c = *w.tcx.common();
                let closure = w.closure(&[c.i64], c.void);
                let layout = w.ok(closure);
                assert_eq!((layout.size, layout.align), (2 * p, p as u32));
                assert_eq!(layout.fields, [0, p], "code, then environment");
                // `T | null` has no niche: a closure parameter that may be null is tagged.
                let nullable = w.tcx.mk_nullable(closure);
                assert_eq!(w.size_align(nullable), (3 * p, p as u32));
                for spelling in ["(fn(i64) => void) | null", "*u8 | null"] {
                    let ty = w.ty(spelling);
                    assert_eq!(w.size_align(ty), (2 * p, p as u32), "{spelling}");
                }
            },
        );

        h.case(
            format!("forms/an &I may be null in its own word on {target}"),
            move || {
                let mut w = world(target);
                let p = w.p();
                let ty = w.ty("&Speaker | null");
                let layout = w.ok(ty);
                assert_eq!((layout.size, layout.align), (2 * p, p as u32));
                let variants = layout.variants.as_ref().expect("two cases");
                assert_eq!(variants.tag, TagLayout::NullWord);
                assert_eq!(variants.payload, 0);
                assert_eq!(variants.variants[0].fields, Vec::<u64>::new());
                assert_eq!(variants.variants[1].fields, [0]);
                assert_eq!(variants.variants[1].size, 2 * p);
                // The exception is `&I` alone: a box of one, or a nullable view, is tagged.
                let boxed = w.ty("Box<Speaker> | null");
                assert_eq!(w.size_align(boxed), (3 * p, p as u32));
                let view = w.ty("&Slice<u8> | null");
                assert_eq!(w.size_align(view), (3 * p, p as u32));
                let tagged = w.ok(view);
                let variants = tagged.variants.as_ref().expect("two cases");
                assert_eq!(variants.tag, TagLayout::Direct { size: 4 });
                assert_eq!(variants.payload, p);
            },
        );
    }
}
