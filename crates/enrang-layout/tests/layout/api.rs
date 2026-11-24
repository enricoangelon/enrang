//! The API of ARCHITECTURE 3 and plan a.2: `layout_of`, `LayoutCx` and its cache,
//! `LayoutError::ty`, and layouts that do not depend on the order in which types
//! were defined or interned (ARCHITECTURE 1).

use std::sync::Arc;

use enrang_layout::{LayoutCx, LayoutError, layout_of};
use enrang_testkit::Harness;

use crate::support::{TARGETS, World};

const DECLARATIONS: [&str; 4] = [
    "public final class Point { public x: i32; public y: i32; }",
    "public class Animal { public name: string; public legs: u8; }",
    "public final class Dog extends Animal { public good: bool; }",
    "public enum Token { Num { value: i64 }, Add, Bad { text: string } }",
];

const TYPES: [&str; 8] = [
    "Point",
    "Animal",
    "Dog",
    "Token",
    "{ p: Point, t: Token | null }",
    "[Dog, u8, Point[3]]",
    "Box<Animal> | null",
    "Token[2]",
];

pub fn register(h: &mut Harness) {
    for target in TARGETS {
        h.case(
            format!("api/layout_of and LayoutCx agree on {target}"),
            move || {
                let mut w = World::new(target);
                for declaration in DECLARATIONS {
                    w.declare(declaration);
                }
                let tys: Vec<_> = TYPES.iter().map(|t| w.ty(t)).collect();
                let mut cx = LayoutCx::new(&w.tcx);
                for &ty in &tys {
                    let first = cx.layout_of(ty).expect("a layout");
                    let again = cx.layout_of(ty).expect("a layout");
                    assert!(Arc::ptr_eq(&first, &again), "computed once");
                    assert_eq!(*first, *layout_of(&w.tcx, ty).expect("a layout"));
                    assert_eq!(cx.size_of(ty), Ok(first.size));
                    assert_eq!(cx.align_of(ty), Ok(first.align));
                }
                for &ty in &tys {
                    let first = layout_of(&w.tcx, ty).expect("a layout");
                    let again = layout_of(&w.tcx, ty).expect("a layout");
                    assert!(Arc::ptr_eq(&first, &again), "memoised in the Tcx (A:762)");
                    assert!(w.tcx.layout_memo(ty).is_some());
                }
                assert_eq!(cx.ptr(), w.p());
                assert_eq!(cx.data_layout(), w.tcx.target().layout);
                assert!(std::ptr::eq(cx.tcx(), &w.tcx));
            },
        );

        h.case(
            format!("api/errors are kept and name their type on {target}"),
            move || {
                let mut w = World::new(target);
                let node = w.declare("public final class Node { public next: Node | null; }");
                let nullable = w.ty("Node | null");
                let mut cx = LayoutCx::new(&w.tcx);
                assert_eq!(cx.layout_of(node), Err(LayoutError::Recursive { ty: node }));
                // Reached from inside, `Node | null` held the same error.
                assert_eq!(
                    cx.layout_of(nullable),
                    Err(LayoutError::Recursive { ty: node })
                );
                assert_eq!(cx.size_of(node), Err(LayoutError::Recursive { ty: node }));
                assert_eq!(
                    cx.offset_of(node, "next"),
                    Err(LayoutError::Recursive { ty: node })
                );
                let t = w.param("T");
                let s = w.ty("&string");
                let slice = w.ty("Slice<u8>");
                let big = w.ty("u8[9223372036854775807][2]");
                let error = w.tcx.common().error;
                for e in [
                    LayoutError::TooLarge { ty: big },
                    LayoutError::DependsOnContracts { ty: s },
                    LayoutError::Generic { ty: t },
                    LayoutError::Unsized { ty: slice },
                    LayoutError::Recursive { ty: node },
                    LayoutError::ErrorType { ty: error },
                ] {
                    let ty = e.ty();
                    assert!(matches!(e, LayoutError::TooLarge { ty: x }
                    | LayoutError::DependsOnContracts { ty: x }
                    | LayoutError::Generic { ty: x }
                    | LayoutError::Unsized { ty: x }
                    | LayoutError::Recursive { ty: x }
                    | LayoutError::ErrorType { ty: x } if x == ty));
                }
            },
        );

        h.case(
            format!("api/layouts do not depend on definition order on {target}"),
            move || {
                let mut forward = World::new(target);
                for declaration in DECLARATIONS {
                    forward.declare(declaration);
                }
                let mut backward = World::new(target);
                // Intern other types first, so every id differs.
                for spelling in ["u8[7]", "{ zz: f64 }", "[bool, bool]", "string | null"] {
                    backward.ty(spelling);
                }
                for declaration in [
                    DECLARATIONS[3],
                    DECLARATIONS[0],
                    DECLARATIONS[1],
                    DECLARATIONS[2],
                ] {
                    backward.declare(declaration);
                }
                for spelling in TYPES.iter().rev() {
                    let b = backward.ty(spelling);
                    let f = forward.ty(spelling);
                    assert_eq!(forward.ok(f), backward.ok(b), "{spelling}");
                }
            },
        );

        h.case(
            format!("api/a layout is a value, not an id order on {target}"),
            move || {
                // Equal structures are one interned type, so one layout; two classes with
                // the same fields are two types with equal layouts.
                let mut w = World::new(target);
                let a = w.declare("public final class A { public x: u8; public y: i64; }");
                let b = w.declare("public final class B { public x: u8; public y: i64; }");
                assert_ne!(a, b);
                assert_eq!(w.ok(a), w.ok(b));
                let one = w.ty("{ y: i64, x: u8 }");
                let two = w.ty("{ x: u8, y: i64 }");
                assert_eq!(one, two);
            },
        );
    }
}
