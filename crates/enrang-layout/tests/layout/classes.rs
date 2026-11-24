//! Classes (S:1640, SPEC 7.6, ARCHITECTURE 7.7): declaration order, padding, the
//! hidden method-table pointer of a class that can be extended, subclasses after
//! their base, generic classes and bases at their arguments, and the layout
//! decorators.

use enrang_hir::{Attrs, ClassModifier};
use enrang_layout::LayoutCx;
use enrang_testkit::Harness;

use crate::support::{TARGETS, World};

pub fn register(h: &mut Harness) {
    for target in TARGETS {
        h.case(format!("classes/fields in declaration order on {target}"), move || {
            let mut w = World::new(target);
            let p = w.p();
            let player = w.declare(
                "public final class Player { public name: string; public score: i64; public level: i32; }",
            );
            assert_eq!(w.ok(player).fields, [0, 3 * p, 3 * p + 8]);
            // No reordering: a small field first leaves padding before a large one.
            let padded = w.declare("public final class Padded { public a: u8; public b: u32; public c: u8; }");
            assert_eq!(w.ok(padded).fields, [0, 4, 8]);
            assert_eq!(w.size_align(padded), (12, 4));
            let wide = w.declare("public final class Wide { public a: u8; public b: f64; }");
            let f64_align = u64::from(w.tcx.target().layout.f64_align);
            assert_eq!(w.ok(wide).fields, [0, f64_align]);
            assert_eq!(w.size_align(wide).0, f64_align + 8);
        });

        h.case(format!("classes/an empty class on {target}"), move || {
            let mut w = World::new(target);
            let p = w.p();
            let empty = w.declare("public final class Empty { }");
            assert_eq!(w.size_align(empty), (0, 1));
            // A class that can be extended still carries its table pointer.
            let open = w.declare("public class Open { }");
            assert_eq!(w.size_align(open), (p, p as u32));
            let zero = w.declare("public final class Zero { public a: void; public b: u8[0]; }");
            assert_eq!(w.size_align(zero), (0, 1));
            assert_eq!(w.ok(zero).fields, [0, 0]);
        });

        h.case(
            format!("classes/the hidden table pointer comes first on {target}"),
            move || {
                let mut w = World::new(target);
                let p = w.p();
                let animal =
                    w.declare("public class Animal { public name: string; public legs: u8; }");
                assert_eq!(w.ok(animal).fields, [p, 4 * p]);
                assert_eq!(w.size_align(animal), (5 * p, p as u32));
                let shape = w.declare("public abstract class Shape { public id: u8; }");
                assert_eq!(w.ok(shape).fields, [p]);
                assert_eq!(w.size_align(shape), (2 * p, p as u32));
            },
        );

        h.case(
            format!("classes/a subclass keeps its base's offsets on {target}"),
            move || {
                let mut w = World::new(target);
                let p = w.p();
                let a = w.declare("public class A { public a: i64; public b: u8; }");
                let d = w.declare("public class D extends A { public c: u8; }");
                let e =
                    w.declare("public final class E extends D { public e: u16; public f: i64; }");
                let (la, ld, le) = (w.ok(a), w.ok(d), w.ok(e));
                assert_eq!(ld.fields[..2], la.fields[..]);
                assert_eq!(le.fields[..3], ld.fields[..]);
                // `e` starts at D's whole size, padding included.
                assert_eq!(le.fields[3], ld.size);
                let i64_align = u64::from(w.tcx.target().layout.i64_align);
                assert_eq!(le.fields[4], (ld.size + 2).next_multiple_of(i64_align));
                assert_eq!(le.size % u64::from(le.align), 0);
                // A `final` subclass keeps the pointer too: nothing sits at offset 0.
                assert!(le.fields.iter().all(|&at| at >= p));
                assert_eq!(w.offset(e, "a"), la.fields[0]);
                assert_eq!(w.offset(e, "f"), le.fields[4]);
            },
        );

        h.case(
            format!("classes/a subclass never fills its base's tail on {target}"),
            move || {
                let mut w = World::new(target);
                let p = w.p();
                let base = w.declare("public class Base { public x: i32; public y: u8; }");
                let sub = w.declare("public class Sub extends Base { public z: u8; }");
                // Base: pointer, x at P, y at P + 4; its size rounds up to P.
                let base_size = (p + 5).next_multiple_of(p);
                assert_eq!(w.size_align(base), (base_size, p as u32));
                assert_eq!(w.offset(sub, "z"), base_size);
                assert_eq!(w.size_align(sub).0, (base_size + 1).next_multiple_of(p));
            },
        );

        h.case(
            format!("classes/a generic class at its arguments on {target}"),
            move || {
                let mut w = World::new(target);
                let p = w.p();
                w.declare("public final class Pair<T> { public a: T; public b: u8; }");
                let i64_align = u64::from(w.tcx.target().layout.i64_align);
                for (arg, size, align) in [
                    ("u8", 2, 1),
                    ("u16", 4, 2),
                    ("i64", (9u64).next_multiple_of(i64_align), i64_align),
                    ("string", 4 * p, p),
                    ("Box<u8>", 2 * p, p),
                ] {
                    let ty = w.ty(&format!("Pair<{arg}>"));
                    assert_eq!(w.size_align(ty), (size, align as u32), "Pair<{arg}>");
                }
            },
        );

        h.case(
            format!("classes/a generic base at the subclass's arguments on {target}"),
            move || {
                let mut w = World::new(target);
                let p = w.p();
                w.declare("public class Holder<T> { public item: T; }");
                let concrete =
                    w.declare("public class Bytes extends Holder<u8[3]> { public more: u8; }");
                // `Holder<u8[3]>` is the pointer and 3 bytes, rounded up to `2P`.
                assert_eq!(w.ok(concrete).fields, [p, 2 * p]);
                w.declare("public class Wrap<U> extends Holder<U> { public tag: u16; }");
                let at_u32 = w.ty("Wrap<u32>");
                assert_eq!(w.ok(at_u32).fields, [p, 2 * p]);
                assert_eq!(
                    w.size_align(at_u32),
                    ((2 * p + 2).next_multiple_of(p), p as u32)
                );
                let at_string = w.ty("Wrap<string>");
                assert_eq!(w.ok(at_string).fields, [p, 4 * p]);
            },
        );

        h.case(format!("classes/@packed removes the padding on {target}"), move || {
            let mut w = World::new(target);
            let packed = w.declare(
                "@packed public final class Hdr { public a: u8; public b: i64; public c: u16; public d: u32; }",
            );
            assert_eq!(w.ok(packed).fields, [0, 1, 9, 11]);
            assert_eq!(w.size_align(packed), (15, 1));
            // The same fields unpacked.
            let plain = w.declare(
                "public final class Plain { public a: u8; public b: i64; public c: u16; public d: u32; }",
            );
            let i64_align = u64::from(w.tcx.target().layout.i64_align);
            assert_eq!(w.ok(plain).fields, [0, i64_align, i64_align + 8, i64_align + 12]);
            // A packed class inside another is placed at alignment 1.
            let outer = w.declare("public final class Outer { public x: u8; public h: Hdr; }");
            assert_eq!(w.ok(outer).fields, [0, 1]);
            assert_eq!(w.size_align(outer), (16, 1));
        });

        h.case(
            format!("classes/@align raises the alignment and rounds the size on {target}"),
            move || {
                let mut w = World::new(target);
                let small = w.declare("@align(16) public final class Line { public a: u8; }");
                assert_eq!(w.size_align(small), (16, 16));
                let exact = w.declare("@align(4) public final class Quad { public a: u32[3]; }");
                assert_eq!(w.size_align(exact), (12, 4));
                // `@align` never lowers an alignment.
                let wide = w.declare("@align(2) public final class Wide { public a: u32; }");
                assert_eq!(w.size_align(wide), (4, 4));
                let held =
                    w.declare("public final class Held { public tag: u8; public line: Line; }");
                assert_eq!(w.ok(held).fields, [0, 16]);
                assert_eq!(w.size_align(held), (32, 16));
            },
        );

        h.case(
            format!("classes/@repr(\"C\") is the default order on {target}"),
            move || {
                let mut w = World::new(target);
                let fields =
                    "{ public a: u8; public b: i64; public c: u16; public d: f64; public e: u8; }";
                let c = w.declare(&format!("@repr(\"C\") public final class C {fields}"));
                let plain = w.declare(&format!("public final class Plain {fields}"));
                assert_eq!(w.ok(c), w.ok(plain));
            },
        );

        h.case(
            format!("classes/Atomic64 aligns to 8 everywhere on {target}"),
            move || {
                let mut w = World::new(target);
                let atomic = w.declare("@align(8) public final class Atomic64 { private v: u64; }");
                assert_eq!(w.size_align(atomic), (8, 8));
                let after = w.declare(
                    "public final class Counter { public flag: bool; public n: Atomic64; }",
                );
                assert_eq!(w.ok(after).fields, [0, 8]);
                assert_eq!(w.size_align(after), (16, 8));
            },
        );

        h.case(
            format!("classes/@packed with @align on {target}"),
            move || {
                // Conflicting attributes are EN0817 (S:1290); if sema lets both through,
                // the fields are packed and the alignment then raised.
                let mut w = World::new(target);
                let both = w.declare(
                    "@packed @align(8) public final class Both { public a: u8; public b: u32; }",
                );
                assert_eq!(w.ok(both).fields, [0, 1]);
                assert_eq!(w.size_align(both), (8, 8));
            },
        );

        h.case(
            format!("classes/an @align that is no power of two is ignored on {target}"),
            move || {
                // EN0806 and friends are sema's; layout keeps the natural alignment.
                let mut w = World::new(target);
                let odd = w.declare("@align(12) public final class Odd { public a: u16; }");
                assert_eq!(w.size_align(odd), (2, 2));
                let (adt, _) = w.class(
                    "Zero",
                    ClassModifier::Final,
                    Attrs {
                        align: Some(0),
                        ..Attrs::default()
                    },
                    &[],
                );
                let u8_ty = w.tcx.common().u8;
                w.field(adt, "a", u8_ty);
                let zero = w.tcx.mk_adt(adt, &[]);
                assert_eq!(w.size_align(zero), (1, 1));
            },
        );

        h.case(
            format!("classes/offsetOf by field name on {target}"),
            move || {
                let mut w = World::new(target);
                let p = w.p();
                let ty =
                    w.declare("public class Animal { public name: string; private legs: u8; }");
                let mut cx = LayoutCx::new(&w.tcx);
                assert_eq!(cx.offset_of(ty, "name"), Ok(Some(p)));
                assert_eq!(cx.offset_of(ty, "legs"), Ok(Some(4 * p)));
                assert_eq!(cx.offset_of(ty, "tail"), Ok(None));
                assert_eq!(cx.size_of(ty), Ok(5 * p));
                assert_eq!(cx.align_of(ty), Ok(p as u32));
            },
        );
    }
}
