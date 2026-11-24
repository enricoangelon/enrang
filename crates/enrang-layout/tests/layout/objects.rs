//! Anonymous object types and tuples (S:1642): fields sorted by alignment, largest
//! first, ties broken by name in byte order (a tuple's by position), then placed as
//! a class's; `fields` indexed by the shape's (name-sorted) order or the position.

use enrang_layout::LayoutCx;
use enrang_testkit::Harness;

use crate::support::{TARGETS, World};

pub fn register(h: &mut Harness) {
    for target in TARGETS {
        h.case(
            format!("objects/larger alignments first on {target}"),
            move || {
                let mut w = World::new(target);
                let ty = w.ty("{ x: u8, y: i64, z: u16 }");
                assert_eq!(
                    (w.offset(ty, "y"), w.offset(ty, "z"), w.offset(ty, "x")),
                    (0, 8, 10)
                );
                let i64_align = w.tcx.target().layout.i64_align;
                assert_eq!(
                    w.size_align(ty),
                    (if i64_align == 4 { 12 } else { 16 }, i64_align)
                );
                // The shape is sorted by name, so `fields` reads x, y, z.
                assert_eq!(w.ok(ty).fields, [10, 0, 8]);
            },
        );

        h.case(
            format!("objects/ties by name in byte order on {target}"),
            move || {
                let mut w = World::new(target);
                // Upper case sorts before lower case, and `a` before `ab`.
                let ty = w.ty("{ b: u8, ab: u8, a: u8, B: u8 }");
                assert_eq!(w.offset(ty, "B"), 0);
                assert_eq!(w.offset(ty, "a"), 1);
                assert_eq!(w.offset(ty, "ab"), 2);
                assert_eq!(w.offset(ty, "b"), 3);
                assert_eq!(w.size_align(ty), (4, 1));
            },
        );

        h.case(
            format!("objects/one field set is one layout on {target}"),
            move || {
                let mut w = World::new(target);
                let one = w.ty("{ name: string, age: u8, id: u32 }");
                let other = w.ty("{ id: u32, age: u8, name: string }");
                assert_eq!(one, other);
                let p = w.p();
                if p == 4 {
                    // `string` and `u32` both align to 4: `id` sorts before `name`.
                    assert_eq!(w.offset(one, "id"), 0);
                    assert_eq!(w.offset(one, "name"), 4);
                    assert_eq!(w.offset(one, "age"), 16);
                    assert_eq!(w.size_align(one), (20, 4));
                } else {
                    assert_eq!(w.offset(one, "name"), 0);
                    assert_eq!(w.offset(one, "id"), 24);
                    assert_eq!(w.offset(one, "age"), 28);
                    assert_eq!(w.size_align(one), (32, 8));
                }
            },
        );

        h.case(
            format!("objects/nested objects and optional fields on {target}"),
            move || {
                let mut w = World::new(target);
                // `x?: T` is a `T | null` field (S:1642): it aligns to 4 at least.
                let ty = w.ty("{ inner: { a: u8, b: u8 }, opt: u8 | null, last: bool }");
                assert_eq!(w.offset(ty, "opt"), 0);
                assert_eq!(w.offset(ty, "inner"), 8);
                assert_eq!(w.offset(ty, "last"), 10);
                assert_eq!(w.size_align(ty), (12, 4));
            },
        );

        h.case(
            format!("objects/empty objects and tuples on {target}"),
            move || {
                let mut w = World::new(target);
                for spelling in ["{ }", "[]", "{ a: void }", "[void, never]"] {
                    let ty = w.ty(spelling);
                    assert_eq!(w.size_align(ty), (0, 1), "{spelling}");
                }
            },
        );

        h.case(
            format!("objects/tuple ties by position on {target}"),
            move || {
                let mut w = World::new(target);
                let ty = w.ty("[u8, u8, u8]");
                assert_eq!(w.ok(ty).fields, [0, 1, 2]);
                let mixed = w.ty("[u8, string, u16, i64, bool]");
                let p = w.p();
                let i64_align = u64::from(w.tcx.target().layout.i64_align);
                let layout = w.ok(mixed);
                if i64_align == p {
                    // string and i64 align alike: position decides.
                    assert_eq!(layout.fields[1], 0);
                    assert_eq!(layout.fields[3], 3 * p);
                } else {
                    assert_eq!(layout.fields[3], 0);
                    assert_eq!(layout.fields[1], 8);
                }
                assert_eq!(layout.fields[2], 3 * p + 8);
                assert_eq!(layout.fields[0], 3 * p + 10);
                assert_eq!(layout.fields[4], 3 * p + 11);
            },
        );

        h.case(
            format!("objects/a long tuple keeps numeric positions on {target}"),
            move || {
                // ARCHITECTURE 7.7: ties by position, so part 10 follows part 9.
                let mut w = World::new(target);
                let parts = ["u8"; 12].join(", ");
                let ty = w.ty(&format!("[{parts}]"));
                assert_eq!(w.ok(ty).fields, (0..12).collect::<Vec<u64>>());
            },
        );

        h.case(
            format!("objects/offsetOf on a tuple by position on {target}"),
            move || {
                let mut w = World::new(target);
                let ty = w.ty("[bool, i32, bool]");
                let mut cx = LayoutCx::new(&w.tcx);
                assert_eq!(cx.offset_of(ty, "0"), Ok(Some(4)));
                assert_eq!(cx.offset_of(ty, "1"), Ok(Some(0)));
                assert_eq!(cx.offset_of(ty, "2"), Ok(Some(5)));
                for missing in ["3", "01", "-1", "x", ""] {
                    assert_eq!(cx.offset_of(ty, missing), Ok(None), "{missing:?}");
                }
                let object = w.ty("{ a: u8 }");
                let scalar = w.ty("i64");
                let mut cx = LayoutCx::new(&w.tcx);
                assert_eq!(cx.offset_of(object, "b"), Ok(None));
                assert_eq!(cx.offset_of(scalar, "a"), Ok(None));
            },
        );

        h.case(format!("objects/fixed arrays on {target}"), move || {
            let mut w = World::new(target);
            let p = w.p();
            let i64_align = w.tcx.target().layout.i64_align;
            for (spelling, size, align) in [
                ("u8[8]", 8, 1),
                ("u32[1024]", 4096, 4),
                ("i64[3]", 24, i64_align),
                ("string[2]", 6 * p, p as u32),
                ("[bool, i32, bool][4]", 32, 4),
                ("u16[3][2]", 12, 2),
                ("u8[0]", 0, 1),
                ("i64[0]", 0, i64_align),
            ] {
                let ty = w.ty(spelling);
                let layout = w.ok(ty);
                assert_eq!((layout.size, layout.align), (size, align), "{spelling}");
                assert!(layout.fields.is_empty() && layout.variants.is_none());
            }
        });
    }
}
