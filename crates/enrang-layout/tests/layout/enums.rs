//! Enums, `Result` and `T | null` (S:1644-1650): the tag at 0, the payload at the
//! next offset aligned for the largest case, each case laid out as a `final` class
//! there, the alignment at least the tag's; tags by position, but discriminants for
//! a payload-free enum; `@repr("u8"|"u16"|"u32")`; no niche but `&I | null`.

use enrang_hir::VariantIdx;
use enrang_layout::{Layout, TagLayout, VariantsLayout};
use enrang_testkit::Harness;

use crate::support::{TARGETS, World};

fn cases(layout: &Layout) -> &VariantsLayout {
    layout.variants.as_ref().expect("a sum type")
}

fn tags(layout: &Layout) -> Vec<u64> {
    cases(layout).variants.iter().map(|v| v.tag).collect()
}

pub fn register(h: &mut Harness) {
    for target in TARGETS {
        h.case(
            format!("enums/Token's cases after the tag on {target}"),
            move || {
                let mut w = World::new(target);
                let p = w.p();
                let token = w
                    .declare("public enum Token { Num { value: i64 }, Add, Bad { text: string } }");
                let layout = w.ok(token);
                let payload = if p == 4 { 4 } else { 8 };
                assert_eq!(cases(&layout).tag, TagLayout::Direct { size: 4 });
                assert_eq!(cases(&layout).payload, payload);
                assert_eq!(tags(&layout), [0, 1, 2]);
                let v = &cases(&layout).variants;
                assert_eq!((v[0].fields.clone(), v[0].size), (vec![payload], 8));
                assert_eq!((v[1].fields.clone(), v[1].size), (vec![], 0));
                assert_eq!((v[2].fields.clone(), v[2].size), (vec![payload], 3 * p));
                assert_eq!(layout.align, p as u32);
                assert!(layout.fields.is_empty());
            },
        );

        h.case(format!("enums/each case is a final class at the payload on {target}"), move || {
            let mut w = World::new(target);
            let shape = w.declare(
                "public enum Shape { Circle { radius: f64 }, Rect { w: i32, h: i32, filled: bool }, Empty }",
            );
            let layout = w.ok(shape);
            let payload = u64::from(w.tcx.target().layout.f64_align);
            let v = &cases(&layout).variants;
            assert_eq!(v[0].fields, [payload]);
            assert_eq!(v[1].fields, [payload, payload + 4, payload + 8]);
            assert_eq!(v[1].size, 12);
            assert_eq!(layout.size, (payload + 12).next_multiple_of(payload));
        });

        h.case(
            format!("enums/the alignment is at least 4 on {target}"),
            move || {
                let mut w = World::new(target);
                let small = w.declare("public enum Small { A { x: u8 }, B { y: u16, z: u8 } }");
                let layout = w.ok(small);
                assert_eq!((layout.size, layout.align), (8, 4));
                assert_eq!(cases(&layout).payload, 4);
                assert_eq!(cases(&layout).variants[1].fields, [4, 6]);
            },
        );

        h.case(
            format!("enums/payload-free enums by default on {target}"),
            move || {
                let mut w = World::new(target);
                let color = w.declare("public enum Color { Red, Green, Blue }");
                let layout = w.ok(color);
                assert_eq!((layout.size, layout.align), (4, 4));
                assert_eq!(tags(&layout), [0, 1, 2]);
                assert!(cases(&layout).variants.iter().all(|v| v.fields.is_empty()));
                let none = w.declare("public enum Never { }");
                assert_eq!(w.size_align(none), (4, 4));
            },
        );

        h.case(
            format!("enums/a payload-free tag is its discriminant on {target}"),
            move || {
                let mut w = World::new(target);
                // Written values, and consecutive defaults after them (S:591).
                let e = w.declare("public enum Level { Low = 1, Mid, High = 10, Top }");
                assert_eq!(tags(&w.ok(e)), [1, 2, 10, 11]);
                let neg = w.declare("public enum Dir { Down = -1, Flat, Up }");
                assert_eq!(tags(&w.ok(neg)), [0xFFFF_FFFF, 0, 1]);
                // A payload enum numbers its cases by position, whatever is written
                // (an integer there is sema's error, S:591).
                let payload = w.declare("public enum Op { Push { v: i64 }, Pop, Halt }");
                assert_eq!(tags(&w.ok(payload)), [0, 1, 2]);
                let valued = w.declare("public enum Bad { Push { v: i64 }, Pop = 5, Halt }");
                assert_eq!(tags(&w.ok(valued)), [0, 1, 2]);
            },
        );

        h.case(format!("enums/a text enum keeps positions on {target}"), move || {
            let mut w = World::new(target);
            let e = w.declare(
                "public enum AgeError { NotANumber = \"not a number\", Negative = \"negative age\" }",
            );
            let layout = w.ok(e);
            assert_eq!((layout.size, layout.align), (4, 4));
            assert_eq!(tags(&layout), [0, 1]);
        });

        h.case(
            format!("enums/@repr sets a payload-free tag on {target}"),
            move || {
                let mut w = World::new(target);
                for (repr, size) in [("u8", 1u32), ("u16", 2), ("u32", 4)] {
                    let e = w.declare(&format!(
                        "@repr(\"{repr}\") public enum E{repr} {{ A = 3, B, C = 200 }}"
                    ));
                    let layout = w.ok(e);
                    assert_eq!(
                        (layout.size, layout.align),
                        (u64::from(size), size),
                        "{repr}"
                    );
                    assert_eq!(cases(&layout).tag, TagLayout::Direct { size });
                    assert_eq!(tags(&layout), [3, 4, 200], "{repr}");
                }
                let wrapped = w.declare("@repr(\"u8\") public enum Wrapped { A = -1, B }");
                assert_eq!(tags(&w.ok(wrapped)), [0xFF, 0]);
                // In a class, a u8 tag packs like a u8.
                let held = w.declare("public final class Held { public a: u8; public e: Eu8; }");
                assert_eq!(w.ok(held).fields, [0, 1]);
            },
        );

        h.case(
            format!("enums/@repr does not shrink a payload enum's tag on {target}"),
            move || {
                let mut w = World::new(target);
                let e = w.declare("@repr(\"u8\") public enum P { A { x: u8 }, B }");
                let layout = w.ok(e);
                assert_eq!(cases(&layout).tag, TagLayout::Direct { size: 4 });
                assert_eq!((layout.size, layout.align), (8, 4));
            },
        );

        h.case(
            format!("enums/Result's Ok is 0 and Err is 1 on {target}"),
            move || {
                let mut w = World::new(target);
                let p = w.p();
                w.declare("public final class Failure { private text: string; }");
                w.declare("public enum Result<T, E> { Ok { value: T }, Err { error: E } }");
                w.declare("public enum Color { Red, Green }");
                let r = w.ty("Result<i64, Failure>");
                let layout = w.ok(r);
                let payload = if p == 4 { 4 } else { 8 };
                assert_eq!(tags(&layout), [0, 1]);
                assert_eq!(cases(&layout).variants[0].fields, [payload]);
                assert_eq!(cases(&layout).variants[1].fields, [payload]);
                assert_eq!(layout.size, payload + 3 * p);
                let unit = w.ty("Result<void, Color>");
                let layout = w.ok(unit);
                assert_eq!((layout.size, layout.align), (8, 4));
                assert_eq!(cases(&layout).variants[0].size, 0);
                let field = w.tcx.field_def(
                    match w.tcx.kind(r) {
                        enrang_hir::TyKind::Adt(adt, _) => adt,
                        _ => unreachable!(),
                    },
                    Some(VariantIdx(1)),
                    enrang_hir::FieldIdx(0),
                );
                assert_eq!(field.name.as_str(), "error");
            },
        );

        h.case(
            format!("enums/T | null is tag and payload on {target}"),
            move || {
                let mut w = World::new(target);
                let p = w.p();
                let i64_align = u64::from(w.tcx.target().layout.i64_align);
                w.declare("public final class Point { public x: i32; public y: i32; }");
                for (spelling, size, payload) in [
                    (
                        "i64 | null",
                        4u64.next_multiple_of(i64_align) + 8,
                        i64_align.max(4),
                    ),
                    ("bool | null", 8, 4),
                    ("u8[3] | null", 8, 4),
                    ("void | null", 4, 4),
                    ("string | null", 4u64.next_multiple_of(p) + 3 * p, p.max(4)),
                    ("&i64 | null", 2 * p, p.max(4)),
                    ("Box<Point> | null", 2 * p, p.max(4)),
                    ("Point | null", 12, 4),
                    ("u16 | null", 8, 4),
                ] {
                    let ty = w.ty(spelling);
                    let layout = w.ok(ty);
                    assert_eq!(layout.size, size, "{spelling}");
                    let sum = cases(&layout);
                    assert_eq!(sum.tag, TagLayout::Direct { size: 4 }, "{spelling}");
                    assert_eq!(sum.payload, payload, "{spelling}");
                    assert_eq!(tags(&layout), [0, 1]);
                    assert_eq!(sum.variants[0].fields, Vec::<u64>::new());
                    assert_eq!(sum.variants[1].fields, [payload]);
                }
            },
        );

        h.case(
            format!("enums/a generic enum at its arguments on {target}"),
            move || {
                let mut w = World::new(target);
                let p = w.p();
                w.declare("public enum Maybe<T> { None, Some { value: T } }");
                let at_u8 = w.ty("Maybe<u8>");
                assert_eq!(w.size_align(at_u8), (8, 4));
                let at_string = w.ty("Maybe<string>");
                assert_eq!(
                    w.size_align(at_string),
                    (4u64.next_multiple_of(p) + 3 * p, p.max(4) as u32)
                );
                let nested = w.ty("Maybe<Maybe<u8>>");
                assert_eq!(w.size_align(nested), (12, 4));
            },
        );
    }
}
