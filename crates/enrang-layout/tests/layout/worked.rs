//! SPEC 11's worked sizes (S:1654-1663), read from the table, and every other size
//! SPEC 11 and 7.6 work out in prose: the descriptors of `string` and `T[]`, the
//! view, the subclass that never reuses its base's tail padding, the anonymous
//! object and the tuple, and SPEC 7.6's layout-control examples. A prose example is
//! quoted here and checked to be in SPEC word for word, so neither can change alone.

use enrang_testkit::Harness;

use crate::support::{TARGETS, World, amount, backticked, spec, spec_says, table_after};

const HEADER: &str = "| Type | `P == 4` | `P == 8` |";

/// The worked sizes: each row's type, as a declaration or a type, with its size on
/// `P == 4` and on `P == 8`. "same with `level: i32` added" is the row above with
/// that field appended.
fn worked_rows() -> Vec<(String, u64, u64)> {
    let mut rows: Vec<(String, u64, u64)> = Vec::new();
    for row in table_after(spec(), HEADER) {
        let text = if row[0].starts_with("same with ") {
            let field = &backticked(&row[0])[0];
            let previous = &rows.last().expect("a row above").0;
            let close = previous.rfind('}').expect("a declaration");
            format!("{}public {field}; }}", &previous[..close])
        } else {
            backticked(&row[0])
                .into_iter()
                .next()
                .expect("a spelled type")
        };
        let size = |cell: &str| cell.parse::<u64>().expect("a size");
        rows.push((text, size(&row[1]), size(&row[2])));
    }
    rows
}

/// The column of each target in the worked sizes.
fn worked_size(target: &str, p4: u64, p8: u64) -> u64 {
    if target.starts_with("i386") { p4 } else { p8 }
}

/// The line of SPEC 11 that starts with `head`.
fn line(head: &str) -> &'static str {
    spec()
        .lines()
        .find(|line| line.starts_with(head))
        .unwrap_or_else(|| panic!("SPEC has no line starting {head:?}"))
}

/// A descriptor as SPEC writes it, `{ ptr: *u8 @0, len: usize @P, cap: usize @2P }`:
/// each field's name and offset at pointer width `p`.
fn descriptor(text: &str, p: u64) -> Vec<(String, u64)> {
    text.trim_matches(|c| c == '{' || c == '}' || c == ' ')
        .split(',')
        .map(|field| {
            let (name, rest) = field.split_once(':').expect("`name: type @offset`");
            let offset = rest.split_once('@').expect("an offset").1;
            (name.trim().to_owned(), amount(offset.trim(), p))
        })
        .collect()
}

/// The `size `nP`` (and `align `nP``) a descriptor line states.
fn stated(text: &str, what: &str, p: u64) -> Option<u64> {
    let after = text.split_once(&format!("{what} `"))?.1;
    Some(amount(&format!("`{}`", after.split('`').next()?), p))
}

const SUBCLASS: &str = "A subclass never reuses its base's tail padding: with `public class A { public a: i64; public b: u8; }` and `public class D extends A { public c: u8; }` on `x86_64`, `A` has its table pointer at 0, `a` at 8 and `b` at 16, size 24, and `D` places `c` at 24, size 32; on `i386`, `A` is size 16, and `D` places `c` at 16, size 20.";

const OBJECT: &str = "`{ found: bool, index: i32, last: bool }` places `index` at 0, `found` at 4 and `last` at 5, size 8 on both `P == 4` and `P == 8`";

const TUPLE: &str = "A tuple follows the same rule with the position as the name: `[bool, i32, bool]` is size 8, with element 1 at offset 0.";

const TARGET_ORDER: &str = "the order can differ between targets, because `i64` aligns to 4 when `P == 4` and to 8 when `P == 8`";

const STATIC_ASSERT: &str =
    "`assert(sizeOf<GdtPointer>() == 6);` at top level is evaluated at compile time.";

/// SPEC 7.6's example block: the declarations after the heading.
fn layout_control_block() -> Vec<String> {
    let section = spec()
        .split("### 7.6 Layout control")
        .nth(1)
        .expect("SPEC 7.6");
    let block = section
        .split("```ts\n")
        .nth(1)
        .expect("its example")
        .split("```")
        .next()
        .expect("its end");
    block
        .split("\n\n")
        .map(|declaration| declaration.split_whitespace().collect::<Vec<_>>().join(" "))
        .filter(|declaration| !declaration.is_empty())
        .collect()
}

pub fn register(h: &mut Harness) {
    h.case("worked/the table has the eight rows SPEC 11 gives", || {
        assert_eq!(worked_rows().len(), 8);
    });
    for (text, p4, p8) in worked_rows() {
        for target in TARGETS {
            let text = text.clone();
            h.case(format!("worked/{text} on {target}"), move || {
                let mut w = World::new(target);
                let ty = w.declare_or_ty(&text);
                let (size, align) = w.size_align(ty);
                assert_eq!(size, worked_size(target, p4, p8), "sizeOf<{text}>()");
                assert_eq!(size % u64::from(align), 0);
            });
        }
    }

    for target in TARGETS {
        h.case(
            format!("worked/the string and array descriptors on {target}"),
            move || {
                let mut w = World::new(target);
                let p = w.p();
                for (head, spelling) in [("**`string`**:", "string"), ("**`T[]`**:", "i64[]")] {
                    let text = line(head);
                    let fields = descriptor(&backticked(text)[1], p);
                    assert_eq!(
                        fields.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>(),
                        ["ptr", "len", "cap"]
                    );
                    let ty = w.ty(spelling);
                    let layout = w.ok(ty);
                    let offsets: Vec<u64> = fields.iter().map(|(_, at)| *at).collect();
                    assert_eq!(layout.fields, offsets, "{spelling}");
                    assert_eq!(Some(layout.size), stated(text, "size", p), "{spelling}");
                    assert_eq!(layout.align as u64, stated(text, "align", p).unwrap_or(p));
                }
            },
        );

        h.case(
            format!("worked/the view is a pointer and a length on {target}"),
            move || {
                let mut w = World::new(target);
                let p = w.p();
                let text = line("**`&Slice<T>`**:");
                let ty = w.ty("&Slice<i64>");
                let layout = w.ok(ty);
                assert_eq!(Some(layout.size), stated(text, "size", p));
                assert_eq!(Some(u64::from(layout.align)), stated(text, "align", p));
                assert_eq!(layout.fields, [0, p]);
            },
        );

        h.case(
            format!("worked/a subclass after its base on {target}"),
            move || {
                spec_says(SUBCLASS);
                let mut w = World::new(target);
                let declarations = backticked(SUBCLASS);
                let a = w.declare(&declarations[0]);
                let d = w.declare(&declarations[1]);
                let (la, ld) = (w.ok(a), w.ok(d));
                if target.starts_with("x86_64") {
                    // The table pointer at 0, `a` at 8 and `b` at 16, size 24.
                    assert_eq!((la.fields.clone(), la.size), (vec![8, 16], 24));
                    assert_eq!((ld.fields.clone(), ld.size), (vec![8, 16, 24], 32));
                } else {
                    assert_eq!(la.size, 16);
                    assert_eq!((ld.fields[2], ld.size), (16, 20));
                }
                assert_eq!(w.offset(d, "c"), ld.fields[2]);
            },
        );

        h.case(
            format!("worked/the anonymous object on {target}"),
            move || {
                spec_says(OBJECT);
                let mut w = World::new(target);
                let ty = w.ty(&backticked(OBJECT)[0]);
                assert_eq!(w.offset(ty, "index"), 0);
                assert_eq!(w.offset(ty, "found"), 4);
                assert_eq!(w.offset(ty, "last"), 5);
                assert_eq!(w.size_align(ty).0, 8);
            },
        );

        h.case(format!("worked/the tuple on {target}"), move || {
            spec_says(TUPLE);
            let mut w = World::new(target);
            let ty = w.ty(&backticked(TUPLE)[0]);
            assert_eq!(w.size_align(ty).0, 8);
            assert_eq!(w.offset(ty, "1"), 0);
            assert_eq!(w.ok(ty).fields, [4, 0, 5]);
        });

        h.case(
            format!("worked/the object order follows i64's alignment on {target}"),
            move || {
                spec_says(TARGET_ORDER);
                let mut w = World::new(target);
                let ty = w.ty("{ a: i32, b: i64 }");
                if target.starts_with("i386") {
                    // Both align to 4, so the names decide.
                    assert_eq!((w.offset(ty, "a"), w.offset(ty, "b")), (0, 4));
                    assert_eq!(w.size_align(ty), (12, 4));
                } else {
                    assert_eq!((w.offset(ty, "b"), w.offset(ty, "a")), (0, 8));
                    assert_eq!(w.size_align(ty), (16, 8));
                }
            },
        );

        h.case(
            format!("worked/SPEC 7.6's examples on {target}"),
            move || {
                spec_says(STATIC_ASSERT);
                let declarations = layout_control_block();
                assert_eq!(declarations.len(), 3, "{declarations:?}");
                let mut w = World::new(target);
                let tys: Vec<_> = declarations.iter().map(|d| w.declare(d)).collect();
                // `@packed`: no padding, alignment 1; `sizeOf<GdtPointer>() == 6`.
                assert_eq!(w.size_align(tys[0]), (6, 1));
                assert_eq!(w.ok(tys[0]).fields, [0, 2]);
                // `@repr("C")`: declaration order, natural alignment.
                assert_eq!(w.size_align(tys[1]), (8, 4));
                assert_eq!(w.ok(tys[1]).fields, [0, 4]);
                // `@align(4096)` raises the alignment and rounds the size.
                assert_eq!(w.size_align(tys[2]), (4096, 4096));
            },
        );
    }
}
