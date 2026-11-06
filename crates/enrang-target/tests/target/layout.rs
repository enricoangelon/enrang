//! SPEC 11's size and alignment rules, at the `DataLayout` level: its tables are
//! parsed from the document and evaluated with each target's layout. The layout
//! engine arrives at M2; the small calculator here only shows that these fields are
//! enough to reach the worked sizes SPEC states.

use enrang_target::{CpuLevel, DataLayout};
use enrang_testkit::Harness;

use crate::support::{NATIVE_TARGETS, TARGETS, Table, default_spec, section, table};

fn spec_11() -> &'static str {
    section("SPEC.md", "## 11. Runtime data layout")
}

fn sizes() -> Table {
    table(spec_11(), &["Type", "Size", "Align"])
}

fn worked() -> Table {
    table(spec_11(), &["Type", "`P == 4`", "`P == 8`"])
}

/// Evaluates a size or alignment cell for pointer width `p`: `4`, `` `P` ``,
/// `` `2P` (code, env), stack only ``, or `` 4 when `P == 4`, 8 when `P == 8` ``.
fn eval(cell: &str, p: u32) -> u32 {
    if cell.contains(" when ") {
        for arm in cell.split(", ") {
            let (value, condition) = arm.split_once(" when ").expect("`v when `P == n``");
            let wanted = condition
                .trim_matches('`')
                .strip_prefix("P == ")
                .expect("a condition on P");
            if wanted.parse::<u32>() == Ok(p) {
                return value.parse().expect("a value");
            }
        }
        panic!("no arm of `{cell}` covers P == {p}");
    }
    let first = cell.split_whitespace().next().expect("a value");
    match first.trim_matches('`') {
        "P" => p,
        "2P" => 2 * p,
        number => number.parse().unwrap_or_else(|_| panic!("`{cell}`")),
    }
}

/// The row of the size table that names `ty`.
fn row_of(table: &Table, ty: &str) -> (String, String) {
    let quoted = format!("`{ty}`");
    let row = table
        .rows
        .iter()
        .find(|row| row[0] == ty || row[0].split(", ").any(|name| name == quoted))
        .unwrap_or_else(|| panic!("`{ty}` is in no row of the table"));
    (row[1].clone(), row[2].clone())
}

pub fn register(h: &mut Harness) {
    table_rows(h);
    aligned_by_field(h);
    atomic64(h);
    frames(h);
    worked_sizes(h);
    eval_cases(h);
}

fn table_rows(h: &mut Harness) {
    // Every type in the table, every target: what the layout's fields say of it.
    let readers: &[(&str, fn(DataLayout) -> (u32, u32))] = &[
        ("bool", |_| (1, 1)),
        ("i8", |_| (1, 1)),
        ("u8", |_| (1, 1)),
        ("i16", |_| (2, 2)),
        ("u16", |_| (2, 2)),
        ("i32", |_| (4, 4)),
        ("u32", |_| (4, 4)),
        ("f32", |_| (4, 4)),
        ("i64", |l| (8, l.i64_align)),
        ("u64", |l| (8, l.i64_align)),
        ("f64", |l| (8, l.f64_align)),
        ("isize", |l| (l.ptr_bytes, l.ptr_bytes)),
        ("usize", |l| (l.ptr_bytes, l.ptr_bytes)),
        ("&T", |l| (l.ptr_bytes, l.ptr_bytes)),
        ("&mut T", |l| (l.ptr_bytes, l.ptr_bytes)),
        ("*T", |l| (l.ptr_bytes, l.ptr_bytes)),
        ("*mut T", |l| (l.ptr_bytes, l.ptr_bytes)),
        ("fn(...)", |l| (l.ptr_bytes, l.ptr_bytes)),
        ("Box<T>", |l| (l.ptr_bytes, l.ptr_bytes)),
        ("closure parameter", |l| (2 * l.ptr_bytes, l.ptr_bytes)),
        ("Atomic64", |_| (8, 8)),
        ("void", |_| (0, 1)),
        ("never", |_| (0, 1)),
    ];
    let evaluated = readers.len();
    h.case(
        "spec11/the table has the rows the suite evaluates",
        move || {
            // Every name in the document's table is read below, so a new row fails here.
            let table = sizes();
            let mut names = 0;
            for row in &table.rows {
                names += if row[0].starts_with('`') {
                    row[0].split(", ").count()
                } else {
                    1
                };
            }
            assert_eq!(names, evaluated);
        },
    );
    for &(ty, read) in readers {
        for target in TARGETS {
            h.case(format!("spec11/{target}/{ty}"), move || {
                let layout = default_spec(target).layout;
                let (size, align) = read(layout);
                let table = sizes();
                let (want_size, want_align) = row_of(&table, ty);
                let p = layout.ptr_bytes;
                assert_eq!(size, eval(&want_size, p), "size against `{want_size}`");
                assert_eq!(align, eval(&want_align, p), "align against `{want_align}`");
            });
        }
    }
}

fn aligned_by_field(h: &mut Harness) {
    for target in TARGETS {
        h.case(
            format!("spec11/{target}/i64 and f64 align together"),
            move || {
                let layout = default_spec(target).layout;
                assert_eq!(layout.i64_align, layout.f64_align);
                assert_eq!(layout.i64_align, layout.ptr_bytes);
            },
        );
        h.case(
            format!("spec11/{target}/every alignment is a power of two"),
            move || {
                let layout = default_spec(target).layout;
                for align in [
                    layout.ptr_bytes,
                    layout.i64_align,
                    layout.f64_align,
                    layout.frame_align,
                ] {
                    assert!(align.is_power_of_two(), "{align}");
                }
            },
        );
        h.case(
            format!("spec11/{target}/the pointer fits the frame"),
            move || {
                let layout = default_spec(target).layout;
                assert!(layout.frame_align >= layout.ptr_bytes);
                assert_eq!(layout.frame_align % layout.i64_align, 0);
            },
        );
    }
    let rows = [
        ("i386-linux", 4, 4),
        ("i386-none", 4, 4),
        ("vm32", 4, 4),
        ("x86_64-linux", 8, 8),
        ("x86_64-windows", 8, 8),
        ("x86_64-none", 8, 8),
        ("vm64", 8, 8),
    ];
    for (target, p, i64_align) in rows {
        h.case(format!("spec11/{target}/stated by hand"), move || {
            let layout = default_spec(target).layout;
            assert_eq!(layout.ptr_bytes, p);
            assert_eq!(layout.i64_align, i64_align);
            assert_eq!(layout.f64_align, i64_align);
        });
    }
}

fn atomic64(h: &mut Harness) {
    h.case(
        "spec11/Atomic64 aligns to 8 even where i64 does not",
        || {
            let table = sizes();
            let (_, align) = row_of(&table, "Atomic64");
            for target in ["i386-linux", "i386-none", "vm32"] {
                let layout = default_spec(target).layout;
                assert_eq!(eval(&align, layout.ptr_bytes), 8, "{target}");
                assert_eq!(layout.i64_align, 4, "{target}: so it cannot borrow this");
            }
            let text = section("SPEC.md", "### 10.5 Atomics");
            assert!(text.contains("It has alignment 8 on every target"));
        },
    );
    h.case("spec11/Atomic64's level comes from cmpxchg8b", || {
        let text = section("SPEC.md", "### 10.5 Atomics");
        assert!(text.contains("Naming it below `i586` is EN0910"));
        assert_eq!(
            CpuLevel::lowest_with(enrang_target::Feature::Cmpxchg8b, enrang_target::Arch::I386),
            Some(CpuLevel::I586)
        );
    });
}

fn frames(h: &mut Harness) {
    h.case("frames/ARCHITECTURE 7.5 states 4 and 16", || {
        let text = section("ARCHITECTURE.md", "### 7.5 Frames");
        assert!(text.contains("i386 keeps 4"), "{text}");
        assert!(text.contains("x86-64 keeps 16 at every call"), "{text}");
    });
    for target in NATIVE_TARGETS {
        h.case(format!("frames/{target}"), move || {
            let want = if target.starts_with("i386-") { 4 } else { 16 };
            assert_eq!(default_spec(target).layout.frame_align, want);
        });
    }
    for (vm, want) in [("vm32", 4), ("vm64", 16)] {
        h.case(format!("frames/{vm} borrows"), move || {
            assert_eq!(default_spec(vm).layout.frame_align, want);
        });
    }
}

/// A field for the calculator: its size and alignment.
#[derive(Copy, Clone)]
struct Part {
    size: u64,
    align: u64,
}

fn align_up(offset: u64, align: u64) -> u64 {
    offset.div_ceil(align) * align
}

/// SPEC 11's class rule: declaration order, each field at the next aligned offset,
/// size rounded up to the maximum field alignment. `@packed` drops the padding.
fn class(fields: &[Part], packed: bool) -> Part {
    let mut offset = 0;
    let mut align = 1;
    for field in fields {
        let field_align = if packed { 1 } else { field.align };
        offset = align_up(offset, field_align) + field.size;
        align = align.max(field_align);
    }
    Part {
        size: align_up(offset, align),
        align,
    }
}

/// SPEC 11's enum rule: a `u32` tag at 0, the payload at the next offset aligned for
/// the largest variant alignment, and the size rounded up to the enum's alignment,
/// the maximum of 4 and all payload alignments.
fn tagged(variants: &[Part]) -> Part {
    let payload_align = variants.iter().map(|v| v.align).max().unwrap_or(1);
    let payload_size = variants.iter().map(|v| v.size).max().unwrap_or(0);
    let align = payload_align.max(4);
    let start = align_up(4, payload_align);
    Part {
        size: align_up(start + payload_size, align),
        align,
    }
}

/// The size SPEC 11's rules give a type of the worked table, using only `layout`.
fn worked_size(ty: &str, layout: DataLayout) -> u64 {
    let p = u64::from(layout.ptr_bytes);
    let word = Part { size: p, align: p };
    let i64_part = Part {
        size: 8,
        align: u64::from(layout.i64_align),
    };
    let i32_part = Part { size: 4, align: 4 };
    let u16_part = Part { size: 2, align: 2 };
    let string = class(&[word, word, word], false);
    match ty {
        "`string`" | "`i64[]`" => string.size,
        "`i64 | null`" => tagged(&[i64_part]).size,
        "`class Player { name: string; score: i64; }`" => class(&[string, i64_part], false).size,
        "same with `level: i32` added" => class(&[string, i64_part, i32_part], false).size,
        "`enum Token { Num(i64), Add, Bad { text: string } }`" => {
            let num = class(&[i64_part], false);
            let bad = class(&[string], false);
            tagged(&[num, bad]).size
        }
        "`@packed class GdtPointer { limit: u16; base: u32; }`" => {
            class(&[u16_part, i32_part], true).size
        }
        other => panic!("a type the suite cannot lay out: `{other}`"),
    }
}

fn worked_sizes(h: &mut Harness) {
    let table = worked();
    assert_eq!(table.rows.len(), 7, "SPEC 11's worked sizes");
    for row in table.rows {
        for (target, column) in [
            ("i386-linux", 1),
            ("i386-none", 1),
            ("vm32", 1),
            ("x86_64-linux", 2),
            ("x86_64-windows", 2),
            ("x86_64-none", 2),
            ("vm64", 2),
        ] {
            let ty = row[0].clone();
            let want: u64 = row[column].parse().expect("a size");
            h.case(format!("worked/{target}/{ty}"), move || {
                let layout = default_spec(target).layout;
                assert_eq!(worked_size(&ty, layout), want);
            });
        }
    }
    h.case(
        "worked/an 8-aligned i64 on 32 bits would break Player's size",
        || {
            // The negative control: the worked table does depend on the layout.
            let wrong = DataLayout {
                i64_align: 8,
                f64_align: 8,
                ..default_spec("i386-linux").layout
            };
            let ty = "`class Player { name: string; score: i64; }`";
            assert_eq!(worked_size(ty, default_spec("i386-linux").layout), 20);
            assert_ne!(worked_size(ty, wrong), 20);
        },
    );
}

fn eval_cases(h: &mut Harness) {
    let rows: &[(&str, u32, u32)] = &[
        ("4", 8, 4),
        ("`P`", 4, 4),
        ("`P`", 8, 8),
        ("`2P` (code, env), stack only", 4, 8),
        ("`2P` (code, env), stack only", 8, 16),
        ("4 when `P == 4`, 8 when `P == 8`", 4, 4),
        ("4 when `P == 4`, 8 when `P == 8`", 8, 8),
    ];
    for &(cell, p, want) in rows {
        h.case(format!("spec11/the cell reader/{cell} at {p}"), move || {
            assert_eq!(eval(cell, p), want);
        });
    }
}
