//! SPEC 11's table of sizes and alignments (S:1615-1624), read from the document:
//! one case per type the table names, on each pointer width. A row that names a
//! family (`&T`, `*T`, `fn(...)`, `Box<T>`, the closure parameter) is checked on a
//! set of its members; the four two-word forms the sentence after the table lists
//! are read from that sentence and checked on their own.

use enrang_hir::{Abi, FnPtrSig, Ty, TyKind};
use enrang_layout::LayoutError;
use enrang_testkit::Harness;

use crate::support::{TARGETS, World, amount, backticked, spec, table_after};

const HEADER: &str = "| Type | Size | Align |";

/// The declarations the members of a family use.
const DECLARATIONS: [&str; 5] = [
    "public final class Point { public x: i32; public y: i32; }",
    "public class Animal { public name: string; }",
    "public interface Speaker { }",
    "public final class Holder { private r: &i64; }",
    // The library's `Atomic64` (plan f.2, S:1597), with the field it declares.
    "@align(8) public final class Atomic64 { private v: u64; }",
];

/// The `T`s a `&T`, `*T` or `Box<T>` row is checked on. None is one of the four
/// two-word forms: `string` behind `&`, a view, an interface.
const POINTEES: [&str; 12] = [
    "i64",
    "u8",
    "bool",
    "i64[]",
    "u8[8]",
    "Point",
    "Animal",
    "Box<Point>",
    "i64 | null",
    "[i32, bool]",
    "{ x: i32 }",
    "fn(i64) => void",
];

fn world(target: &str) -> World {
    let mut w = World::new(target);
    for declaration in DECLARATIONS {
        w.declare(declaration);
    }
    w
}

/// The types SPEC's spelling `spelling` stands for.
fn members(w: &mut World, spelling: &str) -> Vec<Ty> {
    let substitute = |w: &mut World, extra: &[&str]| -> Vec<Ty> {
        POINTEES
            .iter()
            .chain(extra)
            .map(|t| w.ty(&spelling.replace('T', &format!("({t})"))))
            .collect()
    };
    match spelling {
        "&T" => substitute(w, &["Holder", "*u8", "Box<Speaker>", "string[]"]),
        "*T" => substitute(w, &["string", "Slice<u8>", "Speaker", "Holder"]),
        "Box<T>" => {
            let mut tys = substitute(w, &["string", "Box<Speaker>"]);
            let t = w.param("T");
            tys.push(w.tcx.mk_box(t));
            tys
        }
        "fn(...)" => {
            let c = *w.tcx.common();
            let s = w.tcx.mk_ref(c.str);
            let bytes = w.tcx.mk_array(c.u8);
            let mut tys = vec![
                w.fn_ptr(&[], c.void),
                w.fn_ptr(&[c.i64], c.i64),
                w.fn_ptr(&[s, bytes], c.bool),
            ];
            tys.push(
                w.tcx
                    .mk_fn_ptr(Abi::Win64, FnPtrSig::new(&[c.u64, c.u64], c.u64)),
            );
            tys
        }
        "closure parameter" => {
            let c = *w.tcx.common();
            let s = w.tcx.mk_ref(c.str);
            vec![w.closure(&[], c.void), w.closure(&[c.i64, s], c.bool)]
        }
        "Atomic64" => vec![w.named("Atomic64")],
        _ => vec![w.ty(spelling)],
    }
}

/// Each row's spellings, with its size and alignment cells.
fn rows() -> Vec<(Vec<String>, String, String)> {
    table_after(spec(), HEADER)
        .into_iter()
        .map(|row| {
            let mut spellings = backticked(&row[0]);
            if spellings.is_empty() {
                spellings.push(row[0].clone());
            }
            (spellings, row[1].clone(), row[2].clone())
        })
        .collect()
}

/// The sentence after the table that lists the two-word forms.
fn two_word_forms() -> Vec<String> {
    let sentence = spec()
        .lines()
        .find(|line| line.starts_with("Four forms of the `&T` and `Box<T>` row are `2P` instead"))
        .expect("the sentence on the two-word forms");
    let listed = sentence
        .split_once("described below:")
        .expect("its list")
        .1
        .split('.')
        .next()
        .expect("the list");
    // The list also names the interface `I` itself, which is no form.
    backticked(listed)
        .into_iter()
        .filter(|item| item.starts_with('&') || item.starts_with("Box<"))
        .collect()
}

pub fn register(h: &mut Harness) {
    for (spellings, size, align) in rows() {
        for spelling in spellings {
            for target in TARGETS {
                let (size, align, spelling) = (size.clone(), align.clone(), spelling.clone());
                h.case(format!("table/{spelling} on {target}"), move || {
                    let mut w = world(target);
                    let p = w.p();
                    let size = amount(&size, p);
                    let align = amount(&align, p);
                    for ty in members(&mut w, &spelling) {
                        let layout = w.ok(ty);
                        let shown = w.tcx.ty_string(ty);
                        assert_eq!(layout.size, size, "sizeOf<{shown}>()");
                        assert_eq!(u64::from(layout.align), align, "alignOf<{shown}>()");
                    }
                });
            }
        }
    }

    h.case("table/every primitive type has a row", || {
        let named: Vec<String> = rows().into_iter().flat_map(|row| row.0).collect();
        for prim in [
            "bool", "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "isize", "usize", "f32",
            "f64", "void", "never",
        ] {
            assert!(named.iter().any(|n| n == prim), "no row names `{prim}`");
        }
        for family in [
            "&T",
            "*T",
            "fn(...)",
            "Box<T>",
            "closure parameter",
            "Atomic64",
        ] {
            assert!(named.iter().any(|n| n == family), "no row names `{family}`");
        }
    });

    h.case(
        "table/the two-word forms are the four the sentence lists",
        || {
            assert_eq!(two_word_forms(), ["&string", "&Slice<T>", "Box<I>", "&I"]);
        },
    );

    for target in TARGETS {
        h.case(format!("table/the two-word forms on {target}"), move || {
            let mut w = world(target);
            let p = w.p();
            for form in two_word_forms() {
                let tys: Vec<Ty> = match form.as_str() {
                    // Only a `&string` that reads is two words; which form a
                    // `&string` has follows its inferred permission.
                    "&string" => {
                        let ty = w.ty("&string");
                        assert_eq!(
                            w.layout(ty).unwrap_err(),
                            LayoutError::DependsOnContracts { ty }
                        );
                        continue;
                    }
                    "&Slice<T>" => {
                        let t = w.param("T");
                        let slice = w.tcx.mk_slice(t);
                        vec![
                            w.ty("&Slice<u8>"),
                            w.ty("&Slice<Point>"),
                            w.ty("&Slice<string>"),
                            w.tcx.mk_ref(slice),
                        ]
                    }
                    "Box<I>" => vec![w.ty("Box<Speaker>")],
                    "&I" => vec![w.ty("&Speaker")],
                    other => panic!("an unknown form `{other}`"),
                };
                for ty in tys {
                    let layout = w.ok(ty);
                    let shown = w.tcx.ty_string(ty);
                    assert_eq!((layout.size, layout.align), (2 * p, p as u32), "{shown}");
                    assert_eq!(layout.fields, [0, p], "{shown}: two words");
                    assert!(matches!(w.tcx.kind(ty), TyKind::Ref(_) | TyKind::Boxed(_)));
                }
            }
        });
    }
}
