//! `apply_fixes`: results, conflict detection, and independence from list order.

use enrang_base::{BytePos, Span};
use enrang_diag::{Edit, FixConflict, apply_fixes};
use enrang_testkit::Harness;

use crate::support::Src;

/// An edit written in offsets from the start of the text, with its replacement.
type E = (usize, usize, &'static str);

/// How a row must come out.
#[derive(Copy, Clone)]
enum Out {
    Fixed(&'static str),
    /// A conflict between these two offsets' edits, in sorted order.
    Overlap(E, E),
    Invalid(E),
}

fn edits(src: &Src, list: &[E]) -> Vec<Edit> {
    list.iter()
        .map(|&(lo, hi, text)| Edit::replace(src.span(lo, hi), text))
        .collect()
}

fn check(text: &str, list: &[E], out: Out) {
    let src = Src::new("a.en", text);
    let edits = edits(&src, list);
    let result = apply_fixes(&src.text, src.base(), &edits);
    let edit_of = |&(lo, hi, text): &E| Edit::replace(src.span(lo, hi), text);
    match out {
        Out::Fixed(expected) => assert_eq!(result, Ok(expected.to_owned())),
        Out::Overlap(first, second) => assert_eq!(
            result,
            Err(FixConflict::Overlap {
                first: edit_of(&first),
                second: edit_of(&second),
            })
        ),
        Out::Invalid(edit) => assert_eq!(
            result,
            Err(FixConflict::InvalidSpan {
                edit: edit_of(&edit),
            })
        ),
    }
}

fn table(h: &mut Harness) {
    let rows: Vec<(&str, &'static str, Vec<E>, Out)> = vec![
        ("no edits", "abc", vec![], Out::Fixed("abc")),
        ("an empty text and no edits", "", vec![], Out::Fixed("")),
        (
            "an insertion at the start",
            "abc",
            vec![(0, 0, "x")],
            Out::Fixed("xabc"),
        ),
        (
            "an insertion in the middle",
            "abc",
            vec![(1, 1, "x")],
            Out::Fixed("axbc"),
        ),
        (
            "an insertion at the end",
            "abc",
            vec![(3, 3, "x")],
            Out::Fixed("abcx"),
        ),
        (
            "an insertion into nothing",
            "",
            vec![(0, 0, "x")],
            Out::Fixed("x"),
        ),
        (
            "a replacement",
            "abc",
            vec![(1, 2, "xy")],
            Out::Fixed("axyc"),
        ),
        ("a deletion", "abc", vec![(1, 2, "")], Out::Fixed("ac")),
        (
            "deleting everything",
            "abc",
            vec![(0, 3, "")],
            Out::Fixed(""),
        ),
        (
            "replacing everything",
            "abc",
            vec![(0, 3, "z")],
            Out::Fixed("z"),
        ),
        (
            "an empty insertion",
            "abc",
            vec![(1, 1, "")],
            Out::Fixed("abc"),
        ),
        (
            "two replacements",
            "abcdef",
            vec![(1, 2, "X"), (4, 5, "Y")],
            Out::Fixed("aXcdYf"),
        ),
        (
            "given out of order",
            "abcdef",
            vec![(4, 5, "Y"), (1, 2, "X")],
            Out::Fixed("aXcdYf"),
        ),
        (
            "touching replacements",
            "abcd",
            vec![(0, 2, "X"), (2, 4, "Y")],
            Out::Fixed("XY"),
        ),
        (
            "an insertion at a replacement's start goes before it",
            "abcd",
            vec![(1, 3, "X"), (1, 1, "i")],
            Out::Fixed("aiXd"),
        ),
        (
            "an insertion at a replacement's end goes after it",
            "abcd",
            vec![(3, 3, "i"), (1, 3, "X")],
            Out::Fixed("aXid"),
        ),
        (
            "insertions around a replacement",
            "abcd",
            vec![(3, 3, "r"), (1, 3, "X"), (1, 1, "l")],
            Out::Fixed("alXrd"),
        ),
        (
            "an edit given twice applies once",
            "abc",
            vec![(1, 1, "x"), (1, 1, "x")],
            Out::Fixed("axbc"),
        ),
        (
            "a replacement given twice applies once",
            "abc",
            vec![(0, 1, "x"), (2, 3, "y"), (0, 1, "x")],
            Out::Fixed("xby"),
        ),
        (
            "a multi-byte replacement",
            "日本語",
            vec![(3, 6, "x")],
            Out::Fixed("日x語"),
        ),
        (
            "an insertion between scalars",
            "日本",
            vec![(3, 3, "x")],
            Out::Fixed("日x本"),
        ),
        (
            "replacement text with line breaks",
            "ab",
            vec![(1, 1, "\n\n")],
            Out::Fixed("a\n\nb"),
        ),
        (
            "CRLF stays as it is around an edit",
            "a\r\nb\r\n",
            vec![(1, 1, ";"), (4, 4, ";")],
            Out::Fixed("a;\r\nb;\r\n"),
        ),
        (
            "a BOM stays",
            "\u{FEFF}ab",
            vec![(3, 3, "x")],
            Out::Fixed("\u{FEFF}xab"),
        ),
        (
            "two replacements overlap",
            "abcdef",
            vec![(1, 4, "X"), (3, 5, "Y")],
            Out::Overlap((1, 4, "X"), (3, 5, "Y")),
        ),
        (
            "the conflict is reported in sorted order",
            "abcdef",
            vec![(3, 5, "Y"), (1, 4, "X")],
            Out::Overlap((1, 4, "X"), (3, 5, "Y")),
        ),
        (
            "one replacement inside another",
            "abcdef",
            vec![(0, 6, "X"), (2, 3, "Y")],
            Out::Overlap((0, 6, "X"), (2, 3, "Y")),
        ),
        (
            "the same span with different text",
            "abc",
            vec![(0, 1, "X"), (0, 1, "Y")],
            Out::Overlap((0, 1, "X"), (0, 1, "Y")),
        ),
        (
            "the same start with different ends",
            "abc",
            vec![(0, 2, "X"), (0, 1, "Y")],
            Out::Overlap((0, 1, "Y"), (0, 2, "X")),
        ),
        (
            "an insertion strictly inside a replacement",
            "abcd",
            vec![(0, 4, "X"), (2, 2, "i")],
            Out::Overlap((0, 4, "X"), (2, 2, "i")),
        ),
        (
            "two different insertions at one place have no defined order",
            "abc",
            vec![(1, 1, "x"), (1, 1, "y")],
            Out::Overlap((1, 1, "x"), (1, 1, "y")),
        ),
        (
            "a conflict later in the list is still found",
            "abcdefgh",
            vec![(0, 1, "a"), (6, 7, "b"), (2, 3, "c"), (6, 8, "d")],
            Out::Overlap((6, 7, "b"), (6, 8, "d")),
        ),
        (
            "a span past the end",
            "abc",
            vec![(1, 2, "ok"), (2, 4, "x")],
            Out::Invalid((2, 4, "x")),
        ),
        (
            "a start past the end",
            "abc",
            vec![(4, 4, "x")],
            Out::Invalid((4, 4, "x")),
        ),
        (
            "an inverted span",
            "abc",
            vec![(2, 1, "x")],
            Out::Invalid((2, 1, "x")),
        ),
        (
            "a start inside a scalar",
            "日本",
            vec![(1, 3, "x")],
            Out::Invalid((1, 3, "x")),
        ),
        (
            "an end inside a scalar",
            "日本",
            vec![(0, 4, "x")],
            Out::Invalid((0, 4, "x")),
        ),
        (
            "an insertion inside a scalar",
            "日本",
            vec![(2, 2, "x")],
            Out::Invalid((2, 2, "x")),
        ),
        (
            "an invalid span is found before an overlap",
            "abc",
            vec![(0, 2, "x"), (1, 2, "y"), (9, 9, "z")],
            Out::Invalid((9, 9, "z")),
        ),
    ];
    for (name, text, list, out) in rows {
        h.case(format!("fixes/{name}"), move || check(text, &list, out));
    }
}

fn others(h: &mut Harness) {
    h.case(
        "fixes/positions are global and `base` places the text",
        || {
            let src = Src::files(&[("a.en", "first\n"), ("b.en", "abc")]);
            let b = src.f(1);
            let fixed = apply_fixes(&b.text, b.base(), &[Edit::replace(b.find("b"), "X")]);
            assert_eq!(fixed, Ok("aXc".to_owned()));
        },
    );
    h.case("fixes/an edit of another file is invalid", || {
        let src = Src::files(&[("a.en", "first\n"), ("b.en", "abc")]);
        let edit = Edit::replace(src.f(0).find("first"), "x");
        let b = src.f(1);
        assert_eq!(
            apply_fixes(&b.text, b.base(), std::slice::from_ref(&edit)),
            Err(FixConflict::InvalidSpan { edit })
        );
    });
    // The text starts at 10, so these reach before it, where the subtraction that
    // turns a position into an offset has nothing to subtract from.
    let before_the_text: &[(&str, u32, u32)] = &[
        ("a start before the text", 5, 11),
        ("an end before the text", 10, 5),
        ("both ends before the text", 5, 7),
        ("an inverted span below the text", 7, 5),
        ("an insertion before the text", 5, 5),
    ];
    for &(name, lo, hi) in before_the_text {
        h.case(format!("fixes/{name}"), move || {
            let edit = Edit::replace(
                Span {
                    lo: BytePos(lo),
                    hi: BytePos(hi),
                },
                "x",
            );
            assert_eq!(
                apply_fixes("abc", BytePos(10), std::slice::from_ref(&edit)),
                Err(FixConflict::InvalidSpan { edit })
            );
        });
    }
    h.case("fixes/a command is not a source edit", || {
        let edit = Edit::command("enrang run");
        assert_eq!(
            apply_fixes("abc", BytePos(0), std::slice::from_ref(&edit)),
            Err(FixConflict::InvalidSpan { edit })
        );
    });
    h.case("fixes/the conflict's message names the spans", || {
        let first = Edit::replace(
            Span {
                lo: BytePos(1),
                hi: BytePos(4),
            },
            "X",
        );
        let second = Edit::replace(
            Span {
                lo: BytePos(3),
                hi: BytePos(5),
            },
            "Y",
        );
        let conflict = FixConflict::Overlap { first, second };
        assert_eq!(
            conflict.to_string(),
            "the edit at 1..4 conflicts with the edit at 3..5"
        );
        let invalid = FixConflict::InvalidSpan {
            edit: Edit::command("x"),
        };
        assert_eq!(
            invalid.to_string(),
            "the edit at 0..0 does not fit this text"
        );
    });
    h.case("fixes/delete and insert build the edits they say", || {
        let span = Span {
            lo: BytePos(2),
            hi: BytePos(3),
        };
        assert_eq!(Edit::delete(span).replacement, "");
        assert_eq!(Edit::delete(span).span, span);
        let insert = Edit::insert(BytePos(9), "x");
        assert_eq!(insert.span.lo, insert.span.hi);
        assert_eq!(insert.span.lo, BytePos(9));
        assert!(Edit::command("c").span.is_dummy());
    });
}

pub fn register(h: &mut Harness) {
    table(h);
    others(h);
}
