//! `BytePos` and `Span`.

#![forbid(unsafe_code)]

use std::collections::{BTreeSet, HashSet};

use enrang_base::{BytePos, Span};

fn sp(lo: u32, hi: u32) -> Span {
    Span {
        lo: BytePos(lo),
        hi: BytePos(hi),
    }
}

#[test]
fn span_is_eight_bytes() {
    assert_eq!(size_of::<BytePos>(), 4);
    assert_eq!(size_of::<Span>(), 8);
}

#[test]
fn dummy_is_position_zero() {
    assert_eq!(Span::DUMMY, sp(0, 0));
}

#[test]
fn is_dummy_table() {
    let cases = [
        (sp(0, 0), true),
        (sp(0, 1), false),
        (sp(1, 1), false),
        (sp(1, 2), false),
        (sp(u32::MAX, u32::MAX), false),
    ];
    for (span, expected) in cases {
        assert_eq!(span.is_dummy(), expected, "{span:?}");
    }
}

#[test]
fn is_empty_table() {
    let cases = [
        (sp(0, 0), true),
        (sp(5, 5), true),
        (sp(u32::MAX, u32::MAX), true),
        (sp(5, 6), false),
        (sp(0, 1), false),
        (sp(1, u32::MAX), false),
    ];
    for (span, expected) in cases {
        assert_eq!(span.is_empty(), expected, "{span:?}");
    }
}

#[test]
fn to_table() {
    let cases = [
        ("forward with a gap", sp(1, 3), sp(7, 9), sp(1, 9)),
        ("backward with a gap", sp(7, 9), sp(1, 3), sp(1, 9)),
        ("adjacent", sp(1, 3), sp(3, 9), sp(1, 9)),
        ("overlapping", sp(1, 5), sp(3, 9), sp(1, 9)),
        ("first contains second", sp(1, 9), sp(3, 5), sp(1, 9)),
        ("second contains first", sp(3, 5), sp(1, 9), sp(1, 9)),
        ("identical", sp(3, 5), sp(3, 5), sp(3, 5)),
        ("same start", sp(3, 5), sp(3, 9), sp(3, 9)),
        ("same end", sp(1, 9), sp(3, 9), sp(1, 9)),
        ("empty then real", sp(2, 2), sp(5, 7), sp(2, 7)),
        ("real then empty", sp(2, 4), sp(9, 9), sp(2, 9)),
        ("empty inside real", sp(2, 8), sp(4, 4), sp(2, 8)),
        ("two empties", sp(2, 2), sp(6, 6), sp(2, 6)),
        ("same empty", sp(6, 6), sp(6, 6), sp(6, 6)),
        ("upper bound", sp(1, 2), sp(9, u32::MAX), sp(1, u32::MAX)),
    ];
    for (name, a, b, expected) in cases {
        assert_eq!(a.to(b), expected, "{name}");
    }
}

#[test]
fn to_ignores_dummy_on_either_side() {
    for real in [sp(1, 1), sp(1, 2), sp(5, 90), sp(u32::MAX, u32::MAX)] {
        assert_eq!(Span::DUMMY.to(real), real, "dummy first: {real:?}");
        assert_eq!(real.to(Span::DUMMY), real, "dummy last: {real:?}");
    }
}

#[test]
fn dummy_to_dummy_is_dummy() {
    assert!(Span::DUMMY.to(Span::DUMMY).is_dummy());
}

#[test]
fn to_laws_hold_over_a_grid() {
    let mut spans = vec![Span::DUMMY];
    for lo in [1, 2, 7, 8, 30] {
        for width in [0, 1, 6, 40] {
            spans.push(sp(lo, lo + width));
        }
    }
    for &a in &spans {
        for &b in &spans {
            let hull = a.to(b);
            assert_eq!(hull, b.to(a), "symmetric: {a:?} {b:?}");
            assert_eq!(hull.to(a), hull, "absorbs left: {a:?} {b:?}");
            assert_eq!(hull.to(b), hull, "absorbs right: {a:?} {b:?}");
            assert!(hull.lo <= hull.hi, "never inverted: {a:?} {b:?}");
            for &c in &spans {
                assert_eq!(hull.to(c), a.to(b.to(c)), "associative: {a:?} {b:?} {c:?}");
            }
        }
    }
}

#[test]
fn byte_pos_adds_offsets() {
    let cases = [
        (0, 0, 0),
        (0, 7, 7),
        (5, 0, 5),
        (5, 7, 12),
        (u32::MAX - 1, 1, u32::MAX),
    ];
    for (base, offset, expected) in cases {
        assert_eq!(
            BytePos(base) + offset,
            BytePos(expected),
            "{base} + {offset}"
        );
    }
}

#[test]
fn byte_pos_orders_numerically() {
    let mut positions = vec![
        BytePos(300),
        BytePos(2),
        BytePos(u32::MAX),
        BytePos(0),
        BytePos(10),
    ];
    positions.sort();
    let expected = [
        BytePos(0),
        BytePos(2),
        BytePos(10),
        BytePos(300),
        BytePos(u32::MAX),
    ];
    assert_eq!(positions, expected);
}

#[test]
fn spans_order_by_lo_then_hi() {
    let ordered: Vec<Span> = BTreeSet::from([sp(5, 9), sp(1, 9), sp(5, 6), sp(1, 2), sp(5, 5)])
        .into_iter()
        .collect();
    assert_eq!(ordered, [sp(1, 2), sp(1, 9), sp(5, 5), sp(5, 6), sp(5, 9)]);
}

#[test]
fn spans_hash_by_value() {
    let set = HashSet::from([sp(1, 2), sp(1, 2), sp(1, 3), sp(2, 2)]);
    assert_eq!(set.len(), 3);
    assert!(set.contains(&sp(1, 3)));
    assert!(!set.contains(&sp(2, 3)));
}

#[test]
fn span_equality_compares_both_ends() {
    assert_eq!(sp(1, 2), sp(1, 2));
    assert_ne!(sp(1, 2), sp(1, 3));
    assert_ne!(sp(1, 2), sp(0, 2));
}
