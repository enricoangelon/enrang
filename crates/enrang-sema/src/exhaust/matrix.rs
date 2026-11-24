//! Pattern matrices and Maranget's usefulness (plan d.13; A:916): the values a
//! column can hold ([`Space`]), its patterns ([`Pat`]), and `U(P, q)`, whether a
//! pattern matches a value that no row above it matches.
//!
//! Arms bind nothing and do not nest, so a matrix has one column. Its only
//! constructor with a field is `Present`, the value of a nullable that is not
//! `null` (SPEC 6), so a vector of patterns never holds more than one: `useful`
//! and `missing` (in `witness.rs`) are Maranget's algorithm on vectors of length
//! one or zero, with the specialised matrix `S(c, P)` and the default matrix
//! `D(P)` written out for each constructor.

use std::cmp::Ordering;

/// What a column can hold: the subject's type, as constructors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Space {
    /// The cases `0..n` of an enum, `Result` or a string-literal union, in
    /// declaration order: a complete signature once every case is listed.
    Enum(u32),
    /// `true` and `false`.
    Bool,
    /// Integers. Numbers and strings always need `default` (SPEC 6), so their
    /// signature is never complete, whatever the type's width: literals and
    /// ranges count only for redundancy, by interval cover (A:916).
    Int,
    Float,
    Str,
    /// Any other type: only `default` covers it.
    Opaque,
    /// `T | null`: `null`, or a present `T`.
    Nullable(Box<Space>),
}

/// One arm value as a pattern of the column.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Pat {
    /// `default`, or a condition of `match (true)` (which is always guarded).
    Wild,
    /// `null`, which always matches the outermost level (SPEC 6).
    Null,
    /// A present value of a nullable: every arm value but `null` and `default`
    /// wraps in it, once per level of `| null`.
    Present(Box<Pat>),
    Case(u32),
    Bool(bool),
    /// The integers `lo..hi`, half-open; a literal `n` is `n..n+1`. Empty when
    /// `lo >= hi`.
    Range(i128, i128),
    /// A float literal, by the key of [`float_key`].
    Float(u64),
    Str(String),
    /// Matches no value: a NaN literal, or a value that a constant subject can
    /// never equal.
    Empty,
}

/// The key of a float pattern: its bits, with `-0.0` keyed as `0.0`, since a
/// `match` compares with `==`; `None` for NaN, which equals nothing.
pub(crate) fn float_key(value: f64) -> Option<u64> {
    if value.is_nan() {
        None
    } else if value == 0.0 {
        Some(0.0f64.to_bits())
    } else {
        Some(value.to_bits())
    }
}

/// `S(Present, P)`: the rows that match a present value, each with the pattern
/// of its field; a `default` row stays a `default` row.
pub(crate) fn specialize_present<'p>(rows: &[&'p Pat]) -> Vec<&'p Pat> {
    rows.iter()
        .filter_map(|row| match row {
            Pat::Present(inner) => Some(&**inner),
            Pat::Wild => Some(&Pat::Wild),
            _ => None,
        })
        .collect()
}

/// Whether some row is `default`, which makes `D(P)` non-empty: no value is
/// left for any later pattern.
pub(crate) fn has_wild(rows: &[&Pat]) -> bool {
    rows.iter().any(|row| matches!(row, Pat::Wild))
}

/// Maranget's `U(P, q)` on one column: whether `q` matches a value of `space`
/// that no row of `rows` matches.
pub(crate) fn useful(rows: &[&Pat], q: &Pat, space: &Space) -> bool {
    match q {
        // U(P, _): some value is missing from P.
        Pat::Wild => !super::witness::missing(rows, space).is_empty(),
        Pat::Empty => false,
        // A `default` row matches every value, so `S(c, P)` holds a row with no
        // column for every constructor c, and U of that is false.
        _ if has_wild(rows) => false,
        Pat::Present(inner) => match space {
            Space::Nullable(inner_space) => useful(&specialize_present(rows), inner, inner_space),
            _ => false,
        },
        Pat::Range(lo, hi) => uncovered_in(&ranges(rows), *lo, *hi).is_some(),
        // An arity-zero constructor: `S(c, P)` is the rows whose head is `c`,
        // each with no column left, and U of that is true only when it is empty.
        Pat::Null | Pat::Case(_) | Pat::Bool(_) | Pat::Float(_) | Pat::Str(_) => !rows.contains(&q),
    }
}

/// Whether `pat` matches some value of `space` at all.
pub(crate) fn satisfiable(pat: &Pat, space: &Space) -> bool {
    useful(&[], pat, space)
}

/// The integer ranges of `rows`, sorted and merged, adjacent ones joined, empty
/// ones dropped.
pub(crate) fn ranges(rows: &[&Pat]) -> Vec<(i128, i128)> {
    let mut found: Vec<(i128, i128)> = rows
        .iter()
        .filter_map(|row| match row {
            Pat::Range(lo, hi) if lo < hi => Some((*lo, *hi)),
            _ => None,
        })
        .collect();
    found.sort_unstable();
    let mut merged: Vec<(i128, i128)> = Vec::with_capacity(found.len());
    for (lo, hi) in found {
        match merged.last_mut() {
            Some(last) if lo <= last.1 => last.1 = last.1.max(hi),
            _ => merged.push((lo, hi)),
        }
    }
    merged
}

/// The first integer of `lo..hi` that no range of `merged` holds: the interval
/// cover of A:916, which is Maranget's specialisation by the segments the rows'
/// ends split `lo..hi` into.
pub(crate) fn uncovered_in(merged: &[(i128, i128)], lo: i128, hi: i128) -> Option<i128> {
    let mut at = lo;
    for &(start, end) in merged {
        if at >= hi {
            return None;
        }
        match start.cmp(&at) {
            Ordering::Greater => return Some(at),
            Ordering::Less | Ordering::Equal => at = at.max(end),
        }
    }
    (at < hi).then_some(at)
}
