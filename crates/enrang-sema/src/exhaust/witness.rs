//! Witnesses (plan d.13): the values no row of a matrix matches, which EN0501
//! names. This is Maranget's `U(P, _)` with witness reconstruction: a complete
//! signature (every case of an enum, both booleans, `null` and `Present` of a
//! nullable) splits into its constructors, each specialised; an incomplete one
//! takes the default matrix, whose witnesses are the constructors missing from
//! the rows, or, for numbers, strings and other types, which no list completes,
//! one value no row names.

use std::collections::BTreeSet;

use super::matrix::{Pat, Space, float_key, has_wild, ranges, specialize_present, uncovered_in};

/// A value no row matches: a missing constructor with its field, or, for the
/// types no list completes, one value no row names.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Witness {
    Null,
    Present(Box<Witness>),
    Case(u32),
    Bool(bool),
    Int(i128),
    /// A float's bits.
    Float(u64),
    Str(String),
    /// A value of a type whose values no arm can name.
    Other,
}

impl Witness {
    /// The witness under its `Present` wrappers, with how many there are.
    pub(crate) fn peel(&self) -> (&Witness, usize) {
        let mut at = self;
        let mut depth = 0;
        while let Witness::Present(inner) = at {
            at = inner;
            depth += 1;
        }
        (at, depth)
    }
}

/// Whether `pat` matches the value `w`.
pub(crate) fn matches(pat: &Pat, w: &Witness) -> bool {
    match (pat, w) {
        (Pat::Wild, _) => true,
        (Pat::Null, Witness::Null) => true,
        (Pat::Present(p), Witness::Present(v)) => matches(p, v),
        (Pat::Case(a), Witness::Case(b)) => a == b,
        (Pat::Bool(a), Witness::Bool(b)) => a == b,
        (Pat::Range(lo, hi), Witness::Int(v)) => lo <= v && v < hi,
        (Pat::Float(key), Witness::Float(bits)) => float_key(f64::from_bits(*bits)) == Some(*key),
        (Pat::Str(a), Witness::Str(b)) => a == b,
        _ => false,
    }
}

/// Every value of `space` no row of `rows` matches, in the order EN0501 reports
/// them: a nullable's present values before its `null` (the order `T | null`
/// is written in), cases in declaration order, `true` before `false`. Of the
/// values of a type no list completes, one stands for all.
pub(crate) fn missing(rows: &[&Pat], space: &Space) -> Vec<Witness> {
    // A `default` row: D(P) holds a row with no column, so nothing is missing.
    if has_wild(rows) {
        return Vec::new();
    }
    match space {
        // Complete signatures: each constructor, specialised.
        Space::Nullable(inner) => {
            let mut out: Vec<Witness> = missing(&specialize_present(rows), inner)
                .into_iter()
                .map(|w| Witness::Present(Box::new(w)))
                .collect();
            if !rows.contains(&&Pat::Null) {
                out.push(Witness::Null);
            }
            out
        }
        Space::Enum(n) => (0..*n)
            .filter(|c| !rows.contains(&&Pat::Case(*c)))
            .map(Witness::Case)
            .collect(),
        Space::Bool => [true, false]
            .into_iter()
            .filter(|b| !rows.contains(&&Pat::Bool(*b)))
            .map(Witness::Bool)
            .collect(),
        // Incomplete signatures with no `default` row: D(P) is empty, so a value
        // no row names is a witness.
        Space::Int => vec![fresh_int(&ranges(rows))],
        Space::Float => vec![fresh_float(rows)],
        Space::Str => vec![fresh_str(rows)],
        Space::Opaque => vec![Witness::Other],
    }
}

/// An integer no range holds: `0`, or the end of the merged range holding it,
/// which the merge leaves uncovered.
fn fresh_int(merged: &[(i128, i128)]) -> Witness {
    if let Some(v) = uncovered_in(merged, 0, i128::MAX) {
        return Witness::Int(v);
    }
    match uncovered_in(merged, i128::MIN, 0) {
        Some(v) => Witness::Int(v),
        None => Witness::Other,
    }
}

/// The first of `0.0, 1.0, 2.0, ...` no row names.
fn fresh_float(rows: &[&Pat]) -> Witness {
    let named: BTreeSet<u64> = rows
        .iter()
        .filter_map(|row| match row {
            Pat::Float(key) => Some(*key),
            _ => None,
        })
        .collect();
    let mut value = 0.0f64;
    while float_key(value).is_some_and(|key| named.contains(&key)) {
        value += 1.0;
    }
    Witness::Float(value.to_bits())
}

/// The first of `""`, `"_"`, `"__"`, ... no row names.
fn fresh_str(rows: &[&Pat]) -> Witness {
    let named: BTreeSet<&str> = rows
        .iter()
        .filter_map(|row| match row {
            Pat::Str(text) => Some(text.as_str()),
            _ => None,
        })
        .collect();
    let mut text = String::new();
    while named.contains(text.as_str()) {
        text.push('_');
    }
    Witness::Str(text)
}
