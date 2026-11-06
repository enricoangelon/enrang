//! Did-you-mean.

use std::collections::BTreeMap;

/// The candidate closest to `name` by Damerau-Levenshtein distance over Unicode
/// scalars, if within `max(1, len / 3)` of it, `len` being `name`'s length.
///
/// A tie goes to the alphabetically first candidate, so the answer does not depend
/// on the order of `candidates`. An empty name has nothing to correct and an empty
/// candidate is nothing to suggest.
pub fn did_you_mean<'a>(name: &str, candidates: &[&'a str]) -> Option<&'a str> {
    let wanted: Vec<char> = name.chars().collect();
    if wanted.is_empty() {
        return None;
    }
    let limit = (wanted.len() / 3).max(1);
    let mut best: Option<(usize, &'a str)> = None;
    for &candidate in candidates {
        let chars: Vec<char> = candidate.chars().collect();
        if chars.is_empty() || chars.len().abs_diff(wanted.len()) > limit {
            continue;
        }
        let distance = damerau_levenshtein(&wanted, &chars);
        if distance <= limit && best.is_none_or(|known| (distance, candidate) < known) {
            best = Some((distance, candidate));
        }
    }
    best.map(|(_, candidate)| candidate)
}

/// The unrestricted distance: a transposed pair may also have text inserted
/// between its characters, so `ca` to `abc` is 2, not the 3 of the restricted form.
fn damerau_levenshtein(a: &[char], b: &[char]) -> usize {
    let width = b.len() + 2;
    let beyond = a.len() + b.len();
    // Row i + 1, column j + 1 holds the distance between a[..i] and b[..j]. Row 0
    // and column 0 hold `beyond`, so a transposition with no earlier match loses.
    let mut table = vec![0; (a.len() + 2) * width];
    table[0] = beyond;
    for i in 0..=a.len() {
        table[(i + 1) * width] = beyond;
        table[(i + 1) * width + 1] = i;
    }
    for j in 0..=b.len() {
        table[j + 1] = beyond;
        table[width + j + 1] = j;
    }
    let mut last_row: BTreeMap<char, usize> = BTreeMap::new();
    for i in 1..=a.len() {
        let mut last_col = 0;
        for j in 1..=b.len() {
            let row = last_row.get(&b[j - 1]).copied().unwrap_or(0);
            let col = last_col;
            let cost = usize::from(a[i - 1] != b[j - 1]);
            if cost == 0 {
                last_col = j;
            }
            let substitute = table[i * width + j] + cost;
            let insert = table[(i + 1) * width + j] + 1;
            let delete = table[i * width + j + 1] + 1;
            let transpose = table[row * width + col] + (i - row - 1) + 1 + (j - col - 1);
            table[(i + 1) * width + j + 1] = substitute.min(insert).min(delete).min(transpose);
        }
        last_row.insert(a[i - 1], i);
    }
    table[(a.len() + 1) * width + b.len() + 1]
}
