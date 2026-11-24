//! `BitMatrix`, concentrating on word boundaries within and between rows.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;
use std::panic::{AssertUnwindSafe, catch_unwind};

use enrang_base::{BitMatrix, BitSet, Idx};

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
struct R(u32);

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
struct C(u32);

impl Idx for R {
    fn new(i: usize) -> Self {
        R(i as u32)
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

impl Idx for C {
    fn new(i: usize) -> Self {
        C(i as u32)
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

type Matrix = BitMatrix<R, C>;

/// Columns, the two operands, the expected row and whether the destination changes.
type UnionCase = (
    usize,
    &'static [u32],
    &'static [u32],
    &'static [usize],
    bool,
);

const COLS: &[usize] = &[1, 2, 63, 64, 65, 127, 128, 129, 193];

fn edge_cols(cols: usize) -> Vec<usize> {
    let candidates = [0, 1, 62, 63, 64, 65, 126, 127, 128, 129, 192, cols - 1];
    let unique: BTreeSet<usize> = candidates.into_iter().filter(|&c| c < cols).collect();
    unique.into_iter().collect()
}

fn row_of(matrix: &Matrix, row: u32) -> Vec<usize> {
    matrix.iter_row(R(row)).map(|c| c.index()).collect()
}

fn set_of(cols: usize, members: &[u32]) -> BitSet<C> {
    let mut set = BitSet::new(cols);
    for &c in members {
        set.insert(C(c));
    }
    set
}

fn matrix_with(rows: usize, cols: usize, bits: &[(u32, u32)]) -> Matrix {
    let mut matrix = Matrix::new(rows, cols);
    for &(r, c) in bits {
        matrix.insert(R(r), C(c));
    }
    matrix
}

fn panics(f: impl FnOnce()) -> bool {
    catch_unwind(AssertUnwindSafe(f)).is_err()
}

#[test]
fn new_is_all_zero_table() {
    for &cols in COLS {
        for rows in [1, 2, 3] {
            let matrix = Matrix::new(rows, cols);
            assert_eq!((matrix.rows(), matrix.cols()), (rows, cols));
            assert_eq!(matrix.count(), 0);
            for r in 0..rows as u32 {
                assert_eq!(matrix.count_row(R(r)), 0);
                assert_eq!(matrix.iter_row(R(r)).count(), 0);
                assert!((0..cols as u32).all(|c| !matrix.contains(R(r), C(c))));
            }
        }
    }
}

#[test]
fn zero_sized_matrices_work() {
    let no_rows = Matrix::new(0, 64);
    assert_eq!(
        (no_rows.rows(), no_rows.cols(), no_rows.count()),
        (0, 64, 0)
    );
    assert!(panics(|| {
        no_rows.contains(R(0), C(0));
    }));

    let no_cols = Matrix::new(3, 0);
    assert_eq!((no_cols.rows(), no_cols.cols(), no_cols.count()), (3, 0, 0));
    assert_eq!(no_cols.iter_row(R(2)).count(), 0);
    assert_eq!(no_cols.count_row(R(2)), 0);
    assert!(
        panics(|| {
            no_cols.count_row(R(3));
        }),
        "count_row checks rows"
    );
    assert!(
        panics(|| {
            let _ = no_cols.iter_row(R(3));
        }),
        "iter_row checks rows"
    );
    assert!(panics(|| {
        no_cols.contains(R(0), C(0));
    }));

    let neither = Matrix::new(0, 0);
    assert_eq!((neither.rows(), neither.cols(), neither.count()), (0, 0, 0));
    assert_eq!(format!("{neither:?}"), "BitMatrix(0x0) {}");
}

#[test]
#[should_panic(expected = "bit matrix size overflows usize")]
fn absurd_sizes_are_refused() {
    Matrix::new(usize::MAX, 65);
}

#[test]
fn insert_and_remove_report_change_at_edges() {
    for &cols in COLS {
        for rows in [1u32, 2, 3] {
            let mut matrix = Matrix::new(rows as usize, cols);
            let row = R(rows - 1);
            for c in edge_cols(cols) {
                let col = C(c as u32);
                assert!(!matrix.contains(row, col));
                assert!(!matrix.remove(row, col), "remove absent {c} of {cols}");
                assert!(matrix.insert(row, col), "first insert {c} of {cols}");
                assert!(matrix.contains(row, col));
                assert!(!matrix.insert(row, col), "second insert {c} of {cols}");
                assert!(matrix.remove(row, col), "remove present {c} of {cols}");
                assert!(!matrix.contains(row, col));
            }
            assert_eq!(matrix.count(), 0);
        }
    }
}

#[test]
fn a_single_bit_touches_only_itself() {
    // Scans the whole matrix, so a bit bleeding into the next word or the next
    // row is caught for every width around a word boundary.
    for &cols in COLS {
        let rows = 3;
        for c in edge_cols(cols) {
            for r in 0..rows as u32 {
                let matrix = matrix_with(rows, cols, &[(r, c as u32)]);
                assert_eq!(matrix.count(), 1, "({r}, {c}) of {cols}");
                for other_r in 0..rows as u32 {
                    let expected = if other_r == r { vec![c] } else { vec![] };
                    assert_eq!(row_of(&matrix, other_r), expected, "({r}, {c}) of {cols}");
                    for other_c in 0..cols {
                        let is_it = other_r == r && other_c == c;
                        assert_eq!(matrix.contains(R(other_r), C(other_c as u32)), is_it);
                    }
                }
            }
        }
    }
}

#[test]
fn the_last_column_of_a_row_is_not_the_first_of_the_next() {
    for cols in [63u32, 64, 65, 128] {
        let matrix = matrix_with(2, cols as usize, &[(0, cols - 1)]);
        assert!(matrix.contains(R(0), C(cols - 1)));
        assert!(!matrix.contains(R(1), C(0)), "{cols} columns");
    }
}

#[test]
fn rows_past_the_end_panic() {
    for &cols in COLS {
        for rows in [0usize, 1, 2] {
            let mut matrix = Matrix::new(rows, cols);
            let row = R(rows as u32);
            assert!(
                panics(|| {
                    matrix.contains(row, C(0));
                }),
                "contains {rows}x{cols}"
            );
            assert!(
                panics(|| {
                    matrix.insert(row, C(0));
                }),
                "insert {rows}x{cols}"
            );
            assert!(
                panics(|| {
                    matrix.remove(row, C(0));
                }),
                "remove {rows}x{cols}"
            );
            assert!(
                panics(|| {
                    matrix.clear_row(row);
                }),
                "clear_row {rows}x{cols}"
            );
            assert!(
                panics(|| {
                    matrix.count_row(row);
                }),
                "count_row {rows}x{cols}"
            );
            assert!(
                panics(|| {
                    matrix.row_set(row);
                }),
                "row_set {rows}x{cols}"
            );
            assert!(
                panics(|| {
                    let _ = matrix.iter_row(row);
                }),
                "iter_row {rows}x{cols}"
            );
        }
    }
}

#[test]
fn columns_past_the_end_panic_even_inside_the_last_word() {
    for (cols, col) in [
        (1u32, 1),
        (63, 63),
        (64, 64),
        (65, 65),
        (65, 127),
        (127, 127),
        (128, 128),
    ] {
        // Two rows, so a stray column cannot run off the backing store instead.
        let mut matrix = Matrix::new(2, cols as usize);
        assert!(
            panics(|| {
                matrix.contains(R(0), C(col));
            }),
            "contains {col} of {cols}"
        );
        assert!(
            panics(|| {
                matrix.insert(R(0), C(col));
            }),
            "insert {col} of {cols}"
        );
        assert!(
            panics(|| {
                matrix.remove(R(0), C(col));
            }),
            "remove {col} of {cols}"
        );
        assert_eq!(matrix.count(), 0);
    }
}

#[test]
fn iter_row_is_ascending_across_words() {
    let bits = [(1, 128), (1, 0), (1, 64), (1, 63), (1, 192), (0, 5), (2, 7)];
    let matrix = matrix_with(3, 193, &bits);
    assert_eq!(row_of(&matrix, 1), [0, 63, 64, 128, 192]);
    assert_eq!(row_of(&matrix, 0), [5]);
    assert_eq!(row_of(&matrix, 2), [7]);
}

#[test]
fn counts_table() {
    type CountCase = (usize, &'static [(u32, u32)], [usize; 3]);
    let cases: &[CountCase] = &[
        (64, &[], [0, 0, 0]),
        (64, &[(0, 63)], [1, 0, 0]),
        (65, &[(0, 63), (0, 64)], [2, 0, 0]),
        (65, &[(1, 64), (2, 0)], [0, 1, 1]),
        (129, &[(0, 0), (0, 64), (0, 128), (2, 128)], [3, 0, 1]),
        (129, &[(1, 128), (1, 128)], [0, 1, 0]),
    ];
    for &(cols, bits, expected) in cases {
        let matrix = matrix_with(3, cols, bits);
        let per_row = [0, 1, 2].map(|r| matrix.count_row(R(r)));
        assert_eq!(per_row, expected, "{bits:?}");
        assert_eq!(matrix.count(), expected.iter().sum::<usize>(), "{bits:?}");
    }
}

#[test]
fn clear_row_clears_only_that_row() {
    for cols in [63u32, 64, 65, 129] {
        let last = cols - 1;
        let mut matrix = matrix_with(3, cols as usize, &[(0, last), (1, 0), (1, last), (2, 0)]);
        matrix.clear_row(R(1));
        assert_eq!(row_of(&matrix, 0), [last as usize], "{cols} columns");
        assert_eq!(row_of(&matrix, 1), [] as [usize; 0], "{cols} columns");
        assert_eq!(row_of(&matrix, 2), [0], "{cols} columns");
    }
}

#[test]
fn union_rows_table() {
    let cases: &[UnionCase] = &[
        (64, &[], &[], &[], false),
        (64, &[], &[63], &[63], false),
        (64, &[63], &[], &[63], true),
        (64, &[63], &[63], &[63], false),
        (65, &[64], &[63], &[63, 64], true),
        (65, &[63], &[64], &[63, 64], true),
        (65, &[63, 64], &[63, 64], &[63, 64], false),
        (129, &[0, 128], &[64], &[0, 64, 128], true),
        (129, &[128], &[0, 64, 128], &[0, 64, 128], false),
    ];
    for &(cols, src, dst, expected, changed) in cases {
        let bystander = (2, 1);
        let mut bits: Vec<(u32, u32)> = vec![bystander];
        bits.extend(src.iter().map(|&c| (0, c)));
        bits.extend(dst.iter().map(|&c| (1, c)));
        let mut matrix = matrix_with(3, cols, &bits);
        assert_eq!(
            matrix.union_rows(R(0), R(1)),
            changed,
            "{src:?} into {dst:?}"
        );
        assert_eq!(row_of(&matrix, 1), expected, "{src:?} into {dst:?}");
        let src_after: Vec<usize> = src.iter().map(|&c| c as usize).collect();
        assert_eq!(row_of(&matrix, 0), src_after, "the source is left alone");
        assert_eq!(row_of(&matrix, 2), [1], "other rows are left alone");
        assert!(
            !matrix.union_rows(R(0), R(1)),
            "a second union changes nothing"
        );
    }
}

#[test]
fn union_rows_works_towards_a_lower_row() {
    let mut matrix = matrix_with(3, 65, &[(2, 64), (0, 0)]);
    assert!(matrix.union_rows(R(2), R(0)));
    assert_eq!(row_of(&matrix, 0), [0, 64]);
    assert_eq!(row_of(&matrix, 2), [64]);
}

#[test]
fn union_of_a_row_with_itself_changes_nothing() {
    let mut matrix = matrix_with(2, 65, &[(1, 64), (1, 3)]);
    assert!(!matrix.union_rows(R(1), R(1)));
    assert_eq!(row_of(&matrix, 1), [3, 64]);
}

#[test]
fn union_rows_panics_on_bad_rows() {
    let mut matrix = Matrix::new(2, 64);
    assert!(
        panics(|| {
            matrix.union_rows(R(2), R(0));
        }),
        "bad source"
    );
    assert!(
        panics(|| {
            matrix.union_rows(R(0), R(2));
        }),
        "bad destination"
    );
}

#[test]
fn union_row_with_table() {
    let cases: &[UnionCase] = &[
        (64, &[], &[], &[], false),
        (64, &[63], &[], &[63], true),
        (64, &[63], &[63], &[63], false),
        (65, &[64], &[63], &[63, 64], true),
        (65, &[63], &[63, 64], &[63, 64], false),
        (129, &[0, 64, 128], &[1], &[0, 1, 64, 128], true),
    ];
    for &(cols, set, row, expected, changed) in cases {
        let bits: Vec<(u32, u32)> = row.iter().map(|&c| (1, c)).collect();
        let mut matrix = matrix_with(3, cols, &bits);
        let set = set_of(cols, set);
        assert_eq!(
            matrix.union_row_with(&set, R(1)),
            changed,
            "{set:?} into {row:?}"
        );
        assert_eq!(row_of(&matrix, 1), expected, "{set:?} into {row:?}");
        assert_eq!(matrix.count_row(R(0)), 0, "row 0 is left alone");
        assert_eq!(matrix.count_row(R(2)), 0, "row 2 is left alone");
    }
}

#[test]
fn union_row_with_panics_on_a_set_of_another_domain() {
    // 63 and 64 columns use one word per row, so only a domain check catches this.
    for (cols, domain) in [(64, 63), (63, 64), (65, 64), (64, 65)] {
        let mut matrix = Matrix::new(1, cols);
        let set = BitSet::new(domain);
        assert!(
            panics(|| {
                matrix.union_row_with(&set, R(0));
            }),
            "{cols} {domain}"
        );
    }
}

#[test]
fn row_set_copies_a_row() {
    let mut matrix = matrix_with(3, 129, &[(1, 0), (1, 64), (1, 128), (0, 9), (2, 8)]);
    let mut set = matrix.row_set(R(1));
    assert_eq!(set, set_of(129, &[0, 64, 128]));
    assert_eq!(set.domain_size(), 129);
    set.remove(C(64));
    assert!(matrix.contains(R(1), C(64)), "the copy is independent");
    matrix.insert(R(1), C(5));
    assert!(!set.contains(C(5)), "the copy is independent");
}

#[test]
fn row_set_and_union_row_with_round_trip() {
    let source = matrix_with(
        2,
        193,
        &[(0, 0), (0, 63), (0, 64), (0, 127), (0, 128), (0, 192)],
    );
    let mut target = Matrix::new(2, 193);
    assert!(target.union_row_with(&source.row_set(R(0)), R(1)));
    assert_eq!(row_of(&target, 1), row_of(&source, 0));
    assert_eq!(target.count_row(R(0)), 0);
}

#[test]
fn equality_requires_the_same_shape() {
    // Both shapes use two words, so comparing only the words would call them equal.
    assert_ne!(Matrix::new(2, 64), Matrix::new(1, 128));
    assert_ne!(Matrix::new(1, 63), Matrix::new(1, 64));
    assert_ne!(Matrix::new(1, 64), Matrix::new(2, 64));
    assert_ne!(Matrix::new(0, 64), Matrix::new(0, 65));
    assert_ne!(Matrix::new(1, 0), Matrix::new(2, 0));
    assert_eq!(Matrix::new(2, 65), Matrix::new(2, 65));
    assert_ne!(
        matrix_with(2, 65, &[(0, 64)]),
        matrix_with(2, 65, &[(1, 64)])
    );
    assert_eq!(
        matrix_with(2, 65, &[(0, 1), (1, 64)]),
        matrix_with(2, 65, &[(1, 64), (0, 1)])
    );
}

#[test]
fn clone_is_independent() {
    let original = matrix_with(2, 65, &[(1, 64)]);
    let mut copy = original.clone();
    assert_eq!(original, copy);
    copy.remove(R(1), C(64));
    copy.insert(R(0), C(0));
    assert_eq!(row_of(&original, 1), [64]);
    assert_eq!(original.count(), 1);
    assert_eq!(row_of(&copy, 0), [0]);
}

#[test]
fn debug_lists_shape_and_bits() {
    let matrix = matrix_with(2, 65, &[(1, 64), (0, 2)]);
    assert_eq!(format!("{matrix:?}"), "BitMatrix(2x65) {(0, 2), (1, 64)}");
    assert_eq!(format!("{:?}", Matrix::new(3, 0)), "BitMatrix(3x0) {}");
}

#[test]
fn operations_agree_with_a_btree_model() {
    let mut state = 0x9E37_79B9_7F4A_7C15u64;
    let mut next = move |n: usize| {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        (state % n as u64) as usize
    };
    for &cols in COLS {
        let rows = 5;
        let mut matrix = Matrix::new(rows, cols);
        let mut model: BTreeSet<(usize, usize)> = BTreeSet::new();
        for step in 0..3_000 {
            let (r, c) = (next(rows), next(cols));
            let (row, col) = (R(r as u32), C(c as u32));
            let context = format!("step {step} ({r}, {c}) of {cols}");
            match next(8) {
                0..=2 => assert_eq!(matrix.insert(row, col), model.insert((r, c)), "{context}"),
                3 | 4 => assert_eq!(matrix.remove(row, col), model.remove(&(r, c)), "{context}"),
                5 => {
                    let src = next(rows);
                    let added: Vec<_> = model
                        .iter()
                        .filter(|&&(mr, _)| mr == src)
                        .map(|&(_, mc)| (r, mc))
                        .collect();
                    let before = model.len();
                    model.extend(added);
                    let changed = matrix.union_rows(R(src as u32), row);
                    assert_eq!(changed, model.len() != before, "{context}");
                }
                6 => {
                    matrix.clear_row(row);
                    model.retain(|&(mr, _)| mr != r);
                }
                _ => assert_eq!(
                    matrix.contains(row, col),
                    model.contains(&(r, c)),
                    "{context}"
                ),
            }
            assert_eq!(matrix.count(), model.len(), "{context}");
        }
        for r in 0..rows {
            let expected: Vec<usize> = model
                .iter()
                .filter(|&&(mr, _)| mr == r)
                .map(|&(_, mc)| mc)
                .collect();
            assert_eq!(
                row_of(&matrix, r as u32),
                expected,
                "row {r} of {cols} columns"
            );
            assert_eq!(matrix.count_row(R(r as u32)), expected.len());
        }
    }
}
