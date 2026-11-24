//! Dense, fixed-domain bit sets over typed indices.
//!
//! Indices at or past the domain panic, even when the backing word has room for
//! them. Bits past the domain are always zero, so counts, equality and subset
//! tests can work on whole words.

use std::fmt;
use std::marker::PhantomData;
use std::ops::Range;

use crate::index::Idx;

const WORD_BITS: usize = 64;

fn locate(bit: usize) -> (usize, u64) {
    (bit / WORD_BITS, 1 << (bit % WORD_BITS))
}

fn set_bit(word: &mut u64, mask: u64) -> bool {
    let changed = *word & mask == 0;
    *word |= mask;
    changed
}

fn clear_bit(word: &mut u64, mask: u64) -> bool {
    let changed = *word & mask != 0;
    *word &= !mask;
    changed
}

fn count_bits(words: &[u64]) -> usize {
    words.iter().map(|w| w.count_ones() as usize).sum()
}

/// The positions of the set bits of `words`, ascending.
fn set_bits(words: &[u64]) -> impl Iterator<Item = usize> {
    words.iter().enumerate().flat_map(|(i, &word)| {
        let mut rest = word;
        std::iter::from_fn(move || {
            if rest == 0 {
                return None;
            }
            let bit = rest.trailing_zeros() as usize;
            rest &= rest - 1;
            Some(i * WORD_BITS + bit)
        })
    })
}

/// Applies `op` word by word and reports whether any word changed.
fn combine(dst: &mut [u64], src: &[u64], op: impl Fn(u64, u64) -> u64) -> bool {
    let mut changed = false;
    for (d, &s) in dst.iter_mut().zip(src) {
        let merged = op(*d, s);
        changed |= merged != *d;
        *d = merged;
    }
    changed
}

/// A set of indices below a fixed domain size.
#[derive(Clone, PartialEq, Eq)]
pub struct BitSet<I: Idx> {
    domain: usize,
    words: Vec<u64>,
    _index: PhantomData<fn() -> I>,
}

impl<I: Idx> BitSet<I> {
    /// An empty set over indices `0..domain`.
    pub fn new(domain: usize) -> Self {
        BitSet {
            domain,
            words: vec![0; domain.div_ceil(WORD_BITS)],
            _index: PhantomData,
        }
    }

    /// The set of all indices `0..domain`.
    pub fn full(domain: usize) -> Self {
        let mut set = Self::new(domain);
        set.insert_all();
        set
    }

    pub fn domain_size(&self) -> usize {
        self.domain
    }

    /// The number of indices in the set.
    pub fn count(&self) -> usize {
        count_bits(&self.words)
    }

    pub fn is_empty(&self) -> bool {
        self.words.iter().all(|&w| w == 0)
    }

    fn slot(&self, index: I) -> (usize, u64) {
        let bit = index.index();
        assert!(bit < self.domain, "bit {bit} out of domain {}", self.domain);
        locate(bit)
    }

    pub fn contains(&self, index: I) -> bool {
        let (word, mask) = self.slot(index);
        self.words[word] & mask != 0
    }

    /// Returns whether the set changed.
    pub fn insert(&mut self, index: I) -> bool {
        let (word, mask) = self.slot(index);
        set_bit(&mut self.words[word], mask)
    }

    /// Returns whether the set changed.
    pub fn remove(&mut self, index: I) -> bool {
        let (word, mask) = self.slot(index);
        clear_bit(&mut self.words[word], mask)
    }

    pub fn clear(&mut self) {
        self.words.fill(0);
    }

    pub fn insert_all(&mut self) {
        self.words.fill(u64::MAX);
        let tail = self.domain % WORD_BITS;
        if tail != 0 {
            let last = self.words.len() - 1;
            self.words[last] = (1 << tail) - 1;
        }
    }

    fn same_domain(&self, other: &Self) {
        assert_eq!(self.domain, other.domain, "bit set domains differ");
    }

    /// Adds every index of `other`. Returns whether the set changed.
    pub fn union(&mut self, other: &Self) -> bool {
        self.same_domain(other);
        combine(&mut self.words, &other.words, |a, b| a | b)
    }

    /// Keeps only indices also in `other`. Returns whether the set changed.
    pub fn intersect(&mut self, other: &Self) -> bool {
        self.same_domain(other);
        combine(&mut self.words, &other.words, |a, b| a & b)
    }

    /// Removes every index of `other`. Returns whether the set changed.
    pub fn subtract(&mut self, other: &Self) -> bool {
        self.same_domain(other);
        combine(&mut self.words, &other.words, |a, b| a & !b)
    }

    pub fn is_subset(&self, other: &Self) -> bool {
        self.same_domain(other);
        self.words
            .iter()
            .zip(&other.words)
            .all(|(a, b)| a & !b == 0)
    }

    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.same_domain(other);
        self.words.iter().zip(&other.words).all(|(a, b)| a & b == 0)
    }

    /// The indices in the set, ascending.
    pub fn iter(&self) -> impl Iterator<Item = I> {
        set_bits(&self.words).map(I::new)
    }
}

impl<I: Idx> fmt::Debug for BitSet<I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(set_bits(&self.words)).finish()
    }
}

/// A dense `rows` by `cols` matrix of bits.
#[derive(Clone, PartialEq, Eq)]
pub struct BitMatrix<R: Idx, C: Idx> {
    rows: usize,
    cols: usize,
    words_per_row: usize,
    words: Vec<u64>,
    _index: PhantomData<fn() -> (R, C)>,
}

impl<R: Idx, C: Idx> BitMatrix<R, C> {
    /// An all-zero matrix.
    pub fn new(rows: usize, cols: usize) -> Self {
        let words_per_row = cols.div_ceil(WORD_BITS);
        let total = rows
            .checked_mul(words_per_row)
            .expect("bit matrix size overflows usize");
        BitMatrix {
            rows,
            cols,
            words_per_row,
            words: vec![0; total],
            _index: PhantomData,
        }
    }

    pub fn rows(&self) -> usize {
        self.rows
    }

    pub fn cols(&self) -> usize {
        self.cols
    }

    fn row_range(&self, row: R) -> Range<usize> {
        let row = row.index();
        assert!(row < self.rows, "row {row} out of {} rows", self.rows);
        let start = row * self.words_per_row;
        start..start + self.words_per_row
    }

    fn slot(&self, row: R, col: C) -> (usize, u64) {
        let start = self.row_range(row).start;
        let col = col.index();
        assert!(col < self.cols, "column {col} out of {} columns", self.cols);
        let (word, mask) = locate(col);
        (start + word, mask)
    }

    pub fn contains(&self, row: R, col: C) -> bool {
        let (word, mask) = self.slot(row, col);
        self.words[word] & mask != 0
    }

    /// Returns whether the matrix changed.
    pub fn insert(&mut self, row: R, col: C) -> bool {
        let (word, mask) = self.slot(row, col);
        set_bit(&mut self.words[word], mask)
    }

    /// Returns whether the matrix changed.
    pub fn remove(&mut self, row: R, col: C) -> bool {
        let (word, mask) = self.slot(row, col);
        clear_bit(&mut self.words[word], mask)
    }

    pub fn clear_row(&mut self, row: R) {
        let range = self.row_range(row);
        self.words[range].fill(0);
    }

    /// The number of set bits in the whole matrix.
    pub fn count(&self) -> usize {
        count_bits(&self.words)
    }

    pub fn count_row(&self, row: R) -> usize {
        count_bits(&self.words[self.row_range(row)])
    }

    /// The columns set in `row`, ascending.
    pub fn iter_row(&self, row: R) -> impl Iterator<Item = C> {
        set_bits(&self.words[self.row_range(row)]).map(C::new)
    }

    /// Adds the bits of row `src` to row `dst`. Returns whether `dst` changed.
    pub fn union_rows(&mut self, src: R, dst: R) -> bool {
        let src = self.row_range(src);
        let dst = self.row_range(dst);
        let mut changed = false;
        for (s, d) in src.zip(dst) {
            let merged = self.words[d] | self.words[s];
            changed |= merged != self.words[d];
            self.words[d] = merged;
        }
        changed
    }

    /// Adds the columns of `set` to row `dst`. Returns whether `dst` changed.
    pub fn union_row_with(&mut self, set: &BitSet<C>, dst: R) -> bool {
        assert_eq!(set.domain, self.cols, "bit set domain differs from columns");
        let dst = self.row_range(dst);
        combine(&mut self.words[dst], &set.words, |a, b| a | b)
    }

    /// A copy of `row` as a set of columns.
    pub fn row_set(&self, row: R) -> BitSet<C> {
        BitSet {
            domain: self.cols,
            words: self.words[self.row_range(row)].to_vec(),
            _index: PhantomData,
        }
    }
}

impl<R: Idx, C: Idx> fmt::Debug for BitMatrix<R, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BitMatrix({}x{}) ", self.rows, self.cols)?;
        let per_row = self.words_per_row.max(1);
        let rows = self.words.chunks(per_row).enumerate();
        let bits = rows.flat_map(|(r, row)| set_bits(row).map(move |c| (r, c)));
        f.debug_set().entries(bits).finish()
    }
}
