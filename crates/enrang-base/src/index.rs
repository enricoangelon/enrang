//! Typed indices and the vector they index.

use std::fmt;
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

/// A newtype usable as an index. `new` panics if `i` does not fit the type.
pub trait Idx: Copy + Ord {
    fn new(i: usize) -> Self;
    fn index(self) -> usize;
}

/// A `Vec<T>` indexed by `I` instead of `usize`.
#[derive(Clone, PartialEq, Eq)]
pub struct IdVec<I: Idx, T> {
    raw: Vec<T>,
    _index: PhantomData<fn() -> I>,
}

impl<I: Idx, T> IdVec<I, T> {
    pub fn new() -> Self {
        Vec::new().into()
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Vec::with_capacity(capacity).into()
    }

    /// `len` copies of `value`.
    pub fn from_elem(value: T, len: usize) -> Self
    where
        T: Clone,
    {
        vec![value; len].into()
    }

    /// Appends `value` and returns its index.
    pub fn push(&mut self, value: T) -> I {
        let index = self.next_index();
        self.raw.push(value);
        index
    }

    /// The index the next `push` will return.
    pub fn next_index(&self) -> I {
        I::new(self.raw.len())
    }

    pub fn len(&self) -> usize {
        self.raw.len()
    }

    pub fn is_empty(&self) -> bool {
        self.raw.is_empty()
    }

    pub fn get(&self, index: I) -> Option<&T> {
        self.raw.get(index.index())
    }

    pub fn get_mut(&mut self, index: I) -> Option<&mut T> {
        self.raw.get_mut(index.index())
    }

    /// Appends `fill()` values until `index` is in bounds. Never shrinks.
    pub fn ensure_index(&mut self, index: I, mut fill: impl FnMut() -> T) {
        let needed = index.index() + 1;
        if needed > self.raw.len() {
            self.raw.resize_with(needed, &mut fill);
        }
    }

    pub fn as_slice(&self) -> &[T] {
        &self.raw
    }

    pub fn iter(&self) -> std::slice::Iter<'_, T> {
        self.raw.iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, T> {
        self.raw.iter_mut()
    }

    pub fn iter_enumerated(&self) -> impl DoubleEndedIterator<Item = (I, &T)> + ExactSizeIterator {
        self.raw.iter().enumerate().map(|(i, v)| (I::new(i), v))
    }

    pub fn iter_enumerated_mut(
        &mut self,
    ) -> impl DoubleEndedIterator<Item = (I, &mut T)> + ExactSizeIterator {
        self.raw.iter_mut().enumerate().map(|(i, v)| (I::new(i), v))
    }

    /// All valid indices, ascending.
    pub fn indices(&self) -> impl DoubleEndedIterator<Item = I> + ExactSizeIterator + use<I, T> {
        (0..self.raw.len()).map(I::new)
    }
}

impl<I: Idx, T> Default for IdVec<I, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<I: Idx, T: fmt::Debug> fmt::Debug for IdVec<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.raw, f)
    }
}

impl<I: Idx, T> Index<I> for IdVec<I, T> {
    type Output = T;

    fn index(&self, index: I) -> &T {
        &self.raw[index.index()]
    }
}

impl<I: Idx, T> IndexMut<I> for IdVec<I, T> {
    fn index_mut(&mut self, index: I) -> &mut T {
        &mut self.raw[index.index()]
    }
}

impl<I: Idx, T> From<Vec<T>> for IdVec<I, T> {
    fn from(raw: Vec<T>) -> Self {
        IdVec {
            raw,
            _index: PhantomData,
        }
    }
}

impl<I: Idx, T> FromIterator<T> for IdVec<I, T> {
    fn from_iter<It: IntoIterator<Item = T>>(iter: It) -> Self {
        iter.into_iter().collect::<Vec<T>>().into()
    }
}

impl<I: Idx, T> IntoIterator for IdVec<I, T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.raw.into_iter()
    }
}

impl<'a, I: Idx, T> IntoIterator for &'a IdVec<I, T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.raw.iter()
    }
}

impl<'a, I: Idx, T> IntoIterator for &'a mut IdVec<I, T> {
    type Item = &'a mut T;
    type IntoIter = std::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.raw.iter_mut()
    }
}
