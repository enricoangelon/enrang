//! A generic greedy shrinker (TESTING 10, 14).
//!
//! A failing input is replaced by the first candidate that still fails, until
//! no candidate does. The result is a local minimum: removing or simplifying
//! any one thing makes the failure go away.

use std::iter;
use std::rc::Rc;

/// How many times [`shrink`] calls its predicate before settling for what it
/// has. A wrong [`Shrink`] impl can offer candidates forever, and a suite that
/// is already reporting a failure must not then hang.
pub const SHRINK_ATTEMPTS: usize = 100_000;

/// A value that knows how to propose simpler versions of itself.
///
/// Candidates are lazy because a large input has many, and most are never looked
/// at: the shrinker restarts from the first one that still fails. They should
/// come simplest first and must be strictly simpler than `self`.
pub trait Shrink: Sized {
    fn candidates(&self) -> Box<dyn Iterator<Item = Self> + '_>;
}

/// The simplest value reachable from `failing` for which `still_fails` holds.
/// `failing` is assumed to fail, and comes back unchanged if nothing simpler does.
pub fn shrink<T: Shrink>(failing: T, still_fails: impl FnMut(&T) -> bool) -> T {
    shrink_within(failing, SHRINK_ATTEMPTS, still_fails)
}

/// [`shrink`] with an explicit limit on calls of `still_fails`.
pub fn shrink_within<T: Shrink>(
    failing: T,
    max_attempts: usize,
    mut still_fails: impl FnMut(&T) -> bool,
) -> T {
    let mut current = failing;
    let mut attempts = 0;
    loop {
        let mut simpler = None;
        for candidate in current.candidates() {
            if attempts == max_attempts {
                break;
            }
            attempts += 1;
            if still_fails(&candidate) {
                simpler = Some(candidate);
                break;
            }
        }
        match simpler {
            Some(candidate) => current = candidate,
            None => return current,
        }
    }
}

/// `x - x/2, x - x/4, ..., x - 1`: a binary search towards zero that ends one
/// step short of `x`, so a threshold is always found exactly.
fn halving_steps<T>(x: T, zero: T, halve: fn(T) -> T, sub: fn(T, T) -> T) -> impl Iterator<Item = T>
where
    T: Copy + Eq + 'static,
{
    iter::successors(Some(halve(x)), move |&d| Some(halve(d)))
        .take_while(move |&d| d != zero)
        .map(move |d| sub(x, d))
}

macro_rules! shrink_unsigned {
    ($($t:ty)*) => {$(
        impl Shrink for $t {
            fn candidates(&self) -> Box<dyn Iterator<Item = $t> + '_> {
                let x = *self;
                if x == 0 {
                    return Box::new(iter::empty());
                }
                Box::new(iter::once(0).chain(halving_steps(x, 0, |v| v / 2, |a, b| a - b)))
            }
        }
    )*};
}

shrink_unsigned!(u8 u16 u32 u64 u128 usize);

macro_rules! shrink_signed {
    ($($t:ty)*) => {$(
        impl Shrink for $t {
            /// Towards zero, trying the positive value first: `-5` is a less
            /// surprising counterexample only if `5` does not also fail.
            fn candidates(&self) -> Box<dyn Iterator<Item = $t> + '_> {
                let x = *self;
                if x == 0 {
                    return Box::new(iter::empty());
                }
                let flip = if x < 0 { x.checked_neg() } else { None };
                Box::new(
                    iter::once(0)
                        .chain(flip)
                        .chain(halving_steps(x, 0, |v| v / 2, |a, b| a - b)),
                )
            }
        }
    )*};
}

shrink_signed!(i8 i16 i32 i64 i128 isize);

impl Shrink for bool {
    fn candidates(&self) -> Box<dyn Iterator<Item = bool> + '_> {
        Box::new((*self).then_some(false).into_iter())
    }
}

impl Shrink for char {
    fn candidates(&self) -> Box<dyn Iterator<Item = char> + '_> {
        Box::new((*self != 'a').then_some('a').into_iter())
    }
}

impl<T: Shrink + Clone> Shrink for Option<T> {
    fn candidates(&self) -> Box<dyn Iterator<Item = Option<T>> + '_> {
        match self {
            None => Box::new(iter::empty()),
            Some(inner) => Box::new(iter::once(None).chain(inner.candidates().map(Some))),
        }
    }
}

/// The runs of a sequence to try removing, as `(start, length)`: the whole of it,
/// then halves, quarters and so on down to single elements.
fn removal_runs(len: usize) -> impl Iterator<Item = (usize, usize)> {
    iter::successors(Some(len), |&run| Some(run / 2))
        .take_while(|&run| run > 0)
        .flat_map(move |run| (0..=len - run).step_by(run).map(move |start| (start, run)))
}

impl<T: Shrink + Clone> Shrink for Vec<T> {
    /// Removes runs of elements, longest first, then simplifies each element.
    fn candidates(&self) -> Box<dyn Iterator<Item = Vec<T>> + '_> {
        let len = self.len();
        let removals = removal_runs(len).map(move |(start, run)| {
            let mut rest = Vec::with_capacity(len - run);
            rest.extend_from_slice(&self[..start]);
            rest.extend_from_slice(&self[start + run..]);
            rest
        });
        let simplifications = (0..len).flat_map(move |index| {
            self[index].candidates().map(move |simpler| {
                let mut copy = self.clone();
                copy[index] = simpler;
                copy
            })
        });
        Box::new(removals.chain(simplifications))
    }
}

impl Shrink for String {
    /// The candidates of the same text as a `Vec<char>`.
    fn candidates(&self) -> Box<dyn Iterator<Item = String> + '_> {
        let chars: Rc<[char]> = self.chars().collect();
        let in_removals = Rc::clone(&chars);
        let removals = removal_runs(chars.len()).map(move |(start, run)| {
            in_removals[..start]
                .iter()
                .chain(&in_removals[start + run..])
                .collect()
        });
        let simplifications = (0..chars.len()).filter_map(move |index| {
            (chars[index] != 'a').then(|| {
                let (before, after) = (&chars[..index], &chars[index + 1..]);
                before.iter().chain(&['a']).chain(after).collect()
            })
        });
        Box::new(removals.chain(simplifications))
    }
}

impl<A, B> Shrink for (A, B)
where
    A: Shrink + Clone,
    B: Shrink + Clone,
{
    fn candidates(&self) -> Box<dyn Iterator<Item = (A, B)> + '_> {
        let (a, b) = self;
        Box::new(
            a.candidates()
                .map(move |simpler| (simpler, b.clone()))
                .chain(b.candidates().map(move |simpler| (a.clone(), simpler))),
        )
    }
}

impl<A, B, C> Shrink for (A, B, C)
where
    A: Shrink + Clone,
    B: Shrink + Clone,
    C: Shrink + Clone,
{
    fn candidates(&self) -> Box<dyn Iterator<Item = (A, B, C)> + '_> {
        let (a, b, c) = self;
        Box::new(
            a.candidates()
                .map(move |simpler| (simpler, b.clone(), c.clone()))
                .chain(
                    b.candidates()
                        .map(move |simpler| (a.clone(), simpler, c.clone())),
                )
                .chain(
                    c.candidates()
                        .map(move |simpler| (a.clone(), b.clone(), simpler)),
                ),
        )
    }
}
