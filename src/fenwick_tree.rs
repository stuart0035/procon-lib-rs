//! A data structure that allows efficient updating of values
//! and calculation of prefix sums in arrays.
//! Also called a binary indexed tree.

use crate::algebraic::{CommutativeGroup, CommutativeMonoid};
use std::iter::FromIterator;
use std::ops::{Bound, RangeBounds};

/// A data structure that allows efficient updating of values
/// and calculation of prefix sums in arrays.
/// Also called a binary indexed tree.
///
/// The Fenwick tree (or the binary indexed tree)
/// can process both value update
/// and prefix sum calculation in $O(\log n)$ time.
#[derive(Debug, Clone)]
pub struct FenwickTree<A>
where
    A: CommutativeMonoid,
{
    data: Vec<A::S>,
}

/// Converts a `Vec<A::S>` into a `FenwickTree<A>`.
///
/// This conversion happens in-place, and has $O(n)$ time complexity.
impl<A: CommutativeMonoid> From<Vec<A::S>> for FenwickTree<A> {
    fn from(value: Vec<A::S>) -> Self {
        let mut fw = Self { data: value };
        for i in 1..=fw.len() {
            let parent = i + (i & i.wrapping_neg());
            if parent <= fw.len() {
                fw.data[parent - 1] = A::op(&fw.data[parent - 1], &fw.data[i - 1]);
            }
        }
        fw
    }
}

impl<A: CommutativeMonoid, const N: usize> From<[A::S; N]> for FenwickTree<A> {
    fn from(arr: [A::S; N]) -> Self {
        Self::from_iter(arr)
    }
}

impl<A: CommutativeMonoid> FromIterator<A::S> for FenwickTree<A> {
    fn from_iter<I: IntoIterator<Item = A::S>>(iter: I) -> Self {
        Self::from(iter.into_iter().collect::<Vec<_>>())
    }
}

impl<A> FenwickTree<A>
where
    A: CommutativeMonoid,
{
    /// Creates an array $a_0, a_1, \dots, a_{n - 1}$ of length $n$.
    ///
    /// All the elements are initialized to
    /// the identity element `A::id()`,
    /// which is `0` in integer addition.
    pub fn new(n: usize) -> Self {
        Self {
            data: vec![A::id(); n + 1],
        }
    }

    /// Returns the number of elements in the Fenwick tree.
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns `true` if the Fenwick tree contains no elements.
    pub fn is_empty(&self) -> bool {
        self.data.len() == 0
    }

    /// Updates `a[index]` with `a[index] + value`.
    pub fn add(&mut self, index: usize, value: A::S) {
        let mut index = index + 1;
        while index <= self.len() {
            self.data[index - 1] = A::op(&self.data[index - 1], &value);
            index += index & index.wrapping_neg();
        }
    }

    /// Returns `a[0] + a[1] + ... + a[index - 1]`.
    pub fn accum(&self, mut index: usize) -> A::S {
        let mut sum = A::id();
        while index != 0 {
            sum = A::op(&sum, &self.data[index - 1]);
            index &= index - 1;
        }
        sum
    }

    /// Returns `a[l] + a[l + 1] + ... + a[r - 1]`.
    pub fn sum<R>(&self, range: R) -> A::S
    where
        A: CommutativeGroup,
        R: RangeBounds<usize>,
    {
        let r = match range.end_bound() {
            Bound::Included(r) => r + 1,
            Bound::Excluded(r) => *r,
            Bound::Unbounded => self.len(),
        };
        let l = match range.start_bound() {
            Bound::Included(l) if *l != 0 => *l,
            Bound::Excluded(l) => l + 1,
            _ => return self.accum(r),
        };
        A::op(&self.accum(r), &A::inv(&self.accum(l)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebraic::Additive;

    #[test]
    fn test_fenwick_tree() {
        let mut fw = FenwickTree::<Additive<_>>::from([1, 10, 100, 1000, 10000, 100000]);
        assert_eq!(fw.accum(0), 0);
        assert_eq!(fw.accum(1), 1);
        assert_eq!(fw.accum(3), 111);
        assert_eq!(fw.accum(6), 111111);
        assert_eq!(fw.sum(1..3), 110);
        assert_eq!(fw.sum(1..=3), 1110);
        assert_eq!(fw.sum(2..), 111100);
        assert_eq!(fw.sum(4..=4), 10000);
        assert_eq!(fw.sum((Bound::Excluded(1), Bound::Included(3))), 1100);

        fw.add(3, -1000);
        assert_eq!(fw.accum(4), 111);
        assert_eq!(fw.accum(6), 110111);
        assert_eq!(fw.sum(1..3), 110);
        assert_eq!(fw.sum(2..), 110100);
        assert_eq!(fw.sum(3..=3), 0);
    }
}
