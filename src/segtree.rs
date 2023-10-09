use crate::algebraic::Monoid;
use std::ops::{Bound, RangeBounds};

#[derive(Debug, Clone)]
pub struct SegTree<M>
where
    M: Monoid,
{
    n: usize,
    size: usize,
    data: Vec<M::S>,
}

impl<M> From<Vec<M::S>> for SegTree<M>
where
    M: Monoid,
{
    fn from(value: Vec<M::S>) -> Self {
        let n = value.len();
        let size = n.next_power_of_two();
        let mut data = vec![M::id(); 2 * size];
        data[size..][..n].clone_from_slice(&value);
        let mut segtree = Self { n, size, data };
        for i in (1..size).rev() {
            segtree.update(i);
        }
        segtree
    }
}

impl<M> FromIterator<M::S> for SegTree<M>
where
    M: Monoid,
{
    fn from_iter<T: IntoIterator<Item = M::S>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let n = iter.size_hint().0;
        let size = n.next_power_of_two();
        let mut data = Vec::with_capacity(size * 2);
        data.extend(
            std::iter::repeat_with(M::id)
                .take(size)
                .chain(iter)
                .chain(std::iter::repeat_with(M::id).take(size - n)),
        );
        let mut segtree = Self { n, size, data };
        for i in (1..size).rev() {
            segtree.update(i);
        }
        segtree
    }
}

impl<M> SegTree<M>
where
    M: Monoid,
{
    pub fn new(n: usize) -> Self {
        vec![M::id(); n].into()
    }

    /// Returns the number of elements in the segment tree.
    pub fn len(&self) -> usize {
        self.n
    }

    /// Returns `true` if the segment tree contains no elements.
    pub fn is_empty(&self) -> bool {
        self.n == 0
    }

    pub fn get(&self, index: usize) -> M::S {
        assert!(index < self.n);
        self.data[index + self.size].clone()
    }

    pub fn set(&mut self, mut index: usize, element: M::S) {
        assert!(index < self.n);
        index += self.size;
        self.data[index] = element;
        index >>= 1;
        while index != 0 {
            self.update(index);
            index >>= 1;
        }
    }

    pub fn prod<R>(&self, range: R) -> M::S
    where
        R: RangeBounds<usize>,
    {
        if range.start_bound() == Bound::Unbounded && range.end_bound() == Bound::Unbounded {
            return self.all_prod();
        }

        let mut l = match range.start_bound() {
            Bound::Included(l) => *l,
            Bound::Excluded(l) => l + 1,
            Bound::Unbounded => 0,
        };

        let mut r = match range.end_bound() {
            Bound::Included(r) => r + 1,
            Bound::Excluded(r) => *r,
            Bound::Unbounded => self.n,
        };

        assert!(l <= r && r <= self.n);
        let mut result_l = M::id();
        let mut result_r = M::id();
        l += self.size;
        r += self.size;

        while l < r {
            if l & 1 != 0 {
                result_l = M::op(&result_l, &self.data[l]);
                l += 1;
            }
            if r & 1 != 0 {
                r -= 1;
                result_r = M::op(&self.data[r], &result_r);
            }
            l >>= 1;
            r >>= 1;
        }

        M::op(&result_l, &result_r)
    }

    pub fn all_prod(&self) -> M::S {
        self.data[1].clone()
    }

    pub fn max_right<F>(&self, mut l: usize, f: F) -> usize
    where
        F: Fn(&M::S) -> bool,
    {
        assert!(l <= self.n);
        assert!(f(&M::id()));

        if l == self.n {
            return self.n;
        }
        l += self.size;
        let mut sm = M::id();
        loop {
            // do
            while l % 2 == 0 {
                l >>= 1;
            }
            if !f(&M::op(&sm, &self.data[l])) {
                while l < self.size {
                    l *= 2;
                    let res = M::op(&sm, &self.data[l]);
                    if f(&res) {
                        sm = res;
                        l += 1;
                    }
                }
                return l - self.size;
            }
            sm = M::op(&sm, &self.data[l]);
            l += 1;

            // while
            if l & l.wrapping_neg() == l {
                break;
            }
        }
        self.n
    }

    pub fn min_left<F>(&self, mut r: usize, f: F) -> usize
    where
        F: Fn(&M::S) -> bool,
    {
        assert!(r <= self.n);
        assert!(f(&M::id()));

        if r == 0 {
            return 0;
        }
        r += self.size;
        let mut sm = M::id();
        loop {
            // do
            r -= 1;
            while r > 1 && r % 2 == 1 {
                r >>= 1;
            }
            if !f(&M::op(&self.data[r], &sm)) {
                while r < self.size {
                    r = 2 * r + 1;
                    let res = M::op(&self.data[r], &sm);
                    if f(&res) {
                        sm = res;
                        r -= 1;
                    }
                }
                return r + 1 - self.size;
            }
            sm = M::op(&self.data[r], &sm);

            // while
            if r & r.wrapping_neg() == r {
                break;
            }
        }
        0
    }

    fn update(&mut self, i: usize) {
        self.data[i] = M::op(&self.data[2 * i], &self.data[2 * i + 1]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebraic::Max;

    #[test]
    fn test_max_segtree() {
        let a = [1, 2, 3, 2, 1];
        let mut segtree = SegTree::<Max<_>>::from(a.to_vec());

        assert_eq!(segtree.len(), 5);
        assert!(!segtree.is_empty());

        assert_eq!(segtree.prod(0..5), 3);
        assert_eq!(segtree.max_right(1, |&x| x < 3), 2);
        segtree.set(2, 1);
        assert_eq!(segtree.prod(1..4), 2);
        assert_eq!(segtree.max_right(0, |&x| x < 3), 5);
        segtree.set(1, 3);
        assert_eq!(segtree.min_left(4, |&x| x < 3), 2);
    }
}
