//! A double-ended priority queue implemented with an interval heap.

use std::mem::swap;

/// A double-ended priority queue implemented with an interval heap.
///
/// See: [J. van Leeuwen and D. Wood, Interval Heaps, The Computer Journal, Volume 36, Issue 3, 1993, Pages 209–216](https://doi.org/10.1093/comjnl/36.3.209)
///
/// Insertion and popping the smallest or largest element have $O(\log n)$ time complexity.
/// Checking the smallest or largest element is $O(1)$.
/// Converting a vector to an interval heap can be done in-place, and has $O(n)$ complexity.
#[derive(Debug)]
pub struct IntervalHeap<T> {
    data: Vec<T>,
}

impl<T: Clone> Clone for IntervalHeap<T> {
    fn clone(&self) -> Self {
        IntervalHeap {
            data: self.data.clone(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.data.clone_from(&source.data);
    }
}

impl<T: Ord> Default for IntervalHeap<T> {
    /// Creates an empty `IntervalHeap<T>`.
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Ord> From<Vec<T>> for IntervalHeap<T> {
    /// Converts a `Vec<T>` into a `IntervalHeap<T>`.
    ///
    /// This conversion happens in-place, and has $O(n)$ time complexity.
    fn from(vec: Vec<T>) -> Self {
        let mut heap = Self { data: vec };
        heap.rebuild();
        heap
    }
}

impl<T: Ord, const N: usize> From<[T; N]> for IntervalHeap<T> {
    /// ```
    /// use procon_lib::IntervalHeap;
    ///
    /// let mut h1 = IntervalHeap::from([1, 4, 2, 3]);
    /// let mut h2: IntervalHeap<_> = [1, 4, 2, 3].into();
    /// while let Some((a, b)) = h1.pop_min().zip(h2.pop_min()) {
    ///     assert_eq!(a, b);
    /// }
    /// ```
    fn from(arr: [T; N]) -> Self {
        Self::from_iter(arr)
    }
}

impl<T: Ord> FromIterator<T> for IntervalHeap<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self::from(iter.into_iter().collect::<Vec<_>>())
    }
}

impl<T: Ord> IntervalHeap<T> {
    /// Creates an empty `IntervalHeap`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use procon_lib::IntervalHeap;
    /// let mut heap = IntervalHeap::new();
    /// heap.push(4);
    /// ```
    pub fn new() -> Self {
        Self { data: vec![] }
    }

    /// Returns the least item in the interval heap, or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use procon_lib::IntervalHeap;
    /// let mut heap = IntervalHeap::new();
    /// assert_eq!(heap.peek_min(), None);
    ///
    /// heap.push(1);
    /// heap.push(5);
    /// heap.push(2);
    /// assert_eq!(heap.peek_min(), Some(&1));
    /// ```
    pub fn peek_min(&self) -> Option<&T> {
        self.data.get(0)
    }

    /// Returns the greatest item in the interval heap, or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use procon_lib::IntervalHeap;
    /// let mut heap = IntervalHeap::new();
    /// assert_eq!(heap.peek_max(), None);
    ///
    /// heap.push(1);
    /// heap.push(5);
    /// heap.push(2);
    /// assert_eq!(heap.peek_max(), Some(&5));
    /// ```
    pub fn peek_max(&self) -> Option<&T> {
        self.data.get(1).or(self.data.get(0))
    }

    /// Removes the least item from the interval heap and returns it,
    /// or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use procon_lib::IntervalHeap;
    /// let mut heap = IntervalHeap::from([1, 3]);
    ///
    /// assert_eq!(heap.pop_min(), Some(1));
    /// assert_eq!(heap.pop_min(), Some(3));
    /// assert_eq!(heap.pop_min(), None);
    /// ```
    pub fn pop_min(&mut self) -> Option<T> {
        self.data.pop().map(|mut item| {
            if self.len() & 1 == 1 {
                swap(&mut item, self.data.last_mut().unwrap());
            }
            if self.len() > 1 {
                swap(&mut item, &mut self.data[0]);
                self.sift_down_left(0);
            }
            item
        })
    }

    /// Removes the greatest item from the interval heap and returns it,
    /// or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use procon_lib::IntervalHeap;
    /// let mut heap = IntervalHeap::from([1, 3]);
    ///
    /// assert_eq!(heap.pop_max(), Some(3));
    /// assert_eq!(heap.pop_max(), Some(1));
    /// assert_eq!(heap.pop_max(), None);
    /// ```
    pub fn pop_max(&mut self) -> Option<T> {
        self.data.pop().map(|mut item| {
            if self.len() > 1 {
                swap(&mut item, &mut self.data[1]);
                self.sift_down_right(1);
            }
            item
        })
    }

    /// Pushes an item onto the interval heap.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use procon_lib::IntervalHeap;
    /// let mut heap = IntervalHeap::new();
    /// heap.push(3);
    /// heap.push(1);
    /// heap.push(6);
    ///
    /// assert_eq!(heap.len(), 3);
    /// assert_eq!(heap.peek_min(), Some(&1));
    /// assert_eq!(heap.peek_max(), Some(&6));
    /// ```
    pub fn push(&mut self, item: T) {
        self.data.push(item);
        let index = self.len() - 1;
        if index & 1 == 1 {
            if self.data[index - 1] > self.data[index] {
                self.data.swap(index - 1, index);
                self.sift_up_left(index - 1);
            } else {
                self.sift_up_right(index);
            }
        } else if index != 0 {
            let parent_right = ((index >> 1) - 1) | 1;
            if self.data[index] > self.data[parent_right] {
                self.data.swap(index, parent_right);
                self.sift_up_right(parent_right);
            } else {
                self.sift_up_left(index);
            }
        }
    }

    /// Returns the length of the interval heap.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use procon_lib::IntervalHeap;
    /// let heap = IntervalHeap::from([3, 1, 4]);
    ///
    /// assert_eq!(heap.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Checks if the interval heap is empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use procon_lib::IntervalHeap;
    /// let mut heap = IntervalHeap::new();
    ///
    /// assert!(heap.is_empty());
    ///
    /// heap.push(3);
    /// heap.push(5);
    ///
    /// assert!(!heap.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.data.len() == 0
    }

    fn sift_up_left(&mut self, mut index: usize) {
        while index != 0 {
            let parent_l = ((index >> 1) - 1) & !1;
            if self.data[index] < self.data[parent_l] {
                self.data.swap(index, parent_l);
                if index + 1 < self.len() && self.data[index] > self.data[index + 1] {
                    self.data.swap(index, index + 1);
                }
                index = parent_l;
            } else {
                break;
            }
        }
    }

    fn sift_up_right(&mut self, mut index: usize) {
        while index != 1 {
            let parent_r = ((index >> 1) - 1) | 1;
            if self.data[index] > self.data[parent_r] {
                self.data.swap(index, parent_r);
                if self.data[index - 1] > self.data[index] {
                    self.data.swap(index - 1, index);
                }
                index = parent_r;
            } else {
                break;
            }
        }
    }

    fn sift_down_left(&mut self, mut index: usize) {
        while 2 * index + 2 < self.len() {
            let child_l = if 2 * index + 4 < self.len()
                && self.data[2 * index + 2] > self.data[2 * index + 4]
            {
                2 * index + 4
            } else {
                2 * index + 2
            };
            if self.data[index] > self.data[child_l] {
                self.data.swap(index, child_l);
                if child_l + 1 < self.len() && self.data[child_l] > self.data[child_l + 1] {
                    self.data.swap(child_l, child_l + 1);
                }
                index = child_l;
            } else {
                break;
            }
        }
    }

    fn sift_down_right(&mut self, mut index: usize) {
        while 2 * index + 1 < self.len() {
            let child_r = if 2 * index + 3 < self.len()
                && self.data[2 * index + 1] < self.data[2 * index + 3]
            {
                2 * index + 3
            } else {
                2 * index + 1
            };
            if self.data[index] < self.data[child_r] {
                self.data.swap(index, child_r);
                if self.data[child_r - 1] > self.data[child_r] {
                    self.data.swap(child_r - 1, child_r);
                }
                index = child_r;
            } else {
                break;
            }
        }
    }

    fn rebuild(&mut self) {
        let mut n = self.len() & !1;
        while n > 0 {
            n -= 2;
            if self.data[n] > self.data[n + 1] {
                self.data.swap(n, n + 1);
            }
        }
        let mut n = ((self.len() + 1) >> 1) & !1;
        while n > 0 {
            n -= 2;
            self.sift_down_left(n);
            self.sift_down_right(n + 1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_interval_heap() {
        let heap = IntervalHeap::<i32>::from([]);
        assert!(heap.is_empty());

        let heap = IntervalHeap::<i32>::from([4]);
        assert_eq!(heap.peek_min(), Some(&4));
        assert_eq!(heap.peek_max(), Some(&4));

        let mut heap = IntervalHeap::from([3, 1, 4, 1, 5, 9]);
        assert_eq!(heap.len(), 6);
        assert!(!heap.is_empty());
        assert_eq!(heap.peek_min(), Some(&1));
        assert_eq!(heap.peek_max(), Some(&9));
        heap.push(2);
        assert_eq!(heap.pop_min(), Some(1));
        assert_eq!(heap.pop_max(), Some(9));
        assert_eq!(heap.peek_min(), Some(&1));
        assert_eq!(heap.peek_max(), Some(&5));
        heap.push(6);
        assert_eq!(heap.pop_min(), Some(1));
        assert_eq!(heap.pop_max(), Some(6));
        assert_eq!(heap.peek_min(), Some(&2));
        assert_eq!(heap.peek_max(), Some(&5));
        heap.push(5);
        assert_eq!(heap.pop_min(), Some(2));
        assert_eq!(heap.pop_min(), Some(3));
        assert_eq!(heap.pop_min(), Some(4));
        assert_eq!(heap.pop_min(), Some(5));
        assert_eq!(heap.pop_min(), Some(5));
        assert_eq!(heap.pop_min(), None);
        assert_eq!(heap.pop_max(), None);
        assert!(heap.is_empty());
    }
}
