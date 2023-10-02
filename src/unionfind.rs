use std::ops::{Add, Neg, Sub};

use ParentOrSize::*;

#[derive(Debug, Clone)]
enum ParentOrSize {
    Parent(usize),
    Size(usize),
}

/// A disjoint-set data structure.
///
/// Performs the following operations on an undirected graph of
/// `n` vertices with amortized time complexity `O(α(n))`,
/// where `α(n)` is the inverse Ackermann function, which grows very slowly.
/// - Add an edge
/// - Determine if two vertices are in the same connected component
///
/// # Examples
///
/// ```
/// use procon_lib::unionfind::UnionFind;
///
/// let mut uf = UnionFind::new(5);
/// uf.union(0, 1);
/// uf.union(1, 2);
/// uf.union(3, 4);
/// assert!(uf.is_same(0, 2));
/// assert!(!uf.is_same(2, 3));
/// assert!(uf.is_same(3, 4));
/// ```
#[derive(Debug, Clone)]
pub struct UnionFind {
    n: usize,
    parent_or_size: Vec<ParentOrSize>,
}

impl UnionFind {
    /// Creates a new `UnionFind` which represents
    /// an undirected graph with `n` vertices and 0 edges.
    pub fn new(n: usize) -> Self {
        Self {
            n,
            parent_or_size: vec![Size(1); n],
        }
    }

    /// Returns the representitive of the connected component that contains the vertex `a`.
    ///
    /// Panics if `a >= n`.
    pub fn find(&mut self, a: usize) -> usize {
        assert!(a < self.n);
        match self.parent_or_size[a] {
            Size(_) => a,
            Parent(p) => {
                let root = self.find(p);
                self.parent_or_size[a] = Parent(root);
                root
            }
        }
    }

    /// Adds an edge (`a`, `b`).
    ///
    /// Panics if `a >= n` or `b >= n`.
    pub fn union(&mut self, a: usize, b: usize) {
        assert!(a < self.n);
        assert!(b < self.n);
        let mut x = self.find(a);
        let mut y = self.find(b);
        if x == y {
            return;
        }
        let Size(size_x) = self.parent_or_size[x] else { unreachable!() };
        let Size(size_y) = self.parent_or_size[y] else { unreachable!() };
        if size_x < size_y {
            std::mem::swap(&mut x, &mut y);
        }
        self.parent_or_size[x] = Size(size_x + size_y);
        self.parent_or_size[y] = Parent(x);
    }

    /// Returns whether the vertices `a` and `b` are in the same connected component.
    ///
    /// Panics if `a >= n` or `b >= n`.
    pub fn is_same(&mut self, a: usize, b: usize) -> bool {
        assert!(a < self.n);
        assert!(b < self.n);
        self.find(a) == self.find(b)
    }

    /// Returns the size of the connected component that contains the vertex `a`.
    ///
    /// Panics if `a >= n`.
    pub fn size(&mut self, a: usize) -> usize {
        assert!(a < self.n);
        let x = self.find(a);
        let Size(size) = self.parent_or_size[x] else { unreachable!() };
        size
    }

    /// Divides the graph into connected components.
    ///
    /// # Examples
    ///
    /// ```
    /// use procon_lib::unionfind::UnionFind;
    ///
    /// let mut uf = UnionFind::new(5);
    /// uf.union(0, 1);
    /// uf.union(0, 3);
    /// uf.union(2, 4);
    /// let mut groups = uf.groups();
    /// groups.sort();
    /// assert_eq!(groups, vec![vec![0, 1, 3], vec![2, 4]]);
    /// ```
    pub fn groups(&mut self) -> Vec<Vec<usize>> {
        let mut roots = vec![0; self.n];
        let mut group_size = vec![0; self.n];
        for i in 0..self.n {
            roots[i] = self.find(i);
            group_size[roots[i]] += 1;
        }
        let mut result = vec![vec![]; self.n];
        for i in 0..self.n {
            result[i].reserve(group_size[i]);
        }
        for i in 0..self.n {
            result[roots[i]].push(i);
        }
        result
            .into_iter()
            .filter(|x| !x.is_empty())
            .collect::<Vec<_>>()
    }
}

/// A disjoint-set data structure where each vertex has a "weight".
///
/// In the following, `weight[a]` represents the weight of the vertex `a`.
///
/// # Examples
///
/// ```
/// use procon_lib::unionfind::WeightedUnionFind;
///
/// let mut uf = WeightedUnionFind::<i32>::new(5, 0);
/// uf.union(0, 1, 4);
/// assert_eq!(uf.diff(0, 1), Some(4));
/// uf.union(1, 2, -3);
/// assert_eq!(uf.diff(0, 2), Some(1));
/// assert_eq!(uf.diff(0, 3), None);
/// uf.union(3, 4, 6);
/// assert_eq!(uf.diff(4, 3), Some(-6));
/// ```
#[derive(Debug, Clone)]
pub struct WeightedUnionFind<T> {
    n: usize,
    parent_or_size: Vec<ParentOrSize>,
    weight_diff: Vec<T>,
}

impl<T> WeightedUnionFind<T>
where
    T: Clone + Add<Output = T> + Sub<Output = T> + Neg<Output = T>,
{
    /// Creates a new `WeightedUnionFind` which represents
    /// an undirected graph with `n` vertices and 0 edges.
    pub fn new(n: usize, e: T) -> Self {
        Self {
            n,
            parent_or_size: vec![Size(1); n],
            weight_diff: vec![e; n],
        }
    }

    /// Returns the representitive of the connected component that contains the vertex `a`.
    ///
    /// Panics if `a >= n`.
    pub fn find(&mut self, a: usize) -> usize {
        assert!(a < self.n);
        match self.parent_or_size[a] {
            Size(_) => a,
            Parent(p) => {
                let root = self.find(p);
                self.parent_or_size[a] = Parent(root);
                self.weight_diff[a] = self.weight_diff[a].clone() + self.weight_diff[p].clone();
                root
            }
        }
    }

    /// Adds an edge (`a`, `b`) and sets `weight[b]` to `weight[a] + w`.
    ///
    /// If `a` and `b` are already in the same connected component,
    /// this function does nothing.
    ///
    /// Panics if `a >= n` or `b >= n`.
    pub fn union(&mut self, a: usize, b: usize, w: T) {
        assert!(a < self.n);
        assert!(b < self.n);
        let mut x = self.find(a);
        let mut y = self.find(b);
        if x == y {
            return;
        }
        let Size(size_x) = self.parent_or_size[x] else { unreachable!() };
        let Size(size_y) = self.parent_or_size[y] else { unreachable!() };
        let mut w = w + self.weight_diff[a].clone() - self.weight_diff[b].clone();
        if size_x < size_y {
            std::mem::swap(&mut x, &mut y);
            w = -w;
        }
        self.parent_or_size[x] = Size(size_x + size_y);
        self.parent_or_size[y] = Parent(x);
        self.weight_diff[y] = w;
    }

    /// Returns whether the vertices `a` and `b` are in the same connected component.
    ///
    /// Panics if `a >= n` or `b >= n`.
    pub fn is_same(&mut self, a: usize, b: usize) -> bool {
        assert!(a < self.n);
        assert!(b < self.n);
        self.find(a) == self.find(b)
    }

    /// Returns `Some(weight[b] - weight[a])` if `a` and `b` are in the same connected component,
    /// `None` otherwise.
    ///
    /// Panics if `a >= n` or `b >= n`.
    ///
    /// # Examples
    ///
    /// ```
    /// use procon_lib::unionfind::WeightedUnionFind;
    ///
    /// let mut uf = WeightedUnionFind::new(4, 0);
    /// uf.union(0, 1, 3);
    /// uf.union(0, 2, 5);
    /// assert_eq!(uf.diff(1, 2), Some(2));
    /// assert_eq!(uf.diff(1, 3), None);
    /// ```
    pub fn diff(&mut self, a: usize, b: usize) -> Option<T> {
        if self.is_same(a, b) {
            Some(self.weight_diff[b].clone() - self.weight_diff[a].clone())
        } else {
            None
        }
    }

    /// Returns the size of the connected component that contains the vertex `a`.
    ///
    /// Panics if `a >= n`.
    pub fn size(&mut self, a: usize) -> usize {
        assert!(a < self.n);
        let x = self.find(a);
        let Size(size) = self.parent_or_size[x] else { unreachable!() };
        size
    }

    /// Divides the graph into connected components.
    ///
    /// # Examples
    ///
    /// ```
    /// use procon_lib::unionfind::WeightedUnionFind;
    ///
    /// let mut uf = WeightedUnionFind::<i32>::new(5, 0);
    /// uf.union(0, 1, 1);
    /// uf.union(0, 3, 1);
    /// uf.union(2, 4, 1);
    /// let mut groups = uf.groups();
    /// groups.sort();
    /// assert_eq!(groups, vec![vec![0, 1, 3], vec![2, 4]]);
    /// ```
    pub fn groups(&mut self) -> Vec<Vec<usize>> {
        let mut roots = vec![0; self.n];
        let mut group_size = vec![0; self.n];
        for i in 0..self.n {
            roots[i] = self.find(i);
            group_size[roots[i]] += 1;
        }
        let mut result = vec![vec![]; self.n];
        for i in 0..self.n {
            result[i].reserve(group_size[i]);
        }
        for i in 0..self.n {
            result[roots[i]].push(i);
        }
        result
            .into_iter()
            .filter(|x| !x.is_empty())
            .collect::<Vec<_>>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unionfind() {
        let mut uf = UnionFind::new(6);
        assert!(!uf.is_same(0, 1));
        uf.union(0, 1);
        assert!(uf.is_same(0, 1));
        uf.union(1, 2);
        assert!(uf.is_same(0, 2));
        assert!(!uf.is_same(0, 3));
        assert_eq!(uf.size(0), 3);
        uf.union(3, 4);
        assert!(uf.is_same(3, 4));
        assert_eq!(uf.groups(), vec![vec![0, 1, 2], vec![3, 4], vec![5]]);
    }
}
