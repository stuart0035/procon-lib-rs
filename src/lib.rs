//! Utilities for competitive programming

pub mod algebraic;
pub mod fenwick_tree;
pub mod interval_heap;
pub mod primes;
pub mod segtree;
pub mod unionfind;

mod internal_montgomery;
mod internal_num_traits;

pub use algebraic::{
    Additive, BitwiseAnd, BitwiseOr, BitwiseXor, CommutativeGroup, Group, Max, Min, Monoid,
    Multiplicative,
};
pub use fenwick_tree::FenwickTree;
pub use interval_heap::IntervalHeap;
pub use primes::{factorize, is_prime};
pub use segtree::SegTree;
pub use unionfind::{UnionFind, WeightedUnionFind};
