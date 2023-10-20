//! Utilities for competitive programming

pub mod algebraic;
pub mod fenwick_tree;
pub mod interval_heap;
pub mod math;
pub mod modint;
pub mod primes;
pub mod segtree;
pub mod unionfind;

mod internal_math;
mod internal_num_traits;

pub use algebraic::{
    Additive, BitwiseAnd, BitwiseOr, BitwiseXor, CommutativeGroup, Group, Max, Min, Monoid,
    Multiplicative,
};
pub use fenwick_tree::FenwickTree;
pub use interval_heap::IntervalHeap;
pub use math::{checked_inv_mod, inv_mod, pow_mod};
pub use modint::{
    Barrett, DefaultId, DynamicModInt, Id, ModInt, ModInt1000000007, ModInt998244353, RemEuclidU32,
    StaticModInt,
};
pub use primes::{factorize, is_prime};
pub use segtree::SegTree;
pub use unionfind::{UnionFind, WeightedUnionFind};
