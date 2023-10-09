//! Utilities for competitive programming

pub mod algebraic;
pub mod primes;
pub mod segtree;
pub mod unionfind;

mod internal_montgomery;
mod internal_num_traits;

pub use algebraic::{
    Additive, BitwiseAnd, BitwiseOr, BitwiseXor, Max, Min, Monoid, Multiplicative,
};
pub use primes::{factorize, is_prime};
pub use segtree::SegTree;
pub use unionfind::{UnionFind, WeightedUnionFind};
