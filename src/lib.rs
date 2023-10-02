//! Utilities for competitive programming

pub mod primes;
pub mod unionfind;

mod internal_montgomery;

pub use primes::{factorize, is_prime};
pub use unionfind::{UnionFind, WeightedUnionFind};
