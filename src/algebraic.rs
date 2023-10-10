use crate::internal_num_traits::{BoundedAbove, BoundedBelow, One, Zero};
use std::convert::Infallible;
use std::marker::PhantomData;
use std::ops::{Add, BitAnd, BitOr, BitXor, Mul, Not};

/// The algebraic structure that consists of a set $S$
/// and a binary operation $\cdot$,
/// and satisfies the following properties:
///
/// - Associativity:
/// $(a \cdot b) \cdot c = a \cdot (b \cdot c)$ for all $a, b, c \in S$.
/// - Identity Element:
/// There exists some $e \in S$ such that
/// $a \cdot e = e \cdot a = a$ for all $a \in S$.
pub trait Monoid {
    type S: Clone;
    fn id() -> Self::S;
    fn op(a: &Self::S, b: &Self::S) -> Self::S;
}

pub struct Max<S>(Infallible, PhantomData<fn() -> S>);
impl<S> Monoid for Max<S>
where
    S: Copy + Ord + BoundedBelow,
{
    type S = S;
    fn id() -> Self::S {
        S::min_value()
    }
    fn op(a: &Self::S, b: &Self::S) -> Self::S {
        std::cmp::max(*a, *b)
    }
}

pub struct Min<S>(Infallible, PhantomData<fn() -> S>);
impl<S> Monoid for Min<S>
where
    S: Copy + Ord + BoundedAbove,
{
    type S = S;
    fn id() -> Self::S {
        S::max_value()
    }
    fn op(a: &Self::S, b: &Self::S) -> Self::S {
        std::cmp::min(*a, *b)
    }
}

pub struct Additive<S>(Infallible, PhantomData<fn() -> S>);
impl<S> Monoid for Additive<S>
where
    S: Copy + Add<Output = S> + Zero,
{
    type S = S;
    fn id() -> Self::S {
        S::zero()
    }
    fn op(a: &Self::S, b: &Self::S) -> Self::S {
        *a + *b
    }
}

pub struct Multiplicative<S>(Infallible, PhantomData<fn() -> S>);
impl<S> Monoid for Multiplicative<S>
where
    S: Copy + Mul<Output = S> + One,
{
    type S = S;
    fn id() -> Self::S {
        S::one()
    }
    fn op(a: &Self::S, b: &Self::S) -> Self::S {
        *a * *b
    }
}

pub struct BitwiseOr<S>(Infallible, PhantomData<fn() -> S>);
impl<S> Monoid for BitwiseOr<S>
where
    S: Copy + BitOr<Output = S> + Zero,
{
    type S = S;
    fn id() -> Self::S {
        S::zero()
    }
    fn op(a: &Self::S, b: &Self::S) -> Self::S {
        *a | *b
    }
}

pub struct BitwiseAnd<S>(Infallible, PhantomData<fn() -> S>);
impl<S> Monoid for BitwiseAnd<S>
where
    S: Copy + BitAnd<Output = S> + Not<Output = S> + Zero,
{
    type S = S;
    fn id() -> Self::S {
        !S::zero()
    }
    fn op(a: &Self::S, b: &Self::S) -> Self::S {
        *a & *b
    }
}

pub struct BitwiseXor<S>(Infallible, PhantomData<fn() -> S>);
impl<S> Monoid for BitwiseXor<S>
where
    S: Copy + BitXor<Output = S> + Zero,
{
    type S = S;
    fn id() -> Self::S {
        S::zero()
    }
    fn op(a: &Self::S, b: &Self::S) -> Self::S {
        *a ^ *b
    }
}
