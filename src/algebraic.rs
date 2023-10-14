use crate::internal_num_traits::{BoundedAbove, BoundedBelow, One, Zero};
use std::convert::Infallible;
use std::marker::PhantomData;
use std::ops::{Add, BitAnd, BitOr, BitXor, Mul, Neg, Not};

/// An algebraic structure that consists of a set $S$
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

/// A [`Monoid`] that consists of a set $S$
/// and a binary operation $\cdot$,
/// and the operation is commutative;
/// that is, it satisfies
/// $a \cdot b = b \cdot a$ for all $a, b \in S$.
pub trait CommutativeMonoid: Monoid {}

/// An algebraic structure that consists of a set $S$
/// and a binary operation $\cdot$,
/// and satisfies the following properties:
///
/// - Associativity:
/// $(a \cdot b) \cdot c = a \cdot (b \cdot c)$ for all $a, b, c \in S$.
/// - Identity Element:
/// There exists some $e \in S$ such that
/// $a \cdot e = e \cdot a = a$ for all $a \in S$.
/// - Inverse Element:
/// For each $a \in S$, there exists some $b \in S$
/// such that $a \cdot b = b \cdot a = e$,
/// where $e$ is the identity element.
///
/// In other words, a group is a [`Monoid`] that
/// each element has an inverse element.
pub trait Group: Monoid {
    fn inv(x: &Self::S) -> Self::S;
}

/// A [`Group`] that consists of a set $S$
/// and a binary operation $\cdot$,
/// and the operation is commutative;
/// that is, it satisfies
/// $a \cdot b = b \cdot a$ for all $a, b \in S$.
pub trait CommutativeGroup: CommutativeMonoid + Group {}
impl<T> CommutativeGroup for T where T: CommutativeMonoid + Group {}

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

impl<S> CommutativeMonoid for Max<S> where S: Copy + Ord + BoundedBelow {}

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

impl<S> CommutativeMonoid for Min<S> where S: Copy + Ord + BoundedAbove {}

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

impl<S> CommutativeMonoid for Additive<S> where S: Copy + Add<Output = S> + Zero {}

impl<S> Group for Additive<S>
where
    S: Copy + Add<Output = S> + Neg<Output = S> + Zero,
{
    fn inv(x: &Self::S) -> Self::S {
        -*x
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

impl<S> CommutativeMonoid for Multiplicative<S> where S: Copy + Mul<Output = S> + One {}

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

impl<S> CommutativeMonoid for BitwiseOr<S> where S: Copy + BitOr<Output = S> + Zero {}

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

impl<S> CommutativeMonoid for BitwiseAnd<S> where
    S: Copy + BitAnd<Output = S> + Not<Output = S> + Zero
{
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

impl<S> CommutativeMonoid for BitwiseXor<S> where S: Copy + BitXor<Output = S> + Zero {}

impl<S> Group for BitwiseXor<S>
where
    S: Copy + BitXor<Output = S> + Zero,
{
    fn inv(x: &Self::S) -> Self::S {
        *x
    }
}
