//! Structs that treat the modular arithmetic.
//!
//! Reference:
//! - [ac-library](https://github.com/atcoder/ac-library)
//! - [ac-library-rs](https://github.com/rust-lang-ja/ac-library-rs)

use super::internal_math;
use std::{
    fmt,
    hash::{Hash, Hasher},
    iter::{Product, Sum},
    marker::PhantomData,
    num::ParseIntError,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    str::FromStr,
    sync::atomic,
    sync::atomic::{AtomicU32, AtomicU64},
};

pub type ModInt998244353 = StaticModInt<998_244_353>;
pub type ModInt1000000007 = StaticModInt<1_000_000_007>;
pub type ModInt = DynamicModInt<DefaultId>;

/// Represents $\mathbb{Z}/m\mathbb{Z}$ where $m$ is a constant value.
///
/// # Examples
///
/// ```
/// use procon_lib::{ModInt1000000007 as Mint, StaticModInt};
///
/// let a = StaticModInt::<13>::new(5);
/// let b = StaticModInt::<13>::new(9);
///
/// assert_eq!(1, (a + b).val()); // 5 + 9 = 14 ≡ 1 (mod 13)
/// assert_eq!(9, (a - b).val()); // 5 - 9 = -4 ≡ 9 (mod 13)
/// assert_eq!(6, (a * b).val()); // 5 * 9 = 45 ≡ 6 (mod 13)
///
/// // The multiplicative inverse of 9 is 3 (mod 13).
/// assert_eq!(3, b.inv().val());
/// assert_eq!(2, (a / b).val()); // 5 / 9 ≡ 5 * 3 = 15 ≡ 2 (mod 13)
///
/// // "ModInt1000000007" is an alias of "StaticModInt<1_000_000_007>".
/// let a = Mint::new(1_000_000_006);
/// let b = Mint::new(2);
/// assert_eq!(1, (a + b).val());
/// ```
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct StaticModInt<const M: u32> {
    val: u32,
}

impl<const M: u32> StaticModInt<M> {
    const IS_PRIME: bool = internal_math::is_prime_const(M);

    /// Returns the modulus, which is `M`.
    ///
    /// # Examples
    ///
    /// ```
    /// use procon_lib::ModInt1000000007 as Mint;
    ///
    /// assert_eq!(1_000_000_007, Mint::modulus());
    /// ```
    #[inline(always)]
    pub fn modulus() -> u32 {
        M
    }

    /// Creates a new `StaticModInt`.
    ///
    /// Takes [any primitive integer].
    ///
    /// # Examples
    ///
    /// ```
    /// use procon_lib::ModInt1000000007 as Mint;
    ///
    /// let x = Mint::new(2);
    /// assert_eq!(2, x.val());
    ///
    /// let x = Mint::new(1_000_000_008);
    /// assert_eq!(1, x.val());
    ///
    /// let x = Mint::new(-1);
    /// assert_eq!(1_000_000_006, x.val());
    /// ```
    ///
    /// [any primitive integer]:  trait.RemEuclidU32.html
    #[inline]
    pub fn new<T: RemEuclidU32>(val: T) -> Self {
        Self::new_raw(val.rem_euclid_u32(M))
    }

    /// Constructs a `Self` from a `val < Self::modulus()` without checking it.
    ///
    /// # Constraints
    ///
    /// - `val` is less than `Self::modulus()`
    ///
    /// **Note that all operations assume that inner values are smaller than the modulus.**
    /// If `val` is greater than or equal to `Self::modulus()`, the behaviors are not defined.
    #[inline]
    pub fn new_raw(val: u32) -> Self {
        Self { val }
    }

    /// Returns the representative.
    #[inline]
    pub fn val(self) -> u32 {
        self.val
    }

    /// Returns `self` to the power of `exp`.
    ///
    /// # Examples
    ///
    /// ```
    /// use procon_lib::ModInt1000000007 as Mint;
    ///
    /// let x = Mint::new(2);
    /// assert_eq!(8, x.pow(3).val());
    ///
    /// let x = Mint::new(-1);
    /// assert_eq!(1, x.pow(2).val());
    /// ```
    #[inline]
    pub fn pow(self, exp: u64) -> Self {
        <Self as ModIntBase>::pow(self, exp)
    }

    /// Returns the multiplicative inverse of `self`.
    ///
    /// # Panics
    ///
    /// Panics if the multiplicative inverse does not exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use procon_lib::ModInt1000000007 as Mint;
    ///
    /// assert_eq!(500_000_004, Mint::new(2).inv().val());
    /// ```
    #[inline]
    pub fn inv(self) -> Self {
        if Self::IS_PRIME {
            if self.val() == 0 {
                panic!("attempt to divide by zero");
            }
            self.pow((M - 2).into())
        } else {
            Self::inv_for_non_prime_modulus(self)
        }
    }

    /// Computes the multiplicative inverse of `self`,
    /// returning `None` if the multiplicative inverse does not exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use procon_lib::{ModInt1000000007 as Mint, StaticModInt};
    ///
    /// assert_eq!(Some(500_000_004), Mint::new(2).checked_inv().map(StaticModInt::val));
    /// assert_eq!(None, Mint::new(0).checked_inv().map(StaticModInt::val));
    /// ```
    #[inline]
    pub fn checked_inv(self) -> Option<Self> {
        if Self::IS_PRIME {
            if self.val() == 0 {
                None
            } else {
                Some(self.pow((M - 2).into()))
            }
        } else {
            Self::checked_inv_for_non_prime_modulus(self)
        }
    }

    /// Computes `self / rhs`,
    /// returning `None` if the multiplicative inverse of `rhs` does not exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use procon_lib::{ModInt1000000007 as Mint, StaticModInt};
    ///
    /// let x = Mint::new(2);
    /// let y = Mint::new(0);
    ///
    /// assert_eq!(Some(3), Mint::new(6).checked_div(x).map(StaticModInt::val));
    /// assert_eq!(None, Mint::new(6).checked_div(y).map(StaticModInt::val));
    /// ```
    #[inline]
    pub fn checked_div(self, rhs: Self) -> Option<Self> {
        <Self as ModIntBase>::checked_div(self, rhs)
    }
}

/// Represents $\mathbb{Z}/m\mathbb{Z}$ where $m$ is a dynamic value.
///
/// # Example
///
/// ```
/// use procon_lib::ModInt as Mint;
///
/// Mint::set_modulus(13);
///
/// let a = Mint::new(5);
/// let b = Mint::new(9);
///
/// assert_eq!(1, (a + b).val()); // 5 + 9 = 14 ≡ 1 (mod 13)
/// assert_eq!(9, (a - b).val()); // 5 - 9 = -4 ≡ 9 (mod 13)
/// assert_eq!(6, (a * b).val()); // 5 * 9 = 45 ≡ 6 (mod 13)
///
/// // The multiplicative inverse of 9 is 3 (mod 13).
/// assert_eq!(3, b.inv().val());
/// assert_eq!(2, (a / b).val()); // 5 / 9 ≡ 5 * 3 = 15 ≡ 2 (mod 13)
/// ```
#[derive(Copy, Clone, Eq, PartialEq)]
#[repr(transparent)]
pub struct DynamicModInt<I> {
    val: u32,
    phantom: PhantomData<fn() -> I>,
}

impl<I: Id> DynamicModInt<I> {
    /// Returns the modulus.
    ///
    /// # Example
    ///
    /// ```
    /// use procon_lib::ModInt as Mint;
    ///
    /// assert_eq!(998_244_353, Mint::modulus()); // default modulus
    /// ```
    #[inline]
    pub fn modulus() -> u32 {
        I::companion_barrett().modulus()
    }

    /// Sets a modulus.
    ///
    /// # Constraints
    ///
    /// - This function must be called earlier than any other operation of `Self`.
    ///
    /// # Example
    ///
    /// ```
    /// use procon_lib::ModInt as Mint;
    ///
    /// Mint::set_modulus(7);
    /// assert_eq!(7, Mint::modulus());
    /// ```
    #[inline]
    pub fn set_modulus(modulus: u32) {
        if modulus == 0 {
            panic!("the modulus must not be 0");
        }
        I::companion_barrett().update(modulus);
    }

    /// Creates a new `DynamicModInt`.
    ///
    /// Takes [any primitive integer].
    ///
    /// # Examples
    ///
    /// ```
    /// use procon_lib::ModInt as Mint;
    ///
    /// Mint::set_modulus(7);
    ///
    /// let x = Mint::new(2);
    /// assert_eq!(2, x.val());
    ///
    /// let x = Mint::new(10);
    /// assert_eq!(3, x.val());
    /// ```
    ///
    /// [any primitive integer]:  trait.RemEuclidU32.html
    #[inline]
    pub fn new<T: RemEuclidU32>(val: T) -> Self {
        <Self as ModIntBase>::new(val)
    }

    /// Constructs a `Self` from a `val < Self::modulus()` without checking it.
    ///
    /// # Constraints
    ///
    /// - `val` is less than `Self::modulus()`
    ///
    /// **Note that all operations assume that inner values are smaller than the modulus.**
    /// If `val` is greater than or equal to `Self::modulus()`, the behaviors are not defined.
    #[inline]
    pub fn new_raw(val: u32) -> Self {
        Self {
            val,
            phantom: PhantomData,
        }
    }

    /// Returns the representative.
    #[inline]
    pub fn val(self) -> u32 {
        self.val
    }

    /// Returns `self` to the power of `exp`.
    #[inline]
    pub fn pow(self, exp: u64) -> Self {
        <Self as ModIntBase>::pow(self, exp)
    }

    /// Returns the multiplicative inverse of `self`.
    ///
    /// # Panics
    ///
    /// Panics if the multiplicative inverse does not exist.
    #[inline]
    pub fn inv(self) -> Self {
        Self::inv_for_non_prime_modulus(self)
    }

    /// Computes the multiplicative inverse of `self`,
    /// returning `None` if the multiplicative inverse does not exist.
    #[inline]
    pub fn checked_inv(self) -> Option<Self> {
        Self::checked_inv_for_non_prime_modulus(self)
    }

    /// Computes `self / rhs`,
    /// returning `None` if the multiplicative inverse of `rhs` does not exist.
    #[inline]
    pub fn checked_div(self, rhs: Self) -> Option<Self> {
        <Self as ModIntBase>::checked_div(self, rhs)
    }
}

pub trait Id: 'static + Copy + Eq {
    fn companion_barrett() -> &'static Barrett;
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub enum DefaultId {}

impl Id for DefaultId {
    fn companion_barrett() -> &'static Barrett {
        static BARRETT: Barrett = Barrett::default();
        &BARRETT
    }
}

/// Pair of $m$ and $\lceil 2^{64}/m \rceil$.
pub struct Barrett {
    m: AtomicU32,
    im: AtomicU64,
}

impl Barrett {
    /// Creates a new `Barrett`.
    #[inline]
    pub const fn new(m: u32) -> Self {
        Self {
            m: AtomicU32::new(m),
            im: AtomicU64::new((u64::MAX / m as u64).wrapping_add(1)),
        }
    }

    #[inline]
    const fn default() -> Self {
        Self::new(998_244_353)
    }

    #[inline]
    fn update(&self, m: u32) {
        let im = (u64::MAX / m as u64).wrapping_add(1);
        self.m.store(m, atomic::Ordering::SeqCst);
        self.im.store(im, atomic::Ordering::SeqCst);
    }

    #[inline]
    fn modulus(&self) -> u32 {
        self.m.load(atomic::Ordering::SeqCst)
    }

    #[inline]
    fn mul(&self, a: u32, b: u32) -> u32 {
        let m = self.m.load(atomic::Ordering::SeqCst);
        let im = self.im.load(atomic::Ordering::SeqCst);
        internal_math::mul(a, b, m, im)
    }
}

impl Default for Barrett {
    #[inline]
    fn default() -> Self {
        Self::default()
    }
}

/// A trait for [`StaticModInt`] and [`DynamicModInt`].
///
/// [`StaticModInt`]: struct.StaticModInt.html
pub trait ModIntBase:
    Default
    + FromStr
    + From<i8>
    + From<i16>
    + From<i32>
    + From<i64>
    + From<i128>
    + From<isize>
    + From<u8>
    + From<u16>
    + From<u32>
    + From<u64>
    + From<u128>
    + From<usize>
    + Copy
    + Eq
    + Hash
    + fmt::Display
    + fmt::Debug
    + Neg<Output = Self>
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + AddAssign
    + SubAssign
    + MulAssign
    + DivAssign
{
    /// Returns the modulus.
    fn modulus() -> u32;

    /// Constructs a `Self` from a `val < Self::modulus()` without checking it.
    ///
    /// # Constraints
    ///
    /// - `val` is less than `Self::modulus()`
    ///
    /// **Note that all operations assume that inner values are smaller than the modulus.**
    /// If `val` is greater than or equal to `Self::modulus()`, the behaviors are not defined.
    fn new_raw(val: u32) -> Self;

    /// Returns the representative.
    fn val(self) -> u32;

    /// Returns the multiplicative inverse of `self`.
    ///
    /// # Panics
    ///
    /// Panics if the multiplicative inverse does not exist.
    fn inv(self) -> Self;

    /// Computes the multiplicative inverse of `self`,
    /// returning `None` if multiplicative inverse does not exist.
    fn checked_inv(self) -> Option<Self>;

    /// Creates a new `Self`.
    ///
    /// Takes [any primitive integer].
    ///
    /// [any primitive integer]:  trait.RemEuclidU32.html
    #[inline]
    fn new<T: RemEuclidU32>(val: T) -> Self {
        Self::new_raw(val.rem_euclid_u32(Self::modulus()))
    }

    /// Returns `self` to the power of `exp`.
    #[inline]
    fn pow(self, mut exp: u64) -> Self {
        let mut x = self;
        let mut r = Self::new_raw(1);
        while exp > 0 {
            if exp & 1 == 1 {
                r *= x;
            }
            x *= x;
            exp >>= 1;
        }
        r
    }

    /// Computes `self / rhs`,
    /// returning `None` if the multiplicative inverse of `rhs` does not exist.
    #[inline]
    fn checked_div(self, rhs: Self) -> Option<Self> {
        Some(self * rhs.checked_inv()?)
    }
}

/// These methods are implemented for the struct.
/// You don't need to `use` `ModIntBase` to call methods of `StaticModInt`.
impl<const M: u32> ModIntBase for StaticModInt<M> {
    #[inline(always)]
    fn modulus() -> u32 {
        Self::modulus()
    }

    #[inline]
    fn new_raw(val: u32) -> Self {
        Self::new_raw(val)
    }

    #[inline]
    fn val(self) -> u32 {
        self.val()
    }

    #[inline]
    fn inv(self) -> Self {
        self.inv()
    }

    #[inline]
    fn checked_inv(self) -> Option<Self> {
        self.checked_inv()
    }
}

/// These methods are implemented for the struct.
/// You don't need to `use` `ModIntBase` to call methods of `DynamicModInt`.
impl<I: Id> ModIntBase for DynamicModInt<I> {
    #[inline]
    fn modulus() -> u32 {
        Self::modulus()
    }

    #[inline]
    fn new_raw(val: u32) -> Self {
        Self::new_raw(val)
    }

    #[inline]
    fn val(self) -> u32 {
        self.val()
    }

    #[inline]
    fn inv(self) -> Self {
        self.inv()
    }

    #[inline]
    fn checked_inv(self) -> Option<Self> {
        self.checked_inv()
    }
}

/// A trait for `{StaticModInt, DynamicModInt, ModIntBase}::new`.
pub trait RemEuclidU32 {
    /// Calculates `self` $\bmod$ `modulus` losslessly.
    fn rem_euclid_u32(self, modulus: u32) -> u32;
}

macro_rules! impl_rem_euclid_u32_for_small_signed {
    ($($ty:tt),*) => {
        $(
            impl RemEuclidU32 for $ty {
                #[inline]
                fn rem_euclid_u32(self, modulus: u32) -> u32 {
                    (self as i64).rem_euclid(i64::from(modulus)) as _
                }
            }
        )*
    }
}

impl_rem_euclid_u32_for_small_signed!(i8, i16, i32, i64, isize);

impl RemEuclidU32 for i128 {
    #[inline]
    fn rem_euclid_u32(self, modulus: u32) -> u32 {
        self.rem_euclid(i128::from(modulus)) as _
    }
}

macro_rules! impl_rem_euclid_u32_for_small_unsigned {
    ($($ty:tt),*) => {
        $(
            impl RemEuclidU32 for $ty {
                #[inline]
                fn rem_euclid_u32(self, modulus: u32) -> u32 {
                    self as u32 % modulus
                }
            }
        )*
    }
}

macro_rules! impl_rem_euclid_u32_for_large_unsigned {
    ($($ty:tt),*) => {
        $(
            impl RemEuclidU32 for $ty {
                #[inline]
                fn rem_euclid_u32(self, modulus: u32) -> u32 {
                    (self % (modulus as $ty)) as _
                }
            }
        )*
    }
}

impl_rem_euclid_u32_for_small_unsigned!(u8, u16, u32);
impl_rem_euclid_u32_for_large_unsigned!(u64, u128);

#[cfg(target_pointer_width = "32")]
impl_rem_euclid_u32_for_small_unsigned!(usize);

#[cfg(target_pointer_width = "64")]
impl_rem_euclid_u32_for_large_unsigned!(usize);

trait InternalImplementations: ModIntBase {
    #[inline]
    fn inv_for_non_prime_modulus(this: Self) -> Self {
        Self::checked_inv_for_non_prime_modulus(this)
            .expect("the multiplicative inverse does not exist")
    }

    #[inline]
    fn checked_inv_for_non_prime_modulus(this: Self) -> Option<Self> {
        let (gcd, x) = internal_math::inv_gcd(this.val().into(), Self::modulus().into());
        if gcd == 1 {
            Some(Self::new(x))
        } else {
            None
        }
    }

    #[inline]
    fn default_impl() -> Self {
        Self::new_raw(0)
    }

    #[inline]
    fn from_str_impl(s: &str) -> Result<Self, ParseIntError> {
        s.parse::<i64>().map(Self::new)
    }

    #[inline]
    fn hash_impl(this: &Self, state: &mut impl Hasher) {
        this.val().hash(state)
    }

    #[inline]
    fn display_impl(this: &Self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&this.val(), f)
    }

    #[inline]
    fn debug_impl(this: &Self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&this.val(), f)
    }

    #[inline]
    fn neg_impl(this: Self) -> Self {
        Self::sub_impl(Self::new_raw(0), this)
    }

    #[inline]
    fn add_impl(lhs: Self, rhs: Self) -> Self {
        let modulus = Self::modulus();
        let mut val = lhs.val().wrapping_add(rhs.val());
        if lhs.val() >= modulus - rhs.val() {
            val = val.wrapping_sub(modulus);
        }
        Self::new_raw(val)
    }

    #[inline]
    fn sub_impl(lhs: Self, rhs: Self) -> Self {
        let modulus = Self::modulus();
        let mut val = lhs.val().wrapping_sub(rhs.val());
        if lhs.val() < rhs.val() {
            val = val.wrapping_add(modulus)
        }
        Self::new_raw(val)
    }

    fn mul_impl(lhs: Self, rhs: Self) -> Self;

    #[inline]
    fn div_impl(lhs: Self, rhs: Self) -> Self {
        Self::mul_impl(lhs, rhs.inv())
    }
}

impl<const M: u32> InternalImplementations for StaticModInt<M> {
    #[inline]
    fn mul_impl(lhs: Self, rhs: Self) -> Self {
        Self::new_raw((u64::from(lhs.val()) * u64::from(rhs.val()) % u64::from(M)) as u32)
    }
}

impl<I: Id> InternalImplementations for DynamicModInt<I> {
    #[inline]
    fn mul_impl(lhs: Self, rhs: Self) -> Self {
        Self::new_raw(I::companion_barrett().mul(lhs.val, rhs.val))
    }
}

macro_rules! impl_basic_traits {
    () => {};
    (impl <$($generic_param:ident)*: $generic_param_bound:tt> _ for $self:ty; $($rest:tt)*) => {
        impl <$($generic_param)*: $generic_param_bound> Default for $self {
            #[inline]
            fn default() -> Self {
                Self::default_impl()
            }
        }

        impl <$($generic_param)*: $generic_param_bound> FromStr for $self {
            type Err = ParseIntError;
            #[inline]
            fn from_str(s: &str) -> Result<Self, ParseIntError> {
                Self::from_str_impl(s)
            }
        }

        impl<$($generic_param)*: $generic_param_bound, V: RemEuclidU32> From<V> for $self {
            #[inline]
            fn from(from: V) -> Self {
                Self::new(from)
            }
        }

        impl<$($generic_param)*: $generic_param_bound> Hash for $self {
            #[inline]
            fn hash<H: Hasher>(&self, state: &mut H) {
                Self::hash_impl(self, state)
            }
        }

        impl<$($generic_param)*: $generic_param_bound> fmt::Display for $self {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                Self::display_impl(self, f)
            }
        }

        impl<$($generic_param)*: $generic_param_bound> fmt::Debug for $self {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                Self::debug_impl(self, f)
            }
        }

        impl<$($generic_param)*: $generic_param_bound> Neg for $self {
            type Output = $self;

            #[inline]
            fn neg(self) -> $self {
                Self::neg_impl(self)
            }
        }

        impl<$($generic_param)*: $generic_param_bound> Neg for &'_ $self {
            type Output = $self;

            #[inline]
            fn neg(self) -> $self {
                <$self>::neg_impl(*self)
            }
        }

        impl_basic_traits!($($rest)*);
    };
}

impl_basic_traits! {
    impl<const M: u32> _ for StaticModInt<M>;
    impl<I: Id       > _ for DynamicModInt<I>;
}

macro_rules! impl_bin_ops {
    () => {};
    (for<$($($generic_param:ident)* : $generic_param_bound:tt),*> <$lhs_ty:ty> ~ <$rhs_ty:ty> -> $output:ty { { $lhs_body:expr } ~ { $rhs_body:expr } } $($rest:tt)*) => {
        impl <$($($generic_param)*: $generic_param_bound),*> Add<$rhs_ty> for $lhs_ty {
            type Output = $output;

            #[inline]
            fn add(self, rhs: $rhs_ty) -> $output {
                <$output>::add_impl(apply($lhs_body, self), apply($rhs_body, rhs))
            }
        }

        impl <$($($generic_param)*: $generic_param_bound),*> Sub<$rhs_ty> for $lhs_ty {
            type Output = $output;

            #[inline]
            fn sub(self, rhs: $rhs_ty) -> $output {
                <$output>::sub_impl(apply($lhs_body, self), apply($rhs_body, rhs))
            }
        }

        impl <$($($generic_param)*: $generic_param_bound),*> Mul<$rhs_ty> for $lhs_ty {
            type Output = $output;

            #[inline]
            fn mul(self, rhs: $rhs_ty) -> $output {
                <$output>::mul_impl(apply($lhs_body, self), apply($rhs_body, rhs))
            }
        }

        impl <$($($generic_param)*: $generic_param_bound),*> Div<$rhs_ty> for $lhs_ty {
            type Output = $output;

            #[inline]
            fn div(self, rhs: $rhs_ty) -> $output {
                <$output>::div_impl(apply($lhs_body, self), apply($rhs_body, rhs))
            }
        }

        impl_bin_ops!($($rest)*);
    };
}

macro_rules! impl_assign_ops {
    () => {};
    (for<$($($generic_param:ident)* : $generic_param_bound:tt),*> <$lhs_ty:ty> ~= <$rhs_ty:ty> { _ ~= { $rhs_body:expr } } $($rest:tt)*) => {
        impl <$($($generic_param)*: $generic_param_bound),*> AddAssign<$rhs_ty> for $lhs_ty {
            #[inline]
            fn add_assign(&mut self, rhs: $rhs_ty) {
                *self = *self + apply($rhs_body, rhs);
            }
        }

        impl <$($($generic_param)*: $generic_param_bound),*> SubAssign<$rhs_ty> for $lhs_ty {
            #[inline]
            fn sub_assign(&mut self, rhs: $rhs_ty) {
                *self = *self - apply($rhs_body, rhs);
            }
        }

        impl <$($($generic_param)*: $generic_param_bound),*> MulAssign<$rhs_ty> for $lhs_ty {
            #[inline]
            fn mul_assign(&mut self, rhs: $rhs_ty) {
                *self = *self * apply($rhs_body, rhs);
            }
        }

        impl <$($($generic_param)*: $generic_param_bound),*> DivAssign<$rhs_ty> for $lhs_ty {
            #[inline]
            fn div_assign(&mut self, rhs: $rhs_ty) {
                *self = *self / apply($rhs_body, rhs);
            }
        }

        impl_assign_ops!($($rest)*);
    };
}

#[inline]
fn apply<F: FnOnce(X) -> O, X, O>(f: F, x: X) -> O {
    f(x)
}

impl_bin_ops! {
    for<const M: u32> <StaticModInt<M>     > ~ <StaticModInt<M>     > -> StaticModInt<M>  { { |x| x  } ~ { |x| x  } }
    for<const M: u32> <StaticModInt<M>     > ~ <&'_ StaticModInt<M> > -> StaticModInt<M>  { { |x| x  } ~ { |&x| x } }
    for<const M: u32> <&'_ StaticModInt<M> > ~ <StaticModInt<M>     > -> StaticModInt<M>  { { |&x| x } ~ { |x| x  } }
    for<const M: u32> <&'_ StaticModInt<M> > ~ <&'_ StaticModInt<M> > -> StaticModInt<M>  { { |&x| x } ~ { |&x| x } }
    for<I: Id       > <DynamicModInt<I>    > ~ <DynamicModInt<I>    > -> DynamicModInt<I> { { |x| x  } ~ { |x| x  } }
    for<I: Id       > <DynamicModInt<I>    > ~ <&'_ DynamicModInt<I>> -> DynamicModInt<I> { { |x| x  } ~ { |&x| x } }
    for<I: Id       > <&'_ DynamicModInt<I>> ~ <DynamicModInt<I>    > -> DynamicModInt<I> { { |&x| x } ~ { |x| x  } }
    for<I: Id       > <&'_ DynamicModInt<I>> ~ <&'_ DynamicModInt<I>> -> DynamicModInt<I> { { |&x| x } ~ { |&x| x } }

    for<const M: u32, T: RemEuclidU32> <StaticModInt<M>     > ~ <T> -> StaticModInt<M>  { { |x| x  } ~ { StaticModInt::<M>::new } }
    for<I: Id     , T: RemEuclidU32> <DynamicModInt<I>    > ~ <T> -> DynamicModInt<I> { { |x| x  } ~ { DynamicModInt::<I>::new } }
}

impl_assign_ops! {
    for<const M: u32> <StaticModInt<M> > ~= <StaticModInt<M>     > { _ ~= { |x| x  } }
    for<const M: u32> <StaticModInt<M> > ~= <&'_ StaticModInt<M> > { _ ~= { |&x| x } }
    for<I: Id       > <DynamicModInt<I>> ~= <DynamicModInt<I>    > { _ ~= { |x| x  } }
    for<I: Id       > <DynamicModInt<I>> ~= <&'_ DynamicModInt<I>> { _ ~= { |&x| x } }

    for<const M: u32, T: RemEuclidU32> <StaticModInt<M> > ~= <T> { _ ~= { StaticModInt::<M>::new } }
    for<I: Id,        T: RemEuclidU32> <DynamicModInt<I>> ~= <T> { _ ~= { DynamicModInt::<I>::new } }
}

macro_rules! impl_folding {
    () => {};
    (impl<$($generic_param:ident)* : $generic_param_bound:tt> $trait:ident<_> for $self:ty { fn $method:ident(_) -> _ { _($unit:expr, $op:expr) } } $($rest:tt)*) => {
        impl<$($generic_param)*: $generic_param_bound> $trait<Self> for $self {
            #[inline]
            fn $method<S>(iter: S) -> Self
            where
                S: Iterator<Item = Self>,
            {
                iter.fold($unit, $op)
            }
        }

        impl<'a, $($generic_param)*: $generic_param_bound> $trait<&'a Self> for $self {
            #[inline]
            fn $method<S>(iter: S) -> Self
            where
                S: Iterator<Item = &'a Self>,
            {
                iter.fold($unit, $op)
            }
        }

        impl_folding!($($rest)*);
    };
}

impl_folding! {
    impl<const M: u32> Sum<_>     for StaticModInt<M>  { fn sum(_)     -> _ { _(Self::new_raw(0), Add::add) } }
    impl<const M: u32> Product<_> for StaticModInt<M>  { fn product(_) -> _ { _(Self::new(1), Mul::mul) } }
    impl<I: Id       > Sum<_>     for DynamicModInt<I> { fn sum(_)     -> _ { _(Self::new_raw(0), Add::add) } }
    impl<I: Id       > Product<_> for DynamicModInt<I> { fn product(_) -> _ { _(Self::new(1), Mul::mul) } }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn static_modint() {
        let (x, y) = (StaticModInt::<7>::new(5), StaticModInt::<7>::new(4));
        assert_eq!(2, (x + y).val());
        assert_eq!(1, (x - y).val());
        assert_eq!(6, (x * y).val());
        assert_eq!(3, (x / y).val());

        let (x, y) = (StaticModInt::<13>::new(7), StaticModInt::<13>::new(8));
        assert_eq!(2, (x + y).val());
        assert_eq!(12, (x - y).val());
        assert_eq!(4, (x * y).val());
        assert_eq!(9, (x / y).val());

        let (x, y) = (StaticModInt::<10>::new(6), StaticModInt::<10>::new(7));
        assert_eq!(3, (x + y).val());
        assert_eq!(9, (x - y).val());
        assert_eq!(2, (x * y).val());
        assert_eq!(8, (x / y).val());

        // Supports moduli larger than 2^31
        let x = StaticModInt::<3758096383>::new(2147483647_u32);
        let y = StaticModInt::<3758096383>::new(3000000019_u32);
        assert_eq!(1389387283, (x + y).val());
        assert_eq!(2905580011, (x - y).val());
        assert_eq!(3009253001, (x * y).val());
    }

    #[test]
    fn dynamic_modint_small() {
        for m in 1..=100 {
            ModInt::set_modulus(m);
            for a in 0..m {
                let a = ModInt::new(a);
                for b in 0..m {
                    let b = ModInt::new(b);
                    assert_eq!((a + b).val(), (a.val() + b.val()) % m);
                    assert_eq!((a - b).val(), (m + a.val() - b.val()) % m);
                    assert_eq!((a * b).val(), (a.val() * b.val()) % m);
                }
            }
        }
    }

    #[test]
    fn dynamic_modint_large() {
        ModInt::set_modulus(3758096383);
        let x = ModInt::new(2147483647_u32);
        let y = ModInt::new(3000000019_u32);
        assert_eq!(1389387283, (x + y).val());
        assert_eq!(2905580011, (x - y).val());
        assert_eq!(3009253001, (x * y).val());
    }
}
