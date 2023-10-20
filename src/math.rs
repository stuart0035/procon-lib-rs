//! Number-theoretic algorithms.

use super::internal_math;
use super::modint::RemEuclidU32;

/// Returns $x^n \bmod m$.
///
/// # Constraints
///
/// - $1 \leq m$
///
/// # Panics
///
/// Panics if the above constraints are not satisfied.
///
/// # Complexity
///
/// - $O(\log n)$
///
/// # Example
///
/// ```
/// use procon_lib::math;
///
/// assert_eq!(math::pow_mod(2, 10000, 7), 2);
/// ```
pub fn pow_mod<T>(x: T, mut exp: u64, m: u32) -> u32
where
    T: RemEuclidU32,
{
    assert!(1 <= m);
    if m == 1 {
        return 0;
    }
    let bt = internal_math::Barrett::new(m);
    let mut res = 1;
    let mut y = x.rem_euclid_u32(m);
    while exp != 0 {
        if exp & 1 != 0 {
            res = bt.mul(res, y);
        }
        y = bt.mul(y, y);
        exp >>= 1;
    }
    res
}

/// Returns an integer $y \in [0, m)$ such that $xy \equiv 1 \pmod m$.
///
/// # Constraints
///
/// - $\gcd(x, m) = 1$
/// - $1 \leq m$
///
/// # Panics
///
/// Panics if the above constraints are not satisfied.
///
/// # Complexity
///
/// - $O(\log m)$
///
/// # Example
///
/// ```
/// use procon_lib::math;
///
/// assert_eq!(math::inv_mod(3, 7), 5);
/// ```
pub fn inv_mod(x: i64, m: i64) -> i64 {
    assert!(1 <= m);
    checked_inv_mod(x, m).expect("the multiplicative inverse does not exist")
}

/// Returns an integer $y \in [0, m)$ such that $xy \equiv 1 \pmod m$,
/// or `None` if $m \le 0$ or $\gcd(x, m) = 1$.
///
/// # Complexity
///
/// - $O(\log m)$
///
/// # Example
///
/// ```
/// use procon_lib::math;
///
/// assert_eq!(math::checked_inv_mod(3, 7), Some(5));
/// assert_eq!(math::checked_inv_mod(0, 7), None);
/// ```
pub const fn checked_inv_mod(x: i64, m: i64) -> Option<i64> {
    if m <= 0 {
        return None;
    }
    match internal_math::inv_gcd(x, m) {
        (1, z) => Some(z),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pow_mod() {
        assert_eq!(pow_mod(0, 0, 1), 0);
        assert_eq!(pow_mod(0, 0, 3), 1);
        assert_eq!(pow_mod(0, 0, 723), 1);
        assert_eq!(pow_mod(0, 0, 998244353), 1);
        assert_eq!(pow_mod(0, 0, 1u32 << 31), 1);

        assert_eq!(pow_mod(0, 1, 1), 0);
        assert_eq!(pow_mod(0, 1, 3), 0);
        assert_eq!(pow_mod(0, 1, 723), 0);
        assert_eq!(pow_mod(0, 1, 998244353), 0);
        assert_eq!(pow_mod(0, 1, 1u32 << 31), 0);

        assert_eq!(pow_mod(0, (1u64 << 63) - 1, 1), 0);
        assert_eq!(pow_mod(0, (1u64 << 63) - 1, 3), 0);
        assert_eq!(pow_mod(0, (1u64 << 63) - 1, 723), 0);
        assert_eq!(pow_mod(0, (1u64 << 63) - 1, 998244353), 0);
        assert_eq!(pow_mod(0, (1u64 << 63) - 1, 1u32 << 31), 0);

        assert_eq!(pow_mod(1, 0, 1), 0);
        assert_eq!(pow_mod(1, 0, 3), 1);
        assert_eq!(pow_mod(1, 0, 723), 1);
        assert_eq!(pow_mod(1, 0, 998244353), 1);
        assert_eq!(pow_mod(1, 0, 1u32 << 31), 1);

        assert_eq!(pow_mod(1, 1, 1), 0);
        assert_eq!(pow_mod(1, 1, 3), 1);
        assert_eq!(pow_mod(1, 1, 723), 1);
        assert_eq!(pow_mod(1, 1, 998244353), 1);
        assert_eq!(pow_mod(1, 1, 1u32 << 31), 1);

        assert_eq!(pow_mod(1, (1u64 << 63) - 1, 1), 0);
        assert_eq!(pow_mod(1, (1u64 << 63) - 1, 3), 1);
        assert_eq!(pow_mod(1, (1u64 << 63) - 1, 723), 1);
        assert_eq!(pow_mod(1, (1u64 << 63) - 1, 998244353), 1);
        assert_eq!(pow_mod(1, (1u64 << 63) - 1, 1u32 << 31), 1);

        assert_eq!(pow_mod((1u64 << 63) - 1, 0, 1), 0);
        assert_eq!(pow_mod((1u64 << 63) - 1, 0, 3), 1);
        assert_eq!(pow_mod((1u64 << 63) - 1, 0, 723), 1);
        assert_eq!(pow_mod((1u64 << 63) - 1, 0, 998244353), 1);
        assert_eq!(pow_mod((1u64 << 63) - 1, 0, 1u32 << 31), 1);

        assert_eq!(pow_mod((1u64 << 63) - 1, (1u64 << 63) - 1, 1), 0);
        assert_eq!(pow_mod((1u64 << 63) - 1, (1u64 << 63) - 1, 3), 1);
        assert_eq!(pow_mod((1u64 << 63) - 1, (1u64 << 63) - 1, 723), 640);
        assert_eq!(
            pow_mod((1u64 << 63) - 1, (1u64 << 63) - 1, 998244353),
            683296792
        );
        assert_eq!(
            pow_mod((1u64 << 63) - 1, (1u64 << 63) - 1, 1u32 << 31),
            2147483647
        );

        assert_eq!(pow_mod(2, 3, 1_000_000_007), 8);
        assert_eq!(pow_mod(5, 7, 1_000_000_007), 78125);
        assert_eq!(pow_mod(123, 456, 1_000_000_007), 565291922);

        assert_eq!(pow_mod(0, u64::MAX, u32::MAX), 0);
        assert_eq!(pow_mod(1, u64::MAX, u32::MAX), 1);
        assert_eq!(pow_mod(2, u64::MAX, u32::MAX), 1u32 << 31);
    }
}
