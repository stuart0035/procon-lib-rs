/// Fast modular by Barrett reduction.
///
/// Reference:
/// - <https://en.wikipedia.org/wiki/Barrett_reduction>
/// - <https://github.com/atcoder/ac-library>
/// - <https://github.com/rust-lang-ja/ac-library-rs>
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct Barrett {
    m: u32,
    im: u64,
}

impl Barrett {
    /// Creates a new `Barrett`.
    pub(super) const fn new(modulus: u32) -> Barrett {
        Barrett {
            m: modulus,
            im: (u64::MAX / modulus as u64).wrapping_add(1),
        }
    }

    /// Returns `m`.
    #[allow(dead_code)]
    #[inline]
    pub(super) const fn modulus(&self) -> u32 {
        self.m
    }

    /// Calculates `a * b % m`.
    ///
    /// * `a` `0 <= a < m`
    /// * `b` `0 <= b < m`
    #[inline]
    pub(super) const fn mul(&self, a: u32, b: u32) -> u32 {
        mul(a, b, self.m, self.im)
    }
}

/// Calculates `a * b % m`.
///
/// * `a` `0 <= a < m`
/// * `b` `0 <= b < m`
/// * `m` `1 <= m < 2^32`
/// * `im` = ceil(2^64 / `m`) = floor((2^64 - 1) / m) + 1
pub(super) const fn mul(a: u32, b: u32, m: u32, im: u64) -> u32 {
    // [1] m = 1
    // a = b = im = 0, so okay

    // [2] m >= 2
    // im = ceil(2^64 / m) = floor((2^64 - 1) / m) + 1
    // -> im * m = 2^64 + r (0 <= r < m)
    // let z = a*b = c*m + d (0 <= c, d < m)
    // a*b * im = (c*m + d) * im = c*(im*m) + d*im = c*2^64 + c*r + d*im
    // c*r + d*im < m * m + m * im < m * m + 2^64 + m = 2^64 + m * (m + 1) < 2^64 * 2
    // ((ab * im) >> 64) == c or c + 1
    let z = a as u64 * b as u64;
    let x = ((z as u128 * im as u128) >> 64) as u64;
    match z.overflowing_sub(x.wrapping_mul(m as u64)) {
        (v, true) => (v as u32).wrapping_add(m),
        (v, false) => v as u32,
    }
}

/// Fast modular by Montgomery reduction.
///
/// Reference:
/// - <https://en.wikipedia.org/wiki/Montgomery_modular_multiplication>
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct Montgomery {
    m: u64,
    m_prime: u64,
    r2: u128,
}

impl Montgomery {
    // R = 2^64

    /// Creates a new `Montgomery`.
    pub(super) const fn new(modulus: u64) -> Self {
        debug_assert!(modulus & 1 == 1);

        // r2 = R^2 % m = 2^128 % m = (2^128 - m) % m
        let r2 = (modulus as u128).wrapping_neg() % modulus as u128;

        // im ≡ m^{-1} mod R
        let mut im = modulus;

        // For all odd m, m * m ≡ 1 (mod 4),
        // and we can use the following identity:
        //
        // a * x ≡ 1 (mod 2^k) -> a * x * (2 - a * x) ≡ 1 (mod 2^2k)
        //
        // Proof:
        // If we have a * x = 1 + n * 2^k, then we have
        // a * x * (2 - a * x) = 2 * a * x - (a * x)^2
        //                     = 2 * (1 + n * 2^k) - (1 + n * 2^k)^2
        //                     = 2 + 2 * n * 2^k - 1 - 2 * n * 2^k - n^2 * 2^2k
        //                     = 1 - n^2 * 2^2k.
        let mut i = 5;
        while i > 0 {
            im = 2u64.wrapping_sub(modulus.wrapping_mul(im)).wrapping_mul(im);
            i -= 1;
        }

        // m′ ≡ −m^{-1} mod R
        let m_prime = im.wrapping_neg();

        Self {
            m: modulus,
            m_prime,
            r2,
        }
    }

    /// Returns `m`.
    #[allow(dead_code)]
    #[inline]
    pub(super) const fn modulus(&self) -> u64 {
        self.m
    }

    /// Montgomery reduction.
    #[inline]
    const fn reduce(&self, t: u128) -> u64 {
        let x = (t as u64).wrapping_mul(self.m_prime) as u128 * self.m as u128;
        let mut result = (t.wrapping_add(x) >> 64) as u64;
        if x >= ((self.m as u128) << 64) - t {
            result = result.wrapping_sub(self.m);
        }
        result
    }

    /// Returns `a * b % m`.
    #[inline]
    pub(super) const fn mul(&self, a: u64, b: u64) -> u64 {
        debug_assert!(a < self.m);
        debug_assert!(b < self.m);
        self.reduce(self.reduce(a as u128 * b as u128) as u128 * self.r2)
    }

    /// Returns `x ^ exp % m`.
    #[inline]
    pub(super) const fn pow(&self, x: u64, mut exp: u64) -> u64 {
        debug_assert!(x < self.m);
        match exp {
            0 => 1,
            1 => x,
            2 => self.mul(x, x),
            _ => {
                let mut res = self.reduce(self.r2) as u128;
                let mut y = self.reduce(x as u128 * self.r2) as u128;
                while exp != 0 {
                    if exp & 1 == 1 {
                        res = self.reduce(res * y) as u128;
                    }
                    y = self.reduce(y * y) as u128;
                    exp >>= 1;
                }
                self.reduce(res)
            }
        }
    }
}

pub(super) const fn inv_gcd(a: i64, b: i64) -> (i64, i64) {
    let a = a.rem_euclid(b);
    if a == 0 {
        return (b, 0);
    }

    let mut s = b;
    let mut t = a;
    let mut m0 = 0;
    let mut m1 = 1;

    while t != 0 {
        let u = s / t;
        s -= t * u;
        m0 -= m1 * u;
        (s, t) = (t, s);
        (m0, m1) = (m1, m0);
    }
    if m0 < 0 {
        m0 += b / s;
    }
    (s, m0)
}

pub(super) const fn is_prime_const(n: u32) -> bool {
    if n == 2 {
        return true;
    }
    if n < 2 || n & 1 == 0 {
        return false;
    }
    if n < 9 {
        return true;
    }
    if n % 3 == 0 || n % 5 == 0 || n % 7 == 0 {
        return false;
    }
    if n < 121 {
        return true;
    }

    const BASES: [u32; 3] = [2, 7, 61];
    let s = (n - 1).trailing_zeros();
    let d = (n - 1) >> s;
    let mut i = 0;
    while i < BASES.len() {
        let mut t = pow_mod_const(BASES[i], d, n);
        let mut s = s;
        while s > 0 && t != 1 && t != n - 1 {
            t = (t as u64 * t as u64 % n as u64) as u32;
            s -= 1;
        }
        if t != 1 && t != n - 1 {
            return false;
        }
        i += 1;
    }
    true
}

const fn pow_mod_const(x: u32, mut exp: u32, m: u32) -> u32 {
    let mut x = x as u64;
    let m = m as u64;
    let mut res = 1;
    while exp > 0 {
        if exp & 1 == 1 {
            res = res * x % m;
        }
        x = x * x % m;
        exp >>= 1;
    }
    res as u32
}

#[cfg(test)]
mod tests {
    extern crate static_assertions as sa;

    use super::{Barrett, Montgomery};

    #[test]
    fn barrett_small() {
        for m in 1..=100 {
            let bt = Barrett::new(m);
            assert_eq!(bt.modulus(), m);
            for a in 0..m {
                for b in 0..m {
                    let ans = (a as u64 * b as u64 % m as u64) as u32;
                    assert_eq!(bt.mul(a, b), ans, "expected {ans} (= {a} * {b} % {m})");
                }
            }
        }
    }

    #[test]
    fn barrett_large() {
        let b = Barrett::new(998244353);
        assert_eq!(b.modulus(), 998244353);
        assert_eq!(b.mul(2, 3), 6);
        assert_eq!(b.mul(3141592, 653589), 919583920);
        assert_eq!(b.mul(323846264, 338327950), 568012980);

        let b = Barrett::new(2147483647);
        assert_eq!(b.modulus(), 2147483647);
        assert_eq!(b.mul(1073741824, 2147483645), 2147483646);

        let b = Barrett::new(3221225471);
        assert_eq!(b.modulus(), 3221225471);
        assert_eq!(b.mul(3188445886, 2844002853), 1840468257);
        assert_eq!(b.mul(2834869488, 2779159607), 2084027561);
        assert_eq!(b.mul(3032263594, 3039996727), 2130247251);
        assert_eq!(b.mul(3029175553, 3140869278), 1892378237);
    }

    #[test]
    fn montgomery_small() {
        for m in (1..=99).step_by(2) {
            let mt = Montgomery::new(m);
            assert_eq!(mt.modulus(), m);
            for a in 0..m {
                for b in 0..m {
                    let ans = a * b % m;
                    assert_eq!(mt.mul(a, b), ans, "expected {ans} (= {a} * {b} % {m})");
                }
            }
        }
    }

    #[test]
    fn montgomery_large() {
        let m = Montgomery::new(998244353);
        assert_eq!(m.modulus(), 998244353);
        assert_eq!(m.mul(2, 3), 6);
        assert_eq!(m.mul(3141592, 653589), 919583920);
        assert_eq!(m.mul(69141883, 43536721), 31892378);

        let m = Montgomery::new(314495938705744139);
        assert_eq!(m.modulus(), 314495938705744139);
        assert_eq!(m.mul(3141592653, 5897932384), 288136600532014690);
        assert_eq!(m.mul(52287926161, 10185274357), 125249279517926150);

        let m = Montgomery::new(u64::MAX);
        assert_eq!(m.modulus(), u64::MAX);
        assert_eq!(m.mul(1 << 32, 1 << 32), 1);
        assert_eq!(m.mul(1 << 30, 1 << 40), 64);
        assert_eq!(m.mul(u64::MAX - 1, u64::MAX - 1), 1);
        assert_eq!(m.mul(u64::MAX - 2, u64::MAX - 3), 6);
    }

    #[test]
    fn montgomery_pow() {
        let m = Montgomery::new(13);
        assert_eq!(m.pow(0, 0), 1);
        assert_eq!(m.pow(1, 1), 1);
        assert_eq!(m.pow(7, 9), 8);

        let m = Montgomery::new(u64::MAX);
        assert_eq!(m.pow(2, 64), 1);
        assert_eq!(m.pow(3, 61), 7838787818839166943);
    }

    #[test]
    fn inv_gcd() {
        inv_gcd_sub(0, 1, 1);
        inv_gcd_sub(0, 7, 7);
        inv_gcd_sub(2, 3, 1);
        inv_gcd_sub(-2, 3, 1);
        inv_gcd_sub(4, 6, 2);
        inv_gcd_sub(-4, 6, 2);
        inv_gcd_sub(12345, 67890, 15);
    }

    fn inv_gcd_sub(a: i64, b: i64, g: i64) {
        let (gcd, x) = super::inv_gcd(a, b);
        assert_eq!(gcd, g);
        let b = b as i128;
        assert_eq!((x as i128 * a as i128).rem_euclid(b), g as i128 % b);
    }

    #[test]
    fn is_prime() {
        sa::const_assert!(!super::is_prime_const(0));
        sa::const_assert!(!super::is_prime_const(1));
        sa::const_assert!(super::is_prime_const(2));
        sa::const_assert!(super::is_prime_const(3));
        sa::const_assert!(!super::is_prime_const(4));
        sa::const_assert!(!super::is_prime_const(57));
        sa::const_assert!(super::is_prime_const(59));
        sa::const_assert!(!super::is_prime_const(805_624_241)); // 15737 * 51193
        sa::const_assert!(super::is_prime_const(998_244_353));
        sa::const_assert!(super::is_prime_const(1_000_000_007));
    }
}
