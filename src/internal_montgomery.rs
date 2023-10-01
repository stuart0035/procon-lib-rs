pub(crate) const R: u128 = 1 << u64::BITS;

#[derive(Debug, Clone)]
pub(crate) struct Montgomery {
    /// modulus
    m: u128,

    /// mʹ (where mmʹ ≡ -1 mod R)
    m_prime: u128,

    /// R² mod m
    r2: u128,
}

impl Montgomery {
    pub(crate) const fn new(modulus: u64) -> Self {
        debug_assert!(modulus % 2 == 1);

        let m = modulus as u128;
        let r2 = m.wrapping_neg() % m;

        let mut m_prime = modulus;
        let mut i = 0;
        while i < 5 {
            m_prime = 2u64
                .wrapping_sub(modulus.wrapping_mul(m_prime))
                .wrapping_mul(m_prime);
            i += 1;
        }
        let m_prime = m_prime.wrapping_neg() as u128;
        debug_assert!((m * m_prime) % R == R - 1);

        Self { m, m_prime, r2 }
    }

    #[inline]
    const fn reduce(&self, t: u128) -> u128 {
        let (res, ovf) = t.overflowing_add((((t & (R - 1)) * self.m_prime) & (R - 1)) * self.m);
        let mut res = res >> u64::BITS;
        if ovf {
            res += 1 << u64::BITS;
        }
        if res >= self.m {
            res -= self.m
        }
        res
    }

    #[inline]
    pub(crate) const fn mul(&self, a: u64, b: u64) -> u64 {
        debug_assert!(a < self.m as u64);
        debug_assert!(b < self.m as u64);
        let (a, b) = (a as u128, b as u128);
        self.reduce(self.reduce(a * b) * self.r2) as u64
    }

    #[inline]
    pub(crate) const fn pow(&self, a: u64, mut n: u64) -> u64 {
        debug_assert!(a < self.m as u64);
        match n {
            0 => 1,
            1 => a,
            2 => self.mul(a, a),
            _ => {
                let mut res = self.reduce(self.r2);
                let mut a = self.reduce(a as u128 * self.r2);
                while n > 0 {
                    if n & 1 == 1 {
                        res = self.reduce(res * a);
                    }
                    a = self.reduce(a * a);
                    n >>= 1;
                }
                self.reduce(res) as u64
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_montgomery_mul() {
        let monty = Montgomery::new(1);
        assert_eq!(monty.mul(0, 0), 0);

        let monty = Montgomery::new(13);
        assert_eq!(monty.mul(0, 0), 0);
        assert_eq!(monty.mul(1, 1), 1);
        assert_eq!(monty.mul(3, 5), 2);

        let monty = Montgomery::new(998244353);
        assert_eq!(monty.mul(0, 0), 0);
        assert_eq!(monty.mul(1, 1), 1);
        assert_eq!(monty.mul(314159, 265358), 510322623);

        let monty = Montgomery::new(u64::MAX);
        assert_eq!(monty.mul(0, 0), 0);
        assert_eq!(monty.mul(1, 1), 1);
        assert_eq!(monty.mul(1 << 32, 1 << 32), 1);
        assert_eq!(monty.mul(1 << 30, 1 << 40), 64);
    }

    #[test]
    fn test_montgomery_pow() {
        let monty = Montgomery::new(13);
        assert_eq!(monty.pow(0, 0), 1);
        assert_eq!(monty.pow(1, 1), 1);
        assert_eq!(monty.pow(7, 9), 8);

        let monty = Montgomery::new(u64::MAX);
        assert_eq!(monty.pow(2, 64), 1);
        assert_eq!(monty.pow(3, 61), 7838787818839166943);
    }
}
