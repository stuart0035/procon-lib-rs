use crate::internal_montgomery::Montgomery;

const BASES_SMALL: [u64; 3] = [2, 7, 61];
const BASES_LARGE: [u64; 7] = [2, 325, 9375, 28178, 450775, 9780504, 1795265022];

/// Checks if an integer is prime.
///
/// This function uses a deterministic variant of the Miller-Rabin primality test.
///
/// # Examples
///
/// ```
/// use procon_lib::primes::is_prime;
///
/// assert!(!is_prime(0));
/// assert!(!is_prime(1));
/// assert!(is_prime(2));
/// assert!(is_prime(3));
/// assert!(!is_prime(4));
/// assert!(is_prime(31));
/// assert!(!is_prime(57));
/// ```
pub fn is_prime(n: u64) -> bool {
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
    miller_rabin(n, &Montgomery::new(n))
}

/// Factorizes an integer into prime factors, returning them in ascending order.
///
/// Returns an empty [`Vec`] if the given integer is 0 or 1.
///
/// This function uses a deterministic variant of the Miller-Rabin primality test
/// and Pollard's rho algorithm.
///
/// # Examples
///
/// ```
/// use procon_lib::primes::factorize;
///
/// assert_eq!(factorize(0), []);
/// assert_eq!(factorize(1), []);
/// assert_eq!(factorize(2), [2]);
/// assert_eq!(factorize(3), [3]);
/// assert_eq!(factorize(57), [3, 19]);
/// assert_eq!(factorize(121), [11, 11]);
/// assert_eq!(factorize(180), [2, 2, 3, 3, 5]);
/// assert_eq!(factorize(111111), [3, 7, 11, 13, 37]);
/// ```
pub fn factorize(n: u64) -> Vec<u64> {
    if n == 0 {
        return vec![];
    }
    let ctz = n.trailing_zeros() as usize;
    let n = n >> ctz;
    let mut res = vec![2; ctz];
    if n > 1 {
        factorize_sub(n, &mut res);
        res.sort_unstable();
    }
    res
}

fn miller_rabin(n: u64, monty: &Montgomery) -> bool {
    debug_assert_eq!(n % 2, 1);
    debug_assert!(n > 61);

    let s = (n - 1).trailing_zeros();
    let d = (n - 1) >> s;

    let f = |a| {
        let mut t = monty.pow(a, d);
        if t == 1 || t == n - 1 {
            return true;
        }
        for _ in 1..s {
            t = monty.mul(t, t);
            if t == n - 1 {
                return true;
            }
        }
        false
    };

    let bases = if n < 1 << 32 {
        BASES_SMALL.to_vec()
    } else {
        BASES_LARGE.to_vec()
    };

    bases.into_iter().all(f)
}

fn factorize_sub(n: u64, res: &mut Vec<u64>) {
    debug_assert_eq!(n % 2, 1);
    debug_assert!(n >= 3);

    if n < 9 {
        res.push(n);
        return;
    }
    if n % 3 == 0 {
        res.push(3);
        factorize_sub(n / 3, res);
        return;
    }
    if n % 5 == 0 {
        res.push(5);
        factorize_sub(n / 5, res);
        return;
    }
    if n % 7 == 0 {
        res.push(7);
        factorize_sub(n / 7, res);
        return;
    }
    if n < 121 {
        res.push(n);
        return;
    }
    let monty = Montgomery::new(n);
    if miller_rabin(n, &monty) {
        res.push(n);
        return;
    }
    let d = find_divisor(n, &monty);
    factorize_sub(d, res);
    factorize_sub(n / d, res);
}

/// Pollard's rho algorithm
fn find_divisor(n: u64, monty: &Montgomery) -> u64 {
    debug_assert_eq!(n % 2, 1);
    debug_assert!(n >= 121);

    let m = (n as f64).powf(0.125) as u64;
    for c in 1..n {
        let f = |x| {
            let mut res = monty.mul(x, x);
            if res >= n - c {
                res = res.wrapping_sub(n);
            }
            res.wrapping_add(c)
        };
        let mut x0 = 0;
        let mut y0 = 0;
        let mut x = 0;
        let mut y = 0;
        let mut g = 1;
        let mut q = 1;
        while g == 1 {
            (x0, y0) = (x, y);
            for _ in 0..m {
                x = f(x);
                y = f(f(y));
                q = monty.mul(q, x.abs_diff(y));
            }
            g = gcd(n, q);
        }
        if 1 < g && g < n {
            return g;
        }
        (x, y) = (x0, y0);
        loop {
            x = f(x);
            y = f(f(y));
            g = gcd(n, x.abs_diff(y));
            if 1 < g && g < n {
                return g;
            }
            if g == n {
                break;
            }
        }
    }
    unreachable!();
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    if a < b {
        std::mem::swap(&mut a, &mut b);
    }
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prime() {
        assert!(!is_prime(0));
        assert!(!is_prime(1));
        assert!(is_prime(2));
        assert!(is_prime(3));
        assert!(!is_prime(4));
        assert!(is_prime(5));
        assert!(!is_prime(6));
        assert!(is_prime(7));
        assert!(!is_prime(8));
        assert!(!is_prime(9));
        assert!(is_prime(31));
        assert!(!is_prime(57));
        assert!(!is_prime(121));
        assert!(is_prime(294936923));
        assert!(!is_prime(3427836479));
        assert!(!is_prime(103890955799));
        assert!(is_prime(7230348073755451703));
        assert!(!is_prime(15085450279637773827));
    }

    #[test]
    fn test_factorize() {
        assert_eq!(factorize(0), []);
        assert_eq!(factorize(1), []);
        assert_eq!(factorize(2), [2]);
        assert_eq!(factorize(3), [3]);
        assert_eq!(factorize(4), [2, 2]);
        assert_eq!(factorize(5), [5]);
        assert_eq!(factorize(6), [2, 3]);
        assert_eq!(factorize(7), [7]);
        assert_eq!(factorize(8), [2, 2, 2]);
        assert_eq!(factorize(9), [3, 3]);
        assert_eq!(factorize(1194508291), [1194508291]);
        assert_eq!(factorize(2932189941842519), [239, 239, 263, 499, 599, 653]);
        assert_eq!(factorize(494735143715855249), [11437, 19309, 31607, 70879]);
        assert_eq!(factorize(856767094714903492), [2, 2, 257510657, 831778289]);
        assert_eq!(factorize(6584979800587831631), [6584979800587831631]);
        assert_eq!(factorize(16394442362560039097), [1905509897, 8603703601]);
    }
}
