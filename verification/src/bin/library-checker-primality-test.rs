// verification-helper: PROBLEM https://judge.yosupo.jp/problem/primality_test

use procon_lib::primes::is_prime;
use proconio::{fastout, input};

#[fastout]
fn main() {
    input! {
        n: [u64]
    }
    for n in n {
        if is_prime(n) {
            println!("Yes");
        } else {
            println!("No");
        }
    }
}
