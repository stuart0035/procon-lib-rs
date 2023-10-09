// verification-helper: PROBLEM https://judge.yosupo.jp/problem/factorize

use procon_lib::primes::factorize;
use proconio::{fastout, input};

#[fastout]
fn main() {
    input! {
        a: [u64]
    }
    for a in a {
        let f = factorize(a);
        let f = f.into_iter().map(|x| format!(" {}", x)).collect::<Vec<_>>();
        println!("{}{}", f.len(), f.join(""));
    }
}
