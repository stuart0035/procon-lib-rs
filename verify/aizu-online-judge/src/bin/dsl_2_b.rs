// verification-helper: PROBLEM https://onlinejudge.u-aizu.ac.jp/problems/DSL_2_B

use procon_lib::{Additive, FenwickTree};
use proconio::{fastout, input, marker::Usize1};

#[fastout]
fn main() {
    input! {
        n: usize,
        q: usize,
    }
    let mut fw = FenwickTree::<Additive<_>>::new(n);
    for _ in 0..q {
        input! { com: usize }
        if com == 0 {
            input! {
                x: Usize1,
                y: i64,
            }
            fw.add(x, y);
        } else {
            input! {
                x: Usize1,
                y: Usize1,
            }
            println!("{}", fw.sum(x..=y));
        }
    }
}
