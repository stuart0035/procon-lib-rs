// verification-helper: PROBLEM https://onlinejudge.u-aizu.ac.jp/problems/DSL_1_B

use procon_lib::WeightedUnionFind;
use proconio::input;

fn main() {
    input! {
        n: usize,
        q: usize,
    }
    let mut uf = WeightedUnionFind::<i64>::new(n, 0);
    for _ in 0..q {
        input! { t: usize }
        if t == 0 {
            input! {
                x: usize,
                y: usize,
                z: i64,
            }
            uf.union(x, y, z);
        } else {
            input! {
                x: usize,
                y: usize,
            }
            match uf.diff(x, y) {
                Some(d) => println!("{}", d),
                None => println!("?"),
            }
        }
    }
}
