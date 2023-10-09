// verification-helper: PROBLEM https://onlinejudge.u-aizu.ac.jp/problems/DSL_2_A

use procon_lib::algebraic::Min;
use procon_lib::segtree::SegTree;
use proconio::{fastout, input};

#[fastout]
fn main() {
    input! {
        n: usize,
        q: usize,
        queries: [(usize, usize, usize); q],
    }

    let mut segtree = SegTree::<Min<usize>>::from(vec![(1 << 31) - 1; n]);
    for (com, x, y) in queries {
        if com == 0 {
            segtree.set(x, y);
        } else {
            println!("{}", segtree.prod(x..=y));
        }
    }
}
