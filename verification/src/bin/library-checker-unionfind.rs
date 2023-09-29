// verification-helper: PROBLEM https://judge.yosupo.jp/problem/unionfind

use procon_lib::UnionFind;
use proconio::input;

fn main() {
    input! {
        n: usize,
        queries: [(usize, usize, usize)],
    }
    let mut uf = UnionFind::new(n);
    for (t, u, v) in queries {
        if t == 0 {
            uf.union(u, v);
        } else if uf.is_same(u, v) {
            println!("1");
        } else {
            println!("0");
        }
    }
}
