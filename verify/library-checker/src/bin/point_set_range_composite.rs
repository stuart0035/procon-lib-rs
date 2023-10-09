// verification-helper: PROBLEM https://judge.yosupo.jp/problem/point_set_range_composite

use procon_lib::algebraic::Monoid;
use procon_lib::segtree::SegTree;
use proconio::{fastout, input};

const MOD: u64 = 998244353;

#[derive(Debug, Clone, Copy)]
struct LinearFn {
    a: u64,
    b: u64,
}

struct Composite;
impl Monoid for Composite {
    type S = LinearFn;
    fn id() -> Self::S {
        LinearFn { a: 1, b: 0 }
    }
    fn op(a: &Self::S, b: &Self::S) -> Self::S {
        let (lhs, rhs) = (a, b);
        let a = lhs.a * rhs.a % MOD;
        let b = (lhs.b * rhs.a + rhs.b) % MOD;
        LinearFn { a, b }
    }
}

#[fastout]
fn main() {
    input! {
        n: usize,
        q: usize,
        ab: [(u64, u64); n],
    }

    let base = ab
        .into_iter()
        .map(|(a, b)| LinearFn { a, b })
        .collect::<Vec<_>>();

    let mut segtree = SegTree::<Composite>::from(base);
    for _ in 0..q {
        input! { t: u32 }
        if t == 0 {
            input! {
                p: usize,
                c: u64,
                d: u64,
            }
            segtree.set(p, LinearFn { a: c, b: d });
        } else {
            input! {
                l: usize,
                r: usize,
                x: u64,
            }
            let LinearFn { a, b } = segtree.prod(l..r);
            println!("{}", (a * x + b) % MOD);
        }
    }
}
