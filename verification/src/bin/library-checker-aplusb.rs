// verification-helper: PROBLEM https://judge.yosupo.jp/problem/aplusb

use procon_lib::aplusb;
use proconio::input;

fn main() {
    input! {
        a: u64,
        b: u64,
    }

    let ans = aplusb::add(a, b);
    println!("{}", ans);
}
