// verification-helper: PROBLEM https://judge.yosupo.jp/problem/double_ended_priority_queue

use procon_lib::IntervalHeap;
use proconio::{fastout, input};

#[fastout]
fn main() {
    input! {
        n: usize,
        q: usize,
        s: [i32; n],
    }
    let mut heap = IntervalHeap::from(s);
    for _ in 0..q {
        input! { t: usize }
        match t {
            0 => {
                input! { x: i32 }
                heap.push(x);
            }
            1 => println!("{}", heap.pop_min().unwrap()),
            2 => println!("{}", heap.pop_max().unwrap()),
            _ => unreachable!(),
        }
    }
}
