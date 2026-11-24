// Twin of TESTING 18's `OQ25-order` (corpus row OQ25-order): `*slot(&xs) =
// val(&ys);` with `xs` and `ys` both `[1, 2]`. Enrang runs the target's call
// first and prints `slot`, `val`, `[2, 2]`; rustc runs the right side first, so
// this twin prints `val`, `slot`, `[2, 2]` (TESTING 18's twin column). Both
// compile: the disagreement is the order of the output.
//
// `slot` returns a writable `&i64` that the assignment writes through, so the call
// uses its `get_mut` twin `slot_mut` (TESTING 13).

#![allow(dead_code)]

fn slot(xs: &Vec<i64>) -> &i64 {
    println!("slot");
    &xs[0]
}

fn slot_mut(xs: &mut Vec<i64>) -> &mut i64 {
    println!("slot");
    &mut xs[0]
}

fn val(xs: &Vec<i64>) -> i64 {
    println!("val");
    xs[1]
}

fn main() {
    let mut xs: Vec<i64> = vec![1, 2];
    let ys: Vec<i64> = vec![1, 2];
    *slot_mut(&mut xs) = val(&ys);
    println!("{:?}", xs);
}
