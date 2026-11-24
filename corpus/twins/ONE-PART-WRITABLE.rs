// Twin of `tests/compile/EN0706/one-part-writable.pass.en` (corpus row
// ONE-PART-WRITABLE, TESTING 13): a body that forms a writable result with one
// reference part, from a parameter it does not also store, while a second
// reference to the same parameter is live. Enrang accepts it, since such a result
// needs no exclusive-access proof in the callee (SPEC 5.4); rustc rejects the
// `get_mut` twin, whose `&mut xs[0]` meets the live `second`.
//
// let xs: i64[] = [1, 2];
// *pick(&xs) = 5;
// console.log(xs);
//
// public function pick(xs: &i64[]): &i64 {
//   const second = &xs[1];
//   const first = &xs[0];
//   console.log(*second);
//   return first;
// }
//
// `pick` returns a writable `&i64`, so it has two twins (TESTING 13), and the
// call, which writes through the result, uses `pick_mut`.

#![allow(dead_code)]

fn pick(xs: &Vec<i64>) -> &i64 {
    let second = &xs[1];
    let first = &xs[0];
    println!("{}", *second);
    first
}

fn pick_mut(xs: &mut Vec<i64>) -> &mut i64 {
    let second = &xs[1];
    let first = &mut xs[0];
    println!("{}", *second);
    first
}

fn main() {
    let mut xs: Vec<i64> = vec![1, 2];
    *pick_mut(&mut xs) = 5;
    println!("{:?}", xs);
}
