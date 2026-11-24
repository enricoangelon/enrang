// Twin of TESTING 18's `TK-03-first-two` (corpus row TK-03-first-two):
// `public function firstTwo(xs: &Slice<i64>): [&i64, &i64] | null`, which keeps
// the first element above 2 in `a` and the second in `b`, leaves the loop with
// `break` at the second, and returns `[a, b]` after the loop under `a != null &&
// b != null`; then `if (p != null) { *p[0] = 0; *p[1] = 0; }` over `let q: i64[] =
// [1, 5, 3, 7];`.
//
// Enrang makes the pair read-only (EN0616 at `*p[0] = 0`, help: return the pair
// inside the loop). The twin over `iter_mut` compiles and prints `[1, 0, 0, 7]`.
// `firstTwo` returns a writable result, so it has two twins (TESTING 13), and the
// call, which writes through it, uses `first_two_mut`.

#![allow(dead_code)]

fn first_two(xs: &[i64]) -> Option<(&i64, &i64)> {
    let mut a: Option<&i64> = None;
    let mut b: Option<&i64> = None;
    for x in xs.iter() {
        if *x > 2 {
            if a.is_none() {
                a = Some(x);
            } else {
                b = Some(x);
                break;
            }
        }
    }
    if let (Some(a), Some(b)) = (a, b) {
        return Some((a, b));
    }
    None
}

fn first_two_mut(xs: &mut [i64]) -> Option<(&mut i64, &mut i64)> {
    let mut a: Option<&mut i64> = None;
    let mut b: Option<&mut i64> = None;
    for x in xs.iter_mut() {
        if *x > 2 {
            if a.is_none() {
                a = Some(x);
            } else {
                b = Some(x);
                break;
            }
        }
    }
    if let (Some(a), Some(b)) = (a, b) {
        return Some((a, b));
    }
    None
}

fn main() {
    let mut q: Vec<i64> = vec![1, 5, 3, 7];
    let p = first_two_mut(&mut q);
    if let Some(p) = p {
        *p.0 = 0;
        *p.1 = 0;
    }
    println!("{:?}", q);
}
