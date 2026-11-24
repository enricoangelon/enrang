// Twin of TESTING 18's `TK-03-last-two` (corpus row TK-03-last-two): `public
// function lastTwo(xs: &Slice<i64>): [&i64, &i64] | null`, whose loop runs `if
// (*x > 2) { b = a; a = x; }` and which returns `[a, b]` after it, with the writes
// of `TK-03-first-two` (`if (p != null) { *p[0] = 0; *p[1] = 0; }`) over `let r:
// i64[] = [1, 5, 3, 7, 1];`.
//
// Enrang makes the pair read-only (EN0616 at the first write, help: return the
// pair inside the loop). The twin over `iter_mut` compiles and prints `[1, 5, 0,
// 0, 1]`. `lastTwo` returns a writable result, so it has two twins (TESTING 13),
// and the call, which writes through it, uses `last_two_mut`.

#![allow(dead_code)]

fn last_two(xs: &[i64]) -> Option<(&i64, &i64)> {
    let mut a: Option<&i64> = None;
    let mut b: Option<&i64> = None;
    for x in xs.iter() {
        if *x > 2 {
            b = a;
            a = Some(x);
        }
    }
    if let (Some(a), Some(b)) = (a, b) {
        return Some((a, b));
    }
    None
}

fn last_two_mut(xs: &mut [i64]) -> Option<(&mut i64, &mut i64)> {
    let mut a: Option<&mut i64> = None;
    let mut b: Option<&mut i64> = None;
    for x in xs.iter_mut() {
        if *x > 2 {
            b = a;
            a = Some(x);
        }
    }
    if let (Some(a), Some(b)) = (a, b) {
        return Some((a, b));
    }
    None
}

fn main() {
    let mut r: Vec<i64> = vec![1, 5, 3, 7, 1];
    let p = last_two_mut(&mut r);
    if let Some(p) = p {
        *p.0 = 0;
        *p.1 = 0;
    }
    println!("{:?}", r);
}
