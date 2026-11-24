// Twin of TESTING 18's `TK-03-fields-of-turn` (corpus row TK-03-fields-of-turn):
//
// public function firstFields(ps: &Slice<Pair>): [&i64[], &i64[]] | null {
//   for (const p of ps) { return [&p.a, &p.b]; }
//   return null;
// }
// public class Pair { public a: i64[]; public b: i64[]; }
// public function firstDestructured(ps: &Slice<[i64[], i64[]]>): [&i64[], &i64[]] | null {
//   for (const [k, v] of ps) { return [k, v]; }
//   return null;
// }
//
// each called over a one-element `let` array, `[new Pair { a: [1], b: [2] }]` and
// `[[[1], [2]]]`, and followed by `if (r != null) { r[0].push(3); r[1].push(4); }`.
//
// Enrang makes both pairs read-only (EN0614 at `r[0].push(3)`). The `iter_mut`
// twins compile and print `[1, 3] [2, 4] [([1, 3], [2, 4])]`. Each function
// returns a writable result, so it has two twins (TESTING 13), and the calls,
// which write through them, use the `_mut` ones.

#![allow(dead_code)]

// Fields in reverse declaration order (TESTING 13, drop order).
struct Pair {
    b: Vec<i64>,
    a: Vec<i64>,
}

fn first_fields(ps: &[Pair]) -> Option<(&Vec<i64>, &Vec<i64>)> {
    for p in ps.iter() {
        return Some((&p.a, &p.b));
    }
    None
}

fn first_fields_mut(ps: &mut [Pair]) -> Option<(&mut Vec<i64>, &mut Vec<i64>)> {
    for p in ps.iter_mut() {
        return Some((&mut p.a, &mut p.b));
    }
    None
}

fn first_destructured(ps: &[(Vec<i64>, Vec<i64>)]) -> Option<(&Vec<i64>, &Vec<i64>)> {
    for (k, v) in ps.iter() {
        return Some((k, v));
    }
    None
}

fn first_destructured_mut(
    ps: &mut [(Vec<i64>, Vec<i64>)],
) -> Option<(&mut Vec<i64>, &mut Vec<i64>)> {
    for (k, v) in ps.iter_mut() {
        return Some((k, v));
    }
    None
}

fn main() {
    let mut ps: Vec<Pair> = vec![Pair {
        b: vec![2],
        a: vec![1],
    }];
    let r = first_fields_mut(&mut ps);
    if let Some(r) = r {
        r.0.push(3);
        r.1.push(4);
    }
    print!("{:?} {:?} ", ps[0].a, ps[0].b);

    let mut ts: Vec<(Vec<i64>, Vec<i64>)> = vec![(vec![1], vec![2])];
    let r = first_destructured_mut(&mut ts);
    if let Some(r) = r {
        r.0.push(3);
        r.1.push(4);
    }
    println!("{:?}", ts);
}
