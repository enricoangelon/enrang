// Twin of TESTING 18's `TK-01-local-ref` (corpus row TK-01-local-ref):
//
// public function pair(p: &P): [&i64[], &i64[]] { const r = &p.inner; return [&r.a, &r.b]; }
// public class Inner { public a: i64[]; public b: i64[]; }
// public class P { public inner: Inner; }
//
// then `let p = new P { inner: new Inner { a: [1], b: [2] } }; const [x, y] =
// pair(&p); x.push(3); y.push(4);`.
//
// Enrang makes the pair read-only (EN0614 at `x.push(3)`): both parts hold `r`'s
// loan on `p.inner`. The twin, `let r = &mut p.inner; (&mut r.a, &mut r.b)`,
// compiles and prints `[1, 3] [2, 4]`. `pair` returns a writable result, so it has
// two twins (TESTING 13), and the call, which writes through it, uses `pair_mut`.

#![allow(dead_code)]

// Fields in reverse declaration order (TESTING 13, drop order).
struct Inner {
    b: Vec<i64>,
    a: Vec<i64>,
}

struct P {
    inner: Inner,
}

fn pair(p: &P) -> (&Vec<i64>, &Vec<i64>) {
    let r = &p.inner;
    (&r.a, &r.b)
}

fn pair_mut(p: &mut P) -> (&mut Vec<i64>, &mut Vec<i64>) {
    let r = &mut p.inner;
    (&mut r.a, &mut r.b)
}

fn main() {
    let mut p = P {
        inner: Inner {
            b: vec![2],
            a: vec![1],
        },
    };
    let (x, y) = pair_mut(&mut p);
    x.push(3);
    y.push(4);
    println!("{:?} {:?}", p.inner.a, p.inner.b);
}
