// Twin of TESTING 18's `TK-02-reassign-break` (corpus row TK-02-reassign-break),
// its first program, the named disagreement:
//
// let q: i64[] = [1, 5, 3, 7]; let o: i64[] = [0]; let r = &q;
// let keep: &i64 | null = null;
// for (const x of r) { if (*x > 2) { keep = x; r = &o; break; } }
// if (keep != null) { *keep = 0; }
// console.log(r); console.log(q);
//
// Enrang accepts it: the `break` ends the hold, so it is dead at `r = &o`, and
// prints `[0]` and `[1, 0, 3, 7]`. `r` is a reference slot that can be repointed
// (a `let` local) and the body assigns it, and `x` is written through after the
// loop through `keep`, so the loop becomes `let s = &mut r; for x in s.iter_mut()`
// (TESTING 13), and `keep` keeps `s` alive: E0506 `cannot assign to `r` because
// it is borrowed`.

fn main() {
    let mut q: Vec<i64> = vec![1, 5, 3, 7];
    let mut o: Vec<i64> = vec![0];
    let mut r: &mut Vec<i64> = &mut q;
    let mut keep: Option<&mut i64> = None;
    let s = &mut r;
    for x in s.iter_mut() {
        if *x > 2 {
            keep = Some(x);
            r = &mut o;
            break;
        }
    }
    if let Some(keep) = keep {
        *keep = 0;
    }
    println!("{:?}", r);
    println!("{:?}", q);
}
