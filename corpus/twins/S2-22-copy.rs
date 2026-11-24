// Twin of TESTING 18's `S2-22-copy` (corpus row S2-22-copy): `x += bump(&x);
// console.log(x);` with `let x: i64 = 1` and a `bump(x: &i64): i64` that runs
// `*x = 100;` and returns `10`. Enrang reads the old Copy value before the right
// side (SPEC O6) and prints `11`; rustc runs the right side first, so this twin
// prints `110` (TESTING 18's twin column). Both compile.

fn bump(x: &mut i64) -> i64 {
    *x = 100;
    10
}

fn main() {
    let mut x: i64 = 1;
    x += bump(&mut x);
    println!("{}", x);
}
