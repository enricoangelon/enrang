// Twin of TESTING 18's `F12` (corpus row F12): Enrang runs the calls of an
// assignment target first, so `*slot(&xs) = val(&xs);` keeps `xs` borrowed for
// writing across `val` (EN0708), and reads a compound assignment's old Copy value
// before its right side. rustc runs the right side first: this twin compiles and
// prints `val`, `slot`, `[2, 2]`, then `[10]` (TESTING 18's twin column).
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
    // *slot(&xs) = val(&xs);
    let mut xs: Vec<i64> = vec![1, 2];
    *slot_mut(&mut xs) = val(&xs);
    println!("{:?}", xs);

    // xs[0] += (xs[0] = 5); with xs = [1]: an assignment's value is its target
    // read after the store (SPEC 3.5).
    let mut xs: Vec<i64> = vec![1];
    xs[0] += {
        xs[0] = 5;
        xs[0]
    };
    println!("{:?}", xs);
}
