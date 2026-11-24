// Twin of TESTING 18's `D20-core-3` (corpus row D20-core-3), its third program,
// the named disagreement:
//
// let keep: [&string, int] = ["none", 0];
// const tmp = "xy" + "z";
// { const pair: [&string, int] = [&tmp, 1]; const r = &pair; keep = *r; }
// console.log(keep[0]);
//
// Enrang rejects it with EN0711 where `pair` is dropped: a copy through `r` keeps
// `r`'s own loan on `pair` (SPEC O9). rustc copies the tuple with no borrow of
// `pair`: the twin compiles and prints `xyz`.

#![allow(unused_assignments)]

fn main() {
    let mut keep: (&str, i64) = ("none", 0);
    let tmp: String = String::from("xy") + "z";
    {
        let pair: (&str, i64) = (&tmp, 1);
        let r = &pair;
        keep = *r;
    }
    println!("{}", keep.0);
}
