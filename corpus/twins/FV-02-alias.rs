// Twin of TESTING 18's `FV-02-alias` (corpus row FV-02-alias), its form with
// `const q = w.src; w.src = q;`, the named disagreement:
//
// public final class Copier {
//   private src: readonly &u8[]; private dst: &u8[];
//   public constructor(s: &u8[], d: &u8[]) { this.src = s; this.dst = d; }
//   public static make(s: &u8[], d: &u8[]): Copier { return new Copier(s, d); }
//   public peek(): readonly &u8 { return &this.src[0]; }
//   public step(): void { this.dst.push(1); }
//   public static alias(s: &u8[], d: &u8[]): Copier {
//     let w = Copier.make(s, d); const q = w.src; w.src = q; return w;
//   }
// }
//
// then `let buf: u8[] = [1]; const tbl: u8[] = [0]; let c = Copier.alias(&tbl,
// &buf); const a = c.peek(); c.step(); c.step(); c.step(); c.step();
// console.log(*a);`.
//
// Enrang rejects it with EN0616 at `w.src = q` and EN0709 at `return w`. The twin
// `let q = w.src; w.src = q;` compiles and prints `0`.
//
// A borrowing class becomes a struct with two lifetimes (TESTING 13): `'r` for its
// `readonly &` field `src`, `&'r Vec<u8>`, and `'a` for `dst`, `&'a mut Vec<u8>`,
// since `step` writes through it; `peek` reaches the value only through `src` and
// has no other source, so it returns `&'r u8`.

#![allow(dead_code)]

// Fields in reverse declaration order (TESTING 13, drop order).
struct Copier<'r, 'a> {
    dst: &'a mut Vec<u8>,
    src: &'r Vec<u8>,
}

impl<'r, 'a> Copier<'r, 'a> {
    fn new(s: &'r Vec<u8>, d: &'a mut Vec<u8>) -> Copier<'r, 'a> {
        Copier { dst: d, src: s }
    }

    fn make(s: &'r Vec<u8>, d: &'a mut Vec<u8>) -> Copier<'r, 'a> {
        Copier::new(s, d)
    }

    fn peek(&self) -> &'r u8 {
        &self.src[0]
    }

    fn step(&mut self) {
        self.dst.push(1);
    }

    fn alias(s: &'r Vec<u8>, d: &'a mut Vec<u8>) -> Copier<'r, 'a> {
        let mut w = Copier::make(s, d);
        let q = w.src;
        w.src = q;
        w
    }
}

fn main() {
    let mut buf: Vec<u8> = vec![1];
    let tbl: Vec<u8> = vec![0];
    let mut c = Copier::alias(&tbl, &mut buf);
    let a = c.peek();
    c.step();
    c.step();
    c.step();
    c.step();
    println!("{}", *a);
}
