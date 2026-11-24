// Twin of TESTING 18's `FV-02-reset` (corpus row FV-02-reset), its second
// program, the named disagreement:
//
// public final class Copier {
//   private src: readonly &u8[]; private dst: &u8[] | null;
//   public constructor(s: &u8[]) { this.src = s; }
//   public static make(s: &u8[], d: &u8[]): Copier { let c = new Copier(s); c.dst = d; return c; }
//   public reset(u: Copier): void { *this = u; }
//   public peek(): readonly &u8 { return &this.src[0]; }
//   public step(): void { this.dst!.push(1); }
//   public static demo(): void {
//     let buf: u8[] = [1]; const tbl: u8[] = [0]; let c = new Copier(&tbl);
//     c.reset(Copier.make(&tbl, &buf));
//     const p = c.dst!; c.src = p; console.log(*c.peek());
//   }
// }
//
// Enrang rejects it with EN0616 at `c.src = p`, since a value reset through a
// by-value parameter counts everything it holds as held by `dst`. rustc rejects
// such a store only at a later write through `dst` or a move: the twin, with
// `fn reset(&mut self, u: Copier<'r, 'a>) { *self = u; }`, compiles and prints
// `1`.
//
// `src` is `readonly &`, so `&'r Vec<u8>`; `step` writes through `dst`, so it is
// `Option<&'a mut Vec<u8>>` (TESTING 13). `p` is only read, so its copy out of
// `dst` is a shared reborrow.

#![allow(dead_code)]

// Fields in reverse declaration order (TESTING 13, drop order).
struct Copier<'r, 'a> {
    dst: Option<&'a mut Vec<u8>>,
    src: &'r Vec<u8>,
}

impl<'r, 'a> Copier<'r, 'a> {
    fn new(s: &'r Vec<u8>) -> Copier<'r, 'a> {
        Copier { dst: None, src: s }
    }

    fn make(s: &'r Vec<u8>, d: &'a mut Vec<u8>) -> Copier<'r, 'a> {
        let mut c = Copier::new(s);
        c.dst = Some(d);
        c
    }

    fn reset(&mut self, u: Copier<'r, 'a>) {
        *self = u;
    }

    fn peek(&self) -> &'r u8 {
        &self.src[0]
    }

    fn step(&mut self) {
        self.dst.as_mut().unwrap().push(1);
    }
}

// `Copier.demo`, a static method that uses neither lifetime of the class.
fn demo() {
    let mut buf: Vec<u8> = vec![1];
    let tbl: Vec<u8> = vec![0];
    let mut c = Copier::new(&tbl);
    c.reset(Copier::make(&tbl, &mut buf));
    let p: &Vec<u8> = c.dst.as_deref().unwrap();
    c.src = p;
    println!("{}", *c.peek());
}

fn main() {
    demo();
}
