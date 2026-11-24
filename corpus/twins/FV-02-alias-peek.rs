// Twin of TESTING 18's `FV-02-alias-peek` (corpus row FV-02-alias-peek): in the
// `Copier` of `FV-02-alias`,
//
// public static peekAlias(s: &u8[], d: &u8[]): void {
//   let w = Copier.make(s, d); const p = w.dst; w.src = p; console.log(*w.peek());
// }
//
// then `const tbl: u8[] = [0]; let buf: u8[] = [1]; Copier.peekAlias(&tbl,
// &buf);`.
//
// Enrang rejects it with EN0616 at `w.src = p`, and nothing else. rustc rejects
// such a store only at a later write through `dst` or a move of `w`: the twin,
// with `where 'a: 'r`, compiles and prints `1`.
//
// `src` is `readonly &`, so `&'r Vec<u8>`; `step` writes through `dst`, so it is
// `&'a mut Vec<u8>` (TESTING 13). `p` is only read, so its copy out of `dst` is a
// shared reborrow.

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

    fn peek_alias(s: &'r Vec<u8>, d: &'a mut Vec<u8>)
    where
        'a: 'r,
    {
        let mut w = Copier::make(s, d);
        let p = &*w.dst;
        w.src = p;
        println!("{}", *w.peek());
    }
}

fn main() {
    let tbl: Vec<u8> = vec![0];
    let mut buf: Vec<u8> = vec![1];
    Copier::peek_alias(&tbl, &mut buf);
}
