// Twin of TESTING 18's `FV-02-field-copy` (corpus row FV-02-field-copy), its
// `show` program, the named disagreement: in the `Copier` of `FV-02-alias`,
//
// public show(): void { const p = this.src; this.step(); console.log(p); }
//
// then `const t: u8[] = [7]; let o: u8[] = []; let c = new Copier(&t, &o);
// c.show(); console.log(o);`.
//
// Enrang rejects it with EN0706 at `this.step()`: `p` holds a loan through `this`.
// The twin, with `src: &'r Vec<u8>`, compiles and prints `[7]` and `[1]`, since
// rustc's borrow of the object does not reach through a shared reference's deref.
//
// `src` is `readonly &`, so `&'r Vec<u8>`; `step` writes through `dst`, so it is
// `&'a mut Vec<u8>` (TESTING 13).

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

    fn show(&mut self) {
        let p = self.src;
        self.step();
        println!("{:?}", p);
    }
}

fn main() {
    let t: Vec<u8> = vec![7];
    let mut o: Vec<u8> = vec![];
    let mut c = Copier::new(&t, &mut o);
    c.show();
    println!("{:?}", o);
}
