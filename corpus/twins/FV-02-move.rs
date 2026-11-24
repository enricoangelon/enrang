// Twin of TESTING 18's `FV-02-move` (corpus row FV-02-move), its `skipped`
// program, the named disagreement: in the `Copier` of `FV-02-skip`,
//
// public move skipped(): Copier { this.src = this.src.slice(1, this.src.length()); return this; }
//
// then `const table: u8[3] = [7, 8, 9]; let out: u8[3] = [0, 0, 0]; let c = new
// Copier(&table, &out).skipped(); c.step(); console.log(out);`.
//
// Enrang rejects it with EN0709 at `return this`: the slice's receiver loan,
// taken through `this`, meets the move (SPEC 5.8 H05). The twin `fn skipped(mut
// self) -> Copier<'r, 'a> { self.src = &self.src[1..self.src.len()]; self }`
// compiles and prints `[8, 0, 0]`.
//
// `src` is `readonly &`, so `&'r [u8]`; `step` writes through `dst`, so it is
// `&'a mut [u8]` (TESTING 13).

#![allow(dead_code)]

// Fields in reverse declaration order (TESTING 13, drop order).
struct Copier<'r, 'a> {
    pos: isize,
    dst: &'a mut [u8],
    src: &'r [u8],
}

impl<'r, 'a> Copier<'r, 'a> {
    fn new(src: &'r [u8], dst: &'a mut [u8]) -> Copier<'r, 'a> {
        Copier { pos: 0, dst, src }
    }

    fn step(&mut self) {
        self.dst[self.pos as usize] = self.src[0];
        self.pos += 1;
    }

    fn skip(&mut self) {
        self.src = &self.src[1..self.src.len()];
    }

    fn skipped(mut self) -> Copier<'r, 'a> {
        self.src = &self.src[1..self.src.len()];
        self
    }
}

fn main() {
    let table: [u8; 3] = [7, 8, 9];
    let mut out: [u8; 3] = [0, 0, 0];
    let mut c = Copier::new(&table, &mut out).skipped();
    c.step();
    println!("{:?}", out);
}
