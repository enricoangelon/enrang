// Twin of TESTING 18's `FV-02-skip` (corpus row FV-02-skip), its two programs that
// are the named disagreement, over a `Copier` with `private src: readonly
// &Slice<u8>;`, `private dst: &Slice<u8>;` and `private pos: isize;`,
//
// public step(): void { this.dst[this.pos] = this.src[0]; this.pos += 1; }
// public skip(): void { this.src = this.src.slice(1, this.src.length()); }
//
// and `function twice(c: &Copier): void { c.skip(); c.step(); }`:
//
// 1. with `function id(x: &Copier): &Copier { return x; }`, `const table: u8[3] =
//    [7, 8, 9]; let out: u8[3] = [0, 0, 0]; let c = new Copier(&table, &out);
//    const r = id(&c); r.skip(); c.step(); console.log(out);`, which Enrang rejects
//    with EN0707 at `c.step()`; the twin with `fn id<'x, 'r, 'a>(x: &'x mut
//    Copier<'r, 'a>) -> &'x mut Copier<'r, 'a>` prints `[8, 0, 0]`;
// 2. `public final class Wrapper { private cp: &Copier; public constructor(cp:
//    &Copier) { this.cp = cp; } public static nudge(w: &Wrapper): void {
//    w.cp.skip(); } }`, then `let c = new Copier(&table, &out); let w = new
//    Wrapper(&c); Wrapper.nudge(&w); c.step(); console.log(out);`, which Enrang
//    rejects with EN0616 at `Wrapper.nudge(&w)`; the twin with `fn nudge(w: &mut
//    Wrapper) { w.cp.skip(); }` prints `[8, 0, 0]`.
//
// `src` is `readonly &`, so `&'r [u8]`; `step` writes through `dst`, so it is
// `&'a mut [u8]`, and `Wrapper`'s `cp` is `&'w mut Copier`, since `nudge` writes
// through it (TESTING 13). `skip` is the row's `fn skip(&mut self) { self.src =
// &self.src[1..self.src.len()]; }`. `id` and `twice` return or take a reference
// that is written through, so they use their writing twins.

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
}

fn twice(c: &mut Copier) {
    c.skip();
    c.step();
}

fn id<'x, 'r, 'a>(x: &'x mut Copier<'r, 'a>) -> &'x mut Copier<'r, 'a> {
    x
}

struct Wrapper<'w, 'r, 'a> {
    cp: &'w mut Copier<'r, 'a>,
}

impl<'w, 'r, 'a> Wrapper<'w, 'r, 'a> {
    fn new(cp: &'w mut Copier<'r, 'a>) -> Wrapper<'w, 'r, 'a> {
        Wrapper { cp }
    }
}

fn nudge(w: &mut Wrapper) {
    w.cp.skip();
}

fn main() {
    {
        let table: [u8; 3] = [7, 8, 9];
        let mut out: [u8; 3] = [0, 0, 0];
        let mut c = Copier::new(&table, &mut out);
        let r = id(&mut c);
        r.skip();
        c.step();
        println!("{:?}", out);
    }
    {
        let table: [u8; 3] = [7, 8, 9];
        let mut out: [u8; 3] = [0, 0, 0];
        let mut c = Copier::new(&table, &mut out);
        let mut w = Wrapper::new(&mut c);
        nudge(&mut w);
        c.step();
        println!("{:?}", out);
    }
}
