// Twin of TESTING 18's `FV-02-closure` (corpus row FV-02-closure): the second
// `Copier` of `FV-02-whole-write`, with `private src: readonly &Slice<u8>;`,
// `private dst: &Slice<u8>;` and `private pos: isize;`,
//
// public step(): void { this.dst[this.pos] = this.src[this.pos]; this.pos += 1; }
// public peek(): readonly &Slice<u8> { return this.src.slice(this.pos, this.pos + 1); }
// public retarget(s: &Slice<u8>): void { this.src = s; this.pos = 0; }
//
// and `function run(f: () => void): void { f(); }`, then `const table: u8[3] = [7,
// 8, 9]; let out: u8[3] = [0, 0, 0]; let c = new Copier(&table, &out); const a =
// c.peek(); c.step(); console.log(a);` and `run(() => { const b = c.peek();
// c.step(); console.log(b); }); console.log(out);`.
//
// Enrang rejects it with EN0706 at `c.step()` inside the arrow: a read through
// `_env` holds the capture's loan. The twin `run(&mut || { let b = c.peek();
// c.step(); println!("{:?}", b); })` compiles and prints `[7]`, `[8]` and `[7, 8,
// 0]`.
//
// `src` is `readonly &`, so `&'r [u8]`, and `peek` reaches it only through that
// field, so it returns `&'r [u8]`; `step` writes through `dst`, so it is `&'a mut
// [u8]` (TESTING 13). `slice` applies SPEC 8.2's index rule.

#![allow(dead_code)]

/// `xs.slice(a, b)` by SPEC 8.2's index rule, JavaScript's, which never panics.
fn slice<T>(xs: &[T], a: isize, b: isize) -> &[T] {
    let n = xs.len() as isize;
    let clamp = |i: isize| (if i < 0 { (n + i).max(0) } else { i.min(n) }) as usize;
    let (a, b) = (clamp(a), clamp(b));
    if a >= b {
        &xs[a..a]
    } else {
        &xs[a..b]
    }
}

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
        self.dst[self.pos as usize] = self.src[self.pos as usize];
        self.pos += 1;
    }

    fn peek(&self) -> &'r [u8] {
        slice(self.src, self.pos, self.pos + 1)
    }

    fn retarget(&mut self, s: &'r [u8]) {
        self.src = s;
        self.pos = 0;
    }
}

fn run(f: &mut dyn FnMut()) {
    f();
}

fn main() {
    let table: [u8; 3] = [7, 8, 9];
    let mut out: [u8; 3] = [0, 0, 0];
    let mut c = Copier::new(&table, &mut out);
    let a = c.peek();
    c.step();
    println!("{:?}", a);
    run(&mut || {
        let b = c.peek();
        c.step();
        println!("{:?}", b);
    });
    println!("{:?}", out);
}
