// Twin of TESTING 18's `FV-02-lost-store` (corpus row FV-02-lost-store), its two
// programs that are the named disagreement:
//
// SPEC 5.1's `Lexer` with `public setSrc(s: &string): void { this.src = s; }` and
// public static configure(let lx: Lexer, s: &string): Lexer { lx.setSrc(s); return lx; }
//
// and, in the `Copier` of `FV-02-alias` with `public retarget(v: &u8[]): void {
// this.src = v; }`,
// public static rebuild(w: Copier, s: &u8[]): Copier {
//   let c = new Copier(s, w.dst); c.retarget(s); return c;
// }
// then `const tbl: u8[] = [0]; let buf: u8[] = [1]; const other: u8[] = [5]; let
// c = Copier.rebuild(new Copier(&tbl, &buf), &other); c.step(); console.log(*c.peek());
// console.log(buf);`.
//
// Enrang rejects both with EN0616 (at `lx.setSrc(s)` and at `c.retarget(s)`),
// since the keys cannot tell a by-value value from what its fields reach. The
// twins compile: `fn configure<'a>(mut lx: Lexer<'a>, s: &'a str) -> Lexer<'a>`
// prints `xy` for a `b` holding `xy`, and `fn rebuild(w: Copier<'r, 'a>, s: &'r
// Vec<u8>) -> Copier<'r, 'a>` prints `5` then `[1, 1]`.
//
// No body of `Lexer` writes through `src`, so it is `&'a str`; `Copier`'s `src` is
// `readonly &`, `&'r Vec<u8>`, and `step` writes through `dst`, `&'a mut Vec<u8>`
// (TESTING 13).

#![allow(dead_code)]

/// `s.slice(a, b)` by SPEC 8.2's index rule, which never panics.
fn slice(s: &str, a: isize, b: isize) -> &str {
    let n = s.len() as isize;
    let clamp = |i: isize| {
        let mut i = (if i < 0 { (n + i).max(0) } else { i.min(n) }) as usize;
        while !s.is_char_boundary(i) {
            i -= 1;
        }
        i
    };
    let (a, b) = (clamp(a), clamp(b));
    if a >= b {
        &s[a..a]
    } else {
        &s[a..b]
    }
}

// Fields in reverse declaration order (TESTING 13, drop order).
struct Lexer<'a> {
    pos: isize,
    src: &'a str,
}

impl<'a> Lexer<'a> {
    fn new(src: &'a str) -> Lexer<'a> {
        Lexer { pos: 0, src }
    }

    fn next(&mut self) -> Option<&'a str> {
        if self.pos >= self.src.len() as isize {
            return None;
        }
        let start = self.pos;
        self.pos = self.src.len() as isize; // a sketch: the rest of the text is one token
        Some(slice(self.src, start, self.pos))
    }

    fn set_src(&mut self, s: &'a str) {
        self.src = s;
    }
}

fn configure<'a>(mut lx: Lexer<'a>, s: &'a str) -> Lexer<'a> {
    lx.set_src(s);
    lx
}

// Fields in reverse declaration order (TESTING 13, drop order).
struct Copier<'r, 'a> {
    dst: &'a mut Vec<u8>,
    src: &'r Vec<u8>,
}

impl<'r, 'a> Copier<'r, 'a> {
    fn new(s: &'r Vec<u8>, d: &'a mut Vec<u8>) -> Copier<'r, 'a> {
        Copier { dst: d, src: s }
    }

    fn peek(&self) -> &'r u8 {
        &self.src[0]
    }

    fn step(&mut self) {
        self.dst.push(1);
    }

    fn retarget(&mut self, v: &'r Vec<u8>) {
        self.src = v;
    }

    fn rebuild(w: Copier<'r, 'a>, s: &'r Vec<u8>) -> Copier<'r, 'a> {
        let mut c = Copier::new(s, w.dst);
        c.retarget(s);
        c
    }
}

fn main() {
    let a: String = "ab".to_string();
    let b: String = "xy".to_string();
    let mut lx = configure(Lexer::new(&a), &b);
    println!("{}", lx.next().unwrap_or(""));

    let tbl: Vec<u8> = vec![0];
    let mut buf: Vec<u8> = vec![1];
    let other: Vec<u8> = vec![5];
    let mut c = Copier::rebuild(Copier::new(&tbl, &mut buf), &other);
    c.step();
    println!("{}", *c.peek());
    println!("{:?}", buf);
}
