// Twin of TESTING 18's `FV-02-through-ref` (corpus row FV-02-through-ref), its
// last program, the named disagreement: SPEC 5.1's `Lexer` with
//
// public setSrc(s: &string): void { this.src = s; }
// public static demo(): void {
//   const base = "ab".toString(); const other = "xy".toString();
//   let lx = new Lexer(&base); const r = &lx; const t = r.src.slice(0, 1);
//   lx.setSrc(&other); console.log(t);
// }
//
// Enrang rejects it with EN0706 at `lx.setSrc(&other)`: the token read through
// `r.src` keeps `r`'s loan on `lx`. rustc types `src` as a shared reference, whose
// deref outlives the borrow of `lx`: the twin compiles and prints `a`.
//
// No body of `Lexer` writes through `src`, so it is `&'a str` (TESTING 13; the
// lifetime FV-02-lost-store's twin gives it). `slice` applies SPEC 8.2's index
// rule over byte indexes, moving an index inside a character back to its start.

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

// `Lexer.demo`, a static method that uses no lifetime of the class.
fn demo() {
    let base: String = "ab".to_string();
    let other: String = "xy".to_string();
    let mut lx = Lexer::new(&base);
    let r = &lx;
    let t = slice(r.src, 0, 1);
    lx.set_src(&other);
    println!("{}", t);
}

fn main() {
    demo();
}
