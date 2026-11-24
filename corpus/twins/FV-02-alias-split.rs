// Twin of TESTING 18's `FV-02-alias-split` (corpus row FV-02-alias-split), its
// third program, the named disagreement:
//
// public final class Splitter {
//   private src: readonly &Slice<string>; private dst: &Slice<string>;
//   public constructor(x: &Slice<string>) { const [a, b] = x.splitAt(1); this.src = a; this.dst = b; }
//   public peek(): readonly &string { return &this.src[0]; }
//   public step(): void { this.dst[0] = "zz".toString(); }
//   public static peekFused(x: &Slice<string>): void {
//     let w = new Splitter(x); w.src = w.dst; console.log(*w.peek());
//   }
// }
//
// then `let words: string[] = ["a".toString(), "b".toString()];
// Splitter.peekFused(&words);`.
//
// Enrang rejects it with EN0616 at `w.src = w.dst`, and nothing else. The twin,
// with `split_at_mut` and `w.src = &*w.dst;`, compiles and prints `b`.
//
// `src` is `readonly &`, so `&'r [String]`; `step` writes through `dst`, so it is
// `&'a mut [String]` (TESTING 13). The constructor stores the two parts of one
// `split_at_mut` of `x`, one into each field, so `x` takes `'a` with `'a: 'r`.

#![allow(dead_code)]

// Fields in reverse declaration order (TESTING 13, drop order).
struct Splitter<'r, 'a> {
    dst: &'a mut [String],
    src: &'r [String],
}

impl<'r, 'a: 'r> Splitter<'r, 'a> {
    fn new(x: &'a mut [String]) -> Splitter<'r, 'a> {
        let (a, b) = x.split_at_mut(1);
        Splitter { dst: b, src: a }
    }

    fn peek(&self) -> &'r String {
        &self.src[0]
    }

    fn step(&mut self) {
        self.dst[0] = "zz".to_string();
    }

    fn peek_fused(x: &'a mut [String]) {
        let mut w = Splitter::new(x);
        w.src = &*w.dst;
        println!("{}", *w.peek());
    }
}

fn main() {
    let mut words: Vec<String> = vec!["a".to_string(), "b".to_string()];
    Splitter::peek_fused(&mut words);
}
