// Twin of TESTING 18's `FV-02-upcast-local` (corpus row FV-02-upcast-local), its
// first program, the named disagreement:
//
// public class Base {
//   private src: readonly &Slice<u8>;
//   public constructor(s: &Slice<u8>) { this.src = s; }
//   public peek(): readonly &Slice<u8> { return this.src.slice(0, 1); }
//   public retarget(v: &Slice<u8>): void { this.src = v; }
// }
// public final class Sub extends Base {
//   private dst: &u8[];
//   public constructor(s: &Slice<u8>, d: &u8[]) { this.dst = d; super(s); }
//   public static make(s: &Slice<u8>, d: &u8[]): Sub { return new Sub(s, d); }
//   public step(): void { this.dst.push(1); }
// }
//
// then `const tbl: u8[] = [7, 8]; let buf: u8[] = [0]; let w = Sub.make(&tbl,
// &buf); w.retarget(w.peek()); w.step(); console.log(w.peek()); console.log(buf);`.
//
// Enrang rejects it with EN0616 at `w.retarget(w.peek())`: the read-set check keys
// on `Sub`, whose flag is on, and `w`, returned by a call, counts every loan it
// holds as one `dst` may write through. The twin compiles and prints `[7]` and
// `[0, 1]`.
//
// A subclass becomes a struct whose own fields, reversed, come before a last
// `base` field holding its base class's twin (TESTING 13). `w` is a local of the
// final class `Sub`, so `w.retarget` and `w.peek` are direct calls, which use the
// inherent twins of `Base`'s bodies. `src` is `readonly &`, `&'r [u8]`, and `peek`
// reaches it only through that field, so it returns `&'r [u8]`; `step` writes
// through `dst`, `&'a mut Vec<u8>`. `slice` applies SPEC 8.2's index rule.

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

struct Base<'r> {
    src: &'r [u8],
}

impl<'r> Base<'r> {
    fn new(s: &'r [u8]) -> Base<'r> {
        Base { src: s }
    }

    fn peek(&self) -> &'r [u8] {
        slice(self.src, 0, 1)
    }

    fn retarget(&mut self, v: &'r [u8]) {
        self.src = v;
    }
}

struct Sub<'r, 'a> {
    dst: &'a mut Vec<u8>,
    base: Base<'r>,
}

impl<'r, 'a> Sub<'r, 'a> {
    fn new(s: &'r [u8], d: &'a mut Vec<u8>) -> Sub<'r, 'a> {
        let dst = d;
        Sub {
            dst,
            base: Base::new(s),
        }
    }

    fn make(s: &'r [u8], d: &'a mut Vec<u8>) -> Sub<'r, 'a> {
        Sub::new(s, d)
    }

    fn step(&mut self) {
        self.dst.push(1);
    }
}

fn main() {
    let tbl: Vec<u8> = vec![7, 8];
    let mut buf: Vec<u8> = vec![0];
    let mut w = Sub::make(&tbl, &mut buf);
    w.base.retarget(w.base.peek());
    w.step();
    println!("{:?}", w.base.peek());
    println!("{:?}", buf);
}
