// Twin of `tests/compile/EN0701/array_of_a_borrowing_class.fail.en`, one of
// Enrang's own R1 rejections (corpus row R1, TESTING 13): an array can't hold a
// `Lexer`, because `Lexer` holds a reference (SPEC 5.1, EN0701). rustc has
// lifetimes, so a `Vec<Lexer<'a>>` compiles.
//
// const source = "let x = 1;";
// let lx = new Lexer(&source);
// let all: Lexer[] = [lx];
//
// private class Lexer {
//   private src: &string;
//   private pos: isize = 0;
//   public constructor(src: &string) { this.src = src; }
// }

#![allow(dead_code)]

// Fields in reverse declaration order (TESTING 13, drop order). No body of
// `Lexer` writes through `src`, so it is `&'a str` (TESTING 13).
struct Lexer<'a> {
    pos: isize,
    src: &'a str,
}

impl<'a> Lexer<'a> {
    fn new(src: &'a str) -> Lexer<'a> {
        Lexer { pos: 0, src }
    }
}

fn main() {
    let source: String = "let x = 1;".to_string();
    let lx = Lexer::new(&source);
    let all: Vec<Lexer> = vec![lx];
    println!("{}", all.len());
}
