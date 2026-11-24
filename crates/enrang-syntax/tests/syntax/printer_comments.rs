//! SPEC 12.5's Comments bullet and the comment places of ARCHITECTURE 2.3: comments
//! come from the source between token spans and keep their text and order, apart
//! from the indentation and trailing spaces the bullet allows. Every row also passes
//! the four tests of TESTING 17 (`fmt::four_tests`), whose comment test checks
//! exactly that.

use enrang_testkit::Harness;

use crate::fmt::{fmt, four_tests};

/// One row: a name, the input, and the formatted text.
type Row = (&'static str, &'static str, &'static str);

const ROWS: &[Row] = &[
    (
        "no space is added after //",
        "//no space\nconst a = 1;  //tight\n",
        "//no space\nconst a = 1;  //tight\n",
    ),
    (
        "//~ and //! anchors are untouched",
        "const a = 1; //~ EN0100 \"expected\"\n//! a module note\nconst b = 2;\n",
        "const a = 1;  //~ EN0100 \"expected\"\n//! a module note\nconst b = 2;\n",
    ),
    (
        "a trailing comment gets exactly 2 spaces, never aligned",
        "const a = 1;      // one\nconst bb = 22;// two\n",
        "const a = 1;  // one\nconst bb = 22;  // two\n",
    ),
    (
        "a comment right after { stays on that line",
        "private function f(): void { // why\n  a();\n}\npublic class A {    // fields\n  public x: i64;\n}\n",
        "private function f(): void {  // why\n  a();\n}\npublic class A {  // fields\n  public x: i64;\n}\n",
    ),
    (
        "a // comment moves to the code's indentation and loses trailing spaces",
        "private function f(): void {\n        // deep   \n  a();\n// shallow\n  b();\n}\n",
        "private function f(): void {\n  // deep\n  a();\n  // shallow\n  b();\n}\n",
    ),
    (
        "a block comment of * lines is reprinted at the code's indentation plus one",
        "private function f(): void {\n      /**\n        * doc   \n           */\n  a();\n}\n",
        "private function f(): void {\n  /**\n   * doc\n   */\n  a();\n}\n",
    ),
    (
        "any other block comment is printed as written, only its first line moves",
        "private function f(): void {\n      /* not\n           a star */\n  a();\n}\n",
        "private function f(): void {\n  /* not\n           a star */\n  a();\n}\n",
    ),
    (
        "a one-line block comment does not split a short body",
        "if (a) { /* why */ return; }\n",
        "if (a) { /* why */ return; }\n",
    ),
    (
        "a block comment before the closing brace of a one-line body stays inline",
        "if (a) { return; /* why */ }\n",
        "if (a) { return; /* why */ }\n",
    ),
    (
        "it becomes a trailing comment when the body splits",
        "if (a) { return someFunctionWithAVeryLongName(firstArgumentHere, secondArgumentHere123456); /* why */ }\n",
        "if (a) {\n  return someFunctionWithAVeryLongName(firstArgumentHere, secondArgumentHere123456);  /* why */\n}\n",
    ),
    (
        "a // comment inside splits a body",
        "if (a) { return; // why\n}\n",
        "if (a) {\n  return;  // why\n}\n",
    ),
    (
        "a body holding only a comment puts it on its own line",
        "private function f(): void { /* nothing */ }\nprivate function g(): void {\n  // nothing\n}\n",
        "private function f(): void {\n  /* nothing */\n}\nprivate function g(): void {\n  // nothing\n}\n",
    ),
    (
        "comments may run past the width",
        "// a comment that is much longer than one hundred columns, which no rule ever breaks or reflows at all\nconst a = 1;  // and a trailing comment that also runs well past the hundredth column of the line\n",
        "// a comment that is much longer than one hundred columns, which no rule ever breaks or reflows at all\nconst a = 1;  // and a trailing comment that also runs well past the hundredth column of the line\n",
    ),
    (
        "comments between and after statements keep their places and blank lines",
        "// head\n\nconst a = 1;\n// before b\nconst b = 2;\n\n// tail\n",
        "// head\n\nconst a = 1;\n// before b\nconst b = 2;\n\n// tail\n",
    ),
    (
        "a block comment between two statements on one line ends the first one's line",
        "private function f(): void {\n  c(); /* inline */ d();\n}\n",
        "private function f(): void {\n  c();  /* inline */\n  d();\n}\n",
    ),
    (
        "a block comment before code on its line stays on that line",
        "public class A {\n  /* c */ public y: i64;\n}\n",
        "public class A {\n  /* c */ public y: i64;\n}\n",
    ),
    (
        "comments in a broken list stay beside their items and before the closer",
        "const a = f(\n  x, // the x\n  y,\n);\nconst b = [\n  1,  // one\n  // two next\n  2,\n  // done\n];\n",
        "const a = f(\n  x,  // the x\n  y,\n);\nconst b = [\n  1,  // one\n  // two next\n  2,\n  // done\n];\n",
    ),
    (
        "a comment in an empty list stays inside it",
        "const h = [\n  // empty\n];\nconst g = f(/* nothing */);\nconst o = { /* nothing */ };\n",
        "const h = [\n  // empty\n];\nconst g = f(/* nothing */);\nconst o = { /* nothing */ };\n",
    ),
    (
        "a block comment inside an expression stays in place",
        "const d = /* pre */ 5;\nconst e = 1 + /* mid */ 2;\nconst f2 = g(a /* last */);\n",
        "const d = /* pre */ 5;\nconst e = 1 + /* mid */ 2;\nconst f2 = g(a /* last */);\n",
    ),
    (
        "a comment after a parameter stays with it",
        "function k(\n  a: i64, // first\n  b: i64,\n): void {}\nconst q = (a: i64 /* the a */) => a;\n",
        "function k(\n  a: i64,  // first\n  b: i64,\n): void {}\nconst q = (a: i64 /* the a */) => a;\n",
    ),
    (
        "a comment after the } of an if moves else to the next line",
        "if (a) {\n  b();\n} // after if\nelse {\n  c();\n}\n",
        "if (a) {\n  b();\n}  // after if\nelse {\n  c();\n}\n",
    ),
    (
        "a comment between } and else goes on its own line",
        "if (a) {\n  b();\n}\n// otherwise\nelse {\n  c();\n}\n",
        "if (a) {\n  b();\n}\n// otherwise\nelse {\n  c();\n}\n",
    ),
    (
        "a comment after a decorator stays on its line, and the declaration follows",
        "@entry // the entry\npublic function main(): void {\n  run();\n}\n",
        "@entry  // the entry\npublic function main(): void { run(); }\n",
    ),
    (
        "a comment between decorators and the declaration stays before it",
        "@packed\n// laid out by hand\npublic class Gdt {\n  public limit: u16;\n}\n",
        "@packed\n// laid out by hand\npublic class Gdt {\n  public limit: u16;\n}\n",
    ),
    (
        "a // comment before the { of a body goes inside, never leaving { alone",
        "function f() // why\n{\n  run();\n}\nconst x = match (y) // m\n{\n  default => 3,\n};\n",
        "function f() {\n  // why\n  run();\n}\nconst x = match (y) {\n  // m\n  default => 3,\n};\n",
    ),
    (
        "a block comment before the { of a body on its line stays before it",
        "private function g() /* c */ {\n  run();\n}\n",
        "private function g() /* c */ { run(); }\n",
    ),
    (
        "a comment before ? or : of a broken ternary goes before the operator",
        "const m = cond\n  // why\n  ? yes\n  : no;\nconst n = cond // why\n  ? yes // because\n  : no;\n",
        "const m =\n  cond\n    // why\n    ? yes\n    : no;\nconst n =\n  cond  // why\n    ? yes  // because\n    : no;\n",
    ),
    (
        "a comment between operands stays before its operand",
        "const t = first +\n  // the second\n  second;\n",
        "const t =\n  first +\n  // the second\n  second;\n",
    ),
    (
        "comments between match arms and after them keep their places",
        "match (s) {\n  // the first\n  1 => a(), // after one\n  /* two */ 2 => b(),\n  default => c(),\n  // done\n}\n",
        "match (s) {\n  // the first\n  1 => a(),  // after one\n  /* two */ 2 => b(),\n  default => c(),\n  // done\n}\n",
    ),
    (
        "comments between class members, enum cases and interface members",
        "public class A {\n  // x\n  public x: i64; // the x\n\n  // m\n  public m(): void {}\n}\npublic enum E {\n  A, // a\n  // b\n  B,\n}\npublic interface I {\n  // f\n  f(): void;\n}\n",
        "public class A {\n  // x\n  public x: i64;  // the x\n\n  // m\n  public m(): void {}\n}\npublic enum E {\n  A,  // a\n  // b\n  B,\n}\npublic interface I {\n  // f\n  f(): void;\n}\n",
    ),
    (
        "comments inside asm options keep their places",
        "private function outb(port: u16, value: u8): void {\n  unsafe {\n    asm(\"out dx, al\", {\n      in: { dx: port }, // the port\n      out: { al: value /* the value */ },\n      clobbers: [\n        // none\n      ],\n    });\n    asm(\"hlt\", { /* nothing */ });\n  }\n}\n",
        "private function outb(port: u16, value: u8): void {\n  unsafe {\n    asm(\"out dx, al\", {\n      in: { dx: port },  // the port\n      out: { al: value /* the value */ },\n      clobbers: [\n        // none\n      ],\n    });\n    asm(\"hlt\", { /* nothing */ });\n  }\n}\n",
    ),
    (
        "comments inside a node kept by enrang-fmt-ignore stay as written",
        "// enrang-fmt-ignore\nconst m = [1,0,   // row one\n           0,1];  // row two\nconst   n = 1;\n",
        "// enrang-fmt-ignore\nconst m = [1,0,   // row one\n           0,1];  // row two\nconst n = 1;\n",
    ),
    (
        "comments in imports keep their group as written",
        "// the imports\nimport { o } from \"os\";  // os first\nimport { c } from \"core\";\n",
        "// the imports\nimport { o } from \"os\";  // os first\nimport { c } from \"core\";\n",
    ),
    (
        "two block comments after code stay in order on its line",
        "a(); /* x */ /* y */\nb();\n",
        "a();  /* x */ /* y */\nb();\n",
    ),
    (
        "a // comment ends its line, so a later one on the statement's line moves down",
        "a//\n;//\nconst x = a // one\n; // two\nconst y = b /* x */ // one\n; /* z */ // two\n",
        "a;  //\n//\nconst x = a;  // one\n// two\nconst y = b;  /* x */ // one\n/* z */ // two\n",
    ),
    // The review of the printer stage.
    (
        "a comment after `=` trails it, and the value continues on the next line",
        "public function f(): i64 {\n  const x = // c\n    5;\n  let y = 1;\n  y += // d\n    2;\n  return // e\n    x + y;\n}\n",
        "public function f(): i64 {\n  const x =  // c\n    5;\n  let y = 1;\n  y +=  // d\n    2;\n  return  // e\n    x + y;\n}\n",
    ),
    (
        "a comment after `=>` trails it",
        "const g = (x: i64) => // line\n  x;\nconst h = match (x) {\n  1 => // one\n    10,\n  default => return // none\n    0,\n};\n",
        "const g = (x: i64) =>  // line\n  x;\nconst h = match (x) {\n  1 =>  // one\n    10,\n  default => return  // none\n    0,\n};\n",
    ),
    (
        "a comment after an arm value's `,` trails it",
        "const r = match (x) {\n  1, // one\n    2 => 10,\n  default => 1,\n};\n",
        "const r = match (x) {\n  1,  // one\n    2 => 10,\n  default => 1,\n};\n",
    ),
    (
        "a comment after a `|` trails it",
        "public type T = \"a\" | // first\n  \"b\";\npublic type U = A | // a\n  B | null;\n",
        "public type T = \"a\" |  // first\n  \"b\";\npublic type U = A |  // a\n  B |\n  null;\n",
    ),
    (
        "a comment after an implements `,` trails it",
        "public class C implements A, // a\n  B {}\n",
        "public class C implements\n  A,  // a\n  B {}\n",
    ),
    (
        "a comment right after `{` of a brace list stays on that line",
        "const o = { // c\n  a: 1,\n  b: 2,\n};\nconst p = new P { // d\n  x: 1,\n};\n",
        "const o = {  // c\n  a: 1,\n  b: 2,\n};\nconst p = new P {  // d\n  x: 1,\n};\n",
    ),
    (
        "a comment right after `{` of an import list stays on that line",
        "import { // c\n  a,\n  b,\n} from \"x\";\n",
        "import {  // c\n  a,\n  b,\n} from \"x\";\n",
    ),
    (
        "`;` before a trailing comment in an enum",
        "public enum E {\n  A,\n  B; // after b\n  public m(): void {}\n}\n",
        "public enum E {\n  A,\n  B,  // after b\n  ;\n  public m(): void {}\n}\n",
    ),
    (
        "an own-line comment indented with tabs",
        "public function f(): void {\n\ta();\n\t// own line\n\tb();\n}\n",
        "public function f(): void {\n  a();\n  // own line\n  b();\n}\n",
    ),
];

pub fn register(h: &mut Harness) {
    for &(name, input, expected) in ROWS {
        h.case(format!("printer/comments: {name}"), move || {
            four_tests(input, Some(expected))
        });
    }
    h.case(
        "printer/comments: CRLF line ends become LF and lose their CR",
        || {
            let out = fmt("const a = 1; // one\r\n\r\n// two\r\nconst b = 2;\r\n");
            assert_eq!(out, "const a = 1;  // one\n\n// two\nconst b = 2;\n");
        },
    );
    h.case(
        "printer/comments: an ignore-file line with trailing spaces or CRLF",
        || {
            for text in [
                "// enrang-fmt-ignore-file   \nconst   a = 1;\n",
                "// enrang-fmt-ignore-file\r\nconst   a = 1;\r\n",
            ] {
                assert_eq!(fmt(text), text);
            }
        },
    );
    h.case("printer/comments: a file of comments only", || {
        four_tests("  // one\n\n\n/* two */\n", Some("// one\n\n/* two */\n"))
    });
}
