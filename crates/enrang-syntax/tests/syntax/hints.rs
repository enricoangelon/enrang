//! The TypeScript habits (EN02xx) and the deferred features of SPEC 16 (EN10xx)
//! that phase 1 reports, and the test-file codes EN1102, EN1105 and EN1112: each
//! fires at its primary span with its message and nothing else, and a near miss
//! reports nothing. Every EN10xx message head and help is read from SPEC 16's
//! table, and every fix-it here is applied and checked.

use enrang_diag::{Code, EntryKind, Owner, Phase, apply_fixes};
use enrang_testkit::Harness;

use crate::parser::{Parsed, shape};
use crate::recovery::{Fires, NearMiss, check_fires, check_near_miss};
use crate::support::{doc, section};

const SPREAD: &str = "rest, and spread outside an array literal, are not supported yet";

pub const FIRES: &[Fires] = &[
    // EN0201 (SPEC 2, G03).
    (
        "EN0201/===",
        "s.en",
        "const y = a === b;\n",
        &[(Code::EN0201, "===", "`===` does not exist in Enrang")],
    ),
    (
        "EN0201/!==",
        "s.en",
        "const y = a !== b;\n",
        &[(Code::EN0201, "!==", "`!==` does not exist in Enrang")],
    ),
    // EN0202 (G04).
    (
        "EN0202/a statement",
        "s.en",
        "var x = 1;\n",
        &[(Code::EN0202, "var", "`var` does not exist in Enrang")],
    ),
    (
        "EN0202/a for loop",
        "s.en",
        "for (var i = 0; i < 3; i++) {}\n",
        &[(Code::EN0202, "var", "`var` does not exist in Enrang")],
    ),
    (
        "EN0202/a for...of loop",
        "s.en",
        "for (var x of xs) {}\n",
        &[(Code::EN0202, "var", "`var` does not exist in Enrang")],
    ),
    // EN0205 (G04).
    (
        "EN0205/a parameter",
        "s.en",
        "public function f(x: any): void {}\n",
        &[(Code::EN0205, "any", "`any` does not exist in Enrang")],
    ),
    (
        "EN0205/a local",
        "s.en",
        "let x: any[] = [];\n",
        &[(Code::EN0205, "any", "`any` does not exist in Enrang")],
    ),
    // EN0206 (G04).
    (
        "EN0206/a value",
        "s.en",
        "const x = undefined;\n",
        &[(
            Code::EN0206,
            "undefined",
            "`undefined` does not exist in Enrang",
        )],
    ),
    (
        "EN0206/a type",
        "s.en",
        "let x: string | undefined = null;\n",
        &[(
            Code::EN0206,
            "undefined",
            "`undefined` does not exist in Enrang",
        )],
    ),
    // EN0207.
    (
        "EN0207/throw",
        "s.en",
        "throw new Error(\"x\");\nf();\n",
        &[(Code::EN0207, "throw", "`throw` does not exist in Enrang")],
    ),
    (
        "EN0207/try",
        "s.en",
        "try {\n  f();\n} catch (e) {\n  g();\n}\n",
        &[(Code::EN0207, "try", "`try` does not exist in Enrang")],
    ),
    (
        "EN0207/a stray catch",
        "s.en",
        "catch (e) {\n  g();\n}\n",
        &[(Code::EN0207, "catch", "`catch` does not exist in Enrang")],
    ),
    // EN0208.
    (
        "EN0208/>>>",
        "s.en",
        "const y = x >>> 2;\n",
        &[(Code::EN0208, ">>>", "`>>>` does not exist in Enrang")],
    ),
    // EN0209.
    (
        "EN0209/switch",
        "s.en",
        "switch (x) {\n  case 1: f();\n}\ng();\n",
        &[(Code::EN0209, "switch", "`switch` does not exist in Enrang")],
    ),
    (
        "EN0209/case in a match",
        "s.en",
        "const y = match (x) { case 1: 2, default => 3 };\n",
        &[(Code::EN0209, "case", "`case` does not exist in Enrang")],
    ),
    // EN0210.
    (
        "EN0210/unknown",
        "s.en",
        "public function f(x: unknown): void {}\n",
        &[(
            Code::EN0210,
            "unknown",
            "`unknown` does not exist in Enrang",
        )],
    ),
    // EN0211.
    (
        "EN0211/typeof",
        "s.en",
        "const t = typeof x;\n",
        &[(Code::EN0211, "typeof", "`typeof` does not exist in Enrang")],
    ),
    (
        "EN0211/instanceof",
        "s.en",
        "if (a instanceof B) {}\n",
        &[(
            Code::EN0211,
            "instanceof",
            "`instanceof` does not exist in Enrang",
        )],
    ),
    (
        "EN0211/typeof as a type",
        "s.en",
        "let y: typeof x = x;\n",
        &[(Code::EN0211, "typeof", "`typeof` does not exist in Enrang")],
    ),
    // EN0213.
    (
        "EN0213/using",
        "s.en",
        "using r = open();\n",
        &[(Code::EN0213, "using", "`using` does not exist in Enrang")],
    ),
    // EN0215.
    (
        "EN0215/two object types",
        "s.en",
        "let x: { a: i64 } | { b: i64 } = y;\n",
        &[(Code::EN0215, "|", "`|` cannot join object types")],
    ),
    // EN0216.
    (
        "EN0216/outside an alias",
        "s.en",
        "let d: \"left\" | \"right\" = \"left\";\n",
        &[(
            Code::EN0216,
            "\"left\"",
            "a string literal as a type goes only in a `type` alias",
        )],
    ),
    (
        "EN0216/a string in an object type in an alias",
        "s.en",
        "private type S = { kind: \"circle\" };\n",
        &[(
            Code::EN0216,
            "\"circle\"",
            "a string literal as a type goes only in a `type` alias",
        )],
    ),
    (
        "EN0216/a string first, then a type",
        "s.en",
        "private type T = \"a\" | i64;\n",
        &[(
            Code::EN0216,
            "i64",
            "a string-literal union cannot mix with other types",
        )],
    ),
    (
        "EN0216/a type first, then a string",
        "s.en",
        "private type T = i64 | \"a\";\n",
        &[(
            Code::EN0216,
            "\"a\"",
            "a string-literal union cannot mix with other types",
        )],
    ),
    // EN0218.
    (
        "EN0218/a function expression",
        "s.en",
        "const f = function (x: i64): i64 { return x; };\n",
        &[(
            Code::EN0218,
            "function",
            "`function` expressions do not exist in Enrang",
        )],
    ),
    // EN0220.
    (
        "EN0220/interface extends",
        "s.en",
        "public interface A extends B, C {\n  m(): void;\n}\n",
        &[(
            Code::EN0220,
            "extends B, C",
            "`interface ... extends` does not exist in Enrang",
        )],
    ),
    // EN0222.
    (
        "EN0222/namespace",
        "s.en",
        "namespace N {\n  const x = 1;\n}\n",
        &[(
            Code::EN0222,
            "namespace",
            "`namespace` does not exist in Enrang",
        )],
    ),
    (
        "EN0222/delete",
        "s.en",
        "delete o.x;\n",
        &[(Code::EN0222, "delete", "`delete` does not exist in Enrang")],
    ),
    // EN0224 (SPEC 3.4).
    (
        "EN0224/a bare parameter with a return type",
        "s.en",
        "const f = x: i64 => x * 2;\n",
        &[(
            Code::EN0224,
            ": i64",
            "a return type needs the arrow's parameters in parentheses",
        )],
    ),
    // EN0225 (SPEC 4.2).
    (
        "EN0225/number",
        "s.en",
        "let n: number = 1;\n",
        &[(Code::EN0225, "number", "`number` does not exist in Enrang")],
    ),
    // EN0226 for `export` (SPEC 3.1).
    (
        "EN0226/export",
        "s.en",
        "export function f(): void {}\n",
        &[(Code::EN0226, "export", "`export` does not exist in Enrang")],
    ),
    // EN0228 (SPEC 6, 4.13).
    (
        "EN0228/an argument",
        "s.en",
        "queue.push(move t);\n",
        &[(Code::EN0228, "move", "`move` is not needed here")],
    ),
    (
        "EN0228/an initialiser",
        "s.en",
        "const b = move r;\n",
        &[(Code::EN0228, "move", "`move` is not needed here")],
    ),
    (
        "EN0228/a spread operand",
        "s.en",
        "const c = [...move a];\n",
        &[(Code::EN0228, "move", "`move` is not needed here")],
    ),
    (
        "EN0228/a loop source",
        "s.en",
        "for (const x of move r) {}\n",
        &[(Code::EN0228, "move", "`move` is not needed here")],
    ),
    // EN1001.
    (
        "EN1001/async function",
        "s.en",
        "public async function f(): void {}\n",
        &[(
            Code::EN1001,
            "async",
            "async functions are not supported yet",
        )],
    ),
    (
        "EN1001/await",
        "s.en",
        "const x = await f();\n",
        &[(
            Code::EN1001,
            "await",
            "async functions are not supported yet",
        )],
    ),
    (
        "EN1001/Promise",
        "s.en",
        "let p: Promise<i64> = q;\n",
        &[(
            Code::EN1001,
            "Promise",
            "async functions are not supported yet",
        )],
    ),
    (
        "EN1001/an async arrow",
        "s.en",
        "const g = async () => 1;\n",
        &[(
            Code::EN1001,
            "async",
            "async functions are not supported yet",
        )],
    ),
    (
        "EN1001/an async method",
        "s.en",
        "public class A {\n  public async m(): void {}\n}\n",
        &[(
            Code::EN1001,
            "async",
            "async functions are not supported yet",
        )],
    ),
    // EN1002.
    (
        "EN1002/function*",
        "s.en",
        "public function* gen(): void {}\n",
        &[(Code::EN1002, "*", "generators are not supported yet")],
    ),
    (
        "EN1002/yield",
        "s.en",
        "const x = yield 1;\n",
        &[(Code::EN1002, "yield", "generators are not supported yet")],
    ),
    (
        "EN1002/a generator method",
        "s.en",
        "public class A {\n  public *gen(): void {}\n}\n",
        &[(Code::EN1002, "*", "generators are not supported yet")],
    ),
    // EN1005 (SPEC 2).
    (
        "EN1005/a reference's lifetime",
        "s.en",
        "public function f(x: &'a T): void {}\n",
        &[(Code::EN1005, "'a", "named lifetimes are not supported yet")],
    ),
    (
        "EN1005/a lifetime parameter",
        "s.en",
        "public function f<'a>(x: &T): void {}\n",
        &[(Code::EN1005, "'a", "named lifetimes are not supported yet")],
    ),
    (
        "EN1005/a string in single quotes after `&`",
        "s.en",
        "const s = &'a b';\n",
        &[(
            Code::EN1005,
            "'a b'",
            "named lifetimes are not supported yet",
        )],
    ),
    // EN1009.
    (
        "EN1009/a default import",
        "s.en",
        "import x from \"./x\";\n",
        &[(
            Code::EN1009,
            "import x from \"./x\";",
            "this module form is not supported yet",
        )],
    ),
    (
        "EN1009/a side-effect import",
        "s.en",
        "import \"./x\";\n",
        &[(
            Code::EN1009,
            "import \"./x\";",
            "this module form is not supported yet",
        )],
    ),
    (
        "EN1009/export default",
        "s.en",
        "export default function f(): void {}\n",
        &[(
            Code::EN1009,
            "export default",
            "this module form is not supported yet",
        )],
    ),
    (
        "EN1009/an export list",
        "s.en",
        "export { a, b };\n",
        &[(
            Code::EN1009,
            "export { a, b };",
            "this module form is not supported yet",
        )],
    ),
    (
        "EN1009/require",
        "s.en",
        "const fs = require(\"fs\");\n",
        &[(
            Code::EN1009,
            "require(\"fs\")",
            "this module form is not supported yet",
        )],
    ),
    // EN1010 (TESTING 18).
    (
        "EN1010/an object pattern",
        "s.en",
        "const { a = 1 } = p;\n",
        &[(
            Code::EN1010,
            "=",
            "defaults in patterns are not supported yet",
        )],
    ),
    (
        "EN1010/a tuple pattern",
        "s.en",
        "const [a = 1, b] = t;\n",
        &[(
            Code::EN1010,
            "=",
            "defaults in patterns are not supported yet",
        )],
    ),
    (
        "EN1010/an assignment pattern",
        "s.en",
        "[a = 1, b] = t;\n",
        &[(
            Code::EN1010,
            "=",
            "defaults in patterns are not supported yet",
        )],
    ),
    // EN1013 (SPEC 3.4).
    (
        "EN1013/a spread argument",
        "s.en",
        "f(...a);\n",
        &[(Code::EN1013, "...", SPREAD)],
    ),
    // EN1017.
    (
        "EN1017/a class setter",
        "s.en",
        "public class A {\n  public set x(v: i64) {}\n}\n",
        &[(Code::EN1017, "set x", "setters are not supported yet")],
    ),
    (
        "EN1017/an interface setter",
        "s.en",
        "public interface I {\n  set x(v: i64): void;\n}\n",
        &[(Code::EN1017, "set x", "setters are not supported yet")],
    ),
    // EN1018.
    (
        "EN1018/an operator method",
        "s.en",
        "public class V {\n  public operator +(o: V): V { return o; }\n}\n",
        &[(
            Code::EN1018,
            "operator +",
            "operator overloading is not supported yet",
        )],
    ),
    // EN1021.
    (
        "EN1021/a static field",
        "s.en",
        "public class A {\n  public static x: i64 = 1;\n}\n",
        &[(
            Code::EN1021,
            "static",
            "static fields are not supported yet",
        )],
    ),
    (
        "EN1021/a static field with no type",
        "s.en",
        "public class A {\n  public static x = 1;\n}\n",
        &[(
            Code::EN1021,
            "static",
            "static fields are not supported yet",
        )],
    ),
    // EN1022.
    (
        "EN1022/**",
        "s.en",
        "const y = a ** b;\n",
        &[(Code::EN1022, "**", "the `**` operator is not supported yet")],
    ),
    // EN1023.
    (
        "EN1023/keyof",
        "s.en",
        "let k: keyof T = x;\n",
        &[(
            Code::EN1023,
            "keyof",
            "type-level computation is not supported yet",
        )],
    ),
    (
        "EN1023/a mapped type",
        "s.en",
        "let m: { [K in T]: i64 } = x;\n",
        &[(
            Code::EN1023,
            "{ [K in T]: i64 }",
            "type-level computation is not supported yet",
        )],
    ),
    (
        "EN1023/a conditional type",
        "s.en",
        "let c: T extends U ? X : Y = x;\n",
        &[(
            Code::EN1023,
            "T extends U ? X : Y",
            "type-level computation is not supported yet",
        )],
    ),
    // EN1024.
    (
        "EN1024/A & B",
        "s.en",
        "let x: A & B = y;\n",
        &[(
            Code::EN1024,
            "&",
            "intersection types are not supported yet",
        )],
    ),
    // EN1025.
    (
        "EN1025/a regular expression",
        "s.en",
        "const r = /ab+c/i;\n",
        &[(
            Code::EN1025,
            "/ab+c/i",
            "regular expressions are not supported yet",
        )],
    ),
    // EN1035.
    (
        "EN1035/a function in a function",
        "s.en",
        "public function f(): void {\n  function g(): void {}\n  g();\n}\n",
        &[(
            Code::EN1035,
            "function",
            "nested functions are not supported yet",
        )],
    ),
    // EN1036.
    (
        "EN1036/a generic arrow",
        "s.en",
        "const id = <T>(x: T) => x;\n",
        &[(Code::EN1036, "<T>", "generic arrows are not supported yet")],
    ),
    // EN1037.
    (
        "EN1037/a class expression",
        "s.en",
        "const C = class {\n  public x: i64;\n};\n",
        &[(
            Code::EN1037,
            "class",
            "class expressions are not supported yet",
        )],
    ),
    (
        "EN1037/new class",
        "s.en",
        "const o = new class {}();\n",
        &[(
            Code::EN1037,
            "class",
            "class expressions are not supported yet",
        )],
    ),
    // EN1038.
    (
        "EN1038/a labelled block",
        "s.en",
        "outer: {\n  f();\n}\n",
        &[(
            Code::EN1038,
            "outer:",
            "labelled blocks are not supported yet",
        )],
    ),
    // EN1039.
    (
        "EN1039/as const",
        "s.en",
        "const xs = [1, 2] as const;\n",
        &[(Code::EN1039, "as const", "`as const` is not supported yet")],
    ),
    // EN1102, EN1105 and EN1112 (SPEC 12.1).
    (
        "EN1102/a statement in describe",
        "s.test.en",
        "describe(\"a\", () => {\n  const x = 1;\n  test(\"b\", () => {});\n});\n",
        &[(
            Code::EN1102,
            "const x = 1;",
            "a `describe` body holds only `describe`, `test`, `compileFails` and `compileOk`",
        )],
    ),
    (
        "EN1105/beforeEach at the top level",
        "s.test.en",
        "beforeEach(() => {\n  setup();\n});\ntest(\"a\", () => {});\n",
        &[(
            Code::EN1105,
            "beforeEach",
            "`beforeEach` does not exist in Enrang",
        )],
    ),
    (
        "EN1105/afterAll in describe",
        "s.test.en",
        "describe(\"a\", () => {\n  afterAll(() => {});\n});\n",
        &[(
            Code::EN1105,
            "afterAll",
            "`afterAll` does not exist in Enrang",
        )],
    ),
    (
        "EN1112/a test in a module",
        "math.en",
        "test(\"adds\", () => {});\n",
        &[(Code::EN1112, "test", "tests go in `math.test.en`")],
    ),
    (
        "EN1112/a describe in a module",
        "s.en",
        "describe(\"a\", () => {});\npublic function f(): void {}\n",
        &[(Code::EN1112, "describe", "tests go in `s.test.en`")],
    ),
    (
        "EN1112/a compile case in a module",
        "s.en",
        "compileOk(\"a\", raw`const x = 1;`);\n",
        &[(Code::EN1112, "compileOk", "tests go in `s.test.en`")],
    ),
    (
        "EN1112/once, at the outermost test item",
        "m.en",
        "describe(\"g\", () => { test(\"a\", () => {}); test(\"b\", () => {}); });\n",
        &[(Code::EN1112, "describe", "tests go in `m.test.en`")],
    ),
    (
        "EN1105/a hook in a misplaced describe is a mistake of its own",
        "m.en",
        "describe(\"g\", () => {\n  beforeEach(() => {});\n});\n",
        &[
            (Code::EN1112, "describe", "tests go in `m.test.en`"),
            (
                Code::EN1105,
                "beforeEach",
                "`beforeEach` does not exist in Enrang",
            ),
        ],
    ),
    (
        "EN1024/after a field's tuple type",
        "s.en",
        "public class A {\n  private t: [A] & B;\n}\n",
        &[(
            Code::EN1024,
            "&",
            "intersection types are not supported yet",
        )],
    ),
    (
        "EN1023/a conditional type after a field's tuple type",
        "s.en",
        "public class A {\n  private t: [A] extends B ? C : D;\n}\n",
        &[(
            Code::EN1023,
            "[A] extends B ? C : D",
            "type-level computation is not supported yet",
        )],
    ),
    (
        "EN1013/a rest element in an object pattern's array",
        "s.en",
        "({ a: [x, ...r] } = o);\n",
        &[(Code::EN1013, "...", SPREAD)],
    ),
    (
        "EN1025/flags only touching the closing `/`",
        "s.en",
        "const r = /ab/ g;\n",
        &[
            (
                Code::EN1025,
                "/ab/",
                "regular expressions are not supported yet",
            ),
            (Code::EN0100, "g", "expected `;`, found `g`"),
        ],
    ),
    (
        "EN0222/a skipped namespace leaves the imports' place open",
        "s.en",
        "namespace X {}\nimport { a } from \"./a\";\n",
        &[(
            Code::EN0222,
            "namespace",
            "`namespace` does not exist in Enrang",
        )],
    ),
];

pub const NEAR_MISSES: &[NearMiss] = &[
    (
        Code::EN0201,
        "== and !=",
        "s.en",
        "const y = a == b && a != c;\n",
    ),
    (
        Code::EN0202,
        "let and const",
        "s.en",
        "let x = 1;\nconst y = 2;\nfor (let i = 0; i < 3; i++) {}\n",
    ),
    (
        Code::EN0205,
        "a generic",
        "s.en",
        "public function f<T>(x: &T): void {}\n",
    ),
    (
        Code::EN0206,
        "null",
        "s.en",
        "let x: string | null = null;\n",
    ),
    (
        Code::EN0207,
        "a Result and `?`",
        "s.en",
        "panic(\"x\");\nconst r = f()?;\n",
    ),
    (
        Code::EN0208,
        ">> and a closing `>>>`",
        "s.en",
        "const y = x >> 2;\nlet b: Box<Box<Box<i64>>> = c;\n",
    ),
    (
        Code::EN0209,
        "match",
        "s.en",
        "const y = match (x) { 1 => 2, default => 3 };\n",
    ),
    (
        Code::EN0210,
        "a generic",
        "s.en",
        "public function f<T>(x: T): void {}\n",
    ),
    (
        Code::EN0211,
        "an enum and match",
        "s.en",
        "const n = match (shape) { Shape.Circle => 1, default => 0 };\n",
    ),
    (Code::EN0213, "const", "s.en", "const r = open();\n"),
    (
        Code::EN0215,
        "an object type or null",
        "s.en",
        "let x: { a: i64 } | null = null;\nlet y: A | B = z;\n",
    ),
    (
        Code::EN0216,
        "a string-literal alias",
        "s.en",
        "private type Direction = \"left\" | \"right\";\n",
    ),
    (
        Code::EN0218,
        "an arrow",
        "s.en",
        "const f = (x: i64): i64 => { return x; };\n",
    ),
    (
        Code::EN0220,
        "bounds joined by `&`",
        "s.en",
        "public interface A {\n  m(): void;\n}\npublic function f<T extends A & B>(x: &T): void {}\n",
    ),
    (Code::EN0222, "a field set to null", "s.en", "o.x = null;\n"),
    (
        Code::EN0224,
        "both arrow forms, and a ternary",
        "s.en",
        "const f = (x: i64) => x * 2;\nconst g = (x): i64 => x * 2;\nconst h = c ? x : y => y;\n",
    ),
    (
        Code::EN0225,
        "f64 and int",
        "s.en",
        "let n: f64 = 1.0;\nlet m: int = 1;\n",
    ),
    (
        Code::EN0228,
        "a value with no `move`, and a method named `move`",
        "s.en",
        "queue.push(t);\nx.move();\nconst c = [...a];\n",
    ),
    (
        Code::EN1001,
        "a blocking function",
        "s.en",
        "public function f(): i64 { return 1; }\n",
    ),
    (
        Code::EN1002,
        "an array",
        "s.en",
        "public function gen(): i64[] { return []; }\n",
    ),
    (
        Code::EN1005,
        "strings in single quotes",
        "s.en",
        "const s = 'a';\nf(x, 'a b');\n",
    ),
    (
        Code::EN1009,
        "a named import",
        "s.en",
        "import { name } from \"./file\";\nimport * as m from \"./m\";\n",
    ),
    (
        Code::EN1010,
        "`??` after destructuring",
        "s.en",
        "const { a } = p;\nconst x = a ?? 1;\n",
    ),
    (
        Code::EN1013,
        "a spread in an array",
        "s.en",
        "const c = [...a];\n",
    ),
    (
        Code::EN1017,
        "a method named `set`",
        "s.en",
        "public class A {\n  public set(v: i64): void {}\n}\n",
    ),
    (
        Code::EN1018,
        "a named method, and a method named `operator`",
        "s.en",
        "public class V {\n  public add(o: V): V { return o; }\n  public operator(x: i64): void {}\n}\n",
    ),
    (
        Code::EN1021,
        "a static method",
        "s.en",
        "public class A {\n  public static make(): A { return new A(); }\n}\n",
    ),
    (
        Code::EN1022,
        "pow, and `**` as two dereferences",
        "s.en",
        "const y = a.pow(b);\nconst z = **p;\n",
    ),
    (
        Code::EN1023,
        "an object type",
        "s.en",
        "let o: { a: i64 } = x;\n",
    ),
    (
        Code::EN1024,
        "a bound",
        "s.en",
        "const y = a & b;\npublic function f<T extends A & B>(x: &T): void {}\n",
    ),
    (Code::EN1025, "a division", "s.en", "const r = a / b / c;\n"),
    (
        Code::EN1035,
        "an arrow in a local",
        "s.en",
        "public function f(): void {\n  const g = (): void => {};\n}\n",
    ),
    (
        Code::EN1036,
        "a generic function",
        "s.en",
        "public function id<T>(x: T): T { return x; }\n",
    ),
    (
        Code::EN1037,
        "a declared class",
        "s.en",
        "private class C {}\n",
    ),
    (
        Code::EN1038,
        "a labelled loop",
        "s.en",
        "outer: while (x) {}\n",
    ),
    (
        Code::EN1039,
        "a plain cast",
        "s.en",
        "const xs = [1, 2];\nconst n = x as i64;\n",
    ),
    (
        Code::EN1102,
        "tests in describe",
        "s.test.en",
        "describe(\"a\", () => {\n  test(\"b\", () => {});\n  describe(\"c\", () => {});\n});\n",
    ),
    (
        Code::EN1105,
        "a hook outside a test file is a call",
        "s.en",
        "beforeEach(() => {});\n",
    ),
    (
        Code::EN1112,
        "a test in a test file",
        "s.test.en",
        "test(\"a\", () => {});\n",
    ),
];

/// SPEC 16's table: each code's message head and help, `None` for no help.
fn deferred_table() -> Vec<(String, String, Option<String>)> {
    let text = section(doc("SPEC.md"), "## 16. Deferred features");
    let mut rows = Vec::new();
    for line in text.lines().filter(|line| line.starts_with("| EN10")) {
        let unescaped = line.replace("\\|", "\u{0}");
        let cells: Vec<String> = unescaped
            .split('|')
            .map(|cell| cell.trim().replace('\u{0}', "|"))
            .collect();
        let help = (!cells[4].is_empty()).then(|| cells[4].clone());
        rows.push((cells[1].clone(), cells[3].clone(), help));
    }
    rows
}

/// A fix-it applied: the source with the edits of help `help` of the first
/// diagnostic with `code`.
fn fixed(file: &str, text: &str, code: Code, help: usize) -> String {
    let parsed = Parsed::new(file, text);
    let diag = parsed
        .diags
        .iter()
        .find(|diag| diag.code == code)
        .unwrap_or_else(|| panic!("{code} fires: {}", parsed.listing()));
    apply_fixes(text, parsed.file.start, &diag.helps[help].edits)
        .unwrap_or_else(|conflict| panic!("{conflict}"))
}

pub fn register(h: &mut Harness) {
    for &(label, file, text, want) in FIRES {
        h.case(format!("hints/fires/{label}"), move || {
            check_fires(file, text, want)
        });
    }
    for &(code, label, file, text) in NEAR_MISSES {
        h.case(format!("hints/near miss/{code}/{label}"), move || {
            check_near_miss(file, text)
        });
    }
    let codes: Vec<Code> = Code::ALL
        .iter()
        .copied()
        .filter(|code| {
            code.owner() == Owner::Syntax
                && code.phase() == Phase::Syntax
                && code.name().starts_with("EN10")
        })
        .collect();
    for code in codes {
        h.case(
            format!("hints/SPEC 16/{code}'s message head, note and help"),
            move || {
                let table = deferred_table();
                let (_, message, help) = table
                    .iter()
                    .find(|(name, ..)| name == code.name())
                    .unwrap_or_else(|| panic!("SPEC 16 has no row {code}"));
                let (_, file, text, _) = FIRES
                    .iter()
                    .find(|(_, _, _, want)| want.iter().any(|&(c, ..)| c == code))
                    .unwrap_or_else(|| panic!("no row fires {code}"));
                let parsed = Parsed::new(file, text);
                let diag = parsed
                    .diags
                    .iter()
                    .find(|diag| diag.code == code)
                    .expect("it fires");
                assert_eq!(&diag.message, message);
                let notes = diag
                    .entries
                    .iter()
                    .filter(|entry| entry.kind == EntryKind::Note)
                    .count();
                assert!(notes >= 1, "a `= note:` with the reason");
                let helps: Vec<&str> = diag.helps.iter().map(|h| h.message.as_str()).collect();
                match help {
                    Some(help) => assert_eq!(helps, [help.as_str()]),
                    None => assert!(helps.is_empty(), "{helps:?}"),
                }
            },
        );
    }
    register_fixes(h);
}

fn register_fixes(h: &mut Harness) {
    let rows: &[(&str, &str, &str, Code, usize, &str)] = &[
        (
            "EN0201/!== becomes !=",
            "s.en",
            "const y = a !== b;\n",
            Code::EN0201,
            0,
            "const y = a != b;\n",
        ),
        (
            "EN0202/var becomes let in a loop",
            "s.en",
            "for (var i = 0; i < 3; i++) {}\n",
            Code::EN0202,
            0,
            "for (let i = 0; i < 3; i++) {}\n",
        ),
        (
            "EN0205/a generic beside existing ones",
            "s.en",
            "public function f<U>(u: U, x: any): void {}\n",
            Code::EN0205,
            0,
            "public function f<U, T>(u: U, x: &T): void {}\n",
        ),
        (
            "EN0205/a part of a parameter's type",
            "s.en",
            "public function f(xs: any[]): void {}\n",
            Code::EN0205,
            0,
            "public function f<T>(xs: T[]): void {}\n",
        ),
        (
            "EN0205/empty type parameters",
            "s.en",
            "public function f<>(x: any): void {}\n",
            Code::EN0205,
            0,
            "public function f<T>(x: &T): void {}\n",
        ),
        (
            "EN0206/a nullable binding",
            "s.en",
            "let y = undefined;\n",
            Code::EN0206,
            0,
            "let y: i64 | null = null;\n",
        ),
        (
            "EN0206/a type",
            "s.en",
            "let y: string | undefined = null;\n",
            Code::EN0206,
            0,
            "let y: string | null = null;\n",
        ),
        (
            "EN0213/using becomes const",
            "s.en",
            "using r = open();\n",
            Code::EN0213,
            0,
            "const r = open();\n",
        ),
        (
            "EN0218/an arrow",
            "s.en",
            "const f = function (x: i64): i64 { return x; };\n",
            Code::EN0218,
            0,
            "const f = (x: i64): i64 => { return x; };\n",
        ),
        (
            "EN0224/the parameter's type",
            "s.en",
            "const f = x: i64 => x * 2;\n",
            Code::EN0224,
            0,
            "const f = (x: i64) => x * 2;\n",
        ),
        (
            "EN0224/the return type",
            "s.en",
            "const f = x: i64 => x * 2;\n",
            Code::EN0224,
            1,
            "const f = (x): i64 => x * 2;\n",
        ),
        (
            "EN0225/f64",
            "s.en",
            "let n: number = 1;\n",
            Code::EN0225,
            0,
            "let n: f64 = 1;\n",
        ),
        (
            "EN0226/export becomes public",
            "s.en",
            "export function f(): void {}\n",
            Code::EN0226,
            0,
            "public function f(): void {}\n",
        ),
        (
            "EN0228/move removed",
            "s.en",
            "queue.push(move t);\n",
            Code::EN0228,
            0,
            "queue.push(t);\n",
        ),
        (
            "EN1022/a call of pow",
            "s.en",
            "const y = a ** b;\n",
            Code::EN1022,
            0,
            "const y = a.pow(b);\n",
        ),
        (
            "EN1022/a negative base in parentheses",
            "s.en",
            "const y = -a ** 2;\n",
            Code::EN1022,
            0,
            "const y = (-a).pow(2);\n",
        ),
        (
            "EN1022/a base in parentheses keeps them",
            "s.en",
            "const x = (a) ** b;\n",
            Code::EN1022,
            0,
            "const x = (a).pow(b);\n",
        ),
        (
            "EN0205/after a trailing comma",
            "s.en",
            "public class A { public m<U,>(x: any): void {} }\n",
            Code::EN0205,
            0,
            "public class A { public m<U, T>(x: &T): void {} }\n",
        ),
        (
            "EN0205/a parameter with a default takes `&T`",
            "s.en",
            "public function f(x: any = 1): void {}\n",
            Code::EN0205,
            0,
            "public function f<T>(x: &T = 1): void {}\n",
        ),
        (
            "EN0206/a binding that ends at `}`",
            "s.en",
            "public function f(): void { let y = undefined }\n",
            Code::EN0206,
            0,
            "public function f(): void { let y: i64 | null = null }\n",
        ),
        (
            "EN1105/a helper function",
            "s.test.en",
            "beforeEach(() => {\n  setup();\n});\n",
            Code::EN1105,
            0,
            "private function beforeEach(): void {\n  setup();\n}\n",
        ),
    ];
    for &(label, file, text, code, help, want) in rows {
        h.case(format!("hints/fix-it/{label}"), move || {
            assert_eq!(fixed(file, text, code, help), want);
            let again = Parsed::new(file, want);
            assert!(
                again.diags.iter().all(|diag| diag.code != code),
                "{}",
                again.listing()
            );
        });
    }
    h.case("hints/EN0208/`>>>` binds as `>>` does", || {
        let parsed = Parsed::new("s.en", "a >>> b + c;\n");
        assert_eq!(shape(parsed.expr()), "(>> a (+ b c))");
    });
    h.case("hints/EN1005/`&'a b'` is told to use double quotes", || {
        let parsed = Parsed::new("s.en", "const s = &'a b';\n");
        let notes: Vec<&str> = parsed.diags[0]
            .entries
            .iter()
            .map(|entry| entry.text.as_str())
            .collect();
        assert!(
            notes.contains(&"a string is written in double quotes here: `&\"a b\"`"),
            "{notes:?}"
        );
    });
    h.case(
        "hints/EN1022/`**` binds tighter than `*`, to the right",
        || {
            for (source, want) in [
                (
                    "a * b ** c ** d",
                    "(* a (call (. b pow) (call (. c pow) d)))",
                ),
                ("a ** b * c", "(* (call (. a pow) b) c)"),
                ("a as T ** b", "(call (. (as a T) pow) b)"),
            ] {
                let parsed = Parsed::new("s.en", &format!("{source};\n"));
                assert_eq!(shape(parsed.expr()), want, "{source}");
            }
        },
    );
    h.case("hints/EN0225/its note names the replacements", || {
        let parsed = Parsed::new("s.en", "let n: number = 1;\n");
        assert_eq!(
            parsed.diags[0].entries[0].text,
            "use `f64`, or `int` for whole numbers"
        );
    });
}
