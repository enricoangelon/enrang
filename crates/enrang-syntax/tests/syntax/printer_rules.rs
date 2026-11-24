//! SPEC 12.5's rules one by one: for each bullet, inputs written the way an author
//! might, and the canonical text the bullet's own words and examples fix. Every row
//! also passes the four tests of TESTING 17 (`fmt::four_tests`): the tree, a second
//! run, the comments, and the text itself. The comment rules are in
//! `printer_comments.rs`.

use enrang_testkit::Harness;

use crate::fmt::four_tests;

/// One row: the rule it checks, a name, the input, and the formatted text.
type Row = (&'static str, &'static str, &'static str, &'static str);

/// `text` repeated `n` times.
fn rep(text: &str, n: usize) -> String {
    text.repeat(n)
}

const ROWS: &[Row] = &[
    // -------------------------------------------------------------------------
    // What never changes.
    (
        "What never changes",
        "number literals keep their spelling, hex case included",
        "const a=0xB8000;const b=1e308;const c=0xb8000;const d=1_000_000;const e=0b1010;\n",
        "const a = 0xB8000;\nconst b = 1e308;\nconst c = 0xb8000;\nconst d = 1_000_000;\nconst e = 0b1010;\n",
    ),
    (
        "What never changes",
        "every pair of parentheses around an expression stays",
        "const x = ((a + b));\nconst y = (a) * (b);\nconst z = (match (s) { default => 1 }).f;\n",
        "const x = ((a + b));\nconst y = (a) * (b);\nconst z = (match (s) {\n  default => 1,\n}).f;\n",
    ),
    (
        "What never changes",
        "a spread is written ...e",
        "const all = [ ... xs, ...ys ];\n",
        "const all = [...xs, ...ys];\n",
    ),
    (
        "What never changes",
        "a path and the { of its literal stay on one line",
        "const p = new Point{x: 1, y: 2};\nconst s = Shape.Circle{radius: 2.5};\n",
        "const p = new Point { x: 1, y: 2 };\nconst s = Shape.Circle { radius: 2.5 };\n",
    ),
    (
        "What never changes",
        "a broken named literal keeps new Point { on its first line",
        "const p = new Point { horizontal: someLongExpressionName, vertical: anotherLongExpressionName, z: 0 };\n",
        "const p = new Point {\n  horizontal: someLongExpressionName,\n  vertical: anotherLongExpressionName,\n  z: 0,\n};\n",
    ),
    (
        "What never changes",
        "a < that starts type arguments keeps no space before it",
        "const s = Stack<i64>.empty();\nconst n = parse<u8>(text);\nconst b = new Box<i32>(5);\nconst xs = i64[].withCapacity(8);\n",
        "const s = Stack<i64>.empty();\nconst n = parse<u8>(text);\nconst b = new Box<i32>(5);\nconst xs = i64[].withCapacity(8);\n",
    ),
    (
        "What never changes",
        "a type never gets a space before <",
        "let x: Box < Box < i64 >>= v;\n",
        "let x: Box<Box<i64>> = v;\n",
    ),
    (
        "What never changes",
        "the text of a template stays, holes included",
        "const t = `a  ${ b  +  c }  d`;\nconst r = raw`\\d+  ${x}`;\n",
        "const t = `a  ${ b  +  c }  d`;\nconst r = raw`\\d+  ${x}`;\n",
    ),
    (
        "What never changes",
        "a statement match loses its optional ;",
        "private function f(): void {\n  match (s) {\n    State.On => go(),\n    default => stop(),\n  };\n}\n",
        "private function f(): void {\n  match (s) {\n    State.On => go(),\n    default => stop(),\n  }\n}\n",
    ),
    // -------------------------------------------------------------------------
    // Opting out.
    (
        "Opting out",
        "enrang-fmt-ignore keeps the next statement as written",
        "private function f(): void {\n  // enrang-fmt-ignore\n  const m = [1,0,\n             0,1];\n  const   n   =   1;\n}\n",
        "private function f(): void {\n  // enrang-fmt-ignore\n  const m = [1,0,\n             0,1];\n  const n = 1;\n}\n",
    ),
    (
        "Opting out",
        "enrang-fmt-ignore keeps the next declaration as written",
        "// enrang-fmt-ignore\nprivate const   TABLE: u8[4] = [1,2,\n                               3,4];\nprivate const   X = 1;\n",
        "// enrang-fmt-ignore\nprivate const   TABLE: u8[4] = [1,2,\n                               3,4];\nprivate const X = 1;\n",
    ),
    (
        "Opting out",
        "enrang-fmt-ignore keeps the next class member as written",
        "public class A {\n  // enrang-fmt-ignore\n  public  m():void{return;}\n  public  n():void{return;}\n}\n",
        "public class A {\n  // enrang-fmt-ignore\n  public  m():void{return;}\n  public n(): void { return; }\n}\n",
    ),
    (
        "Opting out",
        "a whole table is the unit, never one element of it",
        "public enum E {\n  // enrang-fmt-ignore\n  A  =  1,\n  B,\n}\n",
        "public enum E {\n  // enrang-fmt-ignore\n  A = 1,\n  B,\n}\n",
    ),
    (
        "Opting out",
        "enrang-fmt-ignore-file on line 1 leaves the whole file as written",
        "// enrang-fmt-ignore-file\nconst   a=[1,0,\n  0,1];\nfunction f( ) : void { }\n",
        "// enrang-fmt-ignore-file\nconst   a=[1,0,\n  0,1];\nfunction f( ) : void { }\n",
    ),
    (
        "Opting out",
        "enrang-fmt-ignore-file on a later line is an ordinary comment",
        "const   a = 1;\n// enrang-fmt-ignore-file\nconst   b = 2;\n",
        "const a = 1;\n// enrang-fmt-ignore-file\nconst b = 2;\n",
    ),
    // -------------------------------------------------------------------------
    // Bodies.
    (
        "Bodies",
        "one statement with no block goes on one line, however written",
        "private function f(p: Point | null): void {\n  if (p == null) {\n    return;\n  }\n}\n",
        "private function f(p: Point | null): void {\n  if (p == null) { return; }\n}\n",
    ),
    (
        "Bodies",
        "two statements go one per line",
        "private function f(): void { a(); b(); }\n",
        "private function f(): void {\n  a();\n  b();\n}\n",
    ),
    (
        "Bodies",
        "a statement holding a block splits, and the rule applies again inside",
        "private function f(): void { if (a) { if (b) { c(); } } }\n",
        "private function f(): void {\n  if (a) {\n    if (b) { c(); }\n  }\n}\n",
    ),
    (
        "Bodies",
        "an arrow with a block body counts as a block",
        "private function f(): void { const g = () => { run(); }; }\n",
        "private function f(): void {\n  const g = () => { run(); };\n}\n",
    ),
    (
        "Bodies",
        "a body whose one line does not fit splits",
        "private function f(): void { if (ready) { startTheEngineWithAVeryLongFunctionName(firstArgument, secondArgumentWithALongName1234); } }\n",
        "private function f(): void {\n  if (ready) {\n    startTheEngineWithAVeryLongFunctionName(firstArgument, secondArgumentWithALongName1234);\n  }\n}\n",
    ),
    (
        "Bodies",
        "class bodies always go one member per line",
        "public class A { public x: i64; }\n",
        "public class A {\n  public x: i64;\n}\n",
    ),
    (
        "Bodies",
        "the last enum case gets a trailing comma",
        "public enum Color { Red, Green, Blue }\n",
        "public enum Color {\n  Red,\n  Green,\n  Blue,\n}\n",
    ),
    (
        "Bodies",
        "enum methods follow the cases after ;",
        "public enum Shape { Circle { r: f64 }, Dot; public area(): f64 { return 0.0; } }\n",
        "public enum Shape {\n  Circle { r: f64 },\n  Dot,\n  ;\n  public area(): f64 { return 0.0; }\n}\n",
    ),
    (
        "Bodies",
        "an if with an else always splits, else on the } line",
        "if (a) { b(); } else { c(); }\n",
        "if (a) {\n  b();\n} else {\n  c();\n}\n",
    ),
    (
        "Bodies",
        "every branch of an else-if chain splits",
        "if (a) { b(); }\nelse if (c) { d(); }\nelse { e(); }\n",
        "if (a) {\n  b();\n} else if (c) {\n  d();\n} else {\n  e();\n}\n",
    ),
    (
        "Bodies",
        "an empty body written over several lines is {}",
        "function f(): void {\n\n}\nwhile (x) {\n}\n",
        "function f(): void {}\nwhile (x) {}\n",
    ),
    (
        "Bodies",
        "do, while and for bodies follow the rule",
        "do { a(); } while (x);\nfor (let i = 0; i < n; i++) { a(); b(); }\nfor (const x of xs) { use(x); }\nfor (const i of 0..n) { use(i); }\n",
        "do { a(); } while (x);\nfor (let i = 0; i < n; i++) {\n  a();\n  b();\n}\nfor (const x of xs) { use(x); }\nfor (const i of 0..n) { use(i); }\n",
    ),
    (
        "Bodies",
        "unsafe blocks and labelled loops follow the rule",
        "unsafe { poke(); }\nouter: while (true) { break outer; }\n",
        "unsafe { poke(); }\nouter: while (true) { break outer; }\n",
    ),
    // -------------------------------------------------------------------------
    // match.
    (
        "match",
        "arms go one per line even when the match fits, the last with a comma",
        "const label = match (s) { State.On => \"on\", default => \"off\" };\n",
        "const label = match (s) {\n  State.On => \"on\",\n  default => \"off\",\n};\n",
    ),
    (
        "match",
        "a body holding a match always splits",
        "private function f(): void { match (s) { default => go() } }\n",
        "private function f(): void {\n  match (s) {\n    default => go(),\n  }\n}\n",
    ),
    (
        "match",
        "a return of a match keeps the return's ;",
        "private function f(): i64 { return match (s) { 1, 2 => 10, default => 0 }; }\n",
        "private function f(): i64 {\n  return match (s) {\n    1, 2 => 10,\n    default => 0,\n  };\n}\n",
    ),
    (
        "match",
        "a block arm follows the body rule",
        "while (go) {\n  match (s) {\n    1 => {\n      a();\n    },\n    2 => { a(); b(); },\n    0..5 if x > 0 => {},\n    null => return,\n    Ok => break,\n    Err => continue,\n  }\n}\n",
        "while (go) {\n  match (s) {\n    1 => { a(); },\n    2 => {\n      a();\n      b();\n    },\n    0..5 if x > 0 => {},\n    null => return,\n    Ok => break,\n    Err => continue,\n  }\n}\n",
    ),
    // -------------------------------------------------------------------------
    // Lists.
    (
        "Lists",
        "arguments that do not fit go one per line with a trailing comma",
        "configureTheDevice(firstArgumentName, secondArgumentName, thirdArgumentName, fourthArgumentXXXXXXXX);\n",
        "configureTheDevice(\n  firstArgumentName,\n  secondArgumentName,\n  thirdArgumentName,\n  fourthArgumentXXXXXXXX,\n);\n",
    ),
    (
        "Lists",
        "a last argument that is a block-bodied arrow stays on the call's line",
        "test(\"boots\", () => { boot(); check(); });\n",
        "test(\"boots\", () => {\n  boot();\n  check();\n});\n",
    ),
    (
        "Lists",
        "a last argument that is an object literal stays on the call's line",
        "configure(device, { name: \"serial\", speed: 115200, parity: Parity.None, stopBits: 1, flow: false, extra: 0 });\n",
        "configure(device, {\n  name: \"serial\",\n  speed: 115200,\n  parity: Parity.None,\n  stopBits: 1,\n  flow: false,\n  extra: 0,\n});\n",
    ),
    (
        "Lists",
        "a hug needs everything before the last argument to fit",
        "test(\"a test name that is long enough to push the arrow past the edge of the line, really it is\", () => { a(); b(); });\n",
        "test(\n  \"a test name that is long enough to push the arrow past the edge of the line, really it is\",\n  () => {\n    a();\n    b();\n  },\n);\n",
    ),
    (
        "Lists",
        "items all 10 characters or shorter fill lines",
        "const table = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10];\n",
        "const table = [\n  0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,\n  0x10,\n];\n",
    ),
    (
        "Lists",
        "items of exactly 10 characters fill lines",
        "const t = [0x00000001, 0x00000002, 0x00000003, 0x00000004, 0x00000005, 0x00000006, 0x00000007, 0x00000008, 0x00000009];\n",
        "const t = [\n  0x00000001, 0x00000002, 0x00000003, 0x00000004, 0x00000005, 0x00000006, 0x00000007, 0x00000008,\n  0x00000009,\n];\n",
    ),
    (
        "Lists",
        "items of 11 characters go one per line",
        "const t = [0x000000001, 0x000000002, 0x000000003, 0x000000004, 0x000000005, 0x000000006, 0x000000007, 0x000000008, 0x000000009];\n",
        "const t = [\n  0x000000001,\n  0x000000002,\n  0x000000003,\n  0x000000004,\n  0x000000005,\n  0x000000006,\n  0x000000007,\n  0x000000008,\n  0x000000009,\n];\n",
    ),
    (
        "Lists",
        "short arguments fill lines too",
        "plotTheCurve(argument01, argument02, argument03, argument04, argument05, argument06, argument07, argument08, argument09);\n",
        "plotTheCurve(\n  argument01, argument02, argument03, argument04, argument05, argument06, argument07, argument08,\n  argument09,\n);\n",
    ),
    (
        "Lists",
        "short import names fill lines too, sorted in byte order",
        "import { module01, module02, module03, module04, module05, module06, module07, module08, module09, module010, module011, module012 } from \"os\";\n",
        "import {\n  module01, module010, module011, module012, module02, module03, module04, module05, module06,\n  module07, module08, module09,\n} from \"os\";\n",
    ),
    (
        "Lists",
        "one item longer than 10 characters puts every item on its own line",
        "const table = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10000000000];\n",
        "const table = [\n  0x00,\n  0x01,\n  0x02,\n  0x03,\n  0x04,\n  0x05,\n  0x06,\n  0x07,\n  0x08,\n  0x09,\n  0x0a,\n  0x0b,\n  0x0c,\n  0x0d,\n  0x0e,\n  0x0f,\n  0x10000000000,\n];\n",
    ),
    (
        "Lists",
        "the outermost list breaks first and inner lists stay whole",
        "const nested = outerFunction(firstArgument, innerFunction(innerArgumentOne, innerArgumentTwo), last);\n",
        "const nested = outerFunction(\n  firstArgument,\n  innerFunction(innerArgumentOne, innerArgumentTwo),\n  last,\n);\n",
    ),
    (
        "Lists",
        "a list holding a multi-line template goes one item per line",
        "console.log(`one\ntwo`, x);\n",
        "console.log(\n  `one\ntwo`,\n  x,\n);\n",
    ),
    (
        "Lists",
        "a call whose only argument is a multi-line template keeps it in place",
        "asm(`\n  cli\n  hlt\n`);\n",
        "asm(`\n  cli\n  hlt\n`);\n",
    ),
    (
        "Lists",
        "an import list that does not fit goes one name per line",
        "import { alphaModuleName, betaModuleName, gammaModuleName, deltaModuleName, epsilonName, zetaName } from \"os\";\n",
        "import {\n  alphaModuleName,\n  betaModuleName,\n  deltaModuleName,\n  epsilonName,\n  gammaModuleName,\n  zetaName,\n} from \"os\";\n",
    ),
    // -------------------------------------------------------------------------
    // Rows.
    (
        "Rows",
        "arrays of 2 or more elements go one per line even when they fit",
        "const m = [[1, 0], [0, 1]];\nconst range = [[min, max], [lo, hi]];\n",
        "const m = [\n  [1, 0],\n  [0, 1],\n];\nconst range = [\n  [min, max],\n  [lo, hi],\n];\n",
    ),
    (
        "Rows",
        "class and object literals of 2 or more fields, the classes may differ",
        "const ps = [new Point { x: 1, y: 2 }, Shape.Circle { r: 1, c: 2 }, { a: 1, b: 2 }];\n",
        "const ps = [\n  new Point { x: 1, y: 2 },\n  Shape.Circle { r: 1, c: 2 },\n  { a: 1, b: 2 },\n];\n",
    ),
    (
        "Rows",
        "any other element switches the rule off",
        "const a = [[1], [2]];\nconst b = [[1, 0], 2];\nconst c = [entry(0, 0x9a), entry(1, 0x92)];\nconst d = [[0; 3], [1, 2]];\nconst e = [...xs, [1, 2]];\nconst f = [{ a: 1 }, { b: 2 }];\nconst g = [[1, 2]];\n",
        "const a = [[1], [2]];\nconst b = [[1, 0], 2];\nconst c = [entry(0, 0x9a), entry(1, 0x92)];\nconst d = [[0; 3], [1, 2]];\nconst e = [...xs, [1, 2]];\nconst f = [{ a: 1 }, { b: 2 }];\nconst g = [[1, 2]];\n",
    ),
    (
        "Rows",
        "columns are never aligned, and a row too long breaks like any list",
        "const m = [[1, 100], [firstVeryLongElementNameNumberOne, secondVeryLongElementName, thirdVeryLongElementName1XXXXXXXXXX]];\n",
        "const m = [\n  [1, 100],\n  [\n    firstVeryLongElementNameNumberOne,\n    secondVeryLongElementName,\n    thirdVeryLongElementName1XXXXXXXXXX,\n  ],\n];\n",
    ),
    // -------------------------------------------------------------------------
    // Signatures.
    (
        "Signatures",
        "parameters that do not fit go one per line, closed by ): Ret { ending its line",
        "public function copyBytesBetweenBuffers(source: &Slice<u8>, destination: &u8[], count: usize): usize {\n  return 0;\n}\n",
        "public function copyBytesBetweenBuffers(\n  source: &Slice<u8>,\n  destination: &u8[],\n  count: usize,\n): usize {\n  return 0;\n}\n",
    ),
    (
        "Signatures",
        "parameters are never filled, however short",
        "public function manyParameters(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i64): i64 {\n  return a;\n}\n",
        "public function manyParameters(\n  a: i64,\n  b: i64,\n  c: i64,\n  d: i64,\n  e: i64,\n  f: i64,\n  g: i64,\n  h: i64,\n): i64 {\n  return a;\n}\n",
    ),
    (
        "Signatures",
        "a long return type alone forces it, even for one parameter",
        "public function short(a: i64): SomeVeryLongReturnTypeName<WithArguments, AndMoreArguments, AndEvenMore> {\n  a();\n  b();\n}\n",
        "public function short(\n  a: i64,\n): SomeVeryLongReturnTypeName<WithArguments, AndMoreArguments, AndEvenMore> {\n  a();\n  b();\n}\n",
    ),
    (
        "Signatures",
        "type parameters that do not fit break first, closed by >(",
        "public function generic<TFirstTypeParameter extends Comparable & Hashable, TSecondTypeParameter extends Ord>(a: i64): void {\n  a();\n  b();\n}\n",
        "public function generic<\n  TFirstTypeParameter extends Comparable & Hashable,\n  TSecondTypeParameter extends Ord,\n>(a: i64): void {\n  a();\n  b();\n}\n",
    ),
    (
        "Signatures",
        "a return type still too long breaks its type arguments one per line",
        "public function short(a: i64): SomeVeryLongReturnTypeName<WithArguments, AndMoreArguments, AndEvenMoreOfThemXXXXXXXXXXXXXXXXXXX> {\n  a();\n  b();\n}\n",
        "public function short(\n  a: i64,\n): SomeVeryLongReturnTypeName<\n  WithArguments,\n  AndMoreArguments,\n  AndEvenMoreOfThemXXXXXXXXXXXXXXXXXXX,\n> {\n  a();\n  b();\n}\n",
    ),
    (
        "Signatures",
        "methods, constructors and declared functions break the same way",
        "public class A {\n  public constructor(public readonly firstFieldName: i64, private secondFieldName: string, third: u8) {}\n  public static method(firstParameter: i64, secondParameter: i64, thirdParameter: i64): Result<void> where T extends Ord {\n    return Ok();\n  }\n}\nprivate declare function hostCallWithALongName(firstParameter: i64, secondParameter: i64, thirdParameter: i64): i64;\n",
        "public class A {\n  public constructor(\n    public readonly firstFieldName: i64,\n    private secondFieldName: string,\n    third: u8,\n  ) {}\n  public static method(\n    firstParameter: i64,\n    secondParameter: i64,\n    thirdParameter: i64,\n  ): Result<void> where T extends Ord {\n    return Ok();\n  }\n}\nprivate declare function hostCallWithALongName(\n  firstParameter: i64,\n  secondParameter: i64,\n  thirdParameter: i64,\n): i64;\n",
    ),
    // -------------------------------------------------------------------------
    // Right-hand sides.
    (
        "Right-hand sides",
        "= callee( stays on the first line and the call's list breaks",
        "const veryLongVariableNameNumberOne = computeSomething(argumentNumberOne, argumentNumberTwo, threeee);\n",
        "const veryLongVariableNameNumberOne = computeSomething(\n  argumentNumberOne,\n  argumentNumberTwo,\n  threeee,\n);\n",
    ),
    (
        "Right-hand sides",
        "a class literal and an array keep = new C { and = [ on the first line",
        "const user = new User { name: \"Ada Lovelace\", age: 36, email: \"ada@example.com\", role: Role.Administrator };\nconst xs = [firstElementName, secondElementName, thirdElementName, fourthElementName, fifthElement1];\n",
        "const user = new User {\n  name: \"Ada Lovelace\",\n  age: 36,\n  email: \"ada@example.com\",\n  role: Role.Administrator,\n};\nconst xs = [\n  firstElementName,\n  secondElementName,\n  thirdElementName,\n  fourthElementName,\n  fifthElement1,\n];\n",
    ),
    (
        "Right-hand sides",
        "a right-hand side with no list breaks after = first",
        "const total = basePrice * quantity + shippingCostForTheOrder + handlingFeeForTheOrder + taxesOnTheOrder;\nconst name = user.profile.settings.displayName ?? user.profile.settings.fallbackName ?? defaultName1;\nconst pick = someCondition ? someVeryLongExpressionNumberOne(withArgs) : someOtherLongExpression(two);\nconst field = someObject.someProperty.anotherProperty.yetAnotherProperty.andOneMoreProperty.lastOneX;\n",
        "const total =\n  basePrice * quantity + shippingCostForTheOrder + handlingFeeForTheOrder + taxesOnTheOrder;\nconst name =\n  user.profile.settings.displayName ?? user.profile.settings.fallbackName ?? defaultName1;\nconst pick =\n  someCondition ? someVeryLongExpressionNumberOne(withArgs) : someOtherLongExpression(two);\nconst field =\n  someObject.someProperty.anotherProperty.yetAnotherProperty.andOneMoreProperty.lastOneX;\n",
    ),
    (
        "Right-hand sides",
        "a sum still too long then breaks by the operator rule",
        "const total = basePrice * quantity + shippingCostForTheOrder + handlingFeeForTheOrder + taxesOnTheOrderX + moreAndMore;\n",
        "const total =\n  basePrice * quantity +\n  shippingCostForTheOrder +\n  handlingFeeForTheOrder +\n  taxesOnTheOrderX +\n  moreAndMore;\n",
    ),
    (
        "Right-hand sides",
        "the break goes after = when name = callee( alone does not fit",
        "const someExtremelyLongVariableNameThatGoesOnAndOnAndOnForeverAndEver = someEvenLongerFunctionNameXX(a);\n",
        "const someExtremelyLongVariableNameThatGoesOnAndOnAndOnForeverAndEver =\n  someEvenLongerFunctionNameXX(a);\n",
    ),
    (
        "Right-hand sides",
        "assignments, fields, defaults and constants follow the rule",
        "total = basePrice * quantity + shippingCostForTheOrder + handlingFeeForTheOrder + taxesOnTheOrder123;\nprivate const LIMIT: i64 = someFunctionWithAVeryLongName(firstArgumentHere, secondArgumentHere12345);\n",
        "total =\n  basePrice * quantity + shippingCostForTheOrder + handlingFeeForTheOrder + taxesOnTheOrder123;\nprivate const LIMIT: i64 = someFunctionWithAVeryLongName(\n  firstArgumentHere,\n  secondArgumentHere12345,\n);\n",
    ),
    (
        "Right-hand sides",
        "a return of a call breaks the call's list",
        "private function f(): i64 {\n  return someFunctionWithALongName(firstArgumentHere, secondArgumentHere, thirdArgumentHere123456789);\n}\n",
        "private function f(): i64 {\n  return someFunctionWithALongName(\n    firstArgumentHere,\n    secondArgumentHere,\n    thirdArgumentHere123456789,\n  );\n}\n",
    ),
    (
        "Right-hand sides",
        "a string literal is never broken, so its line may pass 100",
        "const message = \"a string literal that is very long and that is never broken, however long it grows, ever\";\n",
        "const message =\n  \"a string literal that is very long and that is never broken, however long it grows, ever\";\n",
    ),
    // -------------------------------------------------------------------------
    // Operators.
    (
        "Operators",
        "a long && ends each line with its operator",
        "const ok = config.enabled && config.features.someVeryLongFeatureFlagName && userIsAllowedToSeeItNow(user, today, tomorrow);\n",
        "const ok =\n  config.enabled &&\n  config.features.someVeryLongFeatureFlagName &&\n  userIsAllowedToSeeItNow(user, today, tomorrow);\n",
    ),
    (
        "Operators",
        "it breaks at the weakest operator and keeps tighter groups whole",
        "const mixed = alphaValue && betaValue || gammaValue && deltaValue || epsilonValue && zetaValueXXXXXXXXXXXXXXXXXXXXXXX;\n",
        "const mixed =\n  alphaValue && betaValue ||\n  gammaValue && deltaValue ||\n  epsilonValue && zetaValueXXXXXXXXXXXXXXXXXXXXXXX;\n",
    ),
    (
        "Operators",
        "?? chains break one operand per line",
        "const name = user.profile.settings.displayName ?? user.profile.settings.fallbackName ?? defaultNameXXXXXXXXXXXXXXX;\n",
        "const name =\n  user.profile.settings.displayName ??\n  user.profile.settings.fallbackName ??\n  defaultNameXXXXXXXXXXXXXXX;\n",
    ),
    (
        "Operators",
        "continuation lines are indented 2 more, and no parentheses are added",
        "drawTheShape(basePrice * quantity + shippingCostForTheOrder + handlingFeeForTheOrder + taxes, color);\n",
        "drawTheShape(\n  basePrice * quantity + shippingCostForTheOrder + handlingFeeForTheOrder + taxes,\n  color,\n);\n",
    ),
    (
        "Operators",
        "an operand list too long for its own line breaks with 2 more",
        "private function f(): i64 {\n  return firstOperandName + secondOperandName + thirdOperandName + fourthOperandName + fifthOperandX;\n}\n",
        "private function f(): i64 {\n  return firstOperandName +\n    secondOperandName +\n    thirdOperandName +\n    fourthOperandName +\n    fifthOperandX;\n}\n",
    ),
    (
        "Operators",
        "a broken if condition is if (, the operands, then ) {",
        "if (config.enabled && config.features.someVeryLongFeatureFlagName && userIsAllowedToSeeIt(user, now)) {\n  go();\n}\n",
        "if (\n  config.enabled &&\n  config.features.someVeryLongFeatureFlagName &&\n  userIsAllowedToSeeIt(user, now)\n) {\n  go();\n}\n",
    ),
    (
        "Operators",
        "a broken while condition follows the if rule",
        "while (config.enabled && config.features.someVeryLongFeatureFlagName && userIsAllowedToSeeIt(user)) {\n  go();\n  stop();\n}\n",
        "while (\n  config.enabled &&\n  config.features.someVeryLongFeatureFlagName &&\n  userIsAllowedToSeeIt(user)\n) {\n  go();\n  stop();\n}\n",
    ),
    (
        "Operators",
        "a broken ternary puts ? and : at the start of their lines",
        "const pick = someCondition ? someVeryLongExpressionNumberOne(withArgs) : someOtherLongExpression(two, three, four);\n",
        "const pick =\n  someCondition\n    ? someVeryLongExpressionNumberOne(withArgs)\n    : someOtherLongExpression(two, three, four);\n",
    ),
    // -------------------------------------------------------------------------
    // Method chains.
    (
        "Method chains",
        "a chain of 2 calls that does not fit puts each call on its own line",
        "const longer = this.items.filterTheseItemsByTheirName(theName).mapTheseItemsToTheirIdentifiers(project);\n",
        "const longer = this.items\n  .filterTheseItemsByTheirName(theName)\n  .mapTheseItemsToTheirIdentifiers(project);\n",
    ),
    (
        "Method chains",
        "the names before the first call stay on the first line",
        "os.fs.openTheFileWithAVeryLongName(pathToTheFile).readAllTheBytesFromIt(someBufferArgumentXXXXXXXXX);\n",
        "os.fs\n  .openTheFileWithAVeryLongName(pathToTheFile)\n  .readAllTheBytesFromIt(someBufferArgumentXXXXXXXXX);\n",
    ),
    (
        "Method chains",
        "a property access between calls starts the line of the call after it",
        "const n = this.queue.takeTheNextItemFromTheQueue(now).payload.describeThePayloadInFullDetail(verbose);\n",
        "const n = this.queue\n  .takeTheNextItemFromTheQueue(now)\n  .payload.describeThePayloadInFullDetail(verbose);\n",
    ),
    (
        "Method chains",
        "postfix ? and ! stay attached",
        "const b = this.items.filter(isActive)!.map(toNameOfTheItem)?.joinTheseItemsWithACommaAndASpace(\", \")?;\n",
        "const b = this.items\n  .filter(isActive)!\n  .map(toNameOfTheItem)\n  ?.joinTheseItemsWithACommaAndASpace(\", \")?;\n",
    ),
    (
        "Method chains",
        "a ! or an index among the names before the first call stays on the first line",
        "const c = this.items!.filter(isActiveItemWithLongName).map(transformTheItemIntoSomething).join(separatorValue);\nconst d = this.groups[0].filter(isActiveItemWithLongName).map(transformTheItemIntoSomething).join(sep);\nconfig.server!.handlers.filter(isActiveItemWithLongName).map(transformTheItemIntoSomething).join(sep);\n",
        "const c = this.items!\n  .filter(isActiveItemWithLongName)\n  .map(transformTheItemIntoSomething)\n  .join(separatorValue);\nconst d = this.groups[0]\n  .filter(isActiveItemWithLongName)\n  .map(transformTheItemIntoSomething)\n  .join(sep);\nconfig.server!.handlers\n  .filter(isActiveItemWithLongName)\n  .map(transformTheItemIntoSomething)\n  .join(sep);\n",
    ),
    (
        "Method chains",
        "a single call breaks its argument list",
        "x.y.doSomethingImportant(firstArgumentHere, secondArgumentHere, thirdArgumentHere123456789012345678);\n",
        "x.y.doSomethingImportant(\n  firstArgumentHere,\n  secondArgumentHere,\n  thirdArgumentHere123456789012345678,\n);\n",
    ),
    (
        "Method chains",
        "more than 2 calls with an argument that is not simple break when they fit",
        "items.filter(isActive).sortBy(byName).forEach(item => {\n  show(item);\n  count(item);\n});\nitems.filter(x => x > 0).map(f).join(\",\");\n",
        "items\n  .filter(isActive)\n  .sortBy(byName)\n  .forEach(item => {\n    show(item);\n    count(item);\n  });\nitems\n  .filter(x => x > 0)\n  .map(f)\n  .join(\",\");\n",
    ),
    (
        "Method chains",
        "a chain of 2 calls keeps such an arrow on its first line",
        "items.filter(isActive).forEach(item => {\n  show(item);\n  count(item);\n});\n",
        "items.filter(isActive).forEach(item => {\n  show(item);\n  count(item);\n});\n",
    ),
    (
        "Method chains",
        "simple arguments keep a chain that fits on one line",
        "const s = items.map(getId).filter(isPositive).slice(0, 10).join(\",\");\nconst t = a.f(this, -x, [1, 2], { k: v }, p.q, g(1), `t`).g().h();\n",
        "const s = items.map(getId).filter(isPositive).slice(0, 10).join(\",\");\nconst t = a.f(this, -x, [1, 2], { k: v }, p.q, g(1), `t`).g().h();\n",
    ),
    // -------------------------------------------------------------------------
    // Arrow parameters.
    (
        "Arrow parameters",
        "a single untyped parameter has no parentheses",
        "const doubled = xs.map((x) => x * 2);\n",
        "const doubled = xs.map(x => x * 2);\n",
    ),
    (
        "Arrow parameters",
        "parentheses stay for a type, let, none, two or more, and a return type",
        "const a = xs.map((x: i64) => x * 2);\nconst b = xs.map((let x) => x);\nconst c = () => 1;\nconst d = (x, y) => x + y;\nconst e = (x): i64 => x * 2;\n",
        "const a = xs.map((x: i64) => x * 2);\nconst b = xs.map((let x) => x);\nconst c = () => 1;\nconst d = (x, y) => x + y;\nconst e = (x): i64 => x * 2;\n",
    ),
    // -------------------------------------------------------------------------
    // Spaces.
    (
        "Spaces",
        "a one-line brace list has one space inside each brace",
        "import {serial, vga} from \"os\";\nconst u = new User {name: \"Ada\", age: 36};\nconst {a, b} = p;\nfunction f(x: i64): i64 {return x;}\n",
        "import { serial, vga } from \"os\";\nconst u = new User { name: \"Ada\", age: 36 };\nconst { a, b } = p;\nfunction f(x: i64): i64 { return x; }\n",
    ),
    (
        "Spaces",
        "an empty pair is {}",
        "const o = {  };\nconst p = new Empty {  };\nfunction f(): void {   }\npublic class A {\n}\n",
        "const o = {};\nconst p = new Empty {};\nfunction f(): void {}\npublic class A {}\n",
    ),
    (
        "Spaces",
        "brackets and parentheses are never padded",
        "const xs = [ 1, 2 ];\nf( a, b );\nconst t: [ i64, string ] = [ 1, \"a\" ];\nconst [ m, n ] = pair;\n",
        "const xs = [1, 2];\nf(a, b);\nconst t: [i64, string] = [1, \"a\"];\nconst [m, n] = pair;\n",
    ),
    (
        "Spaces",
        "operators and types get their spaces",
        "const x=a+b*c;let y:i64|null=null;const z=x as u8;const w=-x+!y+~z;i+=1;const v=a ?b:c;\n",
        "const x = a + b * c;\nlet y: i64 | null = null;\nconst z = x as u8;\nconst w = -x + !y + ~z;\ni += 1;\nconst v = a ? b : c;\n",
    ),
    (
        "Spaces",
        "a minus before a minus keeps a space, so the tree stays",
        "const a = - -x;\nconst b = -(-x);\nconst c = - --x;\n",
        "const a = - -x;\nconst b = -(-x);\nconst c = - --x;\n",
    ),
    // -------------------------------------------------------------------------
    // Quotes.
    (
        "Quotes",
        "double quotes unless the text holds more \" than '",
        "const a = 'it\\'s';\nconst b = 'say \"hi\"';\nconst c = \"say \\\"hi\\\"\";\nconst d = 'plain';\n",
        "const a = \"it's\";\nconst b = 'say \"hi\"';\nconst c = 'say \"hi\"';\nconst d = \"plain\";\n",
    ),
    (
        "Quotes",
        "only the quote escapes change; every other escape stays as written",
        "const a = '\\n\\t\\x41\\u{1F600}\\\\';\nconst b = 'a\\\\\\'b';\n",
        "const a = \"\\n\\t\\x41\\u{1F600}\\\\\";\nconst b = \"a\\\\'b\";\n",
    ),
    (
        "Quotes",
        "template and raw literals are untouched",
        "const a = `it's \"x\"`;\nconst b = raw`'q'`;\n",
        "const a = `it's \"x\"`;\nconst b = raw`'q'`;\n",
    ),
    (
        "Quotes",
        "right after & or < a literal keeps double quotes when single would lex as a lifetime",
        "const a = &\"say \\\"hi\\\"\";\nconst b = x < \"say \\\"hi\\\"\";\nconst c = x & \"say \\\"hi\\\"\";\nconst d = x + \"say \\\"hi\\\"\";\nconst e = &\"\\\"\\\"\";\nconst f = &Stack<i64>.make(\"say \\\"hi\\\"\");\n",
        "const a = &\"say \\\"hi\\\"\";\nconst b = x < \"say \\\"hi\\\"\";\nconst c = x & \"say \\\"hi\\\"\";\nconst d = x + 'say \"hi\"';\nconst e = &'\"\"';\nconst f = &Stack<i64>.make('say \"hi\"');\n",
    ),
    (
        "Quotes",
        "import paths, test names and string unions follow the rule",
        "import { a } from 'core';\nprivate type Mode = 'on' | 'off';\nassert(x, 'it\\'s fine');\n",
        "import { a } from \"core\";\nprivate type Mode = \"on\" | \"off\";\nassert(x, \"it's fine\");\n",
    ),
    // -------------------------------------------------------------------------
    // Imports.
    (
        "Imports",
        "lines sort by path in byte order: \"./x\" before \"core\", uppercase first",
        "import { c } from \"core\";\nimport { x } from \"./x\";\nimport { z } from \"Zeta\";\nimport { o } from \"os\";\n",
        "import { x } from \"./x\";\nimport { z } from \"Zeta\";\nimport { c } from \"core\";\nimport { o } from \"os\";\n",
    ),
    (
        "Imports",
        "names sort in byte order, an alias by the imported name",
        "import { vga, Serial, b as a, a as z } from \"os\";\n",
        "import { Serial, a as z, b as a, vga } from \"os\";\n",
    ),
    (
        "Imports",
        "public import lines sort among the others, and equal paths keep their order",
        "import { b } from \"os\";\npublic import { A } from \"./a\";\nimport { a } from \"os\";\nimport * as ns from \"./b\";\n",
        "public import { A } from \"./a\";\nimport * as ns from \"./b\";\nimport { b } from \"os\";\nimport { a } from \"os\";\n",
    ),
    (
        "Imports",
        "a blank line ends a group, and each group sorts on its own",
        "import { c } from \"core\";\nimport { a } from \"alloc\";\n\nimport { z } from \"./z\";\nimport { y } from \"./y\";\n",
        "import { a } from \"alloc\";\nimport { c } from \"core\";\n\nimport { y } from \"./y\";\nimport { z } from \"./z\";\n",
    ),
    (
        "Imports",
        "a group holding a comment stays as written",
        "import { c } from \"core\";\n// why alloc\nimport { b, a } from \"alloc\";\n\nimport { z } from \"./z\";  // last\nimport { y } from \"./y\";\n",
        "import { c } from \"core\";\n// why alloc\nimport { b, a } from \"alloc\";\n\nimport { z } from \"./z\";  // last\nimport { y } from \"./y\";\n",
    ),
    (
        "Imports",
        "a brace list holding a comment stays as written",
        "import { vga, /* the screen */ serial } from \"os\";\n",
        "import { vga, /* the screen */ serial } from \"os\";\n",
    ),
    (
        "Imports",
        "a comment before the group does not stop the sort",
        "// the imports\nimport { o } from \"os\";\nimport { c } from \"core\";\n",
        "// the imports\nimport { c } from \"core\";\nimport { o } from \"os\";\n",
    ),
    // -------------------------------------------------------------------------
    // Decorators.
    (
        "Decorators",
        "decorators keep their placement, a same-line one followed by one space",
        "@entry   public function main(): void { run(); }\n@packed\n@align(16)\npublic class Gdt {\n  @deprecated   public base: u32;\n  @inline\n  public m(): void {}\n}\n",
        "@entry public function main(): void { run(); }\n@packed\n@align(16)\npublic class Gdt {\n  @deprecated public base: u32;\n  @inline\n  public m(): void {}\n}\n",
    ),
    (
        "Decorators",
        "a decorator inside a type stays inline",
        "public function set(handler: @interrupt   fn(frame: &Frame) => void): void {}\n",
        "public function set(handler: @interrupt fn(frame: &Frame) => void): void {}\n",
    ),
    (
        "Decorators",
        "a same-line decorator that passes 100 columns lets the other rules apply",
        "@intrinsic(\"MemCopy\") public declare function memoryCopyWithAName<T>(destination: *T, source: *T, n: usize): void;\n",
        "@intrinsic(\"MemCopy\") public declare function memoryCopyWithAName<T>(\n  destination: *T,\n  source: *T,\n  n: usize,\n): void;\n",
    ),
    // -------------------------------------------------------------------------
    // Blank lines.
    (
        "Blank lines",
        "at most one blank line in a row",
        "const a = 1;\n\n\n\nconst b = 2;\n",
        "const a = 1;\n\nconst b = 2;\n",
    ),
    (
        "Blank lines",
        "none at the start or end of a block",
        "private function f(): void {\n\n  a();\n  b();\n\n}\npublic class A {\n\n  public x: i64;\n\n}\n",
        "private function f(): void {\n  a();\n  b();\n}\npublic class A {\n  public x: i64;\n}\n",
    ),
    (
        "Blank lines",
        "elsewhere 0 or 1 is kept as written and none is inserted",
        "public class A {\n  public x: i64;\n  public y: i64;\n\n  public m(): void {}\n  public n(): void {}\n}\n",
        "public class A {\n  public x: i64;\n  public y: i64;\n\n  public m(): void {}\n  public n(): void {}\n}\n",
    ),
    (
        "Blank lines",
        "a file's leading and trailing blank lines go, and it ends with one line break",
        "\n\n\nconst a = 1;\n\n\n",
        "const a = 1;\n",
    ),
    // -------------------------------------------------------------------------
    // The rest of SPEC 3: forms with no rule of their own print in one spelling.
    (
        "Forms",
        "items and statements of SPEC 3",
        "public abstract class A<T extends Ord & Eq> extends Base<T> implements I, J {\n  protected abstract override let m(x?: i64, let y: &T = null): readonly &T;\n  public destructor() { free(); }\n}\npublic interface I { static make(): I; move take(): void; field?: i64; }\nprivate type Pair<T> = [T, T] | null;\nextend<T> T[] { @intrinsic public push(x: T): void; }\nprivate unsafe let screen: u16[2000] = [0; 2000];\nassert(sizeOf<u8>() == 1, \"one byte\");\n",
        "public abstract class A<T extends Ord & Eq> extends Base<T> implements I, J {\n  protected abstract override let m(x?: i64, let y: &T = null): readonly &T;\n  public destructor() { free(); }\n}\npublic interface I {\n  static make(): I;\n  move take(): void;\n  field?: i64;\n}\nprivate type Pair<T> = [T, T] | null;\nextend<T> T[] {\n  @intrinsic public push(x: T): void;\n}\nprivate unsafe let screen: u16[2000] = [0; 2000];\nassert(sizeOf<u8>() == 1, \"one byte\");\n",
    ),
    (
        "Forms",
        "TypeScript's for...in, which only sema rejects (EN1015), keeps its `in`",
        "for (const k in o) { use(k); }\nfor (let [a, b]   in   pairs) {}\n",
        "for (const k in o) { use(k); }\nfor (let [a, b] in pairs) {}\n",
    ),
    (
        "Forms",
        "types of SPEC 3.2",
        "let a: &T[] | null;\nlet b: *u8;\nlet c: (x: i64, let y: &u8) => void;\nlet d: unsafe fn(x: i64) => readonly &u8;\nlet e: { name: string, age?: i64 };\nlet f: T[3][4];\nlet g: (A) | null;\nlet h: void;\n",
        "let a: &T[] | null;\nlet b: *u8;\nlet c: (x: i64, let y: &u8) => void;\nlet d: unsafe fn(x: i64) => readonly &u8;\nlet e: { name: string, age?: i64 };\nlet f: T[3][4];\nlet g: (A) | null;\nlet h: void;\n",
    ),
    (
        "Forms",
        "expressions of SPEC 3.4",
        "const a = x?.y ?? z!;\nconst b = f()?;\nconst c = &xs[0];\nconst d = *p as i64;\nconst e = sizeOf<Header>() + alignOf<u64>() + offsetOf<Header>(\"len\");\nconst f = void g();\nconst h = [0; 4];\nconst i = super.m(this);\nconst j = asm(\"hlt\");\n",
        "const a = x?.y ?? z!;\nconst b = f()?;\nconst c = &xs[0];\nconst d = *p as i64;\nconst e = sizeOf<Header>() + alignOf<u64>() + offsetOf<Header>(\"len\");\nconst f = void g();\nconst h = [0; 4];\nconst i = super.m(this);\nconst j = asm(\"hlt\");\n",
    ),
    (
        "Forms",
        "test items of SPEC 3.6",
        "describe(\"math\", () => { test(\"adds\", () => { expect(add(1, 2)).toBe(3); }); });\ntest.panics(\"overflows\", \"overflow\", () => { add(i64.MAX, 1); });\ntest.each(\"cases\", () => cases(), (c) => { expect(c.got).not.toBe(c.bad); });\ncompileFails(\"bad\", raw`const x = ;`, { code: \"EN0100\" });\ntest.todo(\"later\");\nprivate function t(): void { expect(s).toMatchPattern(Shape.Circle); }\n",
        "describe(\"math\", () => {\n  test(\"adds\", () => { expect(add(1, 2)).toBe(3); });\n});\ntest.panics(\"overflows\", \"overflow\", () => { add(i64.MAX, 1); });\ntest.each(\"cases\", () => cases(), c => { expect(c.got).not.toBe(c.bad); });\ncompileFails(\"bad\", raw`const x = ;`, { code: \"EN0100\" });\ntest.todo(\"later\");\nprivate function t(): void { expect(s).toMatchPattern(Shape.Circle); }\n",
    ),
    // -------------------------------------------------------------------------
    // The review of the printer stage: rows for the layouts it fixed and for the
    // choices no row pinned.
    (
        "Method chains",
        "two calls with type arguments break every group they hold",
        "const r = aaaa.bbbbbbbbbb(x).cccccccccc<T>(argumentNumberOneIsLongAndLongerStillMore, argumentNumberTwoIsLongTooAndMoreMoreMore, threeFourFive);\n",
        "const r = aaaa\n  .bbbbbbbbbb(x)\n  .cccccccccc<T>(\n    argumentNumberOneIsLongAndLongerStillMore,\n    argumentNumberTwoIsLongTooAndMoreMoreMore,\n    threeFourFive,\n  );\n",
    ),
    (
        "Method chains",
        "a link of two argument lists measures the second",
        "const r = aaaa.bbbbbbbbbb(x).cccccccccc(firstArgumentListElementOne)(argumentNumberOneIsLongAndLongerStillMore, argumentNumberTwoIsLongTooAndMoreMoreMore, threeFourFive);\n",
        "const r = aaaa\n  .bbbbbbbbbb(x)\n  .cccccccccc(firstArgumentListElementOne)(\n    argumentNumberOneIsLongAndLongerStillMore,\n    argumentNumberTwoIsLongTooAndMoreMoreMore,\n    threeFourFive,\n  );\n",
    ),
    (
        "Method chains",
        "a multi-line template is no simple argument",
        "const r = xs.a(`l1\nl2`).b(c).d(e);\n",
        "const r = xs\n  .a(`l1\nl2`)\n  .b(c)\n  .d(e);\n",
    ),
    (
        "Bodies",
        "a match holds a block, so its body splits",
        "public function f(x: i64): void {\n  if (x == 1) { const r = match (x) {}; }\n}\n",
        "public function f(x: i64): void {\n  if (x == 1) {\n    const r = match (x) {};\n  }\n}\n",
    ),
    (
        "Bodies",
        "the if of an else if splits too",
        "public function f(a: bool, b: bool): void {\n  if (a) { x(); } else if (b) { y(); }\n}\n",
        "public function f(a: bool, b: bool): void {\n  if (a) {\n    x();\n  } else if (b) {\n    y();\n  }\n}\n",
    ),
    (
        "Signatures",
        "type parameters that do not fit go one per line",
        "public function someFunctionNameThatIsQuiteLongIndeedAndLongerStillMoreMore<Aaaa, Bbbb, Cccc, Dddd, Eeee, Ffff, Gggg>(a: i64): i64 {\n  return a;\n}\n",
        "public function someFunctionNameThatIsQuiteLongIndeedAndLongerStillMoreMore<\n  Aaaa,\n  Bbbb,\n  Cccc,\n  Dddd,\n  Eeee,\n  Ffff,\n  Gggg,\n>(a: i64): i64 { return a; }\n",
    ),
    (
        "Width",
        "arm values that do not fit fill the lines",
        "const r = match (x) {\n  1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029 => 0,\n  default => 1,\n};\n",
        "const r = match (x) {\n  1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015,\n    1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029 => 0,\n  default => 1,\n};\n",
    ),
    (
        "Width",
        "a long union breaks at each `|`",
        "public type T = Aaaaaaaaaaaaaaaaaaaa | Bbbbbbbbbbbbbbbbbbbbbbbbb | Cccccccccccccccccccccccc | Dddddddddddddddddddddd | null;\n",
        "public type T = Aaaaaaaaaaaaaaaaaaaa |\n  Bbbbbbbbbbbbbbbbbbbbbbbbb |\n  Cccccccccccccccccccccccc |\n  Dddddddddddddddddddddd |\n  null;\n",
    ),
    (
        "Width",
        "a long string union breaks at each `|`",
        "public type Mode = \"readOnlyAccessMode\" | \"writeOnlyAccessMode\" | \"readWriteAccessMode\" | \"appendMode\";\n",
        "public type Mode = \"readOnlyAccessMode\" |\n  \"writeOnlyAccessMode\" |\n  \"readWriteAccessMode\" |\n  \"appendMode\";\n",
    ),
    (
        "Width",
        "a long implements list goes one per line",
        "public class Foo extends BaseClassWithLongName implements InterfaceNumberOne, InterfaceNumberTwo, InterfaceThree {\n  public x: i64;\n}\n",
        "public class Foo extends BaseClassWithLongName implements\n  InterfaceNumberOne,\n  InterfaceNumberTwo,\n  InterfaceThree {\n  public x: i64;\n}\n",
    ),
    (
        "Width",
        "a long for header breaks as a condition does",
        "for (let index = 0; index < someCollectionWithAVeryLongName.length && keepGoingFlagWithLongName; index += 1) { work(index); }\n",
        "for (\n  let index = 0;\n  index < someCollectionWithAVeryLongName.length && keepGoingFlagWithLongName;\n  index += 1\n) {\n  work(index);\n}\n",
    ),
    (
        "Width",
        "a for header that fits stays",
        "for (;;) { work(); }\nfor (let i = 0;; i += 1) {}\n",
        "for (;;) { work(); }\nfor (let i = 0;; i += 1) {}\n",
    ),
    (
        "Blank lines",
        "one blank line between an object's fields is kept",
        "const o = {\n  alphaFieldWithLongName: 1,\n\n\n  betaFieldWithLongName: 2,\n  gammaFieldWithLongName: 3,\n};\n",
        "const o = {\n  alphaFieldWithLongName: 1,\n\n  betaFieldWithLongName: 2,\n  gammaFieldWithLongName: 3,\n};\n",
    ),
    (
        "Blank lines",
        "one blank line between arguments is kept",
        "f(a,\n\n  b);\nconst xs = [1,\n\n  2];\n",
        "f(\n  a,\n\n  b,\n);\nconst xs = [\n  1,\n\n  2,\n];\n",
    ),
    (
        "Imports",
        "a trailing comment on the last import's line holds the group",
        "import { b } from \"b\";\nimport { a } from \"a\"; // keep\n\nconsole.log(1);\n",
        "import { b } from \"b\";\nimport { a } from \"a\";  // keep\n\nconsole.log(1);\n",
    ),
    (
        "Opting out",
        "an ignored import keeps its group as written",
        "// enrang-fmt-ignore\nimport {   b,a } from \"z\";\nimport { d, c } from \"a\";\n\nconsole.log(1);\n",
        "// enrang-fmt-ignore\nimport {   b,a } from \"z\";\nimport { d, c } from \"a\";\n\nconsole.log(1);\n",
    ),
    (
        "Width",
        "long arm values go one per line",
        "const r = match (shape) {\n  Shape.CircleWithAVeryLongName, Shape.SquareWithAVeryLongName, Shape.TriangleWithAVeryLongName => 0,\n  default => 1,\n};\n",
        "const r = match (shape) {\n  Shape.CircleWithAVeryLongName,\n    Shape.SquareWithAVeryLongName,\n    Shape.TriangleWithAVeryLongName => 0,\n  default => 1,\n};\n",
    ),
    (
        "Width",
        "a long where clause goes one per line",
        "public interface Sorter<T> {\n  sort<U, V>(xs: &T): void where UnusuallyLongParameterName extends ComparableThingWithLongName, V extends AnotherBoundNameThatIsLong;\n}\n",
        "public interface Sorter<T> {\n  sort<U, V>(\n    xs: &T,\n  ): void where\n    UnusuallyLongParameterName extends ComparableThingWithLongName,\n    V extends AnotherBoundNameThatIsLong;\n}\n",
    ),
];

pub fn register(h: &mut Harness) {
    for &(rule, name, input, expected) in ROWS {
        h.case(format!("printer/rule {rule}: {name}"), move || {
            four_tests(input, Some(expected))
        });
    }

    // SPEC 12.5 Width: 100 columns, counted in characters, so a line of 100 stays
    // and a line of 101 breaks; trailing comments do not count.
    h.case(
        "printer/rule Width: a line of exactly 100 characters stays",
        || {
            let name = rep("x", 100 - "const a = f(b, );".len());
            let line = format!("const a = f(b, {name});\n");
            assert_eq!(line.chars().count(), 100 + 1);
            four_tests(&line, Some(&line))
        },
    );
    h.case(
        "printer/rule Width: a line of 101 characters breaks",
        || {
            let name = rep("x", 100 - "const a = f(b, );".len() + 1);
            let input = format!("const a = f(b, {name});\n");
            let output = format!("const a = f(\n  b,\n  {name},\n);\n");
            four_tests(&input, Some(&output))
        },
    );
    h.case(
        "printer/rule Width: counted in characters, not bytes",
        || {
            let name = rep("é", 100 - "const a = f(b, );".len());
            let line = format!("const a = f(b, {name});\n");
            assert!(line.len() > 101);
            four_tests(&line, Some(&line))
        },
    );
    h.case(
        "printer/rule Width: a trailing comment does not count",
        || {
            let name = rep("x", 100 - "const a = f(b, );".len());
            let line = format!("const a = f(b, {name});  // a comment that runs past the width\n");
            four_tests(&line, Some(&line))
        },
    );
    h.case(
        "printer/rule Width: no line passes 100 without a literal or a comment",
        || {
            let mut out = String::new();
            for &(_, _, _, expected) in ROWS {
                out.push_str(expected);
            }
            for line in out.lines() {
                let width = line.chars().count();
                let excused = ["\"", "'", "`", "//", "/*", "enrang-fmt-ignore"]
                    .iter()
                    .any(|mark| line.contains(mark));
                assert!(width <= 100 || excused, "{width} columns: {line}");
            }
        },
    );
    h.case("printer/rule Width: an empty file prints empty", || {
        four_tests("", Some(""))?;
        four_tests("\n\n  \n", Some(""))
    });
}
