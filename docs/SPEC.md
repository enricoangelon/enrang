# Enrang Language Reference (prototype edition)

Language: Enrang. CLI: `enrang`. Source extension: `.en`. Source encoding: UTF-8.

This document is normative for the parser, type checker, borrow checker, library surface and golden diagnostics. "Must" and "is" are requirements; anything not listed as in scope produces a diagnostic from section 16 and never a miscompile. Implementation structure (LIR, encoder tables, VM internals, boot-sector layout) belongs to the architecture document; only what programmers can observe is fixed here.

The compiler and `enrang dev` run only on a modern x86-64 development machine and cross-compile. Only their output runs on old chips. "Enrang" in this document always means the language; statements about CPUs concern emitted programs.

## 0. Thesis and decisions

**Thesis.** TypeScript syntax, Rust semantics, no lifetime type system. References live only in stack-frame slots (locals, parameters, temporaries, return values) and in the `private` fields of borrowing classes, which themselves live only where a reference can. That restriction removes lifetime syntax, region inference, variance and drop check, while leaving a flow-sensitive MIR borrow check that accepts everything NLL accepts within the restriction, plus NLL problem case #3. There is one reference type, `&T`: whether a borrow reads or writes is inferred from function bodies and stored in each module's interface, so callers are checked without reading the bodies they call.

| # | Question | Decision |
|---|---|---|
| 1 | Bindings | `const` cannot be reassigned and its owned contents cannot change (Rust's `let`); `let` can (Rust's `let mut`); a `const` may hold a reference and write through it; parameters are read-only unless marked `let`; `const xs = []; xs.push(1)` gets a one-token fix-it and a TS note |
| 2 | Ownership surface | One reference type `&T`; bare `T` moves. Whether a borrow reads or writes is inferred from bodies and checked at every call. `&` is written wherever a reference is made, calls included (`f(&x)`), except for a string literal or a value that already is a reference; receivers, operators, `console.log`, template holes and `expect` borrow automatically |
| 3 | Lifetimes | No syntax. Frame-bound references (rule R1), plus `private` reference fields of borrowing classes, which live only where a reference can; a returned reference's sources are inferred from the body (rule R3), with signature defaults where no body can be read or trusted; never in array elements, enum cases or generic arguments |
| 4 | Copy | Scalars, `&T`, raw and function pointers, payload-free enums, and fixed arrays, tuples, anonymous objects and `T \| null` of Copy; classes opt in with `implements Copy`, never with a destructor; `.clone()` synthesised memberwise |
| 5 | Data types | `class` is a nominal inline value type with `constructor`, `destructor`, methods and mandatory `public`/`private`/`protected` members, built with `new C(...)` or, when it has no constructor, `new C { f: v }`; single inheritance with `extends`, `abstract`, `final`, `override` and `super`, where a call always runs the object's own method, in a base constructor too, since a subclass sets its own fields before `super(...)`; `override` also gives an inherited field a new default; and moving a whole object out of a `Box<A>` or `&A` checks its class at run time. Receivers are inferred from the body; `move m()` consumes the object, and `let m()` says it changes the object where no body shows it. A returned reference is as changeable as its source, as in TypeScript, unless the return type says `readonly`. Anonymous object types `{ name: string, age: int }` are structural |
| 6 | Interfaces | Structural with optional checked `implements` and one exact satisfaction rule (4.4); usable as bounds (`T extends A & B`), as by-value parameters and as `&I` wherever a reference may stand (an `&I` parameter that is not nullable gets one copy per class for direct calls, and one dynamic copy for a two-word `&I`, the form an `&I` has everywhere else, `&I \| null` and calls chosen at run time included), and as `Box<I>` for dynamic dispatch; an interface with only fields is a named object type; `Copy`, `Error` and the sealed `core` bounds are nominal; every type satisfies `Display`, so every value prints, a class with no `fmt` field by field |
| 7 | Sums and null | Nominal `enum` whose cases name their fields and are created without `new`; string-literal unions as payload-free enums; exhaustive `match` expression as in PHP 8, with comma-separated values, `default`, guards and ranges, whose arms bind nothing and narrow the subject; `T \| null` as non-flattening built-in option, path narrowing, `?.`, `??`, `x!` |
| 8 | Errors | `Result<T, E>` where `E` is an error type (any enum, `Failure`, or a class that `implements Error`); `Result<T>` is `Result<T, Failure>`, a text error made by `Err("...")`; a plain returned value counts as success; postfix `?` with no conversion, except into `Result<T>`, where `?` and `Err(e)` turn any error into the text it prints; unused `Result` is an error, panic aborts, bounds and overflow are always checked |
| 9 | Numbers | No `number` (EN0225); `int` = `i32` on every target, explicit widths plus target-width `isize`/`usize`; literals infer across the function, default `int`/`f64`; `length()` is `isize`; comparisons between integer types compare true values, and any integer type indexes |
| 10 | Strings | One type `string`: owned UTF-8 `{ptr,len,cap}`; literals have `cap == 0`; `+` allocates; `slice` gives a read-only `&string` part and copies nothing, and a returned `&string` that may be a part can't grow; no `str`; `length()` counts bytes, `charCount()` characters |
| 11 | Arrays | `T[]` owned and growable, `T[N]` inline, tuples `[int, string]`; indexing is a checked place and never moves; `&Slice<T>` is a view that can be read or set but never grown, made by `xs.slice(a, b)` or from a `&T[N]` or `&T[]`, so a function that only reads or sets elements takes `&Slice<T>` and one that pushes takes `&T[]`; `for (const x of &q)` borrows `q` and locks it for the whole loop, `for (const x of q)` takes `q`; `[...a]` builds a new `T[]` by cloning; owned iteration over `T[N]` needs Copy elements |
| 12 | Generics | Monomorphised, checked once before instantiation, `T` ranges over reference-free types (no borrowing classes either), and also over a view `Slice<U>` where its function uses it only behind `&`; a bound is an interface or a class, `T extends Animal` admitting its subclasses; local inference; a function taking an anonymous object type or an interface type gets one copy per shape |
| 13 | Closures | Arrows are values, passed as arguments or stored in locals. A capturing arrow holds loans on what it uses while it will still be used, and cannot be stored in a field or returned (EN1007); an arrow that captures nothing is a plain `fn` value. `fn` pointers are first-class but non-capturing |
| 14 | Destructors | `public destructor()` runs at every scope exit, `?` included, and `dispose(x)` ends a value early; reverse creation order for locals and elements and reverse declaration order for a class's fields, the destructor body before the fields, and a derived class's destructor and fields before its base's, as in C++, though a subclass's fields are created first; no field moves out of a class with a destructor |
| 15 | Modules | Multi-file relative `import`, `import * as m` and re-exports with `public import`; every top-level declaration is `public` or `private`; no cycles; modular checking through interface files, which are checked when loaded, whole-program code generation; `core`/`alloc`/`os` by bare name; library child modules and user folders import as namespaces; a program may begin with top-level statements, as in C#; tests live in `*.test.en` files |
| 16 | FFI and unsafe | `unsafe` blocks with exactly five powers; static storage is `unsafe let`; one raw pointer kind `*T`; a function containing `unsafe` counts as writing every reference unless marked `const`; `@dll` plus `declare function` on Windows; ABI-tagged and `unsafe fn` pointers; no libc FFI |
| 17 | Deferred | Section 16, each with a named diagnostic |

## 1. Language tour

The three programs in this section are extracted cases, like those of sections 14 and 15. Section 14 defines the `case` markers.

<!-- case: tour files=tour.en cmd="enrang run tour.en" exit=0 stdout=inline -->
```ts
// tour.en: run with `enrang run tour.en`
const prog = [Op.Push { value: 2 }, Op.Push { value: 40 }, Op.Add, Op.Print];
const r = run(&prog);  // `&prog` lends the array; the result is owned
match (r) {  // `Ok` and `Err` arms read `r.value` and `r.error`
  Ok => console.log(`result ${r.value}`),
  Err => console.log(`error: ${r.error}`),
}

private enum Op {
  Push { value: i64 },
  Add,
  Mul,
  Print,
}

private class Stack<T> {
  private items: T[] = [];

  public push(x: T): void { this.items.push(x); }  // `x` moves in; the body writes `this`
  public pop(): T | null { return this.items.pop(); }
  public top(): &T | null { return this.items.last(); }  // borrows from `this`, as changeable as the stack (R3)
  public size(): isize { return this.items.length(); }
}

private class Trace {
  public constructor(public name: string) {}
  public destructor() { console.log(`[${this.name}] done`); }
}

private function pop2(s: &Stack<i64>): Result<i64> {
  const v = s.pop();
  if (v == null) { return Err("stack underflow"); }
  return v;  // narrowed to i64; a plain value means `Ok(v)`
}

private function run(program: &Slice<Op>): Result<i64> {
  const _trace = new Trace("vm");  // its destructor runs on every exit, `?` included
  let s = new Stack<i64>();
  for (const op of program) {  // op: &Op
    match (op) {  // arms name the case; inside an arm, `op` is narrowed to it
      Op.Push => s.push(op.value),  // `op.value` reads through `&Op`, since i64 is Copy
      Op.Add => {
        const b = pop2(&s)?;
        const a = pop2(&s)?;
        s.push(a + b);
      },
      Op.Mul => {
        const b = pop2(&s)?;
        const a = pop2(&s)?;
        s.push(a * b);
      },
      Op.Print => {
        const t = s.top();
        if (t != null) { console.log(`top = ${t}`); }  // last use: the loan ends here
      },
    }
  }
  return pop2(&s);
}
```

Output: `top = 42`, `[vm] done`, `result 42`.

**Ownership in three lines.** `T` hands a value over and `&T` lends it; whether the borrower reads or writes is inferred from its body and checked at every call. A loan is always written: `f(&x)` lends `x`, and `f(x)` moves it, or copies it if it is Copy. Lending copies nothing: it passes a reference.

<!-- case: ownership files=ownership.en cmd="enrang check ownership.en" exit=0 -->
```ts
function total(xs: &Slice<i64>): i64 {
  let t = 0;
  for (const x of xs) { t += x; }
  return t;
}

function bump(xs: &Slice<i64>): void {
  for (const x of xs) { *x += 1; }
}

function keep(xs: i64[]): i64[] { return xs; }

let a = [1, 2, 3];
total(&a);  // lent for reading
bump(&a);  // lent for writing, because `bump` writes the elements
const b = keep(a);  // moved; using `a` now is EN0601
```

**TS habits that survive.** Template literals, `class` with `extends`, `abstract`, `override`, `protected` and `super`, `public` and `private`, `new`, `implements`, interfaces as types and data interfaces such as `interface Point { x: f64; y: f64; }`, `T extends A & B`, `T | null`, `?.`, `??`, `x!`, object literals and anonymous object types, string-literal unions, tuples and destructuring, default and optional parameters, arrow functions in `map` and in locals, `for...of`, array spread `[...a]`, `import { a } from "./b"` and `import * as b from "./b"`, top-level statements, `describe`/`test`/`expect`.

**TS habits the compiler redirects.** `===` to `==`, `var` to `let`, `any` to a generic, `undefined` to `null`, `number` to `f64` or `int`, `export` to `public`, `.length` to `.length()`, `throw` to `return Err("...")`, `switch` to `match`, truthiness to explicit comparison. Section 13 lists all of them.

**A kernel in the same language.**

<!-- case: tour-kernel files=hello.en cmd="enrang build --target=i386-none --image=hdd hello.en" exit=0 -->
```ts
// hello.en: enrang build --target=i386-none --image=hdd hello.en
import { serial, vga } from "os";

@entry private function kmain(boot: &BootInfo): never {
  serial.init(boot);
  let screen = vga.Screen.fromBoot(boot);
  screen.write("Hello from Enrang\n");
  serial.write(boot, "Hello from Enrang\n");
  halt();
}

@panicHandler private function onPanic(info: &PanicInfo): never {
  vga.emergency(info.message());
  halt();
}
```

No allocator is registered, so `string` values and `T[]` are compile errors here (EN0820). String literals still work, because a literal in `&string` position is a static descriptor in read-only data.

## 2. Lexical grammar

Input is UTF-8; invalid UTF-8 is EN0001. A leading BOM is skipped and counts toward neither lines nor columns; anywhere else it is an ordinary scalar. Line terminators are LF and CRLF. A line is what column counting resets on; columns count Unicode scalar values from 1.

```ebnf
Whitespace   = " " | "\t" | "\r" | "\n" ;
LineComment  = "//" { any - "\n" } ;
BlockComment = "/*" { any } "*/" ;            (* does not nest; unterminated is EN0002 *)
AnchorComment= "//~" ...  | "//!" ... ;       (* ordinary comments; meaningful only in compileFails snippets *)

Ident        = IdentStart { IdentCont } ;     (* XID_Start | "_" | "$" ; XID_Continue | "$" *)
Keyword      = "abstract" | "as" | "asm" | "break" | "class" | "const" | "constructor"
             | "destructor" | "continue" | "declare" | "default" | "do" | "else" | "enum"
             | "false" | "final" | "fn" | "for" | "function" | "if" | "implements" | "import"
             | "interface" | "let" | "match" | "move" | "never" | "new" | "null" | "override"
             | "private" | "protected" | "public" | "readonly" | "return" | "static" | "super"
             | "this" | "true" | "type" | "unsafe" | "void" | "while" ;
             (* `default` outside a `match` arm, as in `export default`, is EN1009 *)
Contextual   = "describe" | "test" | "expect" | "compileFails" | "compileOk" | "raw"
             | "extends" | "from" | "of" | "not" | "in" | "out" | "clobbers"
             | "assert" | "extend" | "where" ;
             (* identifiers everywhere except the grammar positions that name them *)
Reserved     = "any" | "await" | "async" | "case" | "catch" | "delete" | "export" | "finally"
             | "instanceof" | "keyof" | "namespace" | "number" | "switch" | "throw" | "try"
             | "typeof" | "undefined" | "unknown" | "using" | "var" | "yield" ;
             (* lexed as keywords; each has a section 13 or 16 hint *)

IntLit       = DecLit | HexLit | OctLit | BinLit ;
DecLit       = Digit { Digit | "_" } ;        (* leading zero then digit is EN0005, TS legacy octal *)
HexLit       = "0x" HexDigit { HexDigit | "_" } ;
OctLit       = "0o" OctDigit { OctDigit | "_" } ;
BinLit       = "0b" BinDigit { BinDigit | "_" } ;
FloatLit     = Digit { Digit | "_" } "." Digit { Digit | "_" } [ Exponent ]
             | Digit { Digit | "_" } Exponent ;
Exponent     = ("e" | "E") [ "+" | "-" ] Digit { Digit } ;
             (* ".5" and "5." are EN0006; suffixes such as 1u8 are EN0007: use `1 as u8` or an annotation *)

StringLit    = '"' { StrChar | Escape } '"' | "'" { StrChar | Escape } "'" ;
Escape       = "\\" ( "n" | "r" | "t" | "0" | "\\" | '"' | "'" | "`" | "$"
                    | "x" HexDigit HexDigit | "u{" HexDigit{1,6} "}" ) ;
             (* unknown escape EN0003; unterminated EN0004; \x above 7F must form valid UTF-8 *)
TemplateLit  = "`" { TplChar | Escape | "${" Expr "}" } "`" ;
             (* nests; the tokeniser tracks brace depth inside ${ } *)
RawTemplate  = "raw" "`" { any - "`" } "`" ;  (* no escapes, no interpolation, no surrounding space *)

Punct = "(" ")" "{" "}" "[" "]" ";" "," ":" "." ".." "..." "=>" "@" "?" "?." "??" "!" "~"
      | "+" "-" "*" "/" "%" "&" "|" "^" "<<" ">>" "&&" "||"
      | "=" "+=" "-=" "*=" "/=" "%=" "&=" "|=" "^=" "<<=" ">>=" "++" "--"
      | "==" "!=" "<" "<=" ">" ">=" "===" "!==" ">>>" "**" ;
```

**Tokenising rules.**
- Maximal munch, and the parser may then split a token (`split_token`). When closing type arguments it splits `>>`, `>>>`, `>=` and `>>=` after their first `>`, so `Box<Box<Box<i64>>>` and `let x: Box<i32>= v;` parse. In prefix or type position it reads `**` as two `*` and `&&` as two `&`, so `**pp` and `**u8` are ordinary, and `&&T` reaches EN0702.
- `...` is tried before `..`, and both before the `.5` check of EN0006. So `0..n` is `0`, `..`, `n`; `[...a]` is `[`, `...`, `a`, `]`; `[....5]` is `[`, `...`, then `.5`, which is EN0006; and `a...b` is `a`, `...`, `b`, which the parser rejects (3.4). `5.` never takes a dot, so no `split_token` is needed.
- `===`, `!==`, `>>>` and `**` are tokens only so they can get EN0201, EN0201, EN0208 and, for `**` in binary position only, EN1022; the parser recovers as `==`, `!=`, `>>` and a call to `pow`.
- `'` followed by identifier characters and then any character other than `'` lexes as a `Lifetime` token when the previous token is `&` or `<`, or is `,` directly after another `Lifetime`. The parser reports it as EN1005. Everywhere else `'` starts a string, so `'a'` and `f(x, 'a b')` are strings. `&'a b'` also gets EN1005, with a note to write `&"a b"`.
- `?.` is always one token and always means optional chaining. To propagate then access, write `(x?).f`.
- Every token records `spaceBefore: bool`. **Postfix `?` and `!` must have `spaceBefore == false`; ternary `?` must have `spaceBefore == true`.** `a ? b : c` is a ternary, `a? b : c` is EN0103 with a fix-it, `f()?` propagates, `f() ?` is EN0103, whose fix-it removes the space. A line break before `?` counts as the space a ternary `?` requires, so a broken ternary may start a line with `?`. A ternary `?` whose `:` never comes is EN0100, `expected `:` to finish the choice`.
- `!` after an expression with `spaceBefore == false` is the postfix null assertion; `!=` is munched first, so `x! = y` needs the space shown.
- No automatic semicolon insertion. A missing `;` is EN0101, whose fix-it inserts it; the parser recovers at the next line start as if it were present, so a TS file with no semicolons gets one diagnostic per file rather than one per statement. That diagnostic is the first site; it adds ``= note: N more statements in this file are missing `;` `` and its fix-it carries every insertion.
- An unclosed `{` at end of file is EN0102. The parser compares each matched `}` with the indentation of the line holding its `{`. The first mismatch gives the primary span (that `{`) and the secondary span (that `}`), and the fix-it inserts a `}` at the `{` line's indentation before the `}` line. If nothing mismatches, the innermost open `{` is primary and the insertion goes at end of file. The parser then recovers as if the fix-it's `}` were present, as it does for a missing `;`, so in G02 the `}` on line 4 closes `greet` and `greet();` stays a top-level statement.

## 3. Syntax grammar

Notation: `[x]` optional, `{x}` zero or more, `A % ","` means `[A {"," A} [","]]` (comma list, trailing comma allowed).

### 3.1 Files and items

```ebnf
File        = { Import } { TopStmt } { Item } ;
             (* a statement after the first Item is EN0115 *)
TopStmt     = Stmt | { Decorator } FunctionDecl | TopAssert ;
             (* top-level statements and the local functions among them, which state no
                visibility (section 6); an unmarked function in a file with no statements is EN0226 *)
Import      = [ "public" ] "import" ( "{" ImportName % "," "}" | "*" "as" Ident )
              "from" StringLit ";" ;
ImportName  = Ident [ "as" Ident ] ;
             (* path "./x", "../x" relative, extension omitted; "core", "core/...", "alloc",
                "alloc/...", "os", "os/..." name embedded library modules; the files of a folder
                import as namespaces; `public import` re-exports; binding rule in 4.12 *)

Item        = { Decorator } ItemVis ItemKind | { Decorator } ExtendDecl | TestItem | TopAssert ;
ItemVis     = "public" | "private" ;           (* missing: EN0226, which also turns `export` into `public` *)
Decorator   = "@" Ident [ "(" DecoratorArg % "," ")" ] ;
DecoratorArg= Literal | ObjectLit | Ident ;    (* an ObjectLit here holds literals and arrays of literals *)
ItemKind    = FunctionDecl | ClassDecl | EnumDecl | InterfaceDecl | TypeAlias | TopConst
            | UnsafeLet | DeclareFn ;
MemberName  = Ident | Keyword | Reserved ;     (* the position decides: `node.type`, `new Point { type: 1 }` *)

FunctionDecl= [ "unsafe" ] "function" Ident [ TypeParams ] "(" Param % "," ")"
              [ ":" RetType ] Block ;
             (* library modules may use MemberName as the name; such a function is reachable
                only through a namespace: `ptr.null<T>()` *)
DeclareFn   = "declare" "function" Ident [ TypeParams ] "(" Param % "," ")" [ ":" Type ] ";" ;
Param       = [ "let" | "const" ] Binding [ "?" ] ":" ParamType [ "=" Expr ] ;
             (* "let": the body may change its own copy or, on a reference, write through it;
                "const": a reference parameter only read, in a function containing unsafe (5.9);
                `x?: T` means `x: T | null = null`, a closure type included, and `x?: T | null`
                means the same, never a nested null (4.14); "?" with "=" is EN0227, and a
                parameter with neither after one with either is EN0229 *)
ParamType   = Type | ClosureType | "(" ClosureType ")" "|" "null" ;
             (* `| null` only at the top of a closure type: `((k: u8) => void) | null` *)
RetType     = [ "readonly" ] Type ;
             (* "readonly": the returned reference is read-only (5.4); only before a type that
                starts with `&`, a tuple type with a reference part or a borrowing class type,
                each optionally `| null`, else EN0214, which waits for name resolution when the
                type is a name; no `from` clause: result sources are inferred, 5.4 *)
TypeParams  = "<" TypeParam % "," ">" ;
TypeParam   = Ident [ "extends" Bound { "&" Bound } ] ;
Bound       = NamedType ;                     (* an interface, or a class and its subclasses (4.10) *)

TopConst    = "const" Ident [ ":" Type ] "=" ConstExpr ";" ;
UnsafeLet   = "unsafe" "let" Ident ":" Type [ "=" ConstExpr ] ";" ;
             (* the only spelling of static storage; a plain top-level `let` is a statement,
                and in an imported file EN0312 *)
TopAssert   = "assert" "(" Expr [ "," StringLit ] [ "," ] ")" ";" ;
             (* checked at compile time (4.9); among a program's top-level statements, a
                non-constant condition is checked at run time *)
ConstExpr   = Expr ;   (* restricted, section 4.9 *)

ClassDecl   = [ "abstract" | "final" ] "class" Ident [ TypeParams ] [ "extends" NamedType ]
              [ "implements" NamedType { "," NamedType } ] "{" { ClassMember } "}" ;
             (* extending a `final` class is EN0442 *)
ClassMember = { Decorator } ( FieldDecl | Constructor | Destructor | MethodDecl ) ;
FieldDecl   = Visibility [ "override" ] [ "readonly" ] MemberName [ "?" ] ":" FieldType
              [ "=" Expr ] ";" ;
             (* `x?: T` means `x: T | null = null`, and `x?: T | null` means the same, never a
                nested null; "?" with "=" is EN0227; "override": a new default for a visible
                inherited field (4.3); "readonly" here: no assignment after construction *)
FieldType   = [ "readonly" ] Type | "[" FieldType % "," "]" [ "|" "null" ] ;
             (* "readonly": the class never writes through this reference (4.3); only before
                a type that starts with `&`, optionally `| null`, at the top of a field's type
                or at a reference part of its tuple, `private t: [readonly &i64[], i32];`, else
                EN0214, before a whole tuple type included; distinct from the modifier before
                the name, and both may be written: `private readonly src: readonly &Slice<u8>;` *)
Visibility  = "public" | "private" | "protected" ;   (* missing: EN0226 *)
Constructor = Visibility "constructor" "(" CtorParam % "," ")" Block ;
CtorParam   = [ Visibility [ "readonly" ] ] [ "let" | "const" ] Ident [ "?" ] ":" FieldType
              [ "=" Expr ] ;
             (* "let", "const", "?" and "=" as in Param; `readonly` before the type only with a
                Visibility, which makes the parameter a field *)
Destructor  = "public" "destructor" "(" ")" Block ;
MethodDecl  = Visibility [ "static" | "abstract" ] [ "override" ] [ "let" | "const" | "move" ]
              [ "unsafe" ] MemberName [ TypeParams ] "(" Param % "," ")" [ ":" RetType ]
              [ WhereClause ] ( Block | ";" ) ;
             (* "let": may change the object, also where the body doesn't, as on an abstract
                method or an overridable hook (4.3); "const": `this` is only read in a body
                containing unsafe (5.9); "move": consumes `this`; ";" in place of the body only
                for `abstract`, or for an @intrinsic member of an `extend` *)
WhereClause = "where" WherePred { "," WherePred } ;
WherePred   = Ident "extends" Bound { "&" Bound } ;  (* Ident names a parameter of the enclosing class *)

EnumDecl    = "enum" Ident [ TypeParams ] "{" Variant % "," [ ";" { MethodDecl } ] "}" ;
Variant     = { Decorator } Ident [ "{" EnumField % "," "}" | "=" ( ConstExpr | StringLit ) ] ;
             (* cases name their fields; the "=" values are all integers or all texts, EN0456 *)
EnumField   = MemberName ":" Type ;

InterfaceDecl = "interface" Ident [ TypeParams ] "{" { IfaceMember } "}" ;
IfaceMember = [ "static" ] [ "let" | "move" ] [ "unsafe" ] MemberName [ TypeParams ] "(" Param % "," ")"
              [ ":" RetType ] [ WhereClause ] ";"
            | MemberName [ "?" ] ":" Type ";" ;
             (* no accessor; "let": may change the object; a returned reference is writable
                unless the return type says `readonly`; an interface with only fields is a named
                object type; fields and methods mixed are EN0417 *)
TypeAlias   = "type" Ident [ TypeParams ] "=" ( Type | StringLit { "|" StringLit } ) ";" ;
             (* a union of string literals is a payload-free enum (4.3) *)
ExtendDecl  = "extend" [ TypeParams ] Type "{" { { Decorator } MethodDecl } "}" ;
             (* library only, see below *)
```

Every top-level declaration states `public` (other files may import it) or `private` (only its own module, `*.test.en` part included, may use it); a missing one is EN0226, and `export` gets the same code with a fix-it to `public`. Static storage states one too: `@at(0xB8000) private unsafe let screen: u16[2000];`. A local function among a program's top-level statements, an `extend` block, a top-level `assert` and a test item state none. Class fields, methods and constructors, and enum methods, state `public`, `private` or `protected`, and a `private` member is visible only inside the body that declares it, never to the module's `*.test.en` part (4.3); a destructor is always `public`; interface members state none. A file may begin with top-level statements, which make it a program (section 6): imports come first, then the statements and the local functions written among them, then classes and other declarations. Only the file being built may have top-level statements (importing one that has them is EN0312), and freestanding targets have none: a kernel names its entry point with `@entry`.

A `where` clause adds bounds to a class type parameter for one method. The body is checked with the extended bounds. A call is checked after inference and reports EN0419, with the method's bound as the secondary span: `sort() where T extends Ord`. The bounds are part of the signature. `where` is legal in user code too.

Allowed decorators are fixed; anything else is EN0806. Their targets are checked, and a decorator that makes the compiler, a runtime or foreign code the caller is also EN0806 on a local function that has hidden arguments (5.5):

| Decorator | Target | Section |
|---|---|---|
| `@entry` | function | 7.8 |
| `@panicHandler` | function | 7.9 |
| `@globalAllocator` | `unsafe let` | 7.9 |
| `@interrupt`, `@interrupt({ errorCode: true })` | function | 7.7 |
| `@naked`, `@bits(16\|32\|64)` | `unsafe function` | 7.5 |
| `@requires("feature", ...)` | function, method | 10.3 |
| `@mustUse` | function, method | 6 |
| `@section("name")` | function, `unsafe let`, `const` | 7.8 |
| `@at(address)` | `unsafe let` | 7.8 |
| `@packed`, `@repr("C"\|"u8"\|"u16"\|"u32")`, `@align(n)` | `final` class with no base (EN0827), enum, `@align` also `unsafe let` | 7.6 |
| `@dll("name")` | `declare function` | 7.10 |
| `@abi("win64"\|"sysv")` | function, function pointer type | 7.10 |
| `@lang("name")` | `core`, `alloc` and `os` modules only | below |
| `@intrinsic("Kind")` | `declare function` or a bodyless `extend` member in `core`, `alloc`, `os` | below |
| `@hostCall("name")` | `declare function` in `os/vm` only | below |
| `@was("oldName")` | class, enum, field, variant, function; inert outside `dev` | 8.5 |
| `@devMigrate` | function with an object-typed parameter; stripped outside `dev` | 8.5 |
| `@owner` | `alloc` only | 8.5 |

**Library-only forms** (`core`, `alloc`, `os`; EN0806 anywhere else). The library needs these three, and they are the whole of the mechanism behind built-in types:

- **`extend`** declares members on a type that has no class body of its own, or that lives in another layer: `extend<T> T[] { public push(x: T): void {...} public static withCapacity(n: isize): T[] {...} }`, `extend<T> T | null {...}`, `extend<T> *T {...}`, `extend<I extends __Int> I { @intrinsic public wrappingAdd(o: I): I; }`. A member marked `@intrinsic` has `;` in place of its body. Type constants such as `i64.MAX` are plain constants read through the type's name, not members. An `extend` body sees the private fields of the type it extends. Member lookup and interface satisfaction both read `extend` members, so `i64` satisfies `Ord`. `extend` on an anonymous object type or a tuple type, written out or reached through a `type` alias, is EN0439: such a type cannot have methods.
- **`@lang`** registers an item the compiler names. `string` is an `@lang("string")` class in `core/string`; `T[]` and `Box<T>` are `@lang("array")` and `@lang("box")` classes in `alloc`. They are real `final` classes with fields private to the library. `string`, `T[]` and `Box<T>` remain their only spellings.
- **`@intrinsic("MemCopy") public declare function memCopy<T>(d: *T, s: *T, n: usize): void;`** binds a name to a compiler intrinsic. **`@hostCall("fs.open") public declare function ...`** binds a VM host call. Both are exempt from EN0815 and always `unsafe` to call, so safe library wrappers sit on top of them. A bodyless `extend` member takes its safety from its own declaration: `wrappingAdd` is safe, `readVolatile` is `unsafe`.

### 3.2 Types

```ebnf
Type        = NullableType ;
NullableType= PrefixType [ "|" "null" ] ;      (* any other `|` is EN0406; string literals joined by `|` are a
                                                  whole TypeAlias, and anywhere else EN0216; a closure type
                                                  takes `| null` only at the top of a parameter's type (3.1) *)
PrefixType  = "&" PrefixType | "*" PrefixType | PostfixType ;
PostfixType = PrimaryType { "[" [ ConstExpr ] "]" } ;
PrimaryType = NamedType | "(" Type ")" | FnPtrType | "void" | "never" | "null"
            | ObjectType | TupleType ;
NamedType   = Ident { "." Ident } [ "<" Type % "," ">" ] ;
FnPtrType   = { Decorator } [ "unsafe" ] "fn" "(" TypedParam % "," ")" "=>" RetType ;
ClosureType = "(" TypedParam % "," ")" "=>" Type ;  (* parameter position only: else EN0705 *)
TypedParam  = [ "let" ] Ident ":" Type ;       (* a closure type here is EN0705: closures do not nest *)
ObjectType  = "{" ( MemberName [ "?" ] ":" Type ) % "," "}" ;
TupleType   = "[" Type % "," "]" ;
```

`&T[]` is `&(T[])`, a whole growable array, and `&Slice<T>` a view of elements that never grows (4.3); `Slice<T>` appears only behind `&`. `&T | null` is `(&T) | null`. `T[3][4]` reads left to right: an array of 4 elements of `T[3]`. `[int, string]` is a tuple type and `int[2]` a fixed array; a bracket literal takes its meaning from the expected type. `{ name: string, age: int }` is an anonymous object type: structural, with its fields separated by commas and in any order, and `x?: T` is a field of type `T | null`, or `T` when `T` as written is already nullable, that a literal may leave out. `*u8` is the one raw pointer kind; reading and writing through it both need `unsafe`, and a function that is not `unsafe` and does either through one of its raw-pointer parameters gets warning EN0828 (7.1). `unsafe fn(...) => R` is a function pointer whose call is power 2 of section 5.9. Parameter names in function pointer and closure types exist so that `let` can mark a parameter the function may change, as in `(let x: &i64) => void`; identity compares by position, and 4.1 says how the `let` marks convert. A function pointer's result type may start with `readonly`, as a function's may: `fn(xs: &Slice<i64>) => readonly &i64`. A closure parameter may be nullable at the top, `handler: ((k: u8) => void) | null`, which `handler?: (k: u8) => void` abbreviates (4.14); that is not a nested closure type.

### 3.3 Statements

```ebnf
Block       = "{" { Stmt } "}" ;
Stmt        = VarDecl | IfStmt | WhileStmt | DoStmt | ForStmt | ForOfStmt | ReturnStmt
            | BreakStmt | ContinueStmt | Block | UnsafeBlock | LabeledStmt
            | MatchStmt | ExprStmt | ExpectStmt ;               (* ExpectStmt: section 3.6 *)
MatchStmt   = MatchExpr [ ";" ] ;
VarDecl     = "const" Binding [ ":" Type ] "=" Expr ";"
            | "let" Binding [ ":" Type ] [ "=" Expr ] ";" ;
             (* a `const` without a value is EN0116; destructuring requires "=" Expr *)
Binding     = Ident | ObjPattern | TuplePattern ;
ObjPattern  = "{" ( MemberName [ ":" Binding ] ) % "," "}" ;   (* `{ name: who }` renames *)
TuplePattern= "[" Binding % "," "]" ;
             (* patterns nest: `{ pos: { x, y } }`, `[i, { name }]`; tuples and objects only, at
                any depth: a `= default` is EN1010, `...` EN1013, and an array source EN1042
                once types are known *)
IfStmt      = "if" "(" Expr ")" Block [ "else" ( IfStmt | Block ) ] ;
WhileStmt   = "while" "(" Expr ")" Block ;
DoStmt      = "do" Block "while" "(" Expr ")" ";" ;
ForStmt     = "for" "(" ( VarDecl | ExprStmt | ";" ) [ Expr ] ";" [ Expr ] ")" Block ;
ForOfStmt   = "for" "(" ( "const" | "let" ) Binding "of" ForSource ")" Block ;
ForSource   = Expr ".." Expr | Expr ;
             (* `&q` borrows the source and a source with no `&` is taken; a range is half-open
                and appears only here and in `match` arms; classified in 5.6 *)
ReturnStmt  = "return" [ Expr ] ";" ;
BreakStmt   = "break" [ Ident ] ";" ;
ContinueStmt= "continue" [ Ident ] ";" ;
LabeledStmt = Ident ":" ( WhileStmt | DoStmt | ForStmt | ForOfStmt ) ;
UnsafeBlock = "unsafe" Block ;
ExprStmt    = Expr ";" ;
```

Braces are mandatory after `if`, `else`, `while` and `for`; `if (x) y();` is EN0104, whose fix-it wraps the lines indented under the `if` and whose second label marks a line indented as if it were inside it. `} else if (x) {` needs no extra braces, and a one-line guard is written `if (user == null) { return; }`. Assignment and `++`/`--` are expressions (3.4), written as statements through `ExprStmt`; an assignment used as an `if`, `while`, `do` or `for` condition is EN0105, with a `==` fix-it. A `const` always needs a value (EN0116); a `let` declared without one starts at its type's default where the type has one (5.2), so `let n: i64;` is `0`. Destructuring takes tuples and objects: `const [lo, hi] = minMax(&xs);`, `const { name: who, age } = &ada;`, `for (const { name, age } of &people) { ... }`. A tuple pattern gives its right-hand side an expected tuple type (4.7), so a bracket literal there is a tuple: `[a, b] = [b, a];` swaps. A `Block` in a body position has no value.

A statement that starts with `match` ends at the closing `}`, plus an optional `;`, which `enrang fmt` removes (12.5); a `match` inside a declaration keeps the declaration's `;`. No binary or postfix continuation is parsed after it, as in Rust. To use the value, write `const x = match (...) {...};` or `(match (...) {...}).f;`.

`break` or `continue` outside a loop, or crossing an arrow body, is EN0111. An unknown label is EN0112, a label already in scope EN0113, and an assignment target that is not a place (`f() = 1;`) EN0114.

### 3.4 Expressions

```ebnf
Expr        = ArrowFn | Assign ;
Assign      = Ternary [ AssignOp Expr ] ;
             (* right-associative; the value is the target, read after the store (3.5), and a use that
                keeps it from a place that is not Copy is EN0621; the target is a place (EN0114)
                or, after "=", a tuple or object pattern: `[a, b] = [b, a];`. An assignment as an
                if, while, do or for condition, as a ternary's condition, or as an operand of &&,
                || or ! is EN0105 *)
AssignOp    = "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>=" ;
Ternary     = Coalesce [ "?" Expr ":" Expr ] ;
Coalesce    = LogOr [ "??" Coalesce ] ;        (* right-associative; mixing ?? with || or && unparenthesised: EN0106 *)
LogOr       = LogAnd { "||" LogAnd } ;
LogAnd      = BitOr { "&&" BitOr } ;
BitOr       = BitXor { "|" BitXor } ;
BitXor      = BitAnd { "^" BitAnd } ;
BitAnd      = Equality { "&" Equality } ;
Equality    = Relation { ("==" | "!=") Relation } ;   (* chaining `a == b == c` is EN0107 *)
Relation    = Shift { ("<" | "<=" | ">" | ">=") Shift } ;  (* chaining is EN0107 *)
Shift       = Additive { ("<<" | ">>") Additive } ;
Additive    = Mult { ("+" | "-") Mult } ;
Mult        = Cast { ("*" | "/" | "%") Cast } ;
Cast        = Unary { "as" PrefixType } ;
Unary       = ("!" | "-" | "~" | "*" | "&" | "++" | "--" | "void") Unary | Postfix ;
Postfix     = Primary { "." MemberName | "?." MemberName
                      | "[" Expr "]" | CallArgs | "?" | "!" | "++" | "--" } ;
CallArgs    = [ TypeArgs ] "(" Expr % "," ")" ;
TypeArgs    = "<" Type % "," ">" ;   (* expression context: see Disambiguation *)
ArrowFn     = ( Ident | "(" ArrowParam % "," ")" [ ":" RetType ] ) "=>" ( Expr | Block ) ;
ArrowParam  = [ "let" ] Ident [ ":" Type ] ;
             (* a return type after a bare parameter, `x: i64 => x * 2`, is EN0224 *)

Primary     = Literal | Ident | "this" | "super" | "(" Expr ")" | ArrayLit | RepeatLit | NewExpr
            | ObjectLit | CaseLit | MatchExpr | SizeForm | AsmExpr | TypeMember ;
             (* `super` only as `super(...)`, a statement of the own body of a constructor of a class
                with a base, or as `super.name` in a method; in a class with no base, or as
                `super(...)` outside a constructor, EN0219, and inside an arrow or a local
                function of a constructor, EN0619 *)
TypeMember  = NamedType [ "[" "]" ] "." MemberName ;
             (* tried when an identifier is followed by a no-space "<", or by "[" "]":
                Stack<i64>.empty(), i64[].withCapacity(8), E<i64>.V { x: 1 } *)
Literal     = IntLit | FloatLit | StringLit | TemplateLit | RawTemplate | "true" | "false" | "null" ;
ArrayLit    = "[" ArrayElem % "," "]" ;        (* a tuple value where a tuple type is expected *)
ArrayElem   = Expr | "..." Expr ;              (* spread, section 4.13; "..." appears nowhere else *)
RepeatLit   = "[" Expr ";" ConstExpr "]" ;     (* T[N], element must be Copy *)
NewExpr     = "new" NamedType ( "(" Expr % "," ")" | "{" FieldInit % "," "}" ) ;
             (* the named form only for a class with no constructor (EN0447); left-out fields
                take their defaults *)
ObjectLit   = "{" FieldInit % "," "}" ;
             (* an anonymous object, or the named form of the expected class *)
CaseLit     = ( NamedPath | TypeMember ) "{" FieldInit % "," "}" ;
             (* an enum case with fields, created without `new`: Shape.Circle { radius: 2.5 } *)
FieldInit   = MemberName [ ":" Expr ] ;        (* field shorthand: `{ name }` is `{ name: name }` *)
NamedPath   = Ident { "." Ident } ;
MatchExpr   = "match" "(" Expr ")" "{" MatchArm % "," "}" ;
MatchArm    = ( "default" | ArmValue { "," ArmValue } ) [ "if" Expr ] "=>"
              ( Expr | Block | "return" [ Expr ] | "break" [ Ident ] | "continue" [ Ident ] ) ;
ArmValue    = Literal | "-" IntLit | "null" | NamedPath | "Ok" | "Err" | Expr ".." Expr | Expr ;
             (* an arm binds nothing; an enum arm names the case and narrows the subject in its
                guard and body; `Expr` arms only under `match (true)`; ranges are half-open *)
SizeForm    = ("sizeOf" | "alignOf") "<" Type ">" "(" ")"
            | "offsetOf" "<" Type ">" "(" StringLit [ "," ] ")" ;

AsmExpr     = "asm" "(" ( TemplateLit | StringLit ) [ "," AsmOptions ] [ "," ] ")" ;
             (* as in every argument list, a trailing comma is allowed: `enrang fmt` writes one
                when it puts the arguments one per line (12.5) *)
AsmOptions  = "{" AsmOption % "," "}" ;        (* each key at most once, in any order *)
AsmOption   = "in" ":" RegMap | "out" ":" RegMap | "clobbers" ":" "[" StringLit % "," "]" ;
RegMap      = "{" ( RegName [ ":" Expr ] ) % "," "}" ;
RegName     = Ident ;     (* physical register; `{ edx }` is `{ edx: edx }` *)
```

**Disambiguation.**
- `new C`, a path or a `TypeMember` followed by `{` on the same line starts a named-form literal (`NewExpr` or `CaseLit`), and a `{` on a later line never does. All conditions are parenthesised, so no production places an expression directly before a block; the only hazard is a missing `;` before a block on the next line. This works for `new Point { x: 1 }`, `new vga.Screen { ... }` and `Shape.Circle { radius: 2.5 }` alike. The parser cannot tell a class from an enum, so `Point { x: 1 }` parses as a `CaseLit`, and naming a class there is rejected once names are resolved: a class is built with `new`.
- A `{` at the start of a statement always starts a block, as in JavaScript: `{ name: "Ada", age: 36 };` is a block and fails to parse at the `:`. So does a `{` right after the `=>` of an arrow or a `match` arm, so an arrow that returns an object literal wraps it in parentheses: `() => ({ x: 1 })`.
- In expression context, `<` starts type arguments only when it has `spaceBefore == false` and speculation succeeds, and in calls and members the next token must then be `(`, `{` or `.`. After `as`, a no-space `<` also speculates, any next token is accepted, and on failure the parser rewinds and ends the type at the name. In pure type positions spacing is irrelevant, and `enrang fmt` writes no space. So `a < b > (c)` is EN0107, `a<b>(c)` is a call, `f(a < b, c > (d))` has two arguments, `x as usize < n` is a comparison and `x as Box<i32>` is a cast.
- Type arguments always attach to a `Call` or to a `TypeMember`, never to a member access: `x.wrap<u8>()` has one derivation.
- **`...` is consumed in one place only: an `ArrayElem`.** Wherever else an expression, parameter, field, pattern or literal is expected, `...` is EN1013 at that token; the parser skips it and goes on. That covers `f(...a)`, `new C(...a)`, `console.log(...a)`, rest parameters, `(...a) => 1`, `{ ...o }`, `new Point { ...p }`, `const { a, ...r } = p`, `xs[...i]` and `for (const x of ...a)`. `[a, ...r] = xs` and `const [a, ...r] = xs` are EN1013 at `...`, with no EN1042 and no EN0114; without `...` they destructure a tuple, and are EN1042 when `xs` is an array. After a complete expression `...` is EN0100, as in `a...b`, with a fix-it to `..` in a `ForSource`. The first token after `[` picks the spread path with no backtracking, so `[...a; 3]` is EN0100 at `;`, and `[...0..n]` is EN0100 at `..`, because a range is not an expression. `TypeMember` needs `[` and `]` adjacent, so it never meets `x[...`.
- `(x) => ...` is an arrow if a `=>` follows the matching `)`, and `x => ...` if a `=>` follows the identifier. The annotated form `(x: f64): f64 => x * 2` is recognised only where `(` starts an expression, which keeps `a ? (b) : c` a ternary. In the first branch of a ternary it is recognised only if a `:` follows its body, as in TypeScript, so `a ? (b) : c => d` is `a ? (b) : (c => d)`, while `a ? (x): i64 => x : y` has the arrow in its first branch. A bare parameter cannot carry a return type: `x: i64 => x * 2` is EN0224, with the helps `(x: i64) => x * 2` and `(x): i64 => x * 2`.
- An arm binds no names. A bare identifier that names a case of the subject's enum is EN0502 with a fix-it to the qualified name.
- In a class or interface body, `static`, `let`, `const`, `move`, `abstract` and `override` are modifiers only when followed by a `MemberName`, so `public move(): void` declares a method named `move`. `get` is an ordinary name, so the library's `public get(i: isize): &T | null` is a method named `get`.
- At the top level, `test`, `describe`, `compileFails` and `compileOk` followed by `(` or `.` start a test item, never a call statement, and outside a `*.test.en` file a test item is EN1112. `assert` followed by `(` starts a `TopAssert`, never a call statement.

### 3.5 Operator precedence

| Prec | Operators | Assoc | Notes |
|---|---|---|---|
| 1 | `.` `?.` `[]` `()` postfix `?` postfix `!` postfix `++` `--` | left | |
| 2 | prefix `!` `-` `~` `*` `&` `++` `--` `void` | right | |
| 3 | `as` | left | Tighter than `*`, unlike TS |
| 4 | `*` `/` `%` | left | |
| 5 | `+` `-` | left | |
| 6 | `<<` `>>` | left | |
| 7 | `<` `<=` `>` `>=` | none | |
| 8 | `==` `!=` | none | |
| 9 | `&` | left | As in JS: `a & b == c` is `a & (b == c)`, a type error EN0420 with a parenthesise fix-it |
| 10 | `^` | left | |
| 11 | `\|` | left | |
| 12 | `&&` | left | |
| 13 | `\|\|` | left | |
| 14 | `??` | right | `a ?? b ?? c` is the JS idiom. No mixing with 12 or 13 |
| 15 | `? :` | right | |
| 16 | `=` `+=` `-=` `*=` `/=` `%=` `&=` `\|=` `^=` `<<=` `>>=` | right | The value is the target, read after the store, kept only from a Copy place (EN0621). Not as a condition, a ternary's condition, or an operand of `&&`, `\|\|` or `!` (EN0105) |
| 17 | `=>` | | Arrow functions |

Assignment is an expression, and its value is its target read after the store: for a Copy place a copy, so `a = b = 0;` sets both; for a reference place the reference (O7); and for any other place the place itself, which stays the only owner, so a use that does not keep the value, a comparison, an operator, a `console.log` argument, a template hole or a `&` argument, borrows the place as the same use with the place written by name would (O7, N8): shared, or exclusive where it is an argument to a parameter that writes or a source of a write-live result. The loan lives as long as a slot holding it is live (O10), which for a use that keeps nothing is the end of that use's temporaries (D2): the end of the statement, or right after the condition of an `if`, a loop or a ternary. So with `let s = "a".toString();`, `console.log(s += "!");` prints `a!` and leaves `s` as `a!`, and with `let line: string | null = null;` and a `readLine(): string | null`, `while ((line = readLine()) != null) { console.log(line.length()); }` reads until `null`, with `line` a `string` in the body (4.8), as TypeScript narrows it. A use that would keep the value of an assignment to a place that is not Copy would make a second owner of the place, so it is EN0621, `an assignment's value can't be kept`: a binding's initialiser, the right side of another assignment, a by-value argument, a `return`, an element or field of a literal, or a capture by value. So `const t = (s += "?");` is EN0621, labelled `` `s += "?"` is still owned by `s` ``, with `` help: assign first, then copy: `s += "?"; const t = s.clone();` ``, and with strings `a = b = s2;` is EN0621 at `b = s2`, with `` help: assign one at a time: `b = s2; a = b.clone();` ``. `i++` and `i--` give the old value, `++i` and `--i` the new one, and operands evaluate left to right, so `let i = 0; const a = [i++, i++, ++i];` gives `[0, 1, 3]` and leaves `i` at 3. An assignment evaluates its target first, calls in it included, and a compound assignment on a place of Copy type then reads the old value before the right side, as in JavaScript, while one on a non-Copy place, as `s += t` on a string, reserves the place and takes it for writing only when it stores, so its right side may read the place, as `s += s.toUpperCase()` does, but not change it, and nothing it reads from the place may still be used at the store (O6).

### 3.6 Test declarations

Legal only at the top level of a `*.test.en` file, which holds test items and ordinary items. A test item in any other file is EN1112, whose fix-it moves it to that module's `*.test.en` part; `enrang build` and `enrang run` leave tests out.

```ebnf
TestItem    = DescribeItem | TestDecl | CompileCase ;
DescribeItem= "describe" "(" StringLit "," "(" ")" "=>" "{" { DescribeItem | TestDecl | CompileCase } "}"
              [ "," ] ")" ";" ;
TestDecl    = "test" [ "." TestMode ] "(" StringLit [ "," TestExtra ] [ "," TestBody ] [ "," ObjectLit ]
              [ "," ] ")" ";" ;
             (* a trailing comma before ")" here, in CompileCase and in ExpectStmt is the one
                `enrang fmt` writes when it puts the arguments one per line (12.5) *)
TestMode    = "only" | "skip" | "todo" | "panics" | "each" ;
TestExtra   = StringLit                        (* test.panics: expected message substring *)
            | "(" ")" "=>" Expr ;              (* test.each: case generator *)
TestBody    = ( Ident | "(" [ ArrowParam ] ")" [ ":" Type ] ) "=>" Block ;
             (* absent annotation means void; the annotation must be void or Result<void, E>,
                Result<void> included, else EN0401 *)
CompileCase = ("compileFails" | "compileOk") "(" StringLit "," RawTemplate [ "," ObjectLit ] [ "," ] ")" ";" ;
ExpectStmt  = "expect" "(" Expr [ "," ] ")" [ "." "not" ] "." Ident "(" MatcherArg % "," ")" ";" ;
MatcherArg  = Expr | ArmValue ;                (* ArmValue, such as an enum case, only for toMatchPattern *)
```

`ExpectStmt` is a statement, not an expression; it is valid only lexically inside a test body or a function declared in a `*.test.en` file. The parser always builds it for `expect(...).ident(...)`, because it cannot resolve names. Sema reinterprets it as a call if `expect` resolves to an item, and otherwise reports EN1101. `const e = expect(x)` is EN1103. Semantics are in section 12.

## 4. Type system

### 4.1 The type grammar that carries soundness

```text
V ::= bool | i8|i16|i32|i64 | u8|u16|u32|u64 | isize|usize | f32|f64 | void | never
    | string | V[] | V[N] | [V..] | { f: V.. } | Box<V> | Box<I> | V | null | Result<V,V>
    | Class<V..> | Enum<V..> | *V | fn(S..) => S | unsafe fn(S..) => S | T  // T ranges over V; Slice<V> too if only behind & (4.10)
R ::= &V | &Slice<V> | &B | &(B | null) | &I                // Slice<V> only behind &; &I as below
B ::= Class<V..> with a field, or [S..] with a part, in S but not in V  // borrowing values
S ::= V | R | R | null | B | B | null                       // locals, temporaries, params, returns
F ::= (S..) => V | ((S..) => V) | null                      // parameters, and locals holding a capturing arrow; does not nest
I ::= an interface that is not fields-only                  // never in V; alone only as a parameter type
```

`V` is closed: no constructor accepts `R`, `B` or `F`, with one deliberate exception. A function pointer's signature may mention `S`, because a function pointer holds no reference, so `public class C { public cb: fn(s: &string) => void; }` is legal. An `fn` type has no body, so the sources of its returned reference are the signature defaults of 5.4: every reference parameter, or none. Its permission row comes from its marks: each reference parameter is read, or written when marked `let` (`fn(let buf: &Slice<u8>) => usize`), its returned reference is writable unless the type says `readonly` before it or the result is a `&string`, a `&string | null` or a tuple with a `&string` part, which may be a part of a string (4.4, 5.4), and it stores no parameter into a borrowing value (5.4). Type checking never reads a row (N1), so two `fn` types that differ only in their rows are one type in phase 2. Phase 3 compares rows: a value converts to a row that allows more writes at the top of a coercion site (4.5), while under `&`, `T[]`, `T | null`, a field, a generic argument or another `fn` type's parameters or result, rows must be equal, and a mismatch either way is EN0615. Monomorphisation and code generation still tell rows apart, because a row decides how reference parameters are passed (section 11). An unannotated `fn` local takes its initialiser's row, and a ternary or array literal of `fn` values takes the join. A raw pointer `*V` is in `V` because it carries no loan. A borrowing class (4.3), or a tuple with a reference or borrowing part, is in `B`. Like a reference, it lives only in a slot, with or without `| null`, or in a field of another borrowing class, so an array, enum case or generic argument holding one is EN0701, and `&B` is the one reference to something that holds references (5.1). An anonymous object type has no `private` fields, so a reference or borrowing field in one is EN0701. `&&T` and `&(&T | null)` do not exist (EN0702). A `T` instantiated or inferred as a reference is EN0703, except the read-through rule in 4.5. A view is no reference: a `T` that its function uses only behind `&` may stand for a `Slice<U>`, and its `&T` is then a `&Slice<U>` (4.10). An interface type `I` (4.4) has no size, so it is not in `V`, and no type parameter or constructor takes it, except `Box<I>`, which is in `V` and carries the object's table beside it (section 11). `I` alone is only a parameter type, one copy per class (C22). `&I` is in `R` and stands wherever a reference may (R1, 5.1), as in TypeScript and as Rust's `&dyn I`: as a parameter, a local, a result, a `private` field of a borrowing class, a tuple part, and `&I | null`. In a copy of a function made for the classes passed to it (4.4), an `&I` parameter that is not nullable is one pointer; every other `&I` is two words, the object and its class's table for `I`, the form of an `&I` taken from a `Box<I>` (C04, section 11), an `&I | null` parameter included, and so is every `&I` argument of a call whose callee is chosen at run time (4.4). So a type parameter is never inferred or written as an interface type: with `a` and `b` of type `Box<Speaker>`, `mem.swap(&*a, &*b)` is EN1006, with the note `` `Speaker` is an interface, so the size of `*a` isn't known `` and `help: swap the boxes: mem.swap(&a, &b)`, and with G04's `show<T>(x: &T)`, `show(&*a)` is EN1006 with `help: show(&a)`, which prints the contents.

### 4.2 Primitive types

| Type | Meaning | Copy |
|---|---|---|
| `bool` | `true`, `false` | yes |
| `i8 i16 i32 i64` | two's complement | yes |
| `u8 u16 u32 u64` | unsigned | yes |
| `isize usize` | signed and unsigned of the target's pointer width: 32 bits on `i386-*`, 64 bits on `x86_64-*` | yes |
| `f32 f64` | IEEE 754 binary32, binary64 | yes |
| `int` | alias of `i32` on every target | yes |
| `void` | the one-value unit type; expression `void 0` is not special, `Ok()` means `Ok(void)` | yes |
| `never` | the empty type; coerces to anything | yes |
| `string` | owned UTF-8 text, section 11 | no |

There is no `number`: writing it is EN0225, whose note says to use `f64`, or `int` for whole numbers. There is no `char`; `s.byteAt(i)` and `s.codePointAt(i)` yield `u8` and `u32`. Target-width types exist so loops on `i386` stay single-register: no program assumes `usize` is 64 bits, and the compiler rejects constants that do not fit the target (`EN0411`), never truncating.

### 4.3 Declared types

- **`class C<T>`**: nominal, inline value type. `new` never implies heap, and a variable of a class type holds exactly that class. Every field, method and constructor states `public`, `private` or `protected` (EN0226 when missing), as every top-level declaration states `public` or `private` (4.12). `private` members, fields and methods alike, are visible only inside the class body, as in TypeScript: a subclass, another file and the module's own `.test.en` part, which does see the module's `private` top-level items (4.12), all get EN0308. `protected` members are visible in the class and its subclasses, and using one from outside is EN0308, so a test reaches one only from a subclass it declares. `readonly` fields may be assigned only by their initialiser or the constructor. Every class can be printed: one with no `fmt`, of its own or inherited, prints its name and its fields, `Header { len: 3, flags: 0 }` (4.4).
- **Construction.** A class with no constructor is created by naming its fields, `new User { name: "Ada", age: 36 }`, with the shorthand `new User { name }`; every named field must be visible where the literal is written. A class that declares a constructor is created only through it, `new User("Ada", 36)`, so its checks cannot be skipped, and naming its fields is EN0447. Where the expected type is a class with no constructor, an object literal is its named form: `const u: User = { name: "Ada", age: 36 };`. Literals nest: `new Team { owner: new User { name: "Ada" } }`. The defaults of the fields a named form leaves out belong to the class that declares them, as a parameter's default belongs to its function (4.14): each class's own module gives it one fill step for each set of left-out fields, which stores the defaults that class declares, for its own fields and for the fields it overrides (field overrides, below), and then runs its base's fill step for the rest, most derived first, as the implicit constructor of such a chain does (subclass construction, below). A named form, in its class's module or another, evaluates the values it names, left to right, then runs its class's fill step, which first writes the method-table pointer, and then writes only the fields it names, so a named value that exits early, by `?` or a panic, leaves no default to clean up. So no field default and no `private` field appears in another module's stored code, and editing a default leaves every importer's stored code as it is, running the new fill step, so a warm build prints the new value as a cold one does (4.12). Field initialisers run first, in declaration order; then the defaults of the parameters a call left out, and the parameter properties (below); then the constructor body, in which `this` is a partially initialised local tracked by init dataflow. Reading `this` as a whole, calling a method or returning before every field without a default is assigned is EN0610, an inherited one that the `super()` of a base chain with no constructor leaves unset included (subclass construction, below), and so is `this` in a field initialiser. A subclass sets its own fields before its base part is built (subclass construction, below).
- **Field defaults.** A field with no `= value` starts at its type's default, in the named form and in constructors alike: numbers `0`, `bool` `false`, `string` `""`, arrays `[]`, `T | null` `null`, raw pointers address 0. None of these allocates. Classes, enums, `Box`, `Result` and references have no default, so such a field must always be set: EN0433 (`` missing field `owner` ``). `new Counter()` means all defaults, and `new Team()` with a field that has no default is EN0433 (`` `new Team()` leaves `owner` unset ``, help `` use `new Team { owner: ... }` ``). The `super()` of a subclass's constructor runs the defaults of a base chain with no constructor, as `new Counter()` does, and leaves a base field with no default for that constructor to assign after it (subclass construction, below). A `private` field with no default cannot be set from outside, so its class needs a constructor (EN0448, at the class). `x?: T` on a field is shorthand for `x: T | null = null`, and a type that is already nullable gains no second `null`: `width?: i64 | null` means `width: i64 | null = null`, as on a parameter (4.14). That is decided on the type as written where `?` is written, and a type parameter is never already nullable there, so a generic body reads the same field type for every instance: with `public type Opt<T> = { v?: T };`, `Opt<i64 | null>` has a field `v` of type `(i64 | null) | null`, which is not the type `{ v?: i64 | null }` written out, and so does a class field `public v?: T` at `T := i64 | null`. `x?: T = v` is EN0227.
- **Parameter properties.** `public constructor(public x: T, private y: U)` declares and assigns fields. A constructor starts in one fixed order: its class's field initialisers, which use neither `this` nor a parameter; then the defaults of the parameters the call left out, in parameter order (4.14); then the parameter properties' assignments; then its written body. So a parameter property with a default stores the default when the call leaves it out: with `public constructor(public name: string = "anon", public nick?: string) {}` in `Animal`, `new Animal()` has `name` `anon` and `nick` `null`, and `new Animal("Rex")` has `Rex` and `null`. In a subclass all of these run before `super(...)`, so a default that reads `this` or calls a method is EN0610 there, as it is in any class while a field without a default is still unassigned. A reference field declared this way may say `readonly` before its type, `private src: readonly &Slice<u8>` (borrowing classes, below).
- **Inheritance.** `public class Dog extends Animal { ... }` extends one base class. Every class can be extended unless it is `final`, and extending a `final` class is EN0442. A call through a base reference always runs the object's own method, with no `virtual` word: with `` public override speak(): string { return `${this.name} barks`; } `` in `Dog` and `function introduce(a: &Animal): void { console.log(a.speak()); }`, `introduce(&rex)` prints `Rex barks` for `const rex = new Dog("Rex");`. That holds inside a base constructor too, as in Swift: while `new Dog("Rex")` runs `Animal`'s constructor, `this.speak()` and printing `this` there run `Dog`'s code, which finds `Dog`'s fields set, because a subclass sets them before `super(...)` (subclass construction, below). The one exception is a base class's destructor, which runs on an object that is no longer a `Dog`: before it runs, the object's method-table pointer is set to the base's table, so `this.speak()` and printing `this` there run `Animal`'s code (5.7). A method that replaces a base method says `override`; `override` on a member that replaces nothing is EN0443, and a replacing member without it is EN0444, for fields (below) as for methods. A `private` method is never replaced: subclasses cannot see it, so a subclass method of the same name is a new method, and a call to the `private` one never goes through the method table (5.4). A method compiled once per type, one with type parameters of its own, a by-value interface parameter or an object-type parameter (4.4, extra fields below), is never replaced either: it may be declared in any class, but it gets no method-table slot, since no single function could fill one, so every call to it is direct, with the body of the class that declares it, and, where a subclass can see it, an `override` of it, or a subclass method with its signature, is EN0460 at the subclass, `` `show` has its own type parameters, so it can't be overridden ``, with `help: give Dog's method another name`, while an `abstract` one is EN0460 at its declaration, since no subclass could implement it; a subclass method with the name of a `private` one is a new method, as above. A subclass method of the same name and another signature is an overload as usual (4.14). An override matches one overload exactly (4.14), and may return a reference into `this` or into whatever the base method's body returns into, so a call through a base reference locks the object as well as those arguments (5.4). `super(...)` in a constructor calls the base constructor, and `super.speak()` calls the base version. A `Dog` never fits in an `Animal` variable (EN0401; there is no slicing): it is referred to as `&Animal` or owned as `Box<Animal>` (C21), so a mixed list is `Box<Animal>[]`, and moving a whole `Animal` out of one that holds a `Dog` panics (`Box<T>` below). A class that can be extended carries a hidden method-table pointer, 4 bytes on `i386` and 8 on `x86_64`, and a class that extends one keeps it, `final` or not; a `final` class with no base carries none, so hardware structures are `final` classes with no base (7.6). In a per-class copy (4.4) or a generic instance (4.10) for a class that can be extended, a call to an interface or bound member goes through the method table too, so the object's own method runs there as well, except a member compiled once per type, which has no slot and is called directly, its one body being the object's own.
- **Field overrides.** A subclass may give a field that it inherits and can see a new default: with `protected sound: string = "...";` in `Animal`, `protected override sound: string = "woof";` in `Dog` names the same field, not a second one, so a `Dog` has one `sound`, in one slot and printed once, and its default replaces `Animal`'s, whose initialiser for `sound` does not run for a `Dog`. A `Dog` sets its fields first (subclass construction, below), so `Animal`'s constructor already sees `woof` there, where TypeScript would still see `...`. The type, `readonly` and visibility stay as the base declares them: a field that differs in any of them replaces nothing, so `override` on it is EN0443, as on a method that matches no overload (4.14), and a visible field of the same name without `override` is EN0444. A `private` base field is invisible to subclasses, so a subclass field of the same name is a new field, as for a `private` method. The new default follows the rules of a field initialiser, so `this` in it is EN0610, and an assignment by a base constructor, a parameter property included, runs later and wins, dropping the default it replaces as any assignment drops an initialised value (D3), also when the base declares the field with no default: with `protected owner: Person;` in an `Animal` whose constructor assigns it and `protected override owner: Person = new Person("nobody");` in `Dog`, `new Dog(new Person("Ada"))` drops `nobody` when `Animal`'s constructor stores `Ada`. The named form and a subclass with no constructor use the new default for a field that is left out.
- **Abstract classes.** `public abstract class Shape { public abstract area(): f64; ... }` cannot be created: `new Shape()` is EN0445. An abstract method has no body. A subclass that is not `abstract` and lacks one is EN0446 at the class, and implementing one needs `override`. A `super.m()` whose nearest declaration of `m` above the calling class is abstract is EN0457: `super.area()` in a direct subclass of `Shape` gives `` `Shape.area` is abstract, so it has no body to call ``, while in a subclass of a class that implements `area` it calls that implementation. A `move` method with a body in an `abstract` class can never run: every object of the class belongs to a subclass, where a call that reaches that body, through inheritance or `super`, is EN0458, and one in generic code or a per-class copy panics on entry (`Box<T>` below), so it is warning EN0459, `` `move` method of an abstract class can never run ``, with `` help: declare it `abstract` ``, while an `abstract move` method compiles.
- **Subclass construction.** If no class in the chain has a constructor, the named form lists base and subclass fields together, `new Square { color: "red", side: 2 }`, and passing arguments is EN0449. If a base has a constructor, a subclass with none reuses it: `new Dog("Rex")` sets `Dog`'s own fields to their defaults and then runs `Animal`'s, and naming fields is EN0447. If a subclass declares a constructor and no class above it does, that base chain has an implicit `public` constructor with no parameters, which runs the chain's field initialisers and type defaults as `new Counter()` does, an override's default in place of the one it replaces (field overrides, above); the subclass's constructor calls it as `super()`, by the exactly-once rule below, and `super(...)` with arguments is EN0449. Such a `super()` leaves a base field with no default unset, as TypeScript's does, and the subclass's constructor assigns it after `super()`, since before `super()` it may assign only its own fields (EN0610, below): the rule that every field without a default is assigned before `this` is read as a whole, a method is called, `this` is passed or the constructor returns, the closing brace included, covers such an inherited field too, EN0610, `` `owner` is not set ``, with `help: assign this.owner after super()`. So with `public class Shape { public color: string = "red"; public owner: Person; }`, which has no constructor, and `public class Circle extends Shape { public constructor(public r: i64, o: Person) { super(); this.owner = o; } }`, `const c = new Circle(2, new Person("Ada"));` makes `` console.log(`${c.color} shape of ${c.owner.name}`); `` print `red shape of Ada`, as TypeScript's program does, though with no `!` on `owner`, since the compiler proves the assignment; the same constructor without `this.owner = o;` is EN0610 at its closing brace, and with `this.owner = o;` before `super();` it is EN0610 there. This is sound because a base with no constructor runs none of its own code inside `super()`, and its initialisers cannot use `this`. Where a class below may override such a field with a default, the assignment after `super()` drops that default in the instances that store one, as a base constructor's assignment does (field overrides, above). A subclass field with no default means the subclass writes a constructor (EN0448, at the class). A subclass sets its own fields before its base part is built, as Swift does, so a base constructor that calls an overridden method finds them set: its field initialisers run first, then its constructor up to `super(...)`, which may run only once every own field without a default is assigned, and only then the base's field initialisers and constructor, level by level along the chain, most derived first. In a class with a base, every constructor runs `super(...)` exactly once on every path that returns, as Swift checks `super.init`: init dataflow tracks it as it tracks a field, so a `return` or the closing brace reached where it may not have run is EN0619, `` `super(name)` isn't called on every path before the constructor returns ``, labelled there, with a note naming the branch that skips it, as `` when `quiet` is true ``, and a `super(...)` reached where it may already have run is EN0619 too, `` `super(age)` may already have run here ``. A path that ends in a panic needs none, since `panic(...)` has type `never`, and loops need no rule of their own: in `while (i < n) { super(); i++; }` the back edge reaches `super()` where it may have run, and the path with no turn reaches the end where it has not, so both are reported. `super(...)` is a statement of the constructor's own body, never inside an arrow or a local function, and only in a class with a base: inside an arrow or a local function of a constructor it is EN0619 as well, while `super` in a class with no base, and `super(...)` in any function that is not a constructor, are EN0219, which phase 2 reports first. So `if (quiet) { super("anon"); } else { super(name); }` and `if (bad) { panic("no"); } super(name);` compile. Before `super(...)`, and wherever it may not have run yet, the constructor may compute from its parameters and locals, and it touches `this` only to assign its own fields: reading `this` or a base field, assigning a base field, calling a method or passing `this` there is EN0610, and so is a `super(...)` reached while an own field without a default is unassigned. With `public owner: Person;` in `Dog`, `public constructor(name: string, owner: Person) { super(name); this.owner = owner; }`, the order TypeScript requires, is EN0610 at `super(name)`, `` `this.owner` is not set when `super(name)` runs ``, with `` help: set `this.owner` before `super(name)`, because `Animal`'s constructor may call `Dog`'s methods `` and a fix-it that moves `this.owner = owner;` above `super(name);`: the reverse of TypeScript's TS17009, which rejects a field set before `super(...)` (G24).
- **Receivers (N7).** Inside a method `this` has type `&C`, and whether the method reads or changes the object is inferred from its body (section 5). `public move close(): void` consumes `this`, as Rust's `self` does: when it ends, everything in the object is disposed except what it returns, which moves to the caller, so returning a reference into the object is EN0710 (5.4), and using the object afterwards is EN0601. Consumption is never inferred, so moving `this` or a non-Copy field out of `this` in a method not marked `move`, or in a constructor, is EN0603. A returned reference is as changeable as what it comes from, `this` included, as in TypeScript: with `public book(id: i64): &Book`, `lib.book(1).title = "Dune";` changes a `let lib`, and the call borrows `lib` for writing (5.4). `readonly` before the return type keeps callers from changing it: `public count(): readonly &isize { return &this.n; }` lends a private count that only the class changes. `let` before the name says the method may change the object even where its body doesn't: an abstract method writes it as an interface member does (4.4), and so does an overridable hook whose overrides may change the object, `public let update(): void {}`; elsewhere what a body changes is inferred. `const` before the name promises that a body containing `unsafe` only reads (5.9). A `static` method has no receiver. At an expected type `C`, a non-Copy `this` is a move, legal only in a `move` method; `const me = this` copies the reference; `*this = v` writes the whole value; `this` is a keyword, never rebound. There are no getters: a class exposes values through methods, `s.total()`.
- **Destructor.** `public destructor() { ... }` has no parameters and no return type, and runs automatically at the end of the object's life (5.7); `dispose(x)` ends a value early. A class with a destructor, its own or one of any base class, cannot be `Copy` (EN0418), since a copy would run that destructor once for each copy: with `public class Region { private p: *u8; private n: usize; public destructor() { ... } }`, `public class Snapshot extends Region implements Copy {}` is EN0418 at `Snapshot`, `` `Region`'s destructor runs for every `Snapshot`, so copying one would run it twice ``, with `` help: remove `implements Copy`; to copy a `Snapshot`, write `clone()` ``. No field can be moved out of a class with a destructor (EN0607), and `f.destructor()` is EN0606.
- **Borrowing classes.** A class with a `&` field, or with a field whose type is or contains a borrowing tuple other than inside a borrowing-class field, is a borrowing class, and such a field is a reference field. The field must be `private` (EN0701), and the class follows reference rules (5.1). It lives only where a reference can: locals, parameters, return values and fields of another borrowing class, which a class holding one is too. An array, enum case or generic argument holding one is EN0701. Whether the class *writes through its reference fields* is inferred from every body that sees its `private` fields: its methods, `static` ones included, its constructors, parameter properties included, its destructor, and every arrow nested in one of these, at any depth. No other code sees them, tests included, so the answer is the same under `check` and `build` (12.4). It is one flag for all those fields: it does if one of those bodies writes through a reference read from a reference field, passes such a reference to a Write parameter, or returns it, or a part of it, as a writable reference or as a reference part of a returned tuple; returning a borrowing value by value does not count, because writes through that value go through its own class's methods. The flag is also set when the base class's flag is set, because a base's bodies write through the base's fields of a subclass value as of any other: with a `Base` whose `step` pushes through its `dst` and a `public final class Sub extends Base` that adds no body, `Sub` writes through its reference fields too, so a result that `Base`'s code reads through a `&Sub`'s fields holds the object, a reference that it stores into a `Sub` is borrowed for writing, and `implements Copy` on `Sub` is EN0418 (`TESTING.md` `FV-02-base-flag`, `S2-08-copy`). So a constructor that pushes through the field it has just set, `this.v = v; this.v.push(0);`, sets the flag, and `new Grower(&data)` then borrows `data` for writing (N3 (e)), EN0706 while a reference into `data` is still used and EN0608 over a `const data`, and so does an arrow in a method that writes through `this.v`. A reference field of tuple type sets the flag when any of its reference parts, at any depth, a nullable payload included, is not declared `readonly` (below), because through `this` its parts are behind a reference, as for any tuple reached through one (N3 (e)). A reference field declared `readonly &`, `private src: readonly &Slice<u8>;`, never sets it: the class only reads through that field, as through Rust's `src: &'a [u8]`. A store into such a field never borrows for writing, even when another field sets the flag (N3 (e)): in a `Copier` with `private src: readonly &Slice<u8>;` and a `private dst: &Slice<u8>;` that `step` writes through, the constructor's `src` is Read, so `new Copier(&data, &buf)` over a `const data` compiles. Writing through a `readonly &` field, or through anything reached from it, is EN0616, `` `src` is declared `readonly &Slice<u8>` ``, and so is passing it to a parameter that writes (EN0614 for a method that changes it), while what a method returns from it is read-only, as a `readonly` result is: by its marks (4.11), and by N6's own reason for a result reached through a `readonly &` field, whatever marks its flows carry (5.4). The loans stored into its fields declared `readonly &`, never into a tuple part, are the object's read set, which it keeps apart from its other loans (5.1), so a result that reaches `this` only through its `readonly &` fields holds, for `this`, the read set and never the object, whatever the flag and whatever its other sources, as Rust's `fn peek(&self) -> &'a [u8]` does: with a `private pos: isize;`, a `step()` that runs `this.dst[this.pos] = this.src[this.pos]; this.pos += 1;` and `public peek(): readonly &Slice<u8> { return this.src.slice(this.pos, this.pos + 1); }`, `let c = new Copier(&table, &out);` over `const table: u8[3] = [7, 8, 9];` and `let out: u8[3] = [0, 0, 0];` runs `const a = c.peek(); c.step(); c.step(); console.log(a, c.peek());`, which prints `[7] [9]`, and `console.log(table, out);` then prints `[7, 8, 9] [7, 8, 0]`. A result reached from any other reference field still holds the object while the flag is set (5.1), so a `public last(): readonly &Slice<u8>` that returns `this.dst.slice(0, 1)`, kept across `c.step()`, is EN0706. So that the read set stays sound, a `readonly &` field holds only loans that nothing in the object writes through: in a class that writes through its reference fields, storing into it a reference reached from another reference field of the same object that is not `readonly &`, as `this.src = this.dst.slice(0, 1);` in this `Copier`, is EN0616, `` `src` is declared `readonly &`, so it can't hold a reference from `dst` ``, with `` help: store a reference from a parameter, or from another `readonly &` field ``, as Rust rejects `self.src = &self.dst[..]` (`lifetime may not live long enough`), while a store from a parameter or from another `readonly &` field compiles. A class whose flag is off writes through none of its reference fields, so there such a store compiles, as Rust accepts `self.src = &self.other[0..1]` from a `&'a [u8]` field. A reference taken from another object's field brings the loan on that object with it when its class writes through its reference fields (R2, 5.1), so `public alias(other: &Copier): void { this.src = other.dst; }` compiles and keeps `other` borrowed while `this` holds what it stored: after `c.alias(&b);` on a new `c`, with `b` built over `let out2: u8[3] = [5, 6, 0];`, `console.log(c.peek());` prints `[5]`, while a `b.step();` between the two is EN0706, as Rust takes that store with `other: &'r Copier<'_, '_>` and then rejects `b.step()` (E0502). Inside a tuple field's type, `readonly` may stand before a reference part, `private t: [readonly &i64[], i32];`, and a reference read from that part is marked the same way, so writing through it is EN0616 naming the field. Such a tuple part declared `readonly` is no `readonly &` field for the read set, until a mark per part is added: a reference read through it holds the object's main set, never its read set, and a store into a tuple field never joins the read set, whatever its parts say, so its loans join the main set, exclusive ones in a class whose flag is set (N3 (e)). A reference to a tuple field, or to a part of one at any depth, is read-only as a whole, and so is any result reached from it, when the place it points at contains, at any depth, a nullable payload included, a reference part declared `readonly`: `&this.t` is, and with `private t: [&i64[], [readonly &i64[], i32]];` so are `&this.t` and `&this.t[1]`, while a reference to a sub-tuple that contains no such part is not: with `public tup(): &[&i64[], i32] { return &this.t; }` in a `Pad`, `p.tup()[0].push(4)` is EN0614 and `p.tup()[1] = 5` is EN0616, each naming `t`, while the class itself still writes `this.t[1] = 5` directly. Nothing then writes through a part declared `readonly`, so a tuple field whose reference parts at every depth, a nullable payload included, are all declared so does not set the flag: its constructor's parameter only reads, and `new Pad(&k)` over a `const k` compiles, while a tuple field with any plain reference part, nested or not, still sets it, as `private t: [readonly &i64[], [&i64[], i32]];` does. `readonly` before a whole tuple type is EN0214. This mark on the type is not the `readonly` modifier before the field's name, which only forbids reassigning the field after construction; `private readonly src: readonly &Slice<u8>;` has both. In a body containing `unsafe` or `asm`, an `unsafe function` or an `@naked` function, a reference read from a reference field counts as written where it is read, unless the method is marked `const`, or the field is declared `readonly &` or the reference is read from a tuple part declared `readonly`, which promises the same for that field or part (5.9). The flag is stored with the class's contracts (5.3) and decides how a reference stored into the class is borrowed (N3 (e)). When what sets the flag is only a method that returns a part of a reference field as a writable result, as a byte lexer's `public next(): &Slice<u8> | null` that returns `this.src.slice(start, this.pos)` does, each EN0608, EN0706 or EN0707 that the set flag causes, at `new ByteLexer(&bytes)` over a `const` buffer or at a second token kept while the first is used, adds the note `` `ByteLexer` counts as writing through `src`, because `next` returns a part of it as a writable reference ``, `` help: if `ByteLexer` only reads `src`, declare `private src: readonly &Slice<u8>;` `` and `` help: or, if callers only read what `next` returns, write `public next(): readonly &Slice<u8> | null` ``. Either one leaves the flag off, so the constructor's `src` is only read and two tokens can be kept, while the `&string` `Lexer` of 5.1 needs neither, because a part of a string is read-only already. A copy of a class whose flag is set would be a second writer through its reference fields, so `implements Copy` on one is EN0418, `` `Cursor` writes through its reference fields, so copying it would make two writers ``, with `` help: if `Cursor` only reads through them, write `readonly` before their types or before the return types that hand them out, or remove `implements Copy` ``. Type checking still treats such a class as Copy (N1); this verdict waits for the flags, in phase 3.
- **`enum E<T>`**: nominal tagged sum. A case is a name, `Empty`, or a name with named fields, `Circle { radius: f64 }`; there are no positional cases. A value is created without `new`: `Shape.Circle { radius: 2.5 }`, `Shape.Empty`, and left-out fields take the field defaults above. Payload-free enums are Copy and may give their cases integer values (`Red = 1`, consecutive defaults starting at 0). A case without fields, in any enum, may instead carry a text (`NotANumber = "not a number"`); an enum's `=` values are all integers or all texts, and a mix is EN0456. A text enum keeps position tags with its texts in a read-only table, has no `as int`, and `AgeError.Negative == "negative age"` is EN0401. Enums may have methods after a `;`, each with its accessor. Cases are always qualified, `E.V`, in expressions and in `match` arms; only `Ok` and `Err` are bare. Every enum is an error type (4.4), and a case of an enum with no written `fmt` prints its text, or else its qualified name, bare for `Result`'s `Ok` and `Err` (4.4), followed by its fields, if it has any: `Shape.Empty` prints `Shape.Empty`, `Shape.Circle { radius: 2.5 }` prints `Shape.Circle { radius: 2.5 }`, and `AgeError.NotANumber` prints `not a number`, while an enum that writes `fmt` prints what its `fmt` writes, for every case (4.4). `Result<T, E>` is the prelude enum with cases `Ok { value: T }` and `Err { error: E }`, built with `Ok(v)`, `Ok()` and `Err(e)` (section 6), and `Result<T>` means `Result<T, Failure>`.
- **String-literal unions.** `private type Direction = "left" | "right";` is a payload-free enum written as a type alias. Its values are string literals where the type is known (`turn("left")`), it is stored as a small integer, `console.log(d)` prints `left`, and a `match` that lists every value needs no `default`. A literal not in the union is EN0401 (`` `"lft"` is not a `Direction` ``, help `` did you mean `"left"`? ``). A literal union outside a type alias, or mixed with other types, is EN0216. A run-time `string` needs a check, and a `match` with a `default` arm gives `Direction | null`:
  ```ts
  const d: Direction | null = match (input) {
    "left" => "left",
    "right" => "right",
    default => null,
  };
  ```
- **Anonymous object types.** An object literal with no expected class type has an anonymous object type: `const p = { name: "Ada", age: 36 };` has type `{ name: string, age: int }`. Such a type can be written anywhere a type can (`function show(x: &{ name: string, age: int }): void`) and named by an alias, `public type Person = { name: string, age: int };`. Its fields are separated by commas, as in the value, and their order never matters, so `{ name, age }` and `{ age, name }` are one type. These types are structural; classes stay nominal. A value is copied when every field is Copy and moved otherwise: `const a = { x: 1, y: 2 }; let b = a; b.x = 9; console.log(a, b);` prints `{ x: 1, y: 2 } { x: 9, y: 2 }`, and `const p = { name: "Ada", age: 36 }; const q = p; console.log(p);` is EN0601 (fix with `p.clone()`). A field may be optional, `subtitle?: string`, of type `string | null`, as is `subtitle?: string | null`: a literal written at that type may leave it out, and it is then `null`, while a variable that lacks the field is EN0433 (`` missing `subtitle` ``, help `` add `subtitle: null` ``). An anonymous object type or a tuple cannot get methods: `extend` on one is EN0439 (`extend` is library-only, so user code gets EN0806, with the help `make it a class`). An anonymous object never becomes a class: `const v: User = p;` is EN0401, while a literal written at the class type is that class's named form (`const w: User = { name: "Ada", age: 36 };`). Layout is in section 11.
- **Extra fields.** A value with more fields than expected, an anonymous object or a class instance by its public fields, is accepted only where the compiler keeps the real shape: a function parameter, by value or by reference, and a reference such as `&{ name: string }` (C20). The compiler builds one copy of such a function per shape passed to it, like generics, and the copy reads a class at the class's own offsets; a by-value parameter keeps all the fields and drops them when it is dropped. So such a parameter stands for any value type with those fields, like a type parameter bounded by the shape (4.10): it may be passed on by value to another such parameter or to a generic `T`, or behind a reference, and `dispose(x)` drops the whole `User`, but moving it whole into storage whose size its declared type fixes (a result, a field, a `Box`, an array element) is EN0440 in the body, `` `x` may have more fields than `{ name: string }` ``, with `` help: build the smaller object: `{ name: x.name }` ``. Each such parameter stands for a type of its own, as each interface parameter does (4.4), so with two by-value parameters `let a: { name: string }` and `b: { name: string }`, `a = b` is EN0401, `` `b` may hold another class than `a` ``. With `` function greet(x: &{ name: string }): void { console.log(`hi ${x.name}`); } ``, `greet(&p)` prints `hi Ada` for `p` above and for `new User { name: "Ada", age: 36 }` alike, so a function can accept any class with the fields it needs, without an interface. Private fields never count: a `User` given to a parameter `&{ secret: int }` is EN0401 (`` `User` has no public field `secret` ``, with `` note: `secret` is private to `User` ``). Where the declared type fixes the storage, in an annotated variable, a function result, a class field or an array element, extra fields are EN0440 (`` `p` has a field `age` that `{ name: string }` does not have ``, helps `` build the smaller object: `{ name: p.name }` `` and `` or keep a reference: `const q = &p;` ``). A field written in the literal itself that the expected type lacks is EN0434: `greet(&{ name: "Bo", age: 1 })` points at `age` (`` `greet` doesn't use the field `age`, so it would be thrown away ``).
- **Tuples.** `[int, int]` is a tuple type, and parts may differ in type (`[int, string]`). A tuple value is a bracket literal where a tuple type is expected: `function minMax(xs: &Slice<int>): [int, int] { ... return [min, max]; }`, then `const t = minMax(&[3, 1, 4, 1, 5]); console.log(t[0], t[1]);` prints `1 5`, and `console.log(t)` prints `[1, 5]`. Access is by a constant index; `t[2]` on a pair is EN0452 (`` `[int, int]` has no element 2 ``), and so is `t[i]` with an index that is not a constant, because positions can differ in type. A tuple is copied when every part is Copy and moved otherwise, like an anonymous object, and destructures as `const [lo, hi] = minMax(&xs);`. A tuple with a reference part is a borrowing tuple and follows the rules for borrowing classes. A tuple has no methods to infer from, so one reached through a reference counts as writing through its reference parts (N3 (e)), while for a tuple held directly in a local, parameter or temporary, write-liveness follows each reference part on its own (N3), which gives a by-value tuple parameter one permission per part (5.3), until `&` of it is taken into a slot that writes, which makes every reference part write-live there (N3). A copy of a borrowing tuple, or of a nullable one, takes a new loan per reference part (O7), and a field whose type is a borrowing tuple is a reference field of its class (borrowing classes, above).
- **Recursion** needs `Box`: `public class Node { public next: Node | null; }` is EN0408 with a fix-it to `Box<Node> | null`.
- **`type A<T> = B;`** is a transparent alias; aliases cannot be recursive.
- **`Box<T>`**, in `alloc`: `new Box(v)` allocates; `b.unbox()` consumes and returns `T`; `*b` and auto-deref on `.` give the place. Moves out of `*b` are EN0605: use `unbox`. A `Box<A>` of a class that can be extended may hold a subclass (C21), so freeing it uses the size and alignment in the object's method table (section 11), and a call through it needs no check: with `const pet: Box<Animal> = new Box(new Dog("Rex"));`, `pet.speak()` prints `Rex barks`. Moving, copying or writing a whole `A` is different, because the object may be larger than `A`: every copy or move of a whole `A` reached through a `Box<A>`, an `a: &A` or `this`, and every whole write through one, first compares the object's method table with `A`'s and panics if they differ (9.1). The check follows the event, whatever its syntax: `unbox()`; a copy out of a Copy `A`, by C05 or C08, as an explicit `*a` or `*pet`, or as a ternary or `??` arm that reads one; `*a = v`; `mem.replace`, `mem.swap` and `clone`; and, in generic code and per-class copies (4.4), the entry to a `move` method of `A`, which takes the whole object as its `this` and disposes of what it does not move out as an `A` (5.7 D4). Elsewhere that entry is decided at compile time: a call of a `move` method on a receiver whose static type is a class `D`, not a type parameter, that reaches a body declared in a proper base of `D`, which `D` inherits without overriding it, `this.m()` in a `move` method included, is EN0458, and so is every `super.m()` whose target is a `move` method. With `public move into(): Animal { return this; }` in `Animal`, `rex.into()` on a `const rex = new Dog("Rex");` whose class does not override `into` is EN0458, `` `move` method not declared in the receiver's class ``, labelled `` `Dog` inherits `into` from `Animal` ``, with `` help: override `into` in `Dog` ``, because that body would dispose of a `Dog` as an `Animal`. In a `Builder` with `private parts: string[];` and `public move build(): string[] { return this.parts; }`, an override in `HtmlBuilder` that returns `super.build()` is EN0458 too, with `` help: move the state out with a helper the base shares, `protected takeParts(): string[] { return mem.replace(&this.parts, []); }` ``: such a helper, a `protected` method that is not `move` and takes the state out with `mem.replace`, is how classes share consuming logic, each calling it from its own `move` method, so with `public override move build(): string[] { return this.takeParts(); }` in `HtmlBuilder`, `console.log(b.build());` prints `['a']` after `b.add("a");`. Generic code keeps the run-time check, since an instance adds no errors (4.10): with `function f<T extends Animal>(x: T): Animal { return x.into(); }`, `f(new Dog("Rex"))` panics on entry to `into`, `` `into` expected an `Animal`, but the reference points at a `Dog` ``, and `f(new Animal("Generic"))` returns its `Animal`. A per-class copy keeps it too, since the receiver's static type there is an interface, and the copy for a class that can be extended calls through the method table: with `public interface Buildable { move build(): string[]; }` and `function consume(b: Buildable): string[] { return b.build(); }`, `consume(new HtmlBuilder())` over a `HtmlBuilder` that inherits `build` panics on entry, `` `build` expected a `Builder`, but the reference points at a `HtmlBuilder` ``. So `pet.unbox()` panics `` `unbox` expected an `Animal`, but the box holds a `Dog` ``, while a box that holds an exact `Animal` unboxes it. A `final` class needs no check, because its boxes and references hold exactly that class. With EN0458 and, in generic code and per-class copies, that check, `this` in a `move` method of `A` is exactly an `A`, so moving it whole needs no other check, and what the method leaves is disposed of in full, with no subclass destructor or field skipped.
- **`Slice<T>`**, in `core`: a view of consecutive elements of an array, a pointer and a length (section 11), like TypeScript's `Uint8Array` beside `number[]`. It appears only behind `&`: `xs.slice(a, b)` makes one, by JavaScript's index rule, so it never panics (8.2), `&T[N]` and a whole `&T[]` convert to one (C18), and `unsafe` code makes one from a pointer and a length with `Slice<T>.fromRaw(p, n)` (8.2). Its elements can be read and set, which changes the array it views, and its length never changes: it has no `push` or other member that grows or shrinks it (8.2). So a function that only reads or sets elements takes `&Slice<T>` and accepts any array: with `function fill(part: &Slice<u8>, v: u8): void`, `fill(&sector, 7)` for `let sector: u8[8]`, `fill(&bytes, 7)` for a `let bytes: u8[]` and `fill(sector.slice(4, 8), 7)` all compile. A function that pushes takes `&T[]`, and only a whole growable array fits a `&T[]`: with `function checksum(data: &u8[]): u32`, `checksum(&sector)` is EN0401, `a fixed array can't grow`, with `` help: if `checksum` only reads or sets elements, take `data: &Slice<u8>`; to let it grow, make `sector` a `u8[]` ``, and a part where a `&T[]` is expected is EN0401, `a part of an array can't grow`, with `help: pass the whole array: addOne(&list)` when the part is a `slice` call on a whole array, and otherwise with a help that names both parameter types (8.3). `Slice<T>` without `&` in front, as a variable, field, element or result, or as a type argument anywhere but for a type parameter that stands for a view (below), is EN0401, `` `Slice<u8>` is a view, so it exists only behind `&` ``, with `` help: write `&Slice<u8>`, or `u8[]` for an array of its own ``. A type parameter may stand for a view where its function uses it only behind `&` (4.10), as Rust's `?Sized` allows, but inferred from the body: with `public function show<T>(x: &T): void { console.log(x); }`, the form G04's help gives, and `const sector: u8[4] = [7, 7, 7, 7];`, `show(&sector)` prints `[7, 7, 7, 7]` and `show(sector.slice(0, 2))` prints `[7, 7]`. Where the body uses `T` by value, binding a view to it is EN0401, `` `T` can't stand for the view `Slice<u8>` ``, with a label at that use and `` help: add `show<T>(x: &Slice<T>)` `` (4.10).
- **Member lookup** is one rule, for `.` and `?.`. Strip one `&` to get `U`. Look up on `U`: its own members, the members it inherits from base classes and `extend` members together. If `U` is `Box<V>` and that misses, repeat on `V`. If `U` is a narrowed nullable, try the payload first and then nullable members; a member found on the nullable type takes its receiver at that type, which 4.8 records. An unnarrowed nullable has only nullable members, and a miss is EN0303 with a `?.` or narrowing fix-it. `?.` looks up on the payload by this same rule and never short-circuits: `a?.b.c` is EN0303 with a `?.c` fix-it, and `a?.b?.c` is legal. A `destructor` is never found (4.4). A bare `.length` is EN0441: `length()` is a method.

### 4.4 Interfaces

Structural. A type `C` satisfies `interface I` when, after substituting `Self`, lookup on `C` itself finds, for every member of `I`, a member meeting all of these. Own, inherited and `extend` members count; auto-deref never contributes a member, so `Box<C>` does not satisfy what `C` does. A bound that names a class is no interface: it is met by name, by that class and its subclasses (4.10).

- It is public. A `private` or `protected` member never satisfies an interface.
- It has the same unsafety: a safe interface member needs a safe method, and an `unsafe` one needs an `unsafe` method.
- It has no `@requires`.
- It is a method.
- It has equal type parameters and bounds, equal parameter types and an equal return type.

Whether a type parameter may stand for a view (4.10) is not part of this: a member of an interface has no body, so none of its type parameters may stand for one, whatever the classes that satisfy it do, and a call through the interface binds no view to them. A member keeps the fact that a type parameter may stand for `string` (4.10), and the member found must meet one more clause, which waits until every body's facts are known: each of its type parameters may stand for `string` wherever the interface member's corresponding type parameter may. Satisfaction is one relation, checked wherever a class is used as an interface, so this clause runs at every such site: an `implements` entry, a C22 conversion, an argument to a non-null `&I` or by-value `I` parameter, which makes a per-class copy, and a bound `T extends I` met by a written or inferred type argument, EN0419's site; and the member it checks is the one lookup finds, own, inherited or `extend`. Breaking it is EN0401, `` a `&string` can't become a `&Measured`, because it may be a part of a string ``, labelled at the conversion or call in the member's body that loses the fact, with `` note: `Keeper` is used as a `Sizer` here `` at the satisfaction site and `` note: `Sizer.size` lets `T` stand for `string` ``, once per member and interface, however many sites there are. With `public interface Dumper { dump<T>(x: &T): void; }` and `private function dumpWith(d: &Dumper, v: &Slice<u8>): void { d.dump(v); }`, the call `d.dump(v)` is EN0401, `` `T` can't stand for the view `Slice<u8>` ``, with `` note: `Dumper.dump` has no body, so its `T` may be used by value ``, even when every class that implements `Dumper` uses `T` only behind `&`.

These are checked in phase 2, and type checking reads no permissions (N1). Phase 3 then compares contracts (section 5, N10): what the member does with its references must fit what the interface declares, or the class gets EN0615. It does so for every satisfaction recorded above, each class, interface and member, not only for classes with an `implements` clause, so a class passed to a `&Sizer` parameter whose `size` writes `this`, where `Sizer.size` has no `let`, is EN0615 at the class. Interface members carry no accessor, since they are always public, and declare their contract with marks. An unmarked member reads every reference and `this`, and a reference it returns is as changeable as the object, as in TypeScript, unless the return type says `readonly`. `let` before the member name means it may change the object; `let` before a reference parameter means it may change that argument; `move` before the name means it consumes `this`. A member fits if it writes `this` and each reference parameter only where the interface says `let`, returns a writable reference unless the interface's result is `readonly`, returns from parameters within the interface's sources (the signature defaults of 5.4, where a method's result comes from `this`; a `return` outside them is EN0714), stores no parameter into a borrowing value, because an interface member declares no stores (5.4), and matches `move` exactly. So one name serves reading and writing, as in `public interface Shelf { book(id: i64): &Book; }`. With `function show(s: &Shelf): void { console.log(s.book(1).title); }` and `function rename(s: &Shelf): void { s.book(1).title = "Dune"; }`, `rename(&lib)` changes a `let lib` and `show(&fixed)` reads a `const fixed`, while `rename(&fixed)` is EN0608, `` `rename` can change `s`, but `fixed` is `const` ``, with `` help: declare it `let fixed = new Library();` ``, because writing through the result makes `rename` write its parameter (N3 (d)). A member whose result callers must not change says so: a reader that moves forward and returns parts of its text is declared `let next(): readonly &string | null;`, and writing through a token it returns is EN0616 (5.4). Its result comes from `this`, so a token holds the reader while it is used: with `t: &TokenReader`, `const a = t.next(); const b = t.next(); console.log(a, b);` is EN0707, with `help: keep a copy: const a = t.next()?.toString();`, and a borrowing reader, which could keep both, never reaches an interface (EN0701, below), while the class's own `next`, called on a local of that class, may keep both when the class only reads through its reference fields (5.1). Every other position with no body declares its contract with the same marks and defaults: an abstract method exactly as an interface member, and an `fn` type or a closure parameter type with `let` on reference parameters only, an `fn` type's returned reference being writable unless it says `readonly` or is a `&string`, a `&string | null` or a tuple with a `&string` part that may come from a `&string` or `&string | null` parameter not marked `let`, which may be a part of a string (4.1, 5.4); a row written with a type parameter is computed before substitution (4.10).

Implementing classes write no `let` or `readonly` marks: what their bodies change and return is inferred and checked against the interface. They still write `move` on a consuming method, and `const` where a body containing `unsafe` implements a member the interface declares read-only (5.9). A body that writes where the interface has no `let` is EN0615 at its first write of the object (G18): `` `read` changes the object, but `Reader` declares that it doesn't ``, with `` help: if implementations may change the object, write `let read(let buf: &Slice<u8>): usize;` in `Reader` ``; a `let` on such a method declares the same change and is EN0615 as well. A body whose result is read-only, such as a part of a string, where the interface's result has no `readonly` is EN0615 too: `` `Words.next` returns a read-only reference, but `TokenReader` declares a writable one ``, with `` help: if callers only read it, write `let next(): readonly &string | null;` in `TokenReader` ``.

This definition is what makes "checked once generically" true: a member the bound promises behaves, for borrowing and safety, exactly as the bound said. The same contract check applies when a method overrides a base method, whose contract is the join of its body and its marks, with result sources from the base body plus `this`, and stores from the base body, with their bits (5.4), and when a function coerces to an `fn` type (4.5).

`implements I` is an assertion checked at the class, giving a better diagnostic (EN0416) at the declaration rather than at use, which is EN0419. Both check the shape; the contract part is EN0615 in phase 3, or EN0714 for result sources (5.4).

**Fields-only interfaces.** An interface with only fields is a named object type: `public interface Point { x: f64; y: f64; }` means exactly `public type Point = { x: f64, y: f64 };`, so `const p: Point = { x: 1.0, y: 2.0 };` compiles and `Point` follows the rules for anonymous object types in 4.3. Its fields end with `;` (a comma is EN0100 with a fix-it) and may be optional (`subtitle?: string`). `implements Point` on a class checks its public fields. Mixing fields and methods is EN0417, whose fix-it turns the field into a method `name(): &T`. Adding the first method to a fields-only interface makes it an interface, and a use that is no longer valid is EN0401 (`` `Point` now has a method, so it is an interface, not an object type ``, help `make it a class`). An empty interface is an interface, satisfied by anything.

**Interfaces as types.** `function introduce(s: &Speaker): void { console.log(s.speak()); }` compiles one copy per class passed, as for anonymous object types, and a by-value parameter `s: Speaker` is accepted the same way (C22). A copy for a `final` class costs nothing at run time; in the copy for a class that can be extended, `s.speak()` goes through the method table, so a subclass's override runs (4.3). Only a value type becomes an interface value, as a parameter, behind an `&I` or in a `Box`: an interface declares no loans and no stores, so a borrowing class there is EN0701, `` a `Speaker` can't hold a `View`, because `View` holds a reference ``. A `&string`, whole, a part, a literal or a parameter, never becomes an `&I`, because it may be a part of a string, and an `&I` has room for an address and a table but not for a part's length, as Rust's `&str` never becomes a `&dyn`: with `public interface Measured { length(): isize; }` and `let s = "hello".toString();`, `const m: &Measured = s.slice(1, 3);` and `const w: &Measured = &s;` are each EN0401, `` a `&string` can't become a `&Measured`, because it may be a part of a string ``, with `help: take <T extends Measured>(m: &T)` and `help: or keep a copy: s.slice(1, 3).toString()`, and so is passing either to a `keep(m: &Measured)`, or to a generic function whose body itself converts its `&T` to an `&I` (4.10), while `keepT<T extends Measured>(m: &T): &T` takes the part, so `console.log(keepT(s.slice(1, 3)).length());` prints `2`, and `Box<string>` to `Box<Measured>` and a by-value `string` at a by-value `Measured` parameter still convert, since each holds a whole descriptor (C22). `Box<Speaker>[]` holds a mixed list: the method-table pointer travels beside the object inside the box, so classes, `final` ones included, need no hidden pointer for this. `const all: Box<Speaker>[] = [new Box(new Dog {}), new Box(new Robot {})]; for (const s of &all) { console.log(s.speak()); }` prints `woof` and `beep`. An `&Speaker` taken out of a `Box<Speaker>`, by C04 or as `&*b`, has no known class, so it is two words, the object and its method table, as the box carries them (section 11). An `&Speaker` may also stand anywhere else a reference may (4.1), and has that two-word form there too: as a result, `public function pick(a: &Speaker, b: &Speaker, first: bool): &Speaker { return first ? a : b; }`, as a `private` field of a borrowing class, `private s: &Speaker;` in a `Greeter`, as a tuple part and as `&Speaker | null`. A per-class copy that returns, stores or wraps its `&Speaker` parameter, in a result, a field, a tuple part or a nullable, attaches its class's table for `Speaker` there, read through the object's hidden pointer when the class can be extended, and so does a conversion by C22 anywhere but at a per-class copy's own `&I` parameter. An `&Speaker | null` is always two words, a parameter included, so only an `&I` parameter that is not nullable, and a by-value `I` parameter, get per-class copies, C22 followed by C07 attaches the table at every site, and `null` there is 0 in both words. So with `const d = new Dog {}; const r = new Robot {};`, `console.log(pick(&d, &r, true).speak(), pick(&d, &r, false).speak());` prints `woof beep`, and a `Greeter` built over `&r` whose `hello()` returns `` `hello, ${this.s.speak()}` `` prints `hello, beep`, and with `` function greet(s: &Speaker | null): void { if (s == null) { console.log("nobody"); } else { console.log(s.speak()); } } ``, `greet(&d); greet(null);` prints `woof` then `nobody`. Every function with an interface parameter gets one extra copy for two-word `&I` arguments, made only when one reaches it, in which every member call on an interface parameter goes through the method table, and an argument whose class is known travels with its class's table for the interface, which for a class that can be extended is read through the object's hidden pointer, since the object may be a subclass (section 11). So `for (const s of &all) { introduce(s); }` prints `woof` then `beep`, while `introduce(&rex)` for `const rex = new Dog {};` still reaches the copy for `Dog`. A call whose callee is chosen at run time, through a method table, an interface's table, an `fn` value or a closure, can name no per-class copy, so it passes each `&I` and `&I | null` argument as two words, and a method-table slot, an entry of an interface's table and a function converted to an `fn` value or a closure parameter all name that extra copy; the per-class copies serve direct calls only. With `` public hear(s: &Speaker): string { return `animal hears ${s.speak()}`; } `` in `Animal` and an override in `Dog` that returns `` `dog hears ${s.speak()}` ``, `pet.hear(&r)` through `const pet: Box<Animal> = new Box(new Dog {});` prints `dog hears beep`, and with `private function describe(s: &Speaker): string { return s.speak(); }`, `const f: fn(s: &Speaker) => string = describe;` makes `f(&r)` print `beep`. A `&Self` result of a member called through a table is paired with the receiver's table, so it is a two-word `&I` as the receiver is. A method with type parameters of its own, a by-value interface parameter or an object-type parameter is compiled once per type, so no single function could fill a method-table slot or an entry of an interface's table for it: it has no slot, is never overridden, and every call to it is direct (4.3, 5.4), and an interface with such a member follows the rule below for a member that takes or returns `Self` by value. A function with a by-value interface parameter has no single copy either, so as an `fn` value or a closure parameter it is EN1006 (4.5). `b.unbox()` on a `Box<Speaker>` is EN1006, even where a by-value `s: Speaker` parameter would take it: its result is a `Speaker` by value whose class, and so its size, is not known. In a body, each interface-typed parameter, and each two-word `&I`, stands for a class of its own that the body does not know, and `Self` in a member called on it means that class. So `function same(a: &Eq, b: &Eq): bool { return a.equals(b); }` is EN0401 at `b`, `` `b` may hold another class than `a` ``, with `help: use one type for both: same<T extends Eq>(a: &T, b: &T)`. That holds by value too. A parameter behind `&` still converts to `&I` by C22 at any coercion site, in the two-word form, so `pick` above and `let t: &Speaker = a; t = b;` compile, while a by-value one converts only as a whole argument to a by-value `I` parameter, which reaches the copy for its own class. So with `` private function swapIn(let s: Speaker, o: Speaker): void { s = o; console.log(s.speak()); } ``, `s = o` is EN0401, `` `o` may hold another class than `s` ``, with `help: use one type for both: swapIn<T extends Speaker>(let s: T, o: T)`. A by-value `I` parameter takes a whole argument whose type is one class, or the class of one interface parameter, and C22 never converts a ternary branch, a `match` arm or a `??` operand to a by-value `I`: with `private function relay(x: Speaker): void { console.log(x.speak()); }`, `relay(c ? new Dog {} : new Robot {})` is EN1006, with `` note: this `Speaker` may be a `Dog` or a `Robot`, so its class isn't known `` and `help: call relay in each branch`, and so is `relay(c ? s : o)` where `s` and `o` are by-value `Speaker` parameters, while `relay(c ? new Dog {} : new Dog {})` compiles, since its argument is one `Dog`. A member that takes or returns `Self` by value, as `clone(): Self` does, cannot run where the class is not known, and a member compiled once per type, as the `dump<T>(x: &T)` of `Dumper` above is, has no entry that a table could hold, so a `Box<I>` of an interface with either is EN1006, as `Box<Dumper>` is, and so is an `&I` of it wherever it would need the two-word form: anywhere but at an `&I` parameter that is not nullable, and also as an argument of a call whose callee is chosen at run time and as a parameter of a function converted to an `fn` value or a closure parameter (above), while a parameter of such an `I` still reaches the copy for each class passed in a direct call. `Self` is not a keyword (section 2): inside an interface, the prelude's or a user's, it names the implementing type. Bounds such as `<T extends Speaker>` still work. An interface type by value in a variable, function result, class field or array element (`Speaker[]`, `const s: Speaker`) is EN1006, with helps `use &Speaker` and `use Box<Speaker>`, because `new` never allocates and a variable of a type holds exactly that type.

Prelude interfaces:

| Interface | Members | Notes |
|---|---|---|
| `Copy` | none | **Nominal.** `implements Copy` requires every field Copy, inherited ones included, no destructor, in the class or in any base class, and, on a borrowing class, a flag that is off (EN0418, 4.3). Copy is never inherited: only a class that declares `implements Copy` is Copy, so a subclass of a Copy class that declares none is not, and `T extends Copy` refuses it (EN0419). Tuples and anonymous object types are Copy when every part is |
| `Error` | none of its own; it extends `Display` | **Nominal.** Enums and `Failure`, the prelude class that holds a text (8.1), are errors with no `implements`; a class is one only with `implements Error`. `string`, numbers, other classes and `Box<E>` are not: EN0454 (`` `string` is not an error type ``, `` help: return `Result<i64>` and write the text in `Err("...")` ``); a reference or a borrowing class there is EN0701, as in any generic argument, and not also EN0454. `Result<T, E>` implies `E extends Error`, and `Result<T>` means `Result<T, Failure>`. `Error` is a family of types, not a type: `Result<i64, Error>` is EN1006. `Error` extends `Display`, so `${e}` works for any `E extends Error`, and an error's text is what it prints (below): a `Failure` prints its text, an enum that writes `fmt` what its `fmt` writes, and a case of any other enum its text, otherwise its qualified name (`AgeError.NotANumber`) followed by every field it has, each printed as anywhere else: `DiskError.BadSector { lba: 42 }`, `PacketError.Truncated { got: [1, 2, 3] }`, `PacketError.BadHeader { header: Header { len: 3, flags: 0 } }`. So no enum is refused as an error type, and a class that implements `Error` prints as any class does |
| `Clone` | `clone(): Self` | Every Copy type in `V` satisfies it by a plain copy, with or without raw pointers, and `T extends Copy` implies `T extends Clone`. `string` and `T[]` have it as listed in 8.3. `T \| null`, `T[N]`, tuples, anonymous object types, `Result<T, E>` and `Box<T>` satisfy it when their parts do, and `Box` allocates a new block. Any other class or enum has it synthesised memberwise on demand when its fields all satisfy `Clone`, unless it has a destructor or a raw pointer field. The check is coinductive, so a `Box<Node> \| null` field of `Node` is fine. A class with a destructor needs a user-written `clone`. A user-written `clone` always wins |
| `Eq` | `equals(other: &Self): bool` | `implements Eq` with no body synthesises memberwise. `==` on a class or payload enum calls it; otherwise EN0421 |
| `Ord` | `compare(other: &Self): i32` | Negative, zero, positive. Used by `sort`; `<` never calls it |
| `Display` | `fmt(let f: &Formatter): void` | Needed by `${x}`, `console.log`, `toString` and `join`. Every type has it, so this bound never fails, and a type parameter meets it with no bound written: primitives and `string` in `core`, a class with no `fmt`, of its own or inherited, or an enum with no `fmt` of its own, through one synthesised on demand, and every other type as printing describes (below). A `fmt` that a class writes only changes how it and the subclasses that inherit it print |

`==`, `${}`, `...`, `sort` and `console.log` call these members with the contracts the table declares (N11): `this` is read in `Eq`, `Ord`, `Clone` and `Display`, and `Display`'s `f` is written. An implementation that writes more fails satisfaction, naming the line that writes (EN0615). Members and functions marked `@intrinsic` or `@hostCall` take their contracts from a compiler table, with no override, so the methods of `Atomic` read `this`.

**Printing.** Every value can be printed, and `console.log`, a template hole, `toString` and an error's text all print it the same way. A class with no `fmt`, neither its own nor one inherited from a base, prints its own name, then each field in declaration order, a base class's fields first and private fields included, each printed by these same rules, a field of a `@packed` class copied out first, as `console.log` copies one (EN0826 makes every packed field Copy): with `public class Header { public len: u16; private flags: u8; }` and `const h = new Header { len: 3 };`, `console.log(h)`, `` console.log(`${h}`) `` and `console.log(h.toString())` each print `Header { len: 3, flags: 0 }`. A class that writes `fmt` prints what its `fmt` writes instead, and so does each subclass that does not override it, because a written `fmt` is inherited like any method; that is all `fmt` changes. The synthesised printer is not a declared member, so the first `fmt` written in a chain, one that no base writes, takes no `override`, and `override` on it is EN0443. An enum that writes `fmt` prints what its `fmt` writes, for every case, as a class does; a case of an enum with no written `fmt` prints its text, or else its qualified name followed by its fields, if it has any (4.3). A field of type `void` is never printed, and a case left with no field to print prints its name alone. `Result`'s cases, which code writes bare, print bare in that form: `Ok(5)` prints `Ok { value: 5 }`, `Err("boom")` prints `Err { error: 'boom' }`, `[Ok("x")]` prints `[Ok { value: 'x' }]`, and `Ok()` of a `Result<void>` prints `Ok`, while every other enum keeps its qualified name, `Shape.Circle { radius: 2.5 }`. An array or a `&Slice<T>` prints as `[1, 2, 3]`, a tuple as `[1, 5]`, and an anonymous object as `{ age: 36, name: 'Ada' }`, its fields in name byte order on every target (section 6). A string printed on its own prints as it is, with no quotes: an argument of `console.log`, a template hole, `toString`, each element that `join` joins, and an error's own text where it is the whole output, a `Failure`, a text enum case, the `error: <e>` of `main` and of a test that returns `Err`, and what `toBeErr` compares. A string inside another value, as a field of a class, an anonymous object or an enum case, `Ok` and `Err` included, as an element of an array or a tuple, or as the payload of a nullable inside one, prints in single quotes, as Node prints it, so its commas and braces never read as the value's own: `Header { len: 3, tag: 'x, flags: 0' }`, `['a, b', 'c']` and `{ quote: 'say "hi"' }`. Inside the quotes `\` prints as `\\`, `'` as `\'`, a newline, a tab, a carriage return and NUL as `\n`, `\t`, `\r` and `\0`, and any other character below U+0020, and U+007F, as `\x` and two uppercase hex digits, `\x1B`; this is one fixed rule, and the quote never switches to `"` or a backtick, as Node's does. The same holds for a `&string`, a string part and a value of a string-literal union, and for a `Failure` or a text case of an enum with no written `fmt` inside another value, which prints its text quoted like a string: `[AgeError.Negative]` prints `['negative age']`, while an enum that writes `fmt` prints through it there too, unquoted, as a class with `fmt` does. A value that a failed matcher shows, actual or expected, is never printed on its own, so a string, and every value this rule quotes inside another, is quoted there at every level, the top level included, and a value whose type writes `fmt` shows what its `fmt` writes, as it does inside another value (12.2); a test that returns `Err` shows `error: <e>`, the error printed on its own, exactly as `main` prints one (12.1). A `bool` prints as `true` or `false`, a number as `core/fmt` says (8.2), `null` as `null`, a present `T | null` as its value, a reference or a `Box<T>` as what it points to, a raw pointer as its address, and an `fn` value or a closure as the address of its code, each as `0x` followed by lowercase hex digits with no padding, `0xb8000`; on the VM (`enrang dev`, and `enrang test` by default, 12.4) these are VM addresses (8.5). Through an `&Animal` or a `Box<Animal>` that holds a `Dog`, the `Dog` prints, by the `fmt` it has, its own or inherited, or else with its own name and fields, inside `Animal`'s constructor too, where the `Dog`'s fields are already set (4.3), but not inside `Animal`'s destructor, where it prints as an `Animal` (5.7). The table that travels with a `Box<I>`, or with a two-word `&I`, holds two printers of the type it was made from: its own, written or synthesised, and the one it uses inside another value, which quotes a string, a `&string`, a string-literal-union value, a `Failure` and a text case as above and is otherwise the same. So such a value prints the same way at the top level and nested: a `Box<Labeled>[]` holding the text case `Mood.Happy` and a `Robot` whose `id` is 7 prints `['happy', Robot { id: 7 }]`, and the tuple `[&m, 1]` at `[&Labeled, i64]`, with `m` that case, prints `['happy', 1]` (section 11). Printing writes piece by piece into a `Formatter` and never allocates; only the `string` that `toString` or a template in an allocating position builds does (section 6).

**Destructors.** Cleanup is not an interface, as Rust's `Drop` trait is, but a class's `destructor` (4.3). A destructor is never a member, neither for lookup nor for structural satisfaction: `x.destructor()` is EN0606, and so is a `destructor` declared in an interface. Use the prelude `dispose(x)`. The destructor has exclusive access at the end of the object's life, and running it is not a write of the object's own bytes for the read-only marks of 4.11 (N11). What it writes through the reference fields of a borrowing class still counts toward that class's flag (4.3).

**Sealed bounds.** `core` also declares nominal interfaces with a closed list of implementers, which user code cannot extend (`implements` one is EN0419): `__Int`, `__Float`, `AtomicValue`, `AtomicBits` (section 10.5) and `VolatileValue` (section 7.2). They exist so that rules about particular primitives can be written as ordinary bounds and checked once.

No operator overloading exists beyond `==` through `Eq`.

### 4.5 Coercions

Coercions apply only at coercion sites: argument or parameter default to parameter, initialiser to annotated local, field initialiser, assignment right-hand side to the target's type (compound assignment excluded), `return` and an arrow's expression body to the result type, array-literal element to the expected element type, and match-arm or ternary-branch results to an expected type. No coercion makes a reference from a value: a reference is made only by writing `&`, except that a string literal already is one (C13). Nothing nests: `T[]` never becomes `(T | null)[]`, and `&(T | null)` never becomes `&T`. At one site, at the top only, rows compose in one order: at most one step that makes or adjusts a reference (C13, C04, C21 or C22), then C18, then one wrap (C06 or C07), so with `function read(lba: u32, buf?: &Slice<u8>): void`, `read(0, &sector)` takes C18 then C07, `fill(&b, 7)` with `b: Box<u8[]>` takes C04 then C18, and `return d;` with `d: &Dog` in a function whose result is `&Speaker | null` takes C22 then C07; an arrow at a nullable closure parameter takes C12 then C06 (4.14). A spread operand is not a coercion site (4.13). Assignment follows the same table: a reference variable takes a reference, a string literal or, if nullable, `null`, so `r = &s` repoints `r: &T`, while `r = s` with `s: T`, `r += 1` and `r++` are EN0422, with fix-its to `*r` or `&`.

Row IDs are stable and each row has an accepting and a rejecting fixture (`TESTING.md` section 18). C01 (an implicit shared borrow) and C02 and C03 (reborrows between the two former reference kinds) are retired and never reused.

| ID | From | To | Condition |
|---|---|---|---|
| C04 | `&Box<T>` | `&T` | Box deref; a place of type `Box<T>` also auto-derefs on `.`. From a `Box<I>` for an interface `I`, the `&I` is two words, the object and its method table (4.4) |
| C05 | `&T` | `T` | **Read-through**, only when `T` is Copy |
| C06 | `T` | `T \| null` | Wrap, value level |
| C07 | `&T` | `&T \| null` | Wrap at slot top |
| C08 | `&T \| null` | `T \| null` | When `T` is Copy |
| C09 | `never` | any | |
| C10 | integer or float inference variable | concrete type | Section 4.7 |
| C11 | non-capturing arrow or safe function name | `fn(...)` of identical signature | A capturing arrow is EN1007 |
| C12 | any arrow, a local holding one, or a safe function name | closure parameter type of identical signature | |
| C13 | string literal | `&string` | Static descriptor, section 5.4 |
| C14 | closure parameter | closure parameter type of identical signature | Exclusive reborrow for that call (5.5) |
| C15 | safe `fn(...)` value or safe function name | `unsafe fn(...)` of identical signature and ABI | Never the reverse |
| C16 | name of an `unsafe function`, `@requires` function, `declare function` or `@naked` function | `unsafe fn(...)` of identical signature and ABI | `@dll` functions have `@abi("win64")`. These never become a safe `fn` or a closure parameter: EN0803 |
| C17 | name of an `@interrupt` function | `InterruptHandler` | Only target; anything else is EN0803 |
| C18 | `&T[N]`, `&T[]` | `&Slice<T>` | A view of all the elements, a pointer and a length (section 11). Never the reverse: a `&T[N]` or `&Slice<T>` where `&T[]` is expected is EN0401 (4.3). `&` of a bracket literal of constants that nothing writes through is a static `T[N]`, as C13's string literal is a static descriptor (5.4) |
| C19 | `T` | `Result<T, E>` | Success, at a `return`, an arrow's expression body, and the ternary branches and `match` arms that flow there, in a function or arrow whose result type is written or expected, never one that an arrow's body decides (5.5), where an operand that takes its type from context is checked against `T` (6); falling off the end of a `Result<void, E>` body, or `return;` in one, is `return Ok();`. Never where `Err` would also take the value as it is: a text where `E` is `Failure`, whether fixed, a template or held in a variable: any `string` or `&string` expression; a fixed text that is a value of a string-literal-union `E`; or a value whose own type is `E` (EN0455); and never at the early return of `?` |
| C20 | anonymous object or class instance, or `&` to one | object type with a subset of its fields, or `&` to one | Only at a parameter, by value or by reference, and at a reference such as `&{ name: string }`, with one copy of the function per shape (4.3). A class counts only its public fields, and by value it must be a value type (EN0701). Elsewhere EN0440 |
| C21 | `&D`, `Box<D>`, where `A` is a base class of `D` | `&A`, `Box<A>` | The object's own methods still run (4.3). A `D` value never becomes an `A`: EN0401 |
| C22 | `C`, `&C`, `Box<C>`, where `C` satisfies interface `I` | `I`, `&I`, `Box<I>` | `C` must be a value type: a borrowing class is EN0701 (4.4). `&C` with `C` = `string`, any `&string`, whole, a part, a literal or a parameter, is EN0401, `` a `&string` can't become a `&Measured`, because it may be a part of a string ``, with `help: take <T extends Measured>(m: &T)` and `help: or keep a copy: s.slice(1, 3).toString()`, while `Box<string>` and a by-value `string` convert, since each holds a whole descriptor (4.4); a call that binds `T := string` to a type parameter whose body makes this conversion of its `&T` is EN0401 too (4.10). `I` only at a parameter, from a whole argument whose type is one class or the class of one interface parameter, never at a ternary branch, a `match` arm or a `??` operand, with one copy per class; `&I` wherever a reference may stand (4.1): at an `&I` parameter that is not nullable, with one copy per class for a direct call, and one more for a two-word `&I`, such as one taken from a `Box<I>` by C04 or any argument of a call whose callee is chosen at run time (4.4), and anywhere else, an `&I \| null` parameter included, as two words, the object and its class's table for `I`, read through the hidden pointer when `C` can be extended, since the object may be a subclass; `Box<I>` carries the object's table for `I` beside the object, read through the hidden pointer when `C` can be extended, since the object may be a subclass (section 11). `I` anywhere else is EN1006 |

In C11, C12, C14, C15 and C16, an identical signature ignores permission rows, which type checking never reads (4.1). In phase 3 the function's contract must fit the type's, as an implementation fits an interface member (4.4): a row may allow more writes than the function's own only at the top of the site, a row nested inside the signature must be equal, and the function may store nothing, neither a parameter nor, for a local function, a hidden argument (5.5), since an `fn` type declares no stores (5.4). Otherwise it is EN0615, or EN0714 for result sources outside the type's: `f: (x: &i64) => void` accepts only functions that read `x`, and a function that writes it needs `f: (let x: &i64) => void`. An arrow is fitted the same way wherever it becomes a closure or an `fn` value, a local that keeps it included, against the type it takes there, which for a local with no written type is the arrow's own signature. An arrow has no contract of its own to infer, so a parameter its body writes counts as Write and a store from one parameter into another as a store: `const inc = (x: &i64) => { *x += 1; };` is EN0615 at the arrow, since `inc`'s type `(x: &i64) => void` only reads `x`, and the parameter needs `let`, as in `const inc = (let x: &i64) => { *x += 1; };`, which compiles; `const put = (l: &Lexer, s: &string) => { l.setSrc(s); };` is EN0615 whatever its marks, since the type declares no stores. A row that allows more writes can pass a `&string` in another form than the function takes (section 11): a `&string` parameter that only reads is a pointer and a length, and one that writes is the whole string, so the conversion makes an adapter that loads the pointer and length from the whole string and calls the function. With `function run(f: fn(let s: &string) => void, s: &string): void { f(s); }` and a `show` that only reads its `s`, `run(show, &msg)` gets `show` the string `msg` holds. An adapter calls one known function, so into an `fn` type a conversion that changes a `&string` form, of a parameter, of the result or of a `&string` part of a tuple result, `| null` included, is allowed only from a function name or a non-capturing arrow, and from any other `fn` value it is EN0615: with `function choose(loud: bool): fn(s: &string) => void { return loud ? quote : show; }`, `run(choose(false), &msg)` gives `` `choose(false)` may hold a function that takes `s` as a part, so it can't become a `fn(let s: &string) => void` ``, with `` help: declare the wider row where the value comes from: `fn(let s: &string) => void` ``. Into a closure parameter type the adapter is a closure built on the stack for the call, whose environment is the original value, so a closure parameter forwarded by C14 converts there too. An override of a base method that writes the parameter, by its body or a `let` mark, and a method implementing an interface member marked `let` on it, are reached through the same kind of adapter when a call goes through a method table, and so is a function whose writable `&string` result meets a read-only one. A function whose result is read-only, as one that may return a constant is, fits only a type whose result is read-only too, `fn(xs: &Slice<i64>) => readonly &i64`, and is otherwise EN0615 with the help to add `readonly` there. The fit is checked here, at the conversion: a call through an `fn` value is checked against the type's contract alone, and `enrang dev`, which checks each indirect call at run time, compares only the parameter and result types of the function it reaches with the type's (`DEV_RUNTIME.md` section 2.3). So `private function first(a: &string, b: &string): &string { return a; }`, stored as `const pick: fn(a: &string, b: &string) => &string = first;`, makes `console.log(pick("Ada", "Bo"));` print `Ada` in `enrang dev` as in a build. That rests on every `fn` value naming the body its conversion was checked against: under `enrang dev`, each function reference in code compiled before a reload, a call, a conversion to an `fn` type or a closure, or the function an adapter calls, still names the body that code was compiled against, so a value that an old frame makes after the reload names the retired body, as a value made before the reload does, and every later reload checks a retired body that a live value names as it checks code a frame can reach, refusing with EN1213 when that body would do what blocks a reload in a frame, such as reading a changed field, calling through a changed table entry, building, through a retired constructor, a class that gained a field with no default, or calling a method on, or building with `new`, a class that gained or lost `final` (`DEV_RUNTIME.md` sections 2.3 and 6). An arrow passed to a closure parameter that is nullable at the top converts by C12 and then C06 (4.14). As an `fn` value (4.14), a function with default parameters takes every parameter, an overloaded name takes the overload whose signature is expected, a per-shape function (4.3) is fixed to the shape written in the type, and a function with an `&I` parameter names its copy for two-word `&I` arguments, since a call through the value is chosen at run time (4.4), while a function with a by-value interface parameter, compiled once per class passed, has no single copy to name and is EN1006 there, as an `fn` value or a closure parameter (4.4).

There is **no** implicit `&` (N8): a non-reference argument to a `&` parameter, a `return` from a function returning `&T` and an annotated `&T` initialiser all need it, so `total(a)` with `total(xs: &Slice<i64>)` and `return this.name;` in a method returning `&string` are EN0612, whose fix-it inserts `&`. A variable that already holds a reference is passed as it is, and `&r` with `r: &T` means `r`. Still automatic: method receivers (`a.push(3)`), operators, `console.log`, template holes and `expect`. There is no numeric coercion, no wrap of an error into `Result` (C19 wraps only a success), and no truthiness. Operators see through one reference: arithmetic and comparison on `&T` act on `T` when `T` is Copy or `string`, and `${}` prints what any reference points to (4.4); `==` compares through references on both sides, never by address (raw pointers compare by address).

### 4.6 Numeric rules

Binary arithmetic requires identical types after inference; `i32 + i64` is EN0402 with an `as` fix-it that widens, which never fails: `this.data.length() - this.pos` with `pos: int` is `` cannot subtract `int` from `isize` ``, fixed as `this.data.length() - (this.pos as isize)`. `/` on integers truncates toward zero; if both operands came from unsuffixed literals or literal-default inference variables, warning EN0430 explains that TS would give `3.5` and offers `7.0 / 2.0`. Bitwise and shift operators need integer types (EN0403). Shift counts have any integer type.

**Comparison.**

| Operands | Rule |
|---|---|
| `p == null`, `p != null` | Legal for any `T \| null` |
| Numerics of one type, `bool`, `string`, payload-free enums | Compare natively |
| Two different integer types | Compare the true values, as C++20 `std::cmp_less` does: `this.pos >= this.data.length()` with `int` and `isize` works. An integer and a float never compare: EN0402 |
| Raw pointers | Compare by address |
| Class or payload enum | Calls `Eq`; otherwise EN0421 |
| `T \| null == T \| null` | Needs `T` comparable; equal when both are null, or both present with equal payloads |
| `T \| null == T` | EN0401 with a narrowing fix-it |
| `<`, `<=`, `>`, `>=` | Numerics only; `string` gets EN0420 with a `.compare` fix-it |

**Conversions.** `x as T` is the only conversion. A direct literal operand, optionally negated, takes a numeric target's type: `0xFFFFFFFFFFFFFFFF as u64` is legal and `300 as u8` is EN0411. A raw-pointer target makes the literal `usize`, so `0xB8000 as *u16` is legal. Any other operand whose type is still an inference variable does not unify with the target. It defaults at the end of the function, and the conversion kind is chosen after that.

| Conversion | Behaviour |
|---|---|
| int to int | Panics if the value does not fit: `conversion out of range: 1059392 as u16` |
| int to float, float to float | Rounds to nearest-even, never panics; overflow to infinity follows IEEE |
| float to int | Truncates toward zero; panics on NaN or out of range |
| payload-free enum to int | Discriminant, checked as int to int; an enum with text values has none (EN0404) |
| int to enum | Not allowed: EN0404 |
| `bool` to int | `0` or `1`; the reverse is EN0404 |
| `usize` to raw pointer | Safe to create |
| raw pointer to `usize` | Safe |
| `&T` to `*T` | Safe |
| `*T` to `*U` | Safe to create; dereferencing is `unsafe` |

Non-checking forms are methods: `x.wrap<u8>()` (keep low bits, or sign-extend), `f.toBits()`, `f64.fromBits(b)`, and the arithmetic families `wrappingAdd`, `checkedAdd` (returns `T | null`), `saturatingAdd`, `overflowingAdd` (returns `Overflowing<T>`, a `core` class with `value: T` and `overflowed: bool`), likewise `Sub`, `Mul`, `Neg`, `Shl`, `Shr`. So an interrupt handler's address splits as `const low = handler.wrap<u16>();`, or `(handler & 0xFFFF) as u16`, and `const high = (handler >> 16) as u16;`, which fits, while `handler as u16` panics for an address such as `1059392`.

An index may have any integer type. It is bounds-checked, and a negative index panics as out of bounds; a non-integer index is EN0405. `length()` returns `isize`, so counting down works as in TS: `for (let i = xs.length() - 1; i >= 0; i--) { console.log(xs[i]); }` prints `30`, `20` and `10` for `[10, 20, 30]`, and nothing for an empty array.

### 4.7 Inference

Local, bidirectional, per function body; types in signatures are never inferred, but contracts are: what a function does with its references comes from its body after type checking (section 5). Type checking never reads a contract, so member lookup, inference and interface shape ignore permissions. Parameters and fields must be annotated (EN0409), and `x?: T` on either has type `T | null` and default `null`, where a `T` that is already nullable as written stays `T` (4.3, 4.14) (`?` together with a default is EN0227); return types default to `void`.

1. Each integer literal gets a fresh integer variable, each float literal a float variable. An integer variable may unify with any integer or float type; a float variable with any float type. Variables unify across the whole function, so `for (let i = 0; i < xs.length(); i++)` makes `i` an `isize`, one register on `i386`. In a comparison, an unresolved variable takes the other operand's type; the mixed-integer rule of 4.6 applies only between two already-typed values.
2. Unresolved variables default at the end of the function: integer to `int` (`i32`), float to `f64`. Using one as an index defaults it to `isize` first. A value from something typed keeps that type: `const start = os.now();` is `i64`.
3. A literal that does not fit its final type is EN0411; when that type came from the `int` default, the fix-it adds `: i64` (`` `3_000_000_000` doesn't fit `int` ``, fixed as `const big: i64 = 3_000_000_000;`). A `-` immediately before an `IntLit` folds before the range check, in expressions and patterns, so `const m: i64 = -9223372036854775808;` is legal. A float literal keeps its text and is parsed once, at its final width, so an `f32` literal is correctly rounded and never double rounded.
4. **Generic calls** run in three steps. `f<i32>(x)` gives type arguments explicitly, all or none, and an unresolved `T` at the end is EN0410.
   - Unify the return type with the expected type. This is a hint: if a non-arrow argument then fits its parameter neither as it is nor by a coercion, the hint is dropped, the call is typed again from its arguments alone, and its result meets its coercion site (C21, C22). So in `const pets: Box<Animal>[] = [new Box(new Animal("Generic")), new Box(new Dog("Fido"))];` the second element is a `Box<Dog>`, which C21 converts, while `Ok(x)` with `x: i64` at `Result<i64 | null>` keeps `T := i64 | null` and wraps `x` by C06. When both ways fail, the error reported is the one with the hint.
   - Process non-arrow arguments left to right. `&?T` against a non-reference `U` binds `T := U` and is EN0612, whose fix-it inserts `&`. `&?T` against a view `&Slice<U>` binds `T := Slice<U>`, which the callee's view fact then accepts or rejects (4.10). `?T` against `&U` stays pending until the end of the call, then resolves from other bindings, otherwise by Copy read-through, otherwise EN0703.
   - Process arrows left to right, with substituted parameter types.
5. `[]` needs an expected type or later unification with a `push`; otherwise EN0410. Local type variables unify across later uses, exactly as literals do. A member access on a still-unknown type variable is immediately EN0410. A member access on an integer or float variable looks up the members of `__Int` or `__Float` with `Self` set to that variable, so inference continues: `let a = 5; a.checkedAdd(1)` works. Section 4.13 types a spread.
6. `null` alone needs an expected type, and so does the name of an overloaded function: `const f = describe;` is EN0410, and `const f: fn(n: int) => string = describe;` picks one.
7. A bracket literal takes its meaning from the expected type: `const b: int[2] = [1, 2];` is a fixed array and `const c: [int, int] = [1, 2];` a tuple. Behind `&` where a `&Slice<T>` is expected, it is a `T[N]`, which converts by C18 and allocates nothing: `minMax(&[3, 1, 4, 1, 5])`. When its elements are all constants and nothing writes through it, that `T[N]` is a read-only static, as a string literal is (5.4). With none, `const a = [1, 2];` is `int[]`, and `[1, "a"]` is EN0401 with a help adding a tuple annotation (`const x: [int, string] = [1, "a"];`). A tuple pattern on the left of a declaration or an assignment gives its right-hand side an expected tuple type, whose parts are the targets' types, or fresh variables in a declaration with no annotation: `[a, b] = [b, a];` swaps, and `const [p, q] = [1, 2];` binds two `int`s. A right-hand side that is not a bracket literal keeps its own type, so an array there is EN1042. An object pattern gives no expected type. An object literal with no expected class type has an anonymous object type (4.3).

### 4.8 Null narrowing

Narrowing is flow state during type checking, not a later pass, because it changes types: `return Ok(v)` infers `T := i64` from it, and `n.x` resolves only with it. Facts are `(path, non-null)`, where a path is a local or `this` followed by field projections, possibly through a reference or `Box`. Paths never contain an index.

- **Created by:** `p != null`, `p == null` in the else branch, `!(…)`, `&&` left to right, `||` in its false branch, early `return`/`break`/`continue`/`panic` in the opposite branch, and ternaries. An assignment to `p` tested in place of `p`, as `(line = readLine()) != null`, creates the same fact, since its value is `p` read after the store (3.5).
- **Killed by.** In typing (N2), the fact on `p` dies only on a visible change: assignment to `p` or a prefix, a direct write to `p` or a prefix, and a move of `p`, its payload or a prefix. Writes and moves of a proper extension `p.f` kill only facts on `p.f` and deeper. So `if (n != null) { n.x = 1; n.x = 2; }` and `if (n != null) { n.bump(); n.bump(); }` compile. Calls and borrows kill nothing while typing. Instead, any reference created to a proper prefix of `p`, or to `p` itself at its nullable type, is recorded: a call argument, a receiver, a copy, a binding (destructuring included), a capture or a hidden argument. Once contracts exist, a dataflow on the MIR CFG checks each record: if the recorded reference writes (section 5), a later use typed through the fact with no new test between is EN0401, naming the writing line, with the note `` a writing reference may have changed `p` ``. Nothing is re-typed. A use whose expected type is the nullable type records nothing, and passing `p` at a non-null `&T` records nothing, because that reference cannot store `null`.
- **Evaluation order.** Kills and records follow O6 order, and a receiver auto-borrow or an assignment place takes effect after its arguments or right-hand side, except the place of a compound assignment to a non-Copy place, which takes effect before its right side (O6): its fact is read there, and a right side that would kill it writes the place, which is EN0707 under the reservation, so with a `clear(o: &Obj): &string` that sets `o.s = null`, `if (o.s != null) { o.s += clear(&o); }` is EN0707 at `&o`. The receiver or place is therefore typed as narrowed only if no argument or right-hand side kills the fact, and the check after contracts sees an argument's write before the receiver's use: with `clear` taking `&(T | null)` and writing `null`, `o.add(clear(&o))` and `o.n = clear(&o)` are EN0401, with a note naming the argument.
- **Loops.** Before the condition of a loop is checked, a prescan of the loop's syntax collects its visible changes: assignment targets, `++`/`--`, and direct writes and moves of paths, including inside arrow bodies and spread operands. The kill rules apply to everything collected. References the loop creates are recorded as above, and the dataflow that checks them follows the back edge.
- **`for...of`.** The source is typed under the current facts and classified (5.6). The prescan then covers the body only, and an evaluate-once source uses its fact before any kill: `if (p != null) { for (const x of [...p]) { p = null; } }` compiles. A path source is held for the whole loop (5.6), so changing it inside the loop is EN0706 unless that path leaves the loop: `if (p != null) { for (const x of &p) { p = null; } }` is EN0706, and with `p = null; break;` it compiles. The state after the loop is the join of the head's exit edge with the state at every `break` of this loop, labelled or not, and never the head's state alone, so a fact holds after the loop only if every way out to that point holds it. So `if (p != null) { for (const x of &p) { p = null; break; } console.log(p.length()); }` is EN0303. A `break outer` in an inner loop counts as a `break` of `outer` and not of the inner loop. A `return` or a panic never reaches that point, so `p = null; return;` costs nothing after the loop.
- **Arrows.** The same prescan runs over each arrow argument of a call before narrowing enters it. An arrow inherits facts on paths it does not visibly change. A path that any arrow argument of the call assigns, writes or moves loses its fact at the call, and no arrow of that call sees a fact on it; a capture is recorded as above. So `if (p != null) { xs.forEach(x => { p = null; }); console.log(p + 1); }` is a compile error, EN0420 at `p + 1`, rather than a tag panic (`TESTING.md` T:602).
- **Effect:** a narrowed path has type `T` for reads and moves. `&p` under narrowing has type `&T`, which cannot write `null`; if context needs `&(T | null)`, the expression has that type and is recorded as above. The lowered read is a `CheckTag` immediately before the projection, in the same MIR block with nothing but other checks between them, as for `CheckBounds`, so a compiler bug panics rather than reads garbage.
- **Not narrowed:** truthiness (`if (x)` is EN0203), array elements, `typeof`.

`p?.f` on a place of `T | null` has type `&F | null`, which reads through by C08 when `F` is Copy. `p?.m(args)` calls `m` when non-null and has type `R | null`, except that a `void` method gives `void`. On an `&T | null` value it behaves the same, so `a?.b?.c` works. On an owned `T | null` rvalue it is EN0413: bind it first.

`a ?? b` evaluates `b` only if `a` is null; `a: T | null` and `b: T` give `T`, moving out of `a` when `a` is a place of owned non-Copy `T`. `x!` panics with `unexpected null` if null, reporting the line and column of the `!`, otherwise moves the payload out of an owned path or reads a reference. A custom message is written with `??`, because `panic` has type `never`: `os.env("PORT") ?? panic("set PORT before starting the server")`.

### 4.9 Constants and top-level storage

`public const NAME: T = e;`, or `private`, is compile-time: `e` is built from literals, other constants, arithmetic with checked overflow (failure is EN0412), `sizeOf`/`alignOf`/`offsetOf` of a type that is not a borrowing class or tuple, numeric `as`, `usize` to raw pointer `as`, fixed-array and class literals (`new C { ... }`) of those, and `&` of a bracket literal of those at an annotated `&Slice<T>` or `&T[N]`, a constant literal view. A cycle such as `private const A = B; private const B = A;` is also EN0412. So is `sizeOf<Sink>()` for a borrowing `Sink`, with the note `` the layout of `Sink` depends on what its methods do with its references ``: the form of a reference field or part follows permissions (section 11), which contracts decide after type checking (N1). Inside a body it folds as usual. The annotation may be omitted when the initialiser's type is determined; an integer literal then defaults as in 4.7. `T` has no destructor and no heap; string literals are allowed only as `&string`. A constant literal view is a read-only static, a `T[N]` in read-only data (section 11) with the top-level `const` mark (4.11), as a string literal is a static descriptor (5.4): the defining module emits it once, its interface file stores the literal, and every importer points at that one static, as for a `&string` constant. So `public const PRIMES: &Slice<i64> = &[2, 3, 5, 7];` is accepted, as `public const NAME: &string = "Ada";` is, and `PRIMES[0] = 1;` in a module that imports it is EN0608, naming the top-level `const`. Such a constant holds no state, so it is visible everywhere in its file, class methods included, even in a file with top-level statements. `assert(constExpr, "message")` at top level (`TopAssert`) is a compile-time check, EN0415 on failure; among a program's top-level statements, an `assert` whose condition is not constant is checked at run time. A constant is copied wherever it is read by value, and `&CONST` is a reference with an empty loan set. An array spread allocates at run time, so `...` in a `ConstExpr` is EN0412 at that token, with the note `a spread allocates at run time`, reported before any expected type is compared. That covers top-level `const` and `unsafe let` initialisers, `RepeatLit` counts, `T[N]` lengths and a top-level `assert` outside a program's top-level statements. Field initialisers run at run time and a local `const` is an ordinary binding, so `const ys = [...xs];` in a function body is fine.

`public unsafe let NAME: T [= e];`, or `private`, is mutable static storage, in any file: `@at(0xB8000) private unsafe let screen: u16[2000];`. Like every top-level declaration it states its visibility, and leaving it out is EN0226 (4.12). A plain top-level `let` is a local among a program's top-level statements, and in a file that is imported it is EN0312, with the help to write `unsafe let`. Every read, write or borrow of an `unsafe let` needs `unsafe` (EN0801). `T` must not have a destructor or contain `string`, `T[]` or `Box` (EN0802). With no initialiser it is zero-filled and `T` must be zeroable: integers, floats, `bool`, raw pointers, fixed arrays and `final` classes with no base of those, private fields included. A class that can be extended carries a method-table pointer that zero would leave null (section 11), so such a declaration is EN0802, with the helps `` write `public final class Stats` `` and `` or give it a value: `= new Stats {}` ``. A class in `@at` storage, which the compiler never fills, must likewise be `final` with no base. `void` and references are not allowed.

### 4.10 Generics

Monomorphised on a worklist. Bodies are type-checked and borrow-checked once, generically, against bounds, and instantiation cannot introduce a type or borrow error. Exactly three codes depend on a concrete instantiation: EN0414 (depth above 64), EN0435 (size limits, section 11) and EN0820, for a `?` or `Err(e)` into a `Result<T>` whose error needs a text built at run time for the type an instance gives `E` (8.3). They are reported in phase 5 with the reach chain; EN0820's primary label is at the call that instantiates the body, with a note at the `?` or `Err`, and its help names the generic form, `` return `Result<T, E>` ``. Rules about particular primitives (volatile width, atomics) are sealed bounds, checked at the call site, so they never wait for instantiation. Functions with anonymous-object or interface parameters are instantiated the same way, once per shape or class (4.3, 4.4), and a function with an interface parameter gets one more instance, made only when a two-word `&I`, such as one taken from a `Box<I>`, reaches it, whose member calls go through the method table (4.4). Members called on `T` must come from a bound; `T extends Copy` also grants `clone` (4.4). In an instance whose `T` is a class that can be extended, such a call goes through the method table, so a subclass's override runs, except a call to a member compiled once per type, which has no slot and is direct (4.3). A member called through a bound has the bound's declared contract (4.4), so a generic body's contract never depends on `T`. Likewise the row of an `fn` type or closure parameter type written with a type parameter is computed generically, before substitution: in `function growVia<T>(f: fn(a: &T) => &T, x: &T, v: T): void { *f(x) = v; }`, `f`'s result is writable for every `T`, so `growVia(head, &s, "zz")`, with a `head` that returns a part of its `&string`, is EN0615 at the call. Only the form of a `&T` depends on the instance: at `T := string`, a Read `&T` or `&T | null` parameter, or a Read `&T` part of a by-value tuple parameter, that is in the sources of a writable result, and not stored, is the whole string, and so is such a parameter of an `fn` or closure type written with type parameters, by its row's declared sources (section 11). Under `T extends A & B`, a member both declare takes the lower of the two contracts, and a `move` member against one that is not `move` is an error at the bound. `T` is treated as non-Copy unless bounded by `Copy`; reading it by value moves it. A type parameter in the error position of `Result<T, E>` is implied to extend `Error` (4.4), so generic helpers do not repeat the bound. No associated types, const generics, specialisation or higher-kinded types (EN1014). Type parameters on a class are in scope in its methods; `static` methods use them too: `Stack<i64>.empty()`, or inferred from the expected type.

**Class bounds.** A bound may name a class, as in TypeScript and Java: `T extends Animal` admits `Animal` and every class that extends it, directly or through others, by name and nothing else, so a bound that names a `final` class admits that class alone, and any other type argument is EN0419. With `public constructor(public name: string, public age: i64) {}` in `Animal`, `` public fetch(): string { return `${this.name} fetches`; } `` in `Dog`, and `public function oldest<T extends Animal>(xs: &Slice<T>): &T`, which returns the element with the greatest `age`, `console.log(oldest(&dogs).fetch());` prints `Fido fetches` for `const dogs = [new Dog("Rex", 3), new Dog("Fido", 7)];`, where the same function over `&Slice<Animal>` makes `.fetch()` EN0303. In the body a `T` has the members of `Animal` that code outside it sees: its public fields, read and written as through a `&Animal`, and its public methods, while `protected` and `private` members stay hidden, since the function is no subclass. A call to a method of `Animal` that can be overridden, on a place of type `T` or `&T`, is checked once, against the bound, with the contract of a call through the method table, the base body's sources plus the object and its stores with their bits (5.4), so a subclass's override fits it as it fits a call through a `&Animal`, by the same rule for stores, and each instance makes the call through the method table, so the object's own method runs; a `static` method, and every method of a `final` bound class, keeps its own body's contract and is called directly, as in 5.4. Printing a `T` prints the object's own class. Each class passed gets its own instance, as for any generic. A class bound combines with interface bounds, as in `T extends Animal & Speaker`; a `T` bounded by a class never stands for a view (below); and a borrowing class as a bound is EN0701, `` `T` can't stand for a `Lexer`, because `Lexer` holds a reference ``, since no generic argument can hold one.

**Views.** A type parameter of a function that its signature and body use only behind `&`, never by value, never in `sizeOf<T>()` or `alignOf<T>()`, never as an element type, a field type, a type argument that needs a value type, or the type of a by-value parameter, local or result, never behind a raw pointer, as `*T`, and never converted by C22 to an interface, as `T`, `&T` or `Box<T>` to `I`, `&I` or `Box<I>`, since only a value type becomes an interface value (4.4), may also stand for a view `Slice<U>`, as Rust's `T: ?Sized` allows, but inferred from the body instead of written: `show(sector.slice(0, 2))` binds `T := Slice<u8>` for the `show<T>(x: &T)` of 4.3 and prints `[7, 7]`. In such an instance a `&T` is a `&Slice<U>`, two words, the address and the length (section 11), as a two-word `&I` is (4.4). The second word of an `&I` is its table, with no room for a view's length, which is why C22 loses the fact: with `public interface Measured { length(): isize; }`, which `Slice<u8>` satisfies, and `public function show<T extends Measured>(x: &T): void { const m: &Measured = x; console.log(m.length()); }`, `show(sector.slice(0, 2))` is EN0401, labelled at `const m: &Measured = x;`, and so is a view passed to an `after<T>(x: &T)` whose body casts `x as *T`, labelled at the cast. An arrow nested in the body, at any depth, counts as part of it, for this fact and for the next one. A body that passes its `&T` on to another generic function keeps the fact only if that function's parameter has it too; within a call-graph SCC every type parameter starts with it and loses it by these rules until nothing changes. A declaration with no body, an interface member, an abstract method, a `declare function` or an `@intrinsic` member, has no body to keep the fact, so it lacks it, unless the compiler table that gives an intrinsic its contract (4.4) states it; a call through such a declaration therefore binds no view, whatever the bodies that implement it do (4.4). A method with type parameters of its own has no method-table slot and is never overridden (4.3, 4.4): `public override show<T>(x: &T): void` in a `Dog` over an `Animal.show<T>(x: &T)` is EN0460 whatever its body does, so every call to such a method reaches the body that declares it, and that body's own fact decides. The fact is inferred from the body, as a contract is, but it decides which calls are accepted, a question of types and not of borrows, so it belongs to the function's declaration: the interface file states it with each declaration, every method's included, in the section the API hash covers, so a body edit that starts using `T` by value is a change its callers see, which rebuilds them, or is EN0315 for one with no source, never a recheck, since a recheck reruns only phase 3 (4.12); and the check on load computes it again from the stored code, so a file that states it wrongly is EN0316 (4.12). A call that binds a view to a `T` used by value is EN0401, `` `T` can't stand for the view `Slice<u8>` ``, with a label at that use in the body and `` help: add `show<T>(x: &Slice<T>)` ``. That help makes two generic overloads that both match a view without a chain, and the call then runs the added one, which is more specific (4.14), so the view never reaches the `T` used by value, while `show(&sector)` still runs `show<T>(x: &T)`, the only one of the two that needs no chain. Inference binds `T` the same way whether or not the fact holds, so type checking never waits for it: this check runs once every body's fact is known, still as EN0401. The same inference gives each type parameter a second fact, that it may stand for `string`, because a `&string`, whole or a part, never becomes an `&I` (4.4) and an instance at `T := string` has no whole descriptor to give such a conversion of its `&T`: a type parameter loses it where its body converts a `&T` or a `&T | null` to an interface reference by C22, and where it binds a type parameter of another function, or of a class, that lacks it, by the same fixed point. A class's type parameter has this fact as well, computed over every body of the class, its methods, `static` ones included, its constructors, its destructor and the arrows nested in them: binding `string` to one without it, in a written or inferred type, is EN0401 with the message below, labelled at the conversion, so with `public class Keeper<T extends Measured> { public show(x: &T): void { const m: &Measured = x; console.log(m.length()); } }`, `new Keeper<string> {}` is EN0401, since `k.show(s.slice(1, 3))` would hand that conversion a part. An interface member keeps it, so a call through one binds `string` freely, and a member that satisfies one, by any satisfaction (4.4), which every such call may reach, may not lose it: with `public interface Sizer { size<T extends Measured>(x: &T): isize; }`, a class whose `size` runs `const m: &Measured = x;` is EN0401 there, whether it satisfies `Sizer` by `implements`, by inheriting `size`, structurally at a conversion or an argument, or by meeting a bound `Z extends Sizer`, `` a `&string` can't become a `&Measured`, because it may be a part of a string ``, with `` note: `Sizer.size` lets `T` stand for `string` ``. Any other declaration with no body lacks it, as it lacks the view fact, unless the compiler table that gives an intrinsic its contract states it. A call that binds `T := string` to a type parameter without it is EN0401, `` a `&string` can't become a `&Measured`, because it may be a part of a string ``, labelled at the conversion in the body, with `` help: add `show(x: &string)` ``, an overload the call then prefers, being non-generic (4.14): with the `show<T extends Measured>` above and `let s = "hello".toString();`, `show(s.slice(1, 3))` and `show(&s)` are each EN0401, while a `T` or a `Box<T>` that a body converts by value takes a whole string. This fact belongs to the declaration as the view fact does, stated with it in the interface file and computed again by the check on load.

### 4.11 Mutability

`const` is Rust's plain `let`, and `let` is Rust's `let mut`. Whether a reference writes is not part of its type: it is inferred (section 5), and the marks below decide where writing through one is allowed.

- **Roots.** A `let` local can be reassigned and its owned contents (fields, elements, `Box` contents) changed. A `const` local cannot: reassigning it is EN0613, and changing its contents, also through a reference made from it, is EN0608, or EN0614 when the change is a call to a changing method, as `xs.push(1)` (G16). A by-value parameter is like a `const` unless declared `let`, as in `function clamp(let x: i64): i64 { if (x > 10) { x = 10; } return x; }`. The `let` changes only the function's own copy, so the caller may pass a `const` and the function's type is unaffected. Assigning a parameter not marked `let` is EN0613 (`` cannot assign to parameter `x` ``, helps `` mark it `let x` `` and `` take `x: &i64` and write `*x` ``), and calling a changing method on it is EN0614. An `unsafe let` is changeable inside `unsafe` (4.9). `readonly` fields reject writes outside the constructor, also through a writable reference (EN0609), and through an object type or a fields-only interface: a class passed for one (C20), behind `&`, nullable or not, to a parameter whose permission is Write or by value to one marked `let`, a parameter of an `fn` value or a closure included, where the type names a field the class declares `readonly`, is EN0609 at the argument, since the callee's body is checked once for the type, which has no `readonly` field, so `function setx(p: &{ x: i64 }): void { p.x = 5; }` called as `setx(&c)` with `public readonly x: i64` in `c`'s class is `` `setx` can write `c.x`, but `x` is `readonly` ``, while a `showx(&c)` that only reads `p.x` compiles; the permission is the parameter's, whichever field the body writes, and a result whose sources include such an argument is read-only at the call for the same reason, so with `function px(p: &{ x: i64 }): &i64 { return &p.x; }`, `*px(&c) = 5;` is EN0609 (H42). `this` is never rebound.
- **Read-only marks (N5).** A reference slot is marked if it may hold a reference from: a `const` local, anything reached from it through an owned path (field, element, `Box`), or a by-value parameter without `let`; a top-level `const`, a string literal (C13), or a bracket literal of constants made static (5.4); a `readonly` field, even in a constructor; a reference field declared `readonly &`, a tuple part declared `readonly`, or a reference to a tuple field, or to a part of one at any depth, whose place contains such a part at any depth, a nullable payload included, as `&this.t` does and as `&this.t[1]` does when part `1.0` is one, while a reference to a sub-tuple that contains none is not marked (4.3), and anything reached through it; a raw-derived `&*p`, except as a returned reference: a body containing `unsafe` returns it under the signature-default sources (5.4), so its result is as changeable as they are, and the library's `public const slice(a, b?): &Slice<T>` hands out a writable view of a `let` array, while under rule 3, with no reference parameter and so no source, it keeps its mark, as a reference to a static does, so writing through the result of `public function cell(i: isize): &u16`, which returns `&*p.add(i)` into an `unsafe let` array, is EN0616, with `` help: take a `&` parameter that owns the storage ``, while the view that `Slice<T>.fromRaw` makes carries no mark where it is made and used, since its `unsafe` caller takes on the obligations of 5.9 (8.2), and a body that returns it under sources, as the library's `slice` and `splitAt` return views into `this`, hands it out as changeable as they are, except as the returned reference of a function with no source, where rule 3 keeps a read-only mark on it, as on a returned `&*p`, in an `unsafe function` as in a safe one: with `private unsafe let grid: u16[4];`, writing through the result of `` public function cells(): &Slice<u16> { unsafe { return Slice<u16>.fromRaw(grid.asPtr(), 4); } } `` is EN0616 with the same help, so two calls never give two writers, while a `Screen` class that holds the base pointer and returns the view from a method, with `this` as its source, hands out a writable one that holds the screen; a call result whose callee's result is read-only, or whose source argument is marked; a result declared `readonly`, any result that may point at a constant or static, and a `&string` that may be a part of a string: one made by `slice`, or one a function returns, alone, at the top of `| null` or as a tuple part, from a `&string` or `&string | null` reference it only reads (5.4). Repointing replaces the mark, and joins take the union. Writing through a marked slot is an error naming the mark's origin: EN0608 for a `const` root or a top-level `const`, EN0609 for a `readonly` field, EN0616 for a read-only result, `readonly` ones included, a reference field declared `readonly &`, a tuple part declared `readonly` or a tuple field with such a part, a part of a string or a string literal. So is passing it to a parameter that writes (EN0614 for the receiver of a method that changes the object, whatever the mark's origin, with a help that names it: with `public view(): readonly &i64[]`, `s.view().push(99)` is EN0614, with `` help: to allow this, remove `readonly` from the return type of `view` ``), or to a source parameter whose result is written through, which is one report, at the call, with the mark's code: with `public book(id: i64): &Book`, `lib.book(1).title = "Dune";` on a `const lib` is EN0608, `` `book` hands out a writable reference, but `lib` is `const` ``, with `` help: declare it `let lib` ``. Statement temporaries are not marked, so `make().push(1)` and `*id(&5) = 1` compile. A `for...of` binding carries its source's mark: the bind is a `&` of the source's element, and the binding is marked exactly as any `&` of that place would be, so it is marked over a `const` root or anything it owns, a top-level `const`, a `readonly` field, a reference field declared `readonly &`, a tuple part declared `readonly`, a read-only, constant-pointing or raw-derived result, or a source evaluated once that is any of these, while over `&q` for a `let q` it is not, so such a loop may still write the elements of `q` (5.6). The mark records that it came through that loop's bind. A loop whose binding is written through writes through its source, which is checked at the loop's start as an argument to a parameter that writes is: a `const` root or a top-level `const` is EN0608 (`for (const t of &TABLE) { *t = 0; }`), a `readonly` field EN0609, and a read-only result, a reference field declared `readonly &`, a tuple part declared `readonly` or a tuple field with such a part, one that may point at a constant, or a raw-derived `&*p` EN0616, each reported once, at the source: a write through a slot whose mark came through a loop's bind, or such a slot passed where a write is found (N3), is that loop's report at its source and is never reported again at the write, so `let keep: &i64 | null = null; for (const x of &K) { keep = x; } if (keep != null) { *keep = 0; }` over a top-level `const K` is one EN0608, at `&K`. Every other reading of the mark sees it as any mark, so a function that returns the binding, or a call result whose source argument is the binding, is read-only: with a `firstOf()` that loops over `zeros()`, a function that may return a constant, and returns `x`, `*firstOf() = 1;` is EN0616, `` `firstOf` returns a reference that may point at a constant ``.
- **Raw pointers** end the rule: a `*T` field read through a read-only reference is copied out as a raw pointer, and writing through it needs `unsafe`.
- **Writing through a reference.** `*y = v` writes a whole value through `y`, and `y = &z` repoints `y` if `y` is `let`. `y = v` with `y: &T` and `v: T` is EN0422 with a fix-it to `*y = v`, and so are `y += 1` and `y++`. Field assignment `y.f = v` and method calls need no `*`, and reading needs none (4.5). A reference parameter is never repointed: `let` on it means the function may change what it points to, which callers see even if the body only reads, so with `function fill(let buf: &Slice<u8>): void { console.log(buf.length()); }`, `fill(&data)` on a `const data` is EN0608 (`` `fill` can change `buf`, but `data` is `const` ``).

These rules cover a `const` that holds a reference, with nothing added for it:

```ts
let x = 12;
const y = &x;  // valid: `y` cannot be reassigned, and `x` is frozen while `y` is live
console.log(y);  // the last use of `y`, so the loan ends here
x = 13;  // fine now
```

Writing `y = &z;` is EN0613, and `x = 13;` above the last use of `y` is EN0706. A `const` binding that holds a reference may also write through it:

```ts
let n = 12;
const r = &n;  // `r` writes below, so this borrow is exclusive
*r = 13;  // valid: the write goes through `r` and does not change it
console.log(n);  // prints 13; the loan ended at the last use of `r`
```

Reading `n` between `const r = &n;` and `*r = 13;` is EN0708, because writing makes the borrow exclusive. `const k = 12; let w = &k; *w = 13;` is EN0608 (`cannot mutate immutable data`, naming `k`); repointing `w` to a `let` value first compiles, because a `let` reference to a `const` value may be repointed. `bump(&n)` needs `let n`.

### 4.12 Modules

One file is one module; `foo.test.en` is an extra part of module `foo.en` and sees its private items, the `private` top-level declarations, though never the `private` members of its classes (4.3), and tests live only in such parts (EN1112). Every top-level declaration states `public`, which lets other files import it, or `private`, which keeps it to its own module, `.test.en` part included; a missing visibility is EN0226. Functions among a program's top-level statements are local and take none, and a file with top-level statements cannot be imported (EN0312). Import paths resolve relative to the importing file, and cycles are EN0304; a test part is a unit above its module, so its imports do not count toward EN0304. Checking is modular and code generation whole-program (N14). Each module's interface file holds the contracts of everything reachable from its `public` items and the post-inference MIR of every reachable body. `enrang check` checks a caller only against its imports' contracts, and `enrang build` may use the MIR instead of a dependency's source; code generation runs from MIR over the whole program, with one entry file and no object files or linker step between Enrang modules. An interface file is used only while it is fresh, which covers its own contents, the module's source and every module below it, imported directly or through others: a module's API hash also covers the API hashes of its direct imports, as Rust's crate hash covers its dependencies', so a change anywhere below a module reaches its key. A module whose stored code reads a class that it reaches only through another module, as the result type of an imported function, therefore goes stale when that class's fields are reordered, and a warm build matches a cold one. The command's mode is no part of freshness: a `.test.en` part is a unit above its module, checked from its own source and never stored, so a module's interface file is the same under `build`, `check` and `test` (12.4), and the file that `enrang build` wrote for a module shipped without its source serves `enrang check` and `enrang test` too. Nor are the CPU level and the float strategy: nothing an interface file stores depends on them, since its MIR, contracts, flags, view facts, layouts and API hash are the same at every `--cpu` and `--float` (layouts depend on the target, which is part of the key), so `enrang build --cpu=i386` and `enrang build --cpu=sse2 --float=sse2` write the same bytes. Instead, phase 4's checks that read the level or the float strategy, EN0901 and EN0910 among them, are never cached: every command that reaches phase 4 runs them over the MIR of every module in the program, stored or freshly built, so a library shipped without its source and written at `--cpu=i586` serves a build at `--cpu=i386`, where an `asm("cpuid")` in its code is EN0901 at its stored span, with a note naming the interface file, and `check --cpu=i486` then `check --cpu=i386` reports the same EN0901 both ways. An interface file is never trusted: whenever a module is used from one, the compiler checks its stored code, once per module, before anything uses it, as Java's verifier and WebAssembly's validation check the code they load. It verifies the stored MIR: its types against the current declarations of everything that code uses, and its `unsafe` boundary (EN0801, EN0803, EN0907) against the `unsafe` regions the stored MIR records, a call to an intrinsic whose declaration is `unsafe` included. It reruns every phase-2 rule whose verdict the borrow check, monomorphisation, code generation or the VM rely on, over the file's stored declarations and bodies and against the current declarations, not a fixed list, so it covers at least member and item visibility (EN0308, EN0311) for every field, method, constructor and item the stored code names; the class rules EN0416, EN0418, EN0442, EN0443, EN0444, with the equal type, `readonly` and visibility of a field override (4.3), EN0445, EN0446, EN0457, EN0458 and EN0460; bound satisfaction (EN0419) for every type argument of the stored code, and the view and string checks (EN0401, 4.10), against the facts the check computes again, for every one bound to a view or to `string`, and the string clause of satisfaction for every satisfaction the stored code relies on (4.4); the construction rules EN0433, EN0447 and EN0448 for every stored `new` and named form; and the position rules EN0701 to EN0703 and EN1006 for every type in the stored declarations and in every local, field, element and generic argument of the stored code. It also checks that every run-time check the language requires is present before the operation it guards: a bounds check before every index into an array or a view, a tag check before every read of an enum case's fields, the exact-class check of 4.3 before every whole-object move, copy or write that needs one, a call through a method table only where 5.4 and 4.10 make one under the current declarations, and a store of the method-table pointer only in a class that has one. It then recomputes each contract and each class's flag from the stored MIR, following 5.9 from those same regions, and each view fact (4.10), and reruns phase 3 on it: the borrow check, the narrowing check (N2) and every comparison that reads contracts or flags, EN0615 for each stored override, satisfaction, bound and `fn` coercion against the current declared contracts, EN0714, and EN0418 for `implements Copy` against the recomputed flags. The check runs in every build of the compiler, release builds included, and costs compile time only. A module that has an interface file but no source cannot be rebuilt, but it can be rechecked: when its file is stale only because contracts changed, that is, when every item its stored code uses, from whichever module, types reached through results, fields and re-exports included, keeps every fact of its declaration apart from its contract and its flag (4.3), the compiler verifies the stored MIR as above, recomputes the module's contracts and flags from it against the new contracts and reruns phase 3 on it, its comparisons included, as above, and if that passes, it writes a fresh file. A borrow or contract error that this recheck finds is reported with its ordinary code at the stored span, with a note at the interface file, which names the file, naming the changed import: `` note: this module has no source; it was rechecked against the new `lib` ``. When a used item's declaration changed in any other way, its type, its layout or its existence, `final` or `abstract` on it or on one of its methods, its set of methods with their signatures and which of them can be overridden, an interface's members, a bound, which of a function's type parameters may stand for a view or for `string` (4.10), a visibility, `readonly`, `@requires` or a constant's value, which code copies where it reads it (4.9), or any other part of the key is stale (the compiler, the target, or the file's own contents), the compile stops with EN0315, as Rust's E0460 does. Stored code that fails the verification, in a fresh file or in one being rechecked, and a fresh file whose stored code does not match its own recorded contracts or view facts, or does not pass the borrow check, are EN0316, naming the file: `` the interface file of `lib.en` says `grow` only reads `xs`, but its code pushes to it ``, or, for a stored `poke` whose raw write lies outside every recorded `unsafe` region, `` the interface file of `lib.en` writes through a raw pointer outside `unsafe` in `poke` ``, or, for a stored `at` that indexes `xs` with no bounds check before it, `` the interface file of `lib.en` indexes `xs` in `at` with no bounds check ``, with `note: the file was not written by this compiler, or it was changed afterwards`. A file that this compiler writes never fails the visibility check, because a named form leaves the fields it does not name to their own class's module (4.3), so no stored code writes another class's `private` field. So the guarantees of section 5 hold for any interface file, one shipped without its source included: its types, its visibility, its `unsafe` regions, its run-time checks, its class, construction and position rules, its contracts and its borrows are all checked, never trusted. Imported class names carry privacy with them; a `private` field stays private to the class, and a `protected` one to the class and its subclasses. The prelude (section 8.1) is implicit. `import * as vga from "./drivers/vga";` binds a namespace, and `public import { Keyboard } from "./drivers/keyboard";` re-exports. Default exports, a default import and `require` are EN1009.

**Binding rule, normative.** `import { x } from "p"` binds the `public` item `x` of `p`, or one that `p` re-exports; otherwise it binds a namespace for the child module `p/x`, for user folders as for `os`: `import { serial, vga } from "./drivers";`. `import * as n from "p"` binds a namespace for `p` itself. A namespace appears only to the left of `.`, in expressions and in type paths, and locals shadow it. Importing a `private` item is EN0311 (`` `Helper` is private to `user.en` ``), and a name that is neither an item of `p` nor a child module is EN0305. A re-export resolves to the item it names, and the cycle check follows re-exports. The hosted `os` root has children `os`, `fs` and `stdin`. On freestanding targets `os` selects `os/none`, with children `vga`, `serial`, `idt`, `pic`, `pit` and `cpu`. `core` has children including `cpu` and `port`. The prelude adds `mem` and `ptr` as namespaces.

### 4.13 Array spread

`[x, ...a, y, ...b]` builds a new `T[]`, and never a `T[N]`. Each element of a spread source is cloned, so `T` must satisfy `Clone`, checked once generically. That is a deep copy, unlike JS's shallow one, because a value has one owner, and the `...` is the visible token that keeps O5 true.

**Sources.** `T[]`, `T[N]`, `&T[]`, `&T[N]` and `&Slice<T>`, each as a place or an rvalue, including a narrowed payload. The operand is a shared-borrow context and not a value context (O1), so it does not move and needs no `&`.

**Typing.** Each operand is checked with no expected type. One `&` is peeled, and the rest must be `Array(U)`, `Fixed(U, _)` or `Slice(U)`. `U` then unifies with the element type of the literal. No coercion applies to a spread operand: an expected `U[]` gives `U` to the plain elements only. The `Clone` check runs at the end of inference, so `let q = []; const c = [...q]; q.push(1);` works.

| Form | Report |
|---|---|
| `let q; const c = [...q]; q = [1];`, where the operand's type is still unknown | EN0410 at once, as for a member access (4.7) |
| `[...5]`, `[..."abc"]` (there is no character type), `[...o]` with `o: T[] \| null` not narrowed, `[...b]` with `b: Box<T[]>` (help `...*b`) | EN0438 |
| A source whose elements do not satisfy `Clone`, a `T` with no bound included | EN0438, with a fix-it to `<T extends Clone>` where it applies (G22). A failed `where` on the generated call reports this too, never EN0419 |
| `[...move a]` | EN0228: a value already moves when there is no `&`, and a spread operand does not move at all |
| `const a: i64[3] = [...b];` | EN0401, with a note that a spread builds a growable array |
| `const n: (i64 \| null)[] = [...xs];` with `xs: i64[]`, and `[0, ...xs]` at that type | EN0401 with a `.map` help. The element `0` alone coerces by C06, and nothing nests |
| `[...a, ...b]` with different element types | EN0401 |
| `...` in a `ConstExpr` | EN0412 (4.9) |
| `...` anywhere but an array-literal element | EN1013 (3.4) |

**Evaluation.** Left to right, and each spread clones at its position, so `[...a, f(&a)]` copies `a` before the call and `[f(&a), ...a]` copies the call's effect. The length of the result is not computed in advance. A `?` or `return` in a later element drops what was built. A source's borrow ends when its copy is made, because the result holds no references, so spread adds no borrow rule: `[...a, f(&a)]`, `a = [...a, x]` and `for (const j of [...queue]) { queue.push(s); }` are accepted, and `const r = &f; const c = [...f]; r[0] = 1;` is EN0708. The result is an ordinary `T[]`, so EN0820 and EN0824 apply as usual.

### 4.14 Default parameters and overloads

**Defaults.** A parameter may have a default, as in TypeScript: with `` function greet(name: &string, greeting: &string = "hello", end: &string = "!"): string { return `${greeting}, ${name}${end}`; } ``, `greet("Ada")` returns `hello, Ada!`, `greet("Bo", "hi")` returns `hi, Bo!` and `greet("Cy", "hello", "?")` returns `hello, Cy?`. A default is evaluated at each call that leaves it out, never once, and may use earlier parameters: `` function span(start: int, end: int = start + 10): string { return `${start}..${end}`; } `` returns `5..15` for `span(5)`. A default belongs to the function's body: it runs as the body's first statements, `if (p was left out) { p = d; }`, in parameter order, in a constructor right after its class's field initialisers and before its parameter properties are assigned (4.3), and a call only passes which parameters it supplied, so the contract inferred from the body (5.3, 5.4) sees what a default does, and an interface file needs no default expression. With `function visit(xs: &i64[], step: () => void = () => { xs.push(0); }): void { const head = xs.first(); step(); console.log(head); }`, `xs` is Write, so `visit(&v)` on a `const v` is EN0608, and `const head = xs.first();` is EN0715, `` `xs` is locked while `step` will still be used ``, because a closure parameter given an arrow by its default holds that arrow's captures, as a local holding an arrow does (5.5); a default that calls a function writing an earlier parameter, as `n: isize = grow(xs)` does, makes that parameter Write the same way. As an `fn` value, a function with defaults takes every parameter: `const g: fn(name: &string, greeting: &string, end: &string) => string = greet;`. Only the last parameters may have defaults, because there is no `undefined` to skip one: `function span(start?: i64, end: i64)` is EN0229 (`` `end` has no default, so it can't follow `start`, which has one ``). `x?: T` on a parameter means `x: T | null = null`, as on a field (4.3), and `?` together with a default is EN0227. With a `?` parameter instead, `` function greet(name: &string, greeting?: &string): string { return `${greeting ?? "hello"}, ${name}!`; } `` returns `hello, Ada!` for `greet("Ada")`, `hi, Bo!` for `greet("Bo", "hi")` and `hello, Cy!` for `greet("Cy", null)`. A closure parameter may be optional too: with `function onKey(key: u8, handler?: (k: u8) => void): void { if (handler != null) { handler(key); } }`, `handler` is `((k: u8) => void) | null = null`, `onKey(65)` prints nothing and `onKey(66, k => console.log(k))` prints `66`. The arrow converts by C12 and then C06 and holds its captures for the call, as any closure argument does (5.5), and `| null` at the top of a closure type is not a nested closure type (EN0705). Calling `handler` needs narrowing: an unnarrowed `handler(key)` is EN0428, because a nullable value cannot be called. A type that is already nullable as written gains no second `null` (4.3): `width?: i64 | null` means `width: i64 | null = null`, on a parameter as on a field, so `width ?? 8` is an `i64`, and `greeting?: &string | null` means `greeting: &string | null = null`.

**Overloads.** A function name may have several overloads, each with its own body: with `` function describe(n: int): string { return `number ${n}`; } `` and `` function describe(s: &string): string { return `text ${s}`; } ``, `console.log(describe(42), describe("hi"));` prints `number 42 text hi`. A call picks the overload whose parameter types match its argument types exactly, since there are no implicit numeric conversions; the reference chains of 4.5 still apply, so `sum(&f)` for `const f: i64[3]` picks `sum(xs: &Slice<i64>)` over `sum(xs: &Slice<f64>)` by C18. A literal follows its default, so with overloads for `int` and `i64`, `describe(5)` picks `int`. Among the overloads a call matches, three preferences decide, in this order: (1) a non-generic overload beats a generic one, as in Swift and Java; (2) within the same kind, an overload that needs no chain beats one that needs a chain; (3) among generic overloads still tied, the more specific one wins, where `F` is more specific than `G` when every parameter type of `F` can be passed to `G`'s, `G`'s type parameters bound by `F`'s types, but not the reverse, as C++'s partial ordering and Swift decide, so `&Slice<T>` is more specific than `&T`. So a special case written without type parameters always beats a catch-all generic one: with `describe(a: &Animal)` and `describe<T extends Animal>(a: &T)`, `describe(&rex)` on a `Dog` runs `describe(a: &Animal)`, which needs C21, and with `total(xs: &Slice<i64>)` and `total<T>(x: &T)`, `total(&arr)` on an `i64[3]` runs `total(xs: &Slice<i64>)`, which needs C18. With `show<T>(x: &T)` and `show<T>(x: &Slice<T>)`, `show(sector.slice(0, 2))` runs `show<T>(x: &Slice<T>)`, the more specific, and `show(&sector)` on a `u8[4]` runs `show<T>(x: &T)`, the only one that needs no chain. These preferences never read whether a type parameter may stand for a view (4.10), which is known only once every body is typed. A call that no overload matches is EN0451, which lists the candidates, and so is a call that two or more overloads still match equally after these preferences, which lists those overloads: with `f<T>(a: &T, b: &Slice<i64>)` and `f<T>(a: &Slice<i64>, b: &T)`, `f(&a3, &b3)` on two `i64[3]` needs one C18 step in each, and neither is more specific than the other, so it is EN0451. Overloads that differ only in their return type, or that one call could match through a default parameter, are EN0450 at the declaration. A subclass's overloads add to the ones it inherits, with no hiding, and an override matches one overload exactly (4.3). Importing a name imports all its overloads, and symbol names include parameter types. The bare name of an overloaded function needs an expected type: `const f = describe;` is EN0410, and `const f: fn(n: int) => string = describe;` picks one (4.7). Operators are not overloaded, beyond `==` through `Eq` (4.4).

## 5. Ownership and borrowing

Everything here is checked on MIR, generically, before monomorphisation, and is independent of target. The rules contain no runtime component: no reference counts, no borrow flags, no GC.

There is one reference type, `&T`. Whether a borrow reads or writes is inferred from the code that uses it, and the compiler enforces the inferred requirement at every call: `function read(x: &i64): void { console.log(*x); }` takes a shared borrow, and `function update(x: &i64): void { *x = 42; }` takes an exclusive one. Three guarantees hold together:

1. **Memory safety.** Conflicting borrows are compile errors. This covers programs with no `unsafe`, given a correct library (5.8); inside `unsafe`, a permission is a reviewable promise (5.9).
2. **NLL.** A borrow ends after its last relevant use, not at the end of its scope.
3. **Modular checking.** What each function does with its references is stored in its module's interface file, so a caller is checked against its callees' contracts and never reads their bodies; the file itself is checked against its stored code when it is loaded (4.12).

The rules that realise them are numbered N1 to N14. N1 (phase order) is in 4.4 and 4.7, N2 (narrowing) in 4.8, N5 (read-only marks) in 4.11, N7 (contract stages and the type of `this`) in 4.3, 5.3 and 5.4, N8 (call-site loans) in 4.5 and 5.3, N10 (declared contracts) in 4.4 and 4.5, N11 (compiler-called roles and compiler-inserted calls) in 4.4, 5.3 and section 7, and N14 (interface files) in 4.12. The others are in this section: N3 and N4 in 5.3, N6 in 5.4, N13 in 5.5, N9 in 5.6 and N12 in 5.9.

### 5.1 Reference placement (R1, R2)

- **R1.** A reference type `&T`, `&I` for an interface `I` included (4.1), with or without `| null` at the top, may appear only as the type of a parameter, local, temporary or return value, of a `private` field of a borrowing class, or of a part of a tuple, which makes the tuple borrowing (below). It is forbidden in any other field, in array elements, enum case fields and generic arguments (EN0701). A closure type, with or without `| null` at the top, may be written only as a parameter type (EN0705).
- **Borrowing classes.** A class with a `&` field is a borrowing class and follows the rules of a reference. It lives only where a reference can: in locals, parameters, return values and fields of another borrowing class, so a class holding one is borrowing too (`Parser { lx: Lexer }`). An array, an enum case and a generic argument cannot hold one: `let all: Lexer[] = [lx];` is EN0701, `` an array can't hold a `Lexer`, because `Lexer` holds a reference ``, with the label `` `Lexer` borrows through its field `src` ``. A reference field must be `private` (EN0701), and a field whose type is a borrowing tuple, or contains one other than inside a borrowing-class field, as `[&i64[], i32] | null` does, is a reference field too: it makes its class borrowing, and it sets the class's flag (4.3) unless every reference part at every depth, a nullable payload included, says `readonly`, because through `this` the tuple's parts are behind a reference, as for any tuple reached through one (N3 (e)). A borrowing value keeps two loan sets: its *read set*, the loans stored into its fields declared `readonly &`, as `private src: readonly &Slice<u8>;`, never into a tuple part, which it only reads through, and its *main set*, every loan stored into it, the read set's included, which is what a reference read through any other reference field holds. One flag, inferred from every body that sees its `private` fields, its methods, constructors and destructor and the arrows nested in them, and set as well when its base class's is, says whether the class writes through its reference fields (4.3); a `readonly &` field never sets it, and nor does a tuple field whose reference parts all say `readonly`, at every depth, since a reference to it is read-only as a whole (4.3). When the flag is off, a reference returned from a reference field carries that field's loans and no loan on the object, as long as the caller does not write through the result, so several results of `lx.next()` on a local `lx` can be kept while it runs again; a call through a `&Lexer` also holds the object, since an override of `next` may return into it (5.4). Otherwise the result also holds the loan on the object, exclusive when the result is written through, as Rust ties such a result to `&mut self`, except a result that reaches the object only through `readonly &` fields, which holds, for the object, the read set alone, whatever the flag and whatever its other sources, as Rust's `-> &'a T` from a `&'a T` field does: it holds no loan on the object, so writing, moving, dropping or repointing the object leaves it valid. To keep this sound, a `readonly &` field of a class whose flag is set takes no reference reached from another reference field of the same object that is not `readonly &` (EN0616, 4.3), so nothing in the object writes through a loan of its read set. A borrowing value returned by value, as from a `public rest(): Lexer` that builds a `Lexer` over the rest of the text, carries only what the fields hold when the class does not write through them, whatever the caller does with it, because writes through it go through its own class's methods. Such a value, and one copied or moved out of a field, keeps its whole set as its read set, because no contract says which of a result's loans are read-set loans, so a result it gives through its `readonly &` fields holds everything it holds. For the same reason, where the class's flag is set, a store into a `readonly &` field of such a value, or of one taken by value as a parameter, treats every loan the value holds as held by its other reference fields, so storing there a reference that holds any of them is EN0616, as `w.src = w.dst;` is on a `w` returned by a call, except by a call that only narrows the value's `readonly &` fields from themselves (R2); a value its constructor built treats exactly what went into its other fields so, together with a parameter stored into a `readonly &` field that the constructor writes through as well, as when it stores the two parts of one `splitAt` one into each field, while a parameter it only reads never reaches a field written through (N3 (e)), and a store of a by-value borrowing class parameter, or of an Own `this`, as `*this = u` makes in a `reset(u: Copier)`, counts everything it stores so, since `u` may carry what its own other fields hold (`TESTING.md` `FV-02-reset`); and a value nested in a field or tuple part treats every loan of the value that holds it so, by the nested value's own class, however the store reaches it, through a reference to the nested value included (`TESTING.md` `FV-02-nested-ref`). The flag that decides this for a local, a temporary or a by-value parameter is that of the value's own class, which it holds exactly (4.3), whichever class declares the field or the method that stores into it, so an inherited setter called on a subclass value is checked with the subclass's flag. A tuple with a reference part is a borrowing tuple by the same rule, so a function can return two parts of one array; a `splitAt` written in Enrang returns them read-only, because both come from one parameter and may overlap (5.4), while `core`'s `splitAt` gives two writable parts (8.2).
- **R2.** A reference's pointee holds no reference: `&&T` and `&(&T | null)` are EN0702, written or inferred, as `const p = &r;` with `r: &i64 | null` is. The one exception is a borrowing value, nullable or not: `&lx`, `&w` with `w: Lexer | null`, or `this` inside a `Lexer` method, refers to something that holds references, and the checker infers which functions store a parameter into a borrowing value: into `this` (`setSrc(s: &string) { this.src = s; }`), or into the value behind another parameter, as a `reset(lx: &Lexer, s: &string)` that calls `lx.setSrc(s)` does, however the reference to that value was obtained, from a call or through a `&Lexer` field included. The stored argument's loans then join that value's main set in the caller, and its read set as well when the field that receives them is declared `readonly &`. A store that took only what another borrowing value's reference fields hold, as `copyFrom(o: &Lexer) { this.src = o.src; }` does, adds those loans and not the loan on `o`, as long as `o`'s class does not write through its reference fields, as for a result (above); otherwise it adds the loan on `o` too, so `o` stays borrowed while the value holds what was stored (4.3). A store that took only what the stored value's `readonly &` fields hold, as a `skip` that narrows its own field with `this.src = this.src.slice(1, n);` does, adds only that value's read set, whatever its class writes, as a result reached only through such fields does (5.4), and when it stores that value into itself, as `skip` does, the caller does not check it against what the value's other fields hold, since it moves only what those `readonly &` fields already reach, so such a method compiles and can be called in a class whose flag is set, on a value that a call returned too. When the class receiving the store writes through its reference fields, the stored argument is borrowed for writing (N3 (e)), unless the field that receives it is declared `readonly &` (4.3). Section 5.4 gives the rules for stores.

```ts
private class Lexer {
  private src: &string;
  private pos: isize;

  public constructor(src: &string) { this.src = src; }

  public next(): &string | null {
    if (this.pos >= this.src.length()) { return null; }
    const start = this.pos;
    this.pos = this.src.length();  // a sketch: the rest of the text is one token
    return this.src.slice(start, this.pos);
  }
}
```

`let lx = new Lexer(&source);` borrows `source`, which cannot change while `lx` is alive (EN0706). Since `lx` is a local of type `Lexer`, it holds exactly a `Lexer`, and `const a = lx.next(); const b = lx.next(); console.log(a, b);` compiles. `Lexer` has a constructor because a `private` field with no default cannot be set from outside (4.3).

### 5.2 Moves and Copy

- **O1. Value contexts move.** Reading a place of non-Copy type in a value context moves it: initialisers, assignment right-hand sides, by-value arguments and receivers, `return`, class, object and array literals, a `for...of` source written without `&`, and destructuring of an owned value (5.6). Copy types copy. An assignment's value is its target place read after the store (3.5), and a use that does not keep it borrows the place as the same use with the place written by name would (O7, N8), shared, or exclusive where it is an argument to a parameter that writes or a source of a write-live result, for as long as a slot holding the loan is live (O10), which for a use that keeps nothing is the end of that use's temporaries (D2), at the end of the statement or right after a condition, so `console.log(s += "!")` moves nothing out of `s`, while a use that would keep it, a binding's initialiser, the right side of another assignment, a by-value argument, a `return`, an element or field of a literal or a capture by value, is EN0621 unless the place is Copy, since it would make a second owner (3.5). `const b = a` moves; it is not an alias. So with `function keep(list: &User[], u: User): void`, `keep(&list, u); console.log(u.name);` is EN0601, `` `u` was moved into `keep` ``, with the label `` `u` moves here, because `keep` takes `User`, not `&User` `` and the helps `` if `keep` only needs to look at it, change the parameter to `u: &User` `` and `` to keep your own, pass a copy: `keep(&list, u.clone())` ``. The subject of `match` is not a value context (6). The operand of `...` is not one either. It is a shared-borrow context: a place auto-borrows, a reference is copied with a shared loan (O7), and an rvalue becomes a statement temporary. Plain array elements still move.
- **O2. Places.** A path is a local, `this`, or a path followed by `.field`, `*deref`, `(as Variant).field`, or `[*]` (all indices alias). The one exception is the bind of a `for...of` loop: every turn and run of a loop binds its element at one bind site, and the loop's own head, its tag checks and its length read, and its own bind, its checks and its borrow, skip the loop's hold and that site's loans, so the binds of one run never conflict with each other or with that run's own head. Each loan of a site carries one of three keys: *this turn*, *earlier turns* of this run, or *earlier runs*. A bind first renames the site's this-turn loans, in every slot that holds them, to earlier turns, and then takes its own loan under this turn's key; the loop's pre-header renames the site's this-turn and earlier-turn loans to earlier runs, and makes plain every loan marked via the bind of that loop (below), since evaluating the source again, or repointing it between runs, may end an earlier run's site loans while the loans its bindings took from the source remain. Everything else treats the site's loans as `[*]`: they overlap every other access to the source, the binds of other loops and the hold that another loop or a later run of the same loop takes at its pre-header included, so a binding kept from an earlier run meets the next run's hold there (5.6). Where one loan is compared against another, as N6's part test does (5.4), two loans of one site are disjoint only when one has this turn's key and the other an earlier turn's, because one run binds each element once and its hold keeps the source from changing in between; two loans of this turn, two of earlier turns, and a loan of an earlier run against any other of the site overlap. A bind also gives its binding what its source holds, the loans the loop keeps for a source evaluated once or those of the reference slot or reference field a source path goes through, among them the loan on a caller's data behind a reference parameter, and each of these carries the mark *via the bind* of that loop; the same loan reaching a binding any other way, by an assignment from another path or by a `&` of the parameter itself, is plain, and where a marked and a plain copy of one loan meet, or two copies marked by different loops, at a join or in one slot, it is plain, wherever they meet, a tuple or object literal and the renames at a bind and at a pre-header included; a bind never marks a loan of its own site, which that site's turn keys decide, unless another loop's bind marked it, as an inner loop over a binding marks the outer loop's loan of this turn, and then that loop's site loans decide it like any loan that bind marks (`TESTING.md` `TK-03-inner-pair`). Each parameter's key in a slot likewise records whether every way it came brought a loan that borrows through that parameter, and a copy that came without one, wherever two meet, makes it count as the whole parameter (N6). In that comparison, a loan that both sides hold only via the bind of one loop is decided by the keys of that loop's site loans that they hold, as above, and a side that holds none of that site's loans, as a binding may once its loop's source was repointed, overlaps, so a loop over `xs.slice(1)` or over a copy `const r = xs;` forms the same writable pairs as a loop over `xs` (5.6); only the pair of one loan that both sides hold via that bind is decided by the site's keys, and every other pair, a plain loan of one side against a loan the other holds via the bind included, is compared by its path, since a plain `&xs[1]` and a binding of a loop over `xs.slice(1)` may be the same element, so nothing is left out of the comparison. A move path contains only field projections on owned values; moving through `&`, a raw pointer, `*box` or `[*]` is rejected (EN0603, EN0605, EN0604). `xs[i]` of non-Copy type in a value context is EN0604, offering `&xs[i]`, `.clone()` and `.remove(i)`.
- **O3. Definite init.** Init state per move path is a forward dataflow fact; a use where a path is not definitely initialised is EN0601 (it was moved) or EN0602 (never assigned). A `let` local declared without a value starts at its type's default when the type has one (numbers `0`, `bool` `false`, `string` `""`, arrays `[]`, `T | null` `null`, raw pointers address 0), so `let n: i64;` is `0`, and `function grade(s: i64): string { let g: string; if (s >= 90) { g = "A"; } return g; }` returns `""` for 30. Only a local of a type with no default (a class, an enum, `Box`, `Result`, a reference) can be EN0602. A move inside a loop reaching itself is EN0611, and so is a move in a `for...of` body that reaches the read of the source at the head or the bind of a later turn, except that a move of the loop's own held source is reported only as EN0709 (5.6). Assigning a whole path reinitialises it. Assigning `x.f` is legal only when `x` is definitely initialised, apart from fields moved out of it, and then reinitialises that exact field. So after `take(p)`, `p.first = c` is EN0601, for classes with and without a destructor alike: no value is ever reassembled field by field. A constructor's `this` is the one exception (4.3). A `const` always has a value (EN0116); a value decided by branches uses a ternary or a `match` expression, as in `const label = score >= 60 ? "pass" : "fail";`.
- **O4. Copy.** Copy types are: numerics, `bool`, `void`, `never`, `&T`, raw pointers, `fn` pointers, payload-free enums, `T[N]` and `T | null` of Copy, anonymous object types and tuples whose every field or part is Copy, and classes declaring `implements Copy`, which is never inherited: a subclass of a Copy class is Copy only if it declares `implements Copy` itself. Copying a reference never moves it; the copy's loans follow O7. A class with a destructor, its own or one of a base class, cannot be Copy (EN0418), nor can a borrowing class that writes through its reference fields, since its copy would be a second writer through them (EN0418, 4.3). A copy of a borrowing tuple copies each reference part by O7. `Result` is Copy when both arguments are.
- **O5. Clone** is always explicit: `.clone()` or `...`. There is no implicit deep copy.
- **O6. Evaluation order.** Left to right. A call evaluates: receiver value operand, arguments left to right, then takes the receiver's auto-borrow **last**. So `a.push(a.length())` needs no two-phase borrow. `i++` and `i--` give the old value and `++i` and `--i` the new one, and operands still run left to right: `let i = 0; const a = [i++, i++, ++i];` gives `[0, 1, 3]` and leaves `i` at 3. In an assignment, the target is evaluated before the right side, left to right, as in JavaScript. That covers its index operands, so `let i = 0; a[i] = i++;` writes `a[0]`, and the calls in it, so in `*slot(&xs) = val(&xs);` `slot` runs first, and the result that the assignment writes through keeps `xs` borrowed for writing, which makes `val(&xs)` EN0708, while `const v = val(&xs); *slot(&xs) = v;` compiles. A compound assignment on a place of Copy type then reads the old value, still before the right side: `let x = [1]; x[0] += (x[0] = 5);` leaves `x[0]` at `6`, as JavaScript does. For a non-Copy place, such as a `string` that `+=` appends to in place (section 6), an early read would be neither a copy nor a legal move, so this order covers Copy places only. A compound assignment to a non-Copy place reads nothing early: it reserves the place from its target's operands until the store, takes it for writing only at the store, as a receiver's borrow is taken last, and then updates the place where it is, as Rust's two-phase borrow of the target does. While the right side runs it may read the place, so `s += "-".repeat(s.length());` and then `s += s.toUpperCase();` take a `let s` from `ab` to `ab--` and then `ab--AB--`, as JavaScript and Rust do. Only the place's own borrow waits: a call in the target that hands out the place for writing, as in `*slot(&xs) += val(&xs);`, borrows `xs` for writing at that call, as in the plain assignment above, so `val(&xs)` is EN0708 there too. A right side that changes the place or borrows it for writing is EN0707, and one that moves it is EN0709 (O11): with `function reset(t: &string): &string { *t = "b".toString(); return "!"; }` and `let s: string = "a".toString();`, `s += reset(&s);` is EN0707 at `&s`, with `` help: run the right side first: `const r = reset(&s); s += r;` ``, after which `console.log(s)` prints `b!`, and `names[0] += take(&names);`, with a `take` that clears `names`, is EN0707 the same way. A read whose loan is still live at the store, because the append uses what it read, is EN0708 at that read: `s += s.slice(0, 1);` is EN0708 at `s.slice(0, 1)`, and `s += s;` at its right side, with `` help: append a copy: `s += s.slice(0, 1).toString();` `` (8.3). An element place follows the same rule, so `names[0] += pad(names.length());` compiles and runs as in JavaScript, where rustc rejects it because its index borrow is not two-phase. JavaScript reads the old value first and prints `a!`, but here that read would leave the append working on a string that the right side may have freed. `*grown(&s) += "!";`, with a `grown` that appends to its parameter and returns it, still compiles, since its right side leaves `s` alone. The address computation and the bounds check of the write run after the right side, so `a[i] = shrink(&a)` and, for a Copy element, `a[i] += shrink(&a)` need no two-phase borrow. An explicit `&` argument takes effect at its position, so `f(&a, a.length())` is EN0708 when `f` writes its first parameter.

### 5.3 Borrows and reborrows

A *slot* is a parameter, local, temporary, capture or hidden argument of reference type. A function's *contract* is what a caller sees of it. It is computed from the body after type checking (N1) and stored in the module's interface file, together with each borrowing class's flag for writing through its reference fields (4.3):

- *perm* for each `&` parameter, for each reference part of a by-value borrowing-tuple parameter, nested parts included, and for `this`: Read or Write, and for `this` also Own, which only the `move` marker declares (4.3). A parameter or part is Write iff it is write-live at entry (N3, N7); a `let` reference parameter is Write even if the body only reads it; positions with no body take their declared marks (4.4); functions containing `unsafe` follow 5.9.
- *sources*: the parameters the returned reference may borrow from, which of them it reaches only through the reference fields of a borrowing value, and which only through its `readonly &` fields, so that the result holds that value's read set alone (5.1, 5.4).
- *stores*: which parameters it stores into the borrowing value behind another parameter or `this`, which of those stores take only what the stored parameter's reference fields hold, which take only what its `readonly &` fields hold, its read set, and which of that value's two loan sets each store joins, the read set for a store into a `readonly &` field (R2, 5.1, 5.4); these three are the store's bits, which fitting compares (5.4).
- *result*: none, read-only with a reason, or writable (5.4).

A Read parameter that is in the sources of a function with a writable result is said to *follow*.

- **N3. Write-liveness.** `wlive(s, point)` is a backward may-analysis on MIR. It is true if some path from the point, not reassigning `s` first, reaches (a) a write through `s`: a whole value, a field, an element, a compound assignment or `++`; (b) `s` as the argument or receiver of a Write parameter, whether the callee is a function, a bound member, an `fn` value or a closure parameter; (c) a copy (a part of a tuple literal included), projection, destructuring binding, narrowing, ternary, `??`, `!`, `?.`, reference conversion (C18, C21, C22), capture or `for...of` bind into a slot `t` with `wlive(t)` just after; (d) `s` as the argument of a parameter in the callee's sources, where the call's result `r` has `wlive(r)` just after; or (e) `s` written into a borrowing value that code out of sight may write through: an object of a class that writes through its reference fields (4.3), or a tuple reached through a reference, which has no methods to tell; a class's own tuple field is no such tuple, so a store into it, or into a part of it at any depth, is write-live exactly when the class's flag is set (4.3), as a write through it in the class's own bodies sets it. That covers a field write `(*t).f = s` or `d.f = s`, a constructor storing `s` into such a class, and a whole-value write `*t = u` whose `u` holds `s`, but not a store whose target is a reference field declared `readonly &`, a parameter property's included, since nothing writes through one (4.3), even when another field sets the flag, and its loan joins the value's read set (5.1); a whole-value write keeps (e); a call that stores `s` into one is covered by (b), because the callee's own parameter is Write by this rule. `return s` is not a write. A borrowing class value, nullable or not, held in a local, a temporary or a by-value parameter or returned by a call, is never write-live itself: neither a write of one of its fields, nor its use as a receiver, a `move` receiver included, nor its use as an argument makes it so, because writes through its reference fields happen only in its class's bodies, where (e) gave each stored loan the mode of the parameter that filled the field; so (d) and N8 ask whether a result is write-live only of a reference result and of the reference parts of a tuple result, and a factory's source takes its mode from its perm: `let c = Copier.make(&table, &out); c.step();` over a `const table` compiles (`TESTING.md` `FV-02-class-writelive`). A tuple held directly in a parameter, local or temporary, a nullable one included, has no such blind spot until a reference to it is taken, so N3 follows each of its reference parts, nested parts included, as a slot of its own: a write through `t[0]` makes part 0 write-live and not part 1, which is how a by-value tuple parameter gets one permission per part. A borrow `&d` of such a tuple into a slot `t` with `wlive(t)` just after puts its parts behind a reference, so it makes every reference part of `d`, nested parts included, write-live at that point, as (e) does for a tuple reached through a reference: with `let pair: [&i64[], i32] = [&data, 1]; const t = &pair; t[0].push(4);`, the loan the literal takes on `data` is exclusive, so a `const e = &data[0];` above it that is read afterwards makes `&data` EN0706, and so does `&d2` in `grow([&d2, 1])` for `function grow(let p: [&i64[], i32]): void { const t = &p; t[0].push(4); }` while a reference into `d2` is still used. The tuple still holds one loan set (O9).
- **O7. A reference is copied, never moved (N4).** Each borrow site, whether an explicit `&`, a receiver auto-borrow or an argument, is exclusive iff its slot is write-live right after; otherwise it is shared. An exclusive loan stays exclusive until the last use of any slot holding it. A copy `t = s` of a reference, nullable or not, never moves `s`: if `wlive(t)`, `t` holds `held(s)` plus a new exclusive loan on `*s`; else if `wlive(s)`, `t` holds `held(s)` plus a new shared loan on `*s`; else `t` holds `held(s)`. So `s` works again when `t` is dead. A copy that takes no new loan still reads what `s` points at, checked as a shared borrow of `*s`, so it meets a live exclusive loan on `*s` as any read does. A capture is a copy. A reference read out of a reference field of a borrowing value or out of a reference part of a tuple, nullable or not, at any depth, as `p = c.dst`, `q = pair[0]` or `d = (*t).f`, is copied the same way, with the field or part counted as write-live, since nothing tracks whether it is written through elsewhere, so such a copy always takes a new loan, exclusive when it is write-live and shared otherwise, as an auto-borrow through the field does; only a part of a tuple held directly in a parameter, local or temporary, which N3 follows part by part, is copied as a slot is. So inside `Copier`, `const p = c.dst; const q = c.dst;` with `q` stored into a field that `Copier` writes through is EN0706 at the second `c.dst`, where two copies with no loan let one buffer reach two fields (`TESTING.md` `FV-02-field-copy`). Such a part's copy, like a slot's, still reads what the part points at when it takes no new loan: with `let t: [&i64[], i32] = [&v, 1];`, `const a = t[0]; const b = t[0]; const e = &b[0]; a.push(3); a.push(4); console.log(*e);` is EN0708 at the second `t[0]`, as with `const r = &v;` and `const a = r; const b = r;` it is at the second `r`, where a copy that read only the part let `a`'s pushes reallocate `v` under `e` (5.8 H39, `TESTING.md` `FV-02-part-copy`). A copy of a borrowing tuple or a nullable one, directly, as `const p2 = pair;`, or through a reference, as `d = *t`, copies each reference part this way, taking a new exclusive loan when the copy's part is write-live and a new shared one when the source's part is: after `const p2 = pair; const f = &p2[0][0];`, `pair[0].push(4)` while `f` is still used is EN0706. Modes are per loan, not per binding: in `let x = 12; const y = &x; *y = 13;` the loan held by `y` is exclusive, so reading `x` before `y`'s last write is EN0708.
- **O8. Explicitness (N8).** A reference is only ever made by writing `&` (4.5). A non-reference argument to a `&` parameter needs `&` whether the callee reads or writes it: `total(&a)`, `bump(&a)`; `total(a)` is EN0612. A variable that is already a reference is passed as it is (`bump(r)`), and `&r` with `r: &T` means `r`. Receivers, operators, `console.log`, template holes and `expect` borrow automatically, and hidden arguments (5.5) need no `&`. An argument's loan is exclusive iff the parameter's perm is Write, or the parameter is in the sources and the result is write-live; it is held while the result lives iff the parameter is in the sources, except where the result reaches it only through the reference fields of a borrowing value whose class does not write through them and, for a reference result, the result is not write-live, or only through that value's `readonly &` fields, where the result holds the value's read set instead (5.1), with no condition on the result's use, since a reference result is then read-only (N6) and is never written through without EN0616, and a borrowing value result keeps those loans only in fields that nothing writes through (N3 (e)); its mode does not change after the call. An exclusive slot's root must not be read-only (N5, 4.11): writing through a read-only slot, passing it to a Write parameter, or looping over it with a binding that is written through (5.6), is an error naming the mark's origin (EN0608, EN0609, EN0614, EN0616).
- **O9. Loans.** Every borrow site creates a loan `(path, mode, span)`, its mode set by O7. Each slot `s` has a flow-sensitive set `held(s)` computed forward:
  - `s = &p` gives `{loan(p)} ∪ held(root-reference-of(p))` when `p` goes through a reference. When `p` has a borrowing type, `s` also holds the loan sets of the borrowing value it points at, so `const r = &lx;` keeps `source` locked while `r` lives, even after `lx`'s last use, and a borrow or copy through a reference field of the borrowing value that a reference `r` points at, as `&r[0][0]` or `r.dst` is, keeps `r`'s own loans on that value beside what its fields hold, so `const r = &t; const e = &r[0][0];` keeps `t` from changing while `e` lives, as `&t[0][0]` does, except through a `readonly &` field, which gives the value's read set alone (5.1, `TESTING.md` `FV-02-through-ref`);
  - `s = t` where `t` is a reference gives `held(t)`, plus the new loan on `*t` that O7 adds, if any;
  - assignment replaces the set and kills loans rooted at the old `*s`. A reference slot can be assigned only a reference, a string literal, or `null` if it is nullable: `y = 13`, `y += 1` and `y++` are EN0422, with fix-its to `*y` or `&` (4.11);
  - control-flow joins take the union;
  - a write into a borrowing value reached through a reference `t`, at any depth (`*t = u`, `*this = v`, `(*t).f = u`, `(*t).f[0] = u`), adds `held(u)` to that value's loans and removes nothing, in the caller too, as a store does (R2, 5.4), keeping its read set apart: a write of a `readonly &` field adds to the read set and to the main set, any other write to the main set alone, and a whole value adds each of `u`'s sets to the same one, checking `u`'s read set once, as a store into a `readonly &` field is checked (5.1), against the sets as they stood before the write; so does a write of a part of a local borrowing value, `d.f[0] = u`. Reading a whole borrowing value through a reference, `d = *t` for a Copy one, gives `d` what `t`'s reference fields hold and `t`'s own loans on that value, as a copy through a reference field does (first bullet, `TESTING.md` `FV-02-through-ref`, `D20-core-3`), and moving `this`, or a borrowing field of `this`, out in a `move` method gives what the fields hold; a tuple, or a nullable one, read this way also takes the new loan per reference part that a copy takes (O7);
  - a `V`-typed value holds nothing: a call returning `V` ends every loan it took. A borrowing value holds two loan sets, its read set for its `readonly &` fields and its main set for all of its reference fields, the read set's loans included (5.1).
- **O10. Liveness.** A loan is live at a point iff a slot holding it is live there (backward liveness; drop of a reference is not a use; drop of a `V` holds nothing; drop of a borrowing value is a use of its loans only when a destructor runs on it or on a borrowing value inside it, I5).
- **O11. The check.** At every read, write, move, borrow, drop and scope end of a path `p`, for each live loan on an overlapping path:

  | Access | Live shared loan | Live exclusive loan |
  |---|---|---|
  | read, Copy, shared borrow | ok | EN0708 |
  | write, assign, exclusive borrow | EN0706 | EN0707 |
  | move | EN0709 | EN0709 |
  | drop, scope end | EN0711 | EN0711 |

  Two paths overlap when one is a prefix of the other; `x.a` and `x.b` are disjoint, `x[*]` overlaps itself and `x`, and a loan through a reference `r` overlaps `*r`. A `for...of` loop's own head, its tag checks and its length read, and its own bind, its checks and its borrow, are not checked against the loop's hold or the loans of its bind site (O2); every other access is, and two loans of one bind site overlap each other unless one carries this turn's key and the other an earlier turn's (O2). A loan reached through a borrowing value's reference fields does not overlap a write of a reference field itself, which repoints the field and leaves its old target untouched, while the loan that a loop's hold takes on a reference field its path goes through sits on the field itself, and does (5.6). An access through a dereference of a loan's holder, by that holder, is permitted; an access to the holder's own place never is, so a loan that a borrowing value holds on part of itself conflicts with every later move or write of that value (H05).
- **O12. Sharing means frozen.** No `Cell`, `RefCell` or global that safe code can write. The single exception is `core`'s `Atomic<T>` and `Atomic64` for integers and `bool`, whose methods take their contracts from a compiler table, as every `@intrinsic` and `@hostCall` declaration does (N11, 4.4), so they are Read for `this` with no override; they hold no references and no narrowing applies to them. Only these `@lang` atomic types may write their own bytes under Read.

Location sensitivity accepts these, both sound because the loan is simply not held on the other path: NLL problem case #3, and a list cursor that walks with `let cur = &head;` and then `cur = &cur.next`.

```ts
public function getOrInsert(m: &Table, k: i64): &Entry {
  const hit = m.find(k);  // NLL problem case #3
  if (hit != null) { return hit; }
  m.insert(k);
  return m.last();
}
```

### 5.4 The lifetime rule (R3)

**Sources.** A function's returned reference borrows from its *sources*. In a function with a body and no `unsafe`, the compiler infers them from the body: they are the reference parameters, `this` included, that a returned reference can come from, and nothing is written for them. In the example below, `first` returns `&xs[0]`, so after `const f = first(&names, &label);` only `names` is locked, and `label = "people";` is legal while `f` is still used. Where the body cannot be read (an interface member, an abstract method, an `fn` value, a `declare` function) or cannot be trusted (a function containing `unsafe`, where `&*p` holds no loans), signature defaults apply:

1. a method's result comes from `this`;
2. a free function's result comes from all its reference parameters;
3. a function with no reference parameters returns a reference that holds no loans.

So `map.get(&key)` never locks `key`. Rule 3 covers string-literal descriptors and references to top-level `const` storage, which hold no loans and are valid for the whole program, and it keeps raw-pointer accessors safe, because a raw-derived reference returned under it keeps its read-only mark (4.11), a view that `Slice<T>.fromRaw` makes included. A body containing `unsafe` still infers its stores (below) from its safe operations; only its sources fall back to the defaults. The `this` of a `move` method contributes no loan on the object, which moves into the call and is disposed when the method ends, so returning a reference into the object itself is EN0710, `` `posRef` returns a reference into the object it consumes ``; a result taken from the reference fields of a moved borrowing value still holds their loans (5.1).

**Overrides.** A method that a subclass can override is any method of a class that isn't `final` other than a `static` or `private` one and one compiled once per type, with type parameters of its own, a by-value interface parameter or an object-type parameter, which has no method-table slot (4.3). A call to one goes through the method table exactly when the receiver place's last step dereferences a `&A` or a `Box<A>` where `A` can be extended, or the receiver is `this` inside such a class (`this.label()`), and such a call has as sources those of the base body plus `this`, because an override may return into its own object. An override may return into `this` or into any source of the base body, and returning into another parameter is EN0714: with `public label(name: &string, fallback: &string): &string { return name; }` in `Labeler`, an override in `Strict` that returns `fallback` gets `` `Strict.label` returns a reference into `fallback`, but `Labeler.label` returns only into `name` or `this` ``, with `` help: through a `&Labeler`, callers only expect `name` or the object ``. Such a call therefore locks the object as well as those arguments. With `public label(): &string { return "animal"; }` and `public rename(name: &string): void` in `Animal`, an override in `Dog` that returns `&this.name`, and `a: &Animal`, `const tag = a.label(); a.rename("Max"); console.log(tag);` is EN0706, `` `a` can't change while `tag` points into it ``, with `help: keep a copy: const tag = a.label().toString();`. Every other receiver place of type `A`, whether a local, a by-value parameter, a field, an element of an array, a part of a tuple, a field of an enum case, a narrowed payload or a temporary, holds exactly an `A` (4.3), with no slicing, so a call on it is direct: it reaches only the body `A` runs and applies that body's own sources, which add nothing, and so does a `super` call. The one other receiver that goes through the method table is a place of type `T` or `&T` where `T extends A` names a class `A` that can be extended (4.10): the generic body is checked once with these widened sources, and each instance calls through the table, since a `&T` may point at a subclass. So the several results of `lx.next()` on the local `lx` of 5.1 can be kept, while through an `r: &Lexer` a second `r.next()` while the first token is still used is EN0707, since `Lexer` isn't `final`. The methods of a `final` class, and `static` and `private` methods and those compiled once per type, add nothing, since nothing overrides them, and an abstract method keeps the signature default, `this`. Stores are not widened: an overridable method declares its base body's, with their bits, and an override fits them by the rule for stores (below). A call through the method table passes each `&I` and `&I | null` argument as two words, so each class's slot for a method with an `&I` parameter names that class's copy of the method for two-word `&I` arguments (4.4). A method compiled once per type is called directly, with the body of the class that declares it, through a base reference as anywhere else, so a `Dog.show<T>(x: &T)` over an `Animal.show<T>(x: &T)` is EN0460 at the override (4.3), whether or not its body uses `T` by value where `Animal.show` lets `T` stand for a view.

Where these rules are too strict, return an index (`-1` when there is none, like `findIndex`), as in `public interface Policy { pick(ready: &Slice<Task>): isize; }`, or return `null` and let the caller write `??`: with `public interface Settings { get(key: &string): &string | null; }`, the caller writes `const theme = settings.get("theme") ?? &dark;`. Within a call-graph SCC, sources and stores are found first, as a least fixed point in which every function starts with none, before permissions and results (N7), so a recursive function has defined sources and N3 (d) reads the final ones. Sources and stores also read the flags of 4.3, which come from permissions and from results, so a borrowing class counts as a node of the call graph, linked to its methods, constructors and destructor, each with the arrows nested in it, and to each function whose contract reads its flag; in an SCC that holds one, the sources and stores and the permissions and flags repeat together until neither changes. A flag reads the result of a call to a member of its own SCC as writable unless its return type says `readonly`, which is where the result fixed point below starts, so a flag is only ever set too often, never too rarely. The sets and permissions only grow, and a set flag only makes a call hold more, so their joint answer is the least one.

**Stores (R2).** A function *stores* parameter `j` into parameter `m` when, at a `return`, the borrowing value behind `m`, `this` included, may hold a loan that came through `j`: one the argument for `j` holds, or one taken on data reached through it. Stores are inferred from the body, like the sources, and a store that took only what `j`'s reference fields hold, from a value whose class does not write through them, is marked as such (5.1), and one that took only what its `readonly &` fields hold is marked read-set-only, whatever its class writes. A read-set-only store of a parameter into the value behind itself, as `skip`'s in 5.1, moves only what that value's own `readonly &` fields already reach, which nothing its other fields write through may hold (5.1), and a reference read from one goes into no field written through (N3 (e)), so the caller adds that read set as for any such store, since it may land in a value behind the value's reference fields, but does not check it against what the value's other fields hold: `c.skip()` compiles on a `c` that a call returned, which counts every loan it holds as held by its other fields (`TESTING.md` `FV-02-skip`). The `this` of a `move` method is no `m`: the object is locally owned there (definition check, below), so a write into it is a write into a local borrowing value (O9), whose read-set check is the one a parameter gets: storing into a `readonly &` field what another reference field of `this` holds is EN0616, while narrowing that field from itself passes, though the narrowed reference keeps the loan its slice took through `this`, so moving `this` out afterwards, as `return this;` does, is EN0709 (H05), a listed difference from Rust (`TESTING.md` `FV-02-move`); and a result that moves it out carries the loans written into it, so `public move withSrc(s: &string): Lexer { this.src = s; return this; }` stores nothing, and N6's stored-source test leaves its result alone. Neither it nor a by-value borrowing parameter, which has no caller's value behind it either, can carry a store back to the caller, so a call that would store into any value that holds one of its loans is EN0616, `` cannot store a reference into a value reached through consumed `this` ``, with `help: write the field directly, or take the value by reference`: a value reached through it, as `this.cp.retarget(s)` in a `move` method of a class with a `&Copier` field, the value itself, as `w.setSrc(s)` on a by-value `let w: Lexer`, or a local built from what it holds, as `c.retarget(s)` after `let c = new Copier(s, w.dst);` on a by-value `w: Copier`, since the checker cannot tell the value itself from what its fields reach, nor a value built from its fields from one reached through them; a direct write such as `this.src = s` stores nothing and compiles, and a reference parameter carries a store back through the caller's own loans, so `let lx = new Lexer(s); lx.setSrc(t);` in a function taking `s: &string` and `t: &string` compiles (`TESTING.md` `FV-02-lost-store`). Inside the body, a loan stored into the value behind `m` stays live until every `return`, because that value outlives the call, so storing a reference to a local into `this` is EN0711 at the local's scope end. At a call, the loans of argument `j`, or for such a store only what its reference fields hold, or for a read-set-only one only its read set, join the main set of the value behind argument `m` that the store names, and its read set as well for a store into a `readonly &` field (5.1). All the stores of one call apply together, each against the sets as they stood before the call, so neither their order nor the order of a constructor's parameters changes what the caller's slots hold (`TESTING.md` `FV-02-store-snapshot`); the callee applies its own stores one statement at a time, so one that stores `s` into `c` and then `c` into `h` also stores `s` into `h`, while one that stores `c` into `h` and then stores into `c` meets the loan on `c` that `h` keeps. A position with no body declares no stores, and an overridable method declares its base body's. A closure value declares none either: a call through an arrow passed as an argument or kept in a local applies the signature defaults above and no stores, so an arrow that stores one of its parameters into another is EN0615 as well. A function, implementation or override fits a declared contract only if its stores are within the declared ones: each of its stores `(j, m)` has a declared store `(j, m)` that gives the caller at least as much, so where the declared store takes only what `j`'s reference fields hold, its store does too, where the declared store takes only `j`'s read set, its store does too, and where its store joins the read set, the declared one does too. An override may therefore store less, but never more: keeping the whole parameter where the base keeps only its fields is refused, while keeping its fields where the base keeps the whole parameter is allowed, and so is a plain field where the base stores into a `readonly &` field; otherwise it is EN0615 at the override, naming the field and the base, `` `Holder.adopt` keeps `o` itself, but `Base.adopt` keeps only what `o`'s fields hold `` or `` `Sub.retarget` keeps `v` in the `readonly &` field `extra`, but `Base.retarget` keeps it in another field ``, because a call through the method table applies the base body's stores with their bits. The same comparison applies wherever stores are compared: overrides, and class bounds `T extends C`, which use the same declared contract (4.10). So `reset(lx: &Lexer, s: &string)`, which calls `lx.setSrc(s)`, converts to no `fn` type: EN0615, `` `reset` stores `s` into `lx`, which `fn(...)` can't declare ``. Inside an arrow, a store into a borrowing value reached through a capture is EN0616 (5.5).

**Definition check.** At each `return`, a loan on a locally owned path is EN0710 (dangling); in a `move` method, the object behind `this` counts as locally owned. Where the sources come from the signature defaults, a base body with `this` added or another declared set (an interface member that a method implements, or an `fn` type that a function converts to), a loan from a parameter outside them is EN0714, reported once: at the `return` for an implementation or an override, with the declaring member as the secondary span, and at the coercion for a function converted to an `fn` type, labelled `converted here`, with no secondary span.

**Result writability (N6).** A contract's *result* is none if no reference is returned; read-only, with the first reason, if the return type says `readonly`, if it is a reference, a nullable one or a tuple with a reference part and has a source that it reaches only through the `readonly &` fields of a borrowing value (5.3), whatever marks its flows carry (`` `find` returns a reference reached from the `readonly &` field `rows` ``; a borrowing class value with such a source stays writable, since a reference taken from a `readonly &` field is read-only, N5, and goes into no class that writes through its fields, N3 (e)), if any returned value may carry a read-only mark (N5, 4.11), if it is a `&string`, a `&string | null` or a tuple with a `&string` part that may come from a reference of type `&string` or `&string | null` that the function only reads, a Read `&string` part of a by-value tuple parameter included, and so may be a part of a string (section 11), if a parameter it may come from is also stored by the function (`` `keep` also keeps a reference from `x` in `this` ``), or if a returned tuple has two or more reference parts that may point at the same data (`` `two` returns two references that may point at the same data ``), a borrowing class value counting as one part, since writes through its fields happen only in its own class's bodies, which keep them apart (N3 (e), 5.1); otherwise writable. The last test runs at each `return` as if each part were copied into a slot that writes (O7): parts that would then conflict make the result read-only. Each part is compared, pair by pair, through the loans it holds and, for a parameter's key that reached the part on some path without a loan that borrows through that parameter, the whole parameter, or the whole of what its reference fields carry: a loan crosses a parameter's key when it borrows through that parameter, and crosses the key of what the parameter's reference fields carry only when it borrows through one of those fields, so a loan on an owned field, `&this.own`, crosses the first and not the second; a key is left to such loans only where every way it reached the part came with one that the part still holds, so a reference copied without a new loan, a borrow made before a `let` parameter was repointed, or the parameter itself joined with a borrow through it, as `c ? p : &p.kids[0]`, makes the key count as the whole parameter (`TESTING.md` `TK-01-copy-join`, `TK-01-pick-param`, `TK-01-repoint`); and a reference to a place whose type holds no reference, taken through `this` or through a parameter not marked `let`, as `&this.own` is, holds only the first, since it lies in that value's own storage and reaches nothing the reference fields carry. Parts from disjoint fields of one parameter, or from different parameters, stay writable. Parts reached through one local reference, or through one turn's loop binding, share that slot's loans and conflict even when their fields differ, as in `const r = &p.inner; return [&r.a, &r.b];`, each a listed difference from Rust (`TESTING.md` section 13), while two owned fields of a borrowing class, `[&this.a, &this.b]`, or an owned field beside a part reached through a reference field, `[&this.own, &this.view[0]]`, stay writable. Two parts that hold loans of one `for...of` bind site conflict unless each such pair of loans is one of this turn and one of an earlier turn of the same run, which bound different elements, or is one loan that both parts hold only via the bind of another loop, which that loop's site loans decide (O2), so parts from one turn of a loop, or with a loan kept from an earlier run, conflict, while two turns of an inner loop over one turn's binding of an outer loop stay apart (O2, 5.6). The parts are every reference part of the returned value, a nested tuple's parts and a nullable's payload included, a borrowing class value as one part holding its whole set, and each is compared by what it holds. A part that a tuple literal places in the returning statement holds that operand's loans, looking through a nullable and through nested literals, so `return [[r, r], 0];` at `[[&i64[], &i64[]], i32] | null` compares `r` with `r` and is read-only. A part of a local whose only reaching definition is such a literal, when nothing writes the local or a part of it, or borrows it for writing, before the `return`, is compared with the other parts of that local by what the literal's operands held when it was built, so `const t = [&p.a, &p.b]; return t;` stays writable, and with every other part by what the local holds at the `return`, since a loop's new run or a repointed `let` parameter may have changed what those loans stand for in between (`TESTING.md` `TK-01-local-stale`, `TK-01-local-kill`). A call's result, returned in that statement, or kept in a local whose only reaching definition is that call, when nothing writes the local or a part of it, or borrows it for writing, before the `return`, counts as one part only when its arguments for the callee's sources, as they stood at the call, pass this test against each other, each reference part of a by-value tuple argument counting as an argument of its own, compared with the other parts of that argument by what the literal's operand held when the argument is a tuple literal, or a local or temporary whose only reaching definition is one that nothing wrote or borrowed for writing before the call, and otherwise by the argument's whole set, and with every other argument by what the argument holds at the call, since a repointed `let` parameter may have changed what its literal's loans stand for (`TESTING.md` `TK-01-local-kill`), and an argument for a source reached through a borrowing value's reference fields counting by what those fields hold; otherwise each of its parts holds the call's whole loan set; and one kept in such a local is compared with every other part by what the local holds at the `return`. So with `function two(a: &i64[], b: &i64[]): [&i64[], &i64[]] { return [a, b]; }`, `return two(r, r);` in a loop over `rows` is read-only, and so is `return id2([x, x]);` for an `id2` that returns its tuple parameter, while `return two(a, x);` with `a` kept from an earlier turn, and `return v.splitAt(2);`, stay writable, and `let p = two(&q.xs, &q.ys); p[0] = p[1]; return p;` is read-only, since `p` is written after the call (`TESTING.md` `TK-01-split-written`). A by-value tuple parameter that the body never writes, whole or in part, nor borrows for writing, counts as one part, because each caller keeps its parts apart: by N8's per-part loans where the result is written, and by this test where the caller only returns it. Every other reference part, a part of a local or temporary tuple written after it was built included, holds that value's whole loan set (O9), so any two such parts conflict unless the set is empty: a loop that sets `t[0] = r` and `t[1] = r` before `return t;` gives a read-only result. Within a call-graph SCC it is a greatest fixed point: each result starts writable and falls by these rules (N7). So a returned reference is as changeable as its source, as in TypeScript, whether it derives from `this` or from parameters, in methods and free functions alike, library accessors such as `T[]`'s `get` and `last` included, and the use decides: a caller that writes through it makes the call borrow the source argument, the object included, for writing (N3 (d)). With `public book(id: i64): &Book`, `lib.book(1).title = "Dune";` works on a `let lib`, and reading works on a `const lib`. `readonly` before the return type keeps callers from changing what the result points at: with `public count(): readonly &isize { return &this.n; }`, `*c.count() = 5;` is EN0616, `` cannot change the object returned by `count` ``, with the label `` `count` returns a `readonly` reference `` and `` help: to allow this, remove `readonly` from the return type of `count` ``. A returned `&string` that may be a part can't grow: with `longest` below, `*longest(&s, &t) += "!";` is EN0616, `` `longest` returns a string that may be a part, so it can't grow ``, with `` help: change `s` directly: `s += "!";` ``. A result that may point at a constant or static stays read-only. A position with no body gives a writable result unless its return type says `readonly`, or the result is a `&string`, a `&string | null` or a tuple with a `&string` part that may come from a `&string` or `&string | null` parameter not marked `let`, which may be a part (4.4). A writable result with one reference needs no exclusive-access proof in the callee, because no callee reference survives the return: a source that the function also stores makes the result read-only, and a result with several parts gets the proof above. Permission and result writability are separate facts: a function can write a parameter and still return a read-only result.

**Call check.** The result of a call holds the union of `held` of exactly the arguments for its sources, except that for a source the result reaches only through the reference fields of a borrowing value, as `next` reaches `this.src`, it holds what those fields hold and not the argument's own loan, provided the class does not write through its reference fields and, for a reference result, the result is not write-live (5.1), and for a source it reaches only through `readonly &` fields, it holds that value's read set and not the argument's own loan, whatever the class's flag, with no condition on the result's use, since a reference result is then read-only (N6) and is never written through without EN0616, and a borrowing value result keeps those loans only in fields that nothing writes through (N3 (e), 5.1). Where the function stores a source `j` into the value behind another parameter `m`, `this` included, that value and the result hold the same loans after the call, and no loan between them is needed. The result is read-only (N6). When the value's class writes through its reference fields, the store borrows `j` for writing (N3 (e)), unless the field it is stored into is declared `readonly &` (4.3), where the stored loan is shared and the read-only result keeps both holders reading, as when the class only reads (below); otherwise that borrow stays live in the callee until every return, because the caller's value outlives the call (stores, above), so no path of the body both stores `j` and returns a reference derived from it: with `public keep(x: &i64[]): &Slice<i64> { this.r = x; return x.slice(0, 1); }` and `public grow(): void { this.r.push(1); }` in a class `Holder` whose `r` is a `&i64[]`, `keep` itself is EN0708 at `x.slice(0, 1)`, and so is a free function that stores its `xs` into a `c: &Cursor` and then returns a view of `xs`. When the class only reads through its reference fields, or the field is declared `readonly &`, neither holder writes through the stored loan, so with `public reset(s: &string): &string | null { this.src = s; this.pos = 0; return s.slice(0, 1); }` in the `Lexer` of 5.1, `const first = lx.reset(&text); const t = lx.next(); console.log(first, t);` compiles. The lock follows the use: a write borrow lasts from the call to the result's last write. With `let players: Player[]`, this is EN0708, `` `players` can't be read while `q` may write into it ``, with the label `` borrowed for writing here, because `q` writes on line 3 `` on the call, `read here` on the read and `the write` on `q.hp -= 1`, and `` help: read `players` before line 1 or after line 3 ``:

```ts
const q = players.last();
console.log(players.length());
if (q != null) { q.hp -= 1; }
```

The same holds for user functions, so `function find(list: &Slice<Player>, name: &string): &Player | null` needs no writing twin. An argument that is an rvalue is a temporary living to statement end, so `const r = f(&make());` is EN0712 when `r` is used after the statement, and accepted when it is not (O10): bind the argument first. There is no temporary lifetime extension: `const r = &make();` followed by a use of `r` is also EN0712.

The same contract is applied on both sides, so checking is modular. A contract is inferred from the body, so a body edit can change it and break a caller that was not edited.

```ts
public function longest(a: &string, b: &string): &string { return a.length() > b.length() ? a : b; }  // borrows from both

public function first(xs: &Slice<string>, label: &string): &string {  // only `xs` stays borrowed
  console.log(`reading ${label}`);
  return &xs[0];
}
```

**String literals.** A literal has type `string` with `cap == 0`, needing no allocation and no drop action. Where `&string` is expected, it refers to a static descriptor in read-only data (section 11) and holds no loan, so it needs no `&` (C13): `greet("Ada")`, `return "none";` in a `&string` function. It is read-only (N5).

**Literals of constants.** A bracket literal written behind `&` where a `&Slice<T>` or a `&T[N]` is expected, whose elements are all constants (number, `bool` and string literals, compile-time `const`s, enum cases without fields, and such literals nested), is a read-only static in read-only data (section 11) when nothing writes through the reference, by the inferred permission (N3), as Rust's constant promotion makes one. Like a string literal, it holds no loan, and it carries the mark of a top-level `const` (N5). So `const primes: &Slice<i64> = &[2, 3, 5, 7];` keeps its view for as long as it is used, `function zeros(): &Slice<i64> { return &[0, 0]; }` returns one, and with a `total` that sums, `console.log(total(primes), zeros());` prints `17 [0, 0]`, with no heap; the result of `zeros` may point at a constant, so `zeros()[0] = 1;` is EN0616 (N6). A literal that something writes through, as one passed to a parameter that writes, `fill(&[1, 2, 3], 7)`, or bound to a slot that is written through, stays a statement temporary, and so does a literal with an element that is not constant, as `&[n, n]`: no temporary lifetime is extended for either, so keeping one past its statement is EN0712 and returning one is EN0710.

### 5.5 Closures

Arrow functions may be passed as arguments and stored in locals: `const double = (x: &i64) => x * 2; console.log(xs.map(double));` prints `[2, 4, 6]` for `xs = [1, 2, 3]`, and `let count = 0; const inc = () => { count += 1; }; inc(); inc(); console.log(count);` prints `2`. An arrow that uses outer variables behaves like a reference to them. They are locked while the arrow will still be used, so `inc(); console.log(count); inc();` is EN0715, `` `count` is locked while `inc` will still be used ``. Such an arrow cannot be stored in a field or returned (EN1007): `new Button { on: () => console.log(count) }` is an error naming `count`. An arrow that uses no outer variables is a plain `fn` value and can be stored anywhere: `new Button { on: () => console.log("hi") }` is valid. The closure type `(x: S) => V` may be written only as a parameter type, and closure types do not nest (EN0705); `| null` at the top of a parameter's closure type is not nesting, so `handler?: (k: u8) => void` is a valid optional callback, which the body narrows before calling it (4.14).

- **Captures** are inferred per variable: an arrow borrows each local it uses, whole, as its environment holds it (a reference local through what it points at), and reads take shared loans and writes take exclusive loans. The closure value holds them while it can still be called: for the duration of the call when the arrow is an argument, and until the local's last use when it is stored in a local. A conflict with a capture's loan is EN0715. An arrow created inside a loop that changes the loop's held source is EN0706 instead, as any change of that source is (5.6): in a loop over `&q`, `run(() => { q.push(1); });` is `` cannot mutate `q` while iterating over it ``. An arrow created before the loop and called in it already holds its loan when the loop takes its hold, so it is EN0715 at the source: with `const f = () => { q.push(9); };`, `for (const x of &q) { f(); }` is `` `q` is locked while `f` will still be used ``.
- **Capturing through a reference.** Capturing a reference local `r` is a copy of `r` (O7): the capture holds `held(r)`, plus a new exclusive loan on `*r` if the arrow writes through `r`, else a new shared loan on `*r` if `r` is write-live after the capture (N3), and otherwise no new loan. So `both(() => { *r += 1; }, r);` is EN0715 in either argument order, while `run(() => { *r += 1; }); run2(r);` compiles. The capture also holds a shared loan on the local `r` itself while the closure value is live, so the arrow never sees a stale target: after `let r = &x; const f = () => console.log(r);`, `r = &y; f();` is EN0715, `` `r` is locked while `f` will still be used ``.
- **Rebinding.** A captured reference local cannot be rebound inside the arrow (`r = other` is EN0616), so a closure cannot stash its `&T` argument in an outer `let r: &T`. Writes through it, such as `*r += 1` or `this.total += x` in a method that changes the object, are ordinary exclusive captures. For the same reason a closure cannot store into a borrowing value reached through a capture, which nothing at the arrow's creation would record: a reference-field write through a captured `this`, or a call that stores into a captured value (R2), as in `words.forEach((w) => { lx.setSrc(w); });`, is EN0616.
- **Moves.** The body cannot move a captured value (EN0617).
- **A closure value is used exclusively,** like Rust's `&mut dyn FnMut`. Calling a closure parameter `f` is an exclusive use of `f`. Passing `f` as an argument creates an exclusive loan on `f`, held for that callee, and needs an identical signature (C14). So `twice(f, f)` is EN0718, while `visit(f, n); visit(f, m);` is accepted. Capturing `f` holds an exclusive loan too, so `both(f, () => { f(); })` is EN0718.
- **Writing callbacks.** A closure parameter's type states what the closure may write, its permission row (4.1), as every position with no body does (4.4, 4.5): `f: (x: &i64) => void` accepts only functions that read `x`, and `f: (let x: &i64) => void` accepts writing ones. Passing a writing function to the first is EN0615. One function cannot serve both kinds: `function each(xs: &Slice<i64>, f: (x: &i64) => void): void { for (const x of xs) { f(x); } }` reads, and a twin `eachLet(xs: &Slice<i64>, f: (let x: &i64) => void)` writes, so with `let v = [1, 2];`, `eachLet(&v, (x: &i64) => { *x *= 2; }); console.log(v);` prints `[2, 4]`.
- **`return` and `?`** inside an arrow act on the arrow. Its return type comes from the expected type, a parameter's `=> U` or an annotated local, or else from its body; an annotation, `(x: i64): i64 => x * 2`, must match. A return type that comes from the body is never a site of C19 (4.5), whose target must be known before its operand: no plain value is wrapped there, and `Err(e)`, with no expected type, takes `E` from its operand, `Failure` for a text, and a fresh `T`, as `Ok(v)` takes `Failure` (6). So the returns of `const check = (s: &string) => { if (s.isEmpty()) { return Err("empty"); } return s.length(); };` do not unify, whichever comes first: EN0401, with `` help: annotate the result, `(s: &string): Result<isize> => ...`, or write `Ok(s.length())` ``.
- **The result of a closure is `V`.** `users.map(u => u)` gets EN0703, and so does a closure type or a capturing arrow whose result is a reference or a borrowing value, as `f: () => &i64` or `const f = (): &i64 => &b;` is, since what it returns may point into its captures, which no contract names. `users.map(u => u.name)` is a move through a reference: EN0603 with a `.clone()` fix-it.

A non-capturing arrow or a safe named function also coerces to `fn(...)`, which is `V`, Copy, and storable.

**Local functions (N13).** A function written among a program's top-level statements (6) is an ordinary function with one hidden argument per top-level variable it uses: a reference to an owned variable, or a copy of a reference variable. The arguments are evaluated at each call, so `inc()` behaves like `inc(&count)`. Its hidden arguments also include those of every local function it calls, directly or through others, so a `relay()` that calls `grow()` takes `grow`'s too; the declared-above rule below still looks only at the names each body writes. Calls conflict with live loans as explicit arguments do, and with a loop's hold (5.6), and they count as uses for liveness, init dataflow and narrowing. A local function cannot move a captured variable (EN0617), rebind a captured reference (EN0616), return a reference derived from one (EN0714), or become an `fn` value (EN0803); one with no hidden arguments, counted this way, can become an `fn` value, and as a closure argument (C12) a local function captures all of them and may store nothing: a store whose target or stored value is a hidden argument, as `lx.setSrc(&t)` in `function bind(): void { lx.setSrc(&t); }` is, makes `run(bind)` EN0616 at the argument, as the same store in an arrow is (5.4), while a direct call `bind()` applies the store as any call does. Hidden arguments exist only where a call site evaluates them, so a local function that has some may be called only from the statements, arrows among them included, and from other local functions: a call from a class method or any other function is EN0313. For the same reason, a decorator that makes the compiler, a runtime or foreign code its caller (`@entry`, `@panicHandler`, `@interrupt`, `@naked`, `@abi`, `@devMigrate`) is EN0806 on such a function, while `@mustUse`, `@section`, `@requires` and `@was` stay allowed. Writing a captured `const` is EN0608 at the write. It may use only top-level variables declared above it, and a call above a variable it reads is EN0618 (6). So `let count = 0; function inc(): void { count += 1; } inc(); console.log(count); inc();` is valid, `const r = &count; inc(); console.log(r);` is EN0706, and `for (const x of &q) { reset(); }`, where `reset` changes `q`, is EN0706. This is not how arrows capture: an arrow holds its loans for as long as it will still be called.

### 5.6 Binding modes

`match` binds no variables: an arm names values or an enum case, and inside it the subject itself is narrowed (6). Destructuring and `for...of` bind, by the rules below.

**Destructuring** (3.3) reads each named field into its own variable. What it binds is set by what is destructured:

| Destructured value | Bindings |
|---|---|
| A reference: `&ada`, a `&Person` parameter, an item of a borrowed `for...of` source | `&F` for each field, with a loan on the source by O7 |
| An owned place or rvalue | `F` for each field: Copy fields are copied, and the others move out of the source |

So `const { name, age } = &ada;` keeps `ada` whole, and `for (const { name, age } of &people) { console.log(name, age); }` reads each person. Using a moved-out field afterwards is EN0601, `` `ada.name` was moved into `name` ``, with the label `` `ada.name` moved here `` at the pattern and `used after the move` at the use, and `` help: destructure a reference to keep `ada` whole `` with the fix `const { name, age } = &ada;`. A class with a destructor cannot be partially moved (EN0607). When a field's type is itself a reference, its binding is a copy of that reference (O7). Copy fields under a reference read through by 4.5.

Patterns nest, and the table applies at every level: `const { name: who, pos: { x, y } } = &ada;` gives references to `ada.name`, `ada.pos.x` and `ada.pos.y`; `const { scores: [first, second] } = ada;` copies two `int`s; `for (const [i, { name }] of &pairs)` gives `i` and `name` as references into each pair. A nested move is reported like a flat one: after `const { name, pos: { x } } = ada;`, `ada.name` is EN0601. At any depth, a `= default` is EN1010, which the parser reports, and an array source is EN1042, which needs the source's type and so comes in phase 2.

**`for...of` sources.** `for (const x of &q)` borrows `q` and holds it for the whole loop; `x` refers to each element in turn, and whether the body reads or writes through `x` is inferred. `for (const x of q)`, where `q` is not a reference, takes `q`: each element moves out with no copy, and using `q` afterwards is EN0601, `` `q` was used up by the loop ``, with the labels `` the loop takes `q`, because there is no `&` `` and `used here afterwards`, and `` help: to keep `q`, borrow it: `for (const x of &q)` ``. A source that is already a reference (`xs: &i64[]`, `xs: &Slice<i64>`) borrows. A field reached through a reference (`this.items` in a method, `h.items` with `h: &Holder`) cannot be taken, because that would move out through a reference (EN0603), so it is written `&this.items`. Ranges `a..b` and rvalues (`[...q]`, `q.clone()`, a call result) are consumed.

The source is classified once, after type checking and member lookup, and the first row that fits wins. A **path** has the shape of a narrowing path (4.8): a local or `this`, followed by field projections, `*` on a reference or `Box`, and narrowed nullables. It never contains an index, a call, a static or a raw pointer deref. A leading `&` is part of the source's form and not of the path. In the table `F` is the element type and `x` the loop's binding.

| Source | Evaluated | `x` has type | Loan |
|---|---|---|---|
| `&path`, where the path has an owned array type | Read every turn | `&F` | The loop holds the path (N9). Each `x` is an ordinary loan, exclusive when `x` is write-live (O7), as when the body writes through it or keeps it in a binding written through later, live while any binding holding it is, and from the loop's one bind site, under this turn's key, whose loans the loop's own head and bind skip (O2) |
| Path of type `&T[]`, `&T[N]` or `&Slice<T>` | Read every turn | `&F` | The same, and the hold also covers every reference slot or reference field the path goes through |
| `&` of a place containing an index, or of a projection from a temporary: `&grid[r]`, `&make().items` | Once | `&F` | One on the place for the whole loop. A temporary lives for the whole statement (5.7) |
| `&` of a static or of a raw deref: `&TABLE`, `&*p` | Once | `&F` | None (5.9) |
| Reference-typed rvalue: a call, `c ? a : b`, `r!` | Once | By its type | The loop keeps the value's loans for the whole loop |
| Owned place with no `&`, or owned rvalue: `q`, `[...q]`, `q.clone()` | Once | Owned `F` | None. The loop takes the value: `T[]` is consumed, and its remaining elements drop on `break`, `return` or `?`. `T[N]` is copied element by element and needs Copy `T`, otherwise EN1015 with a help to use a `T[]` |
| `a..b` | Bounds once | Owned integer | None |

**The loop holds its source (N9).** A loop over `&path`, or over a path that is already a reference, holds loans on the source path and on every reference slot or reference field the path goes through, the loan on a reference field sitting on the field itself, so that repointing the field is a change of the source. A phantom slot holds them and is used at the loop head, so they are live while a next head is reachable within the same run, because taking the hold at the pre-header defines the phantom slot anew, replacing what an earlier run left in it. The phantom slot has no run-time storage, and the path is still read at the head, whose tag checks and length read are part of the head (O11). Assigning or structurally changing the source inside the loop is therefore an error, also through a called function (`reset(&h)`), a local function or an arrow (5.5): `q = []`, `q.push(9)`, `q[0] = 9` and `q = []; continue;` are rejected, while `q = []; break;`, `q = []; return;`, `q.push(1); break;` and assigning after the loop are valid, because no later turn exists. A move of the source in the body is rejected the same way (EN0709), so `take(q);` and `take(q); q = [];` are errors and `take(q); break;` is accepted. A structural change and a reassignment are both EN0706, also when a written loop variable has made the hold exclusive:

- a structural change gives `` cannot mutate `queue` while iterating over it ``, with the label `immutable borrow begins here` at the source and `conflicting mutable access` at the change, `= note: structural mutations may invalidate the iterator`, and `help: collect new jobs separately, or loop over a copy` with the fix `for (const job of [...queue]) {`;
- a reassignment gives `` cannot reassign `q` during iteration ``, with the label `` `q` is borrowed here `` at the source and `cannot reassign while borrowed` at the assignment, and `` help: iterate over `q.clone()` if reassignment is intentional `` with the fix `for (const x of q.clone())`. Repointing a reference field the path goes through is a reassignment too: `this.view = other;` in `for (const x of this.view)` gives `` cannot reassign `this.view` during iteration ``.

So `for (const job of &queue) { queue.push("retry"); }`, which would never stop, is a compile error by the borrow rule, not by any termination analysis; `while (true)` stays valid. A loop over a copy may change the original: `let q = [1, 2, 3]; for (const x of q.clone()) { console.log(x); q = []; }` prints `1 2 3`, and so does the same loop over `[...q]`.

```ts
let queue = ["a", "b"];
for (const job of [...queue]) { queue.push("retry"); }  // a copy: 2 turns, and `queue` then has 4 items
for (const job of &queue) { queue.push("retry"); }  // EN0706: the loop holds `queue`
```

**Writing through the loop variable.** Whether a loop writes through `x` is inferred from its body: `let nums: i64[] = [1, 2]; for (const n of &nums) { *n *= 2; } console.log(nums);` prints `[2, 4]`, `bump(n)` in the body with `function bump(x: &i64): void { *x += 1; }` gives `[2, 3]`, and `for (const item of &items) { item.count += 1; }` compiles when `items` is `let`. A written loop variable makes the loop's hold exclusive. Pushing to the source and assigning it stay errors: `nums.push(9)` in the body is `` cannot mutate `nums` while iterating over it ``. There is one loop form, and writing needs a source that may be written: a loop whose binding is written through, in its body or later through a binding that keeps it, writes through its source, so at the pre-header its source is checked as an argument to a parameter that writes is, the hold's path for a path source or the value evaluated once for any other source, and a read-only source is reported once, at the source, with its mark's code (4.11). The binding carries its source's mark, as any `&` of the element would (4.11), so a binding over a read-only source stays read-only wherever it goes, returned or passed on, and a write through it, or through a slot that kept it, is reported only at the source. So `for (const t of &TABLE) { *t = 0; }` is EN0608 for a top-level `const TABLE`, and a loop that writes through the elements of a call result that may point at a constant is EN0616. Each turn binds a different element, and every turn binds at one site whose loans the loop's own head and bind skip (O2), so a reference kept from an earlier turn may still be used, and written, after later turns, as Rust's `iter_mut` allows: `let q: i64[] = [1, 5, 3, 7]; let keep: &i64 | null = null; for (const x of &q) { if (x > 2) { keep = x; } } if (keep != null) { *keep = 0; } console.log(q);` prints `[1, 5, 3, 0]`, as a function that finds the last match and returns it does. That holds over a narrowed source path too, whose tag checks belong to the head and the bind: with `public class Bag { public items: i64[] | null = null; }`, `if (b.items != null) { for (const x of &b.items) { if (*x > 2) { keep = x; } } }` followed by the same write through `keep` compiles. Everything else still finds the site's loans overlapping: `q[0]` read or written, a nested loop over `&q`, or another loop over `&q` later, while a kept binding is still used. Two loans of the site compared with each other, as the parts of one result are (N6, 5.4), are told apart by their keys (O2): a loan of this turn and one of an earlier turn of the same run point at different elements, so with `function pairBig(xs: &Slice<i64>): [&i64, &i64] | null { let a: &i64 | null = null; for (const x of xs) { if (x > 2) { if (a != null) { return [a, x]; } a = x; } } return null; }`, which returns the first two elements above 2, found in different turns, the pair is writable, as Rust's `iter_mut` allows: `let q: i64[] = [1, 5, 3, 7]; const p = pairBig(&q); if (p != null) { *p[0] = 0; *p[1] = 0; } console.log(q);` prints `[1, 0, 0, 7]`. A pair from two turns of one run is writable when it is formed inside the loop body, over a parameter, an owned path or a narrowed path, or over a view or a copy of one, or over the binding of an outer loop over one, since the loans a binding takes from its source at the bind are told apart by the same keys (O2): with its loop written `for (const x of xs.slice(1))`, `pairBig` over `let q: i64[] = [9, 1, 5, 3, 7];` gives a writable pair, and the same writes print `[9, 1, 0, 0, 7]`, and a loop over a copied reference, `const r = xs; for (const x of r)`, gives a writable pair as well. So do two turns of an inner loop over the binding of an outer one, `for (const x of rows) { for (const y of x) { ... } }`, which give two cells of one row, since both parts hold the outer loop's loan only via the inner bind (`TESTING.md` `TK-03-inner-pair`). A reference to the source taken any other way is not told apart from a binding: with `pairBig`'s `a` starting as `&xs[1]` before the loop over `xs.slice(1)`, `[a, x]` may be one element, so the pair is read-only. Two shapes that Rust's `iter_mut` accepts stay read-only, each a listed difference from Rust (`TESTING.md` section 13): a pair formed after the loop from bindings kept in two turns, as a `firstTwo` that sets `a` in one turn and `b` in a later one, breaks, and then returns `[a, b]`, and one that keeps the last two matches, as a `lastTwo` whose loop runs `b = a; a = x;`. Writing through a part of either is EN0616, with `` help: return the pair inside the loop ``, the shape of `pairBig`. Two loans of one turn, as in `for (const r of rows) { return [r, r]; }`, overlap, and so does a loan kept from an earlier run against any other, as in a `twice(rows: &Slice<i64[]>): [&i64[], &i64[]]` that returns bindings kept from two runs of one loop inside a `while`, or that joins one kept from the first run of a loop over `rows.slice(0)` with this turn's binding in the second, `stale ?? x`, and returns it beside a binding of an earlier turn of that run, since the pre-header makes the marks of the first run's bindings plain (O2), so each returns a read-only pair, and passing their parts to a function that writes one, as `clash(p0, p1)` does with a `clash(x: &i64[], y: &i64[])` that runs `*y = [9];`, is EN0616. A loop takes its hold at its pre-header, where it starts, before its first turn, as a borrow of the source checked against every live loan, with the code its mode gives (O11). The hold its own earlier run took is not among them, because the pre-header replaces it (N9): `let q: i64[] = [1, 2]; let n = 0; while (n < 2) { for (const x of &q) { *x += 1; } q.push(n); n += 1; } console.log(q);` prints `[3, 4, 1, 1]`, and `q.push(1); break;` stays valid in a loop nested this way. A nested loop over the same source is no change of it, so its hold, head and bind report by mode as well: a writing loop over `xs` inside a writing loop over `xs` is EN0707 at the inner source. The pre-header, which renames the site's loans to earlier runs (O2), keeps the one bind site sound when the loop runs again, inside an outer loop, while a binding kept from its earlier run is live: with `let n = 0; while (n < 2) { for (const x of &q) { keep = x; } n += 1; }` before the same write through `keep`, the hold is exclusive, because `x` is written through `keep`, and the second run's `&q` is EN0707 at the pre-header. A contract records `this` as a whole, so `this.add(x)` in a loop over `&this.items` is rejected even when `add` changes only another field.

**Loops that grow.** A loop that adds to its array is an index loop, which reads the length on every turn: `let q = [1, 2, 3]; for (let i = 0; i < q.length(); i++) { if (q[i] < 10) { q.push(q[i] * 10); } console.log(q[i]); }` prints `1 2 3 10 20 30`. A worklist uses `pop()`, which returns `null` when the array is empty: `let work: i64[] = [3]; let next = work.pop(); while (next != null) { console.log(next); if (next > 0) { work.push(next - 1); } next = work.pop(); }` prints `3 2 1 0`.

### 5.7 Drop

- **D1.** A drop is scheduled for every owned local, parameter and temporary with a non-trivial type on every exit: fall-through, `break`, `continue`, `return`, `?`. Elaboration with init dataflow makes each static, flag-guarded or per-field. A partly moved enum, nullable or `Result` first switches on its tag, and then handles only the active case's fields, so a move flag means something only inside its case's arm. Copy types and types with no destructor in their tree drop trivially.
- **D2. Order.** Locals and parameters end in reverse declaration order. Temporaries end, in reverse creation order, at the first boundary in the table below, always before any local of that block ends. For a value, the destructor body runs first, then its fields in reverse declaration order; a derived class's destructor and own fields come before its base's, and before the base's turn the drop glue writes the base's method table into the object's hidden pointer, as C++ does, so a call through the table, or printing `this`, in the base's destructor runs the base's code, which reads only fields that are still alive: with `public destructor() { console.log(this); }` in `Animal` and a `Dog` that adds `tricks`, dropping `new Dog("Rex")` prints `Animal { name: 'Rex' }`; a call that reaches an abstract method this way, in the destructor of an abstract base, finds in its slot a stub that panics, as a C++ pure virtual slot holds one, `` `Shape.area` is abstract, and the subclass that implements it is already cleaned up `` (9.1); an enum case's fields go in reverse declaration order; array elements go by decreasing index, then the buffer; a `Box`'s inner value goes before its block, and a `Box<A>` of a class that can be extended reads the size and alignment from the object's method table before it cleans up the contents, so that reset never changes the size the block is freed with; a `string` frees only if `cap > 0`. So locals, temporaries and elements end in reverse creation order, and one class's fields in reverse declaration order, as in C++, where Rust drops fields and elements in declaration and index order; and a derived class's destructor and fields go before its base's, as in C++, although a subclass sets its own fields before its base part is built (4.3), so along a chain fields are not cleaned up in reverse creation order.

  | Temporaries created in | End |
  |---|---|
  | Condition of `if`, `while`, `do...while`, `for`, or a ternary | Right after the condition, before the body runs or the condition is re-tested |
  | Step of a `for` | Right after the step |
  | Right operand of `&&` or `\|\|` | Right after that operand |
  | Subject of `match`, source of `for...of` | After the whole statement |
  | `let`/`const` initialiser, expression statement, assignment, `return` | At the end of the statement |

  So `while (ok(&("a" + "b")) && n < 3) { n += 1; }` drops its string once per test and never across the body.
- **D3. Assignment** `x = v` evaluates `v`, drops the old `x` if initialised, then stores. `_` as a local name is ordinary and lives to scope end; it discards nothing (`void e` does, 6).
- **D4. Partial moves** from an owned path are allowed unless the type at any prefix has a destructor (EN0607; use `.clone()`), or is a type parameter, an implicit one for an object-type parameter (4.3) included: the body is checked once for every type, and the value may be a class with a destructor or with fields the bound does not list, so `function keepName(x: { name: string }): string { return x.name; }` is EN0607, `` cannot move `x.name` out of `x`, because `{ name: string }` may have a destructor `` (H41). That holds for a `@devMigrate` hook's `old` too until the dev runtime's quarantine of the fields a hook leaves (8.5, `DEV_RUNTIME.md` section 7) is built, at M6: before then a hook copies what it keeps, `old.name.clone()`. The remaining fields drop normally, by per-field flags where needed. Only a `move` method may move `this` or a non-Copy field out of it: `public move open(): Letter { return this.inside; }` gives the caller `inside` uncopied and disposes the rest of the object, as the method's own class, which EN0458 and, in generic code and per-class copies, the method's entry check make it for a class that can be extended (4.3), when the method ends, so returning `&this.inside` instead is EN0710 (5.4), and using `e` after `const l = e.open();` is EN0601, `` `e` was used up by `open` ``. In a method without `move`, the same move is EN0603 at the method: `public getName(): string { return this.name; }` gives `` cannot move `this.name` out of `this` ``, with the label `` `string` gives the caller its own value `` and the helps `` to return a reference to the same field, write `&string` ``, `` to return a copy, write `this.name.clone()` `` and `` or mark the method `move` to give up the object ``. A constructor never gives up its object, so the same move in one, as `shout(this.name)`, is EN0603 too, without that last help. A class with a destructor cannot hand out its fields even from a `move` method, which may still return other values, and its destructor runs when the method ends. `Box` contents and array elements can never be partially moved.
- **D5.** `dispose(x)` ends a value early. It is a compiler form (section 6), because it takes any value by move, a borrowing value or a reference included, which a generic `T` cannot (4.1): the value's scope ends at once, so a borrowing value's loans end there too, and for a reference it does nothing. It does not call the destructor directly, and it works on any value, including conditionally (`if (done) { dispose(f); }`). For a class `File` whose destructor prints `` `drop ${this.name}` ``, `const f = new File("a"); dispose(f); console.log("end");` prints `drop a` then `end`. A destructor cannot be called by name: `f.destructor()` is EN0606, `` help: use `dispose(f)` to end `f` early ``. `mem.forget(x)`, a compiler form taking any value the same way, ends it without running its destructor, and is safe: leaks are safe and no memory-safety property relies on a destructor running. `mem.replace(&x, v)` and `x.take()` (on `T | null`) cover moves out from behind a reference.
- **D6. No unwinding.** A panic runs no destructors. Allocation-balance checks exempt panicked runs.

### 5.8 Why it is sound

These invariants hold at each MIR step for programs with no `unsafe`, assuming correct compiler and libraries, but not correct interface files, because each is checked when it is loaded, its stored code verified against the current declarations, its contracts recomputed from that code and phase 3 run on it again (4.12):

- **I1.** References exist only in frame slots and in the reference fields of borrowing values, which themselves live only in frame slots, directly or inside another borrowing value (R1).
- **I2.** A reference in frame `F` points into memory owned by `F` or an older frame or static storage. A reference reaches an older frame only by `return`, gated by R3 at both ends, or through a function that stores a parameter into a borrowing value, in `this` or behind another parameter, which the checker infers (R2) and which adds that argument's loans to the borrowing value's loan set in the caller (5.1). That argument is borrowed for writing when the value's class writes through its reference fields, unless the field it is stored into is declared `readonly &` (N3 (e)), whose loans join a read set that the value only reads through, takes nothing reached from the object's reference fields that are not `readonly &` while its class writes through them, and is what a result reached only through such fields holds in place of the object (5.1), a returned reference whose source is also stored, or whose parts may point at the same data, nested parts, a nullable's payload and the parts of a returned call's result included, is read-only (N6), and when the store borrows for writing, that borrow stays live in the callee until it returns, so no path of the callee both stores that argument and returns a reference derived from it (5.4). A copy of a borrowing tuple takes a new loan per reference part (O7), a reference to a borrowing tuple held directly makes its parts write-live (N3), a borrowing class that writes through its reference fields is never Copy (O4), and a field of borrowing tuple type is a reference field (4.3), so no exclusive loan gets a second holder that may write through it without a loan between them. The second path came with borrowing classes, and its soundness is still under review.
- **I3.** While a loan is live, conflicting accesses are rejected, so the pointee cannot be freed, moved, reallocated, change case or be written through another path. A call's writes are not visible in the caller's syntax: the callee's contract states them, and write-liveness (N3) gives each loan the mode of its most demanding later use. No write through a pointer can add a loan invisibly, because pointees contain no references (R2); for a borrowing value, the one exception, the checker infers each function that stores a parameter into one, in `this` or behind another parameter (R2), adds whatever a write through a reference puts into one to its loan set (O9), and lets no position without a body declare a store, nor an arrow store into a captured value, nor a local function passed as a closure argument store through a hidden argument (5.4, 5.5).
- **I4.** Every heap block has one owner and is freed once: move and init dataflow plus elaborated drops.
- **I5.** The destructors of a `V` value reach only its own tree, because `V` holds no references and safe code has no writable globals; so drop check is unnecessary. A borrowing class's destructor may read or write through its reference fields, so the end of life of a borrowing value on which such a destructor runs is a use of its loans (O10), and its writes count toward the class's flag (4.3).
- **I6.** Narrowing facts cannot be invalidated invisibly: a reference made to a narrowed path or a prefix is recorded, and if it turns out to write (N3), a later use typed through the fact with no new test between is EN0401 (N2, 4.8).
- **I7.** Bounds, overflow, division, conversions and stack limit are dynamically checked and panic.

Hazards closed by construction. Row IDs are stable and each has a fixture (`TESTING.md` section 18).

| ID | Hazard | What closes it |
|---|---|---|
| H01 | Reference into an array followed by `push` | `[*]` overlaps the exclusive borrow of `a` that `push` takes |
| H02 | Reference into an enum case's field followed by an overwrite with another case | The field's loan overlaps the whole place |
| H03 | `T[]` used as `(T \| null)[]` | No subtyping, nothing nests, no coercion on a spread operand |
| H04 | A writing reference to a reference, shrinking its target's lifetime, and rust#25860 | No `&&T`, no lifetime parameters; a borrowing value has one loan set for all its reference fields but its `readonly &` ones, whose read set is only read through and takes nothing reached from the others while the class writes through them (5.1), stores into a borrowing value, in `this` or behind another parameter, and writes through a reference into one are inferred (R2, O9), and a stored argument is borrowed for writing when the class writes through its reference fields, unless the field is declared `readonly &` (N3 (e)) |
| H05 | Self-reference | Reference fields only in borrowing values; a loan a field holds on part of its own object conflicts with every later move or write of that object, because the holder's own place is never exempt (O11) |
| H06 | `T := &U` smuggled through a container | `T` ranges over `V`, and a borrowing class is no generic argument (EN0701) |
| H07 | Hole behind a reference during unwinding | No unwinding, no moves through references |
| H08 | Copy-plus-destructor double free | A class with a destructor, own or inherited, cannot be Copy (EN0418) |
| H09 | Guard-page skipping | Descending stack probes and limit checks |
| H10 | Destructor called through a structural interface | A destructor is never a member, and calling one by name is EN0606 |
| H11 | Precondition laundered through a function pointer | `unsafe fn`, EN0803 |
| H12 | Duplicate owner through `Atomic<T>` with non-Copy `T` | Sealed `AtomicValue` |
| H13 | Allocator re-entered from an interrupt, a panic or itself | EN0824 |
| H14 | Size arithmetic wrapping to a small allocation or frame | EN0435, `isize.MAX` capacity limit |
| H15 | Non-UTF-8 `string` built in safe code | `pushByte` panics on bytes from `0x80` up |
| H16 | Misaligned reference to a packed field | EN0804 on every MIR `Ref`, EN0826 |
| H17 | Writing through a read-only reference or a `const` via a by-pointer argument | The caller's temporary is elided only under the rule of `ARCHITECTURE.md` section 7.6 |
| H18 | Narrowing fact invalidated between the check and the projection | Facts die in O6 order, recorded references are checked by N2, `CheckTag` adjacent to the projection |
| H19 | A writing reference aliased through a closure capture | A capture is a copy with its own loan on `*r` (O7) |
| H20 | `for...of` element reference kept across a push that reallocates | The loop holds its source (N9), so a push in the body is EN0706 while a later turn can follow; each binding is an ordinary loan, so using `x` after a push and before `break` is EN0706 too |
| H21 | Stale length or index after a `for...of` source shrinks, is assigned or is rebound | The hold rejects each of these while a next head is reachable (N9); `Len` is still read at every head and `CheckBounds` runs before every projection, never elided |
| H22 | `for...of` source moved in the body and read by a later turn | The hold rejects the move while a next head is reachable (N9); init dataflow at the head and the bind gives EN0611, and both stay in MIR even for an unused binding |
| H23 | `for...of` element reference into a packed field, with no source `Ref` to catch | EN0804 is a rule on the place, not the field |
| H24 | Narrowed `for...of` source cleared in the body, directly or through a reference | The hold rejects the clear while a next head is reachable (N9); the state after the loop joins the head's exit edge with every `break`, so a read there is EN0303 or EN0401 by its use; `CheckTag` at the head and the bind |
| H25 | Hidden index past a zero-sized `T[]` whose length no allocation limits | `push` panics `capacity overflow` at `isize.MAX`, so `_i < _n` cannot overflow |
| H26 | Spread source that cannot give an array header: `T[N]` read as `T[]` | Every spread source becomes a `&Slice<T>` (C18) for the `extendCloned(o: &Slice<T>)` call it lowers to, never a `&T[]` |
| H27 | Two references bound in different turns or runs of one `for...of` loop, alive together | The binds share one site, whose loans only the loop's own head and bind skip (O2, O11); a later run's hold meets loans kept from an earlier run at its pre-header (5.6); each loan of the site carries the key this turn, earlier turns or earlier runs, renamed at each bind and at each pre-header, and two of them are disjoint only as this turn's against an earlier turn's, which bound different elements of one run, so N6, which compares every reference part of a returned value, through nested tuples, nullables, locals and call results, lets only such parts form a writable result (5.4); a loan that a binding takes from its source at the bind carries the loop's mark until the loop's next pre-header, which makes it plain, and is decided by that loop's keys when both parts hold it only that way, an outer loop's loan that an inner loop's bind marked included, while a plain copy, as from `&xs[1]`, is compared by its whole path, pair by pair, against a loan the other part holds via the bind too, so no loan is left out of the comparison, and a pair formed after the loop, or kept across turns, stays read-only (O2, 5.6) |
| H28 | A `for...of` binding over a read-only or read-set source, returned or passed on as writable | The binding carries its source's mark, as any `&` of the element does, and a write through it is reported once, at the source (N5, 5.6); a result with a source reached only through `readonly &` fields is read-only by N6's own reason, whatever marks its flows carry (5.4) |
| H29 | An override that stores more than its base body declares: the whole parameter where the base keeps only its fields, or into a read set the base does not use | Fitting compares stores with their bits: the override's store takes only what the fields hold where the base's does, only the read set where the base's does, and joins the read set only where the base's does (5.4) |
| H30 | A borrowing value returned by value from a call, or read out of a field, that keeps no read set, so what it gives through its `readonly &` fields holds nothing, or that counts nothing as held by its other fields, so its `readonly &` field takes what they write through | It keeps its whole set as its read set, since no contract says which of a result's loans are read-set loans, and counts its whole set as held by its other fields too, as a by-value parameter does, so its `readonly &` fields take nothing it holds, but for what they already reach, through a call that only narrows them (5.1, H36) |
| H31 | A part of a returned value that reaches a parameter by a path that took no loan through it, a reference copied without a new loan, the parameter itself or a borrow made before a `let` parameter was repointed, hidden behind a loan through that parameter that came by another path, so two writable parts are one place | Each parameter's key in a slot records whether every way it came brought a loan through that parameter; a copy that came without one wins wherever two meet, repointing a `let` parameter clears them all, and N6 compares a key that came that way as the whole parameter (O2, 5.4) |
| H32 | A part of a tuple local compared by the loans its literal held, after a loop's new run renamed them or a repointed `let` parameter killed them, or a call result kept in a local and then written in part, so it looks disjoint from a part that is the same place | Its parts are compared with each other by what the literal held, and a call result's as one part by the call's arguments, only while nothing writes the local or borrows it for writing before the `return`, and with every other part by what the local holds at the `return` (5.4) |
| H33 | A reference copied with no loan, out of a reference field or a tuple part, or as a whole nullable reference, so one exclusive loan gets two holders with nothing between them | Such a copy takes a loan, through the value it is read from or on the nullable's payload, shared unless it is written through, as an auto-borrow or a reborrow does (O7) |
| H34 | A store into a value reached through a consumed `this` or a by-value borrowing parameter, which no caller's value carries back, so that value keeps a reference past its target's life | A call that stores into any value holding a loan of such a parameter, the value itself, one reached through it or a local built from what it holds, is EN0616 (5.4) |
| H35 | A module with no source, rechecked or loaded against an import whose contracts or flags moved, keeping an override, a satisfaction, an `implements Copy` or a narrowed use that no longer holds | A recheck or a load runs all of phase 3 again, every comparison and EN0418 against the recomputed flags included (4.12) |
| H36 | A read-set-only store of a parameter into itself, whose read-set check the caller skips, putting into a value what one of its other fields writes through, or left out of the caller altogether, so that a value behind one of its reference fields keeps a reference to data the caller then changes or frees | It moves only what the value's own `readonly &` fields reach, which nothing its other fields write through may hold (5.1), a reference read from one goes into no field written through (N3 (e)), fitting holds every override to such a store or none (5.4), and the store still applies at the call, so a value behind the value's reference fields that receives it holds the read set's loans (5.4) |
| H37 | A borrow or copy through a reference field of a borrowing value reached through a local reference, as `const r = &t; const e = &r[0][0];`, holding what the value's fields hold but not the reference's own loan on the value, so the value changes, and frees what the token points at, once the reference is dead | Such a borrow or copy keeps the reference's own loans on the value beside what its fields hold, as every borrow through a reference does (O9); only a read-set token through a `readonly &` field, which nothing writes through, leaves them out (5.1) |
| H38 | A subclass whose own bodies write through nothing, while its base's bodies write through the base's fields of the same value, counted as never writing through its reference fields, so a result read through its fields, a store into it, its read-set check and `implements Copy` all trust that its stored loans are never written through | A class's flag is set whenever its base class's flag is (4.3) |
| H39 | A copy of a reference part of a tuple held directly in a local, a parameter or a temporary, or of a nullable reference's payload, that takes no new loan and reads only the reference itself, so it reaches data that another copy's exclusive loan still guards, and a write through that other copy reallocates the data under a reference made from this one | A copy that takes no new loan still reads what the reference points at, checked as a shared borrow of it, as `&*r` of a reference local is, so it is EN0708 while such an exclusive loan is live (O7) |
| H40 | A tuple local passed by value to a call beside another of the callee's source arguments, compared with that argument by the loans its literal held after a repointed `let` parameter killed them, so the call's result counts as one part although the two arguments are the same place | The parts of such an argument are compared with each other by what its literal held, and with every other argument by what the local holds at the call (5.4) |
| H41 | A field moved out of a value whose type is a type parameter, an implicit one for an object-type parameter included, in a body checked once for every type, while the value may be a class whose destructor needs that field or with fields the bound does not list, so the rest of the value is dropped whole, the moved field included | No field moves out of such a value, EN0607 (D4), a `@devMigrate` hook's `old` included until the dev runtime quarantines the fields a hook leaves (M6) |
| H42 | A `readonly` field written through an object type or a fields-only interface, whose body is checked once for the type and sees no `readonly` | A class passed for such a type to a parameter the callee may write, behind `&` with a Write permission or by value marked `let`, while the type names a field the class declares `readonly`, is EN0609 at the argument, and writing through a result that has such an argument among its sources is EN0609 at the call (4.11) |

This is not mechanised. Accepted programs are a fragment of safe Rust under Polonius, where each contract's sources are one named lifetime, each borrowing class is a struct with two lifetime parameters, `'r` for its fields declared `readonly &`, which are `&'r T`, and `'a` for its other reference fields, which are `&'a T`, or `&'a mut T` when the class writes through them, a method that stores into a `readonly &` field a reference reached from another reference field taking `where 'a: 'r`, and one that stores a reference reached from a `readonly &` field into a reference field not declared `readonly &` taking `where 'r: 'a`, which only a class whose flag is off can do, since with the flag on rule (e) reports the mark, EN0616, a method's result reached only through `readonly &` fields being `&'r T`, as `fn peek(&self) -> &'r [u8]` is, one that reaches `this` only through `readonly &` fields and has other sources being `&'x T` for a fresh `'x` with `where 'r: 'x`, each other source taking `'x`, and one reached through both kinds of field, in a class that does not write through its reference fields, being `&'a T` with `where 'r: 'a`, and each closure is a `&mut dyn FnMut`. That gives a test oracle: translate accepted programs to Rust and check them with `rustc`; the VM's fault detector treats any dynamic fault in an accepted program as a soundness bug. A loop over `&q` translates to `for x in &q`, or to `for x in &mut q` when `x` is written through, in the body or after it through a binding that keeps it; a loop that takes `q` translates to `for x in q`; a loop over a reference source that cannot be repointed, a parameter not marked `let`, a `const` reference local, a call result or another source evaluated once, translates to `for x in src.iter()`, or `src.iter_mut()` when `x` is written through; and one over a reference slot `r` that can be, a `let` local, a `let` parameter or a reference field, translates the same way when the body never assigns `r`, and otherwise to `let s = &mut r; for x in s.iter_mut()`, or `let s = &r;` with `iter()`, so that repointing `r` in the body is rustc's E0506 where it is EN0706. One case stays a named disagreement: `r = other; break;` in the body while a binding kept from the loop is used after it, which Enrang accepts and the twin rejects with E0506 (`TESTING.md` section 13).

### 5.9 The boundary of `unsafe`

`unsafe { }` blocks and `unsafe function` bodies grant **exactly five** powers:

1. dereference raw pointers, including `*p` places and the `read`, `write`, `readVolatile`, `writeVolatile` pointer methods;
2. call `unsafe function`s, `unsafe` methods, `declare function`s and `@requires` functions, and call through an `unsafe fn` value or any function pointer with an `@abi` tag, which runs foreign code;
3. `asm(...)`;
4. read, write or borrow `unsafe let` variables;
5. access `@at` storage.

`unsafe` does not relax type checking, moves, the loan check on references, R1, R2, or definite init. A reference created from a raw pointer (`&*p`) holds an empty loan set: its validity is the writer's obligation.

**Permissions (N12).** Raw pointer flow never decides a permission: in a function with no `unsafe`, raw pointers are inert. In a function or constructor whose body contains `unsafe` or `asm` (nested arrows included), in an `unsafe function` and in an `@naked` function, every `&` parameter and `this` count as written, and so does every reference read from a reference field of a borrowing class, where it is read, which sets the class's flag (4.3) in whichever of its bodies it is read, a constructor, a `static` method or an arrow nested in one included, except one read from a field declared `readonly &`, or from a tuple part declared `readonly`, which promises that it is only read, as `const` does. `const` before the method name promises that `this` is only read, references read from its reference fields included, and `const` before a reference parameter promises that parameter is only read. So `public set(v: i64): void { unsafe { *this.p = v; } }` counts as changing the object, and `public const get(): &i64 { unsafe { return &*this.p; } }` only reads it. A `const` logger can log:

```ts
private unsafe let count: i64 = 0;

public class Logger {
  public constructor() {}

  public const log(const m: &string): void {
    unsafe { count += 1; }
    console.log(m);
  }
}
```

With it, `const l = new Logger(); l.log("a");` compiles. Without the `const` before `log`, the call is EN0614 with `` help: if `log` doesn't change the logger, mark it `const` ``; without the one before `m`, `m` counts as written, and passing the literal is EN0616 (4.11). The safe operations of a `const`-marked body are checked as if those references were shared, transitively, so a `const` body that hands a reference on to a helper counting as a writer is EN0615. `let` before a reference parameter declares Write in any function (4.11). Closure parameters and bound members keep their declared contracts, so the contract of a body containing `unsafe` never depends on `T`. Its stores are still inferred from its safe operations (5.4). The parameters of `@entry`, `@panicHandler`, `@interrupt` and `test.each` functions are declared Read and are exempt from this default (section 7, 12.1). Only code containing `unsafe` writes these marks; application code writes none.

**Obligations.** Unsafe code must uphold, for all safe code it can reach: every `&T` it creates is aligned, non-null and points to a live initialised `T`, except that a view of 0 elements may have a null pointer, as a view of an empty array may (section 11); a reference that is written through is the only access path while it is live, and a reference that is only read sees no write except through `Atomic`; values read are valid for their type (`bool` is 0 or 1, enum tags are declared, `string` is UTF-8 with consistent `ptr/len/cap`); nothing is freed twice; layout assumptions use `@repr` or `@packed`. A permission protects only memory the object exclusively owns. A raw pointer derived from a `&` parameter must not outlive the call in anything safe code can use, except in a returned reference into memory that the function's sources own: the signature defaults of 5.4 make the caller's loan on those sources cover it, which is how the library's `slice`, `get` and `last` return views into `this` that copy nothing. Any other zero-copy view goes to a closure and is never returned. A `&Slice<T>` is a pointer and a length (section 11), so the library builds one with the compiler intrinsic `SliceFromRaw` (`ARCHITECTURE.md` section 2.5), whose result follows the signature-default sources as any raw-derived result does (4.11), so `slice`'s view borrows `this`, and so do the two parts of `splitAt`, which hold no loans of their own and so form a writable pair (8.2). User `unsafe` code builds a view with `Slice<T>.fromRaw(p, n)`, the `unsafe` member of `core` that makes the same intrinsic's view, writable and holding no loans, except as the result of a function with no source, which keeps a read-only mark (4.11) (8.2, 7.1). Building a view of `n` elements at `p`, either way, obliges its caller to an `n` of at least 0 and a `p` that is aligned, and non-null when `n` is above 0, with `n` live, initialised elements at it within one allocation, `n * sizeOf<T>()` no greater than `isize.MAX`, and, for a view that is written through, memory that may be written and that no read-only mark protects, so never a string literal, a top-level `const`, a constant literal view (4.9, 5.4), memory that a `const` root or a by-value parameter not marked `let` owns, or other read-only data, and no other access path while the view is live. Only `@lang` atomic types may write their own bytes under Read. Breaking one is undefined behaviour, confined by the language to programs containing the `unsafe` keyword: the memory-safety theorem in 5.8 excludes them, and `enrang test`'s VM reports violations dynamically where it can. A false `const` is such a memory bug, as a wrong `&self` is in Rust.

**Allocator contract.** An `unsafe let` marked `@globalAllocator` is an explicit unsafe act, and it does not add a sixth power: it is a promise with these obligations. `alloc(size, align)` returns null, or a block of at least `size` bytes aligned to `align`, overlapping no other live block. `dealloc` receives exactly a pointer, size and alignment that `alloc` handed out. The methods never re-enter the allocator; reaching `alloc` from them is EN0824, so the compiler checks this part.

Creating, casting and comparing raw pointers is safe; only using them is not. A function that is not `unsafe` but reads or writes through one of its raw-pointer parameters gets warning EN0828, with `` help: mark it `unsafe function`, or take a reference ``: an `unsafe` block inside it cannot know that an address its caller chose is valid (7.2). EN0828 is not reported for a method whose signature a safe interface member or a safe base method fixes, since neither half of the help could be followed there. A callback type that passes raw pointers is written `unsafe fn`, as `Formatter.fromFn`'s sink is (8.2), so that an `unsafe function` fits it and a safe one still does by C15.

## 6. Expressions and control flow

- **Conditions** must be `bool`. `if (count)` is EN0203. An assignment used as a condition is EN0105 even at type `bool`, with a `==` fix-it (3.4).
- **`match`** follows PHP 8. It is an expression; arms are tried top to bottom, and there is no fallthrough. An arm lists one or more values separated by commas, and `default` catches everything else: `const text = match (code) { 200, 201 => "ok", 404 => "not found", default => "error" };`. Conditions use `match (true)`: `const group = match (true) { age < 13 => "child", age < 20 => "teen", default => "adult" };`. Arm values are literals, negative integers, `null`, enum cases, `Ok`, `Err` and half-open ranges reusing `..` exactly as in `for (const i of 0..n)`, so `200..300 => "success"` covers 200 to 299; other expressions are arm values only under `match (true)`. An arm may carry a guard, `if Expr`, after its values. Arms bind no variables, and `match` never takes its subject: it only looks at it, and an arm that moves a field moves it as anywhere else, as in `let names: string[] = []; match (s) { Shape.Named => names.push(s.name), default => {} }`. An arm body is an expression, a block, `return`, `break` or `continue`. A block has type `void` unless it diverges; `return`, `break`, `continue` and `panic` have type `never`.
- **Enum arms** name only the case, always qualified (EN0502), and inside the arm and its guard the subject is narrowed, so its fields are read directly: `` const label = match (s) { Shape.Circle => `circle of radius ${s.radius}`, Shape.Named => `named ${s.name}`, Shape.Empty => "empty" }; ``. `Result` arms are the bare `Ok` and `Err`, reading `r.value` and `r.error`.
- **Exhaustiveness** uses Maranget's algorithm with a witness. A missing enum case is EN0501, `` `match` doesn't handle `Shape.Empty` ``, with `` help: add `Shape.Empty => ...`, or a `default` arm ``; an unreachable arm is warning EN0503. Numbers and strings always need `default`. A subject whose type is a string-literal union (4.3) needs no `default` when every value is listed, and a run-time `string` is checked into one with a `default`: `match (input) { "left" => "left", "right" => "right", default => null }` gives `Direction | null`. A guarded arm does not count as handling its case: with `Shape.Circle if s.radius > 10.0 => "big circle",` and no plain `Shape.Circle` arm, the `match` is EN0501, `` `match` doesn't handle every `Shape.Circle` ``, with the label `only when this is true` under the guard and `` help: add an arm for the other circles: `Shape.Circle => ...,` ``. On `T | null` the constructors are `Null` and `Present`: every arm value other than `null` and `default` implicitly wraps in `Present`. `null` always matches the outermost level, and a witness for an inner null prints as `a present null`.
- **`null` arms.** In `` match (name) { null => "anonymous", "admin" => "administrator", default => `user ${name} (${name.length()} bytes)` } ``, the arms after the `null` arm see the subject without `null`. Without a `null` arm, `default` also catches `null`, and the subject stays nullable inside it. For a nullable enum subject a missing `null` is EN0501, `` `match` doesn't handle `null` ``, with `` help: add `null => ...,` ``.
- **Ternary** branches must unify; moves are branch-sensitive.
- **Loops.** `for (init; cond; step)`, `while`, `do...while`, `for...of`; labels on loops, `break label`, `continue label`. Falling through without `return` in a non-`void` function is EN0427, except that reaching the end of a function returning `Result<void, E>` means `return Ok();`.
- **`for...of` sources** are `T[]`, `T[N]`, a reference to either, a `&Slice<T>` and a range `a..b`, classified in 5.6: `for (const x of &q)` borrows `q` and holds it for the whole loop, and `for (const x of q)` takes `q`. `for (const x of b)` with `b: Box<T[]>` is EN1015 with a help to write `&*b`. User iterators and `for (const c of "abc")` are EN1015. `for (let i of 0..n)` allows reassigning the loop's copy, which does not affect the iteration.
- **`Result<T, E>`** is the prelude `enum Result<T, E> { Ok { value: T }, Err { error: E } }`, and `Result<T>` means `Result<T, Failure>`, where `Failure` is a `final` prelude class that holds a text. `Ok(v)` and `Ok()` are ordinary generic prelude functions, `function Ok<T, E>(value: T): Result<T, E> { return Result.Ok { value: value }; }`, typed from the expected type; with no expected type, `Ok(5)` takes `Failure` as its error type. `Err(e)` is a compiler form (below). The enum form `Ok { value: v }` stays valid, and is how a `Result` prints, its cases bare (4.4): `const a: Result<i64> = Ok(5); console.log(a);` prints `Ok { value: 5 }`, `Err("boom")` prints `Err { error: 'boom' }`, and `Ok()` of a `Result<void>` prints `Ok`, since a `void` field is never printed. A plain value counts as success: in a function or arrow returning `Result<T, E>`, `return n;` with `n: T` means `return Ok(n);`, as in `return parseAge(a)? + parseAge(b)?;`, and reaching the end of a `Result<void, E>` function, or `return;` in one, means `return Ok();`. An operand that takes its type from context (a bracket or object literal, `[]`, `null`, a number literal, or a string literal at a literal-union type) is checked against `T` there, so `return [lo, hi];` in a function returning `Result<[i64, i64]>` builds the tuple and `return null;` in one returning `Result<Node | null>` is a success; any other operand is typed as usual and wrapped when its type is `T`. Errors are always written `Err(...)`. A plain value that would be a success is EN0455 where `Err` would also take it as it is: a text where `E` is `Failure`, whether fixed, a template or held in a variable, which is any `string` or `&string` expression, a text that is a value of a string-literal-union `E`, or a value whose own type is `E`. In a `Result<string>` function, `return "file missing";` gives `` `"file missing"` could be a success or an error here ``, with `` help: write `Ok("file missing")` or `Err("file missing")` ``, and `return msg;` with a `msg: string` that earlier checks set gives `` `msg` could be a success or an error here ``, with `` help: write `Ok(msg)` or `Err(msg)` ``, or, for a place that no move may leave, as `return this.name;` in a method, `` help: write `Ok(this.name.clone())` or `Err(&this.name)` ``, so every `string` success there is written `Ok(...)`; in a `Result<Token, Token>` function `return Token.End;` is EN0455 too. A value of another error type is a success, because `Err` would first turn it into its text: in a `Result<Token>` function, `return Token.End;` means `return Ok(Token.End);`. This holds wherever a value is wrapped: a `return`, an arrow's expression body, and the ternary branches and `match` arms that flow there, in a function or arrow whose result type is written or expected, and never in an arrow whose result type its body decides, where nothing is wrapped (5.5). The example after this list shows both forms.
- **Error types.** `E` must be an error type, checked by name like `Copy` (4.4): every enum is an error type, and so is `Failure`; a class is one only with `implements Error`, and `string`, numbers, plain classes and `Box<E>` are not (EN0454, `` `string` is not an error type ``, with `` help: return `Result<i64>` and write the text in `Err("...")` ``); a reference or a borrowing class there is EN0701, as in any generic argument, and not also EN0454. Writing `Result<T, E>` implies `E extends Error`. `Result<i64, Error>` is EN1006 with `` help: `Error` is a family of types, not a type; write `Result<i64>` ``. An enum's payload-free cases may carry texts (4.3), and callers match its cases: `Result<i64, AgeError>` with `Err(AgeError.Negative)`. `Error` extends `Display` (4.4), and an error's text is what it prints: a `Failure` prints its text, an enum that writes `fmt` what its `fmt` writes, and a case of any other enum its text or, with none, its qualified name, `AgeError.NotANumber`, followed by every field it has, each printed as anywhere else, `DiskError.BadSector { lba: 42 }` or `PacketError.Truncated { got: [1, 2, 3] }`, so no enum is refused as an error type. A class that implements `Error` prints as any class does: through the `fmt(let f: &Formatter): void` it writes with `writeTo`, or, with none, field by field.
- **`e?`** on `Result<T, E>` yields `T` or returns `Err(e)` from the enclosing function or arrow, which must return `Result<_, E>` with the identical `E` (EN0425, whose help suggests `Result<T>`; EN0424), or `Result<_>`: `?` into a `Result<T>` accepts any error type and turns it into its text, so `fs.readFile(path)?` turns an `IoError` into a `Failure`, and callers can then read only the text. A case with no fields, of an enum that does not write `fmt`, gives its text, or its qualified name, as a static descriptor with no allocation; a text built at run time, for an error type with a case that has fields, for an enum that writes `fmt`, every case of which goes through it, or for an `implements Error` class, allocates, so with no global allocator such a `?` is EN0820 (8.3). A `Failure` moves as it is, as for an identical `E`, also where a generic body's instance gives `E := Failure`, so it never builds a new text. On `T | null`, `?` yields `T` or returns `null` from a function or arrow returning `_ | null`; inside a function returning `Result<T | null>` this is EN0424, because the early return of `?` is never wrapped as a success. Scheduled destructors run, because `?` is an ordinary return.
- **Unused results.** An expression statement of `Result` type is EN0426; `void f();` discards deliberately, dropping the value. Library methods that leave the original unchanged and return a new value (`trim`, `slice`, `toUpperCase`, `toLowerCase`, `replace`, `repeat`, `wrap`, `checked*` and similar) warn when the value is unused: warning EN0453, `` the result of `trim` is not used ``, with the label `` `trim` returns a new string and leaves `name` as it was `` and `help: keep it` with the fix `name = name.trim();`. A user function opts in with the decorator `@mustUse` (`@mustUse function checksum(data: &Slice<u8>): u32 { ... }`). Other values drop silently (`queue.pop();`). There is no `_ = f();`.
- **Top-level statements and `main`.** A hosted program needs no `main`: the statements of the file being built run from top to bottom, as in C#. Only that file may have them; importing a file with statements is EN0312. A file lists its imports, then its statements and local functions, then its classes and other declarations; a statement after a declaration is EN0115. `args: string[]` is available among the statements, and `os.args()` everywhere. `return 3;` among the statements sets the exit code, with no `return` the program exits with 0, and a failed `?` among them prints the error and exits 1. A function among the statements is a local function (5.5). It may use only top-level variables declared above it, so `` function report(): void { console.log(`count = ${count}`); } let count = 0; `` is EN0313, and class methods cannot see top-level variables at all (EN0313). A local function that uses no top-level variable, counting the local functions it calls, may be called from anywhere; one that uses some may be called only from the statements and other local functions (5.5). With `report();` on line 1 and `let count = 0;` on line 2, the call is EN0618, `` `report()` reads `count` before it is declared ``, with the label `` `count` is declared on line 2 `` and `` help: move this call below `let count = 0;` ``; the check follows calls through other functions. A compile-time `const` stays visible everywhere, including in class methods. A plain top-level `let` is a local, and static storage is a `public` or `private` `unsafe let` (4.9). `enrang test` does not run the statements. A file with no statements has `function main(): void`, `: i32` (exit code) or `: Result<void, E>` as its entry point, where an `Err` prints `error: <e>` to stderr through `Display` and exits 1; any other signature is EN0436. A `function main` beside statements is warning EN0314 and is not the entry point. Freestanding targets allow no top-level statements (EN0809): a kernel keeps `@entry private function kmain(boot: &BootInfo): never` (7.8).
- **`+` on strings** takes `&string` operands and returns a new `string`. `+=` appends in place after its right side runs, copying first if `cap == 0`, and reserves the string meanwhile, so the right side may read it, as `s += "-".repeat(s.length())` does, but a right side that changes it, as in `s += reset(&s)`, is EN0707, with a help to run the right side first, and a part of it still used at the append, as in `s += s.slice(0, 1)`, is EN0708, with a help to append a copy of the part (O6).
- **Integer operators** have section 9 semantics. `i++` and `i--` give the old value and `++i` and `--i` the new one (O6). Assignment and compound assignment are expressions whose value is the target read after the store (`a = b = 0;`), a place that a use which only reads it borrows shared and that a use which would keep it may keep only when it is Copy (EN0621, 3.5), except where a `bool` decides something (EN0105, 3.4).
- **`void e`** evaluates `e`, drops the result and has type `void`. There is no `move x`: a value moves wherever there is no `&`, so `queue.push(move t);` is EN0228, `` `move` is not needed here ``.

An example of both `Result` forms, with a `show` that prints either case:

```ts
import { fs } from "os";

public function parseAge(s: &string): Result<i64> {
  const n = s.parseInt();
  if (n == null) { return Err(`not a number: ${s}`); }
  if (n < 0) { return Err("negative age"); }
  return n;
}

public function loadAge(path: &string): Result<i64> {
  const text = fs.readFile(path)?;
  return parseAge(&text)?;
}

public function show(r: Result<i64>): void {
  match (r) {
    Ok => console.log(`${r.value}`),
    Err => console.log(`caught: ${r.error}`),
  }
}
```

`show(parseAge("42"))`, `show(parseAge("x"))` and `show(parseAge("-1"))` print `42`, `caught: not a number: x` and `caught: negative age`. With an enum `AgeError` whose cases carry the texts `"not a number"` and `"negative age"`, returning `Result<i64, AgeError>` and `Err(AgeError.NotANumber)`, the second prints `caught: not a number`. It prints the same when `parseAge` keeps returning `Result<i64>` and writes `return Err(AgeError.NotANumber);`, because `Err` at a `Result<T>` turns an error of another type into its text, as `?` does.

**Compiler forms.** These cannot be ordinary declarations, and this list is complete. They lower through one HIR callee kind. Everything else, including `Ok`, is an ordinary library member, and a synthesised `clone` is a compiler-generated glue function. `toString` is a form because it takes any value, a borrowing value or a reference included, as `console.log` does, which a member of a generic `T` cannot (4.1).

| Form | Signature | Arguments | Availability |
|---|---|---|---|
| `console.log(a, b, ...)`, `console.error(...)` | Variadic, any values, each printed as 4.4 says: an array as `[1, 2, 3]`, an anonymous object as `{ x: 1, y: 2 }` (4.3), its fields in name byte order on every target, so `{ name: "Ada", age: 36 }` prints `{ age: 36, name: 'Ada' }`, a string inside another value in single quotes while one passed on its own has none, and a class with no `fmt`, of its own or inherited, field by field, `Header { len: 3, flags: 0 }`; `void`. Separated by one space, followed by `\n` | Implicit shared borrows; rvalues become statement temporaries; a packed field is copied first | Hosted and VM; EN0823 on freestanding |
| `` `...${e}...` `` | `string`; each hole any value, printed as by `console.log` | As `console.log` | Allocates through `alloc`, unless passed directly to `console.*`, `writeTo` or `panic`, where pieces go straight to the stream |
| `x.toString()` | `string`; `x` is any value, printed as by `console.log` | As `console.log`; it lowers as the template `` `${x}` `` in an allocating position | Allocates through `alloc`, as such a template does, so with no global allocator it is EN0820 |
| `panic(m)` | `m` is `&string` or a template; `never` | Holes as `console.log` | Everywhere. A template renders into a 256-byte static panic buffer, truncated at a char boundary, so it never allocates |
| `Err(e)` | `Result<T, E>`, from the expected type, or with none, as in an arrow whose return type comes from its body (5.5), `E` from `e`, `Failure` for a text, and a fresh `T`; `e` is a text, fixed, a template or any other `string` or `&string` expression, or an error value | At `E` = `Failure`, a text makes a `Failure`: a fixed text is a static descriptor that needs no allocation, a `string` value moves in with no copy, as in `return Err(msg);`, and a `&string` is copied, which allocates, while a `string` place that no move may leave is EN0603, as `Err(this.name)`, EN0604, as `Err(names[0])`, or EN0605, as `Err(*b)` for a `Box<string>`, as any move out of it is, with `` help: copy the text: `Err(&this.name)` `` and `` help: or move in a copy: `Err(this.name.clone())` ``, and a captured `string` in an arrow is EN0617 with the same helps; a `Failure` moves, and a value of another error type turns into its text, as `?` does, so `Err(AgeError.NotANumber)` in a `Result<i64>` function gives the text `not a number`. At an `E` that is a string-literal union, a fixed text is that union's value (`Err("left")` at `Result<T, Direction>`), and EN0401 when it is not one of them. At any other `E`, `e` is a value of that `E`, which moves, and a text or a value of another error type is EN0401 | Everywhere. A template allocates, so with no global allocator it is EN0820 with `` help: use a fixed text, or return an enum error type whose case holds the value ``, and so are a copied `&string` and a conversion whose text is built at run time (8.3) |
| `assert(c, m?)` | `c: bool`, optional `m` as `panic`; `void` | `c` by value | Everywhere. At top level it is checked at compile time when `c` is constant, and at run time otherwise |
| `unreachable()` | `never` | | Everywhere |
| `dispose(x)`, `mem.forget(x)` | `void`; `x` is any value, a borrowing value or a reference included | `x` by move. `dispose` ends it as its scope end would; `mem.forget` ends it without running its destructor (5.7) | Everywhere |
| `writeTo(f, t)` | `let f: &Formatter`, which it writes; `t` is `&string` or a template; `void` | Holes as `console.log` | Everywhere; never allocates |
| `sizeOf<T>()`, `alignOf<T>()`, `offsetOf<T>("f")` | `usize`, constant | Type only | Everywhere, including `ConstExpr`, except for a borrowing class or tuple there (4.9) |
| `cpu.has("f")` | `bool` | String literal, checked (EN0908) | Everywhere; section 10.3 |
| `asm(...)` | `void` | Section 7.4 | `unsafe` only; EN1201 in the VM |
| `test`, `describe`, `expect`, `compileFails`, `compileOk` | Section 12 | | Test builds |

## 7. Systems programming

### 7.1 Raw pointers

`*T` is the only raw pointer type. It is Copy, carries no loans, and may be stored anywhere; it is nullable with address 0. Reading and writing through it both need `unsafe`. A function that is not `unsafe` and reads or writes through one of its raw-pointer parameters gets warning EN0828, `` help: mark it `unsafe function`, or take a reference ``, because a safe caller could pass it any address; a method whose signature a safe interface member or base method fixes is exempt (5.9). Safe operations: `&x as *T`, `addr as *T` (`addr: usize`), `p as usize`, `p as *U`, `p == q`, `p.isNull()`, `p.add(n)` and `p.sub(n)` (wrapping, scaled by `sizeOf<T>()`), `ptr.null<T>()`. Unsafe operations: `*p`, `&*p`, `p.read()`, `p.write(v)`, `p.readUnaligned()`, `p.writeUnaligned(v)`, `p.readVolatile()`, `p.writeVolatile(v)`, `mem.copy(dst, src, n)`, `mem.copyOverlapping`, `mem.set`. `write` does not drop the old value; `*p = v` does. `mem.copy` and `mem.copyOverlapping` oblige their caller to pointers that are aligned and valid for `n` elements, a destination that may be written, as for a view that is written through (5.9), and, for `copy`, two ranges that do not overlap, which `copyOverlapping` allows; `mem.set` needs a `d` that is valid for `n` bytes and may be written. A call for 0 elements accepts any pointer, null included, since an empty array's `ptr` may be 0 (section 11).

**Views of raw memory.** Memory whose size is known only at run time, such as a UEFI framebuffer, an E820 memory map or a multiboot module, is read and written through a view that `unsafe` code makes with `Slice<T>.fromRaw(p, n)` (8.2), under the obligations of 5.9, as Rust's `slice::from_raw_parts_mut` makes one. `asPtr()` gives the address of an array's or a view's first element back, safely, and only using it needs `unsafe`.

```ts
@repr("C") public final class E820Entry {
  public base: u64;
  public bytes: u64;
  public kind: u32;
  public attributes: u32;
}

public unsafe function usableBytes(table: *E820Entry, count: isize): u64 {
  const entries = Slice<E820Entry>.fromRaw(table, count);
  let total: u64 = 0;
  for (const e of entries) {
    if (e.kind == 1) { total += e.bytes; }
  }
  return total;
}

public unsafe function paint(base: *u32, pixels: isize, color: u32): void {
  const fb = Slice<u32>.fromRaw(base, pixels);
  for (const px of fb) { *px = color; }
}
```

### 7.2 Volatile

Volatile is per access, never a type qualifier. `readVolatile` and `writeVolatile` compile to exactly one load or store of the exact width, in program order relative to other volatile accesses and `asm`; never merged, split or eliminated. `T` must satisfy the sealed bound `VolatileValue`: `u8 u16 u32 i8 i16 i32 usize isize bool` and raw pointers, plus `u64` and `i64` on `x86_64-*`. Anything else is EN0805 at the call, generic or not; `u64` volatile on `i386` is EN0805 because it would tear. Generic code states the bound: `public unsafe function w<T extends VolatileValue>(p: *T, v: T): void`, which is `unsafe` because it writes through `p` (EN0828, section 7.1).

```ts
const VGA = 0xB8000 as *u16;
unsafe { VGA.add(i).writeVolatile(0x0700 | (ch as u16)); }
```

### 7.3 Port I/O

`core/port` provides `unsafe function`s: `inb(p: u16): u8`, `inw`, `inl`, `outb(p: u16, v: u8)`, `outw`, `outl`, and `ioDelay()` (`out 0x80`). They are `asm` wrappers on every x86 target, so they are forbidden in the VM (EN1203). In a hosted process they fault at run time unless the OS allows them.

### 7.4 Inline assembly

```ts
public function cpuFlags(): u32 {
  let value: u32;
  unsafe {
    asm(
      `pushfd
       pop eax`,
      { out: { eax: value } },
    );
  }
  return value;
}
```

- `asm` is an expression of type `void`, legal only in `unsafe` (EN0801). The template is a literal with no interpolation (EN0915), Intel syntax, instructions separated by newlines or `;`, local labels `name:` scoped to one `asm`.
- `in`, `out`: maps from physical register name to a place of a type matching the register's width. `out` places count as initialised for init dataflow. `{ eax }` is shorthand for `{ eax: eax }`, for a place named `eax`.
- `clobbers`: registers destroyed besides `in`/`out`. Flags and memory are always assumed clobbered. `ebp`, `esp`, `rbp` and `rsp` cannot be bound (EN0905) and must be restored by the end of the block. DF must be clear on exit.
- The same assembler and encoder table serve the compiler's own code. Every instruction is checked against the target's level. A form above it is EN0901 naming the instruction, its feature, the level that provides it and the current level. An unknown mnemonic is EN0902 with "did you mean".
- Only forms in the encoder's table are accepted. MMX, 3DNow! and packed SSE forms are EN0916. Scalar SSE1 forms and `ldmxcsr`/`stmxcsr` are tagged `sse` and accepted at level `sse2`, which needs them. `popa`, `popad` at `i386` get warning EN0914 (386 erratum), and the assembler inserts a `nop` after them.

Only `ebp`, `esp`, `rbp` and `rsp` are off limits, so `cpuid` binds `ebx` directly, and `mov cr3` takes its operand in `eax`:

```ts
@requires("cpuid")
public unsafe function vendorRegs(): [u32, u32, u32] {
  let max: u32;
  let ebx: u32;
  let ecx: u32;
  let edx: u32;
  asm(`cpuid`, { in: { eax: 0 }, out: { eax: max, ebx, ecx, edx } });
  return [ebx, edx, ecx];
}

public unsafe function setPageDirectory(dir: usize): void {
  asm(`mov cr3, eax`, { in: { eax: dir } });
}
```

Without `@requires("cpuid")`, the `cpuid` line at `--cpu=i386` is EN0901: `` `cpuid` needs CPU feature `cpuid`, which target level `i386` does not have ``.

### 7.5 Naked and mode-specific code

`@naked unsafe function` has no prologue, epilogue or spills; its body must be a single `asm` statement. `@bits(16)` assembles a naked function's body in 16-bit mode, using the minimal subset the boot stage needs; it is rejected outside `@naked` (EN0913). Calling a `@bits(16)` function from Enrang is EN0913.

A naked body may also use the data directives `db`, `dw`, `dd`, `dq`, `align` and `times <n> db <v>`, where `<n>` is a constant expression over integers, `+`, `-`, parentheses, `$` (current offset) and `$$` (section start). So a raw 512-byte boot sector is user code: `times 510 - ($ - $$) db 0` then `dw 0xAA55`, built with `--format=flat --base=0x7C00`. Symbol operands stay library-only (EN0903).

### 7.6 Layout control

- `@repr("C")` on a class fixes declaration-order natural-alignment layout as a promise (the default layout of a `final` class with no base is the same in this prototype, but only `@repr` is stable across compiler versions).
- `@repr("u8"|"u16"|"u32")` on a payload-free enum sets the tag; values that do not fit are EN0412.
- `@packed` removes padding; alignment becomes 1. Every field of a `@packed` class must have a Copy, non-generic type (EN0826 at the declaration), so no drop glue touches a packed field and alignment is always known when checked. A reference into a packed field that needs more than 1-byte alignment is EN0804, however it arises: `&s.f`, `&s.b[1]`, an auto-borrow, a destructuring binding, a `for...of` element or source, a spread operand. A closure capture borrows the whole variable (5.5), never a field, so an arrow that reads or writes `p.b` does it through the captured `p`, as code outside the arrow does, and makes no reference into the field. The rule is on the place: a MIR `Ref` whose place crosses a field of a `@packed` class with no later `Deref`, and whose referent type has alignment above 1. So `for (const x of &p.b)` over a packed `u32[4]` is EN0804 at the source, and over a packed `u8[4]` it compiles. Use `readUnaligned` through `&s as *u8` offset or copy the field by value, which is allowed. The forms `console.log`, `${}` and `expect` copy such a field to a temporary first, so `console.log(p.b)` works.
- `@align(n)` raises alignment; `n` is a power of two up to 4096. Conflicting attributes are EN0817.
- A class with `@repr("C")`, `@packed` or `@align(n)` must be `final` and extend no class (EN0827: `` a `@packed` class must be `final` ``, with the label `promises an exact layout, but a class that can be extended carries a hidden pointer` and `` help: write `@packed public final class GdtPointer` ``), because a class that can be extended, and every class that extends one, carries a hidden method-table pointer (section 11). A `final` class that extends one gets EN0827 with its own wording, `` a `@packed` class can't extend another class ``, the label `` `Base` gives it a hidden method-table pointer `` and `` help: remove `extends Base` ``. No field of such a class may hold, inline, a class that carries a hidden pointer, which is EN0827 at the field.
- `T[N]` is an inline fixed array of `N` elements, Copy if `T` is Copy, bounds-checked.
- `assert(sizeOf<GdtPointer>() == 6);` at top level is evaluated at compile time.

```ts
@packed public final class GdtPointer {
  public limit: u16;
  public base: u32;
}

@repr("C") public final class Regs {
  public eax: u32;
  public ebx: u32;
}

@align(4096) public final class PageTable {
  public entries: u32[1024];
}
```

### 7.7 Interrupt handlers

```ts
import { outb } from "core/port";

@interrupt private function onTimer(frame: &InterruptFrame): void {
  unsafe { outb(0x20, 0x20); }
}

@interrupt({ errorCode: true })
private function onFault(frame: &InterruptFrame, code: usize): never { panic("page fault"); }
```

Signature is checked (EN0808): one `&InterruptFrame`, an extra `usize` with `errorCode`, and a return of `void` or `never`. The frame is read-only: a handler body that writes it is EN0615. Whether a handler may write its frame is decided with the kernel work of M9 (section 16). The compiler emits the stub: `cld`, individual register pushes and pops (never `pusha`/`popa`), a synthetic frame for stack traces, `fxsave`/`fxrstor` around the body when the float strategy is `sse2`, `fnsave`/`frstor` (108 bytes) when it is `x87`, and `iret`. Handlers cannot be called from Enrang (EN0807) and coerce only to `InterruptHandler`, the type taken by `idt.set(vector, h)` in `os/none`. `idt.set` panics if vectors 8, 10-14 and 17 are not paired with an `errorCode` handler, and vice versa. An `@interrupt` function cannot allocate: reaching an allocation entry point, drop glue that frees, or a `@globalAllocator` method is EN0824, naming the path, and `unsafe` does not lift it. A handler sets a flag or an `Atomic`, and mainline allocates.

### 7.8 Entry point and placement

- **`@entry`** names the program's first Enrang function on freestanding targets; exactly one is required (EN0809), except as stated for flat binaries below. Signature: `function(boot: &BootInfo): never`, and `boot` is read-only: a body that writes it is EN0615. On `x86_64-none --format=efi` it is `function(boot: &BootInfo): never` as well; `BootInfo` is filled from UEFI tables before `ExitBootServices` returns. Freestanding targets have no top-level statements (EN0809): a kernel starts at its `@entry` function. Hosted targets start at the top-level statements, or at `main` in a file that has none; `@entry` there is EN0809.
- **Startup**, always compiled at the floor (section 10.4): zero BSS, load the image's own GDT, set the stack, detect the CPU, check `--cpu`, check for an FPU and the FDIV flaw when built for `x87` (section 9.3), set up the FPU or SSE state if built for it, call `@entry`. Entered by anything other than Enrang's boot stage, `BootInfo` is empty: no memory regions, no serial port, text base `0xB8000`.
- **`@section("name")`** places a function, an `unsafe let` or a `const` in a named output section. Section names beginning `.boot` go first, then `.text`, `.rodata`, `.data`, `.bss`, in that order; others follow in first-use order. Items in `.boot*` are always kept. Unknown section flags cannot be set; hosted targets accept only names starting with `.text.`, `.data.`, `.rodata.`, `.bss.`, and `.bss.stack` is reserved for the compiler's stack on every target (EN0814).
- **`@at(addr)`** gives an `unsafe let` a fixed address with no storage allocated: access is `unsafe`. Overlap within the flat image is EN0813.
- **Flat binary:** `--format=flat --base=<addr>` emits exact bytes at that base with gaps zero-filled. The default base on `i386-none` is `0x10000`, reachable by BIOS load with no extended memory; `0x100000` needs `--base`. If a `.boot*` function exists, it is the raw entry and `@entry` is optional; with no `@entry`, no startup code is emitted.
- **Bootable images** reject a `--base` whose kernel, including BSS and stack, would overlap memory the boot stages use (EN1304).
- **Switching stacks.** A kernel that moves to its own stack declares it with `unsafe { cpu.setStackLimit(addr); }` so the overflow check follows (section 8.4).

```ts
@section(".bss.kstack") private unsafe let kernelStack: u8[16384];
@at(0xB8000) private unsafe let screen: u16[2000];
```

### 7.9 Panic handler and global allocator

```ts
@panicHandler private function onPanic(info: &PanicInfo): never { /* ... */ halt(); }

@globalAllocator private unsafe let heap: FreeListHeap;  // zero-filled: an empty heap
```

- On a freestanding target exactly one `@panicHandler` is required when any panic site is reachable (EN0812); it has signature `function(info: &PanicInfo): never`, and `info` is read-only: a body that writes it is EN0615. A second is EN0811. On hosted targets it is optional and overrides the default printer. A guard flag sends a panic during panic straight to halt or exit.
- On a freestanding target `string` values, `T[]` and `Box` need one `@globalAllocator` (EN0820, section 8.3). A second is EN0821. Its type must satisfy `GlobalAllocator` (EN0822), and its declaration must be `unsafe let` (EN0825), which carries the contract of section 5.9. Hosted targets have a default; registering one replaces it.
- The allocator static is initialised like any other: zero-filled, or a `ConstExpr` with no function call (EN1032). `FreeListHeap` is a `final` class containing only integers and raw pointers, and all-zero bytes mean an empty heap.
- **Allocation-free zones.** Three roots may not reach allocation, on any target: every `@interrupt` function, the `@panicHandler`, and the methods of the `@globalAllocator` itself. Reaching the compiler-called allocation entry points, drop glue that frees, or a `@globalAllocator` method is EN0824, naming the path. A panic can come from inside the allocator, and an interrupt can arrive inside it, so this is what rules out re-entry. There is no run-time lock.
- Regions reach the allocator at run time. `unsafe { heap.addBootRegions(boot); }` adds every usable region of the sanitised `BootInfo` view, and `unsafe { heap.addRegion(addr, bytes); }` adds one by hand. Allocating before that panics with `allocator has no memory`.

### 7.10 FFI

- **Windows.** `@dll("kernel32.dll") public declare function ExitProcess(code: u32): never;`. The compiler writes the import table; only referenced imports are emitted. Calling one needs `unsafe`. Parameters and results are scalars, raw pointers and `fn` pointers (EN0816).
- **Function pointers with an ABI.** `public type EfiPrint = @abi("win64") unsafe fn(self: *Proto, s: *u16) => usize;` is how UEFI protocols and foreign callbacks bind. Calling any `@abi` function pointer is power 2 of section 5.9. `@abi("win64")` on a function makes it callable from foreign code. `cdecl` and `stdcall` are EN1030 and any other unknown name is EN0819.
- **Linux.** There is no dynamic linker or libc; a bodyless `declare function` is EN0815 with a note about inline assembly. Library `@intrinsic` and `@hostCall` declarations are exempt (section 3.1).
- `declare` without `unsafe` at the call is EN0801. FFI never passes `string`, `T[]` or a reference (EN0816, which rejects `&` in `@abi` `fn` types and in `declare` positions) or a class by value (EN1030).

## 8. Standard library layers

The runtime is Enrang source embedded in the compiler binary. Unreferenced functions are stripped from every output. `core` has no allocator and no OS; `alloc` needs a registered allocator; `os` is per-target. Dependencies point only downward.

Signatures in this section show the contract a caller sees: a reference parameter is only read unless it is marked `let`, and a returned reference is as changeable as what it comes from unless its type says `readonly` (5.4). Where a library body contains `unsafe`, its source states the same contract with `const` (section 5.9), so a kernel can pass its read-only `boot` or a string literal to `serial.write`.

### 8.1 Prelude

Implicit in every module. `core`: all primitive types, `Copy Clone Eq Ord Display Error Formatter`, `Result Failure`, `Slice`, the function `Ok` (`Ok(v)`, `Ok()`), the compiler forms of section 6 (among them `Err` and `dispose(x)`), and the namespaces `mem` and `ptr`. `alloc`: `Box`, `T[]` methods, `string` allocating methods, `GlobalAllocator`, `FreeListHeap`. Their signatures are visible on every target; availability is enforced only by EN0820 in phase 5. `os` (hosted only): `console`. `os/none` (freestanding only): `BootInfo PanicInfo InterruptFrame InterruptHandler halt`.

### 8.2 `core`

| Module | API |
|---|---|
| `core/mem` | `unsafe copy<T>(d: *T, s: *T, n: usize)`, `copyOverlapping`, `set(d: *u8, v: u8, n: usize)`, all `@intrinsic`; safe `swap<T>(let a: &T, let b: &T)` and `replace<T>(let x: &T, v: T): T`, which panic when `T` is a class that can be extended and an object is a subclass (4.3), and `forget(x)`, a compiler form like `dispose` (section 6) |
| `core/ptr` | `null<T>()`; pointer methods from section 7.1 |
| `T[N]` | `length(): isize`, indexing, `for...of`, every member of `Slice<T>` below, `slice(a, b?): &Slice<T>`, `splitAt` and `asPtr` included, `clone()` by compiler glue when `T` satisfies `Clone` |
| `Slice<T>` | A view of consecutive elements, only behind `&` (4.3): `&Slice<T>` is a pointer and a length, made by `slice(a, b?)` on `T[]`, `T[N]` and `Slice<T>`, by converting `&T[N]` or a whole `&T[]` (C18), and in `unsafe` code by `Slice<T>.fromRaw(p, n)`. `length(): isize`, `isEmpty()`, indexing, which reads or sets an element of the original, `for...of`, `slice(a: isize, b?: isize): &Slice<T>`, `splitAt(i: isize): [&Slice<T>, &Slice<T>]`, `first(): &T \| null`, `last(): &T \| null`, `get(i): &T \| null`, `find(f: (x: &T) => bool): &T \| null`, `findIndex(f): isize`, `some`, `every`, `forEach(f: (x: &T) => void)`, `reduce<U>(init: U, f: (acc: U, x: &T) => U): U`, `swap(i, j)`, `reverse()`, `sort() where T extends Ord`, `sortBy(f: (a: &T, b: &T) => i32)`, `includes(x: &T) where T extends Eq`, `asPtr(): *T`, and the `static` member `fromRaw`. A returned element reference is writable when the caller writes through it on a changeable array. No member changes the length, so there is no `push`, `pop`, `insert`, `remove` or `clear`. `slice` and `splitAt` never panic, `sort` and `sortBy` are stable, and `fromRaw` is `unsafe` (below) |
| integers | `wrap<U>()`, `toBits`, `wrapping*`, `checked*`, `saturating*`, `overflowing*` for Add, Sub, Mul, Neg, Shl, Shr, the last returning `Overflowing<T>`; `min`, `max`, `abs`, `pow`, `isPowerOfTwo`; `leadingZeros`, `trailingZeros`, `countOnes`, `rotateLeft`, `rotateRight`, `swapBytes`, each lowered to floor instructions unless a higher `--cpu` allows better; `i32.MIN`, `i32.MAX` and likewise |
| `core/float` | `f64`: `sqrt floor ceil trunc round abs min max sign isNaN isFinite isInfinite toBits fromBits`, `sin cos tan atan atan2 exp log log2 pow` (Enrang code, never FSIN), `PI E INFINITY NAN`. `f32`: the same operations from `sqrt` to `fromBits` |
| `core/fmt` | `Formatter`: `write(s: &string)`, `writeByte(b: u8)`; `writeTo(let f: &Formatter, t)` takes a template without allocating; the `static unsafe` factory `Formatter.fromFn(sink: unsafe fn(ctx: *u8, bytes: *u8, n: usize) => void, ctx: *u8)`, whose sink may be an `unsafe function`, or a safe one by C15. Integers print in decimal, `.hex()` wraps for hex. Floats print Dragon4 shortest round-trip, integer-only, identical on every strategy: `1`, `1.5`, `NaN`, `Infinity`, `-0`, `1e+21`, as JS does |
| `core/string` (read-only, no allocation) | `.length(): isize` counts bytes and `.charCount(): isize` counts characters by reading the string (`"città".length()` is 6, `"città".charCount()` is 5); a bare `.length` is EN0441, `` `length` is a method on `string` ``, with `` help: `s.length()` counts bytes (6 here); `s.charCount()` counts characters (5 here) ``, the counts computed for that string (on an array, the help is `` `xs.length()` ``). `.byteAt(i): u8`, `.codePointAt(i): u32` (`i` is a byte index, bounds-checked and required to be a char boundary; decoding never reads past `len`, and a sequence that is invalid because an `unsafe` obligation was broken yields `0xFFFD`), `.slice(a, b?): &string` (a read-only view holding a shared loan on the source, by the index rule of `slice` below over byte indexes, so `"hello".slice(-3)` is `llo`; it copies nothing, needs no heap and never panics, since an index that, once clamped, falls inside a character moves back to that character's start, so `"città".slice(-1)` is `à`; `.toString()` keeps a copy), `.splitAt(i): [&string, &string]` (`[slice(0, i), slice(i)]`, two read-only parts by the same rule), `.startsWith`, `.endsWith`, `.indexOf`, `.includes`, `==`, `.compare`, `.parseInt(): i64 \| null`, `.parseFloat(): f64 \| null`, `.asPtr(): *u8` |
| `core/atomic` | Section 10.5 |
| `core/cpu` | Section 10.3 |
| `core/port` | Section 7.3 |
| `core/option` | `T \| null` methods: `take`, `isNull`, `orElse(d: () => T)`, `clone() where T extends Clone`, declared through `extend<T> T \| null`. `T` ranges over `V`, so on a nullable reference they are EN0703 with a `== null` or `??` fix-it |

**`slice` and `splitAt`.** `slice(a, b?)` on an array, a view or a `string` follows JavaScript's `Array.prototype.slice` and never panics on its range: a left-out `b` is `length()`; a negative index counts from the end, `length() + i`, and stops at 0; an index past the end stops at `length()`; and a start at or after the end gives an empty view, of length 0, whose pointer is the clamped start, never past the end. The arithmetic cannot overflow, so a view always lies inside its source. Over `[10, 20, 30, 40, 50]`, `slice(3, 1)` is `[]`, `slice(-2)` is `[40, 50]`, `slice(1, -1)` is `[20, 30, 40]` and `slice(2, 99)` is `[30, 40, 50]`, as Node prints them, and `"hello".slice(-3)` is `llo`. A `string`'s indexes count bytes, and its `slice` and `splitAt` never panic either: once clamped, each index that falls inside a character moves back to the start of that character, so every part lies on character boundaries. With `à` at bytes 4 and 5 of `"città"`, `"città".slice(-1)` is `à`, as Node prints, `"città".slice(5, 2)` is empty, `"città".slice(0, 5)` is `citt`, and `"città".splitAt(5)` is `['citt', 'à']`, two read-only parts, as every part of a string is (8.3). Node prints `città` for `slice(0, 5)`, because JavaScript counts UTF-16 units, not bytes: a listed difference from JavaScript, as byte indexes already are for text that is not ASCII. Indexing is unchanged: `xs[i]` out of bounds panics. `splitAt(i)` is `[slice(0, i), slice(i)]` by the same rule, so it never panics either, and on an array or a view it gives two writable parts, as Rust's `split_at_mut` does: its body builds them with `SliceFromRaw` in `unsafe` (5.9), so they hold no loans of their own and N6's two-part test keeps the result writable, and destructuring the result gives each part a loan of its own (O7). So `let v: i64[] = [1, 2, 3, 4]; const [lo, hi] = v.splitAt(2); lo[0] = hi[0]; hi[1] = 9; console.log(v);` prints `[3, 2, 3, 9]`, and so does the same over a `let v: i64[4]`, through C18, while over a new `[1, 2, 3, 4]`, `console.log(v.splitAt(-1));` prints `[[1, 2, 3], [4]]`. A `splitAt` written in Enrang returns its two parts read-only, since both come from one parameter (5.1, 5.4).

**Sorting.** `sort` and `sortBy` are stable, as in JavaScript: elements that compare equal keep their order. They sort in place with no heap, since `core` has no allocator, by an in-place stable merge with O(n log^2 n) moves, whose exact algorithm is the library's; there is no unstable sort. For any comparator, one that is not a consistent order included, as `sortBy((a, b) => 1)` is, and for any `Ord` implementation, they stay memory-safe and terminate, and either leave a permutation of the elements, in an order this document does not fix for such a comparator, or panic with `comparator is not a consistent order` (9.1).

**`fromRaw` and `asPtr`.** `@intrinsic public static unsafe fromRaw(p: *T, n: isize): &Slice<T>;` makes a view of the `n` elements at `p`, as Rust's `slice::from_raw_parts_mut` does, for memory whose size is known only at run time (7.1). It is `unsafe` to call, EN0801 outside `unsafe`, and its caller keeps the obligations of 5.9: `n` at least 0, `p` aligned, and non-null when `n` is above 0, `n` live, initialised elements at it within one allocation, `n * sizeOf<T>()` no greater than `isize.MAX`, and, while the view is written through, memory that may be written, never read-only data such as a string literal, a top-level `const` or a constant literal view, nor memory that a `const` root or a by-value parameter not marked `let` owns, and no other access path. So a write through `Slice<i64>.fromRaw(primes.asPtr(), 4)` over `const primes: &Slice<i64> = &[2, 3, 5, 7];` breaks them, which the VM reports as a write to read-only data, as it reports a negative `n` as an invalid value (`DEV_RUNTIME.md` section 2.4). Its contract comes from the compiler table (4.4): the view holds no loans, as rule 3 of 5.4 gives a function with no reference parameter, and carries no read-only mark where it is made (4.11), so there it is as writable as any `&Slice<T>`, and a `const` binding of it may still set elements. A function with no source that returns it hands it out under rule 3, read-only, as it hands out a returned `&*p` (4.11), so writing through that result is EN0616, with `` help: take a `&` parameter that owns the storage ``, such as the `this` of a class that holds the pointer, whose method then returns a writable view that holds the object. `asPtr(): *T` returns the address of the first element and is safe, as Rust's `as_ptr` is; only using the pointer needs `unsafe` (7.1).

### 8.3 `alloc`

```ts
public interface GlobalAllocator {
  let unsafe alloc(size: usize, align: usize): *u8;  // null on failure; contract in section 5.9
  let unsafe dealloc(p: *u8, size: usize, align: usize): void;
}

public final class FreeListHeap implements GlobalAllocator {  // address-ordered first-fit, boundary-tag coalescing
  // Integers and raw pointers only; all-zero bytes are an empty heap.
  // 2 KB code budget, 8-byte header on 32-bit, 16 on 64-bit.
  public unsafe alloc(size: usize, align: usize): *u8;
  public unsafe dealloc(p: *u8, size: usize, align: usize): void;
  public unsafe addRegion(start: usize, bytes: usize): void;
}
```

A failed allocation panics with `out of memory` (programs handling OOM use the allocator directly). Every `alloc` buffer is limited to `cap * size <= isize.MAX` on every target, so `length()` is always representable and 32-bit behaves as 64-bit does; anything larger panics with `capacity overflow`, reachable on `i386`. A `T[]` of a zero-sized `T` uses no memory, so the limit falls on its length: growing it past a length of `isize.MAX` panics the same way.

| Type | API |
|---|---|
| `T[]` | `[]`, `[a, b]`, `[...a]` (4.13); `T[].withCapacity(n)`; `length(): isize`, `capacity(): isize`, `isEmpty()`; `push(x: T)`, `pop(): T \| null`, `insert(i, x)`, `remove(i): T`, `swapRemove(i): T`, `clear()`, `truncate(n)`, `extend(o: T[])`, `extendCloned(o: &Slice<T>) where T extends Clone`, `reserve(n: isize)`; every member of `Slice<T>` (8.2) on the whole array: `slice(a, b?): &Slice<T>`, a view that can be read or set but never grown, which copies nothing and never panics, by the index rule of 8.2; `first(): &T \| null`, `last(): &T \| null`, `get(i): &T \| null` and `find(f): &T \| null`, whose result is writable when the caller writes through it on a `let` array; `forEach`, `findIndex`, `some`, `every`, `reduce`, `swap(i, j)`, `sort`, `sortBy`, `reverse`, `includes`, `splitAt` and `asPtr`. On a `T[]` and on a `&Slice<T>` alike: `map<U>(f: (x: &T) => U): U[]`, `filter(f: (x: &T) => bool): T[] where T extends Clone`, `join(sep: &string): string`, each element printed as 4.4 says. `clone() where T extends Clone` |
| `string` | `""` is empty; `string.withCapacity(n)`; `+`, `+=`; `clone()`; `trim()`, `toUpperCase()`, `toLowerCase()` (ASCII), `split(sep: &string): string[]`, `replace(a, b)`, `repeat(n)`; `pushByte(b: u8)` panics unless `b < 0x80`; `pushCodePoint(c: u32)` panics on a surrogate or above `0x10FFFF`; `unsafe pushByteUnchecked(b: u8)` for raw bytes; `fromUtf8(b: u8[]): string \| null` is the only checked route from bytes; `toString()` on any value, a compiler form (section 6) that prints it as 4.4 says, which also copies a `slice` view into a string of its own |
| `Box<T>` | `new Box(v)`, `unbox()`, auto-deref, `clone() where T extends Clone`, which allocates a new block; when `T` is a class that can be extended, `unbox()` and `clone()` panic unless the box holds exactly a `T` (4.3) |

**Must-use methods.** A library method that leaves its receiver unchanged and returns a new value warns when the result is unused (EN0453): `trim`, `slice`, `toUpperCase`, `toLowerCase`, `replace`, `repeat`, `wrap`, the `checked*` family and the like. User functions opt in with `@mustUse`. Other results drop silently: `queue.pop();` warns about nothing.

**Parts and views.** `slice` copies nothing: its result points into the source, which stays borrowed while the part is used. Changing the source meanwhile is EN0706: `` `line` can't change while `root` points into it ``, with the labels `` `root` points into `line` from here ``, `` `line` changes here `` and `` `root` is still used here ``, and `help: keep a copy: const root = line.slice(5, 14).toString();`. For an array it is `` `list` can't change while `head` points into it ``, with the labels `` `head` points into `list` from here ``, `` `list` grows here `` for a change that grows it or `` `list` changes here `` for any other, and `` `head` is still used here ``, and `help: keep a copy: const head = [...list.slice(0, 2)];`. Returning a part of a local is EN0710, with the same help to keep a copy. A part of a string is read-only, and writing through one is EN0616, `` a part of a string can't grow; copy it with `.toString()` ``; so is writing through a returned `&string` that may be a part (5.4). A part of an array is a `&Slice<T>`, which can be read and set: with `function fill(part: &Slice<u8>, v: u8): void { for (let i = 0; i < part.length(); i++) { part[i] = v; } }`, `let sector: u8[8] = [0; 8]; fill(sector.slice(4, 8), 7);` writes into `sector`, and a `checksum(data: &Slice<u8>): u32` that adds the bytes then gives `28` for `checksum(&sector)`. It never grows: passing a part to a function that pushes, which takes a `&T[]`, is EN0401, `a part of an array can't grow`, with the label `` `addOne` takes `xs: &i64[]`, a whole array it may grow ``, and `help: pass the whole array: addOne(&list)` when the part is a `slice` call on a whole array, as `addOne(list.slice(0, 2))` is; for any other part, as a `part: &Slice<i64>` parameter passed on, the help names both parameter types, `` help: `addOne` takes `xs: &i64[]`, so take `part: &i64[]` in place of `&Slice<i64>` ``. Two writable parts of one array at once are EN0707, as at the second `slice` in `const a = v.slice(0, 2); const b = v.slice(2, 4); a[0] = b[0]; b[1] = 9;`, where both parts are written; `v.splitAt(2)` gives them (8.2).

**Allocator error.** On a freestanding target with no `@globalAllocator`, it is EN0820 when reachable code (a) has a local, field, parameter or return of owned type `string`, `T[]` or `Box<T>`, (b) names a template literal in an allocating position, or (c) calls any `alloc` function. The diagnostic names the first use in call-graph order and offers both a registration snippet and the non-allocating alternative. `&string` is `core` and stays legal; a literal in `&string` position has no owner. A fixed text in `Err("...")` is a static descriptor (`cap == 0`) and is exempt from (a); a template in `Err` is EN0820 with `help: use a fixed text, or return an enum error type whose case holds the value`, and so is a `&string` held in a variable, as in `Err(name)`, which `Err` copies into the `Failure` (section 6). Turning an error into a `Failure`, by `?` into a `Result<T>` or by `Err(x)` at one (section 6), needs no memory when its text is fixed: a case with no fields, of an enum that does not write `fmt`, gives its text, or its qualified name, as a static descriptor, so `return Err(DiskError.Timeout);` in a `Result<u8>` function compiles, and so does `?` into `Result<u8>` on a `Result<u8, BusError>` none of whose cases has fields. A text built at run time needs memory, so on an error type with a case that has fields, on an enum that writes `fmt`, or on an `implements Error` class, the `?` is EN0820, `` turning `DiskError.BadSector` into a text needs memory, and this kernel has no heap ``, with the label `` `BadSector` has fields, so its text is built at run time `` and `` help: return `Result<u8, DiskError>` to pass the error on as it is ``, the label reading `` `AgeError` writes `fmt`, so its text is built at run time `` for an enum that writes `fmt`; `Err(x)` is EN0820 the same way when `x` is such a case written in place, as in `Err(DiskError.BadSector { lba })`, or a value of such a type. The type decides, not the case a run meets, so `readSector(lba)?` is EN0820 even if it only ever fails with `DiskError.Timeout`, while `return readSector(lba)?;` in a function returning `Result<u8, DiskError>` passes the error on with its fields and compiles. In a generic body the type is the one each instance gives `E`, so `return r?;` in `function lift<T, E>(r: Result<T, E>): Result<T>` is EN0820 for `lift(readSector(7))` and compiles for an `E` none of whose cases has fields and that writes no `fmt`, reported at mono with the reach chain (4.10). So with no `@globalAllocator` every `Failure` has `cap == 0`, dropping one frees nothing, and its drop glue is trivial and not (c).

### 8.4 `os`

Selected by TargetSpec: `os/linux_x64`, `os/linux_i386`, `os/windows`, `os/vm`, `os/none`, `os/uefi`. Programs import from `os`.

Hosted API: `console.log`, `console.error`; `os.args(): string[]` (top-level statements also see it as `args`), `os.env(name: &string): string | null`, `os.exit(code: i32): never`, `os.now(): i64` (milliseconds), `os.sleep(ms: i64): void`; `fs.readFile(p: &string): Result<string, IoError>`, `fs.writeFile(p, s): Result<void, IoError>`; `stdin.readLine(): string | null`. `IoError` is an enum, and so an error type: `NotFound`, `PermissionDenied`, `Other { code: i32 }`.

- Linux `i386` uses only syscalls old kernels provide: `exit` 1, `read` 3, `write` 4, `open` 5, `close` 6, `lseek` 19, `brk` 45, `gettimeofday` 78, old `mmap` 90, `nanosleep` 162. `exit_group` and `mmap2` are never used. Linux `x86_64` uses raw `syscall`.
- Windows imports only referenced `kernel32.dll` functions.
- In the VM these reach capability-checked `HostCall`s; denial returns `Err(IoError.PermissionDenied)`.

Freestanding API, `os/none`:

| Item | API |
|---|---|
| `BootInfo` | `regionCount(): usize`, `region(i: usize): MemRegion` (a Copy class with public fields `start: u64`, `bytes: u64`, `usable: bool`), a sorted, non-overlapping view that excludes everything the boot path still uses and clips usable regions to what the target can address; `bootDrive(): u8`, `com1Port(): u16`, `crtcPort(): u16`, `textBase(): usize`, `columns(): u32`, `rows(): u32`, `framebuffer(): Framebuffer \| null` |
| `FreeListHeap` | `unsafe addBootRegions(boot: &BootInfo): void`, an `extend` member in `os/none` that adds every usable region, so kernels never write those casts |
| `vga.Screen` | `static fromBoot(b: &BootInfo): Screen`; `write(s: &string)`, `writeByte(b: u8)`, `clear()`, `setColor(fg: u8, bg: u8)`, which change the screen; mono and colour adapters both work via `crtcPort()`, and under UEFI it renders to the framebuffer. `vga.emergency(s: &string)` writes directly with no state, using the `BootInfo` that start recorded; before that it assumes `0xB8000` |
| `serial` | `serial.init(b: &BootInfo)`, `serial.write(b: &BootInfo, s: &string)`, `serial.writeByte(b: &BootInfo, v: u8)`; 9600 8N1, bounded polling, a missing port never hangs; `serial.kind(): UartKind` is `None, Uart8250, Uart16550`, and reports `None` before start has recorded `BootInfo` |
| `idt` | `idt.init()`, `idt.set(vector: u8, h: InterruptHandler)`, `idt.enable()`, `idt.disable()`; PIC remapped to `0x20`/`0x28` with I/O delays; `idt.enable()` also re-enables NMI, which the boot stage masked |
| `pic`, `pit` | `pic.mask(irq)`, `pic.unmask(irq)`, `pic.eoi(irq)`; `pit.setHz(hz: u32)` |
| CPU | `halt(): never`; in namespace `cpu` of `os/none`: `cpu.withoutInterrupts(f: () => void)` (`pushfd; cli; ...; popfd`, uniprocessor only), `unsafe cpu.setStackLimit(addr: usize)`, `unsafe cpu.enableSse()`. A file needing both `cpu` namespaces writes `import { cpu as hw } from "os"` |

`os/uefi` adds `@abi("win64")` protocol types, `SystemTable`, and `exitBootServices` with map-key retry. It captures the firmware framebuffer before exit. Secure Boot must be off, because the output is unsigned.

### 8.5 Dev-only surface

- `@was("old")` on a type, field, variant or function carries identity across a rename during `enrang dev`; inert elsewhere.
- `@devMigrate private function migrateX(old: { ... }): X` is a migration hook; the object type states the old schema and is checked against it. Stale hooks warn and are ignored. Production builds strip it, and a hook is not callable from code (EN1211). A hook takes only `old` and returns only the new value; if its reachable code contains user `unsafe`, an `unsafe let` or a host call, it is EN1217.
- `HostCall` is a MIR statement legal only in `os/vm`, not user-visible. Library code reaches it through `@hostCall` declarations (section 3.1).
- `@owner` shapes declare ownership edges in `alloc`; user code cannot use them in the prototype (EN0806).

The sandbox, hot-reload and migration semantics are in the architecture document. Programs can observe only: capability failures as `Err(IoError.PermissionDenied)`, a virtual clock without `--allow-clock`, addresses, which are the VM's (a raw pointer, an `fn` value or a closure printed as 4.4 says, `p as usize`, and any value computed from one), so output that depends on an address value, printed or used in arithmetic or a branch, is outside the rule that stdout matches a native run, and the same stdout otherwise. Converting an integer to a raw pointer never faults in the VM, since 4.6 makes it safe to create: a pointer with no provenance, such as `0xB8000 as *u16`, prints as its address, `0xb8000`, and EN1204 fires at the first access through it.

## 9. Runtime semantics

### 9.1 Panics

A panic never unwinds and never runs destructors. Hosted default: writes the message to stderr and exits with status 101. VM in `dev`: pauses instead. Freestanding: calls `@panicHandler`.

Hosted format, exact:

```text
panic: index 2 is out of bounds for length 2
  --> server.en:18:3
stack:
  step (server.en:18:3)
  main (server.en:33:5)
```

The stack comes from the frame-pointer chain plus the `.enr.trace` table; `--trace=none` omits the stack and location, `--trace=fn` omits column and line for inner frames. `PanicInfo` exposes `message(): &string`, `file(): &string`, `line(): u32`, `column(): u32`.

| Message | Cause |
|---|---|
| `index I is out of bounds for length L` | Index or fixed-array access; a negative index of any signed type included |
| `integer overflow: A OP B` | `+ - *`, negation of MIN, `abs(MIN)` (OP includes `neg`) |
| `division by zero` | `/ %` on integers |
| `integer overflow: MIN / -1` | Division or remainder of MIN by -1 |
| `shift count N out of range for BITS bits` | `<< >>` count negative or not below the width |
| `conversion out of range: V as T` | `as`, int to int or float to int (`NaN` prints) |
| `unexpected null` | `x!` |
| `` OP expected an `A`, but the box holds a `D` ``, `` OP expected an `A`, but the reference points at a `D` `` | Moving, copying or writing a whole `A`, a class that can be extended, whose object is a subclass `D` (4.3), through a `Box<A>`, an `&A` or `this`. `OP` names the operation: `` `unbox` `` for `unbox()`, `` `clone` `` for `clone()`, `` `mem.replace` ``, `` `mem.swap` ``, `assignment` for a whole write `*a = v`, `copy` for a copy out (by C05 or C08, or an explicit `*a`), and the method's name, as `` `into` ``, for the entry to a `move` method of `A` in generic code or a per-class copy (4.4), which takes the whole object as `this` (elsewhere a call that would fail it is EN0458). So `pet.unbox()` panics `` `unbox` expected an `Animal`, but the box holds a `Dog` ``, and with `a: &Animal` pointing at a `Dog`, `*a = new Animal("x")` panics `` assignment expected an `Animal`, but the reference points at a `Dog` `` and `mem.swap(a, &other)` `` `mem.swap` expected an `Animal`, but the reference points at a `Dog` `` |
| `byte index I is not a char boundary` | `string.codePointAt` at an index inside a character (8.2); `string.slice` and `splitAt` never panic, since they move such an index back to its character's start |
| `` `C.m` is abstract, and the subclass that implements it is already cleaned up `` | A call through a method table that reaches the slot of an abstract method `m` of an abstract class `C`, which happens only in `C`'s destructor or code it calls, once the object's own class's part is cleaned up and its hidden pointer names `C`'s table (5.7, section 11) |
| `comparator is not a consistent order` | `sort` or `sortBy`, when the library finds that the comparator or the `Ord` implementation contradicts itself; it may instead finish with a permutation of the elements (8.2) |
| `invalid byte B for a string` | `string.pushByte` with `B` from `0x80` up |
| `invalid code point C` | `string.pushCodePoint` |
| `capacity overflow`, `out of memory`, `allocator has no memory` | `alloc` |
| `stack overflow` | Prologue limit check on freestanding, guard page on hosted (hosted prints what the OS delivers) |
| `unreachable code reached`, `assertion failed: MSG` | `unreachable`, `assert` |
| user string | `panic` |

`x!` reports the column of the `!`. A custom message uses `??` with `panic`, whose type is `never`: `os.env("PORT") ?? panic("set PORT before starting the server")`.

### 9.2 Integers

Checks are always on, in every build, with no flag to disable them. Arithmetic is two's complement. `+`, `-`, `*`, unary `-` and `abs` panic on overflow. Results of `wrapping*` are mathematically modulo 2^N. `>>` is arithmetic on signed and logical on unsigned types. `i64` and `u64` on `i386` behave identically to `x86_64`. `/` truncates toward zero; `%` has the sign of the dividend. Truncation is never implicit: an int-to-int `as` that does not fit panics (`conversion out of range: 1059392 as u16`), and keeping the low bits is written `x.wrap<u16>()` or with a mask (section 4.6).

### 9.3 Floating point

**Strategies.** `soft` (Enrang's `core`, integer-only; the default at `i386` and `i486`, because a 386 without a 387 and a 486SX have no FPU and a level is never a requirement), `x87` (the FPU; the default at `i586` and `i686`, and `--float=x87` opts in at `i386`, `i486` and `sse2`; on native `x86_64-*` it is EN0911, as `--float=soft` is), `sse2` (the default at level `sse2`, and the default and only strategy on native `x86_64-*`, where `--float=soft` is EN0911 because every x86-64 CPU has SSE2; `--float=sse2` on `i386` needs `--cpu=sse2` or higher). On VM rows `--float=x87` is EN0911, as `--float=sse2` is.

**Guarantee across all implemented strategies and the VM, bit for bit:**

- `+ - * / %`, `sqrt`, and conversions round to nearest, ties to even, with no flush-to-zero and no denormals-are-zero. `%` is exact, computed like `fmod`, and truncates.
- Non-NaN results are bit-identical, including signed zeros, subnormals and infinities.
- NaN-ness is identical. A NaN's sign and payload are not specified; `toBits()` canonicalises every NaN to `0x7FF8000000000000` (`0x7FC00000` for `f32`), making them unobservable in safe code.
- Rounding mode and exception flags are not exposed. Traps are masked.
- Float moves use integer moves, so an sNaN value keeps its bits until an arithmetic operation.
- Comparison is IEEE: `NaN != NaN`; `-0 == +0`. `sin`, `exp` and the like are `core` Enrang code on top of these operations, therefore also identical.
- `f32` arithmetic is true binary32, never computed in higher precision observably.

Cost: on a 386 soft-float `f64` add is estimated at 1,500-3,000 clocks. Soft float is immune to the Pentium FDIV flaw by construction; `x87` detects the flaw at startup (below).

**x87 meets the same guarantee and passes the same bit vectors:** FNINIT, FLDCW `0x027F` (53-bit precision, round to nearest-even, all exceptions masked); memory-to-memory operations only, with a store after every operation, so no excess precision survives a statement; f64 add, sub, sqrt run directly; f64 mul, div use the strictfp scale pair (`2^-15360`, `2^15360`) to prevent double rounding in the subnormal range; f32 runs at PC=53 where double rounding is innocuous (53 >= 2·24+2); copies use integer moves, never FLD/FSTP. So this prints `Infinity` on `soft`, `sse2` and `x87` alike:

```ts
let a: f64 = 1e308;
let b: f64 = 10;
console.log(a * b / b);
```

Startup in an `x87` build checks that an FPU is present and otherwise stops with a clear message, as the level check does (section 10.2); freestanding startup clears CR0.EM. It also detects the Pentium FDIV flaw by computing `4195835 / 3145727` (correct: `1.333820449136241`; a flawed Pentium gives `1.333739068902037`). On a flawed Pentium `/` and `%` use the software routine, so an `x87` build that divides links it. `@interrupt` stubs save the FPU state with `fnsave`/`frstor` (section 7.7). User `asm` gets only the x87 forms for probing and OS context switching (`fninit`, `fnstsw`, `fnstcw`, `fnsave`, `frstor`, `fwait`), tagged `fpu`; the arithmetic forms are for the compiler's own code.

## 10. CPU levels

### 10.1 The option

`--cpu=<level>` on `enrang build`, `run`, `test`. **A level is an optimisation, never a requirement.** Floor output (`i386`) runs on every listed chip, because x86 is backward compatible. Bitsets back the table; levels are named rungs over them. Default: `i386` on `i386-*`, `x86-64` on `x86_64-*`. The default float strategy follows the level (section 9.3): `soft` at `i386` and `i486`, `x87` at `i586` and `i686`, `sse2` at `sse2` and `x86-64`.

| Level | Code may assume | Covers | Startup check |
|---|---|---|---|
| `i386` | 80386 integer only; no FPU, SSE, CPUID, CR4, CMOV, BSWAP, CMPXCHG, XADD, RDTSC, multi-byte NOP | Everything listed | Boot stage rejects 8086/286 |
| `i486` | + BSWAP, CMPXCHG, XADD, INVLPG | 486, Am486, Am5x86 and up | AC toggle |
| `i586` | + CPUID, CMPXCHG8B, RDTSC, MSRs, CR4 | Pentium, K5, K6, K6-2, K6-III and up | ID toggle, TSC, CX8 bits |
| `i686` | + CMOV, FCOMI family | P6, K7, NetBurst and up; not K5 or K6 | CMOV bit |
| `sse2` | + SSE2 scalar, FXSAVE, `--float=sse2` allowed | NetBurst, Pentium M, Core, Atom, K8 and up; not PIII or K7 | SSE2, FXSR bits; freestanding sets CR4.OSFXSR |
| `x86-64` | SSE2, CMOV, NOPL in long mode. **Not** CMPXCHG16B, long-mode LAHF/SAHF, POPCNT, SSE3+ | All 64-bit | Long-mode bit when freestanding |

Aliases print a note naming the resolved level: `386`, `am386` to `i386`; `486`, `am486`, `am5x86` to `i486`; `pentium`, `k5`, `k6`, `k6-2`, `k6-3` to `i586`; `pentiumpro`, `p2`, `p3`, `k7`, `athlon-xp` to `i686`; `p4`, `pentium-m`, `core-duo`, `atom`, `core2`, `q8400` to `sse2` on 32-bit targets. On 64-bit targets `core2` and `q8400` resolve to `x86-64`; `p4` and `atom` also resolve to it, with a note saying this covers only their 64-bit models; `pentium-m` and `core-duo` are EN0912, because those chips have no long mode. `native` is rejected (EN0909): the host is never the target. An `i386`-family level on an `x86_64-*` target is EN0912. So is `x86-64` on an `i386-*` target, because that level assumes long mode. VM rows have no CPU level, so any `--cpu` on one is EN0912 too.

### 10.2 Failing cleanly

Output built above the floor checks at startup, in floor code: `needs i686 (CMOV); this CPU lacks it`. Linux exits 126. Freestanding writes to VGA and COM1, then halts. Windows calls `ExitProcess(126)`.

### 10.3 Run-time detection

```ts
import { cpu } from "core";

@requires("cmov")
public unsafe function fastMax(a: i32, b: i32): i32 {
  let r: i32 = a;
  asm(
    `cmp eax, ebx
     cmovl eax, ebx`,
    { in: { eax: a, ebx: b }, out: { eax: r } },
  );
  return r;
}

public function max(a: i32, b: i32): i32 {
  if (cpu.has("cmov")) {
    unsafe { return fastMax(a, b); }
  }
  return a > b ? a : b;
}
```

- `cpu.has(feature: &string): bool`, with `feature` a literal checked at compile time (EN0908): `fpu cpuid bswap cmpxchg xadd cmpxchg8b rdtsc msr cr4 cmov fcomi mmx 3dnow sse sse2 sse3 ssse3 sse4.1 sse4.2 popcnt fxsave nopl pae nx lm invlpg`. Cached after first use. CPUID has no bit for some of these; `ARCHITECTURE.md` section 8.3 defines them.
- **On freestanding targets, `cpu.has` means usable now.** For `fpu`, `sse*` and `fxsave` it is the CPUID bit, and CR0.EM clear, and for SSE also CR4.OSFXSR set. A guarded `@requires("sse2")` function therefore never takes `#UD`. At `--cpu=sse2` and above, startup always leaves EM clear and OSFXSR set, so the call folds to `true`. Below that level, `unsafe cpu.enableSse()` turns SSE on and refreshes the cache. At `--cpu=i586` and above, where every listed chip has an FPU, startup leaves EM clear whatever the float strategy, so `cpu.has("fpu")` folds to `true`, as it does on hosted targets at those levels.
- `cpu.vendor(): &string`, `cpu.levelOf(): &string` give `"i386"`, `"i486"` and so on as detected.
- Detection: EFLAGS.AC toggle for 486+, EFLAGS.ID toggle for CPUID. FPU presence is FNINIT/FNSTSW on freestanding only, after clearing CR0.EM and CR0.TS, and on CPUs without CPUID it also requires CR0.ET, so a 287 counts as no FPU; below `i586`, `cpu.has("fpu")` on hosted `i386-linux` is true only if CPUID says so. CR4 is touched only when CPUID reports a CR4 feature. On `x86_64-*`, anything beyond the baseline uses CPUID.
- `@requires("f", ...)` adds features to the allowed set for that function's body, including `asm`; calling it needs `unsafe` (EN0907). A higher `--cpu` makes the attribute satisfied statically, so the call is still `unsafe` but `cpu.has` folds to `true`.

### 10.4 The floor island

Startup, the level check and panic printing are always compiled at `i386`, whatever `--cpu` says, and every function outside them sits at the target level. A startup path never has a form above the floor, except the FPU probe forms and, in an `x87` build, the FDIV check, which runs only after the probe has found an FPU.

### 10.5 Atomics

Threads are deferred, so atomics exist for interrupt-versus-mainline sharing. The class is `Atomic<T extends AtomicValue>`. `AtomicValue` is a sealed `core` interface implemented by `u8 u16 u32 usize i32 bool` and nothing else, so `Atomic<string>` is EN0419, generically too: no atomic load can duplicate an owner, and nothing tears.

| Method | Available | Lowers to |
|---|---|---|
| `load()`, `store(v)`, `exchange(v)` | every level | `mov`, `mov`, `xchg` |
| `add(v)`, `sub(v)`, `and(v)`, `or(v)`, `xor(v)` (no result) | every level | `lock` ALU |
| `incAndTestZero()`, `decAndTestZero()` | every level | `lock inc/dec`, ZF |
| `testAndSet(bit)`, `testAndClear(bit)` | every level, `where T extends AtomicBits`: `u16 u32 usize i32`. On `u8` and `bool`, EN0419 with a help to use `exchange`, because `bts` has no byte form | `lock bts/btr`, CF |
| `fence()` | every level | `lock or [esp], 0` |
| `compareExchange(old, new)`, `fetchAdd(v)` | `i486`+, else EN0910 | `lock cmpxchg`, `lock xadd` |

**`Atomic64`** is a separate class holding a `u64`, with `load`, `store`, `exchange`, `compareExchange` and `fetchAdd`. Naming it below `i586` is EN0910 in phase 4. It lowers to `lock cmpxchg8b` on `i386-*` and ordinary 64-bit forms on `x86_64-*`. It has alignment 8 on every target, so `cmpxchg8b` never splits a cache line.

Both classes write their own `fmt`, which prints the value `load()` returns, so printing one (4.4) is an atomic read and never tears.

There is no silent CAS emulation. SMP below `i486` is unsupported. Freestanding uniprocessor code may use `cpu.withoutInterrupts` instead.

### 10.6 What "supported" means

The docs and `enrang targets --evidence` report four classes per CPU family, generated from test results: **C1** level-proven (encoder tags, assembler oracle, disassembly audit); **C2** run at that level on the development host, which proves the code rather than the chip; **C3** emulated, naming the model; **C4** real hardware. C4 exists only for the owner's Q8400, from the owner's report, and for the `Newer` row, where the i5-12400F development machine runs hosted output in user mode. Every other family reads `no hardware`, because the owner has no other old machines. No class is claimed before it is reached.

Compiled floor code avoids 386 errata by construction: no `popa`/`popad`, `enter`, `ud2`, or `loop`; panic stops with `int3` then a halt loop. Early 386s with the 32-bit multiply bug ("16 BIT S/W ONLY") and hardware-defective K6 steppings are unsupported.

**Size budgets** (enforced by tests from their milestone): stage 1 is 512 B including 350 B code, stage 2 at most 4 KB, hello kernel flat at most 16 KB running in 640 KB with no extended memory, hello ELF at most 12 KB on either Linux target, allocator at most 2 KB, soft-float at most 16 KB if referenced (including the software division and remainder an `x87` build links for flawed Pentiums), full `core`+`alloc`+`os` without floats at most 32 KB, an allocator-using kernel fits a 2 MB machine.

## 11. Runtime data layout

Fixed by target pointer width `P` (4 on `i386-*`, 8 on `x86_64-*`). Stated offsets are normative and conformance-tested via `sizeOf`, `alignOf`, `offsetOf`.

| Type | Size | Align |
|---|---|---|
| `bool`, `i8`, `u8` | 1 | 1 |
| `i16`, `u16` | 2 | 2 |
| `i32`, `u32`, `f32` | 4 | 4 |
| `i64`, `u64`, `f64` | 8 | 4 when `P == 4`, 8 when `P == 8` |
| `isize`, `usize`, `&T`, `*T`, `fn(...)`, `Box<T>` | `P` | `P` |
| closure parameter | `2P` (code, env), stack only | `P` |
| `Atomic64` | 8 | 8 |
| `void`, `never` | 0 | 1 |

Four forms of the `&T` and `Box<T>` row are `2P` instead, each described below: a `&string` that only reads, a `&Slice<T>`, `Box<I>` for an interface `I`, and an `&I` taken from one. The last covers every `&I` but an `&I` parameter, not nullable, of a per-class copy.

**Size limits.** No type or static may exceed `isize.MAX` bytes of the target, no stack frame may exceed `2^31 - 1` bytes, and an image on a RIP-relative target may not span more than `2^31 - 1` bytes. A `T[N]` may not have `N` above `isize.MAX`, whatever the size of `T`, so `length()` always fits. Violations are EN0435: `u8[3000000000]` on `i386`, `u64[536870912]` whose size would wrap to 0, a 3 GB local on `x86_64`. Sizes never wrap. EN0435 fires at layout, at mono for sizes that depend on an instantiation (`public class A<T> { public a: T[65536]; public b: T[65536]; }` with `A<A<u64>>`), and at link for a relocation that does not fit.

**`string`**: `{ ptr: *u8 @0, len: usize @P, cap: usize @2P }`, size `3P`, align `P`. `cap == 0` means `ptr` is static or dangling and drop does nothing. Bytes are UTF-8, no terminator. A string literal is such a descriptor in read-only data, with `cap == 0`. A `&string` that only reads is a pointer and a length, size `2P`, so it can point at part of a string, as a `slice` view does; a literal used as a `&string` is passed this way. A `&string` that may push is one pointer to the whole descriptor, because only a whole string can grow. The inferred permission of a reference decides which form it has. A returned `&string` takes its form from the result's writability (5.4): one pointer to the whole descriptor when the result is writable, and a pointer and a length when it is read-only, `readonly` results from whole places included. So a `&string` that a function returns from a `&string` parameter it only reads is a pointer and a length, and can't grow, and an interface member or `fn` type fixes the form of its result by its marks. A function reached through an `fn` row, a closure parameter, a base method or an interface member that allows more than it does, as a reader of a `&string` stored at `fn(let s: &string) => void` is, is called through an adapter with the row's forms, which reads the pointer and length from the whole descriptor, so it still gets the string the caller passed (4.5); where the function's `&string` result is writable and the row's is read-only, the adapter reads them from the descriptor the function returns. The same goes for a `&string | null`, and for each `&string` part of a returned tuple, which the adapter rebuilds. A method table gives a method one slot per set of `&string` forms: a slot has the forms of the declaration that introduces it, and an override whose forms differ, as a `Dog.label` whose result is writable where `Animal.label`'s is read-only, introduces a slot of its own in its class's table, while the inherited slot points at the adapter. A call through a `&C` or a `Box<C>` uses the slot of the nearest declaration of the method at or above `C`, so on one `Dog`, `d.label()` through a `d: &Dog` gets one pointer and `a.label()` through an `a: &Animal` gets a pointer and a length. A per-class copy or generic instance that calls an interface or bound member through a class's table converts between the member's forms and the slot's at the call. An adapter calls one known function, so into an `fn` type it exists only for a function name or a non-capturing arrow, and converting any other `fn` value to a row with other `&string` forms is EN0615 (4.5); into a closure parameter type it is a closure on the stack whose environment is the original value. In a generic instance at `T := string`, a Read `&T` or `&T | null` parameter, or a Read `&T` part of a by-value tuple parameter, that is in the sources of a writable result, and not stored, is one pointer to the whole descriptor, because the generic body's result is writable for every `T` (4.10), and so is such a parameter of an `fn` or closure type written with type parameters, by its row's declared sources, because that row is computed before substitution. An argument or tuple part that is a pointer and a length at such a call, through an `fn` or closure value included, is always passed through a statement temporary descriptor `{ ptr, len, cap: 0 }`, a `null` staying `null`, and the call's result is turned back into a pointer and a length at once. Nothing writes through that temporary: such an argument is either marked, and then so is the result, or not written through after the call, since a write through the result would have made the caller's own reference write-live, and so whole (N3 (d)). Arrays need no adapter, because `&T[]` is always one pointer and `&Slice<T>` always two words.

**`T[]`**: `{ ptr: *T @0, len: usize @P, cap: usize @2P }`, size `3P`. `len`, `cap` count elements. An empty array holds no allocation, so its `ptr` may be 0, and so may that of a view of it, which is never read through, since it has no elements (5.9). Zero-sized `T` never allocates and has `cap` equal to the maximum `usize`, with `len` still limited to `isize.MAX` (8.3). An array of zero-sized `T` that has elements has `ptr` equal to `alignOf<T>()`, never 0, which whatever gives it its first element sets, as its first `push` does, so a reference to one of its elements is never 0 (`&I | null`, below); an empty one may keep 0, since nothing references its elements. A `&T[]` is always one pointer to the whole array, which it may grow.

**`&Slice<T>`**: a pointer to the first element and a length in elements, size `2P`, align `P`, so a fixed array (`&u8[8]`), a growable array and a part made by `slice` all fit it (C18). It never owns or frees anything. A bracket literal of constants made static (5.4) is a `T[N]` in read-only data, laid out as any `T[N]`, and its view points there; a view made by `Slice<T>.fromRaw` points where its caller says (8.2).

**`T[N]`**: `N` consecutive elements with no header, size `N * sizeOf<T>()`, align of `T`. References and iteration carry the static length.

**`Box<T>`**: one pointer to the heap block that holds the `T`. Freeing a `Box<A>` of a class that can be extended passes `dealloc` the size and alignment recorded in the object's method table, not those of `A`, because the box may hold a subclass (C21). `Box<I>` for an interface `I` is `2P`, align `P`: the pointer, and beside it a pointer to the object's class's table for `I`, as Rust's `Box<dyn I>` carries it: `I`'s members in `I`'s order, then the class's size, alignment, name, drop glue and two printers: its `fmt`, written or synthesised, and the one used inside another value, which quotes a string, a `&string`, a string-literal-union value, a `Failure` and a text case of an enum with no written `fmt`, and is otherwise the same (4.4). A `final` class therefore needs no hidden pointer to be used through an interface: converting a `Box<C>` of one to a `Box<I>` (C22) stores `C`'s table for `I`, known statically. A `Box<C>` of a class `C` that can be extended may hold a subclass (C21), so its conversion reads the table through the object's hidden pointer: for each interface `I` that a `C` is converted to, `C`'s method table holds a pointer to `C`'s table for `I`, at an index that every subclass's table keeps and fills with a pointer to its own. So a `Box<Animal>` holding a `Dog`, converted to a `Box<Speaker>`, runs `Dog`'s `speak` and frees the `Dog`'s size, and an argument whose class is known reaches the extra copy of a function with an interface parameter with its table found the same way (4.4). An `&I` taken from a `Box<I>` is the same two words, size `2P`, align `P`, the object's address and then the table pointer, as Rust's `&dyn I` is, and so is every other `&I` but an `&I` parameter, not nullable, of a per-class copy: one that a per-class copy returns, stores in a field, puts in a tuple or wraps in a nullable, or that C22 makes anywhere but at such a parameter, attaches its class's table for `I`, read through the object's hidden pointer when the class can be extended (4.4). As a parameter of the copy for its class, an `&I` whose class is known is one pointer, and a two-word `&I` passed to an `&I` parameter reaches the extra copy of the function (4.4), as every `&I` argument does at a call whose callee is chosen at run time, through a method table, an interface's table, an `fn` value or a closure, which passes it as two words. A method compiled once per type has no slot in either table, so no call to it is chosen at run time (4.4). The object word of an `&I` is always the address of a whole value, never of a part, which is why a `&string`, which may be a part of a string, never becomes an `&I` (C22), in a generic instance at `T := string` included (4.10). `&I | null` is `2P` too, with address 0 as `null`, the one exception to the tagged layout of `T | null` below, as a parameter as anywhere else: `null` is 0 in both words, and no reference is ever 0, one into an array of a zero-sized type included (`T[]` above). For a class `A` that can be extended, a whole-object move, copy or write through a `Box<A>`, an `&A` or `this` first compares the object's hidden pointer with `A`'s method table (4.3).

**Classes**: fields in declaration order, each at the next offset aligned for it; size rounded up to the class's alignment, the maximum of field alignments and 1. `@packed`: no padding, align 1. `@align(n)`: raises alignment and rounds size. A class that can be extended also carries a hidden method-table pointer of `P` bytes (4 on `i386-*`, 8 on `x86_64-*`), placed like a first field, at offset 0, and every class that extends one keeps it, `final` or not, because a call through a base reference reads it. The method table also records the class's size and alignment, which freeing a `Box` reads, and its name, which the exact-class check prints when it panics (9.1). The pointer names the table of the object's own class from the start of its construction, before the first field initialiser runs, so a base's constructor runs the object's own methods (4.3), and the table of each base in turn while that base's destructor and fields are cleaned up (5.7). Only an abstract class's table has slots for abstract methods, and an object's hidden pointer names it only in that turn, so each such slot, in that table and in its tables for interfaces, names a stub that panics (9.1), as a C++ pure virtual slot names one, and no slot is ever empty. A class that extends another starts with the base's pointer and fields at the base's offsets, where code holding a base reference reads them, and places its own fields after them in declaration order, starting at the base's size. A `final` class with no base carries none: it has no header, vtable or identity, which is why the layout decorators require such a class (EN0827). A subclass never reuses its base's tail padding: with `public class A { public a: i64; public b: u8; }` and `public class D extends A { public c: u8; }` on `x86_64`, `A` has its table pointer at 0, `a` at 8 and `b` at 16, size 24, and `D` places `c` at 24, size 32; on `i386`, `A` is size 16, and `D` places `c` at 16, size 20. A reference field of a borrowing class is laid out as the reference form it holds, and a reference part of a tuple takes the form its permission gives it, a by-value tuple parameter's parts included (5.3). Since these forms follow inferred permissions, the layout of a borrowing class or tuple is known only after contracts, so `sizeOf`, `alignOf` and `offsetOf` of one cannot appear in a `ConstExpr` (4.9).

**Anonymous object types and tuples**: fields are sorted by alignment, largest first, ties broken by field name in byte order, then placed like a class: each at the next offset aligned for it, size rounded up to the largest alignment, at least 1. `{ found: bool, index: i32, last: bool }` places `index` at 0, `found` at 4 and `last` at 5, size 8 on both `P == 4` and `P == 8`; the order can differ between targets, because `i64` aligns to 4 when `P == 4` and to 8 when `P == 8`. A tuple follows the same rule with the position as the name: `[bool, i32, bool]` is size 8, with element 1 at offset 0. A fields-only interface is an anonymous object type and takes this layout, and an optional field `x?: T` is a `T | null` field, or a `T` field when `T` as written where `?` is written is already nullable, which a type parameter never is (4.3). These types take no `@packed`, `@repr` or `@align`: hardware and foreign layouts use a `final` class. `sizeOf`, `alignOf` and `offsetOf` work on them as constants, but not on a borrowing tuple in a `ConstExpr` (4.9). A class passed where `&{ name: string }` is expected is read at the class's own offsets by the copy compiled for its shape.

**Enums**: tag at offset 0, payload at the next offset aligned for the largest case alignment; a case's fields are laid out as a `final` class beginning there; size is rounded up to the enum's alignment, the maximum of 4 and all payload alignments.

- Tag type is `u32` by default, so the alignment is at least 4. Tags number cases from 0 in declaration order, regardless of value. Exception: `@repr("u8")` on payload-free enums uses that size, and the tag equals the discriminant.
- Payload-free enums: size 4, align 4 by default, and the tag equals the discriminant.
- An enum whose cases carry texts (`NotANumber = "not a number"`) keeps the position as the tag, and its texts sit in a read-only table indexed by the tag.
- **`T | null`**: tag 0 means null, tag 1 means present, same layout rule. **No niche optimisation**: `&T | null` is `2P` on the stack when `&T` is one word, and `Box<T> | null` is `2P` when `Box<T>` is, unlike Rust. Raw pointers are the nullable word, and so is the address in `&I | null` for an interface `I`, the one exception (above).
- `Result<T, E>` (cases `Ok { value: T }` and `Err { error: E }`): `Ok` tag 0, `Err` tag 1, payload as above.

**Worked sizes:**

| Type | `P == 4` | `P == 8` |
|---|---|---|
| `string` | 12 | 24 |
| `i64[]` | 12 | 24 |
| `i64 \| null` | 12 | 16 |
| `public final class Player { public name: string; public score: i64; }` | 20 | 32 |
| same with `level: i32` added | 24 | 40 |
| `public enum Token { Num { value: i64 }, Add, Bad { text: string } }` | 16 | 32 |
| `@packed public final class GdtPointer { public limit: u16; public base: u32; }` | 6 | 6 |
| `{ found: bool, index: i32, last: bool }` | 8 | 8 |

**Calling conventions** are unstable and internal: i386 pushes all arguments right to left and the callee pops; x86-64 uses `rdi, rsi, rdx, rcx, r8, r9` and `xmm0-7`; aggregates pass by pointer to caller-owned memory and return through a hidden pointer. Foreign ABI appears only through `@abi` and `@dll`. No target uses a red zone, so interrupts on the current stack are always safe.

## 12. Testing

`test`, `describe`, `expect` and the matchers are compiler forms, not library functions: a by-value `expect` would move its operand, a library `expect` would need a `&` at every call and could not derive equality and printing for every type, and `enrang test` never runs top-level statements, so nothing could register tests at run time. They lower to ordinary MIR.

```ts
// src/stack.test.en: an extra part of module src/stack.en, so its private items are visible
private function twoUsers(): Stack<User> {  // a fixture is a function; teardown is a destructor
  let s = new Stack<User>();
  s.push(new User { name: "Ada", age: 36 });
  s.push(new User { name: "Grace", age: 85 });
  return s;
}

private class Case {
  public input: string;
  public want: i64;
}

describe("Stack", () => {
  test("pop is LIFO", () => {
    let s = twoUsers();
    expect(s.pop()).toBe(new User { name: "Grace", age: 85 });
    expect(s.size()).toBe(1);
  });

  test("top borrows", () => {
    const s = twoUsers();
    expect(s.top()).not.toBeNull();  // `&User | null`, compared through the reference
    expect(s).toMatchSnapshot();  // `s` is only borrowed
  });

  test.each(
    "parses",
    () => [
      new Case { input: "1", want: 1 },
      new Case { input: "x", want: 0 },
    ],
    (c: &Case) => { expect(c.input.parseInt() ?? 0).toBe(c.want); },
  );

  test.panics("bad index", "out of bounds", () => {
    const xs: i64[] = [];
    console.log(xs[0]);
  });

  test("heavy", () => { sortMillion(); }, { fuel: 2000000000, memory: "64MB" });
  test.todo("handles unicode");
});
```

### 12.1 Declarations

- `test`, `describe` are items with string-literal names, so test IDs are stable and filtering runs before execution. `A > B > c` is the ID. Duplicate IDs are EN1109.
- Tests live only in `*.test.en` files. `math.test.en` is an extra part of module `math.en` and sees its private items, the `private` top-level declarations, never a class's `private` members (4.3); a `test`, `describe`, `compileFails` or `compileOk` in any other file is EN1112 (`` tests go in `math.test.en` ``) with a fix-it that moves it there. The test file of a program file sees its classes and ordinary functions; the program's top-level statements never run under `enrang test`, and the local functions among them are not visible to tests.
- A `describe` body contains only `describe`, `test`, `compileFails`, `compileOk` (EN1102). `beforeEach`, `afterEach`, `beforeAll`, `afterAll` get EN1105 with a helper-function fix-it.
- A test is declared at the top level of its test file or in a `describe`, neither of which admits locals, so its arrow has nothing to capture; a `test` declared inside a function is EN1110. Fixtures are functions. The arrow returns `void` unless annotated: `(): Result<void> => { const v = parse("1")?; return Ok(); }`, where reaching the end of the arrow also returns `Ok()`. An `Err` fails the test with T0007, and `?` and `return` act on the arrow. The test binary prints the error itself, `error: <e>` through `Display`, exactly as `main` does (6), and sends that text to the runner as the failure's text, so an error type that writes `fmt` shows what its `fmt` writes, and `Err("disk, full")` shows `error: disk, full`. Test binaries, freestanding ones included, therefore carry the formatter, which costs size but never allocates (4.4).
- `test.only`, `test.skip`, `test.todo` have the obvious meanings; `--ci` refuses `only` (EN1106) and never writes new snapshots. `test.panics(name, substring, body)` passes iff the body panics with that substring.
- `test.each(name, cases, body)` runs `body` once per element with a `&Case`. That parameter's permission is never inferred: it is read-only even in a body containing `unsafe`, and a body that writes through it is EN0615. Each case has the ID `parses[2]`, zero-based, known at run time; `-t` filters on it. Fuel and leak balance are per case. The generator must be deterministic, because a native run re-runs it to resume after a panic. The final `Tests` line counts cases.
- Options: `{ fuel: n, memory: "64MB", allow: ["read:fixtures/"] }`. Only a literal `ObjectLit`. `allow` may name only paths inside the project root, after canonicalisation and with `..` rejected (EN1111); anything wider needs a command-line grant such as `--allow-read=`, so source code cannot widen its own sandbox. `--ci` prints the effective grants.

### 12.2 `expect`

`expect(a).matcher(b);` is a statement. It lowers to `&a`, `&b`, a call to compiler-derived `__eq<T>`, and a cold branch to `__fail`. These are real shared borrows for one statement, so a live exclusive borrow still gets EN0708. Rvalues become temporaries dropped at statement end. With no unwinding, a failed `expect` ends the test with no drops; the VM discards the heap, and a native process dies and is resumed at the next test by the parent.

`__eq<T>` is derived deep structural equality. A user's `Eq` is never consulted, so code under test does not grade itself. Floats follow `Object.is`: `+0` differs from `-0`, `NaN` equals `NaN`. Matchers peel one `&` and one `| null` from the actual type (R2 caps the depth), and literals adapt to the inner type. `__show<T>` is derived printing that does not allocate: tagged records on a framed channel (host call in the VM, fd 3 on Linux, stderr on Windows, COM1 freestanding), rendered by the parent, so reporting cannot disturb allocation counts. The parent renders each value that a failed matcher shows, actual and expected, from these records, and quotes a string, a string part, a value of a string-literal union, a `Failure` and a text case of an enum with no written `fmt` by 4.4's rule for a value inside another, at every level, so a string at the top level is quoted too: `expect(greet()).toBe("hi Ada")` against `"hi Ada "` shows `'hi Ada'` and `'hi Ada '`. A value whose type writes `fmt`, at any level, reaches the parent as a record holding the text its `fmt` writes, which the test binary runs only once the matcher has failed, when the test's allocation counts no longer matter (12.4), with the formatter it carries for T0007 (12.1), so a diff shows such a value as it prints inside another value (4.4).

| Group | Matchers (all accept `.not`) |
|---|---|
| Equality | `toBe(v)` |
| Bool | `toBeTrue()`, `toBeFalse()` |
| Null, Result | `toBeNull()`, `toBeOk(v?)`, `toBeErr(v?)` |
| Enums | `toMatchPattern(ArmValue)`, lowered to `match` |
| Order | `toBeGreaterThan`, `toBeGreaterThanOrEqual`, `toBeLessThan`, `toBeLessThanOrEqual` |
| Floats | `toBeCloseTo(v, eps)`, `toBeNaN()`, `toHaveBits(bits)` (compares `toBits()`) |
| Containers, strings | `toHaveLength(n)`, `toContain(x)`, `toStartWith(s)`, `toEndWith(s)` |
| Snapshots | `toMatchSnapshot()`, `toMatchInlineSnapshot(raw`...`)` |

`toBeErr(v)` compares a `Failure` by its text (`toBeErr("negative age")`) and an enum error by its case (`toBeErr(AgeError.Negative)`). `toMatchPattern` takes the values one `match` arm lists, such as `Shape.Circle`, and binds nothing.

Jest arrivals get EN1104: `toEqual`, `toStrictEqual` get a rename fix-it to `toBe`, `toBeTruthy` explains there is no truthiness, `toThrow` points to `test.panics`, `toHaveBeenCalled` suggests injecting through `T extends Clock`. `expect` outside a test is EN1101; `const e = expect(x)` is EN1103.

### 12.3 Compile-error tests

```ts
compileFails(
  "use after move",
  raw`
  function take(u: U): void {}
  const u = new U { name: "Ada" };
  take(u);
  console.log(u.name); //~ EN0601
  private class U { public name: string; }
`,
);

compileFails(
  "bswap above the floor",
  raw`
  //! target: i386-none, cpu: i386
  private function f(): void { unsafe { asm("bswap eax"); } } //~ EN0901
`,
);

compileOk("borrow ends at last use", raw`...`);
```

The embedded compiler runs these in the runner at discovery, identically for any test target. `enrang fmt` never changes a snippet: raw template contents stay as written and `*.fail.en` files are skipped, so every anchor stays on its line. The set of (line, code) pairs must match exactly, so a snippet cannot pass because of an unrelated typo. The set includes warnings. `compileFails` needs at least one anchor on an `E` code. `compileOk` may carry anchors, only for `W` codes. Any mismatch is EN1107. `//~ EN0601 "substring"` also checks the message. `//!` sets `target`, `cpu`, `float`. `{ snapshot: true }` stores the rendered diagnostic; `{ fixes: true }` applies fix-its and requires the result to compile, and warnings in the fixed program are accepted. Snippets containing backticks live in `name.fail.en` beside the test file with the same anchors, and are discovered automatically.

### 12.4 Runner

- **VM by default.** One worker per core; the front end runs once per file, MIR is shared. Each test gets a fresh heap and globals image. Fuel: one unit is one MIR statement or terminator, default 200 million per test; running out is T0004. No wall clock, so timeouts never flake. No capabilities, a virtual clock, a per-test temp directory unless granted.
- **Native on request:** `enrang test --target=<t> --cpu=<l>`, or `--matrix` for every runnable cell. Each test file is one binary with a static test table. A panic or timeout kills only that process; the parent resumes at the next test. Wall-clock watchdog 10 s. `--isolate=test` respawns per test. `--shuffle=<seed>`.
- **Leaks.** The VM tracks every allocation; native compares `core` allocator counters around each test. A passing test must balance (T0003). Failed tests are exempt, because no drops ran. A leak in a test reaching no user `unsafe` is labelled a compiler bug.
- **Filters:** paths, `-t "Stack > pop"` (substring, `*`), `--only-failed`, `--bail`. **Reporters:** `pretty`, `dots`, `json` (versioned NDJSON), `junit`. Reporter output, including `fail[...]` blocks, goes to stdout; compile diagnostics go to stderr. `-u` updates snapshots; `__snapshots__/` sits beside the test file. `--watch` polls mtimes. `--coverage` is deferred (EN1041).
- **`native-only` tests.** Tests reaching `asm` or port I/O through the monomorphised call graph are counted separately in the VM; `--strict` fails them (EN1201).
- **Stripping.** `build`, `run` and `dev` leave `*.test.en` files out; `__eq`, `__show` exist only in test builds. A module builds byte-identical with or without its test file, and checks the same: a test reaches no `private` member, so its items never set a borrowing class's flag (4.3).

Test verdict codes:

| Code | Meaning |
|---|---|
| T0001 | `toBe` and other value matchers found different values |
| T0002 | Test panicked unexpectedly |
| T0003 | Test passed but leaked: allocation counts did not balance |
| T0004 | Test exceeded its fuel budget |
| T0005 | `test.panics` body did not panic or panicked with another message |
| T0006 | Snapshot mismatch or missing under `--ci` |
| T0007 | Test returned `Err` |
| T0008 | Native watchdog timeout |

### 12.5 Canonical style

`enrang fmt`, from M1, rewrites files into the one style below. `enrang fmt --check` changes nothing and exits 1 if any file would change, whether the input comes from files or stdin (`src/vga.en would be reformatted`, `1 of 9 files would change`). A file that does not parse is left untouched and its syntax error is printed. No flag, configuration file or `enrang.json` key changes the layout. `*.fail.en` files are skipped (12.3). Every code block of Enrang source in this document is already in this style, except G01-G04, which are invalid on purpose; examples quoted inline in prose may stay on one line.

- **What never changes.** The tree: parsing the output gives the input's tree with its import lines and the names in each import brace list reordered by the Imports rule below, and is otherwise equal to it. The tree records a string literal's value, not its quotes or escapes, and records neither the parentheses around a single untyped arrow parameter nor the optional `;` after a statement `match`, so the Quotes, Arrow parameters and `match` rules below keep it equal. A second run changes nothing. The text and order of every comment, apart from the indentation and trailing spaces described below. The text of every template and `raw` literal, and the value of every string literal, whose quotes and escapes change only as the Quotes rule below says. The spelling of each number literal, which the tree keeps (`0xB8000` stays `0xB8000`, hex case included, and `1e308` stays `1e308`), and every pair of parentheses the author wrote around an expression, which the tree keeps as a paren node; only the parentheses around a single untyped arrow parameter are removed (below). Line-sensitive parses: a path and the `{` of its literal stay on one line (`new Point {`, `Shape.Circle {`), and a `<` that starts type arguments keeps no space before it.
- **Opting out.** `// enrang-fmt-ignore` keeps the next statement or declaration exactly as written; a whole table is the unit, never one element of it. `// enrang-fmt-ignore-file` on line 1 leaves the whole file as written. These spellings avoid the reserved `//~` and `//!` prefixes.
- **Width.** 100 columns, a rule rather than a default, counted in characters as displayed. Trailing comments do not count and may run past it, and a string or template literal is never broken, so a line holding one may pass 100. There is no hidden sub-limit, apart from the chain and row rules below.
- **Bodies.** A `{ }` body goes on one line when it holds exactly one statement, that statement holds no block of its own, and the line fits, however the author wrote it: `if (p == null) { return; }`. Two or more statements, a statement holding a block, or a `//` comment inside put one statement per line, and the rule then applies again to each inner body. Class and enum bodies always go one member per line, and the last enum case gets a trailing comma. An `if` with an `else` always splits, every branch one statement per line, with each `else` on the `}` line (`} else {`); a comment after the `}` moves `else` to the next line.
- **`match`.** Arms go one per line, even when the whole `match` would fit on one line, so a body holding a `match` always splits, and the last arm gets a trailing comma, as the last enum case does. A block arm follows the body rule above. A `match` used as a statement ends at its `}` with no `;`, so `fmt` drops the optional `;` that 3.3 allows there. A `match` inside a declaration keeps the declaration's `;` (`const label = match (s) {` ... `};`), and a `match` inside any other statement, such as a `return`, keeps that statement's `;`.
- **Lists.** A list that does not fit (arguments, parameters, arrays, object literals, imports) goes one item per line with a trailing comma and the closing bracket on its own line. A last argument that is a block-bodied arrow or an object literal stays on the call's line when everything before it fits: `test("boots", () => {`. A list whose items are all 10 characters or shorter fills lines instead. When nested lists do not fit, the outermost breaks first, and inner lists stay on one line if they then fit. A list holding a multi-line template goes one item per line, except a call whose only argument it is: ``asm(`...`)``.
- **Rows.** An array literal with 2 or more elements goes one element per line, even when it fits, when every element is an array literal with 2 or more elements, or every element is a class or object literal with 2 or more fields; the classes may differ, and tuple values such as `[min, max]` count. A repeat literal `[0; 3]`, a spread or any other element switches the rule off, so `[[1], [2]]`, `[[1, 0], 2]` and `[entry(0, 0x9a), entry(1, 0x92)]` stay on one line. Columns are never aligned, and a row too long breaks like any list.
- **Signatures.** Parameters that do not fit break one per line with a trailing comma, closed by `): Ret {`; a long return type alone forces this, even for one parameter. If `function name<...>(` does not fit, the type parameters break first, closed by `>(`. If the `): Ret {` line still does not fit, the return type's type arguments break one per line with a trailing comma. `{` never goes on a line by itself.
- **Right-hand sides.** A call, class literal or array on the right of `=` keeps `= callee(` on the first line and breaks its own list. The break goes after `=` only for a right-hand side with no list of its own (a sum, `??`, a ternary, a member access), or when `name = callee(` alone does not fit; a sum then breaks by the operator rule. A `return` of a call breaks the call's list.
- **Operators.** A long `&&`, `||`, `+` or `??` expression ends each line with its operator (`config.enabled &&`). It breaks at the weakest operator present, one operand per line, with higher-precedence groups kept whole (`basePrice * quantity +`) and continuation lines indented 2 more; no parentheses are added. A broken `if` condition is `if (`, the operands, then `) {`. A broken ternary puts `?` and `:` at the start of their lines, since a line break counts as the space before a ternary `?` (section 2).
- **Method chains.** A chain of 2 or more calls that does not fit puts each call on its own line, starting with `.` and indented 2 more; the names and property accesses before the first call stay on the first line (`this.items`, `os.fs`). The chain breaks at its dots before any argument list does, and postfix `?` and `!` stay attached; a single call breaks its argument list. A chain of more than 2 calls also breaks when it fits if any argument is not simple (an arrow, a binary expression such as `x + 1`, `??`, a multi-line template), even when its last argument is a block-bodied arrow: `items`, `.filter(isActive)`, `.sortBy(byName)` and `.forEach(item => {` each start a line, while a chain of 2 calls keeps such an arrow on its first line. Simple arguments are literals, names, `this`, one-line templates, member accesses, unary operators, arrays and class or object literals of simple items, and calls with simple arguments, so `items.map(getId).filter(isPositive).slice(0, 10).join(",")` stays on one line.
- **Arrow parameters.** A single untyped parameter has no parentheses: `xs.map(x => x * 2)`. They stay for a parameter type, a `let` parameter, no parameter, two or more parameters, and a return type: `(x): i64 => x * 2`.
- **Spaces.** A one-line brace list has one space inside each brace: `new User { name: "Ada", age: 36 }`, `const { a, b } = p;`, `import { serial, vga } from "os";`, `{ return x; }`. An empty pair, or an empty body written over several lines, is `{}`, and a body holding only a comment puts it on its own line. Brackets and parentheses are never padded: `[1, 2]`, `f(a, b)`.
- **Quotes.** Double quotes, unless the text holds more `"` than `'`; a tie goes to double quotes. Only the delimiters and the escapes of the two quotes change: the escapes the switch makes unnecessary go, and the chosen quote is escaped wherever the text holds it, as Prettier does. So `'it\'s'` becomes `"it's"`, `'say "hi"'` stays, `"say \"hi\""` becomes `'say "hi"'`, and the tie `'He said "hi" and it\'s, isn\'t'` becomes `"He said \"hi\" and it's, isn't"`. Template and `raw` literals are untouched. A single-quoted result must never lex as a lifetime (section 2, EN1005): right after `&` or `<`, a literal keeps double quotes when its single-quoted form would lex as one there, so `&"say \"hi\""` stays as written.
- **Imports.** Within each group of consecutive import lines, where a blank line ends a group, the lines are sorted, and so are the names in each brace list, in byte order: uppercase before lowercase, `"./x"` before `"core"`. A line's key is the value of its path, so its quotes never matter, `public import` lines sort among the others by the same key, and lines with equal paths keep their order. An `as` alias sorts by the imported name. Two imports from one path are not merged, and a group or brace list holding a comment stays as written.
- **Decorators** keep the placement the author wrote, each on the declaration's line or on a line of its own. A same-line decorator is followed by one space, and if the line then passes 100 columns the other rules apply to it. A decorator inside a type stays inline.
- **Blank lines.** At most one in a row, and none at the start or end of a block. Elsewhere 0 or 1 is kept as written, and `fmt` never inserts one, so blank lines between imports keep marking groups.
- **Comments.** No reflow, no space added after `//`, and `//~` and `//!` anchors untouched. A trailing comment gets exactly 2 spaces after the code, never aligned, and a comment right after `{` stays on that line. A `//` comment moves to the code's indentation and loses its trailing spaces. A block comment whose every line after the first starts with `*` (the closing `*/` counts) is reprinted with each `*` line at the code's indentation plus one space and its trailing spaces removed; any other block comment is printed as written, so only its first line moves. A one-line `/* ... */` does not split a short body. Comments may run past the width.

## 13. Diagnostics

### 13.1 Rendered format

Output goes to stderr, deterministic, UTF-8, no colour unless a TTY and `--color=auto`. Exact shape:

```text
error[EN0601]: `u` was moved into `archive`
 --> moved.en:6:15
  |
4 |   const u = new User("Ada");
  |         - `u` owns this `User`, which is not Copy
5 |   archive(u);
  |           - `u` moves here, because `archive` takes `User`, not `&User`
6 |   console.log(u.name);
  |               ^ used here, after the move
  |
  = note: <free text; continuation lines indented to align after "note: ">
help: <one line>
  |
5 |   archive(u.clone());
  |            ++++++++
  = explain: run `enrang explain EN0601`
```

- Header: `error[CODE]: message`, `warning[CODE]: message`. Message lower-case first letter unless a code span, no final period.
- Location line: gutter-width spaces, `--> file:line:col` of the primary span. Gutter width is the digit count of the largest line number shown, plus one space before `|`.
- Snippet lines in increasing order; line numbers right-aligned to the gutter. Unlabelled lines between two labelled lines print when the gap is at most two lines; otherwise a line containing only `...` replaces them. Labelled lines are followed by an annotation line: `^` repeated for the primary span, `-` for secondary spans, then one space and the label. A line with several spans gets one annotation line per span, primary first, then left to right. Spans are measured in columns of the source line; tabs render as one space.
- A bare gutter line separates snippets from `= note`, `= why`, `= rule`, `= from TypeScript` entries. Help blocks start at column 0 with `help:`; a help with no code is that single line. A suggestion snippet shows the changed line with `+` under additions and `~` under replacements. A wholly inserted line shows `+` in place of `|` with no mark line, and a wholly replaced line in a multi-line edit shows `~` in place of `|`. The line number of an inserted line is the line it will occupy before the other edits in that block apply.
- Last line of every error and test failure: `  = explain: run `enrang explain CODE``, with gutter padding as `|` uses. It prints even before that code's page has arrived, because `enrang explain` then gives the title and the milestone. Warnings do not print it.
- After all diagnostics: `error: aborting due to N previous errors` or `error: aborting due to 1 previous error`, with `; M warnings emitted` if any; a blank line separates diagnostics and precedes this line. Golden tests in section 14 omit nothing: they are the entire stderr.
- One warning reads `; 1 warning emitted`. Warnings alone, or test failures alone, print no aborting line.
- **A note** is `note: text`, with no code, no snippet and no explain line, and it counts toward nothing. An alias naming its resolved `--cpu` level is one.
- **A spanless diagnostic** (a command-line error) has no location line, no snippet and no bare gutter line, and its `=` lines sit where a one-digit gutter puts them.
- **Several files.** Each extra file gets its own `-->` line, with the primary's file first; a help edit in another file gets one too.
- **Spans.** A multi-line span marks from its start to the end of its first line. A zero-width span gets one mark. Any control character renders as one space, as a tab does.
- **Suggestions.** A line counts as wholly replaced when the edit covers it, ignoring outer white space, and `~` goes in the gutter only when the help shows more than one line. A deletion within a line gets one `~` at its place, and a whole line removed renders as `N ~`. A command in a help has a line with no number (`TESTING.md` section 9): it is never applied as a fix.
- `--error-format=json` emits one versioned JSON object per diagnostic with the same fields, and machine-applicable fix-its as byte-span edits. Commands in helps are listed separately, and a note has a null code.
- **Usage messages are not diagnostics.** A malformed command line (a missing argument, an unknown flag, an unknown code given to `explain`), and a command that has not reached its milestone, print `error: ...` with no code, optional `help:`, `note:` and `usage:` lines, and exit 2. Flag values that `TargetSpec` resolution rejects are diagnostics, with codes.
- A compile stops at the end of the first failing phase in this order: 1 lexical and syntax, 2 resolve and types, 3 moves and borrows, 4 level and layout, 5 reachability. Each phase reports all its errors with recovery. Phase 5 includes root collection (EN0310, EN0809). `build`, `run` and `dev` always run it. `check` and compile tests run it only if a root exists, so a file with no top-level statements, `main` or `@entry` is checked as a library.

`enrang explain <code>` prints the title, the rule, a failing example, a fixed example (both compiled by a meta-test for `Compile` codes, a transcript otherwise) and the TS perspective where relevant. Unknown code gets "did you mean".

### 13.2 Catalog

Each row reads `code severity phase owner since fixture title`. Severity is `E` error, `W` warning or `F` test verdict. Phase is the one in 13.1, with `0` for the command line and `R` for run time or reload. `owner` is the crate family that reports the code. `since` is the milestone that must make it fire. `fixture` says how its firing test runs: `Compile` (anchored source), `Cli` (a command), `Reload` (a dev scenario) or `TestRun` (a test-runner run).

`define_codes!` is generated from this table at M0. Meta-tests enforce only rows whose `since` has been reached (`TESTING.md` section 18). A `Compile` row has a firing fixture, a passing near-miss and an explain page whose examples compile; the other kinds have a firing scenario and an explain page with a transcript. Codes are never reused. A retired code leaves this table, and `enrang explain` prints why it went. EN0704 is retired: R3's rule 3 with EN0710 and EN0712 covers what it named. Also retired, each because the form it rejected is now valid or another code reports it: EN0204 and EN0212 (classes may extend a class, and `protected`, `abstract` and `super` are valid; see EN0442), EN0217 (an object literal without a class is an anonymous object), EN0223 (`x?: T` is valid on fields and parameters), EN0306 (user folders have namespaces; a private item is EN0311), EN0407 (object types are valid everywhere), EN0431 (`length()` is a method; a bare `.length` is EN0441), EN0505 (`match` arms bind no variables), EN0620 (a method with type parameters of its own is never overridden; an override of one is EN0460), EN0716 (`from` is removed; returned-reference sources are inferred), EN0719 (a `for...of` source is locked for the loop; changing it is EN0706), EN0720 (a part of an array is a `&Slice<T>`, and one passed where a growable `&T[]` is expected is EN0401), EN0810 (there is one raw pointer kind, `*T`), EN1008 (`match` guards and ranges are supported), EN1016 (default parameters and overloads are supported), EN1020 (`--float=x87` is accepted; it is the default at `i586` and `i686`) and EN1040 (a payload-free enum case may carry a text; mixing numbers and texts is EN0456).

```text
EN0001 E 1 syntax M1 Compile source is not valid UTF-8
EN0002 E 1 syntax M1 Compile unterminated block comment
EN0003 E 1 syntax M1 Compile unknown escape sequence
EN0004 E 1 syntax M1 Compile unterminated string or template
EN0005 E 1 syntax M1 Compile leading-zero integer literal (TS legacy octal)
EN0006 E 1 syntax M1 Compile malformed float literal, `.5` or `5.`
EN0007 E 1 syntax M1 Compile numeric literal suffix
EN0008 E 1 syntax M1 Compile unexpected character

EN0100 E 1 syntax M1 Compile unexpected token
EN0101 E 1 syntax M1 Compile missing `;`
EN0102 E 1 syntax M1 Compile unclosed delimiter
EN0103 E 1 syntax M1 Compile wrong spacing around `?` or postfix `!`
EN0104 E 1 syntax M1 Compile braces required after `if`, `else`, `while`, `for`
EN0105 E 1 syntax M1 Compile assignment used as a condition or as an operand of `&&`, `||` or `!`
EN0106 E 1 syntax M1 Compile `??` mixed with `||` or `&&` without parentheses
EN0107 E 1 syntax M1 Compile chained comparison
EN0108 E 1 syntax M1 Compile decorator cannot appear here
EN0109 E 1 syntax M1 Compile item not allowed at this position
EN0110 E 1 syntax M1 Compile `import` after an item
EN0111 E 1 syntax M1 Compile `break` or `continue` outside a loop, or crossing an arrow
EN0112 E 1 syntax M1 Compile unknown label
EN0113 E 1 syntax M1 Compile duplicate label
EN0114 E 1 syntax M1 Compile invalid assignment target
EN0115 E 1 syntax M1 Compile top-level statement after a class or other declaration
EN0116 E 1 syntax M1 Compile `const` without a value

EN0201 E 1 syntax M1 Compile `===` or `!==`: use `==` and `!=`
EN0202 E 1 syntax M1 Compile `var`: use `let` or `const`
EN0203 E 2 sema M2 Compile no truthiness: a condition must be `bool`
EN0205 E 1 syntax M1 Compile `any`: use a generic or enum
EN0206 E 1 syntax M1 Compile `undefined`: use `null`
EN0207 E 1 syntax M1 Compile `throw`, `try`, `catch`: use `Result`, `?`, `panic`
EN0208 E 1 syntax M1 Compile `>>>`: `>>` is logical on unsigned types
EN0209 E 1 syntax M1 Compile `switch`: use `match`
EN0210 E 1 syntax M1 Compile `unknown`: use a generic
EN0211 E 1 syntax M1 Compile `typeof`, `instanceof`: use an enum and `match`
EN0213 E 1 syntax M1 Compile `using`: every binding already drops; write a `destructor`
EN0214 E 1 syntax M1 Compile `readonly T` as a type other than a returned reference or a reference field: use `&T` (also phase 2)
EN0215 E 1 syntax M1 Compile union of object types: declare a class or enum
EN0216 E 1 syntax M1 Compile string-literal union outside a type alias, or mixed with other types
EN0218 E 1 syntax M1 Compile `function` expression: use an arrow
EN0219 E 2 sema M2 Compile `this` or `super` out of place
EN0220 E 1 syntax M1 Compile `interface ... extends`: list bounds with `&`
EN0221 E 2 sema M2 Compile `new` on a non-class
EN0222 E 1 syntax M1 Compile `namespace`, `delete`: not in Enrang
EN0224 E 1 syntax M1 Compile return type after a bare arrow parameter
EN0225 E 1 syntax M1 Compile `number`: use `f64`, or `int` for whole numbers
EN0226 E 1 syntax M1 Compile missing `public`, `private` or `protected`
EN0227 E 1 syntax M1 Compile both `?` and a default on a parameter or field
EN0228 E 1 syntax M1 Compile `move` before an expression: a value moves when there is no `&`
EN0229 E 1 syntax M1 Compile parameter with no default after one with a default or `?`

EN0301 E 2 sema M2 Compile unresolved name
EN0302 E 2 sema M2 Compile unresolved type
EN0303 E 2 sema M2 Compile no such member
EN0304 E 2 sema M2 Compile import cycle
EN0305 E 2 sema M2 Compile import path not found
EN0307 E 2 sema M2 Compile duplicate definition
EN0308 E 2 sema M2 Compile private or protected member
EN0309 E 2 sema M2 Compile wrong number of type arguments
EN0310 E 5 driver M4 Cli no top-level statements or `main` on a hosted target
EN0311 E 2 sema M2 Compile importing a `private` item
EN0312 E 2 sema M2 Compile imported file has top-level statements
EN0313 E 2 sema M2 Compile top-level variable not visible here
EN0314 W 2 sema M2 Compile `main` beside top-level statements is not the entry point
EN0315 E 2 driver M4 Cli module has a stale interface file and no source
EN0316 E 3 driver M4 Cli interface file's stored code fails the check on load

EN0401 E 2 sema M2 Compile mismatched types
EN0402 E 2 sema M2 Compile mixed numeric types
EN0403 E 2 sema M2 Compile operator needs integer types
EN0404 E 2 sema M2 Compile invalid `as`
EN0405 E 2 sema M2 Compile index must be an integer
EN0406 E 2 sema M2 Compile union other than `T | null`
EN0408 E 2 sema M2 Compile recursive type needs `Box`
EN0409 E 2 sema M2 Compile missing annotation on a parameter or field
EN0410 E 2 sema M2 Compile cannot infer type
EN0411 E 2 sema M2 Compile literal does not fit
EN0412 E 2 sema M2 Compile constant evaluation failed, or constant cycle
EN0413 E 2 sema M2 Compile `?.` on an owned rvalue
EN0414 E 5 mono M4 Compile monomorphisation depth above 64
EN0415 E 2 sema M2 Compile compile-time assert failed
EN0416 E 2 sema M2 Compile class does not satisfy `implements`
EN0417 E 2 sema M2 Compile interface mixes fields and methods
EN0418 E 2 sema M2 Compile invalid `implements Copy` (also phase 3)
EN0419 E 2 sema M2 Compile type argument does not satisfy a bound, or sealed bound implemented
EN0420 E 2 sema M2 Compile operator not applicable to these types
EN0421 E 2 sema M2 Compile `==` needs `Eq`
EN0422 E 2 sema M2 Compile assigning a value to a reference variable
EN0423 E 2 sema M2 Compile wrong argument count
EN0424 E 2 sema M2 Compile `?` in a function that does not return `Result` or nullable
EN0425 E 2 sema M2 Compile `?` error type differs
EN0426 E 2 sema M2 Compile unused `Result`
EN0427 E 2 sema M2 Compile missing return
EN0428 E 2 sema M2 Compile not callable
EN0429 E 2 sema M2 Compile `?` on a type other than `Result` or nullable
EN0430 W 2 sema M2 Compile integer division truncates
EN0432 E 2 sema M2 Compile ternary or arm types differ
EN0433 E 2 sema M2 Compile field with no default left unset
EN0434 E 2 sema M2 Compile unknown field in a literal
EN0435 E 4 layout M2 Compile type, frame or static too large for the target (also phase 5 and link)
EN0436 E 2 sema M2 Compile invalid `main` signature
EN0437 E 2 sema M2 Compile recursive type alias
EN0438 E 2 sema M2 Compile spread source is not an array of cloneable elements
EN0439 E 2 sema M2 Compile `extend` on an anonymous object type or tuple
EN0440 E 2 sema M2 Compile extra fields where the declared type fixes the storage
EN0441 E 2 sema M2 Compile `length` read as a property: call `length()`
EN0442 E 2 sema M2 Compile class extends a `final` class
EN0443 E 2 sema M2 Compile `override` on a member that replaces nothing
EN0444 E 2 sema M2 Compile member replaces a base member without `override`
EN0445 E 2 sema M2 Compile `new` on an abstract class
EN0446 E 2 sema M2 Compile class does not implement an abstract method
EN0447 E 2 sema M2 Compile named form on a class with a constructor
EN0448 E 2 sema M2 Compile class needs a constructor: a field has no default
EN0449 E 2 sema M2 Compile arguments to `new` or `super` for a class with no constructor
EN0450 E 2 sema M2 Compile overloads one call cannot tell apart
EN0451 E 2 sema M2 Compile no overload, or more than one, matches the call
EN0452 E 2 sema M2 Compile tuple index out of range or not a constant
EN0453 W 2 sema M2 Compile result of a must-use call is not used
EN0454 E 2 sema M2 Compile `Result` error argument is not an error type
EN0455 E 2 sema M2 Compile plain value that could be a success or an error
EN0456 E 2 sema M2 Compile enum `=` values mix numbers and texts
EN0457 E 2 sema M2 Compile `super` call to an abstract method
EN0458 E 2 sema M2 Compile `move` method not declared in the receiver's class
EN0459 W 2 sema M2 Compile `move` method of an abstract class can never run
EN0460 E 2 sema M2 Compile override of a method compiled once per type, or an abstract one

EN0501 E 2 sema M2 Compile non-exhaustive `match`
EN0502 E 2 sema M2 Compile unqualified enum case in a `match` arm
EN0503 W 2 sema M2 Compile unreachable arm
EN0504 E 2 sema M2 Compile arm value does not match the subject's type
EN0506 E 2 sema M2 Compile refutable pattern in a destructuring

EN0601 E 3 borrowck M3 Compile use after move
EN0602 E 3 borrowck M3 Compile use before assignment of a type with no default
EN0603 E 3 borrowck M3 Compile move through a reference
EN0604 E 3 borrowck M3 Compile move out of an array element
EN0605 E 3 borrowck M3 Compile move out of `*box`
EN0606 E 2 sema M2 Compile a `destructor` called by name, or declared in an interface
EN0607 E 3 borrowck M3 Compile partial move from a class with a destructor
EN0608 E 3 borrowck M3 Compile mutating through `const`
EN0609 E 3 borrowck M3 Compile writing a `readonly` field
EN0610 E 3 borrowck M3 Compile `this` used before all fields are assigned
EN0611 E 3 borrowck M3 Compile moved in a previous loop iteration
EN0612 E 2 sema M2 Compile missing `&` where a reference is expected
EN0613 E 3 borrowck M3 Compile assignment to a `const` or to a parameter not marked `let`
EN0614 E 3 borrowck M3 Compile changing method called on a `const` value or through a read-only reference
EN0615 E 3 borrowck M3 Compile body does more with its references than its declaration allows
EN0616 E 3 borrowck M3 Compile writing through a read-only reference, rebinding or storing through a capture, or storing into a `readonly &` field from a field written through
EN0617 E 3 borrowck M3 Compile closure moves a capture
EN0618 E 3 borrowck M3 Compile call reads a top-level variable before its declaration
EN0619 E 3 borrowck M3 Compile `super(...)` not run exactly once on every path
EN0621 E 3 borrowck M3 Compile an assignment's value can't be kept

EN0701 E 2 sema M2 Compile reference, or a class holding one, in an element, payload, generic argument or interface value, or in a non-`private` field
EN0702 E 2 sema M2 Compile reference to a reference
EN0703 E 2 sema M2 Compile type parameter bound to a reference
EN0705 E 2 sema M2 Compile closure type outside a parameter, or nested closure type
EN0706 E 3 borrowck M3 Compile mutated while shared-borrowed
EN0707 E 3 borrowck M3 Compile second exclusive borrow
EN0708 E 3 borrowck M3 Compile read while exclusively borrowed
EN0709 E 3 borrowck M3 Compile moved while borrowed
EN0710 E 3 borrowck M3 Compile returning a reference to local data
EN0711 E 3 borrowck M3 Compile dropped while borrowed
EN0712 E 3 borrowck M3 Compile temporary dropped while borrowed
EN0714 E 3 borrowck M3 Compile returned reference from a parameter outside the allowed sources
EN0715 E 3 borrowck M3 Compile closure capture conflicts with a live borrow
EN0718 E 3 borrowck M3 Compile closure used re-entrantly: called, forwarded or captured twice

EN0801 E 2 sema M2 Compile operation needs `unsafe`
EN0802 E 2 sema M2 Compile invalid type for an `unsafe let`
EN0803 E 2 sema M2 Compile function with preconditions used as a safe `fn` or closure
EN0804 E 4 borrowck M3 Compile reference to a misaligned packed field
EN0805 E 2 sema M2 Compile volatile access on a type outside `VolatileValue`
EN0806 E 2 sema M2 Compile unknown or misapplied decorator, or library-only form in user code
EN0807 E 2 sema M2 Compile calling an interrupt handler
EN0808 E 2 sema M2 Compile invalid interrupt signature
EN0809 E 5 driver M9 Compile missing or invalid `@entry`
EN0811 E 2 sema M9 Compile second `@panicHandler`
EN0812 E 5 mono M9 Compile missing `@panicHandler`
EN0813 E 5 link M9 Compile `@at` overlap
EN0814 E 2 sema M2 Compile section not allowed on this target, or reserved
EN0815 E 2 sema M2 Compile `declare function` without `@dll`
EN0816 E 2 sema M2 Compile `string`, `T[]` or a reference in FFI
EN0817 E 2 sema M2 Compile conflicting layout attributes
EN0819 E 2 sema M2 Compile unknown `@abi`
EN0820 E 5 mono M9 Compile allocation with no global allocator
EN0821 E 2 sema M4 Compile second `@globalAllocator`
EN0822 E 2 sema M4 Compile allocator type lacks `GlobalAllocator`
EN0823 E 5 mono M9 Compile `os` hosted API on a freestanding target
EN0824 E 5 mono M9 Compile allocation reachable from an interrupt handler, panic handler or the allocator
EN0825 E 2 sema M4 Compile `@globalAllocator` on something other than an `unsafe let`
EN0826 E 2 sema M2 Compile `@packed` field must be Copy and non-generic
EN0827 E 2 sema M2 Compile layout decorator on a class that is not `final`, has a base, or holds a hidden pointer
EN0828 W 2 sema M2 Compile function that is not `unsafe` reads or writes through a raw-pointer parameter

EN0901 E 4 codegen M5 Compile instruction above the target CPU level
EN0902 E 4 codegen M5 Compile unknown mnemonic
EN0903 E 4 codegen M5 Compile invalid operands
EN0904 E 4 codegen M5 Compile unknown register
EN0905 E 4 codegen M5 Compile cannot bind stack or frame register
EN0907 E 2 sema M2 Compile `@requires` function called outside `unsafe`
EN0908 E 2 sema M2 Compile unknown feature name
EN0909 E 0 target M1 Cli unknown or rejected `--cpu`
EN0910 E 4 sema M5 Compile atomic operation or `Atomic64` above the level
EN0911 E 0 target M1 Cli float strategy not available at this level or on this target
EN0912 E 0 target M1 Cli level does not apply to this target
EN0913 E 4 codegen M5 Compile `@bits` misuse
EN0914 W 4 codegen M5 Compile `popa` erratum at `i386`
EN0915 E 4 codegen M5 Compile interpolation in `asm`
EN0916 E 4 codegen M5 Compile MMX, 3DNow! or packed SSE form
EN0917 E 4 codegen M5 Compile register not valid in this mode

EN1001 E 1 syntax M1 Compile async functions
EN1002 E 1 syntax M1 Compile generators
EN1003 E 2 sema M2 Compile threads
EN1004 E 2 sema M2 Compile shared ownership types
EN1005 E 1 syntax M1 Compile named lifetimes
EN1006 E 2 sema M2 Compile interface type by value outside a parameter
EN1007 E 2 sema M2 Compile capturing arrow as a function pointer
EN1009 E 1 syntax M1 Compile unsupported module form
EN1010 E 1 syntax M1 Compile default in a destructuring pattern
EN1011 E 2 sema M2 Compile range indexing, `str`
EN1012 E 2 sema M2 Compile `Map` and `Set`
EN1013 E 1 syntax M1 Compile spread outside an array literal, and rest
EN1014 E 2 sema M2 Compile unsupported generic feature
EN1015 E 2 sema M2 Compile unsupported `for...of` source
EN1017 E 1 syntax M1 Compile setters
EN1018 E 1 syntax M1 Compile operator overloading
EN1019 E 2 sema M2 Compile character type
EN1021 E 1 syntax M1 Compile static fields
EN1022 E 1 syntax M1 Compile `**` operator
EN1023 E 1 syntax M1 Compile type-level computation
EN1024 E 1 syntax M1 Compile intersection types
EN1025 E 1 syntax M1 Compile regular expressions
EN1026 E 2 sema M2 Compile `Math`
EN1027 E 2 sema M2 Compile `JSON`
EN1028 E 2 sema M2 Compile network APIs
EN1029 E 2 sema M2 Compile reflection
EN1030 E 2 sema M2 Compile foreign ABI, or class by value in FFI
EN1031 E 0 target M1 Cli 32-bit Windows output
EN1032 E 2 sema M2 Compile compile-time function calls
EN1033 E 2 sema M2 Compile unchecked reinterpretation
EN1034 E 0 cli M1 Cli DWARF output
EN1035 E 1 syntax M1 Compile nested functions
EN1036 E 1 syntax M1 Compile generic arrows
EN1037 E 1 syntax M1 Compile class expressions
EN1038 E 1 syntax M1 Compile labelled blocks
EN1039 E 1 syntax M1 Compile `as const`
EN1041 E 0 cli M1 Cli `--multiboot`, `--coverage`
EN1042 E 2 sema M2 Compile destructuring a `T[]` or `T[N]`

EN1101 E 2 sema M4 Compile `expect` outside a test
EN1102 E 1 syntax M4 Compile non-test content in `describe`
EN1103 E 2 sema M4 Compile `expect` as a value
EN1104 E 2 sema M4 Compile Jest matcher hint
EN1105 E 1 syntax M4 Compile lifecycle hook hint
EN1106 E 0 testrun M4 TestRun `test.only` under `--ci`
EN1107 E 0 testrun M4 TestRun compile-test anchor mismatch
EN1108 E 2 sema M4 Compile unknown matcher
EN1109 E 2 sema M4 Compile duplicate test ID
EN1110 E 2 sema M4 Compile test declared inside a function
EN1111 E 0 testrun M4 TestRun `allow` names a path outside the project root
EN1112 E 1 syntax M4 Compile test outside a `*.test.en` file

EN1201 E 5 mono M4 Cli program cannot run in the VM: `asm` reachable
EN1202 E 5 mono M4 Cli raw `syscall` reachable in the VM
EN1203 E 5 mono M4 Cli port I/O reachable in the VM
EN1204 E R vm M4 Cli integer-derived pointer with no provenance, "this touches physical memory"
EN1205 E 5 mono M4 Cli interrupt handler reachable in the VM
EN1210 E R dev M6 Reload reload refused: migration impossible, with path
EN1211 E 2 sema M6 Compile `@devMigrate` hook called from code
EN1212 W R dev M6 Reload stale migration hook
EN1213 E R dev M6 Reload reload blocked by a live reference
EN1214 E R dev M6 Reload reload refused: raw pointer into a rewritten allocation
EN1215 E R dev M6 Reload census failure
EN1216 E R dev M6 Reload narrowing retype failed on a value
EN1217 E R dev M6 Reload migration hook reaches user `unsafe`, an `unsafe let` or a host call

EN1301 E 0 cli M0 Cli deferred command
EN1302 E 0 cli M0 Cli unknown command
EN1303 E 0 target M1 Cli unknown target
EN1304 E 0 target M1 Cli invalid flag value or combination, or `--base` overlapping the boot stages
EN1305 E 0 cli M1 Cli file not found
EN1306 E 0 cli M5 Cli output path not writable
EN1307 E 0 cli M1 Cli `init` would overwrite

T0001 F R testrun M4 TestRun value matcher found different values
T0002 F R testrun M4 TestRun test panicked unexpectedly
T0003 F R testrun M4 TestRun test passed but leaked
T0004 F R testrun M4 TestRun test exceeded its fuel budget
T0005 F R testrun M4 TestRun `test.panics` body did not panic as expected
T0006 F R testrun M4 TestRun snapshot mismatch, or missing under `--ci`
T0007 F R testrun M4 TestRun test returned `Err`
T0008 F R testrun M5 TestRun native watchdog timeout
```

`EN1301` covers `install`, `add`, `publish`, `doc`, `lsp`, `repl`, `bench`, `debug` and `upgrade`. `EN1302` carries the aliases `tsc`, `lint` to `check`, `compile` to `build`, `start` to `run`. Section 16 gives the message head and help of each EN10xx row.

Exit codes: 0 success, 1 compile errors, failed tests or lost output, 2 usage, 3 internal compiler error. `enrang fmt --check` also exits 1 when a file would change. Lost output means a write to stdout or stderr failed during a run that had otherwise succeeded. A reader that closed its pipe, as in `enrang targets | head -n 1`, is not lost output, and a run that already failed keeps its status.

## 14. Golden diagnostics

Each case is a source file, a command, and the full stderr. The marker gives the exit status: 1 for a compile error, and 0 for a program with warnings alone. These become byte-exact golden tests. Source files end with one newline.

**Case markers.** Every extracted case in sections 1, 14 and 15 starts with `<!-- case: ID files=a.en,b.en cmd="..." exit=N [stdout=block|inline] [stderr=block|inline] [serial=block] -->`. The `ts` blocks after the marker are the source files, in `files` order. The `text` blocks after them are the expected outputs, in the order stdout, stderr, serial. `inline` means the expectation is in the code spans of the next sentence that names that stream. A stream the marker does not name is expected to be empty, except that a `dev` or `build` command may also write its artefact. The extractor reads markers and blocks only, and no prose except the one sentence an `inline` stream names. In that sentence `Output:` means stdout, and each code span is one line ending in a newline. A meta-test requires every `G` and `S` heading to have a marker.

### G01 Missing semicolon

<!-- case: G01 files=g01.en cmd="enrang check g01.en" exit=1 stderr=block -->
```ts
const x = 1
console.log(x);
```

`enrang check g01.en`

```text
error[EN0101]: missing `;` after this statement
 --> g01.en:1:12
  |
1 | const x = 1
  |            ^ expected `;` here
  |
  = from TypeScript: Enrang has no automatic semicolon insertion.
help: add the semicolon
  |
1 | const x = 1;
  |            +
  = explain: run `enrang explain EN0101`

error: aborting due to 1 previous error
```

### G02 Unclosed brace

<!-- case: G02 files=g02.en cmd="enrang check g02.en" exit=1 stderr=block -->
```ts
function greet(): void {
  if (true) {
    console.log("hi");
}
greet();
```

`enrang check g02.en`

```text
error[EN0102]: the file ended with `{` still open
 --> g02.en:2:13
  |
2 |   if (true) {
  |             ^ this block has no matching `}`
3 |     console.log("hi");
4 | }
  | - this `}` lines up with `function` on line 1, so it probably closes that instead
  |
help: close the `if` block before line 4
  |
4 +   }
  = explain: run `enrang explain EN0102`

error: aborting due to 1 previous error
```

### G03 TS habit: strict equality

<!-- case: G03 files=g03.en cmd="enrang check g03.en" exit=1 stderr=block -->
```ts
const n = 3;
if (n === 3) {
  console.log("three");
}
```

`enrang check g03.en`

```text
error[EN0201]: `===` does not exist in Enrang
 --> g03.en:2:7
  |
2 | if (n === 3) {
  |       ^^^ use `==` here
  |
  = from TypeScript: `==` never coerces in Enrang, so the strict form is the only form.
help: replace `===` with `==`
  |
2 | if (n == 3) {
  |       ~~
  = explain: run `enrang explain EN0201`

error: aborting due to 1 previous error
```

### G04 TS habits: `any`, `var`, `undefined`

<!-- case: G04 files=g04.en cmd="enrang check g04.en" exit=1 stderr=block -->
```ts
public function show(x: any): void {
  var y = undefined;
}
```

`enrang check g04.en`

```text
error[EN0205]: `any` does not exist in Enrang
 --> g04.en:1:25
  |
1 | public function show(x: any): void {
  |                         ^^^ every value has one known type
  |
help: accept every value type with a generic
  |
1 | public function show<T>(x: &T): void {
  |                     +++    ~~
  = explain: run `enrang explain EN0205`

error[EN0202]: `var` does not exist in Enrang
 --> g04.en:2:3
  |
2 |   var y = undefined;
  |   ^^^ use `let` for a binding that changes, `const` otherwise
  |
help: replace `var` with `let`
  |
2 |   let y = undefined;
  |   ~~~
  = explain: run `enrang explain EN0202`

error[EN0206]: `undefined` does not exist in Enrang
 --> g04.en:2:11
  |
2 |   var y = undefined;
  |           ^^^^^^^^^ absence has one spelling
  |
help: replace `undefined` with `null`, which needs a nullable type
  |
2 |   var y: i64 | null = null;
  |        ++++++++++++   ~~~~
  = explain: run `enrang explain EN0206`

error: aborting due to 3 previous errors
```

### G05 Mismatched types

<!-- case: G05 files=g05.en cmd="enrang check g05.en" exit=1 stderr=block -->
```ts
function area(w: i64, h: i64): i64 { return w * h; }

const a: string = area(2, 3);
console.log(a);
```

`enrang check g05.en`

```text
error[EN0401]: mismatched types: expected `string`, found `i64`
 --> g05.en:3:19
  |
3 | const a: string = area(2, 3);
  |                   ^^^^^^^^^^ this is `i64`
  |          ------ `string` is required by this annotation
  |
  = note: Enrang never converts between numbers and strings implicitly.
help: convert it explicitly
  |
3 | const a: string = area(2, 3).toString();
  |                             +++++++++++
  = explain: run `enrang explain EN0401`

error: aborting due to 1 previous error
```

### G06 Did you mean

<!-- case: G06 files=g06.en cmd="enrang check g06.en" exit=1 stderr=block -->
```ts
const total = 10;
console.log(totl);
```

`enrang check g06.en`

```text
error[EN0301]: cannot find `totl` in this scope
 --> g06.en:2:13
  |
1 | const total = 10;
  |       ----- a local with a similar name is declared here
2 | console.log(totl);
  |             ^^^^ not found
  |
help: did you mean `total`?
  |
2 | console.log(total);
  |             ~~~~~
  = explain: run `enrang explain EN0301`

error: aborting due to 1 previous error
```

### G07 Use after move

<!-- case: G07 files=g07.en cmd="enrang check g07.en" exit=1 stderr=block -->
```ts
function archive(u: User): void { console.log(u.name); }

const u = new User("Ada");
archive(u);
console.log(u.name);

private class User {
  public constructor(public name: string) {}
}
```

`enrang check g07.en`

```text
error[EN0601]: `u` was moved into `archive`
 --> g07.en:5:13
  |
3 | const u = new User("Ada");
  |       - `u` owns this `User`, which is not Copy because it has a `string` field
4 | archive(u);
  |         - `u` moves here, because `archive` takes `User`, not `&User`
5 | console.log(u.name);
  |             ^ used here, after the move
  |
  = from TypeScript: both names would share one object. In Enrang a value has one owner, so passing `u` hands it over.
help: if `archive` only needs to look at it, change the parameter to `u: &User`
  |
1 | function archive(u: &User): void { console.log(u.name); }
  |                     +
4 | archive(&u);
  |         +
help: to keep your own, pass a copy: `archive(u.clone())`
  |
4 | archive(u.clone());
  |          ++++++++
  = explain: run `enrang explain EN0601`

error: aborting due to 1 previous error
```

### G08 Mutation during iteration

<!-- case: G08 files=g08.en cmd="enrang check g08.en" exit=1 stderr=block -->
```ts
let queue = ["a", "b"];
for (const job of &queue) {
  if (job == "a") { queue.push("retry"); }
  console.log(job);
}
```

`enrang check g08.en`

```text
error[EN0706]: cannot mutate `queue` while iterating over it
 --> g08.en:3:21
  |
2 | for (const job of &queue) {
  |                   ------ immutable borrow begins here
3 |   if (job == "a") { queue.push("retry"); }
  |                     ^^^^^^^^^^^^^^^^^^^ conflicting mutable access
  |
  = note: structural mutations may invalidate the iterator
help: collect new jobs separately, or loop over a copy
  |
2 | for (const job of [...queue]) {
  |                   ~~~~     +
  = explain: run `enrang explain EN0706`

error: aborting due to 1 previous error
```

### G09 Two exclusive borrows

<!-- case: G09 files=g09.en cmd="enrang check g09.en" exit=1 stderr=block -->
```ts
function swapFirst(a: &Slice<i64>, b: &Slice<i64>): void {
  const t = a[0];
  a[0] = b[0];
  b[0] = t;
}

let xs = [1, 2];
swapFirst(&xs, &xs);
```

`enrang check g09.en`

```text
error[EN0707]: cannot borrow `xs` as exclusive twice at the same time
 --> g09.en:8:16
  |
8 | swapFirst(&xs, &xs);
  |                ^^^ second exclusive borrow
  |           --- first exclusive borrow, still live until the call returns
  |
  = rule: a value has many shared borrows or one exclusive borrow, never both.
help: to exchange two elements of one array, use `xs.swap(i, j)`
  = explain: run `enrang explain EN0707`

error: aborting due to 1 previous error
```

### G10 Dangling reference: returning a local

<!-- case: G10 files=g10.en cmd="enrang check g10.en" exit=1 stderr=block -->
```ts
public function longest(): &string {
  const s = "owned" + "!";
  return &s;
}
```

`enrang check g10.en`

```text
error[EN0710]: cannot return a reference to local `s`
 --> g10.en:3:10
  |
2 |   const s = "owned" + "!";
  |         - `s` is dropped when `longest` returns
3 |   return &s;
  |          ^^ this reference would point at freed memory
  |
  = rule: a returned reference must borrow from a parameter, and `longest` has no reference parameters.
help: return the owned value instead
  |
1 | public function longest(): string {
  |                            ~~~~~~
3 |   return s;
  |          ~
  = explain: run `enrang explain EN0710`

error: aborting due to 1 previous error
```

### G11 Dangling reference: inner scope

<!-- case: G11 files=g11.en cmd="enrang check g11.en" exit=1 stderr=block -->
```ts
const fallback = "none";
let r: &string = &fallback;
{
  const s = "a" + "b";
  r = &s;
}
console.log(r);
```

`enrang check g11.en`

```text
error[EN0711]: `s` is dropped while `r` still borrows it
 --> g11.en:6:1
  |
4 |   const s = "a" + "b";
  |         - `s` lives until the end of this block
5 |   r = &s;
  |       -- shared borrow of `s` starts here, held by `r`
6 | }
  | ^ `s` is dropped here
7 | console.log(r);
  |             - the borrow is still in use here
  |
help: declare `s` outside the block so it lives as long as `r`
  = explain: run `enrang explain EN0711`

error: aborting due to 1 previous error
```

### G12 Non-exhaustive match

<!-- case: G12 files=g12.en cmd="enrang check g12.en" exit=1 stderr=block -->
```ts
public enum Shape {
  Circle { radius: f64 },
  Square { side: f64 },
  Empty,
}

public function area(s: &Shape): f64 {
  return match (s) {
    Shape.Circle => 3.14 * s.radius * s.radius,
    Shape.Square => s.side * s.side,
  };
}
```

`enrang check g12.en`

```text
error[EN0501]: `match` doesn't handle `Shape.Empty`
  --> g12.en:8:17
   |
 4 |   Empty,
   |   ----- `Shape.Empty` is declared here
...
 8 |   return match (s) {
   |                 ^ missing `Shape.Empty`
   |
help: add `Shape.Empty => ...`, or a `default` arm
   |
11 +     Shape.Empty => panic("unhandled"),
   = explain: run `enrang explain EN0501`

error: aborting due to 1 previous error
```

### G13 Unsafe misuse

<!-- case: G13 files=g13.en cmd="enrang check g13.en" exit=1 stderr=block -->
```ts
const VGA = 0xB8000 as *u16;
VGA.writeVolatile(0x0741);
```

`enrang check g13.en`

```text
error[EN0801]: writing through a raw pointer needs `unsafe`
 --> g13.en:2:1
  |
2 | VGA.writeVolatile(0x0741);
  | ^^^^^^^^^^^^^^^^^^^^^^^^^ `writeVolatile` dereferences `VGA`, a `*u16`
  |
  = rule: `unsafe` grants exactly five powers; this one is "dereference a raw pointer". Nothing checks the address for you.
help: state that you have checked the address
  |
2 | unsafe { VGA.writeVolatile(0x0741); }
  | +++++++++                          ++
  = explain: run `enrang explain EN0801`

error: aborting due to 1 previous error
```

### G14 Allocation on a freestanding target

<!-- case: G14 files=g14.en cmd="enrang build --target=i386-none g14.en" exit=1 stderr=block -->
```ts
@entry private function kmain(boot: &BootInfo): never {
  let names: string[] = [];
  names.push("ada");
  halt();
}

@panicHandler private function onPanic(info: &PanicInfo): never { halt(); }
```

`enrang build --target=i386-none g14.en`

```text
error[EN0820]: `string[]` needs a heap, and this program has no global allocator
 --> g14.en:2:14
  |
2 |   let names: string[] = [];
  |              ^^^^^^^^ first allocating type reached from `@entry`
  |
  = note: target `i386-none` has no operating system to get memory from, so `alloc` works only after a program registers an allocator.
help: register an allocator and give it memory with `heap.addBootRegions(boot)` in `kmain`
  |
1 + @globalAllocator private unsafe let heap: FreeListHeap;
help: or stay allocation-free: fixed arrays `T[N]` and `&string` parameters need no allocator
  = explain: run `enrang explain EN0820`

error: aborting due to 1 previous error
```

### G15 Inline assembly above the target CPU level

<!-- case: G15 files=g15.en cmd="enrang build --target=i386-linux --cpu=i386 g15.en" exit=1 stderr=block -->
```ts
function swap32(x: u32): u32 {
  let r: u32 = x;
  unsafe { asm(`bswap eax`, { in: { eax: x }, out: { eax: r } }); }
  return r;
}

console.log(swap32(1));
```

`enrang build --target=i386-linux --cpu=i386 g15.en`

```text
error[EN0901]: `bswap` needs CPU feature `bswap`, which target level `i386` does not have
 --> g15.en:3:17
  |
3 |   unsafe { asm(`bswap eax`, { in: { eax: x }, out: { eax: r } }); }
  |                 ^^^^^^^^^ `bswap r32` needs level `i486` or higher
  |
  = note: `i386` output must run on every listed CPU, and an 80386 does not decode this instruction.
help: `x.swapBytes()` in `core` does the same at every level, with no `asm`
help: or build for a higher level: `--cpu=i486`
help: or mark a separate function `@requires("bswap")` and guard the call with `cpu.has("bswap")`
  = explain: run `enrang explain EN0901`

error: aborting due to 1 previous error
```

### G16 `const` is deep

<!-- case: G16 files=g16.en cmd="enrang check g16.en" exit=1 stderr=block -->
```ts
const xs: i64[] = [];
xs.push(1);
console.log(xs.length());
```

`enrang check g16.en`

```text
error[EN0614]: `xs` is `const`, so `push` cannot change it
 --> g16.en:2:1
  |
1 | const xs: i64[] = [];
  |       -- declared `const` here: immutable all the way down
2 | xs.push(1);
  | ^^^^^^^^^^ `push` changes `xs`
  |
  = from TypeScript: a TS `const` only freezes the binding. In Enrang values have no shared identity, so `const` freezes the value.
help: make the binding mutable
  |
1 | let xs: i64[] = [];
  | ~~~
  = explain: run `enrang explain EN0614`

error: aborting due to 1 previous error
```

### G17 Missing `&` at the call

<!-- case: G17 files=g17.en cmd="enrang check g17.en" exit=1 stderr=block -->
```ts
function bump(xs: &i64[]): void { xs.push(1); }

let a: i64[] = [];
bump(a);
```

`enrang check g17.en`

```text
error[EN0612]: missing `&`: `bump` takes a reference
 --> g17.en:4:6
  |
4 | bump(a);
  |      ^ expected `&i64[]`, found `i64[]`
  |
  = note: a reference is only ever made by writing `&`; with no `&`, a value is moved or copied.
help: write `&a`
  |
4 | bump(&a);
  |      +
  = explain: run `enrang explain EN0612`

error: aborting due to 1 previous error
```

### G18 A write the interface does not declare

<!-- case: G18 files=g18.en cmd="enrang check g18.en" exit=1 stderr=block -->
```ts
public interface Counter {
  inc(): void;
}

public class Clicks implements Counter {
  private n: i64 = 0;
  public inc(): void { this.n += 1; }
}
```

`enrang check g18.en`

```text
error[EN0615]: `inc` changes the object, but `Counter` declares that it doesn't
 --> g18.en:7:24
  |
2 |   inc(): void;
  |   --- declared here without `let`
...
7 |   public inc(): void { this.n += 1; }
  |                        ^^^^^^^^^^^ this write needs exclusive access to `this`
  |
help: if implementations may change the object, write `let inc(): void;` in `Counter`
  |
2 |   let inc(): void;
  |   ++++
  = explain: run `enrang explain EN0615`

error: aborting due to 1 previous error
```

### G19 An array of a class that holds a reference

<!-- case: G19 files=g19.en cmd="enrang check g19.en" exit=1 stderr=block -->
```ts
const source = "let x = 1;";
let lx = new Lexer(&source);
let all: Lexer[] = [lx];

private class Lexer {
  private src: &string;
  private pos: isize = 0;
  public constructor(src: &string) { this.src = src; }
}
```

`enrang check g19.en`

```text
error[EN0701]: an array can't hold a `Lexer`, because `Lexer` holds a reference
 --> g19.en:3:10
  |
3 | let all: Lexer[] = [lx];
  |          ^^^^^^^ `Lexer` borrows through its field `src`
  |
  = rule: a class that holds a reference lives only where a reference can: in locals, parameters, return values and fields of another such class.
help: own the data: `private src: string;`
  = explain: run `enrang explain EN0701`

error: aborting due to 1 previous error
```

### G20 Unused `Result`

<!-- case: G20 files=g20.en cmd="enrang check g20.en" exit=1 stderr=block -->
```ts
function save(name: &string): Result<void> { return Err(`cannot save ${name}`); }

save("a");
```

`enrang check g20.en`

```text
error[EN0426]: this `Result` is not used, so an error would be lost silently
 --> g20.en:3:1
  |
3 | save("a");
  | ^^^^^^^^^ returns `Result<void>`
  |
  = from TypeScript: a thrown exception cannot be ignored by accident, and neither can this.
help: discard it deliberately
  |
3 | void save("a");
  | +++++
  = explain: run `enrang explain EN0426`

error: aborting due to 1 previous error
```

### G21 Reassigning the source of a loop

<!-- case: G21 files=g21.en cmd="enrang check g21.en" exit=1 stderr=block -->
```ts
let q = [1, 2, 3];
for (const x of &q) {
  console.log(x);
  q = [];
}
```

`enrang check g21.en`

```text
error[EN0706]: cannot reassign `q` during iteration
 --> g21.en:4:3
  |
2 | for (const x of &q) {
  |                 -- `q` is borrowed here
3 |   console.log(x);
4 |   q = [];
  |   ^^^^^^ cannot reassign while borrowed
  |
help: iterate over `q.clone()` if reassignment is intentional
  |
2 | for (const x of q.clone()) {
  |                 ~~~~~~~~~
  = explain: run `enrang explain EN0706`

error: aborting due to 1 previous error
```

### G22 Spreading elements that may not be cloneable

<!-- case: G22 files=g22.en cmd="enrang check g22.en" exit=1 stderr=block -->
```ts
public function snapshot<T>(xs: &T[]): T[] { return [...xs]; }
```

`enrang check g22.en`

```text
error[EN0438]: `...` clones each element, and `T` has no `Clone` bound
 --> g22.en:1:54
  |
1 | public function snapshot<T>(xs: &T[]): T[] { return [...xs]; }
  |                                                      ^^^^^ each element of `xs` would be cloned here
  |                          - `T` is declared here
  |
  = from TypeScript: JS spread copies references to the same objects. In Enrang a value has one owner, so `...` copies the elements too.
help: require `Clone`
  |
1 | public function snapshot<T extends Clone>(xs: &T[]): T[] { return [...xs]; }
  |                           ++++++++++++++
  = explain: run `enrang explain EN0438`

error: aborting due to 1 previous error
```

### G23 A warning and an unrelated error

<!-- case: G23 files=g23.en cmd="enrang check g23.en" exit=1 stderr=block -->
```ts
let name = " Ada ";
name.trim();
console.log(name);

let queue = ["a", "b"];
const first = &queue[0];
queue.clear();
console.log(first);
```

`enrang check g23.en`

```text
warning[EN0453]: the result of `trim` is not used
 --> g23.en:2:1
  |
2 | name.trim();
  | ^^^^^^^^^^^ `trim` returns a new string and leaves `name` as it was
  |
help: keep it
  |
2 | name = name.trim();
  | +++++++

error[EN0706]: `queue` cannot change while `first` still points into it
 --> g23.en:7:1
  |
6 | const first = &queue[0];
  |               --------- shared borrow of `queue` starts here, held by `first`
7 | queue.clear();
  | ^^^^^^^^^^^^^ `clear` changes `queue`, so it needs exclusive access to it
8 | console.log(first);
  |             ----- `first` is used again here
  |
  = rule: a value has many shared borrows or one exclusive borrow, never both.
help: keep a copy instead of a reference
  |
6 | const first = queue[0].clone();
  |               ~~~~~~~~~~~~~~~~
  = explain: run `enrang explain EN0706`

error: aborting due to 1 previous error; 1 warning emitted
```

### G24 A field set after `super(...)`

<!-- case: G24 files=g24.en cmd="enrang check g24.en" exit=1 stderr=block -->
```ts
public class Person {
  public constructor(public name: string) {}
}

public class Animal {
  public constructor(public name: string) {}
}

public class Dog extends Animal {
  public owner: Person;

  public constructor(name: string, owner: Person) {
    super(name);
    this.owner = owner;
  }
}
```

`enrang check g24.en`

```text
error[EN0610]: `this.owner` is not set when `super(name)` runs
  --> g24.en:13:5
   |
13 |     super(name);
   |     ^^^^^^^^^^^ `Animal`'s constructor runs here, before `this.owner` is set
14 |     this.owner = owner;
   |     ------------------- `this.owner` is set only here
   |
   = from TypeScript: TypeScript requires `super(...)` before any use of `this` (TS17009). Enrang sets a subclass's own fields first, so a base constructor that calls an override finds them set.
help: set `this.owner` before `super(name)`, because `Animal`'s constructor may call `Dog`'s methods
   |
13 ~     this.owner = owner;
14 ~     super(name);
   = explain: run `enrang explain EN0610`

error: aborting due to 1 previous error
```

## 15. Sample programs

Each program is a conformance-corpus entry: every implementation (VM and each native target and level) must produce the same bytes on stdout and the same exit status. Hosted samples print the same on `x86_64-linux`, `x86_64-windows` and `i386-linux`, at every `--cpu` level.

### S1 Numbers and templates

<!-- case: S1 files=s01.en cmd="enrang run s01.en" exit=0 stdout=block -->
```ts
console.log("Hello, Enrang");
const a: i64 = 7;
const b: i64 = 2;
console.log(a + b, a - b, a * b);
console.log(7.0 / 2.0);
console.log(`${a} / ${b} = ${a / b}, rem ${a % b}`);
console.log(1.5 + 2.25, 0.1 + 0.2);
const m: i64 = -7;
console.log((300 as u16).wrap<u8>(), m / 2, m % 2);
```

Stdout:

```text
Hello, Enrang
9 5 14
3.5
7 / 2 = 3, rem 1
3.75 0.30000000000000004
44 -3 -1
```

### S2 Moves and drop order

<!-- case: S2 files=s02.en cmd="enrang run s02.en" exit=0 stdout=block -->
```ts
const a = new Tracer("a");
const b = new Tracer("b");
consume(a);
const c = new Tracer("c");
const p = new Pair(new Tracer("x"), new Tracer("y"));
console.log("end");

private class Tracer {
  public constructor(private name: string) {}
  public destructor() { console.log(`drop ${this.name}`); }
}

private class Pair {
  public constructor(public first: Tracer, public second: Tracer) {}
  public destructor() { console.log("drop pair"); }
}

private function consume(t: Tracer): void { console.log("consuming"); }
```

Stdout:

```text
consuming
drop a
end
drop pair
drop y
drop x
drop c
drop b
```

### S3 Enums, `Box`, `match`, `?`

<!-- case: S3 files=s03.en cmd="enrang run s03.en" exit=0 stdout=block -->
```ts
show(&Expr.Add { left: num(2), right: new Box(Expr.Mul { left: num(3), right: num(4) }) });
show(&Expr.Div { left: num(1), right: num(0) });

private enum Expr {
  Num { value: i64 },
  Add { left: Box<Expr>, right: Box<Expr> },
  Mul { left: Box<Expr>, right: Box<Expr> },
  Div { left: Box<Expr>, right: Box<Expr> },
}

private function num(n: i64): Box<Expr> { return new Box(Expr.Num { value: n }); }

private function eval(e: &Expr): Result<i64> {
  return match (e) {
    Expr.Num => Ok(e.value),
    Expr.Add => Ok(eval(&e.left)? + eval(&e.right)?),
    Expr.Mul => Ok(eval(&e.left)? * eval(&e.right)?),
    Expr.Div => {
      const d = eval(&e.right)?;
      if (d == 0) { return Err("division by zero"); }
      return Ok(eval(&e.left)? / d);
    },
  };
}

private function show(e: &Expr): void {
  const r = eval(e);
  match (r) {
    Ok => console.log(`= ${r.value}`),
    Err => console.log(`error: ${r.error}`),
  }
}
```

Stdout:

```text
= 14
error: division by zero
```

### S4 Interfaces, generics, closures

<!-- case: S4 files=s04.en cmd="enrang run s04.en" exit=0 stdout=block -->
```ts
report(&new Circle(2.0));
report(&new Rect(2.0, 3.5));

const xs: i64[] = [1, 2, 3, 4];
const squares = xs.map(x => x * x);
console.log(squares.join(", "));

let sum: i64 = 0;
xs.forEach(x => { sum += x; });
console.log(sum);

const big = xs.find(x => x > 2);
if (big != null) { console.log(big); }

private interface Shape {
  area(): f64;
  name(): readonly &string;
}

private class Circle implements Shape {
  public constructor(public r: f64) {}
  public area(): f64 { return 3.0 * this.r * this.r; }
  public name(): &string { return "circle"; }
}

private class Rect {  // satisfies Shape structurally
  public constructor(public w: f64, public h: f64) {}
  public area(): f64 { return this.w * this.h; }
  public name(): &string { return "rect"; }
}

private function report<T extends Shape>(s: &T): void { console.log(`${s.name()}: ${s.area()}`); }
```

Stdout:

```text
circle: 12
rect: 7
1, 4, 9, 16
10
3
```

### S5 Strings and arrays

<!-- case: S5 files=s05.en cmd="enrang run s05.en" exit=0 stdout=block -->
```ts
const text = "the quick brown fox jumps over the lazy dog";
const words = text.split(" ");
console.log(words.length(), text.length());
console.log(text.slice(4, 9));

let longest = &words[0];
for (const w of &words) {
  if (w.length() > longest.length()) { longest = w; }
}
console.log(longest);

let out = "";
for (let i = words.length() - 1; i >= 0; i--) {
  out += words[i];
  if (i > 0) { out += " "; }
}
console.log(out);

let nums: i64[] = [5, 3, 9, 1];
nums.sort();
console.log(nums.join(" "));
for (const n of &nums) { *n *= 2; }
console.log(nums.reduce(0, (acc, n) => acc + n));
```

Stdout:

```text
9 43
quick
quick
dog lazy the over jumps fox brown quick the
1 3 5 9
36
```

### S6 Generic linked stack, narrowing, `?.`, `??`, `!`

<!-- case: S6 files=s06.en cmd="enrang run s06.en" exit=0 stdout=block -->
```ts
let names = new Stack<string>();
names.push("Ann");
names.push("Bo");

const top = names.peek();  // shared loan, live until its last use
if (top != null) { console.log(`top ${top}`); }

names.push("Cy");  // exclusive borrow is fine now
console.log(names.pop() ?? "empty");
console.log(names.pop()!);
console.log(names.pop() ?? "empty");
console.log(names.pop() ?? "empty");

private class Node<T> {
  public value: T;
  public next: Box<Node<T>> | null;
}

private class Stack<T> {
  private head: Box<Node<T>> | null = null;

  public push(value: T): void {
    const next = this.head.take();
    this.head = new Box(new Node { value, next });
  }

  public pop(): T | null {
    const boxed = this.head.take()?;
    const node = boxed.unbox();
    this.head = node.next;  // partial move from an owned local
    return node.value;
  }

  public peek(): &T | null { return this.head?.value; }
}
```

Stdout:

```text
top Bo
Cy
Bo
Ann
empty
```

### S7 `Result` and `?` among top-level statements

A failed `?` among the top-level statements prints the error to stderr and ends the program with exit status 1.

<!-- case: S7 files=s07.en cmd="enrang run s07.en" exit=1 stdout=block stderr=inline -->
```ts
console.log(sumAges("20", "22")?);
const r = sumAges("x", "1");
match (r) {
  Ok => console.log(r.value),
  Err => console.log(`caught: ${r.error}`),
}
sumAges("1", "-1")?;
console.log("not reached");

private function parseAge(s: &string): Result<i64> {
  const n = s.parseInt();
  if (n == null) { return Err(`not a number: ${s}`); }
  if (n < 0) { return Err("negative age"); }
  return n;
}

private function sumAges(a: &string, b: &string): Result<i64> {
  return parseAge(a)? + parseAge(b)?;
}
```

Stdout:

```text
42
caught: not a number: x
```

Stderr: `error: negative age`. Exit status 1.

### S8 Checked arithmetic and bounds

This program has no top-level statements, so `main` is its entry point, and the panic stack names that frame.

<!-- case: S8 files=s08.en cmd="enrang run s08.en" exit=101 stdout=block stderr=block -->
```ts
private function main(): void {
  const xs: i32[] = [1, 2, 3];
  console.log(xs[1]);
  console.log(i32.MAX.wrappingAdd(1));
  console.log((200 as u8).checkedAdd(100) ?? 0);
  const i: isize = 3;
  console.log(xs[i]);
  console.log("not reached");
}
```

File name `s08.en`. Stdout:

```text
2
-2147483648
0
```

Stderr, exit status 101:

```text
panic: index 3 is out of bounds for length 3
  --> s08.en:7:15
stack:
  main (s08.en:7:15)
```

### S9 Freestanding kernel

`enrang build --target=i386-none --cpu=i386 --image=floppy kernel.en` produces a 1,474,560-byte image that boots on any listed CPU with a legacy BIOS. No allocator, no floats. The expected output is the bytes on COM1 (this kernel's "stdout"); the same text appears on the VGA text screen.

<!-- case: S9 files=kernel.en cmd="enrang build --target=i386-none --cpu=i386 --image=floppy kernel.en" exit=0 serial=block -->
```ts
import { serial, vga } from "os";

@section(".bss.counters") private unsafe let bootCount: u32;

private function writeU32(boot: &BootInfo, value: u32): void {
  let digits: u8[10] = [0; 10];
  let n: isize = 0;
  let v = value;
  do {
    digits[n] = 48 + (v % 10).wrap<u8>();
    v /= 10;
    n += 1;
  } while (v != 0);
  while (n > 0) {
    n -= 1;
    serial.writeByte(boot, digits[n]);
  }
}

@entry private function kmain(boot: &BootInfo): never {
  serial.init(boot);
  let screen = vga.Screen.fromBoot(boot);
  screen.clear();
  screen.write("Hello from Enrang\n");
  serial.write(boot, "Hello from Enrang\n");

  unsafe { bootCount += 1; }

  let sum: u32 = 0;
  for (let i: u32 = 1; i <= 100; i++) { sum += i; }

  serial.write(boot, "sum = ");
  writeU32(boot, sum);
  serial.write(boot, "\nboots = ");
  unsafe { writeU32(boot, bootCount); }
  serial.write(boot, "\n");
  halt();
}

@panicHandler private function onPanic(info: &PanicInfo): never {
  vga.emergency("panic: ");
  vga.emergency(info.message());
  halt();
}
```

COM1:

```text
Hello from Enrang
sum = 5050
boots = 1
```

### S10 Integrated test file

`src/math.en`:

<!-- case: S10 files=src/math.en,src/math.test.en cmd="enrang test --ci src/math.test.en" exit=0 stdout=block -->
```ts
console.log(gcd(84, 36));

public function gcd(a: i64, b: i64): i64 { return b == 0 ? a : gcd(b, a % b); }
```

`src/math.test.en`:

```ts
describe("gcd", () => {
  test("common factor", () => { expect(gcd(84, 36)).toBe(12); });

  test("zero", () => { expect(gcd(7, 0)).toBe(7); });

  compileFails(
    "rejects mixed widths",
    raw`
    private function f(a: i32, b: i64): i64 { return a + b; } //~ EN0402
  `,
  );
});
```

`enrang test src/math.test.en`, stdout, exit status 0 (no timings under `--ci`, the mode golden tests use):

```text
PASS src/math.test.en
  gcd > common factor
  gcd > zero
  gcd > rejects mixed widths

Tests  3 passed, 3 total
```

`enrang run src/math.en`, stdout: `12`. The test file is a part of module `src/math.en`, so it sees the ordinary function `gcd`; `enrang test` never runs the top-level statements of `src/math.en`.

### S11 Array spread and a worklist that grows

A `for...of` loop borrows or takes its source for the whole loop, so the loop that pushes to `queue` walks a copy, `[...queue]`. The last loop pushes to the array it reads, so it is an index loop, which reads `work.length()` again on every turn; it ends because each value it pushes is smaller than the one it read.

<!-- case: S11 files=s11.en cmd="enrang run s11.en" exit=0 stdout=block -->
```ts
const a: i64[] = [1, 2];
const f: i64[2] = [7, 8];
const b = [0, ...a, 3, ...f];
console.log(b.join(" "));

let queue = ["a", "b"];
let turns = 0;
for (const job of [...queue]) {
  queue.push("retry");
  turns += 1;
}
console.log(turns, queue.length());

const names = ["x"];
let copy = [...names];
copy[0] += "y";
console.log(names[0], copy[0]);

let work: i64[] = [3];
let sum: i64 = 0;
for (let i = 0; i < work.length(); i++) {
  const v = work[i];
  sum += v;
  if (v > 1) {
    work.push(v - 1);
    work.push(v - 2);
  }
}
console.log(sum, work.join(" "));
```

Stdout:

```text
0 1 2 3 7 8
2 4
x xy
7 3 2 1 1 0
```

## 16. Deferred features

Each item produces its own diagnostic, never a miscompile. Format: `error[EN10xx]: <message> is not supported yet`, one `= note:` with the reason, and one `help:` where a workaround exists. Text below is the normative message head and help.

| Code | Feature seen | Message | Help |
|---|---|---|---|
| EN1001 | `async`, `await`, `Promise` | async functions are not supported yet | Run blocking; threads and an event loop come later |
| EN1002 | `function*`, `yield` | generators are not supported yet | Return an array, or keep state in a class |
| EN1003 | threads, `Worker`, `spawn` | threads are not supported yet | `Atomic` exists only for interrupt sharing |
| EN1004 | `Rc`, `Arc`, `Cell`, `RefCell` | shared ownership types are not supported yet | Own the value in one place and pass `&T`, or use an arena with integer handles |
| EN1005 | `'a` | named lifetimes are not supported yet | Write no lifetime: a class may hold a `private` `&` field, and a returned reference's sources come from the function body |
| EN1006 | an interface by value outside a parameter: `Shape[]`, `const s: Shape`, a `Shape` field or result, a type argument that is an interface, as in `mem.swap(&*a, &*b)` with `a: Box<Shape>`; `Box<I>` of an interface with a member that takes or returns `Self` by value, as `Box<Clone>`, or that is compiled once per type, as `Box<Dumper>` with `dump<T>(x: &T)`, and an `&I` of one wherever it needs the two-word form, an argument of a call whose callee is chosen at run time and a parameter of a function converted to an `fn` value or a closure parameter included (4.4); a function with a by-value interface parameter as an `fn` value or a closure parameter (4.5); a by-value interface argument whose branches may have different classes, as `relay(c ? new Dog {} : new Robot {})`; `Result<T, Error>` | an interface type by value outside a parameter is not supported yet: one head for every case listed, whose note names the case, as `` this `Speaker` may be a `Dog` or a `Robot`, so its class isn't known `` does for a branch argument | `&Shape` to refer to one, `Box<Shape>` to own one; for errors, `Result<T>`, because `Error` is a family of types, not a type; for a branch argument, call the function in each branch, as `help: call relay in each branch` says |
| EN1007 | capturing arrow where `fn` is needed, as in a field or a return | a function pointer cannot capture variables | Keep it in a local or pass it as a closure parameter, or pass the data explicitly |
| EN1009 | `export default`, a default import, `require` | this module form is not supported yet | Use `import { name } from "./file"` |
| EN1010 | `= default` in a pattern, at any depth | defaults in patterns are not supported yet | Apply a default with `??` after destructuring |
| EN1011 | `&xs[a..b]`, `str` | range indexing is not supported yet | `xs.slice(a, b)` gives a `&Slice<T>`; `s.slice(a, b)` a read-only `&string` part |
| EN1012 | `Map`, `Set` | `Map` and `Set` are not supported yet | Use a sorted `T[]` |
| EN1013 | `...` outside an array-literal element | rest, and spread outside an array literal, are not supported yet | Pass an array; `[...a]` copies one |
| EN1014 | associated types, const generics, specialisation | this generic feature is not supported yet | |
| EN1015 | `for...in`; `for...of` over a user type, over `string`, or by move over `T[N]` of non-Copy | this `for...of` source is not supported yet | Expose an array, or a `get(i)` and `length()`; `byteAt` for `string`; a `T[]` for owned non-Copy elements |
| EN1017 | `set p(v)` | setters are not supported yet | Write a method |
| EN1018 | operator methods | operator overloading is not supported yet | Write a named method |
| EN1019 | the type name `char` | a character type is not supported yet | `s.codePointAt(i)`, `s.byteAt(i)` |
| EN1021 | `static x = ...` field | static fields are not supported yet | Use a top-level `const` or `unsafe let` |
| EN1022 | `a ** b` | the `**` operator is not supported yet | `a.pow(b)` |
| EN1023 | `keyof`, mapped, conditional types | type-level computation is not supported yet | |
| EN1024 | `A & B` outside a bound | intersection types are not supported yet | Use it in `T extends A & B` |
| EN1025 | `/re/` | regular expressions are not supported yet | `indexOf`, `split` |
| EN1026 | `Math.x(...)` | `Math` does not exist | `x.sqrt()`, `f64.PI`, `a.max(b)` |
| EN1027 | `JSON` | `JSON` is not supported yet | |
| EN1028 | `fetch`, sockets | network APIs are not supported yet | |
| EN1029 | `Object.keys`, reflection | reflection is not supported yet | |
| EN1030 | `@abi("cdecl")`, struct by value in FFI | this foreign ABI is not supported yet | Use scalars and pointers |
| EN1031 | `--target=i386-windows` | 32-bit Windows output is not supported yet | `x86_64-windows`; `i386-linux` for 32-bit testing |
| EN1032 | function call in a `const` initialiser | compile-time function calls are not supported yet | Use a literal expression, or initialise at startup |
| EN1033 | `union`, `transmute` | unchecked reinterpretation is not supported yet | `toBits`, `wrap`, raw-pointer casts in `unsafe` |
| EN1034 | `--debug-info=dwarf` | DWARF output is not supported yet | `--symbols` plus stack traces |
| EN1035 | `function` inside a function body | nested functions are not supported yet | Move it to the top level, or store an arrow in a local |
| EN1036 | `<T>(x: T) => x` | generic arrows are not supported yet | Use a generic `function` |
| EN1037 | class expression, anonymous class | class expressions are not supported yet | Declare a class |
| EN1038 | label on a block | labelled blocks are not supported yet | Label a loop |
| EN1039 | `x as const` | `as const` is not supported yet | `const` is already deep |
| EN1041 | `--multiboot`, `--coverage` | this flag is not supported yet | Boot through `--image`; the VM counts blocks internally but reports no coverage yet |
| EN1042 | `const [a, b] = xs` or `[a, b] = xs` with `xs: T[]` or `T[N]`, at any depth of a pattern | array destructuring is not supported yet | Index the array, or return a tuple |

**Also out of the prototype, with no syntax to reject.** MMX, 3DNow! and SSE1-only code generation; auto-vectorisation; PIE; hot reload in production binaries; DWARF unwinding. Named lifetimes remain a compatible future: R3 becomes elision, so today's programs keep their meaning.

**Kept as proposals.** These are rejected today and may be added later: `@growing for (...)`, a `for...of` that may push to its source, with `x` a copy and references into the array still blocked across a push (today, write an index loop); arrows that copy what they use, so that one can be stored in a field or returned (EN1007 today); unions of any types: `string | int` (EN0406), unions of object types (EN0215) and `typeof` (EN0211). Three more can be added without breaking a program that compiles now: named arguments at calls, `greet("Cy", end: "?")`; `asm` registers chosen by the compiler, Rust's `in(reg)`; a `move x` that ends a copyable variable (EN0228 today). Whether an `@interrupt` handler may write its frame is decided with the kernel work of M9; until then its parameters are read-only.

**Compiler commands outside the prototype** are EN1301: `install`, `add`, `publish`, `doc`, `lsp`, `repl`, `bench`, `debug`, `upgrade`.
