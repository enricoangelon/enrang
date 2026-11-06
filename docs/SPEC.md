# Enrang Language Reference (prototype edition)

Language: Enrang. CLI: `enrang`. Source extension: `.en`. Source encoding: UTF-8.

This document is normative for the parser, type checker, borrow checker, library surface and golden diagnostics. "Must" and "is" are requirements; anything not listed as in scope produces a diagnostic from section 16 and never a miscompile. Implementation structure (LIR, encoder tables, VM internals, boot-sector layout) belongs to the architecture document; only what programmers can observe is fixed here.

The compiler and `enrang dev` run only on a modern x86-64 development machine and cross-compile. Only their output runs on old chips. "Enrang" in this document always means the language; statements about CPUs concern emitted programs.

## 0. Thesis and decisions

**Thesis.** TypeScript syntax, Rust semantics, no lifetime type system. References live only in stack-frame slots (locals, parameters, temporaries, return values), never inside data. That single restriction removes lifetime syntax, region inference, variance and drop check, while leaving a flow-sensitive MIR borrow check that accepts everything NLL accepts within the restriction, plus NLL problem case #3.

| # | Question | Decision |
|---|---|---|
| 1 | Bindings | `const` is deeply immutable, `let` is mutable; `const xs = []; xs.push(1)` gets a one-token fix-it and a TS note |
| 2 | Ownership surface | Sigils `&T`, `&mut T`; bare `T` moves. Shared borrow is implicit at call sites, exclusive is explicit (`f(&mut x)`), receivers are automatic |
| 3 | Lifetimes | No syntax. Frame-bound references (rule R1), returns allowed by signature rule R3 with optional `from` clause; never in fields, elements or generic arguments |
| 4 | Copy | Scalars, `&T`, raw and function pointers, payload-free enums, fixed arrays and `T \| null` of Copy; classes opt in with `implements Copy`; `.clone()` synthesised memberwise |
| 5 | Data types | `class` is a nominal inline value type with `constructor`, `new`, methods; no inheritance. Receivers: `m()` shared, `mut m()` exclusive, `own m()` consuming |
| 6 | Interfaces | Structural with optional checked `implements` and one exact satisfaction rule (4.4), static dispatch only via `T extends A & B`; `Copy`, `Drop` and the sealed `core` bounds are nominal |
| 7 | Sums and null | Nominal `enum` with payloads, exhaustive `match`, `T \| null` as non-flattening built-in option, path narrowing, `?.`, `??`, `x!` |
| 8 | Errors | `Result<T, E>`, postfix `?` with no conversion, unused `Result` is an error, panic aborts, bounds and overflow are always checked |
| 9 | Numbers | `number` = `f64`, `int` = `i64`, explicit widths plus target-width `isize`/`usize`; literals infer across the function, default `i64`/`f64`; `.length` is `isize` |
| 10 | Strings | One type `string`: owned UTF-8 `{ptr,len,cap}`; literals have `cap == 0`; `+` allocates; `slice` copies; no `str` |
| 11 | Arrays | `T[]` owned and growable, `T[N]` inline; indexing is a checked place and never moves; `for...of` over a path re-reads its source every turn, so items added in the body get turns (warning EN0719); `[...a]` builds a new `T[]` by cloning; owned iteration over `T[N]` needs Copy elements |
| 12 | Generics | Monomorphised, checked once before instantiation, `T` ranges over reference-free types, local inference |
| 13 | Closures | Second-class arrows: arguments to function-typed parameters only, captures are loans for the call, and a closure value is an exclusive reborrow. `fn` pointers are first-class but non-capturing |
| 14 | Destructors | `implements Drop` with `mut drop()`; reverse-declaration locals, user drop then fields, partial moves unless `Drop` |
| 15 | Modules | Multi-file relative `import`/`export`, no cycles, whole-program compile, `core`/`alloc`/`os` by bare name; library child modules import as namespaces |
| 16 | FFI and unsafe | `unsafe` blocks with exactly five powers; `@dll` plus `declare function` on Windows; ABI-tagged and `unsafe fn` pointers; no libc FFI |
| 17 | Deferred | Section 16, each with a named diagnostic |

## 1. Language tour

The three programs in this section are extracted cases, like those of sections 14 and 15. Section 14 defines the `case` markers.

<!-- case: tour files=tour.en cmd="enrang run tour.en" exit=0 stdout=inline -->
```ts
// tour.en: run with `enrang run tour.en`
enum Op { Push(i64), Add, Mul, Print }

class Stack<T> {
  private items: T[] = [];

  mut push(x: T): void { this.items.push(x); }    // `x` moves in; mut = exclusive `this`
  mut pop(): T | null { return this.items.pop(); }
  top(): &T | null { return this.items.last(); }  // reference borrows from `this` (R3)
  get size(): isize { return this.items.length; }
}

class Trace implements Drop {
  constructor(public name: string) {}
  mut drop(): void { console.log(`[${this.name}] done`); }
}

function pop2(s: &mut Stack<i64>): Result<i64, string> {
  const v = s.pop();
  if (v == null) { return Err("stack underflow"); }
  return Ok(v);                                   // narrowed to i64
}

function run(program: &Op[]): Result<i64, string> {
  const _trace = new Trace("vm");                 // dropped on every exit, `?` included
  let s = new Stack<i64>();
  for (const op of program) {                     // op: &Op
    match (op) {                                  // place scrutinee: payloads borrowed
      Op.Push(v) => s.push(v),                    // &i64 reads through because i64 is Copy
      Op.Add => { const b = pop2(&mut s)?; const a = pop2(&mut s)?; s.push(a + b); },
      Op.Mul => { const b = pop2(&mut s)?; const a = pop2(&mut s)?; s.push(a * b); },
      Op.Print => {
        const t = s.top();
        if (t != null) { console.log(`top = ${t}`); }  // last use: the loan ends here
      },
    }
  }
  return pop2(&mut s);
}

function main(): void {
  const prog = [Op.Push(2), Op.Push(40), Op.Add, Op.Print];
  match (run(prog)) {                             // `prog` auto-borrowed; result is owned
    Ok(v) => console.log(`result ${v}`),
    Err(e) => console.log(`error: ${e}`),
  }
}
```

Output: `top = 42`, `[vm] done`, `result 42`.

**Ownership in three lines.** `T` hands a value over; `&T` lends it for reading; `&mut T` lends it exclusively. `f(x)` lends automatically when the parameter is `&T`; `f(&mut x)` announces mutation; neither changes what the machine does beyond passing a pointer.

<!-- case: ownership files=ownership.en cmd="enrang check ownership.en" exit=0 -->
```ts
function total(xs: &i64[]): i64 { let t = 0; for (const x of xs) { t += x; } return t; }
function bump(xs: &mut i64[]): void { for (const x of xs) { *x += 1; } }
function keep(xs: i64[]): i64[] { return xs; }

function main(): void {
  let a = [1, 2, 3];
  total(a);            // lent
  bump(&mut a);        // lent exclusively, visible at the call
  const b = keep(a);   // moved; using `a` now is EN0601
}
```

**TS habits that survive.** Template literals, `class`, `new`, `implements`, `T extends A & B`, `T | null`, `?.`, `??`, `x!`, arrow functions in `map`, `for...of` that sees pushes, array spread `[...a]`, `import { a } from "./b"`, `describe`/`test`/`expect`.

**TS habits the compiler redirects.** `===` to `==`, `var` to `let`, `any` to a generic, `undefined` to `null`, `throw` to `Err`, `switch` to `match`, `extends` on classes to composition, truthiness to explicit comparison. Section 13 lists all of them.

**A kernel in the same language.**

<!-- case: tour-kernel files=hello.en cmd="enrang build --target=i386-none --image=hdd hello.en" exit=0 -->
```ts
// hello.en: enrang build --target=i386-none --image=hdd hello.en
import { vga, serial } from "os";

@entry function kmain(boot: &BootInfo): never {
  serial.init(boot);
  let screen = vga.Screen.fromBoot(boot);
  screen.write("Hello from Enrang\n");
  serial.write(boot, "Hello from Enrang\n");
  halt();
}

@panicHandler function onPanic(info: &PanicInfo): never {
  vga.emergency(info.message);
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
Keyword      = "as" | "asm" | "break" | "class" | "const" | "constructor" | "continue"
             | "declare" | "do" | "else" | "enum" | "export" | "false" | "fn" | "for"
             | "function" | "if" | "implements" | "import" | "interface" | "let" | "match"
             | "move" | "mut" | "never" | "new" | "null" | "private" | "public" | "readonly"
             | "return" | "static" | "this" | "true" | "type" | "unsafe" | "void" | "while" ;
Contextual   = "describe" | "test" | "expect" | "compileFails" | "compileOk" | "raw"
             | "extends" | "from" | "get" | "of" | "own" | "not" | "in" | "out" | "clobbers"
             | "assert" | "extend" | "where" ;
             (* identifiers everywhere except the one grammar position that names them *)
Reserved     = "any" | "await" | "async" | "case" | "catch" | "default" | "delete" | "finally"
             | "instanceof" | "keyof" | "namespace" | "switch" | "throw" | "try" | "typeof"
             | "undefined" | "unknown" | "using" | "var" | "yield" | "abstract" | "super"
             | "protected" ;                  (* lexed as keywords; each has a section 13 or 16 hint *)

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
- Every token records `spaceBefore: bool`. **Postfix `?` and `!` must have `spaceBefore == false`; ternary `?` must have `spaceBefore == true`.** `a ? b : c` is a ternary, `a? b : c` is EN0103 with a fix-it, `f()?` propagates, `f() ?` is EN0103.
- `!` after an expression with `spaceBefore == false` is the postfix null assertion; `!=` is munched first, so `x! = y` needs the space shown.
- No automatic semicolon insertion. A missing `;` is EN0101, whose fix-it inserts it; the parser recovers at the next line start as if it were present, so a TS file with no semicolons gets one diagnostic per file rather than one per statement. That diagnostic is the first site; it adds ``= note: N more statements in this file are missing `;` `` and its fix-it carries every insertion.
- An unclosed `{` at end of file is EN0102. The parser compares each matched `}` with the indentation of the line holding its `{`. The first mismatch gives the primary span (that `{`) and the secondary span (that `}`), and the fix-it inserts a `}` at the `{` line's indentation before the `}` line. If nothing mismatches, the innermost open `{` is primary and the insertion goes at end of file.

## 3. Syntax grammar

Notation: `[x]` optional, `{x}` zero or more, `A % ","` means `[A {"," A} [","]]` (comma list, trailing comma allowed).

### 3.1 Files and items

```ebnf
File        = { Import } { Item } ;
Import      = "import" "{" ImportName % "," "}" "from" StringLit ";" ;
ImportName  = Ident [ "as" Ident ] ;
             (* path "./x", "../x" relative, extension omitted; "core", "core/...", "alloc",
                "alloc/...", "os", "os/..." name embedded library modules; binding rule in 4.12 *)

Item        = { Decorator } [ "export" ] ItemKind | TestItem | TopAssert ;
Decorator   = "@" Ident [ "(" DecoratorArg % "," ")" ] ;
DecoratorArg= Literal | ObjectLit | Ident ;
ItemKind    = FunctionDecl | ClassDecl | EnumDecl | InterfaceDecl | TypeAlias | TopConst
            | TopLet | DeclareFn | ExtendDecl ;
MemberName  = Ident | Keyword | Reserved ;     (* the position decides: `node.type`, `Point { type: 1 }` *)

FunctionDecl= [ "unsafe" ] "function" Ident [ TypeParams ] "(" Param % "," ")"
              [ ":" RetType ] Block ;
             (* library modules may use MemberName as the name; such a function is reachable
                only through a namespace: `ptr.null<T>()` *)
DeclareFn   = "declare" "function" Ident [ TypeParams ] "(" Param % "," ")" [ ":" Type ] ";" ;
Param       = [ "mut" ] Ident ":" ParamType ;
ParamType   = Type | ClosureType ;
RetType     = Type [ "from" Ident { "|" Ident } ] ;     (* Ident may be `this` *)
TypeParams  = "<" TypeParam % "," ">" ;
TypeParam   = Ident [ "extends" Bound { "&" Bound } ] ;
Bound       = NamedType ;

TopConst    = "const" Ident [ ":" Type ] "=" ConstExpr ";" ;
TopLet      = [ "unsafe" ] "let" Ident ":" Type [ "=" ConstExpr ] ";" ;
             (* "unsafe" exactly when decorated @globalAllocator: EN0825 otherwise *)
TopAssert   = "assert" "(" ConstExpr [ "," StringLit ] ")" ";" ;
ConstExpr   = Expr ;   (* restricted, section 4.9 *)

ClassDecl   = "class" Ident [ TypeParams ] [ "implements" NamedType { "," NamedType } ]
              "{" { ClassMember } "}" ;
ClassMember = { Decorator } ( FieldDecl | Constructor | MethodDecl | GetterDecl ) ;
FieldDecl   = [ Visibility ] [ "readonly" ] MemberName ":" Type [ "=" Expr ] ";" ;
Visibility  = "public" | "private" ;
Constructor = "constructor" "(" CtorParam % "," ")" Block ;
CtorParam   = [ Visibility ] [ "readonly" ] [ "mut" ] Ident ":" Type ;
MethodDecl  = [ Visibility ] [ "static" | "mut" | "own" ] [ "unsafe" ] MemberName [ TypeParams ]
              "(" Param % "," ")" [ ":" RetType ] [ WhereClause ] Block ;
GetterDecl  = [ Visibility ] "get" MemberName "(" ")" ":" RetType Block ;
WhereClause = "where" WherePred { "," WherePred } ;
WherePred   = Ident "extends" Bound { "&" Bound } ;  (* Ident names a parameter of the enclosing class *)

EnumDecl    = "enum" Ident [ TypeParams ] "{" Variant % "," [ ";" { MethodDecl | GetterDecl } ] "}" ;
Variant     = { Decorator } Ident [ "(" Type % "," ")" | "{" EnumField % "," "}" | "=" ConstExpr ] ;
EnumField   = MemberName ":" Type ;

InterfaceDecl = "interface" Ident [ TypeParams ] "{" { IfaceMember } "}" ;
IfaceMember = [ "static" | "mut" | "own" ] [ "unsafe" ] MemberName [ TypeParams ] "(" Param % "," ")"
              [ ":" RetType ] [ WhereClause ] ";"
            | "get" MemberName "(" ")" ":" RetType ";" ;
TypeAlias   = "type" Ident [ TypeParams ] "=" Type ";" ;
ExtendDecl  = "extend" [ TypeParams ] Type "{" { { Decorator } ( MethodDecl | GetterDecl ) } "}" ;
             (* library only, see below *)
```

A `where` clause adds bounds to a class type parameter for one method. The body is checked with the extended bounds. A call is checked after inference and reports EN0419, with the method's bound as the secondary span: `sort() where T extends Ord`. The bounds are part of the signature. `where` is legal in user code too.

Allowed decorators are fixed; anything else is EN0806. Their targets are checked:

| Decorator | Target | Section |
|---|---|---|
| `@entry` | function | 7.8 |
| `@panicHandler` | function | 7.9 |
| `@globalAllocator` | top-level `unsafe let` | 7.9 |
| `@interrupt`, `@interrupt({ errorCode: true })` | function | 7.7 |
| `@naked`, `@bits(16\|32\|64)` | `unsafe function` | 7.5 |
| `@requires("feature", ...)` | function, method | 10.3 |
| `@section("name")` | function, top-level `let`, `const` | 7.8 |
| `@at(address)` | top-level `let` | 7.8 |
| `@packed`, `@repr("C"\|"u8"\|"u16"\|"u32")`, `@align(n)` | class, enum, `@align` also top-level `let` | 7.6 |
| `@dll("name")` | `declare function` | 7.10 |
| `@abi("win64"\|"sysv")` | function, function pointer type | 7.10 |
| `@lang("name")` | `core`, `alloc` and `os` modules only | below |
| `@intrinsic("Kind")` | `declare function` or a bodyless `extend` member in `core`, `alloc`, `os` | below |
| `@hostCall("name")` | `declare function` in `os/vm` only | below |
| `@was("oldName")` | class, enum, field, variant, function; inert outside `dev` | 8.5 |
| `@devMigrate` | function with an object-typed parameter; stripped outside `dev` | 8.5 |
| `@owner` | `alloc` only | 8.5 |

**Library-only forms** (`core`, `alloc`, `os`; EN0806 anywhere else). The library needs these three, and they are the whole of the mechanism behind built-in types:

- **`extend`** declares members on a type that has no class body of its own, or that lives in another layer: `extend<T> T[] { mut push(x: T): void {...} static withCapacity(n: isize): T[] {...} }`, `extend<T> T | null {...}`, `extend<T> *mut T {...}`, `extend<I extends __Int> I { @intrinsic wrappingAdd(o: I): I; }`. A member marked `@intrinsic` has `;` in place of its body, and `static` may precede `get` (`@intrinsic static get MAX(): I;`). An `extend` body sees the private fields of the type it extends. Member lookup and interface satisfaction both read `extend` members, so `i64` satisfies `Ord`.
- **`@lang`** registers an item the compiler names. `string` is an `@lang("string")` class in `core/string`; `T[]` and `Box<T>` are `@lang("array")` and `@lang("box")` classes in `alloc`. They are real classes with fields private to the library. `string`, `T[]` and `Box<T>` remain their only spellings.
- **`@intrinsic("MemCopy") declare function memCopy<T>(d: *mut T, s: *T, n: usize): void;`** binds a name to a compiler intrinsic. **`@hostCall("fs.open") declare function ...`** binds a VM host call. Both are exempt from EN0815 and always `unsafe` to call, so safe library wrappers sit on top of them. A bodyless `extend` member takes its safety from its own declaration: `wrappingAdd` is safe, `readVolatile` is `unsafe`.

### 3.2 Types

```ebnf
Type        = NullableType ;
NullableType= PrefixType [ "|" "null" ] ;      (* any other `|` is EN0406 *)
PrefixType  = "&" [ "mut" ] PrefixType | "*" [ "mut" ] PrefixType | PostfixType ;
PostfixType = PrimaryType { "[" [ ConstExpr ] "]" } ;
PrimaryType = NamedType | "(" Type ")" | FnPtrType | "void" | "never" | "null"
            | ObjectType ;                     (* ObjectType only under @devMigrate: else EN0407 *)
NamedType   = Ident { "." Ident } [ "<" Type % "," ">" ] ;
FnPtrType   = { Decorator } [ "unsafe" ] "fn" "(" TypedParam % "," ")" "=>" RetType ;
ClosureType = "(" TypedParam % "," ")" "=>" Type ;  (* parameter position only: else EN0705 *)
TypedParam  = Ident ":" Type ;                 (* a closure type here is EN0705: closures do not nest *)
ObjectType  = "{" ( Ident ":" Type ) % "," "}" ;
```

`&T[]` is `&(T[])`. `&T | null` is `(&T) | null`. `T[3][4]` reads left to right: an array of 4 elements of `T[3]`. `*u8` is a read-only raw pointer, `*mut u8` a writable one. `unsafe fn(...) => R` is a function pointer whose call is power 2 of section 5.9. Parameter names in function pointer and closure types exist only so `from` can name them; identity compares by position.

### 3.3 Statements

```ebnf
Block       = "{" { Stmt } "}" ;
Stmt        = VarDecl | IfStmt | WhileStmt | DoStmt | ForStmt | ForOfStmt | ReturnStmt
            | BreakStmt | ContinueStmt | Block | UnsafeBlock | LabeledStmt
            | AssignStmt | MatchStmt | ExprStmt | ExpectStmt ;     (* ExpectStmt: section 3.6 *)
MatchStmt   = MatchExpr [ ";" ] ;
VarDecl     = ( "const" | "let" ) Binding [ ":" Type ] [ "=" Expr ] ";" ;
Binding     = Ident | ClassPattern ;           (* destructuring requires "=" Expr *)
IfStmt      = "if" "(" Expr ")" Block [ "else" ( IfStmt | Block ) ] ;
WhileStmt   = "while" "(" Expr ")" Block ;
DoStmt      = "do" Block "while" "(" Expr ")" ";" ;
ForStmt     = "for" "(" [ VarDecl | AssignStmt | ";" ] [ Expr ] ";" [ AssignNoSemi ] ")" Block ;
ForOfStmt   = "for" "(" ( "const" | "let" ) Ident "of" ForSource ")" Block ;
ForSource   = Expr ".." Expr | Expr ;          (* range only here, half-open; classified in 5.6 *)
ReturnStmt  = "return" [ Expr ] ";" ;
BreakStmt   = "break" [ Ident ] ";" ;
ContinueStmt= "continue" [ Ident ] ";" ;
LabeledStmt = Ident ":" ( WhileStmt | DoStmt | ForStmt | ForOfStmt ) ;
UnsafeBlock = "unsafe" Block ;
AssignStmt  = AssignNoSemi ";" ;
AssignNoSemi= Expr AssignOp Expr | Expr "++" | Expr "--" ;
AssignOp    = "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>=" ;
ExprStmt    = Expr ";" ;
```

Braces are mandatory after `if`, `else`, `while` and `for`; `if (x) y();` is EN0104 with a fix-it. Assignment and `++`/`--` are statements, not expressions (EN0105). A `Block` in a body position has no value.

A statement that starts with `match` ends at the closing `}`, plus an optional `;`. No binary or postfix continuation is parsed after it, as in Rust. To use the value, write `const x = match (...) {...};` or `(match (...) {...}).f;`.

`break` or `continue` outside a loop, or crossing an arrow body, is EN0111. An unknown label is EN0112, a label already in scope EN0113, and an assignment target that is not a place (`f() = 1;`) EN0114.

### 3.4 Expressions

```ebnf
Expr        = Ternary ;
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
Unary       = ("!" | "-" | "~" | "*" | "&" [ "mut" ] | "move" | "void") Unary | Postfix ;
Postfix     = Primary { "." MemberName | "?." MemberName
                      | "[" Expr "]" | CallArgs | "?" | "!" } ;
CallArgs    = [ TypeArgs ] "(" Arg % "," ")" ;
Arg         = Expr | ArrowFn ;
TypeArgs    = "<" Type % "," ">" ;   (* expression context: see Disambiguation *)
ArrowFn     = ( Ident | "(" ArrowParam % "," ")" ) [ ":" Type ] "=>" ( Expr | Block ) ;
ArrowParam  = [ "mut" ] Ident [ ":" Type ] ;

Primary     = Literal | Ident | "this" | "(" Expr ")" | ArrayLit | RepeatLit | NewExpr
            | ClassLit | MatchExpr | SizeForm | AsmExpr | TypeMember ;
TypeMember  = NamedType [ "[" "]" ] "." MemberName ;
             (* tried when an identifier is followed by a no-space "<", or by "[" "]":
                Stack<i64>.empty(), i64[].withCapacity(8), E<i64>.V(1) *)
Literal     = IntLit | FloatLit | StringLit | TemplateLit | RawTemplate | "true" | "false" | "null" ;
ArrayLit    = "[" ArrayElem % "," "]" ;
ArrayElem   = Expr | "..." Expr ;              (* spread, section 4.13; "..." appears nowhere else *)
RepeatLit   = "[" Expr ";" ConstExpr "]" ;     (* T[N], element must be Copy *)
NewExpr     = "new" NamedType "(" Arg % "," ")" ;
ClassLit    = NamedPath [ TypeArgs ] "{" ( MemberName [ ":" Expr ] ) % "," "}" ;
             (* also enum struct variants: Op.Bad { text }.  Field shorthand allowed. *)
NamedPath   = Ident { "." Ident } ;
MatchExpr   = "match" "(" Expr ")" "{" MatchArm % "," "}" ;
MatchArm    = Pattern { "|" Pattern } "=>" ( Expr | Block | "return" [ Expr ]
            | "break" [ Ident ] | "continue" [ Ident ] ) ;
SizeForm    = ("sizeOf" | "alignOf") "<" Type ">" "(" ")"
            | "offsetOf" "<" Type ">" "(" StringLit ")" ;

Pattern     = "_" | Ident | Literal | "-" IntLit | "null" | "Ok" "(" Pattern ")" | "Err" "(" Pattern ")"
            | VariantPat | ClassPattern ;
VariantPat  = NamedPath [ "(" Pattern % "," ")" | "{" FieldPat % "," "}" ] ;
ClassPattern= [ NamedPath ] "{" FieldPat % "," "}" ;   (* path optional only in `const { a, b } = p` *)
FieldPat    = MemberName [ ":" Pattern ] ;

AsmExpr     = "asm" "(" ( TemplateLit | StringLit ) [ "," AsmOptions ] ")" ;
AsmOptions  = "{" AsmOption % "," "}" ;        (* each key at most once, in any order *)
AsmOption   = "in" ":" RegMap | "out" ":" RegMap | "clobbers" ":" "[" StringLit % "," "]" ;
RegMap      = "{" ( RegName [ ":" Expr ] ) % "," "}" ;
RegName     = Ident ;     (* physical register; `{ edx }` is `{ edx: edx }` *)

ObjectLit   = "{" ( Ident ":" ObjectValue ) % "," "}" ;   (* decorators and test options only *)
ObjectValue = Literal | "[" Literal % "," "]" ;
```

**Disambiguation.**
- A path followed by `{` on the same line is always tried as `ClassLit`, and a `{` on a later line never is. All conditions are parenthesised, so no production places an expression directly before a block; the only hazard is a missing `;` before a block on the next line. This works for `vec2 { x: 1 }` and `vga.Screen { ... }` alike.
- In expression context, `<` starts type arguments only when it has `spaceBefore == false` and speculation succeeds, and in calls and members the next token must then be `(`, `{` or `.`. After `as`, a no-space `<` also speculates, any next token is accepted, and on failure the parser rewinds and ends the type at the name. In pure type positions spacing is irrelevant, and the AST printer writes no space. So `a < b > (c)` is EN0107, `a<b>(c)` is a call, `f(a < b, c > (d))` has two arguments, `x as usize < n` is a comparison and `x as Box<i32>` is a cast.
- Type arguments always attach to a `Call` or to a `TypeMember`, never to a member access: `x.wrap<u8>()` has one derivation.
- **`...` is consumed in one place only: an `ArrayElem`.** Wherever else an expression, parameter, field, pattern or literal is expected, `...` is EN1013 at that token; the parser skips it and goes on. That covers `f(...a)`, `new C(...a)`, `console.log(...a)`, rest parameters, `(...a) => 1`, `{...o}` (before EN0217 is considered), `Point { ...p }`, `const { a, ...r } = p`, `xs[...i]`, `for (const x of ...a)` and option arrays such as `@d([...a])`. `[a, ...r] = xs` and `const [a, ...r] = xs` are EN1013 at `...`, with no EN1010 and no EN0114; without `...` they stay EN1010. After a complete expression `...` is EN0100, as in `a...b`, with a fix-it to `..` in a `ForSource`. The first token after `[` picks the spread path with no backtracking, so `[...a; 3]` is EN0100 at `;`, and `[...0..n]` is EN0100 at `..`, because a range is not an expression. `TypeMember` needs `[` and `]` adjacent, so it never meets `x[...`.
- `(x) => ...` is an arrow if a `=>` follows the matching `)`; arrows are legal only as direct call arguments (EN0705 elsewhere). The annotated form `(x: number): number => x * 2` is recognised only when `(` is the first token of an `Arg`, which keeps `a ? (b) : c` a ternary.
- A bare identifier in a pattern binds, unless it names a variant of the scrutinee's enum: then EN0502 with a fix-it to the qualified name.
- In a class or interface body, `get`, `own`, `mut` and `static` are modifiers only when followed by a `MemberName`; `get(i): &T` declares a method named `get`.
- At the top level, `test`, `describe`, `compileFails` and `compileOk` followed by `(` or `.` start a test item, and `assert` followed by `(` starts a `TopAssert`. There are no top-level expression statements, so neither can be confused with a call.

### 3.5 Operator precedence

| Prec | Operators | Assoc | Notes |
|---|---|---|---|
| 1 | `.` `?.` `[]` `()` postfix `?` postfix `!` | left | |
| 2 | prefix `!` `-` `~` `*` `&` `&mut` `move` `void` | right | |
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
| 16 | `=>` | | Arguments only |

Assignment is not an operator; it is a statement form.

### 3.6 Test declarations

Legal at the top level of any file, and the only top-level items of a `*.test.en` file besides ordinary items.

```ebnf
TestItem    = DescribeItem | TestDecl | CompileCase ;
DescribeItem= "describe" "(" StringLit "," "(" ")" "=>" "{" { DescribeItem | TestDecl | CompileCase } "}" ")" ";" ;
TestDecl    = "test" [ "." TestMode ] "(" StringLit [ "," TestExtra ] [ "," TestBody ] [ "," ObjectLit ] ")" ";" ;
TestMode    = "only" | "skip" | "todo" | "panics" | "each" ;
TestExtra   = StringLit                        (* test.panics: expected message substring *)
            | "(" ")" "=>" Expr ;              (* test.each: case generator *)
TestBody    = "(" [ ArrowParam ] ")" [ ":" Type ] "=>" Block ;
             (* absent annotation means void; anything but void or Result<void, E> is EN0401 *)
CompileCase = ("compileFails" | "compileOk") "(" StringLit "," RawTemplate [ "," ObjectLit ] ")" ";" ;
ExpectStmt  = "expect" "(" Expr ")" [ "." "not" ] "." Ident "(" MatcherArg % "," ")" ";" ;
MatcherArg  = Arg | Pattern ;                  (* Pattern only for toMatchPattern *)
```

`ExpectStmt` is a statement, not an expression; it is valid only lexically inside a test body or a function declared in a `*.test.en` file. The parser always builds it for `expect(...).ident(...)`, because it cannot resolve names. Sema reinterprets it as a call if `expect` resolves to an item, and otherwise reports EN1101. `const e = expect(x)` is EN1103. Semantics are in section 12.

## 4. Type system

### 4.1 The type grammar that carries soundness

```text
V ::= bool | i8|i16|i32|i64 | u8|u16|u32|u64 | isize|usize | f32|f64 | void | never
    | string | V[] | V[N] | Box<V> | V | null | Result<V,V> | Class<V..> | Enum<V..>
    | *V | *mut V | fn(S..) => S | unsafe fn(S..) => S | T  // T ranges over V only
R ::= &V | &mut V
S ::= V | R | R | null                                      // locals, temporaries, params, returns
F ::= (S..) => V                                            // parameters only; does not nest
```

`V` is closed: no constructor accepts `R` or `F`, with one deliberate exception. A function pointer's signature may mention `S`, because a function pointer holds no reference, so `class C { cb: fn(s: &string) => void; }` is legal. Its `RetSources` are computed by R3 from the pointer type's own `from` clause, and they are part of type identity and of the coercion check. A raw pointer `*V` is in `V` because it carries no loan. `&&T` does not exist (EN0702). A `T` instantiated or inferred as a reference is EN0703, except the read-through rule in 4.5.

### 4.2 Primitive types

| Type | Meaning | Copy |
|---|---|---|
| `bool` | `true`, `false` | yes |
| `i8 i16 i32 i64` | two's complement | yes |
| `u8 u16 u32 u64` | unsigned | yes |
| `isize usize` | signed and unsigned of the target's pointer width: 32 bits on `i386-*`, 64 bits on `x86_64-*` | yes |
| `f32 f64` | IEEE 754 binary32, binary64 | yes |
| `number` | alias of `f64` | yes |
| `int` | alias of `i64` | yes |
| `void` | the one-value unit type; expression `void 0` is not special, `Ok()` means `Ok(void)` | yes |
| `never` | the empty type; coerces to anything | yes |
| `string` | owned UTF-8 text, section 11 | no |

There is no `char`; `s.byteAt(i)` and `s.codePointAt(i)` yield `u8` and `u32`. Target-width types exist so loops on `i386` stay single-register: no program assumes `usize` is 64 bits, and the compiler rejects constants that do not fit the target (`EN0411`), never truncating.

### 4.3 Declared types

- **`class C<T>`**: nominal, inline value type. `new` never implies heap. Fields are public by default; `private` members are visible only inside the class body and its module's `.test.en` part. `readonly` fields may be assigned only by their initialiser or the constructor. No inheritance: `class A extends B` is EN0204.
- **Construction.** Field initialisers run first, in declaration order; then the constructor body, in which `this` is a partially initialised local tracked by init dataflow. Reading `this` as a whole, calling a method or returning before all fields are assigned is EN0610. A class with no constructor has an implicit one with no parameters if every field has an initialiser. `C { a: 1, b }` is an atomic literal: legal where every named and omitted field is visible, omitted fields need initialisers, and it bypasses any constructor.
- **Parameter properties.** `constructor(public x: T, private y: U)` declare and assign fields.
- **Receivers.** `m()` is `&this`; `mut m()` is `&mut this`; `own m()` takes `this` by value; `static m()` has none. `get p(): T` is `&this` and is read without parentheses. `this` is a keyword, never rebindable.
- **`enum E<T>`**: nominal tagged sum. Variants: unit, positional `V(T, U)`, or named `V { f: T }`. Payload-free enums are Copy and may set integer discriminants (`Red = 1`, consecutive defaults starting at 0). Enums may have methods after a `;`. Variants are always qualified, `E.V`, in both expressions and patterns; only `Ok` and `Err` are bare.
- **Recursion** needs `Box`: `class Node { next: Node | null }` is EN0408 with a fix-it to `Box<Node> | null`.
- **`type A<T> = B;`** is a transparent alias; aliases cannot be recursive.
- **`Box<T>`**, in `alloc`: `new Box(v)` allocates; `b.unbox()` consumes and returns `T`; `*b` and auto-deref on `.` give the place. Moves out of `*b` are EN0605: use `unbox`.
- **Member lookup** is one rule, for `.` and `?.`. Strip one `&` or `&mut` to get `U`. Look up on `U`, own members and `extend` members together. If `U` is `Box<V>` and that misses, repeat on `V`. If `U` is a narrowed nullable, try the payload first and then nullable members; the kill rule of 4.8 applies to what is found. An unnarrowed nullable has only nullable members, and a miss is EN0303 with a `?.` or narrowing fix-it. `?.` looks up on the payload by this same rule and never short-circuits: `a?.b.c` is EN0303 with a `?.c` fix-it, and `a?.b?.c` is legal. The `drop` method of a class that `implements Drop` is never found (4.4).

### 4.4 Interfaces

Structural. A type `C` satisfies `interface I` when, after substituting `Self`, lookup on `C` itself finds, for every member of `I`, a member meeting all of these. Own and `extend` members count; auto-deref never contributes a member, so `Box<C>` does not satisfy what `C` does.

- It is public. A `private` member never satisfies an interface.
- It has the same unsafety: a safe interface member needs a safe method, and an `unsafe` one needs an `unsafe` method.
- It has no `@requires`.
- It has an equal receiver mode and the same kind, method or getter.
- It has equal type parameters and bounds, equal parameter types and an equal return type.
- It has equal normalised `RetSources`, compared by parameter position. R3 computes them from each signature.

This definition is what makes "checked once generically" true: a member the bound promises behaves, for borrowing and safety, exactly as the bound said. The same `RetSources` equality applies when a function coerces to an `fn` type.

`implements I` is an assertion checked at the class, giving a better diagnostic (EN0416) at the declaration rather than at use, which is EN0419. Members are methods and getters only; a field in an interface is EN0417 with a fix-it to `get`.

Interfaces appear only as bounds. `function f(s: Shape)` and `Shape[]` are EN1006 with a fix-it to `<T extends Shape>` or an enum.

Prelude interfaces:

| Interface | Members | Notes |
|---|---|---|
| `Copy` | none | **Nominal.** `implements Copy` requires all fields Copy and no `Drop` (EN0418) |
| `Drop` | `mut drop(): void` | **Nominal.** Excludes `Copy`. The method is never a member, neither for lookup nor for structural satisfaction: `x.drop()` is EN0606, also on `T extends Drop`, which grants nothing callable. Declaring an interface member `mut drop(): void` is EN0606. Use the prelude `drop(x)` |
| `Clone` | `clone(): Self` | Every Copy type in `V` satisfies it by a plain copy, with or without raw pointers, and `T extends Copy` implies `T extends Clone`. `string` and `T[]` have it as listed in 8.3. `T \| null`, `T[N]`, `Result<T, E>` and `Box<T>` satisfy it when their parts do, and `Box` allocates a new block. Any other class or enum has it synthesised memberwise on demand when its fields all satisfy `Clone`, unless it has `Drop` or a raw pointer field. The check is coinductive, so a `Box<Node> \| null` field of `Node` is fine. A class with `Drop` needs a user-written `clone`. A user-written `clone` always wins |
| `Eq` | `equals(other: &Self): bool` | `implements Eq` with no body synthesises memberwise. `==` on a class or payload enum calls it; otherwise EN0421 |
| `Ord` | `compare(other: &Self): i32` | Negative, zero, positive. Used by `sort`; `<` never calls it |
| `Display` | `fmt(f: &mut Formatter): void` | Needed by `${x}`. Primitives and `string` have it in `core` |

**Sealed bounds.** `core` also declares nominal interfaces with a closed list of implementers, which user code cannot extend (`implements` one is EN0419): `__Int`, `__Float`, `AtomicValue`, `AtomicBits` (section 10.5) and `VolatileValue` (section 7.2). They exist so that rules about particular primitives can be written as ordinary bounds and checked once.

No operator overloading exists beyond `==` through `Eq`.

### 4.5 Coercions

Coercions apply only at coercion sites: argument to parameter, initialiser to annotated local, field initialiser, assignment right-hand side to the target's type (compound assignment excluded), `return` to result type, array-literal element to the expected element type, and match-arm or ternary-branch results to an expected type. Nothing nests: `T[]` never becomes `(T | null)[]`, and `&mut (T | null)` never becomes `&mut T`. A spread operand is not a coercion site (4.13). Assignment follows the same table, so `r = s` with `r: &T` borrows, and `x = v` with `x: &mut T` stays EN0422.

Row IDs are stable and each row has an accepting and a rejecting fixture (`TESTING.md` section 18).

| ID | From | To | Condition |
|---|---|---|---|
| C01 | place of type `T` | `&T` | Implicit shared borrow. Applies only when the expected type is `&T`; rvalues use a statement temporary |
| C02 | `&mut T` | `&T` | Reborrow |
| C03 | `&mut T` | `&mut T` | Implicit reborrow, never a move (rule O7) |
| C04 | `&Box<T>`, `&mut Box<T>` | `&T`, `&mut T` | Box deref; a place of type `Box<T>` also auto-derefs on `.` |
| C05 | `&T` | `T` | **Read-through**, only when `T` is Copy |
| C06 | `T` | `T \| null` | Wrap, value level |
| C07 | `&T`, `&mut T` | same `\| null` | Wrap at slot top |
| C08 | `&T \| null` | `T \| null` | When `T` is Copy |
| C09 | `never` | any | |
| C10 | integer or float inference variable | concrete type | Section 4.7 |
| C11 | non-capturing arrow or safe function name | `fn(...)` of identical signature, `RetSources` included | Arrows only as direct call arguments |
| C12 | any arrow or safe function name | closure parameter type of identical signature | |
| C13 | string literal | `&string` | Static descriptor, section 5.4 |
| C14 | closure parameter | closure parameter type of identical signature | Exclusive reborrow for that call (5.5) |
| C15 | safe `fn(...)` value or safe function name | `unsafe fn(...)` of identical signature and ABI | Never the reverse |
| C16 | name of an `unsafe function`, `@requires` function, `declare function` or `@naked` function | `unsafe fn(...)` of identical signature and ABI | `@dll` functions have `@abi("win64")`. These never become a safe `fn` or a closure parameter: EN0803 |
| C17 | name of an `@interrupt` function | `InterruptHandler` | Only target; anything else is EN0803 |

There is **no** implicit `&mut` at call sites (EN0612), no numeric coercion, no `T` to `Result`, no truthiness. Operators see through one reference: arithmetic, comparison and `${}` on `&T` act on `T` when `T` is Copy or `string`; `==` compares through references on both sides, never by address (raw pointers compare by address).

### 4.6 Numeric rules

Binary arithmetic and comparison require identical types after inference; `i32 + i64` is EN0402 with an `as` fix-it. `/` on integers truncates toward zero; if both operands came from unsuffixed literals or literal-default inference variables, warning EN0430 explains that TS would give `3.5` and offers `7.0 / 2.0`. Bitwise and shift operators need integer types (EN0403). Shift counts have any integer type.

**Comparison.**

| Operands | Rule |
|---|---|
| `p == null`, `p != null` | Legal for any `T \| null` |
| Numerics of one type, `bool`, `string`, payload-free enums | Compare natively |
| Raw pointers | Compare by address |
| Class or payload enum | Calls `Eq`; otherwise EN0421 |
| `T \| null == T \| null` | Needs `T` comparable; equal when both are null, or both present with equal payloads |
| `T \| null == T` | EN0401 with a narrowing fix-it |
| `<`, `<=`, `>`, `>=` | Numerics only; `string` gets EN0420 with a `.compare` fix-it |

**Conversions.** `x as T` is the only conversion. A direct literal operand, optionally negated, takes a numeric target's type: `0xFFFFFFFFFFFFFFFF as u64` is legal and `300 as u8` is EN0411. A raw-pointer target makes the literal `usize`, so `0xB8000 as *mut u16` is legal. Any other operand whose type is still an inference variable does not unify with the target. It defaults at the end of the function, and the conversion kind is chosen after that.

| Conversion | Behaviour |
|---|---|
| int to int | Panics if the value does not fit |
| int to float, float to float | Rounds to nearest-even, never panics; overflow to infinity follows IEEE |
| float to int | Truncates toward zero; panics on NaN or out of range |
| payload-free enum to int | Discriminant, checked as int to int |
| int to enum | Not allowed: EN0404 |
| `bool` to int | `0` or `1`; the reverse is EN0404 |
| `usize` to raw pointer | Safe to create |
| raw pointer to `usize` | Safe |
| `&T`, `&mut T` to `*T`, `*mut T` | Safe; `&T` cannot become `*mut T` directly (EN0810) |
| `*T` to `*U` | Safe to create; dereferencing is `unsafe` |

Non-checking forms are methods: `x.wrap<u8>()` (keep low bits, or sign-extend), `f.toBits()`, `f64.fromBits(b)`, and the arithmetic families `wrappingAdd`, `checkedAdd` (returns `T | null`), `saturatingAdd`, `overflowingAdd` (returns `Overflowing<T>`, a `core` class with `value: T` and `overflowed: bool`), likewise `Sub`, `Mul`, `Neg`, `Shl`, `Shr`.

Array indices accept `isize` and `usize`; any other type is EN0405 with an `as isize` fix-it. Negative `isize` panics as out of bounds. `.length` is `isize`, so `i - 1 < 0` works as in TS.

### 4.7 Inference

Local, bidirectional, per function body; signatures are never inferred. Parameters and fields must be annotated (EN0409); return types default to `void`.

1. Each integer literal gets a fresh integer variable, each float literal a float variable. An integer variable may unify with any integer or float type; a float variable with any float type. Variables unify across the whole function, so `for (let i = 0; i < xs.length; i++)` makes `i` an `isize`, one register on `i386`.
2. Unresolved variables default at the end of the function: integer to `i64`, float to `f64`. Using one as an index defaults it to `isize` first.
3. A literal that does not fit its final type is EN0411. A `-` immediately before an `IntLit` folds before the range check, in expressions and patterns, so `const m: i64 = -9223372036854775808;` is legal. A float literal keeps its text and is parsed once, at its final width, so an `f32` literal is correctly rounded and never double rounded.
4. **Generic calls** run in three steps. `f<i32>(x)` gives type arguments explicitly, all or none, and an unresolved `T` at the end is EN0410.
   - Unify the return type with the expected type.
   - Process non-arrow arguments left to right. `&?T` against a non-reference `U` binds `T := U` and records an auto-borrow. `&mut ?T` against a non-reference is EN0612. `?T` against `&U` stays pending until the end of the call, then resolves from other bindings, otherwise by Copy read-through, otherwise EN0703.
   - Process arrows left to right, with substituted parameter types.
5. `[]` needs an expected type or later unification with a `push`; otherwise EN0410. Local type variables unify across later uses, exactly as literals do. A member access on a still-unknown type variable is immediately EN0410. A member access on an integer or float variable looks up the members of `__Int` or `__Float` with `Self` set to that variable, so inference continues: `let a = 5; a.checkedAdd(1)` works. Section 4.13 types a spread.
6. `null` alone needs an expected type.

### 4.8 Null narrowing

Narrowing is flow state during type checking, not a later pass, because it changes types: `return Ok(v)` infers `T := i64` from it, and `n.x` resolves only with it. Facts are `(path, non-null)`, where a path is a local or `this` followed by field projections, possibly through a reference or `Box`. Paths never contain an index.

- **Created by:** `p != null`, `p == null` in the else branch, `!(…)`, `&&` left to right, `||` in its false branch, early `return`/`break`/`continue`/`panic` in the opposite branch, and ternaries.
- **Killed by.** The fact on `p` dies on assignment to `p` or a prefix; on `&mut` of a prefix, including every exclusive reborrow of a `&mut` local prefix (O7), whether it is passed to a `&mut` parameter, as in `wipe(h)`, or read into another local, as in `const g = h`; on a binding from a `&mut` scrutinee, which is `&mut` of the bound path, as in `const { items } = h`; on `&mut p` at type `&mut (T | null)`, including `.take()`; on `q?.m(...)` with `q` equal to `p` or a prefix of it, when `m` has mode `mut` or `own`; and on a move of `p`, its payload or a prefix. Writes, `&mut` borrows and moves of a proper extension `p.f` kill only facts on `p.f` and deeper. So `if (n != null) { n.x = 1; n.x = 2; }` and `if (n != null) { n.bump(); n.bump(); }` compile. Shared borrows and calls do not kill facts: exclusivity prevents hidden mutation.
- **Evaluation order.** Kills run in O6 order, and a receiver auto-borrow or an assignment place takes effect after its arguments or right-hand side. The receiver or place is therefore typed as narrowed only if no argument or right-hand side kills the fact. `o.add(clear(&mut o))` and `o.n = clear(&mut o)` are EN0401, with a note naming the argument.
- **Loops.** Before the condition of a loop is checked, a prescan of the loop's syntax collects assignment targets, `++`/`--`, explicit `&mut path`, `path.m(...)`, `path?.m(...)`, every bare use of a local whose known type is `&mut` (one that is not the base of `.`, `?.`, `[]` or `*`), and every binding from a scrutinee or initialiser whose known type is `&mut`, including inside arrow bodies and spread operands. For `path.m(...)` and `path?.m(...)`, `m` is found by walking declared types from the root local's currently known type, peeling `| null`, `&` and `Box`. It counts as a write if its mode is `mut` or `own`, or if it cannot be resolved. The kill rules apply to everything collected. A bare use counts even where the checked call turns out to reborrow it shared, so the prescan can only kill too much.
- **`for...of`.** The source is typed under the current facts and classified (5.6). The prescan then covers the body only, so `&mut p` in the source kills nothing, and an evaluate-once source uses its fact before any kill: `if (p != null) { for (const x of [...p]) { p = null; } }` compiles. A path source is read at the head of every turn, so the facts it depends on are not killed by the prescan. Instead, after the body is typed, each of them must be in the flow state at the fall-through back edge and at every `continue` of this loop. Entry and back edges then all establish the fact, so the head and the body start narrowed soundly. A missing fact is EN0401 at the source, with a note naming the kill: `` `p` is checked again at the start of every turn, and this write removes the narrowing ``. So `if (p != null) { for (const x of p) { p = null; } }` is EN0401, and with `p = null; break;` it compiles, because that path never returns to the head. The state after the loop is the join of the head's exit edge with the state at every `break` of this loop, labelled or not, and never the head's state alone, so a fact holds after the loop only if every way out to that point holds it. So `if (p != null) { for (const x of p) { p = null; break; } console.log(p.length); }` is EN0303. A `break outer` in an inner loop counts as a `break` of `outer` and not of the inner loop. A `return` or a panic never reaches that point, so `p = null; return;` costs nothing after the loop. `p.push(1)` at the narrowed type kills nothing, so `if (p != null) { for (const x of p) { p.push(1); } }` compiles, with EN0719.
- **Arrows.** The same prescan runs over each arrow argument of a call before narrowing enters it. An arrow inherits facts on paths it only reads. A path that any closure argument of the call writes or borrows exclusively loses its fact at the call, and no arrow of that call sees a fact on it. So `if (p != null) { xs.forEach(x => { p = null; }); console.log(p); }` is a compile error rather than a tag panic.
- **Effect:** a narrowed path has type `T` for reads and moves. `&mut p` under narrowing has type `&mut T`, which cannot write `null`; if context needs `&mut (T | null)`, the fact dies and the expression has that type. The lowered read is a `CheckTag` immediately before the projection, in the same MIR block with nothing but other checks between them, as for `CheckBounds`, so a compiler bug panics rather than reads garbage.
- **Not narrowed:** truthiness (`if (x)` is EN0203), array elements, `typeof`.

`p?.f` on a place of `T | null` has type `&F | null` (shared loan), which reads through by C08 when `F` is Copy. `p?.m(args)` calls `m` when non-null and has type `R | null`, except that a `void` method gives `void`. On an `&T | null` value it behaves the same, so `a?.b?.c` works. On an owned `T | null` rvalue it is EN0413: bind it first.

`a ?? b` evaluates `b` only if `a` is null; `a: T | null` and `b: T` give `T`, moving out of `a` when `a` is a place of owned non-Copy `T`. `x!` panics with `unexpected null` if null, otherwise moves the payload out of an owned path or reads a reference.

### 4.9 Constants and top-level storage

`const NAME: T = e;` is compile-time: `e` is built from literals, other constants, arithmetic with checked overflow (failure is EN0412), `sizeOf`/`alignOf`/`offsetOf`, numeric `as`, `usize` to raw pointer `as`, fixed-array and class literals of those. A cycle such as `const A = B; const B = A;` is also EN0412. The annotation may be omitted when the initialiser's type is determined; an integer literal then defaults as in 4.7. `T` has no `Drop` and no heap; string literals are allowed only as `&string`. `assert(constExpr, "message")` at top level (`TopAssert`) is a compile-time check, EN0415 on failure. A constant is copied wherever it is read by value, and `&CONST` is a reference with an empty loan set. An array spread allocates at run time, so `...` in a `ConstExpr` is EN0412 at that token, with the note `a spread allocates at run time`, reported before any expected type is compared. That covers top-level `const` and `let` initialisers, `RepeatLit` counts, `T[N]` lengths and `assert`. Field initialisers run at run time and a local `const` is an ordinary binding, so `const ys = [...xs];` in a function body is fine.

Top-level `let NAME: T [= e];` is mutable static storage. Every read, write or borrow needs `unsafe` (EN0801). `T` must not implement `Drop` or contain `string`, `T[]` or `Box` (EN0802). With no initialiser it is zero-filled and `T` must be zeroable: integers, floats, `bool`, raw pointers, fixed arrays and classes of those, private fields included. `void` and references are not allowed.

### 4.10 Generics

Monomorphised on a worklist. Bodies are type-checked and borrow-checked once, generically, against bounds, and instantiation cannot introduce a type or borrow error. Exactly two codes depend on a concrete instantiation: EN0414 (depth above 64) and EN0435 (size limits, section 11). They are reported in phase 5 with the reach chain. Rules about particular primitives (volatile width, atomics) are sealed bounds, checked at the call site, so they never wait for instantiation. Members called on `T` must come from a bound; `T extends Copy` also grants `clone` (4.4). `T` is treated as non-Copy unless bounded by `Copy`; reading it by value moves it. No associated types, const generics, specialisation or higher-kinded types (EN1014). Type parameters on a class are in scope in its methods; `static` methods use them too: `Stack<i64>.empty()`, or inferred from the expected type.

### 4.11 Mutability

- A place is mutable iff its root is a `let` local, a `mut` parameter, a `&mut` deref or `this` under `mut`/`own`, or a top-level `let` inside `unsafe`.
- `const` roots are deep: fields, elements and `&mut` borrows of them are rejected (EN0608). `const r = &mut x` cannot be rebound but writes through `*r`.
- Through `&T`, nothing is writable, transitively, including through `Box`. Raw pointers end the transitive rule: `*mut` fields of a `&T` are copied out as raw pointers; writing through them needs `unsafe`.
- `readonly` fields reject writes outside the constructor even from `&mut` (EN0609).
- `x = v` where `x: &mut T` and `v: T` is EN0422, with a fix-it to `*x = v`. Field assignment `x.f = v` auto-derefs. `x = &mut y` rebinds if `x` is `let`.

`const` is Rust's plain `let`, and `let` is Rust's `let mut`. These rules cover a `const` that holds a reference, with nothing added for it:

```ts
let x = 12;
const y = &x;       // valid: `y` cannot be reassigned, and `x` is frozen while `y` is live
console.log(y);     // the last use of `y`, so the loan ends here
x = 13;             // fine now
```

Writing `y = &z;` is EN0613, and `x = 13;` above the last use of `y` is EN0706. `const r = &mut x; *r = 13;` is valid, because the write goes through the binding and does not change it.

### 4.12 Modules

One file is one module; `foo.test.en` is an extra part of module `foo.en`. Items are private unless `export`ed. Import paths resolve relative to the importing file, cycles are EN0304, and the compile is whole-program with one entry file. Imported class names carry privacy with them; a `private` field stays private to the class. The prelude (section 8.1) is implicit. Default exports, `import *`, re-exports and `require` are EN1009.

**Binding rule, normative.** `import { x } from "p"` binds the item `x` exported by `p`; otherwise it binds a namespace for the child module `p/x`. A namespace appears only to the left of `.`, in expressions and in type paths, and locals shadow it. User modules have no child namespaces in the prototype, so a miss there is EN0306. The hosted `os` root has children `os`, `fs` and `stdin`. On freestanding targets `os` selects `os/none`, with children `vga`, `serial`, `idt`, `pic`, `pit` and `cpu`. `core` has children including `cpu` and `port`. The prelude adds `mem` and `ptr` as namespaces.

### 4.13 Array spread

`[x, ...a, y, ...b]` builds a new `T[]`, and never a `T[N]`. Each element of a spread source is cloned, so `T` must satisfy `Clone`, checked once generically. That is a deep copy, unlike JS's shallow one, because a value has one owner, and the `...` is the visible token that keeps O5 true.

**Sources.** `T[]`, `T[N]`, `&T[]`, `&mut T[]`, `&T[N]` and `&mut T[N]`, each as a place or an rvalue, including a narrowed payload. The operand is a shared-borrow context and not a value context (O1), so it does not move and needs no `&`.

**Typing.** Each operand is checked with no expected type. One `&` or `&mut` is peeled, and the rest must be `Array(U)` or `Fixed(U, _)`. `U` then unifies with the element type of the literal. No coercion applies to a spread operand: an expected `U[]` gives `U` to the plain elements only. The `Clone` check runs at the end of inference, so `let q = []; const c = [...q]; q.push(1);` works.

| Form | Report |
|---|---|
| `let q; const c = [...q]; q = [1];`, where the operand's type is still unknown | EN0410 at once, as for a member access (4.7) |
| `[...5]`, `[..."abc"]` (there is no character type), `[...o]` with `o: T[] \| null` not narrowed, `[...b]` with `b: Box<T[]>` (help `...*b`) | EN0438 |
| A source whose elements do not satisfy `Clone`, a `T` with no bound included | EN0438, with a fix-it to `<T extends Clone>` where it applies (G22). A failed `where` on the generated call reports this too, never EN0419 |
| `[...move a]` | EN0401, by the rule of section 6 for `move` where `&T` is expected |
| `const a: i64[3] = [...b];` | EN0401, with a note that a spread builds a growable array |
| `const n: (i64 \| null)[] = [...xs];` with `xs: i64[]`, and `[0, ...xs]` at that type | EN0401 with a `.map` help. The element `0` alone coerces by C06, and nothing nests |
| `[...a, ...b]` with different element types | EN0401 |
| `...` in a `ConstExpr` | EN0412 (4.9) |
| `...` anywhere but an array-literal element | EN1013 (3.4) |

**Evaluation.** Left to right, and each spread clones at its position, so `[...a, f(&mut a)]` copies `a` before the call and `[f(&mut a), ...a]` copies the call's effect. The length of the result is not computed in advance. A `?` or `return` in a later element drops what was built. A source's borrow ends when its copy is made, because the result holds no references, so spread adds no borrow rule: `[...a, f(&mut a)]`, `a = [...a, x]` and `for (const j of [...queue]) { queue.push(s); }` are accepted, and `const r = &mut f; const c = [...f]; r[0] = 1;` is EN0708. The result is an ordinary `T[]`, so EN0820 and EN0824 apply as usual.

## 5. Ownership and borrowing

Everything here is checked on MIR, generically, before monomorphisation, and is independent of target. The rules contain no runtime component: no reference counts, no borrow flags, no GC.

### 5.1 Reference placement (R1, R2)

- **R1.** `&T` and `&mut T` (and either with `| null` at the top) may appear only as the type of a parameter, local, temporary or return value. They are forbidden in fields, array elements, enum payloads and generic arguments (EN0701). Closure types may appear only as parameters (EN0705).
- **R2.** A reference's pointee is reference-free: `&&T`, `&mut (&T | null)` are EN0702.

### 5.2 Moves and Copy

- **O1. Value contexts move.** Reading a place of non-Copy type in a value context moves it: initialisers, assignment right-hand sides, by-value arguments and receivers, `return`, field and array literals. Copy types copy. `const b = a` moves; it is not an alias. The operand of `...` is not a value context. It is a shared-borrow context: a place auto-borrows, a `&mut` reborrows shared, a `&` copies, and an rvalue becomes a statement temporary. Plain array elements still move.
- **O2. Places.** A path is a local, `this`, or a path followed by `.field`, `*deref`, `(as Variant).field`, or `[*]` (all indices alias). A move path contains only field projections on owned values; moving through `&`, `&mut`, a raw pointer, `*box` or `[*]` is rejected (EN0603, EN0605, EN0604). `xs[i]` of non-Copy type in a value context is EN0604, offering `&xs[i]`, `.clone()` and `.remove(i)`.
- **O3. Definite init.** Init state per move path is a forward dataflow fact; a use where a path is not definitely initialised is EN0601 (it was moved) or EN0602 (never assigned). A move inside a loop reaching itself is EN0611, and so is a move in a `for...of` body that reaches the read of the source at the head or the bind of a later turn (5.6). Assigning a whole path reinitialises it. Assigning `x.f` is legal only when `x` is definitely initialised, apart from fields moved out of it, and then reinitialises that exact field. So after `take(p)`, `p.first = c` is EN0601, for plain and `Drop` classes alike: no value is ever reassembled field by field. A constructor's `this` is the one exception (4.3). `const x: T;` may be assigned once on each path (EN0613).
- **O4. Copy.** Copy types are: numerics, `bool`, `void`, `never`, `&T`, raw pointers, `fn` pointers, payload-free enums, `T[N]` and `T | null` of Copy, and classes declaring `implements Copy`. `&mut T` is never Copy. A type cannot be both Copy and `Drop`. `Result` is Copy when both arguments are.
- **O5. Clone** is always explicit: `.clone()` or `...`. There is no implicit deep copy.
- **O6. Evaluation order.** Left to right. A call evaluates: receiver value operand, arguments left to right, then takes the receiver's auto-borrow **last**. So `a.push(a.length)` needs no two-phase borrow. Index expressions and bounds checks run after their right-hand sides: `a[i] = shrink(&mut a)` computes the address after the call. An explicit `&mut` argument takes effect at its position, so `f(&mut a, a.length)` is EN0708.

### 5.3 Borrows and reborrows

- **O7. `&mut` never moves.** Every use of a `&mut T` reborrows: `const b = a` creates a loan on `*a` held by `b`, and `a` works again when `b` is dead. Passing `r` where `&mut T` is expected reborrows implicitly; writing `&mut *r` is also legal.
- **O8. Explicitness.** `&x` is optional where `&T` is expected; `&mut x` is mandatory (EN0612). Method receivers auto-borrow per their declared mode. `&mut x` needs a mutable place (EN0608, EN0616).
- **O9. Loans.** Every borrow site creates a loan `(path, mode, span)`. Each slot `s` has a flow-sensitive set `held(s)` computed forward:
  - `s = &p` gives `{loan(p)} ∪ held(root-reference-of(p))` when `p` goes through a reference;
  - `s = t` where `t` is a reference gives `held(t)`, plus a new loan on `*t` when `t` is `&mut`;
  - assignment replaces the set and kills loans rooted at the old `*s`;
  - control-flow joins take the union;
  - a `V`-typed value holds nothing: a call returning `V` ends every loan it took.
- **O10. Liveness.** A loan is live at a point iff a slot holding it is live there (backward liveness; drop of a reference is not a use; drop of a `V` holds nothing).
- **O11. The check.** At every read, write, move, borrow, drop and scope end of a path `p`, for each live loan on an overlapping path:

  | Access | Live shared loan | Live exclusive loan |
  |---|---|---|
  | read, Copy, shared borrow | ok | EN0708 |
  | write, assign, `&mut` borrow | EN0706 | EN0707 |
  | move | EN0709 | EN0709 |
  | drop, scope end | EN0711 | EN0711 |

  Two paths overlap when one is a prefix of the other; `x.a` and `x.b` are disjoint, `x[*]` overlaps itself and `x`, and a loan through a reference `r` overlaps `*r`. The access by the loan's own holder through that holder is permitted.
- **O12. Sharing means frozen.** No `Cell`, `RefCell` or mutable global reachable from safe code. The single exception is `core`'s `Atomic<T>` and `Atomic64` for integers and `bool`, whose methods take `&this`; they hold no references and no narrowing applies to them.

Location sensitivity accepts these, both sound because the loan is simply not held on the other path:

```ts
function getOrInsert(m: &mut Table, k: i64): &mut Entry from m {
  const hit = m.find(k);            // NLL problem case #3
  if (hit != null) { return hit; }
  m.insert(k);
  return m.last();
}

let cur = &mut head;                // list cursor: `cur = &mut cur.next` style walks
```

### 5.4 The lifetime rule (R3)

**Signature rule.** A function's returned reference borrows from:

1. the parameters named in its `from` clause, if any (`this` allowed);
2. otherwise `this`, if it has a reference receiver;
3. otherwise all its reference parameters;
4. otherwise nothing: the result must hold an empty loan set.

Rule 4 covers string-literal descriptors and references to top-level `const` storage, which hold no loans and are valid for the whole program. `from` naming a non-reference parameter is EN0716.

**Definition check.** At each `return`, `held(result)` may contain only loans derived from reborrowing permitted parameters. A loan on a locally owned path is EN0710 (dangling). A loan from a parameter outside the permitted set is EN0714, whose fix-it adds a `from` clause.

**Call check.** The result of a call holds the union of `held` of exactly the permitted arguments. A shared-borrow argument that was an rvalue is a temporary living to statement end, so `const r = f(make());` is EN0712 when `r` is used after the statement, and accepted when it is not (O10): bind the argument first. There is no temporary lifetime extension: `const r = &make();` followed by a use of `r` is also EN0712.

The same summary is applied on both sides, so checking is modular and signature-stable.

```ts
function longest(a: &string, b: &string): &string {           // borrows from both
  return a.byteLength > b.byteLength ? a : b;
}
function firstWord(s: &string, sep: &string): &string from s { ... }  // only `s` stays borrowed
```

**String literals.** A literal has type `string` with `cap == 0`, needing no allocation and no drop action. Where `&string` is expected, it is a pointer to a descriptor in read-only data, holding no loan.

### 5.5 Closures

Arrow functions are legal only as direct call arguments to closure-typed or `fn`-typed parameters. Anywhere else, including a local initialiser such as `const f: fn(x: i64) => i64 = x => x + 1;`, they are EN0705 with a help suggesting a named `function`. The closure type `(x: S) => V` cannot be stored, returned, put in a local, or passed to another closure: closure types do not nest (EN0705).

- **Captures** are inferred per path: reads take shared loans, writes take exclusive loans, and all are held by the closure value for the duration of the call. A conflict with a capture is EN0715.
- **Capturing through a reference.** Capturing through a `&mut` local `r` always creates `&*r` or `&mut *r`, according to use, with a loan on `*r` held for the call. A `&mut` is never copied into a capture (O7). Only a `&T` local may be copied. So `both(() => { *r += 1; }, r);` is EN0715 in either argument order, while `run(() => { *r += 1; }); run2(r);` compiles.
- **Rebinding.** A captured reference local cannot be rebound inside the arrow (`r = other` is EN0616), so a closure cannot stash its `&T` argument in an outer `let r: &T`. Writes through it, such as `*r += 1` or `this.total += x` in a `mut` method, are ordinary exclusive captures.
- **Moves.** The body cannot move a captured value (EN0617).
- **A closure value is exactly an exclusive reborrow,** like Rust's `&mut dyn FnMut`. Calling a closure parameter `f` is an exclusive use of `f`. Passing `f` as an argument creates an exclusive loan on `f`, held for that callee, and needs an identical signature (C14). So `twice(f, f)` is EN0718, while `visit(f, n); visit(f, m);` is accepted. Capturing `f` holds an exclusive loan too, so `both(f, () => { f(); })` is EN0718.
- **`return` and `?`** inside an arrow act on the arrow. Its return type comes from the parameter's `=> U`, and an annotation, `(x: i64): i64 => x * 2`, must match.
- **The result of a closure is `V`.** `users.map(u => u)` gets EN0703. `users.map(u => u.name)` is a move through a reference: EN0603 with a `.clone()` fix-it.

A non-capturing arrow or a safe named function also coerces to `fn(...)`, which is `V`, Copy, and storable.

### 5.6 Binding modes

`match` and destructuring share one rule, set by the scrutinee alone, and `for...of` has its own table below. Classify by its type first, then by its form:

| Scrutinee | Bindings |
|---|---|
| Type `&T` or `&T \| null`, place or rvalue | `&F`, shared loan |
| Type `&mut T` or `&mut T \| null`, place or rvalue; or `&mut place` | `&mut F`, exclusive loan |
| Owned type, a place | `&F`, shared loan on the path |
| Owned type, a projection from a temporary (`make().kind`) | `&F`; the temporary lives for the whole statement (5.7) |
| Owned type, an rvalue or `move place` | Owned `F`; unbound payloads drop on arm entry |

When the payload type `F` is itself a reference, as with `v` in `match (t) { null => 0, v => use(v) }` and `t: &User | null`, the binding has type `F`. For `&` it is a copy with the same loans as `t`. For `&mut` it is a reborrow with a new loan on `*t`.

`move` on any reference-typed operand is EN0603, because the O7 reborrow does not apply to it: `match (move r)`, `for (const x of move r)` and `const b = move r` are all rejected. Copy payloads under a reference read through by 4.5.

**`for...of` sources.** The source is classified once, after type checking and member lookup, and the first row that fits wins. A **path** has the shape of a narrowing path (4.8): a local or `this`, followed by field projections, `*` on a reference or `Box`, and narrowed nullables. It never contains an index, a getter, a call, a static or a raw pointer deref. One leading `&` or `&mut` is part of the source's form and not of the path, so `&xs` means `xs` (O8). In the table `F` is the element type and `x` the loop's binding.

| Source | Evaluated | `x` has type | Loan |
|---|---|---|---|
| Path of owned array type, or `&path` | Read every turn | `&F` | One each turn, ending at the last use of `x` |
| Path of type `&T[]` or `&T[N]` | Read every turn | `&F` | The same, plus `held` of that reference |
| Path of type `&mut T[]` or `&mut T[N]`, or `&mut path` | Read every turn | `&mut F` | One exclusive loan each turn, ending at the last use of `x` |
| Place containing an index, or projection from a temporary: `grid[r]`, `make().items` | Once | `&F`, or `&mut F` under `&mut` | One on the place for the whole loop. A temporary lives for the whole statement (5.7) |
| Static or raw deref: `TABLE`, `*p` | Once | `&F`, or `&mut F` under `&mut` | None (5.9) |
| Reference-typed rvalue: a call, a getter, `c ? a : b`, `r!` | Once | By its type | The loop keeps the value's loans for the whole loop |
| Owned rvalue or `move place` | Once | Owned `F` | None. `T[]` is consumed, and its remaining elements drop on `break`, `return` or `?`. `T[N]` is copied element by element and needs Copy `T`, otherwise EN1015 with a help to use a `T[]` |
| `a..b` | Bounds once | Owned integer | None |

**A path source holds no borrow between turns.** At the head of every turn the loop reads the source's length as it is then, and leaves if its hidden index has reached it. Otherwise `x` is bound as a fresh ordinary borrow of that element, which lasts until the last use of `x` (O10), and the index moves on. So the loop sees pushes and removals as JS does: pushes get later turns, and removals end the loop early. Assignment differs from JS, whose iterator keeps the array it started with. Here the path is read again, so the next turn reads the assigned array at the same hidden index: `let q = [1, 2, 3]; for (const x of q) { console.log(x); q = []; }` runs one turn and warns (EN0719), where JS runs three. Rebinding a reference the source goes through retargets later turns in the same way.

```ts
let queue = ["a", "b"];
for (const job of [...queue]) { queue.push("retry"); }  // a copy: 2 turns, and `queue` then has 4 items
for (const job of queue) { queue.push("retry"); }       // compiles and warns (EN0719): it never stops by itself
```

Using `x` after the source changed is rejected by the ordinary check, because the element may have moved: `for (const job of queue) { queue.push("retry"); console.log(job); }` is EN0706 (G08). To freeze a source for the whole loop, hold a reference to it: `const r = &queue; for (const job of r) { queue.push("x"); }` is EN0706, because the head reads through `r` on every turn. A move of the source or of a prefix in the body is EN0611 if a later turn can read it, so `take(q);` is rejected, and `take(q); break;` and `take(q); q = [];` are accepted.

**Warning EN0719.** It fires once for each path-source loop over a `T[]` that has, at a point from which the next head is reachable, an assignment to the source or a prefix of it, or an exclusive borrow of either, however the borrow arises: a `mut` method, `&mut`, an implicit reborrow such as `grow(q)`, or a closure capture. An exclusive capture counts even if the arrow writes only elements. Element writes such as `xs[i] = v`, disjoint fields, a `T[N]` source and an evaluate-once source do not fire it, and neither does `q.push(1); break;`, where no later turn exists. No compiler can prove termination, so a conditional push still warns. A plain `for (let i = 0; i < q.length; i++)` gets no warning, and warnings have no opt-out, so that is the form to keep when a loop means to grow. The warning is skipped for a loop that has a phase 3 error on an overlapping path, in the loop or at its source.

**Termination.** Such a loop runs until something stops it: `break`, a panic if an allocation fails, `--max-memory` and `--spin-limit` in the VM, or T0004 in `enrang test`. On a hosted native target the operating system may end it first.

### 5.7 Drop

- **D1.** A drop is scheduled for every owned local, parameter and temporary with a non-trivial type on every exit: fall-through, `break`, `continue`, `return`, `?`. Elaboration with init dataflow makes each static, flag-guarded or per-field. A partly moved enum, nullable or `Result` first switches on its tag, and then handles only the active variant's fields, so a move flag means something only inside its variant's arm. Copy types and types with no `Drop` in their tree drop trivially.
- **D2. Order.** Locals and parameters in reverse declaration order. Temporaries end, in reverse creation order, at the first boundary in the table below, always before any local of that block ends. For a value: user `drop` first, then fields in declaration order; enum payload fields in declaration order; array elements by increasing index, then the buffer; `Box` inner then the block; `string` frees only if `cap > 0`.

  | Temporaries created in | End |
  |---|---|
  | Condition of `if`, `while`, `do...while`, `for`, or a ternary | Right after the condition, before the body runs or the condition is re-tested |
  | Step of a `for` | Right after the step |
  | Right operand of `&&` or `\|\|` | Right after that operand |
  | Scrutinee of `match`, source of `for...of` | After the whole statement |
  | `let`/`const` initialiser, expression statement, assignment, `return` | At the end of the statement |

  So `while (ok("a" + "b") && n < 3) { n += 1; }` drops its string once per test and never across the body.
- **D3. Assignment** `x = v` evaluates `v`, drops the old `x` if initialised, then stores. `_` as a local name is ordinary and lives to scope end; `_` in a pattern binds nothing.
- **D4. Partial moves** from an owned path are allowed unless the type at any prefix implements `Drop` (EN0607). The remaining fields drop normally, by per-field flags where needed. Bodies of `own` methods may partially move `this`. `Box` contents and array elements can never be partially moved.
- **D5.** `drop(x)` ends a value early. `mem.forget(x)` is safe: leaks are safe and no memory-safety property relies on a destructor running. `mem.replace(&mut x, v)` and `x.take()` (on `T | null`) cover moves out from behind `&mut`.
- **D6. No unwinding.** A panic runs no drops. Allocation-balance checks exempt panicked runs.

### 5.8 Why it is sound

These invariants hold at each MIR step for programs with no `unsafe`, assuming correct compiler and libraries:

- **I1.** References exist only in frame slots, by the `V`/`R`/`S` grammar and R1.
- **I2.** A reference in frame `F` points into memory owned by `F` or an older frame or static storage, because the only upward path is `return`, gated by R3 at both ends.
- **I3.** While a loan is live, conflicting accesses are rejected, so the pointee cannot be freed, moved, reallocated, change variant or be mutably aliased. No write through a pointer can add a loan invisibly, because pointees contain no references (R2).
- **I4.** Every heap block has one owner and is freed once: move and init dataflow plus elaborated drops.
- **I5.** Destructors reach only their own tree, because `V` holds no references and safe code has no mutable globals; so drop check is unnecessary.
- **I6.** Narrowing facts cannot be invalidated invisibly: writes need a visible exclusive access (O12).
- **I7.** Bounds, overflow, division, conversions and stack limit are dynamically checked and panic.

Hazards closed by construction. Row IDs are stable and each has a fixture (`TESTING.md` section 18).

| ID | Hazard | What closes it |
|---|---|---|
| H01 | Reference into an array followed by `push` | `[*]` overlaps `&mut a` |
| H02 | Reference into a payload followed by a variant overwrite | Payload loan overlaps the whole place |
| H03 | `T[]` used as `(T \| null)[]` | No subtyping, nothing nests, no coercion on a spread operand |
| H04 | `&mut &T` shrinking and rust#25860 | No nested references, no lifetime parameters |
| H05 | Self-reference | No references in fields |
| H06 | `T := &U` smuggled through a container | `T` ranges over `V` |
| H07 | Hole behind `&mut` during unwinding | No unwinding, no moves through references |
| H08 | Copy-plus-Drop double free | Mutually exclusive |
| H09 | Guard-page skipping | Descending stack probes and limit checks |
| H10 | User `drop` called through a structural interface | The `drop` method is never a member |
| H11 | Precondition laundered through a function pointer | `unsafe fn`, EN0803 |
| H12 | Duplicate owner through `Atomic<T>` with non-Copy `T` | Sealed `AtomicValue` |
| H13 | Allocator re-entered from an interrupt, a panic or itself | EN0824 |
| H14 | Size arithmetic wrapping to a small allocation or frame | EN0435, `isize.MAX` capacity limit |
| H15 | Non-UTF-8 `string` built in safe code | `pushByte` panics on bytes from `0x80` up |
| H16 | Misaligned reference to a packed field | EN0804 on every MIR `Ref`, EN0826 |
| H17 | Mutating through `&T` or a `const` via a by-pointer argument | The caller's temporary is elided only under the rule of `ARCHITECTURE.md` section 7.6 |
| H18 | Narrowing fact invalidated between the check and the projection | Kills in O6 order, `CheckTag` adjacent to the projection |
| H19 | `&mut` aliased through a closure capture | Capture reborrows `*r` with a loan |
| H20 | `for...of` element reference kept across a push that reallocates | Each turn's binding is an ordinary loan, so a later use is EN0706; no reference spans the change |
| H21 | Stale length or index after a `for...of` source shrinks, is assigned or is rebound | `Len` read at every head, `CheckBounds` before every projection, never elided |
| H22 | `for...of` source moved in the body and read by a later turn | Init dataflow at the head and the bind, EN0611; both stay in MIR even for an unused binding |
| H23 | `for...of` element reference into a packed field, with no source `Ref` to catch | EN0804 is a rule on the place, not the field |
| H24 | Narrowed `for...of` source cleared in the body, directly or through a reborrow | Source facts checked at every back edge, EN0401; the state after the loop joins the head's exit edge with every `break`, so a read there is EN0303 or EN0401 by its use; `CheckTag` at the head and the bind |
| H25 | Hidden index past a zero-sized `T[]` whose length no allocation limits | `push` panics `capacity overflow` at `isize.MAX`, so `_i < _n` cannot overflow |
| H26 | Spread source that cannot give an array header: `T[N]` read as `T[]` | `T[N]` lowers to an ordinary MIR loop, never a call taking `&T[]` |

This is not mechanised. Accepted programs are a fragment of safe Rust under Polonius, where each summary is one named lifetime and each closure a `&mut dyn FnMut`. That gives a test oracle: translate accepted programs to Rust and check them with `rustc`; the VM's fault detector treats any dynamic fault in an accepted program as a soundness bug. A path source translates to an index `while` loop and not to `for x in &q`, which `rustc` would reject (`TESTING.md` section 13).

### 5.9 The boundary of `unsafe`

`unsafe { }` blocks and `unsafe function` bodies grant **exactly five** powers:

1. dereference raw pointers, including `*p` places and the `read`, `write`, `readVolatile`, `writeVolatile` pointer methods;
2. call `unsafe function`s, `unsafe` methods, `declare function`s and `@requires` functions, and call through an `unsafe fn` value or any function pointer with an `@abi` tag, which runs foreign code;
3. `asm(...)`;
4. read, write or borrow top-level `let` variables;
5. access `@at` storage.

`unsafe` does not relax type checking, moves, the loan check on references, R1, R2, or definite init. A reference created from a raw pointer (`&*p`) holds an empty loan set: its validity is the writer's obligation.

**Obligations.** Unsafe code must uphold, for all safe code it can reach: every `&T` and `&mut T` it creates is aligned, non-null and points to a live initialised `T`; a live `&mut T` is the only access path, and a live `&T` sees no mutation except through `Atomic`; values read are valid for their type (`bool` is 0 or 1, enum tags are declared, `string` is UTF-8 with consistent `ptr/len/cap`); nothing is freed twice; layout assumptions use `@repr` or `@packed`. Breaking one is undefined behaviour, confined by the language to programs containing the `unsafe` keyword: the memory-safety theorem in 5.8 excludes them, and `enrang test`'s VM reports violations dynamically where it can.

**Allocator contract.** `@globalAllocator unsafe let` is an explicit unsafe act, and it does not add a sixth power: it is a promise with these obligations. `alloc(size, align)` returns null, or a block of at least `size` bytes aligned to `align`, overlapping no other live block. `dealloc` receives exactly a pointer, size and alignment that `alloc` handed out. The methods never re-enter the allocator; reaching `alloc` from them is EN0824, so the compiler checks this part.

Creating, casting and comparing raw pointers is safe; only using them is not.

## 6. Expressions and control flow

- **Conditions** must be `bool`. `if (count)` is EN0203.
- **`match`** works on enums, `T | null`, `Result`, integers, `bool`, `string` and payload-free patterns thereof. It is an expression; arms are tried top to bottom. An arm body that is a block has type `void` unless it diverges; `return`, `break`, `continue` and `panic` have type `never`. No guards, no ranges, no fallthrough. Exhaustiveness uses Maranget's algorithm with a witness; a missing case is EN0501, an unreachable arm is warning EN0503. Integers and strings need a `_` arm. `A | B =>` patterns bind nothing (EN0505). On `T | null` the constructors are `Null` and `Present`: any pattern other than `null` and `_` implicitly wraps in `Present`, so `match (s.parseInt()) { null => 0, 0 => 1, n => n }` is exhaustive with `n: i64`. `null` always matches the outermost level, and a witness for an inner null prints as `a present null`.
- **Ternary** branches must unify; moves are branch-sensitive.
- **Loops.** `for (init; cond; step)`, `while`, `do...while`, `for...of`; labels on loops, `break label`, `continue label`. Falling through without `return` in a non-`void` function is EN0427.
- **`for...of` sources** are `T[]`, `T[N]`, a reference to either and a range `a..b`, classified in 5.6. `for (const x of b)` with `b: Box<T[]>` is EN1015 with a help to write `*b`. User iterators and `for (const c of "abc")` are EN1015. `for (let i of 0..n)` allows reassigning the loop's copy, which does not affect the iteration.
- **`Result<T, E>`** is prelude `enum Result<T, E> { Ok(T), Err(E) }`. `Ok`, `Err` are bare; `Ok()` means `Ok(void)`. There is no implicit wrap in either direction.
- **`e?`** on `Result<T, E>` yields `T` or returns `Err(e)` from the enclosing function or arrow, which must return `Result<_, E>` with the identical `E` (EN0425, EN0424). On `T | null` it yields `T` or returns `null` from a function or arrow returning `_ | null`. Scheduled drops run.
- **Unused results.** An expression statement of `Result` type is EN0426; `void f();` discards deliberately, dropping the value.
- **`main`** is `function main(): void`, `: i32` (exit code), or `: Result<void, E>` with `E extends Display` (an `Err` prints `error: <e>` to stderr and exits 1); any other signature is EN0436. There are no top-level statements. `os.args()` gives the arguments.
- **`+` on strings** takes `&string` operands and returns a new `string`. `+=` appends in place, copying first if `cap == 0`.
- **Integer operators** have section 9 semantics. `i++` is `i += 1`, a statement.
- **`move x`** forces a move as the scrutinee of `match` or the source of `for...of`, which would otherwise borrow. Where the expected type is `&T`, and as the operand of `...`, it is EN0401. On a reference-typed operand it is EN0603. In other value contexts it is redundant but legal. **`void e`** evaluates `e`, drops the result and has type `void`.

**Compiler forms.** These cannot be ordinary declarations, and this list is complete. They lower through one HIR callee kind. Everything else, including `toString()`, is an ordinary library member: `toString` is `extend<T extends Display> T` in `alloc`, and a synthesised `clone` is a compiler-generated glue function.

| Form | Signature | Arguments | Availability |
|---|---|---|---|
| `console.log(a, b, ...)`, `console.error(...)` | Variadic, each `Display`; `void`. Separated by one space, followed by `\n` | Implicit shared borrows; rvalues become statement temporaries; a packed field is copied first | Hosted and VM; EN0823 on freestanding |
| `` `...${e}...` `` | `string`, each hole `Display` | As `console.log` | Allocates through `alloc`, unless passed directly to `console.*`, `writeTo` or `panic`, where pieces go straight to the stream |
| `panic(m)` | `m` is `&string` or a template; `never` | Holes as `console.log` | Everywhere. A template renders into a 256-byte static panic buffer, truncated at a char boundary, so it never allocates |
| `assert(c, m?)` | `c: bool`, optional `m` as `panic`; `void` | `c` by value | Everywhere; the only optional parameter in the language |
| `unreachable()` | `never` | | Everywhere |
| `writeTo(f, t)` | `f: &mut Formatter`, `t` is `&string` or a template; `void` | Holes as `console.log` | Everywhere; never allocates |
| `sizeOf<T>()`, `alignOf<T>()`, `offsetOf<T>("f")` | `usize`, constant | Type only | Everywhere, including `ConstExpr` |
| `cpu.has("f")` | `bool` | String literal, checked (EN0908) | Everywhere; section 10.3 |
| `asm(...)` | `void` | Section 7.4 | `unsafe` only; EN1201 in the VM |
| `test`, `describe`, `expect`, `compileFails`, `compileOk` | Section 12 | | Test builds |

## 7. Systems programming

### 7.1 Raw pointers

`*T` and `*mut T` are Copy, carry no loans, and may be stored anywhere; they are nullable with address 0. Safe operations: `&x as *T`, `&mut x as *mut T`, `addr as *mut T` (`addr: usize`), `p as usize`, `p as *U`, `p == q`, `p.isNull()`, `p.add(n)` and `p.sub(n)` (wrapping, scaled by `sizeOf<T>()`), `ptr.null<T>()`. Unsafe operations: `*p`, `&*p`, `p.read()`, `p.write(v)`, `p.readUnaligned()`, `p.writeUnaligned(v)`, `p.readVolatile()`, `p.writeVolatile(v)`, `mem.copy(dst, src, n)`, `mem.copyOverlapping`, `mem.set`. `write` does not drop the old value; `*p = v` does.

### 7.2 Volatile

Volatile is per access, never a type qualifier. `readVolatile` and `writeVolatile` compile to exactly one load or store of the exact width, in program order relative to other volatile accesses and `asm`; never merged, split or eliminated. `T` must satisfy the sealed bound `VolatileValue`: `u8 u16 u32 i8 i16 i32 usize isize bool` and raw pointers, plus `u64` and `i64` on `x86_64-*`. Anything else is EN0805 at the call, generic or not; `u64` volatile on `i386` is EN0805 because it would tear. Generic code states the bound: `function w<T extends VolatileValue>(p: *mut T, v: T): void`.

```ts
const VGA = 0xB8000 as *mut u16;
unsafe { VGA.add(i).writeVolatile(0x0700 | (ch as u16)); }
```

### 7.3 Port I/O

`core/port` provides `unsafe function`s: `inb(p: u16): u8`, `inw`, `inl`, `outb(p: u16, v: u8)`, `outw`, `outl`, and `ioDelay()` (`out 0x80`). They are `asm` wrappers on every x86 target, so they are forbidden in the VM (EN1203). In a hosted process they fault at run time unless the OS allows them.

### 7.4 Inline assembly

```ts
function cpuFlags(): u32 {
  let value: u32;
  unsafe {
    asm(`pushfd
         pop eax`, { out: { eax: value } });
  }
  return value;
}
```

- `asm` is an expression of type `void`, legal only in `unsafe` (EN0801). The template is a literal with no interpolation (EN0915), Intel syntax, instructions separated by newlines or `;`, local labels `name:` scoped to one `asm`.
- `in`, `out`: maps from physical register name to a place of a type matching the register's width. `out` places count as initialised for init dataflow. `{ eax }` is shorthand when the place has that name.
- `clobbers`: registers destroyed besides `in`/`out`. Flags and memory are always assumed clobbered. `ebp`, `esp`, `rbp` and `rsp` cannot be bound (EN0905) and must be restored by the end of the block. DF must be clear on exit.
- The same assembler and encoder table serve the compiler's own code. Every instruction is checked against the target's level. A form above it is EN0901 naming the instruction, its feature, the level that provides it and the current level. An unknown mnemonic is EN0902 with "did you mean".
- Only forms in the encoder's table are accepted. MMX, 3DNow! and packed SSE forms are EN0916. Scalar SSE1 forms and `ldmxcsr`/`stmxcsr` are tagged `sse` and accepted at level `sse2`, which needs them. `popa`, `popad` at `i386` get warning EN0914 (386 erratum), and the assembler inserts a `nop` after them.

### 7.5 Naked and mode-specific code

`@naked unsafe function` has no prologue, epilogue or spills; its body must be a single `asm` statement. `@bits(16)` assembles a naked function's body in 16-bit mode, using the minimal subset the boot stage needs; it is rejected outside `@naked` (EN0913). Calling a `@bits(16)` function from Enrang is EN0913.

A naked body may also use the data directives `db`, `dw`, `dd`, `dq`, `align` and `times <n> db <v>`, where `<n>` is a constant expression over integers, `+`, `-`, parentheses, `$` (current offset) and `$$` (section start). So a raw 512-byte boot sector is user code: `times 510 - ($ - $$) db 0` then `dw 0xAA55`, built with `--format=flat --base=0x7C00`. Symbol operands stay library-only (EN0903).

### 7.6 Layout control

- `@repr("C")` on a class fixes declaration-order natural-alignment layout as a promise (the default layout is the same in this prototype, but only `@repr` is stable across compiler versions).
- `@repr("u8"|"u16"|"u32")` on a payload-free enum sets the tag; values that do not fit are EN0412.
- `@packed` removes padding; alignment becomes 1. Every field of a `@packed` class must have a Copy, non-generic type (EN0826 at the declaration), so no drop glue touches a packed field and alignment is always known when checked. A reference into a packed field that needs more than 1-byte alignment is EN0804, however it arises: `&s.f`, `&s.b[1]`, an auto-borrow, a match binding, a `for...of` element or source, a spread operand, a closure capture. The rule is on the place: a MIR `Ref` whose place crosses a field of a `@packed` class with no later `Deref`, and whose referent type has alignment above 1. So `for (const x of p.b)` over a packed `u32[4]` is EN0804 at the source, and over a packed `u8[4]` it compiles. Use `readUnaligned` through `&s as *u8` offset or copy the field by value, which is allowed. The forms `console.log`, `${}` and `expect` copy such a field to a temporary first, so `console.log(p.b)` works.
- `@align(n)` raises alignment; `n` is a power of two up to 4096. Conflicting attributes are EN0817.
- `T[N]` is an inline fixed array of `N` elements, Copy if `T` is Copy, bounds-checked.
- `assert(sizeOf<GdtPointer>() == 6);` at top level is evaluated at compile time.

```ts
@packed class GdtPointer { limit: u16; base: u32; }
@repr("C") class Regs { eax: u32; ebx: u32; }
@align(4096) class PageTable { entries: u32[1024]; }
```

### 7.7 Interrupt handlers

```ts
import { outb } from "core/port";

@interrupt function onTimer(frame: &InterruptFrame): void { unsafe { outb(0x20, 0x20); } }
@interrupt({ errorCode: true })
function onFault(frame: &InterruptFrame, code: usize): never { panic("page fault"); }
```

Signature is checked (EN0808): one `&InterruptFrame`, an extra `usize` with `errorCode`, and a return of `void` or `never`. The compiler emits the stub: `cld`, individual register pushes and pops (never `pusha`/`popa`), a synthetic frame for stack traces, `fxsave`/`fxrstor` around the body when the float strategy is `sse2`, and `iret`. Handlers cannot be called from Enrang (EN0807) and coerce only to `InterruptHandler`, the type taken by `idt.set(vector, h)` in `os/none`. `idt.set` panics if vectors 8, 10-14 and 17 are not paired with an `errorCode` handler, and vice versa. An `@interrupt` function cannot allocate: reaching an allocation entry point, drop glue that frees, or a `@globalAllocator` method is EN0824, naming the path, and `unsafe` does not lift it. A handler sets a flag or an `Atomic`, and mainline allocates.

### 7.8 Entry point and placement

- **`@entry`** names the program's first Enrang function on freestanding targets; exactly one is required (EN0809), except as stated for flat binaries below. Signature: `function(boot: &BootInfo): never`. On `x86_64-none --format=efi` it is `function(boot: &BootInfo): never` as well; `BootInfo` is filled from UEFI tables before `ExitBootServices` returns. Hosted targets use `main`; `@entry` there is EN0809.
- **Startup**, always compiled at the floor (section 10.4): zero BSS, load the image's own GDT, set the stack, detect the CPU, check `--cpu`, set up the FPU or SSE state if built for it, call `@entry`. Entered by anything other than Enrang's boot stage, `BootInfo` is empty: no memory regions, no serial port, text base `0xB8000`.
- **`@section("name")`** places a function or static in a named output section. Section names beginning `.boot` go first, then `.text`, `.rodata`, `.data`, `.bss`, in that order; others follow in first-use order. Items in `.boot*` are always kept. Unknown section flags cannot be set; hosted targets accept only names starting with `.text.`, `.data.`, `.rodata.`, `.bss.`, and `.bss.stack` is reserved for the compiler's stack on every target (EN0814).
- **`@at(addr)`** gives a top-level `let` a fixed address with no storage allocated: access is `unsafe`. Overlap within the flat image is EN0813.
- **Flat binary:** `--format=flat --base=<addr>` emits exact bytes at that base with gaps zero-filled. The default base on `i386-none` is `0x10000`, reachable by BIOS load with no extended memory; `0x100000` needs `--base`. If a `.boot*` function exists, it is the raw entry and `@entry` is optional; with no `@entry`, no startup code is emitted.
- **Bootable images** reject a `--base` whose kernel, including BSS and stack, would overlap memory the boot stages use (EN1304).
- **Switching stacks.** A kernel that moves to its own stack declares it with `unsafe { cpu.setStackLimit(addr); }` so the overflow check follows (section 8.4).

```ts
@section(".bss.kstack") let kernelStack: u8[16384];
@at(0xB8000) let screen: u16[2000];
```

### 7.9 Panic handler and global allocator

```ts
@panicHandler function onPanic(info: &PanicInfo): never { /* ... */ halt(); }

@globalAllocator unsafe let heap: FreeListHeap;   // zero-filled: an empty heap
```

- On a freestanding target exactly one `@panicHandler` is required when any panic site is reachable (EN0812); it has signature `function(info: &PanicInfo): never`. A second is EN0811. On hosted targets it is optional and overrides the default printer. A guard flag sends a panic during panic straight to halt or exit.
- On a freestanding target `string` values, `T[]` and `Box` need one `@globalAllocator` (EN0820, section 8.3). A second is EN0821. Its type must satisfy `GlobalAllocator` (EN0822), and its declaration must be `unsafe let` (EN0825), which carries the contract of section 5.9. Hosted targets have a default; registering one replaces it.
- The allocator static is initialised like any other: zero-filled, or a `ConstExpr` with no function call (EN1032). `FreeListHeap` contains only integers and raw pointers, and all-zero bytes mean an empty heap.
- **Allocation-free zones.** Three roots may not reach allocation, on any target: every `@interrupt` function, the `@panicHandler`, and the methods of the `@globalAllocator` itself. Reaching the compiler-called allocation entry points, drop glue that frees, or a `@globalAllocator` method is EN0824, naming the path. A panic can come from inside the allocator, and an interrupt can arrive inside it, so this is what rules out re-entry. There is no run-time lock.
- Regions reach the allocator at run time. `unsafe { heap.addBootRegions(boot); }` adds every usable region of the sanitised `BootInfo` view, and `unsafe { heap.addRegion(addr, bytes); }` adds one by hand. Allocating before that panics with `allocator has no memory`.

### 7.10 FFI

- **Windows.** `@dll("kernel32.dll") declare function ExitProcess(code: u32): never;`. The compiler writes the import table; only referenced imports are emitted. Calling one needs `unsafe`. Parameters and results are scalars, raw pointers and `fn` pointers (EN0816).
- **Function pointers with an ABI.** `type EfiPrint = @abi("win64") unsafe fn(self: *mut Proto, s: *u16) => usize;` is how UEFI protocols and foreign callbacks bind. Calling any `@abi` function pointer is power 2 of section 5.9. `@abi("win64")` on a function makes it callable from foreign code. `cdecl` and `stdcall` are EN1030 and any other unknown name is EN0819.
- **Linux.** There is no dynamic linker or libc; a bodyless `declare function` is EN0815 with a note about inline assembly. Library `@intrinsic` and `@hostCall` declarations are exempt (section 3.1).
- `declare` without `unsafe` at the call is EN0801. FFI never passes `string` or `T[]` (EN0816) or a class by value (EN1030).

## 8. Standard library layers

The runtime is Enrang source embedded in the compiler binary. Unreferenced functions are stripped from every output. `core` has no allocator and no OS; `alloc` needs a registered allocator; `os` is per-target. Dependencies point only downward.

### 8.1 Prelude

Implicit in every module. `core`: all primitive types, `Copy Clone Drop Eq Ord Display Formatter`, `Result Ok Err`, the compiler forms of section 6, `drop<T>(x: T): void`, and the namespaces `mem` and `ptr`. `alloc`: `Box`, `T[]` methods, `string` allocating methods, `GlobalAllocator`, `FreeListHeap`. Their signatures are visible on every target; availability is enforced only by EN0820 in phase 5. `os` (hosted only): `console`. `os/none` (freestanding only): `BootInfo PanicInfo InterruptFrame InterruptHandler halt`.

### 8.2 `core`

| Module | API |
|---|---|
| `core/mem` | `unsafe copy<T>(d: *mut T, s: *T, n: usize)`, `copyOverlapping`, `set(d: *mut u8, v: u8, n: usize)`, all `@intrinsic`; safe `swap<T>(a: &mut T, b: &mut T)`, `replace<T>(x: &mut T, v: T): T`, `forget<T>(x: T)` |
| `core/ptr` | `null<T>()`, `nullMut<T>()`; pointer methods from section 7.1 |
| `T[N]` | `.length: isize`, indexing, `for...of`, `clone()` by compiler glue when `T` satisfies `Clone` |
| integers | `wrap<U>()`, `toBits`, `wrapping*`, `checked*`, `saturating*`, `overflowing*` for Add, Sub, Mul, Neg, Shl, Shr, the last returning `Overflowing<T>`; `min`, `max`, `abs`, `pow`, `isPowerOfTwo`; `leadingZeros`, `trailingZeros`, `countOnes`, `rotateLeft`, `rotateRight`, `swapBytes`, each lowered to floor instructions unless a higher `--cpu` allows better; `i32.MIN`, `i32.MAX` and likewise |
| `core/float` | `f64`: `sqrt floor ceil trunc round abs min max sign isNaN isFinite isInfinite toBits fromBits`, `sin cos tan atan atan2 exp log log2 pow` (Enrang code, never FSIN), `PI E INFINITY NAN`. `f32`: the same operations from `sqrt` to `fromBits` |
| `core/fmt` | `Formatter`: `write(s: &string)`, `writeByte(b: u8)`; `writeTo(f: &mut Formatter, t)` takes a template without allocating; `Formatter.fromFn(sink: fn(ctx: *mut u8, bytes: *u8, n: usize) => void, ctx: *mut u8)`. Integers print in decimal, `.hex()` wraps for hex. Floats print Dragon4 shortest round-trip, integer-only, identical on every strategy: `1`, `1.5`, `NaN`, `Infinity`, `-0`, `1e+21`, as JS does |
| `core/string` (read-only, no allocation) | `string.byteLength`, `.length` (alias of `byteLength`, with warning EN0431 on first use per module, because JS counts UTF-16 units), `.byteAt(i): u8`, `.codePointAt(i): u32` (`i` is a byte index, bounds-checked and required to be a char boundary; decoding never reads past `len`, and a sequence that is invalid because an `unsafe` obligation was broken yields `0xFFFD`), `.startsWith`, `.endsWith`, `.indexOf`, `.includes`, `==`, `.compare`, `.parseInt(): i64 \| null`, `.parseFloat(): f64 \| null`, `.asPtr(): *u8` |
| `core/atomic` | Section 10.5 |
| `core/cpu` | Section 10.3 |
| `core/port` | Section 7.3 |
| `core/option` | `T \| null` methods: `take`, `isNull`, `orElse(d: () => T)`, `clone() where T extends Clone`, declared through `extend<T> T \| null`. `T` ranges over `V`, so on a nullable reference they are EN0703 with a `== null` or `??` fix-it |

### 8.3 `alloc`

```ts
interface GlobalAllocator {
  mut unsafe alloc(size: usize, align: usize): *mut u8;   // null on failure; contract in section 5.9
  mut unsafe dealloc(p: *mut u8, size: usize, align: usize): void;
}
class FreeListHeap implements GlobalAllocator {    // address-ordered first-fit, boundary-tag coalescing
  // Integers and raw pointers only; all-zero bytes are an empty heap.
  // 2 KB code budget, 8-byte header on 32-bit, 16 on 64-bit.
  mut unsafe alloc(size: usize, align: usize): *mut u8;
  mut unsafe dealloc(p: *mut u8, size: usize, align: usize): void;
  mut unsafe addRegion(start: usize, bytes: usize): void;
}
```

A failed allocation panics with `out of memory` (programs handling OOM use the allocator directly). Every `alloc` buffer is limited to `cap * size <= isize.MAX` on every target, so `.length` is always representable and 32-bit behaves as 64-bit does; anything larger panics with `capacity overflow`, reachable on `i386`. A `T[]` of a zero-sized `T` uses no memory, so the limit falls on its length: growing it past `length == isize.MAX` panics the same way.

| Type | API |
|---|---|
| `T[]` | `[]`, `[a, b]`, `[...a]` (4.13); `T[].withCapacity(n)`; `length`, `capacity`, `isEmpty`; `push(x: T)`, `pop(): T \| null`, `insert(i, x)`, `remove(i): T`, `swapRemove(i): T`, `clear()`, `truncate(n)`, `extend(o: T[])`, `extendCloned(o: &T[]) where T extends Clone`, `swap(i, j)`, `reserve(n)`; `first(): &T \| null`, `last()`, `get(i): &T \| null`, `getMut(i): &mut T \| null`, `lastMut()`; `map<U>(f: (x: &T) => U): U[]`, `forEach(f: (x: &T) => void)`, `filter(f: (x: &T) => bool): T[] where T extends Clone`, `find(f): &T \| null`, `findIndex(f): isize`, `some`, `every`, `reduce<U>(init: U, f: (acc: U, x: &T) => U): U`, `sort() where T extends Ord`, `sortBy(f: (a: &T, b: &T) => i32)`, `reverse()`, `includes(x: &T) where T extends Eq`, `join(sep: &string): string where T extends Display`, `clone() where T extends Clone` |
| `string` | `""` is empty; `string.withCapacity(n)`; `+`, `+=`; `clone()`; `slice(a, b): string` (copies, panics off a char boundary), `trim()`, `toUpperCase()`, `toLowerCase()` (ASCII), `split(sep: &string): string[]`, `replace(a, b)`, `repeat(n)`; `pushByte(b: u8)` panics unless `b < 0x80`; `pushCodePoint(c: u32)` panics on a surrogate or above `0x10FFFF`; `unsafe pushByteUnchecked(b: u8)` for raw bytes; `fromUtf8(b: u8[]): string \| null` is the only checked route from bytes; `toString()` on any `Display` |
| `Box<T>` | `new Box(v)`, `unbox()`, auto-deref, `clone() where T extends Clone`, which allocates a new block |

**Allocator error.** On a freestanding target with no `@globalAllocator`, it is EN0820 when reachable code (a) has a local, field, parameter or return of owned type `string`, `T[]` or `Box<T>`, (b) names a template literal in an allocating position, or (c) calls any `alloc` function. The diagnostic names the first use in call-graph order and offers both a registration snippet and the non-allocating alternative. `&string` is `core` and stays legal; a literal in `&string` position has no owner.

### 8.4 `os`

Selected by TargetSpec: `os/linux_x64`, `os/linux_i386`, `os/windows`, `os/vm`, `os/none`, `os/uefi`. Programs import from `os`.

Hosted API: `console.log`, `console.error`; `os.args(): string[]`, `os.env(name: &string): string | null`, `os.exit(code: i32): never`, `os.now(): i64` (milliseconds), `os.sleep(ms: i64): void`; `fs.readFile(p: &string): Result<string, IoError>`, `fs.writeFile(p, s): Result<void, IoError>`; `stdin.readLine(): string | null`. `IoError` is an enum: `NotFound, PermissionDenied, Other(i32)`.

- Linux `i386` uses only syscalls old kernels provide: `exit` 1, `read` 3, `write` 4, `open` 5, `close` 6, `lseek` 19, `brk` 45, `gettimeofday` 78, old `mmap` 90, `nanosleep` 162. `exit_group` and `mmap2` are never used. Linux `x86_64` uses raw `syscall`.
- Windows imports only referenced `kernel32.dll` functions.
- In the VM these reach capability-checked `HostCall`s; denial returns `Err(PermissionDenied)`.

Freestanding API, `os/none`:

| Item | API |
|---|---|
| `BootInfo` | `regionCount(): usize`, `region(i: usize): MemRegion` (a Copy class with `start: u64`, `bytes: u64`, `usable: bool`), a sorted, non-overlapping view that excludes everything the boot path still uses and clips usable regions to what the target can address; `get bootDrive(): u8`, `get com1Port(): u16`, `get crtcPort(): u16`, `get textBase(): usize`, `get columns(): u32`, `get rows(): u32`, `get framebuffer(): Framebuffer \| null` |
| `FreeListHeap` | `mut unsafe addBootRegions(boot: &BootInfo): void`, an `extend` member in `os/none` that adds every usable region, so kernels never write those casts |
| `vga.Screen` | `static fromBoot(b: &BootInfo): Screen`; `mut write(s: &string)`, `mut writeByte(b: u8)`, `mut clear()`, `mut setColor(fg: u8, bg: u8)`; mono and colour adapters both work via `crtcPort`, and under UEFI it renders to the framebuffer. `vga.emergency(s: &string)` writes directly with no state, using the `BootInfo` that start recorded; before that it assumes `0xB8000` |
| `serial` | `serial.init(b: &BootInfo)`, `serial.write(b: &BootInfo, s: &string)`, `serial.writeByte(b: &BootInfo, v: u8)`; 9600 8N1, bounded polling, a missing port never hangs; `serial.kind(): UartKind` is `None, Uart8250, Uart16550`, and reports `None` before start has recorded `BootInfo` |
| `idt` | `idt.init()`, `idt.set(vector: u8, h: InterruptHandler)`, `idt.enable()`, `idt.disable()`; PIC remapped to `0x20`/`0x28` with I/O delays; `idt.enable()` also re-enables NMI, which the boot stage masked |
| `pic`, `pit` | `pic.mask(irq)`, `pic.unmask(irq)`, `pic.eoi(irq)`; `pit.setHz(hz: u32)` |
| CPU | `halt(): never`; in namespace `cpu` of `os/none`: `cpu.withoutInterrupts(f: () => void)` (`pushfd; cli; ...; popfd`, uniprocessor only), `unsafe cpu.setStackLimit(addr: usize)`, `unsafe cpu.enableSse()`. A file needing both `cpu` namespaces writes `import { cpu as hw } from "os"` |

`os/uefi` adds `@abi("win64")` protocol types, `SystemTable`, and `exitBootServices` with map-key retry. It captures the firmware framebuffer before exit. Secure Boot must be off, because the output is unsigned.

### 8.5 Dev-only surface

- `@was("old")` on a type, field, variant or function carries identity across a rename during `enrang dev`; inert elsewhere.
- `@devMigrate function migrateX(old: { ... }): X` is a migration hook; the object type states the old schema and is checked against it. Stale hooks warn and are ignored. Production builds strip it, and a hook is not callable from code (EN1211). A hook takes only `old` and returns only the new value; if its reachable code contains user `unsafe`, a top-level `let` or a host call, it is EN1217.
- `HostCall` is a MIR statement legal only in `os/vm`, not user-visible. Library code reaches it through `@hostCall` declarations (section 3.1).
- `@owner` shapes declare ownership edges in `alloc`; user code cannot use them in the prototype (EN0806).

The sandbox, hot-reload and migration semantics are in the architecture document. Programs can observe only: capability failures as `Err(PermissionDenied)`, a virtual clock without `--allow-clock`, and the same stdout otherwise.

## 9. Runtime semantics

### 9.1 Panics

A panic never unwinds and never runs drops. Hosted default: writes the message to stderr and exits with status 101. VM in `dev`: pauses instead. Freestanding: calls `@panicHandler`.

Hosted format, exact:

```text
panic: index 2 is out of bounds for length 2
  --> server.en:18:3
stack:
  step (server.en:18:3)
  main (server.en:28:5)
```

The stack comes from the frame-pointer chain plus the `.enr.trace` table; `--trace=none` omits the stack and location, `--trace=fn` omits column and line for inner frames. `PanicInfo` exposes `get message(): &string`, `get file(): &string`, `get line(): u32`, `get column(): u32`.

| Message | Cause |
|---|---|
| `index I is out of bounds for length L` | Index or fixed-array access; negative `isize` included |
| `integer overflow: A OP B` | `+ - *`, negation of MIN, `abs(MIN)` (OP includes `neg`) |
| `division by zero` | `/ %` on integers |
| `integer overflow: MIN / -1` | Division or remainder of MIN by -1 |
| `shift count N out of range for BITS bits` | `<< >>` count negative or not below the width |
| `conversion out of range: V as T` | `as`, int to int or float to int (`NaN` prints) |
| `unexpected null` | `x!` |
| `slice index I is not a char boundary` | `string.slice`, `string.codePointAt` |
| `invalid byte B for a string` | `string.pushByte` with `B` from `0x80` up |
| `invalid code point C` | `string.pushCodePoint` |
| `capacity overflow`, `out of memory`, `allocator has no memory` | `alloc` |
| `stack overflow` | Prologue limit check on freestanding, guard page on hosted (hosted prints what the OS delivers) |
| `unreachable code reached`, `assertion failed: MSG` | `unreachable`, `assert` |
| user string | `panic` |

### 9.2 Integers

Checks are always on, in every build, with no flag to disable them. Arithmetic is two's complement. `+`, `-`, `*`, unary `-` and `abs` panic on overflow. Results of `wrapping*` are mathematically modulo 2^N. `>>` is arithmetic on signed and logical on unsigned types. `i64` and `u64` on `i386` behave identically to `x86_64`. `/` truncates toward zero; `%` has the sign of the dividend.

### 9.3 Floating point

**Strategies.** `soft` (Enrang's `core`, integer-only, default at the floor), `sse2` (default and only strategy on native `x86_64-*`, where `--float=soft` is EN0911 because every x86-64 CPU has SSE2; `--float=sse2` on `i386` needs `--cpu=sse2` or higher), `x87` (**deferred past M10**: `--float=x87` is EN1020).

**Guarantee across all implemented strategies and the VM, bit for bit:**

- `+ - * / %`, `sqrt`, and conversions round to nearest, ties to even, with no flush-to-zero and no denormals-are-zero. `%` is exact, computed like `fmod`, and truncates.
- Non-NaN results are bit-identical, including signed zeros, subnormals and infinities.
- NaN-ness is identical. A NaN's sign and payload are not specified; `toBits()` canonicalises every NaN to `0x7FF8000000000000` (`0x7FC00000` for `f32`), making them unobservable in safe code.
- Rounding mode and exception flags are not exposed. Traps are masked.
- Float moves use integer moves, so an sNaN value keeps its bits until an arithmetic operation.
- Comparison is IEEE: `NaN != NaN`; `-0 == +0`. `sin`, `exp` and the like are `core` Enrang code on top of these operations, therefore also identical.
- `f32` arithmetic is true binary32, never computed in higher precision observably.

Cost: on a 386 soft-float `f64` add is estimated at 1,500-3,000 clocks. It shields FDIV-flawed Pentiums by construction.

**x87, when it arrives, must meet the same guarantee:** FNINIT, FLDCW `0x027F`; memory-to-memory operations only, so no excess precision survives a statement; f64 add, sub, sqrt run directly; f64 mul, div use the strictfp scale pair (`2^-15360`, `2^15360`) to prevent double rounding in the subnormal range; f32 runs at PC=53 where double rounding is innocuous (53 >= 2·24+2); no FLD/FSTP moves. It may not ship until it passes the same bit vectors. Until then `asm` x87 forms exist only for probing and OS context switching (`fninit`, `fnstsw`, `fnstcw`, `fnsave`, `frstor`, `fwait`), tagged `fpu`.

## 10. CPU levels

### 10.1 The option

`--cpu=<level>` on `enrang build`, `run`, `test`. **A level is an optimisation, never a requirement.** Floor output (`i386`) runs on every listed chip, because x86 is backward compatible. Bitsets back the table; levels are named rungs over them. Default: `i386` on `i386-*`, `x86-64` on `x86_64-*`.

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
unsafe function fastMax(a: i32, b: i32): i32 {
  let r: i32 = a;
  asm(`cmp eax, ebx
       cmovl eax, ebx`, { in: { eax: a, ebx: b }, out: { eax: r } });
  return r;
}

function max(a: i32, b: i32): i32 {
  if (cpu.has("cmov")) { unsafe { return fastMax(a, b); } }
  return a > b ? a : b;
}
```

- `cpu.has(feature: &string): bool`, with `feature` a literal checked at compile time (EN0908): `fpu cpuid bswap cmpxchg xadd cmpxchg8b rdtsc msr cr4 cmov fcomi mmx 3dnow sse sse2 sse3 ssse3 sse4.1 sse4.2 popcnt fxsave nopl pae nx lm invlpg`. Cached after first use. CPUID has no bit for some of these; `ARCHITECTURE.md` section 8.3 defines them.
- **On freestanding targets, `cpu.has` means usable now.** For `fpu`, `sse*` and `fxsave` it is the CPUID bit, and CR0.EM clear, and for SSE also CR4.OSFXSR set. A guarded `@requires("sse2")` function therefore never takes `#UD`. At `--cpu=sse2` and above, startup always leaves EM clear and OSFXSR set, so the call folds to `true`. Below that level, `unsafe cpu.enableSse()` turns SSE on and refreshes the cache.
- `cpu.vendor(): &string`, `cpu.levelOf(): &string` give `"i386"`, `"i486"` and so on as detected.
- Detection: EFLAGS.AC toggle for 486+, EFLAGS.ID toggle for CPUID. FPU presence is FNINIT/FNSTSW on freestanding only, after clearing CR0.EM and CR0.TS, and on CPUs without CPUID it also requires CR0.ET, so a 287 counts as no FPU; `cpu.has("fpu")` on hosted `i386-linux` is true only if CPUID says so. CR4 is touched only when CPUID reports a CR4 feature. On `x86_64-*`, anything beyond the baseline uses CPUID.
- `@requires("f", ...)` adds features to the allowed set for that function's body, including `asm`; calling it needs `unsafe` (EN0907). A higher `--cpu` makes the attribute satisfied statically, so the call is still `unsafe` but `cpu.has` folds to `true`.

### 10.4 The floor island

Startup, the level check and panic printing are always compiled at `i386`, whatever `--cpu` says, and every function outside them sits at the target level. A startup path never has a form above the floor.

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

There is no silent CAS emulation. SMP below `i486` is unsupported. Freestanding uniprocessor code may use `cpu.withoutInterrupts` instead.

### 10.6 What "supported" means

The docs and `enrang targets --evidence` report four classes per CPU family, generated from test results: **C1** level-proven (encoder tags, assembler oracle, disassembly audit); **C2** run at that level on the development host, which proves the code rather than the chip; **C3** emulated, naming the model; **C4** real hardware. C4 exists only for the owner's Q8400, from the owner's report, and for the `Newer` row, where the i5-12400F development machine runs hosted output in user mode. Every other family reads `no hardware`, because the owner has no other old machines. No class is claimed before it is reached.

Compiled floor code avoids 386 errata by construction: no `popa`/`popad`, `enter`, `ud2`, or `loop`; panic stops with `int3` then a halt loop. Early 386s with the 32-bit multiply bug ("16 BIT S/W ONLY") and hardware-defective K6 steppings are unsupported.

**Size budgets** (enforced by tests from their milestone): stage 1 is 512 B including 350 B code, stage 2 at most 4 KB, hello kernel flat at most 16 KB running in 640 KB with no extended memory, hello ELF at most 12 KB on either Linux target, allocator at most 2 KB, soft-float at most 16 KB if referenced, full `core`+`alloc`+`os` without floats at most 32 KB, an allocator-using kernel fits a 2 MB machine.

## 11. Runtime data layout

Fixed by target pointer width `P` (4 on `i386-*`, 8 on `x86_64-*`). Stated offsets are normative and conformance-tested via `sizeOf`, `alignOf`, `offsetOf`.

| Type | Size | Align |
|---|---|---|
| `bool`, `i8`, `u8` | 1 | 1 |
| `i16`, `u16` | 2 | 2 |
| `i32`, `u32`, `f32` | 4 | 4 |
| `i64`, `u64`, `f64` | 8 | 4 when `P == 4`, 8 when `P == 8` |
| `isize`, `usize`, `&T`, `&mut T`, `*T`, `*mut T`, `fn(...)`, `Box<T>` | `P` | `P` |
| closure parameter | `2P` (code, env), stack only | `P` |
| `Atomic64` | 8 | 8 |
| `void`, `never` | 0 | 1 |

**Size limits.** No type or static may exceed `isize.MAX` bytes of the target, no stack frame may exceed `2^31 - 1` bytes, and an image on a RIP-relative target may not span more than `2^31 - 1` bytes. A `T[N]` may not have `N` above `isize.MAX`, whatever the size of `T`, so `.length` always fits. Violations are EN0435: `u8[3000000000]` on `i386`, `u64[536870912]` whose size would wrap to 0, a 3 GB local on `x86_64`. Sizes never wrap. EN0435 fires at layout, at mono for sizes that depend on an instantiation (`class A<T> { a: T[65536]; b: T[65536]; }` with `A<A<u64>>`), and at link for a relocation that does not fit.

**`string`**: `{ ptr: *u8 @0, len: usize @P, cap: usize @2P }`, size `3P`, align `P`. `cap == 0` means `ptr` is static or dangling and drop does nothing. Bytes are UTF-8, no terminator. A literal `&string` is a pointer to such a descriptor in read-only data.

**`T[]`**: `{ ptr: *mut T @0, len: usize @P, cap: usize @2P }`, size `3P`. `len`, `cap` count elements. An empty array holds no allocation. Zero-sized `T` never allocates and has `cap` equal to the maximum `usize`, with `len` still limited to `isize.MAX` (8.3).

**`T[N]`**: `N` consecutive elements with no header, size `N * sizeOf<T>()`, align of `T`. References and iteration carry the static length.

**Classes**: fields in declaration order, each at the next offset aligned for it; size rounded up to the class's alignment, the maximum of field alignments and 1. `@packed`: no padding, align 1. `@align(n)`: raises alignment and rounds size. There is no header, vtable or identity.

**Enums**: tag at offset 0, payload at the next offset aligned for the largest variant alignment; a variant's payload fields are laid out as a class beginning there; size is rounded up to the enum's alignment, the maximum of 4 and all payload alignments.

- Tag type is `u32` by default, so the alignment is at least 4. Tags number variants from 0 in declaration order, regardless of value. Exception: `@repr("u8")` on payload-free enums uses that size, and the tag equals the discriminant.
- Payload-free enums: size 4, align 4 by default, and the tag equals the discriminant.
- **`T | null`**: tag 0 means null, tag 1 means present, same layout rule. **No niche optimisation**: `&T | null` is `2P` on the stack, `Box<T> | null` is `2P`, unlike Rust. Raw pointers are the nullable word.
- `Result<T, E>`: `Ok` tag 0, `Err` tag 1, payload as above.

**Worked sizes:**

| Type | `P == 4` | `P == 8` |
|---|---|---|
| `string` | 12 | 24 |
| `i64[]` | 12 | 24 |
| `i64 \| null` | 12 | 16 |
| `class Player { name: string; score: i64; }` | 20 | 32 |
| same with `level: i32` added | 24 | 40 |
| `enum Token { Num(i64), Add, Bad { text: string } }` | 16 | 32 |
| `@packed class GdtPointer { limit: u16; base: u32; }` | 6 | 6 |

**Calling conventions** are unstable and internal: i386 pushes all arguments right to left and the callee pops; x86-64 uses `rdi, rsi, rdx, rcx, r8, r9` and `xmm0-7`; aggregates pass by pointer to caller-owned memory and return through a hidden pointer. Foreign ABI appears only through `@abi` and `@dll`. No target uses a red zone, so interrupts on the current stack are always safe.

## 12. Testing

`test`, `describe`, `expect` and the matchers are compiler forms, not library functions: a by-value `expect` would move its operand, R1 forbids a matcher object holding `&T`, and there are no top-level statements to register tests at run time. They lower to ordinary MIR.

```ts
// src/stack.test.en: an extra part of module src/stack.en, so private members are visible
function twoUsers(): Stack<User> {            // a fixture is a function; teardown is Drop
  let s = new Stack<User>();
  s.push(User { name: "Ada", age: 36 });
  s.push(User { name: "Grace", age: 85 });
  return s;
}

class Case { input: string; want: i64; }

describe("Stack", () => {
  test("pop is LIFO", () => {
    let s = twoUsers();
    expect(s.pop()).toBe(User { name: "Grace", age: 85 });
    expect(s.size).toBe(1);
  });

  test("top borrows", () => {
    const s = twoUsers();
    expect(s.top()).not.toBeNull();           // `&User | null`, compared through the reference
    expect(s).toMatchSnapshot();              // `s` is only borrowed
  });

  test.each("parses", () => [Case { input: "1", want: 1 }, Case { input: "x", want: 0 }],
    (c: &Case) => { expect(c.input.parseInt() ?? 0).toBe(c.want); });

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
- A `describe` body contains only `describe`, `test`, `compileFails`, `compileOk` (EN1102). `beforeEach`, `afterEach`, `beforeAll`, `afterAll` get EN1105 with a helper-function fix-it.
- A test is declared at the top level or in a `describe`, neither of which admits locals, so its arrow has nothing to capture; a `test` declared inside a function is EN1110. Fixtures are functions. The arrow returns `void` unless annotated: `(): Result<void, string> => { const v = parse("1")?; return Ok(); }`. An `Err` fails the test and prints the error, and `?` and `return` act on the arrow.
- `test.only`, `test.skip`, `test.todo` have the obvious meanings; `--ci` refuses `only` (EN1106) and never writes new snapshots. `test.panics(name, substring, body)` passes iff the body panics with that substring.
- `test.each(name, cases, body)` runs `body` once per element with a `&Case`. Each case has the ID `parses[2]`, zero-based, known at run time; `-t` filters on it. Fuel and leak balance are per case. The generator must be deterministic, because a native run re-runs it to resume after a panic. The final `Tests` line counts cases.
- Options: `{ fuel: n, memory: "64MB", allow: ["read:fixtures/"] }`. Only a literal `ObjectLit`. `allow` may name only paths inside the project root, after canonicalisation and with `..` rejected (EN1111); anything wider needs a command-line grant such as `--allow-read=`, so source code cannot widen its own sandbox. `--ci` prints the effective grants.

### 12.2 `expect`

`expect(a).matcher(b);` is a statement. It lowers to `&a`, `&b`, a call to compiler-derived `__eq<T>`, and a cold branch to `__fail`. These are real shared borrows for one statement, so a live `&mut` still gets EN0708. Rvalues become temporaries dropped at statement end. With no unwinding, a failed `expect` ends the test with no drops; the VM discards the heap, and a native process dies and is resumed at the next test by the parent.

`__eq<T>` is derived deep structural equality. A user's `Eq` is never consulted, so code under test does not grade itself. Floats follow `Object.is`: `+0` differs from `-0`, `NaN` equals `NaN`. Matchers peel one `&` and one `| null` from the actual type (R2 caps the depth), and literals adapt to the inner type. `__show<T>` is derived printing that does not allocate: tagged records on a framed channel (host call in the VM, fd 3 on Linux, stderr on Windows, COM1 freestanding), rendered by the parent, so reporting cannot disturb allocation counts.

| Group | Matchers (all accept `.not`) |
|---|---|
| Equality | `toBe(v)` |
| Bool | `toBeTrue()`, `toBeFalse()` |
| Null, Result | `toBeNull()`, `toBeOk(v?)`, `toBeErr(v?)` |
| Enums | `toMatchPattern(Pattern)`, lowered to `match` |
| Order | `toBeGreaterThan`, `toBeGreaterThanOrEqual`, `toBeLessThan`, `toBeLessThanOrEqual` |
| Floats | `toBeCloseTo(v, eps)`, `toBeNaN()`, `toHaveBits(bits)` (compares `toBits()`) |
| Containers, strings | `toHaveLength(n)`, `toContain(x)`, `toStartWith(s)`, `toEndWith(s)` |
| Snapshots | `toMatchSnapshot()`, `toMatchInlineSnapshot(raw`...`)` |

Jest arrivals get EN1104: `toEqual`, `toStrictEqual` get a rename fix-it to `toBe`, `toBeTruthy` explains there is no truthiness, `toThrow` points to `test.panics`, `toHaveBeenCalled` suggests injecting through `T extends Clock`. `expect` outside a test is EN1101; `const e = expect(x)` is EN1103.

### 12.3 Compile-error tests

```ts
compileFails("use after move", raw`
  class U { name: string; }
  function take(u: U): void {}
  function main(): void {
    const u = U { name: "Ada" };
    take(u);
    console.log(u.name); //~ EN0601
  }
`);

compileFails("bswap above the floor", raw`
  //! target: i386-none, cpu: i386
  function f(): void { unsafe { asm("bswap eax"); } } //~ EN0901
`);

compileOk("borrow ends at last use", raw`...`);
```

The embedded compiler runs these in the runner at discovery, identically for any test target. The set of (line, code) pairs must match exactly, so a snippet cannot pass because of an unrelated typo. The set includes warnings. `compileFails` needs at least one anchor on an `E` code. `compileOk` may carry anchors, only for `W` codes. Any mismatch is EN1107. `//~ EN0601 "substring"` also checks the message. `//!` sets `target`, `cpu`, `float`. `{ snapshot: true }` stores the rendered diagnostic; `{ fixes: true }` applies fix-its and requires the result to compile, and warnings in the fixed program are accepted. Snippets containing backticks live in `name.fail.en` beside the test file with the same anchors, and are discovered automatically.

### 12.4 Runner

- **VM by default.** One worker per core; the front end runs once per file, MIR is shared. Each test gets a fresh heap and globals image. Fuel: one unit is one MIR statement or terminator, default 200 million per test; running out is T0004. No wall clock, so timeouts never flake. No capabilities, a virtual clock, a per-test temp directory unless granted.
- **Native on request:** `enrang test --target=<t> --cpu=<l>`, or `--matrix` for every runnable cell. Each test file is one binary with a static test table. A panic or timeout kills only that process; the parent resumes at the next test. Wall-clock watchdog 10 s. `--isolate=test` respawns per test. `--shuffle=<seed>`.
- **Leaks.** The VM tracks every allocation; native compares `core` allocator counters around each test. A passing test must balance (T0003). Failed tests are exempt, because no drops ran. A leak in a test reaching no user `unsafe` is labelled a compiler bug.
- **Filters:** paths, `-t "Stack > pop"` (substring, `*`), `--only-failed`, `--bail`. **Reporters:** `pretty`, `dots`, `json` (versioned NDJSON), `junit`. Reporter output, including `fail[...]` blocks, goes to stdout; compile diagnostics go to stderr. `-u` updates snapshots; `__snapshots__/` sits beside the test file. `--watch` polls mtimes. `--coverage` is deferred (EN1041).
- **`native-only` tests.** Tests reaching `asm` or port I/O through the monomorphised call graph are counted separately in the VM; `--strict` fails them (EN1201).
- **Stripping.** `build`, `run` and `dev` drop test items after parsing; `__eq`, `__show` exist only in test builds. A file with tests appended builds byte-identical to the file without them.

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

## 13. Diagnostics

### 13.1 Rendered format

Output goes to stderr, deterministic, UTF-8, no colour unless a TTY and `--color=auto`. Exact shape:

```text
error[EN0601]: `u` is used after it was moved
 --> moved.en:6:15
  |
4 |   const u = new User("Ada");
  |         - `u` owns this `User`, which is not Copy
5 |   archive(u);
  |           - moved here: `archive` takes `u: User` by value
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
- A compile stops at the end of the first failing phase in this order: 1 lexical and syntax, 2 resolve and types, 3 moves and borrows, 4 level and layout, 5 reachability. Each phase reports all its errors with recovery. Phase 5 includes root collection (EN0310, EN0809). `build`, `run` and `dev` always run it. `check` and compile tests run it only if a root exists, so a file with no `main` or `@entry` is checked as a library.

`enrang explain <code>` prints the title, the rule, a failing example, a fixed example (both compiled by a meta-test for `Compile` codes, a transcript otherwise) and the TS perspective where relevant. Unknown code gets "did you mean".

### 13.2 Catalog

Each row reads `code severity phase owner since fixture title`. Severity is `E` error, `W` warning or `F` test verdict. Phase is the one in 13.1, with `0` for the command line and `R` for run time or reload. `owner` is the crate family that reports the code. `since` is the milestone that must make it fire. `fixture` says how its firing test runs: `Compile` (anchored source), `Cli` (a command), `Reload` (a dev scenario) or `TestRun` (a test-runner run).

`define_codes!` is generated from this table at M0. Meta-tests enforce only rows whose `since` has been reached (`TESTING.md` section 18). A `Compile` row has a firing fixture, a passing near-miss and an explain page whose examples compile; the other kinds have a firing scenario and an explain page with a transcript. Codes are never reused. EN0704 is retired: R3's rule 4 with EN0710 and EN0712 covers what it named.

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
EN0105 E 1 syntax M1 Compile assignment or `++` used as an expression
EN0106 E 1 syntax M1 Compile `??` mixed with `||` or `&&` without parentheses
EN0107 E 1 syntax M1 Compile chained comparison
EN0108 E 1 syntax M1 Compile decorator cannot appear here
EN0109 E 1 syntax M1 Compile item not allowed at this position
EN0110 E 1 syntax M1 Compile `import` after an item
EN0111 E 1 syntax M1 Compile `break` or `continue` outside a loop, or crossing an arrow
EN0112 E 1 syntax M1 Compile unknown label
EN0113 E 1 syntax M1 Compile duplicate label
EN0114 E 1 syntax M1 Compile invalid assignment target

EN0201 E 1 syntax M1 Compile `===` or `!==`: use `==` and `!=`
EN0202 E 1 syntax M1 Compile `var`: use `let` or `const`
EN0203 E 2 sema M2 Compile no truthiness: a condition must be `bool`
EN0204 E 1 syntax M1 Compile `class ... extends`: no inheritance
EN0205 E 1 syntax M1 Compile `any`: use a generic or enum
EN0206 E 1 syntax M1 Compile `undefined`: use `null`
EN0207 E 1 syntax M1 Compile `throw`, `try`, `catch`: use `Result`, `?`, `panic`
EN0208 E 1 syntax M1 Compile `>>>`: `>>` is logical on unsigned types
EN0209 E 1 syntax M1 Compile `switch`: use `match`
EN0210 E 1 syntax M1 Compile `unknown`: use a generic
EN0211 E 1 syntax M1 Compile `typeof`, `instanceof`: use an enum and `match`
EN0212 E 1 syntax M1 Compile `protected`, `abstract`, `super`: no inheritance
EN0213 E 1 syntax M1 Compile `using`: every binding already drops; implement `Drop`
EN0214 E 1 syntax M1 Compile `readonly T` as a type: use `&T`
EN0215 E 1 syntax M1 Compile union of object types: declare a class or enum
EN0216 E 1 syntax M1 Compile string-literal union: use a payload-free enum
EN0217 E 1 syntax M1 Compile object literal without a class name
EN0218 E 1 syntax M1 Compile `function` expression: use an arrow
EN0219 E 2 sema M2 Compile `this` outside a method
EN0220 E 1 syntax M1 Compile `interface ... extends`: list bounds with `&`
EN0221 E 2 sema M2 Compile `new` on a non-class
EN0222 E 1 syntax M1 Compile `namespace`, `delete`: not in Enrang
EN0223 E 1 syntax M1 Compile `x?: T` optional field: use `x: T | null = null`

EN0301 E 2 sema M2 Compile unresolved name
EN0302 E 2 sema M2 Compile unresolved type
EN0303 E 2 sema M2 Compile no such member
EN0304 E 2 sema M2 Compile import cycle
EN0305 E 2 sema M2 Compile import path not found
EN0306 E 2 sema M2 Compile name is not exported
EN0307 E 2 sema M2 Compile duplicate definition
EN0308 E 2 sema M2 Compile private member
EN0309 E 2 sema M2 Compile wrong number of type arguments
EN0310 E 5 driver M4 Cli no `main` on a hosted target

EN0401 E 2 sema M2 Compile mismatched types
EN0402 E 2 sema M2 Compile mixed numeric types
EN0403 E 2 sema M2 Compile operator needs integer types
EN0404 E 2 sema M2 Compile invalid `as`
EN0405 E 2 sema M2 Compile index must be `isize` or `usize`
EN0406 E 2 sema M2 Compile union other than `T | null`
EN0407 E 2 sema M2 Compile single object type outside `@devMigrate`
EN0408 E 2 sema M2 Compile recursive type needs `Box`
EN0409 E 2 sema M2 Compile missing annotation on a parameter or field
EN0410 E 2 sema M2 Compile cannot infer type
EN0411 E 2 sema M2 Compile literal does not fit
EN0412 E 2 sema M2 Compile constant evaluation failed, or constant cycle
EN0413 E 2 sema M2 Compile `?.` on an owned rvalue
EN0414 E 5 mono M4 Compile monomorphisation depth above 64
EN0415 E 2 sema M2 Compile compile-time assert failed
EN0416 E 2 sema M2 Compile class does not satisfy `implements`
EN0417 E 2 sema M2 Compile field in an interface
EN0418 E 2 sema M2 Compile invalid `implements Copy`
EN0419 E 2 sema M2 Compile type argument does not satisfy a bound, or sealed bound implemented
EN0420 E 2 sema M2 Compile operator not applicable to these types
EN0421 E 2 sema M2 Compile `==` needs `Eq`
EN0422 E 2 sema M2 Compile assigning `T` to a `&mut T` local
EN0423 E 2 sema M2 Compile wrong argument count
EN0424 E 2 sema M2 Compile `?` in a function that does not return `Result` or nullable
EN0425 E 2 sema M2 Compile `?` error type differs
EN0426 E 2 sema M2 Compile unused `Result`
EN0427 E 2 sema M2 Compile missing return
EN0428 E 2 sema M2 Compile not callable
EN0429 E 2 sema M2 Compile `?` on a type other than `Result` or nullable
EN0430 W 2 sema M2 Compile integer division truncates
EN0431 W 2 sema M2 Compile `string.length` counts bytes
EN0432 E 2 sema M2 Compile ternary or arm types differ
EN0433 E 2 sema M2 Compile missing class field in a literal
EN0434 E 2 sema M2 Compile unknown field in a literal
EN0435 E 4 layout M2 Compile type, frame or static too large for the target (also phase 5 and link)
EN0436 E 2 sema M2 Compile invalid `main` signature
EN0437 E 2 sema M2 Compile recursive type alias
EN0438 E 2 sema M2 Compile spread source is not an array of cloneable elements

EN0501 E 2 sema M2 Compile non-exhaustive `match`
EN0502 E 2 sema M2 Compile unqualified variant in a pattern
EN0503 W 2 sema M2 Compile unreachable arm
EN0504 E 2 sema M2 Compile pattern does not match the scrutinee type
EN0505 E 2 sema M2 Compile or-pattern with bindings
EN0506 E 2 sema M2 Compile refutable pattern in a destructuring

EN0601 E 3 borrowck M3 Compile use after move
EN0602 E 3 borrowck M3 Compile use before assignment
EN0603 E 3 borrowck M3 Compile move through a reference
EN0604 E 3 borrowck M3 Compile move out of an array element
EN0605 E 3 borrowck M3 Compile move out of `*box`
EN0606 E 2 sema M2 Compile the `drop` method called, or declared in an interface
EN0607 E 3 borrowck M3 Compile partial move from a `Drop` type
EN0608 E 3 borrowck M3 Compile mutating through `const`
EN0609 E 3 borrowck M3 Compile writing a `readonly` field
EN0610 E 3 borrowck M3 Compile `this` used before all fields are assigned
EN0611 E 3 borrowck M3 Compile moved in a previous loop iteration
EN0612 E 2 sema M2 Compile missing `&mut` at a call
EN0613 E 3 borrowck M3 Compile second assignment to `const`
EN0614 E 3 borrowck M3 Compile `mut` method called through `&` or on `const`
EN0615 E 3 borrowck M3 Compile method writes `this` but is not `mut`
EN0616 E 3 borrowck M3 Compile writing through `&T`, or rebinding a captured reference
EN0617 E 3 borrowck M3 Compile closure moves a capture

EN0701 E 2 sema M2 Compile reference type in a field, element, payload or generic argument
EN0702 E 2 sema M2 Compile reference to a reference
EN0703 E 2 sema M2 Compile type parameter bound to a reference
EN0705 E 2 sema M2 Compile closure type or arrow outside a call argument, or nested closure type
EN0706 E 3 borrowck M3 Compile mutated while shared-borrowed
EN0707 E 3 borrowck M3 Compile second exclusive borrow
EN0708 E 3 borrowck M3 Compile read while exclusively borrowed
EN0709 E 3 borrowck M3 Compile moved while borrowed
EN0710 E 3 borrowck M3 Compile returning a reference to local data
EN0711 E 3 borrowck M3 Compile dropped while borrowed
EN0712 E 3 borrowck M3 Compile temporary dropped while borrowed
EN0714 E 3 borrowck M3 Compile returned reference from a parameter outside the signature's sources
EN0715 E 3 borrowck M3 Compile closure capture conflicts with a live borrow
EN0716 E 2 sema M2 Compile `from` names a non-reference
EN0718 E 3 borrowck M3 Compile closure used re-entrantly: called, forwarded or captured twice
EN0719 W 3 borrowck M3 Compile `for...of` source can change inside the loop

EN0801 E 2 sema M2 Compile operation needs `unsafe`
EN0802 E 2 sema M2 Compile invalid type for a top-level `let`
EN0803 E 2 sema M2 Compile function with preconditions used as a safe `fn` or closure
EN0804 E 4 borrowck M3 Compile reference to a misaligned packed field
EN0805 E 2 sema M2 Compile volatile access on a type outside `VolatileValue`
EN0806 E 2 sema M2 Compile unknown or misapplied decorator, or library-only form in user code
EN0807 E 2 sema M2 Compile calling an interrupt handler
EN0808 E 2 sema M2 Compile invalid interrupt signature
EN0809 E 5 driver M9 Compile missing or invalid `@entry`
EN0810 E 2 sema M2 Compile `&T` cast to `*mut T`
EN0811 E 2 sema M9 Compile second `@panicHandler`
EN0812 E 5 mono M9 Compile missing `@panicHandler`
EN0813 E 5 link M9 Compile `@at` overlap
EN0814 E 2 sema M2 Compile section not allowed on this target, or reserved
EN0815 E 2 sema M2 Compile `declare function` without `@dll`
EN0816 E 2 sema M2 Compile `string` or `T[]` in FFI
EN0817 E 2 sema M2 Compile conflicting layout attributes
EN0819 E 2 sema M2 Compile unknown `@abi`
EN0820 E 5 mono M9 Compile allocation with no global allocator
EN0821 E 2 sema M4 Compile second `@globalAllocator`
EN0822 E 2 sema M4 Compile allocator type lacks `GlobalAllocator`
EN0823 E 5 mono M9 Compile `os` hosted API on a freestanding target
EN0824 E 5 mono M9 Compile allocation reachable from an interrupt handler, panic handler or the allocator
EN0825 E 2 sema M4 Compile `@globalAllocator` and `unsafe let` must appear together
EN0826 E 2 sema M2 Compile `@packed` field must be Copy and non-generic

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
EN1006 E 2 sema M2 Compile dynamic dispatch
EN1007 E 2 sema M2 Compile capturing arrow as a function pointer
EN1008 E 1 syntax M1 Compile match guards and range patterns
EN1009 E 1 syntax M1 Compile unsupported module form
EN1010 E 1 syntax M1 Compile tuples and array destructuring
EN1011 E 2 sema M2 Compile slices
EN1012 E 2 sema M2 Compile `Map` and `Set`
EN1013 E 1 syntax M1 Compile spread outside an array literal, and rest
EN1014 E 2 sema M2 Compile unsupported generic feature
EN1015 E 2 sema M2 Compile unsupported `for...of` source
EN1016 E 1 syntax M1 Compile default parameters and overloads
EN1017 E 1 syntax M1 Compile setters
EN1018 E 1 syntax M1 Compile operator overloading
EN1019 E 2 sema M2 Compile character type
EN1020 E 0 target M1 Cli x87 float strategy
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
EN1040 E 2 sema M2 Compile string-valued enums
EN1041 E 0 cli M1 Cli `--multiboot`, `--coverage`

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
EN1217 E R dev M6 Reload migration hook reaches user `unsafe`, a top-level `let` or a host call

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

`EN1301` covers `install`, `add`, `publish`, `doc`, `lsp`, `repl`, `bench`, `debug`, `upgrade` and `fmt`. `EN1302` carries the aliases `tsc`, `lint` to `check`, `compile` to `build`, `start` to `run`. Section 16 gives the message head and help of each EN10xx row.

Exit codes: 0 success, 1 compile errors, failed tests or lost output, 2 usage, 3 internal compiler error. Lost output means a write to stdout or stderr failed during a run that had otherwise succeeded. A reader that closed its pipe, as in `enrang targets | head -n 1`, is not lost output, and a run that already failed keeps its status.

## 14. Golden diagnostics

Each case is a source file, a command, and the full stderr. The marker gives the exit status: 1 for a compile error, and 0 for a program with warnings alone. These become byte-exact golden tests. Source files end with one newline.

**Case markers.** Every extracted case in sections 1, 14 and 15 starts with `<!-- case: ID files=a.en,b.en cmd="..." exit=N [stdout=block|inline] [stderr=block|inline] [serial=block] -->`. The `ts` blocks after the marker are the source files, in `files` order. The `text` blocks after them are the expected outputs, in the order stdout, stderr, serial. `inline` means the expectation is in the code spans of the next sentence that names that stream. A stream the marker does not name is expected to be empty, except that a `dev` or `build` command may also write its artefact. The extractor reads markers and blocks only, and no prose except the one sentence an `inline` stream names. In that sentence `Output:` means stdout, and each code span is one line ending in a newline. A meta-test requires every `G` and `S` heading to have a marker.

### G01 Missing semicolon

<!-- case: G01 files=g01.en cmd="enrang check g01.en" exit=1 stderr=block -->
```ts
function main(): void {
  const x = 1
  console.log(x);
}
```

`enrang check g01.en`

```text
error[EN0101]: missing `;` after this statement
 --> g01.en:2:14
  |
2 |   const x = 1
  |              ^ expected `;` here
  |
  = from TypeScript: Enrang has no automatic semicolon insertion.
help: add the semicolon
  |
2 |   const x = 1;
  |              +
  = explain: run `enrang explain EN0101`

error: aborting due to 1 previous error
```

### G02 Unclosed brace

<!-- case: G02 files=g02.en cmd="enrang check g02.en" exit=1 stderr=block -->
```ts
function main(): void {
  if (true) {
    console.log("hi");
}
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
function main(): void {
  const n = 3;
  if (n === 3) {
    console.log("three");
  }
}
```

`enrang check g03.en`

```text
error[EN0201]: `===` does not exist in Enrang
 --> g03.en:3:9
  |
3 |   if (n === 3) {
  |         ^^^ use `==` here
  |
  = from TypeScript: `==` never coerces in Enrang, so the strict form is the only form.
help: replace `===` with `==`
  |
3 |   if (n == 3) {
  |         ~~
  = explain: run `enrang explain EN0201`

error: aborting due to 1 previous error
```

### G04 TS habits: `any`, `var`, `undefined`

<!-- case: G04 files=g04.en cmd="enrang check g04.en" exit=1 stderr=block -->
```ts
function show(x: any): void {
  var y = undefined;
}
```

`enrang check g04.en`

```text
error[EN0205]: `any` does not exist in Enrang
 --> g04.en:1:18
  |
1 | function show(x: any): void {
  |                  ^^^ every value has one known type
  |
help: accept every type with a generic
  |
1 | function show<T extends Display>(x: &T): void {
  |              +++++++++++++++++++    ~~
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
function area(w: i64, h: i64): i64 {
  return w * h;
}

function main(): void {
  const a: string = area(2, 3);
  console.log(a);
}
```

`enrang check g05.en`

```text
error[EN0401]: mismatched types: expected `string`, found `i64`
 --> g05.en:6:21
  |
6 |   const a: string = area(2, 3);
  |                     ^^^^^^^^^^ this is `i64`
  |            ------ `string` is required by this annotation
  |
  = note: Enrang never converts between numbers and strings implicitly.
help: convert it explicitly
  |
6 |   const a: string = area(2, 3).toString();
  |                               +++++++++++
  = explain: run `enrang explain EN0401`

error: aborting due to 1 previous error
```

### G06 Did you mean

<!-- case: G06 files=g06.en cmd="enrang check g06.en" exit=1 stderr=block -->
```ts
function main(): void {
  const total = 10;
  console.log(totl);
}
```

`enrang check g06.en`

```text
error[EN0301]: cannot find `totl` in this scope
 --> g06.en:3:15
  |
2 |   const total = 10;
  |         ----- a local with a similar name is declared here
3 |   console.log(totl);
  |               ^^^^ not found
  |
help: did you mean `total`?
  |
3 |   console.log(total);
  |               ~~~~~
  = explain: run `enrang explain EN0301`

error: aborting due to 1 previous error
```

### G07 Use after move

<!-- case: G07 files=g07.en cmd="enrang check g07.en" exit=1 stderr=block -->
```ts
class User {
  constructor(public name: string) {}
}

function archive(u: User): void {
  console.log(u.name);
}

function main(): void {
  const u = new User("Ada");
  archive(u);
  console.log(u.name);
}
```

`enrang check g07.en`

```text
error[EN0601]: `u` is used after it was moved
  --> g07.en:12:15
   |
10 |   const u = new User("Ada");
   |         - `u` owns this `User`, which is not Copy because it has a `string` field
11 |   archive(u);
   |           - moved here: `archive` takes `u: User` by value
12 |   console.log(u.name);
   |               ^ used here, after the move
   |
   = from TypeScript: both names would share one object. In Enrang a value has one owner, so passing `u` hands it over.
help: `archive` only reads `u`, so borrow it instead
   |
 5 | function archive(u: &User): void {
   |                     +
help: or pass a copy
   |
11 |   archive(u.clone());
   |            ++++++++
   = explain: run `enrang explain EN0601`

error: aborting due to 1 previous error
```

### G08 Mutation during iteration

<!-- case: G08 files=g08.en cmd="enrang check g08.en" exit=1 stderr=block -->
```ts
function main(): void {
  let queue = ["a", "b"];
  for (const job of queue) {
    if (job == "a") {
      queue.push("retry");
    }
    console.log(job);
  }
}
```

`enrang check g08.en`

```text
error[EN0706]: `queue` cannot change while `job` still points into it
 --> g08.en:5:7
  |
3 |   for (const job of queue) {
  |              --- `job` points into `queue` for this turn
4 |     if (job == "a") {
5 |       queue.push("retry");
  |       ^^^^^^^^^^^^^^^^^^^ `push` is a `mut` method, so it needs exclusive access to `queue`
6 |     }
7 |     console.log(job);
  |                 --- `job` is used again here
  |
  = why: `push` may move the array to a bigger block of memory, leaving `job` pointing at freed memory.
  = rule: a value has many shared borrows or one exclusive borrow, never both.
help: to loop over the items as they are now, iterate over a copy
  |
3 |   for (const job of [...queue]) {
  |                     ++++     +
help: or keep a clone of `job` from before the change
  |
4 +     const saved = job.clone();
7 |     console.log(saved);
  |                 ~~~~~
  = explain: run `enrang explain EN0706`

error: aborting due to 1 previous error
```

### G09 Two exclusive borrows

<!-- case: G09 files=g09.en cmd="enrang check g09.en" exit=1 stderr=block -->
```ts
function swapFirst(a: &mut i64[], b: &mut i64[]): void {
  const t = a[0];
  a[0] = b[0];
  b[0] = t;
}

function main(): void {
  let xs = [1, 2];
  swapFirst(&mut xs, &mut xs);
}
```

`enrang check g09.en`

```text
error[EN0707]: cannot borrow `xs` as exclusive twice at the same time
 --> g09.en:9:22
  |
9 |   swapFirst(&mut xs, &mut xs);
  |                      ^^^^^^^ second exclusive borrow
  |             ------- first exclusive borrow, still live until the call returns
  |
  = rule: a value has many shared borrows or one exclusive borrow, never both.
help: to exchange two elements of one array, use `xs.swap(i, j)`
  = explain: run `enrang explain EN0707`

error: aborting due to 1 previous error
```

### G10 Dangling reference: returning a local

<!-- case: G10 files=g10.en cmd="enrang check g10.en" exit=1 stderr=block -->
```ts
function longest(): &string {
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
1 | function longest(): string {
  |                     ~~~~~~
3 |   return s;
  |          ~
  = explain: run `enrang explain EN0710`

error: aborting due to 1 previous error
```

### G11 Dangling reference: inner scope

<!-- case: G11 files=g11.en cmd="enrang check g11.en" exit=1 stderr=block -->
```ts
function main(): void {
  const fallback = "none";
  let r: &string = fallback;
  {
    const s = "a" + "b";
    r = &s;
  }
  console.log(r);
}
```

`enrang check g11.en`

```text
error[EN0711]: `s` is dropped while `r` still borrows it
 --> g11.en:7:3
  |
5 |     const s = "a" + "b";
  |           - `s` lives until the end of this block
6 |     r = &s;
  |         -- shared borrow of `s` starts here, held by `r`
7 |   }
  |   ^ `s` is dropped here
8 |   console.log(r);
  |               - the borrow is still in use here
  |
help: declare `s` outside the block so it lives as long as `r`
  = explain: run `enrang explain EN0711`

error: aborting due to 1 previous error
```

### G12 Non-exhaustive match

<!-- case: G12 files=g12.en cmd="enrang check g12.en" exit=1 stderr=block -->
```ts
enum Shape {
  Circle(f64),
  Square(f64),
  Empty,
}

function area(s: &Shape): f64 {
  return match (s) {
    Shape.Circle(r) => 3.14 * r * r,
    Shape.Square(a) => a * a,
  };
}
```

`enrang check g12.en`

```text
error[EN0501]: this `match` does not handle every `Shape`
  --> g12.en:8:17
   |
 4 |   Empty,
   |   ----- `Shape.Empty` is declared here
...
 8 |   return match (s) {
   |                 ^ missing `Shape.Empty`
   |
help: add the missing arm
   |
11 +     Shape.Empty => panic("unhandled"),
   = explain: run `enrang explain EN0501`

error: aborting due to 1 previous error
```

### G13 Unsafe misuse

<!-- case: G13 files=g13.en cmd="enrang check g13.en" exit=1 stderr=block -->
```ts
const VGA = 0xB8000 as *mut u16;

function main(): void {
  VGA.writeVolatile(0x0741);
}
```

`enrang check g13.en`

```text
error[EN0801]: writing through a raw pointer needs `unsafe`
 --> g13.en:4:3
  |
4 |   VGA.writeVolatile(0x0741);
  |   ^^^^^^^^^^^^^^^^^^^^^^^^^ `writeVolatile` dereferences `VGA`, a `*mut u16`
  |
  = rule: `unsafe` grants exactly five powers; this one is "dereference a raw pointer". Nothing checks the address for you.
help: state that you have checked the address
  |
4 |   unsafe { VGA.writeVolatile(0x0741); }
  |   +++++++++                          ++
  = explain: run `enrang explain EN0801`

error: aborting due to 1 previous error
```

### G14 Allocation on a freestanding target

<!-- case: G14 files=g14.en cmd="enrang build --target=i386-none g14.en" exit=1 stderr=block -->
```ts
@entry function kmain(boot: &BootInfo): never {
  let names: string[] = [];
  names.push("ada");
  halt();
}

@panicHandler function onPanic(info: &PanicInfo): never {
  halt();
}
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
1 + @globalAllocator unsafe let heap: FreeListHeap;
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

function main(): void {
  console.log(swap32(1));
}
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
function main(): void {
  const xs: i64[] = [];
  xs.push(1);
  console.log(xs.length);
}
```

`enrang check g16.en`

```text
error[EN0614]: `xs` is `const`, so `push` cannot change it
 --> g16.en:3:3
  |
2 |   const xs: i64[] = [];
  |         -- declared `const` here: immutable all the way down
3 |   xs.push(1);
  |   ^^^^^^^^^^ `push` is a `mut` method
  |
  = from TypeScript: a TS `const` only freezes the binding. In Enrang values have no shared identity, so `const` freezes the value.
help: make the binding mutable
  |
2 |   let xs: i64[] = [];
  |   ~~~
  = explain: run `enrang explain EN0614`

error: aborting due to 1 previous error
```

### G17 Missing `&mut` at the call

<!-- case: G17 files=g17.en cmd="enrang check g17.en" exit=1 stderr=block -->
```ts
function bump(xs: &mut i64[]): void {
  xs.push(1);
}

function main(): void {
  let a: i64[] = [];
  bump(a);
}
```

`enrang check g17.en`

```text
error[EN0612]: `bump` changes its argument, so the call must say `&mut`
 --> g17.en:7:8
  |
7 |   bump(a);
  |        ^ expected `&mut i64[]`, found `i64[]`
  |
  = note: shared borrows are implicit because they cannot change anything; mutation is always visible at the call.
help: lend it exclusively
  |
7 |   bump(&mut a);
  |        +++++
  = explain: run `enrang explain EN0612`

error: aborting due to 1 previous error
```

### G18 Method writes `this` without `mut`

<!-- case: G18 files=g18.en cmd="enrang check g18.en" exit=1 stderr=block -->
```ts
class Counter {
  private n: i64 = 0;
  inc(): void { this.n += 1; }
}
```

`enrang check g18.en`

```text
error[EN0615]: `inc` changes `this` but is not marked `mut`
 --> g18.en:3:17
  |
3 |   inc(): void { this.n += 1; }
  |                 ^^^^^^^^^^^ this write needs exclusive access to `this`
  |
help: mark the method `mut`
  |
3 |   mut inc(): void { this.n += 1; }
  |   ++++
  = explain: run `enrang explain EN0615`

error: aborting due to 1 previous error
```

### G19 Reference in a field

<!-- case: G19 files=g19.en cmd="enrang check g19.en" exit=1 stderr=block -->
```ts
class Lexer {
  src: &string;
  pos: isize = 0;
}
```

`enrang check g19.en`

```text
error[EN0701]: a class field cannot hold a reference
 --> g19.en:2:8
  |
2 |   src: &string;
  |        ^^^^^^^ references live only in locals, parameters and return values
  |
help: own the data
  |
2 |   src: string;
  |        ~~~~~~
help: or keep only `pos` in the class and pass `src: &string` to each method
  = explain: run `enrang explain EN0701`

error: aborting due to 1 previous error
```

### G20 Unused `Result`

<!-- case: G20 files=g20.en cmd="enrang check g20.en" exit=1 stderr=block -->
```ts
function save(name: &string): Result<void, string> {
  return Err(name.clone());
}

function main(): void {
  save("a");
}
```

`enrang check g20.en`

```text
error[EN0426]: this `Result` is not used, so an error would be lost silently
 --> g20.en:6:3
  |
6 |   save("a");
  |   ^^^^^^^^^ returns `Result<void, string>`
  |
  = from TypeScript: a thrown exception cannot be ignored by accident, and neither can this.
help: discard it deliberately
  |
6 |   void save("a");
  |   +++++
  = explain: run `enrang explain EN0426`

error: aborting due to 1 previous error
```

### G21 A loop that can change its own source

<!-- case: G21 files=g21.en cmd="enrang check g21.en" exit=0 stderr=block -->
```ts
function main(): void {
  let queue = ["a", "b"];
  for (const job of queue) {
    queue.push("retry");
  }
}
```

`enrang check g21.en`

```text
warning[EN0719]: `queue` can change inside this loop, so the loop may never stop
 --> g21.en:3:21
  |
3 |   for (const job of queue) {
  |                     ^^^^^ read again at the start of every turn
4 |     queue.push("retry");
  |     ------------------- `push` is a `mut` method, so it can change `queue`
  |
  = note: a `for...of` loop over a path sees changes to its source: added items get turns and removed items do not.
help: to loop over the items as they are now, iterate over a copy
  |
3 |   for (const job of [...queue]) {
  |                     ++++     +
help: or, to keep the new items and lose this warning, use an index loop: `for (let i = 0; i < queue.length; i++)`
```

### G22 Spreading elements that may not be cloneable

<!-- case: G22 files=g22.en cmd="enrang check g22.en" exit=1 stderr=block -->
```ts
function snapshot<T>(xs: &T[]): T[] {
  return [...xs];
}
```

`enrang check g22.en`

```text
error[EN0438]: `...` clones each element, and `T` has no `Clone` bound
 --> g22.en:2:11
  |
1 | function snapshot<T>(xs: &T[]): T[] {
  |                   - `T` is declared here
2 |   return [...xs];
  |           ^^^^^ each element of `xs` would be cloned here
  |
  = from TypeScript: JS spread copies references to the same objects. In Enrang a value has one owner, so `...` copies the elements too.
help: require `Clone`
  |
1 | function snapshot<T extends Clone>(xs: &T[]): T[] {
  |                    ++++++++++++++
  = explain: run `enrang explain EN0438`

error: aborting due to 1 previous error
```

### G23 A warning and an unrelated error

<!-- case: G23 files=g23.en cmd="enrang check g23.en" exit=1 stderr=block -->
```ts
function main(): void {
  let queue = ["a", "b"];
  for (const job of queue) {
    if (queue.length < 5) {
      queue.push("retry");
    }
  }
  const first = &queue[0];
  queue.clear();
  console.log(first);
}
```

`enrang check g23.en`

```text
warning[EN0719]: `queue` can change inside this loop, so the loop may never stop
 --> g23.en:3:21
  |
3 |   for (const job of queue) {
  |                     ^^^^^ read again at the start of every turn
4 |     if (queue.length < 5) {
5 |       queue.push("retry");
  |       ------------------- `push` is a `mut` method, so it can change `queue`
  |
  = note: a `for...of` loop over a path sees changes to its source: added items get turns and removed items do not.
help: to loop over the items as they are now, iterate over a copy
  |
3 |   for (const job of [...queue]) {
  |                     ++++     +
help: or, to keep the new items and lose this warning, use an index loop: `for (let i = 0; i < queue.length; i++)`

error[EN0706]: `queue` cannot change while `first` still points into it
  --> g23.en:9:3
   |
 8 |   const first = &queue[0];
   |                 --------- shared borrow of `queue` starts here, held by `first`
 9 |   queue.clear();
   |   ^^^^^^^^^^^^^ `clear` is a `mut` method, so it needs exclusive access to `queue`
10 |   console.log(first);
   |               ----- `first` is used again here
   |
   = rule: a value has many shared borrows or one exclusive borrow, never both.
help: keep a copy instead of a reference
   |
 8 |   const first = queue[0].clone();
   |                 ~~~~~~~~~~~~~~~~
   = explain: run `enrang explain EN0706`

error: aborting due to 1 previous error; 1 warning emitted
```

## 15. Sample programs

Each program is a conformance-corpus entry: every implementation (VM and each native target and level) must produce the same bytes on stdout and the same exit status. Hosted samples print the same on `x86_64-linux`, `x86_64-windows` and `i386-linux`, at every `--cpu` level.

### S1 Numbers and templates

<!-- case: S1 files=s01.en cmd="enrang run s01.en" exit=0 stdout=block -->
```ts
function main(): void {
  console.log("Hello, Enrang");
  const a: i64 = 7;
  const b: i64 = 2;
  console.log(a + b, a - b, a * b);
  console.log(7.0 / 2.0);
  console.log(`${a} / ${b} = ${a / b}, rem ${a % b}`);
  console.log(1.5 + 2.25, 0.1 + 0.2);
  const m: i64 = -7;
  console.log((300 as u16).wrap<u8>(), m / 2, m % 2);
}
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
class Tracer implements Drop {
  constructor(private name: string) {}
  mut drop(): void { console.log(`drop ${this.name}`); }
}

class Pair implements Drop {
  constructor(public first: Tracer, public second: Tracer) {}
  mut drop(): void { console.log("drop pair"); }
}

function consume(t: Tracer): void {
  console.log("consuming");
}

function main(): void {
  const a = new Tracer("a");
  const b = new Tracer("b");
  consume(a);
  const c = new Tracer("c");
  const p = new Pair(new Tracer("x"), new Tracer("y"));
  console.log("end of main");
}
```

Stdout:

```text
consuming
drop a
end of main
drop pair
drop x
drop y
drop c
drop b
```

### S3 Enums, `Box`, `match`, `?`

<!-- case: S3 files=s03.en cmd="enrang run s03.en" exit=0 stdout=block -->
```ts
enum Expr {
  Num(i64),
  Add(Box<Expr>, Box<Expr>),
  Mul(Box<Expr>, Box<Expr>),
  Div(Box<Expr>, Box<Expr>),
}

function num(n: i64): Box<Expr> { return new Box(Expr.Num(n)); }

function eval(e: &Expr): Result<i64, string> {
  return match (e) {
    Expr.Num(n) => Ok(n),
    Expr.Add(a, b) => Ok(eval(a)? + eval(b)?),
    Expr.Mul(a, b) => Ok(eval(a)? * eval(b)?),
    Expr.Div(a, b) => {
      const d = eval(b)?;
      if (d == 0) { return Err("division by zero"); }
      return Ok(eval(a)? / d);
    },
  };
}

function show(e: &Expr): void {
  match (eval(e)) {
    Ok(v) => console.log(`= ${v}`),
    Err(m) => console.log(`error: ${m}`),
  }
}

function main(): void {
  show(Expr.Add(num(2), new Box(Expr.Mul(num(3), num(4)))));
  show(Expr.Div(num(1), num(0)));
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
interface Shape {
  area(): f64;
  get name(): &string;
}

class Circle implements Shape {
  constructor(public r: f64) {}
  area(): f64 { return 3.0 * this.r * this.r; }
  get name(): &string { return "circle"; }
}

class Rect {                                   // satisfies Shape structurally
  constructor(public w: f64, public h: f64) {}
  area(): f64 { return this.w * this.h; }
  get name(): &string { return "rect"; }
}

function report<T extends Shape>(s: &T): void {
  console.log(`${s.name}: ${s.area()}`);
}

function main(): void {
  report(new Circle(2.0));
  report(new Rect(2.0, 3.5));

  const xs: i64[] = [1, 2, 3, 4];
  const squares = xs.map(x => x * x);
  console.log(squares.join(", "));

  let sum: i64 = 0;
  xs.forEach(x => { sum += x; });
  console.log(sum);

  const big = xs.find(x => x > 2);
  if (big != null) { console.log(big); }
}
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
function main(): void {
  const text = "the quick brown fox jumps over the lazy dog";
  const words = text.split(" ");
  console.log(words.length, text.byteLength);
  console.log(text.slice(4, 9));

  let longest = &words[0];
  for (const w of words) {
    if (w.byteLength > longest.byteLength) { longest = w; }
  }
  console.log(longest);

  let out = "";
  for (let i = words.length - 1; i >= 0; i--) {
    out += words[i];
    if (i > 0) { out += " "; }
  }
  console.log(out);

  let nums: i64[] = [5, 3, 9, 1];
  nums.sort();
  console.log(nums.join(" "));
  for (const n of &mut nums) { *n *= 2; }
  console.log(nums.reduce(0, (acc, n) => acc + n));
}
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
class Node<T> {
  value: T;
  next: Box<Node<T>> | null;
}

class Stack<T> {
  private head: Box<Node<T>> | null = null;

  mut push(value: T): void {
    const next = this.head.take();
    this.head = new Box(Node { value, next });
  }

  mut pop(): T | null {
    const boxed = this.head.take()?;
    const node = boxed.unbox();
    this.head = node.next;         // partial move from an owned local
    return node.value;
  }

  peek(): &T | null {
    return this.head?.value;
  }
}

function main(): void {
  let names = new Stack<string>();
  names.push("Ann");
  names.push("Bo");

  const top = names.peek();        // shared loan, live until its last use
  if (top != null) { console.log(`top ${top}`); }

  names.push("Cy");                // exclusive borrow is fine now
  console.log(names.pop() ?? "empty");
  console.log(names.pop()!);
  console.log(names.pop() ?? "empty");
  console.log(names.pop() ?? "empty");
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

### S7 `Result` from `main`

<!-- case: S7 files=s07.en cmd="enrang run s07.en" exit=1 stdout=block stderr=inline -->
```ts
function parseAge(s: &string): Result<i64, string> {
  const n = s.parseInt();
  if (n == null) { return Err(`not a number: ${s}`); }
  if (n < 0) { return Err("negative age"); }
  return Ok(n);
}

function sumAges(a: &string, b: &string): Result<i64, string> {
  return Ok(parseAge(a)? + parseAge(b)?);
}

function main(): Result<void, string> {
  console.log(sumAges("20", "22")?);
  match (sumAges("x", "1")) {
    Ok(v) => console.log(v),
    Err(e) => console.log(`caught: ${e}`),
  }
  sumAges("1", "-1")?;
  console.log("not reached");
  return Ok();
}
```

Stdout:

```text
42
caught: not a number: x
```

Stderr: `error: negative age`. Exit status 1.

### S8 Checked arithmetic and bounds

<!-- case: S8 files=s08.en cmd="enrang run s08.en" exit=101 stdout=block stderr=block -->
```ts
function main(): void {
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
import { vga, serial } from "os";

@section(".bss.counters") let bootCount: u32;

function writeU32(boot: &BootInfo, value: u32): void {
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

@entry function kmain(boot: &BootInfo): never {
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

@panicHandler function onPanic(info: &PanicInfo): never {
  vga.emergency("panic: ");
  vga.emergency(info.message);
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
export function gcd(a: i64, b: i64): i64 {
  return b == 0 ? a : gcd(b, a % b);
}

function main(): void {
  console.log(gcd(84, 36));
}
```

`src/math.test.en`:

```ts
describe("gcd", () => {
  test("common factor", () => {
    expect(gcd(84, 36)).toBe(12);
  });

  test("zero", () => {
    expect(gcd(7, 0)).toBe(7);
  });

  compileFails("rejects mixed widths", raw`
    function f(a: i32, b: i64): i64 { return a + b; } //~ EN0402
    function main(): void {}
  `);
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

`enrang run src/math.en`, stdout: `12`.

### S11 Array spread and a worklist that grows

The last loop ends because each value it pushes is smaller than the one it read. No compiler can prove that, so it warns, and the warning goes to stderr before the program runs.

<!-- case: S11 files=s11.en cmd="enrang run s11.en" exit=0 stdout=block stderr=block -->
```ts
function main(): void {
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
  console.log(turns, queue.length);

  const names = ["x"];
  let copy = [...names];
  copy[0] += "y";
  console.log(names[0], copy[0]);

  let work: i64[] = [3];
  let sum: i64 = 0;
  for (const n of work) {
    const v = *n;
    sum += v;
    if (v > 1) {
      work.push(v - 1);
      work.push(v - 2);
    }
  }
  console.log(sum, work.join(" "));
}
```

Stdout:

```text
0 1 2 3 7 8
2 4
x xy
7 3 2 1 1 0
```

Stderr, exit status 0:

```text
warning[EN0719]: `work` can change inside this loop, so the loop may never stop
  --> s11.en:22:19
   |
22 |   for (const n of work) {
   |                   ^^^^ read again at the start of every turn
...
26 |       work.push(v - 1);
   |       ---------------- `push` is a `mut` method, so it can change `work`
   |
   = note: a `for...of` loop over a path sees changes to its source: added items get turns and removed items do not.
help: to keep the new items and lose this warning, use an index loop: `for (let i = 0; i < work.length; i++)`
```

## 16. Deferred features

Each item produces its own diagnostic, never a miscompile. Format: `error[EN10xx]: <message> is not supported yet`, one `= note:` with the reason, and one `help:` where a workaround exists. Text below is the normative message head and help.

| Code | Feature seen | Message | Help |
|---|---|---|---|
| EN1001 | `async`, `await`, `Promise` | async functions are not supported yet | Run blocking; threads and an event loop come later |
| EN1002 | `function*`, `yield` | generators are not supported yet | Return an array, or keep state in a class |
| EN1003 | threads, `Worker`, `spawn` | threads are not supported yet | `Atomic` exists only for interrupt sharing |
| EN1004 | `Rc`, `Arc`, `Cell`, `RefCell` | shared ownership types are not supported yet | Own the value in one place and pass `&T`, or use an arena with integer handles |
| EN1005 | `'a`, `class C<from src>`, views in data | named lifetimes are not supported yet | Own the data, or store an index and pass `&T` per call |
| EN1006 | interface as a type, `Shape[]`, `dyn` | dynamic dispatch is not supported yet | `<T extends Shape>` for one type; an `enum` for mixed values |
| EN1007 | capturing arrow where `fn` is needed | a function pointer cannot capture variables | Pass it as a closure parameter, or pass the data explicitly |
| EN1008 | `x if c =>`, `1..5 =>` in `match` | match guards and range patterns are not supported yet | Move the test into the arm body |
| EN1009 | `export default`, `import *`, re-exports, `require` | this module form is not supported yet | Use `import { name } from "./file"` |
| EN1010 | tuples, `[a, b] = xs` | tuples and array destructuring are not supported yet | Declare a class |
| EN1011 | `&xs[a..b]`, `str` | slices are not supported yet | `slice` copies; or pass `xs` with bounds |
| EN1012 | `Map`, `Set` | `Map` and `Set` are not supported yet | Use a sorted `T[]` |
| EN1013 | `...` outside an array-literal element | rest, and spread outside an array literal, are not supported yet | Pass an array; `[...a]` copies one |
| EN1014 | associated types, const generics, specialisation | this generic feature is not supported yet | |
| EN1015 | `for...in`; `for...of` over a user type, over `string`, or by move over `T[N]` of non-Copy | this `for...of` source is not supported yet | Expose an array, or a `get(i)` and `length`; `byteAt` for `string`; a `T[]` for owned non-Copy elements |
| EN1016 | default parameters, overloads | default parameters and overloads are not supported yet | Use `T \| null`, or several names |
| EN1017 | `set p(v)` | setters are not supported yet | Write a `mut` method |
| EN1018 | operator methods | operator overloading is not supported yet | Write a named method |
| EN1019 | the type name `char` | a character type is not supported yet | `s.codePointAt(i)`, `s.byteAt(i)` |
| EN1020 | `--float=x87` | the x87 float strategy is not supported yet | `--float=soft` works at every level of `i386-*` and is bit-identical |
| EN1021 | `static x = ...` field | static fields are not supported yet | Use a top-level `const` or `let` |
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
| EN1035 | nested `function` | nested functions are not supported yet | Move it to the top level, or use an arrow argument |
| EN1036 | `<T>(x: T) => x` | generic arrows are not supported yet | Use a generic `function` |
| EN1037 | class expression, anonymous class | class expressions are not supported yet | Declare a class |
| EN1038 | label on a block | labelled blocks are not supported yet | Label a loop |
| EN1039 | `x as const` | `as const` is not supported yet | `const` is already deep |
| EN1040 | `enum E { A = "a" }` | string-valued enums are not supported yet | Use a method returning `&string` |
| EN1041 | `--multiboot`, `--coverage` | this flag is not supported yet | Boot through `--image`; the VM counts blocks internally but reports no coverage yet |

**Also out of the prototype, with no syntax to reject.** MMX, 3DNow! and SSE1-only code generation; auto-vectorisation; PIE; hot reload in production binaries; DWARF unwinding. Named lifetimes remain a compatible future: R3 becomes elision, so today's programs keep their meaning.

**Compiler commands outside the prototype** are EN1301: `install`, `add`, `publish`, `doc`, `lsp`, `repl`, `bench`, `debug`, `upgrade`, `fmt`.
