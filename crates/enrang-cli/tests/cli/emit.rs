//! `check --emit=mir` and `--emit=summary` as processes (M3 plan b.11 and f.3,
//! stage 4M): one program per construct family of MIR building, and one per kind
//! of contract a summary states, each a golden of the whole transcript in the
//! project suite (`support::PROJECT_SUITE`), under `check/emit-mir/` and
//! `check/emit-summary/`: exit 0, the text on stdout, nothing on stderr.
//!
//! Plan f.3 put these goldens under `tests/golden/cli/check/`, but every golden
//! there is a transcript that needs no file, which the meta suite runs again in a
//! directory of its own (`meta/support.rs`, `TRANSCRIPTS`), so a program that
//! `check` reads lives with the project suite's cases, as stage 3's `emit_mir`
//! and `emit_summary` do. SPEC 1's ownership block is `check/emit_mir` already.

use crate::project::ProjectCase;

/// A case running `check --emit=<what> main.en` over `source`.
fn case(what: &str, name: &str, source: &str) -> ProjectCase {
    ProjectCase {
        name: format!("check/emit-{what}/{name}.txt"),
        files: vec![("main.en".to_owned(), source.as_bytes().to_vec())],
        dirs: Vec::new(),
        args: ["check", &format!("--emit={what}"), "main.en"]
            .map(str::to_owned)
            .to_vec(),
        stdin: None,
        exit: 0,
        dump: None,
        initialised: false,
    }
}

/// The programs of `--emit=mir`, one per construct family of plan section c.
const MIR: &[(&str, &str)] = &[
    // G08's program with the help's fix applied, a loop over a copy: the copy's
    // `clone` and the loop's drops.
    (
        "g08_fixed",
        r#"let queue = ["a", "b"];
for (const job of [...queue]) {
  if (job == "a") { queue.push("retry"); }
  console.log(job);
}
"#,
    ),
    // a `for...of` over a narrowed path: each head and bind checks the tag.
    (
        "for_of_narrowed",
        r#"console.log(total([1, 2, 3]), total(null));

public function total(p: i64[] | null): i64 {
  let n = 0;
  if (p != null) {
    for (const x of &p) {
      n += *x;
    }
  }
  return n;
}
"#,
    ),
    // a `match` with a guard, which falls through to the next arm.
    (
        "match_guard",
        r#"const flag = true;
console.log(size(Shape.Circle { radius: 2 }, flag), size(Shape.Empty, flag));

public function size(s: Shape, big: bool): i64 {
  return match (s) {
    Shape.Circle if big => s.radius * 2,
    Shape.Circle => s.radius,
    Shape.Empty => 0,
  };
}

public enum Shape {
  Circle { radius: i64 },
  Empty,
}
"#,
    ),
    // `Err(...)`, a plain value as `Ok`, and `?`.
    (
        "result_forms",
        r#"const r = half(10);
console.log(r, quarter(10), half(3));

public function half(n: i64): Result<i64> {
  if (n % 2 != 0) { return Err("odd"); }
  return n / 2;
}

public function quarter(n: i64): Result<i64> {
  const h = half(n)?;
  return half(h);
}
"#,
    ),
    // a closure, and a local function that reaches it through a hidden argument.
    (
        "closure_local_function",
        r#"let total = 0;
const add = (x: i64): void => { total += x; };
add(2);
function twice(): void { add(1); add(1); }
twice();
console.log(total);
"#,
    ),
    // constructors of a class that can be extended: each field initialiser behind
    // its `overridden` switch.
    (
        "extendable_constructor",
        r#"const d = new Dog("Rex");
console.log(d.describe());

public class Animal {
  public name: string;
  public legs: i64 = 4;
  public constructor(name: string) { this.name = name; }
  public describe(): string { return this.name.clone(); }
}

public class Dog extends Animal {
  public tricks: string[] = [];
  public constructor(name: string) { super(name); }
}
"#,
    ),
    // a named form: the fields left out are filled by `named_fill`.
    (
        "named_fill",
        r#"const s = new Solo {};
const t = new Solo { v: 5 };
console.log(s.get() + t.get());

public final class Solo {
  public v: i64 = 1;
  public label: string = "solo";
  public get(): i64 { return this.v; }
}
"#,
    ),
    // array spread.
    (
        "spread",
        r#"const a: string[] = ["x".toString(), "y".toString()];
const b = ["z".toString()];
const all = [...a, "-".toString(), ...b];
console.log(all, a);
"#,
    ),
    // a destructuring assignment, of owned values and of Copy ones.
    (
        "destructuring_assignment",
        r#"let a = "left".toString();
let b = "right".toString();
[a, b] = [b, a];
let n = 1;
let m = 2;
[n, m] = [m, n];
console.log(a, b, n, m);
"#,
    ),
];

/// The programs of `--emit=summary`, one per kind of contract.
const SUMMARY: &[(&str, &str)] = &[
    // SPEC 5.1's `Lexer`: its flag off, `next` through its fields.
    (
        "lexer",
        r#"const source = "let x = 1;".toString();
let lx = new Lexer(&source);
const a = lx.next();
const b = lx.next();
console.log(a, b);

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
"#,
    ),
    // a `Holder` whose reference field a writable result is read from: its flag on,
    // with the witness.
    (
        "holder",
        r#"let data: i64[] = [1, 2];
let h = new Holder(&data);
h.grow();
console.log(*h.first());

public final class Holder {
  private v: &i64[];
  public constructor(v: &i64[]) { this.v = v; }
  public first(): &i64 { return &this.v[0]; }
  public grow(): void { this.v.push(3); }
}
"#,
    ),
    // a `Copier` with a `readonly &` field: `through_read`, a store with the read bit,
    // and its flag with the witness.
    (
        "copier",
        r#"const table: u8[3] = [7, 8, 9];
let out: u8[3] = [0, 0, 0];
let c = new Copier(&table, &out);
const a = c.peek();
c.step();
c.step();
const b = c.peek();
console.log(a, b);
console.log(table, out);

public final class Copier {
  private src: readonly &Slice<u8>;
  private dst: &Slice<u8>;
  private pos: isize;
  public constructor(src: &Slice<u8>, dst: &Slice<u8>) { this.src = src; this.dst = dst; }
  public step(): void { this.dst[this.pos] = this.src[this.pos]; this.pos += 1; }
  public peek(): readonly &Slice<u8> { return this.src.slice(this.pos, this.pos + 1); }
}
"#,
    ),
    // SPEC 5.4's `longest` and `first`: sources from both, and from `xs` alone.
    (
        "longest_first",
        r#"const names: string[] = ["ada".toString(), "grace".toString()];
let label = "names".toString();
const f = first(&names, &label);
label = "people".toString();
console.log(f, label, longest(&names[0], &names[1]));

public function longest(a: &string, b: &string): &string { return a.length() > b.length() ? a : b; }  // borrows from both

public function first(xs: &Slice<string>, label: &string): &string {  // only `xs` stays borrowed
  console.log(`reading ${label}`);
  return &xs[0];
}
"#,
    ),
    // a `Wrapper.retarget` that stores its argument into `this`, `(1, 0)`.
    (
        "wrapper_retarget",
        r#"const a: u8[] = [1];
const b: u8[] = [2];
let w = new Wrapper(&a);
w.retarget(&b);
console.log(w.peek());

public final class Wrapper {
  private src: &u8[];
  public constructor(src: &u8[]) { this.src = src; }
  public retarget(v: &u8[]): void { this.src = v; }
  public peek(): u8 { return this.src[0]; }
}
"#,
    ),
    // a local function, whose captures are hidden arguments.
    (
        "local_function",
        r#"let log: string[] = [];
const prefix = "> ".toString();
function note(line: &string): void { log.push(prefix + line); }
note("one");
note("two");
console.log(log);
"#,
    ),
];

/// Every case: the MIR programs, then the summary programs.
pub fn cases() -> Vec<ProjectCase> {
    let mir = MIR.iter().map(|(name, source)| case("mir", name, source));
    let summary = SUMMARY
        .iter()
        .map(|(name, source)| case("summary", name, source));
    mir.chain(summary).collect()
}
