//! The compiler disagreements of M3 stage 4's first wave (the fix-sound stage):
//! each program the doc rows judge, through all of phase 3, pinned as (code,
//! line) in report order. Every one gave another outcome before its fix: an exit
//! 0 where the row wants a report, a report where it wants none, a second report
//! of one mistake, another code, or an internal error (exit 3, a body that failed
//! the verifier), which `support::phase3` turns into a panic.

use enrang_testkit::Harness;

/// One program, the row or rule it answers, and what phase 3 reports.
struct Fix {
    id: &'static str,
    source: &'static str,
    expected: &'static [(&'static str, u32)],
}

const HOLDER: &str = "
private class Item {
  public n: i64 = 1;
}

private class Holder {
  public item: Item | null = new Item();

  public drop(): void {
    this.item = null;
  }
}
";

const FIXES: &[Fix] = &[
    // (1) T:982 `S2-12-growVia`, SPEC 4.10: an `fn` row written with a type
    // parameter is computed before substitution, so its result is writable.
    Fix {
        id: "S2-12-growVia: a named function returning a string part, at a generic row",
        source: r##"let s = "abc".toString();
growVia(head, &s, "zz");

private function growVia<T>(f: fn(a: &T) => &T, x: &T, v: T): void {
  *f(x) = v;
}

private function head(s: &string): &string {
  return s.slice(0, 1);
}
"##,
        expected: &[("EN0615", 2)],
    },
    Fix {
        id: "S2-12-growVia: an `fn` value held in a local, at a generic row",
        source: r##"let s = "abc".toString();
const h: fn(a: &string) => &string = head;
growVia(h, &s, "zz");

private function growVia<T>(f: fn(a: &T) => &T, x: &T, v: T): void {
  *f(x) = v;
}

private function head(s: &string): &string {
  return s.slice(0, 1);
}
"##,
        expected: &[("EN0615", 3)],
    },
    Fix {
        id: "S2-12-growVia: the same rows at `T := i64` compile",
        source: r##"let n: i64 = 1;
growVia(head, &n, 5);
const k = (a: &i64): &i64 => { return a; };
growVia(k, &n, 7);
const h: fn(a: &i64) => &i64 = head;
growVia(h, &n, 8);

private function growVia<T>(f: fn(a: &T) => &T, x: &T, v: T): void {
  *f(x) = v;
}

private function head(s: &i64): &i64 {
  return s;
}
"##,
        expected: &[],
    },
    // (2) I6, S:742, S:1057, H18.
    Fix {
        id: "I6: a case-narrowed subject passed by reference to a writer in its own arm",
        source: r##"let s: Shape = Shape.Circle { radius: 1.0 };
match (s) {
  Shape.Circle => {
    flatten(&s);
    console.log(s.radius);
  },
  Shape.Empty => {},
}

public enum Shape {
  Circle { radius: f64 },
  Empty,
}

private function flatten(s: &Shape): void {
  *s = Shape.Empty;
}
"##,
        expected: &[("EN0401", 5)],
    },
    // (5) T:987 `S2-30-view`, S:773: a `fromRaw` view returned with no source
    // keeps a read-only mark; one returned under sources is as changeable as
    // they are, as a raw-derived `&*p` returned under `xs` or `this` is.
    Fix {
        id: "S2-30-view: a `fromRaw` view returned by a function with no source",
        source: r##"const a = cells4();
const b = cells4();
a[0] = 7;
b[0] = 8;
console.log(a[0]);

private unsafe let cells: u16[4];

public function cells4(): &Slice<u16> {
  unsafe {
    return Slice<u16>.fromRaw(&cells[0] as *u16, 4);
  }
}
"##,
        expected: &[("EN0616", 3), ("EN0616", 4)],
    },
    Fix {
        id: "S:773: raw-derived results and views returned under their sources compile",
        source: r##"let cells: u16[4] = [0, 0, 0, 0];
const a = cell(&cells, 0);
*a = 7;
let g = new Grid();
const c = g.cell(0);
*c = 7;
let s = new Screen();
s.pixels()[0] = 7;

public function cell(xs: &u16[4], i: isize): &u16 {
  unsafe {
    const p = &xs[0] as *u16;
    return &*p.add(i);
  }
}

public class Grid {
  private cells: u16[4] = [0, 0, 0, 0];

  public cell(i: isize): &u16 {
    unsafe {
      const p = &this.cells[0] as *u16;
      return &*p.add(i);
    }
  }
}

public class Screen {
  private cells: u16[4] = [0, 0, 0, 0];

  public pixels(): &Slice<u16> {
    unsafe {
      return Slice<u16>.fromRaw(&this.cells[0] as *u16, 4);
    }
  }
}
"##,
        expected: &[],
    },
    // (3) S:644 N11, plan d.10 "`fmt` always".
    Fix {
        id: "S:644: a written `fmt` that writes `this`, an override's included",
        source: r##"let a = new Tally();
console.log(`${a}`);

public class Tally implements Display {
  private n: i64 = 0;

  public fmt(f: &Formatter): void {
    this.n += 1;
    f.write("t");
  }
}

public class Base {
  public k: i64 = 0;

  public fmt(f: &Formatter): void {
    f.write("b");
  }
}

public class Sub extends Base {
  public override fmt(f: &Formatter): void {
    this.k += 1;
  }
}
"##,
        expected: &[("EN0615", 8), ("EN0615", 23)],
    },
    Fix {
        id: "S:644: a method named `fmt` with another signature is no printer",
        source: r##"let w = new W();
w.fmt(3);

public class W {
  public n: i64 = 0;

  public fmt(width: i64): void {
    this.n += width;
  }
}
"##,
        expected: &[],
    },
    // (8) T:817, S:1133, A:1353: N12 is transitive.
    Fix {
        id: "N12: a `const` body hands `this` or a `const` parameter to a writer",
        source: r##"const l = new Logger();
l.log("a");
l.put("b");

private unsafe let count: i64 = 0;

private function bump(g: &Logger): void {
  unsafe { count += 1; }
}

private function grow(s: &string): void {
  unsafe { count += 1; }
}

public class Logger {
  public constructor() {}

  public const log(const m: &string): void {
    unsafe { count += 1; }
    bump(this);
    console.log(m);
  }

  public const put(const m: &string): void {
    unsafe { count += 1; }
    grow(m);
  }
}
"##,
        expected: &[("EN0615", 20), ("EN0615", 26)],
    },
    // (4) S:972, A:1295, N13.
    Fix {
        id: "S:972: rebinding a captured reference inside an arrow",
        source: r##"let a: i64 = 1;
let b: i64 = 2;
let r: &i64 = &a;
const f = (): void => { r = &b; };
f();
console.log(*r);
"##,
        expected: &[("EN0616", 4)],
    },
    Fix {
        id: "N13: rebinding a captured reference inside a local function",
        source: r##"let a: i64 = 1;
let b: i64 = 2;
let r: &i64 = &a;
function repoint(): void {
  r = &b;
}
repoint();
console.log(*r);
"##,
        expected: &[("EN0616", 5)],
    },
    Fix {
        id: "S:972: an arrow argument that stashes its parameter in a captured reference, once",
        source: r##"let a: i64 = 1;
let r: &i64 = &a;
const xs: i64[] = [1, 2];
xs.forEach((x: &i64) => { r = x; });
console.log(*r);
"##,
        expected: &[("EN0616", 4)],
    },
    // (6) A `==`/`!=` test of a `&(T | null)` against `null` failed the verifier.
    Fix {
        id: "a `&(T | null)` compared with `null` tests its referent's tag",
        source: r##"private function peek(a: &(Acc | null)): i64 {
  return a == null ? 0 : 1;
}

private function peek2(a: &(Acc | null)): i64 {
  if (a != null) {
    return a.n;
  }
  return 0;
}

private function peek3(a: &(Acc | null)): i64 {
  return null != a ? 1 : 0;
}

private class Acc {
  public n: i64 = 0;
}
"##,
        expected: &[],
    },
    // (7) S:974, A:1259: capturing a closure holds it exclusively.
    Fix {
        id: "S:974: a closure called while a closure that captured it is live",
        source: r##"let n = 0;
const f = () => { n += 1; };
const g = () => { f(); };
f();
g();
"##,
        expected: &[("EN0718", 4)],
    },
    Fix {
        id: "S:974: a closure captured by two live closures",
        source: r##"let n = 0;
const f = () => { n += 1; };
const g = () => { f(); };
const h = () => { f(); };
g();
h();
"##,
        expected: &[("EN0718", 4)],
    },
    Fix {
        id: "S:974: a closure forwarded after an argument that captures it",
        source: r##"let n = 0;
const f = () => { n += 1; };
run(() => { f(); }, f);

private function run(a: () => void, b: () => void): void {
  a();
  b();
}
"##,
        expected: &[("EN0718", 3)],
    },
    Fix {
        id: "S:974: a closure parameter called while a closure that captured it is live",
        source: r##"private function outer(f: () => void): void {
  const g = () => { f(); };
  f();
  g();
}
"##,
        expected: &[("EN0718", 3)],
    },
    Fix {
        id: "A:973: a nullable closure parameter called while a closure that captured it is live",
        source: r##"private function outer(h?: () => void): void {
  const g = () => { if (h != null) { h(); } };
  if (h != null) {
    h();
  }
  g();
}
"##,
        expected: &[("EN0718", 4)],
    },
    Fix {
        id: "A:973: a nullable closure parameter called, then captured, compiles",
        source: r##"private function outer(h?: () => void): void {
  if (h != null) {
    h();
  }
  const g = () => { if (h != null) { h(); } };
  g();
}
"##,
        expected: &[],
    },
    Fix {
        id: "S:974: uses of a closure one after the other compile",
        source: r##"let n = 0;
const f = () => { n += 1; };
f();
const g = () => { f(); };
g();
const h = () => { f(); };
h();
"##,
        expected: &[],
    },
    // (9) D4, A:1270: one report per mistake; O11, A:1262: the write's own
    // bounds read does not pre-empt its EN0707.
    Fix {
        id: "D4: `move open(): &Letter` returning `&this.inside` is one EN0710",
        source: r##"const e = new Envelope { inside: new Letter { text: "hi" } };
const l = e.open();
console.log(l.text);

public class Letter {
  public text: string = "";
}

public class Envelope {
  public inside: Letter = new Letter();

  public move open(): &Letter {
    return &this.inside;
  }
}
"##,
        expected: &[("EN0710", 13)],
    },
    Fix {
        id: "O11: an element write of a growable array under an exclusive loan is EN0707",
        source: r##"let xs: i64[] = [1, 2];
const r = &xs[0];
xs[1] = 5;
*r = 3;
"##,
        expected: &[("EN0707", 3)],
    },
];

/// The retests of S:742: `HOLDER`'s classes after each body.
const RETESTS: &[Fix] = &[
    Fix {
        id: "S:742: a retest after a writing record keeps the payload",
        source: r##"let h = new Holder();
if (h.item != null) {
  h.drop();
  if (h.item != null) {
    console.log(h.item.n);
  }
}
"##,
        expected: &[],
    },
    Fix {
        id: "S:742: retests by an early return, a ternary, a loop and `&&`",
        source: r##"let h = new Holder();
if (h.item != null) {
  h.drop();
  if (h.item == null) {
    return;
  }
  console.log(h.item.n);
  h.drop();
  const k = h.item != null ? h.item.n : 0;
  console.log(k);
  h.drop();
  while (h.item != null) {
    console.log(h.item.n);
    h.drop();
  }
  h.drop();
  if (h.item != null && h.item.n > 0) {
    console.log(h.item.n);
  }
}
"##,
        expected: &[],
    },
    Fix {
        id: "S:742: a retest that fails falls into the join, where the write still holds",
        source: r##"let h = new Holder();
if (h.item != null) {
  h.drop();
  if (h.item == null) {
    console.log(0);
  }
  console.log(h.item.n);
}
"##,
        expected: &[("EN0401", 7)],
    },
    Fix {
        id: "S:742: a retest on one path only",
        source: r##"let c = true;
let h = new Holder();
if (h.item != null) {
  h.drop();
  if (c) {
    if (h.item == null) {
      return;
    }
  }
  console.log(h.item.n);
}
"##,
        expected: &[("EN0401", 10)],
    },
];

fn pairs(list: &[(&str, u32)]) -> Vec<(String, u32)> {
    list.iter().map(|(c, l)| (c.to_string(), *l)).collect()
}

/// The programs phase 3 must accept, by case name, each retest with `HOLDER`'s
/// classes: hosts of `mutants`' violations (TESTING 14).
pub fn accepted() -> Vec<(String, String)> {
    let fixes = (FIXES.iter()).map(|fix| (fix, fix.source.to_owned()));
    let retests = (RETESTS.iter()).map(|fix| (fix, format!("{}{HOLDER}", fix.source)));
    (fixes.chain(retests))
        .filter(|(fix, _)| fix.expected.is_empty())
        .map(|(fix, source)| (format!("soundfix/{}", fix.id), source))
        .collect()
}

pub fn register(h: &mut Harness) {
    for fix in FIXES {
        h.case(format!("soundfix/{}", fix.id), move || {
            assert_eq!(crate::support::phase3(fix.source), pairs(fix.expected));
        });
    }
    for fix in RETESTS {
        h.case(format!("soundfix/{}", fix.id), move || {
            let source = format!("{}{HOLDER}", fix.source);
            assert_eq!(crate::support::phase3(&source), pairs(fix.expected));
        });
    }
}
