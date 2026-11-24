//! The arm and special-lowering audit after stage 5 (M3 close, `audit` key): each
//! hole a catch-all arm or a specially lowered form left, as the program that
//! exploited it, with its near miss; and one program per library item or form
//! that mirbuild lowers specially, showing that phase 3 sees its real move, drop,
//! write, store and result effect, as (code, line) in report order.

use enrang_testkit::Harness;

/// One program, what it shows, the file it is checked as, and what phase 3
/// reports.
struct Case {
    id: &'static str,
    file: &'static str,
    source: &'static str,
    expected: &'static [(&'static str, u32)],
}

const CASES: &[Case] = &[
    Case {
        id: "a borrowing value moved out of a tuple part into a tuple keeps its loans",
        file: "main.en",
        source: r##"let v: i64[] = [1];
const t: [i32, W] = [1, new W(&v[0])];
const u: [W, i32] = [t[1], 2];
v.push(2);
console.log(u[0].get());
public class W { private r: &i64; public constructor(r: &i64) { this.r = r; } public get(): i64 { return *this.r; } }
"##,
        expected: &[("EN0706", 4)],
    },
    Case {
        id: "a borrowing value moved out of a tuple part into a tuple, used before the write",
        file: "main.en",
        source: r##"let v: i64[] = [1];
const t: [i32, W] = [1, new W(&v[0])];
const u: [W, i32] = [t[1], 2];
console.log(u[0].get());
v.push(2);
public class W { private r: &i64; public constructor(r: &i64) { this.r = r; } public get(): i64 { return *this.r; } }
"##,
        expected: &[],
    },
    Case {
        id: "a borrowing value moved out of a tuple part into a present value keeps its loans",
        file: "main.en",
        source: r##"let v: i64[] = [1];
const t: [i32, W] = [1, new W(&v[0])];
const n: W | null = t[1];
v.push(2);
if (n != null) { console.log(n.get()); }
public class W { private r: &i64; public constructor(r: &i64) { this.r = r; } public get(): i64 { return *this.r; } }
"##,
        expected: &[("EN0706", 4)],
    },
    Case {
        id: "a borrowing value moved out of a tuple part into a present value, used before the write",
        file: "main.en",
        source: r##"let v: i64[] = [1];
const t: [i32, W] = [1, new W(&v[0])];
const n: W | null = t[1];
if (n != null) { console.log(n.get()); }
v.push(2);
public class W { private r: &i64; public constructor(r: &i64) { this.r = r; } public get(): i64 { return *this.r; } }
"##,
        expected: &[],
    },
    Case {
        id: "a borrowing value moved out of a tuple part into a constructor that stores it keeps its loans",
        file: "main.en",
        source: r##"let v: i64[] = [1];
const t: [i32, W] = [1, new W(&v[0])];
const h = new H(t[1]);
v.push(2);
console.log(h.get());
public class W { private r: &i64; public constructor(r: &i64) { this.r = r; } public get(): i64 { return *this.r; } }
public class H { private w: W; public constructor(w: W) { this.w = w; } public get(): i64 { return this.w.get(); } }
"##,
        expected: &[("EN0706", 4)],
    },
    Case {
        id: "a borrowing value moved out of a tuple part into a constructor, used before the write",
        file: "main.en",
        source: r##"let v: i64[] = [1];
const t: [i32, W] = [1, new W(&v[0])];
const h = new H(t[1]);
console.log(h.get());
v.push(2);
public class W { private r: &i64; public constructor(r: &i64) { this.r = r; } public get(): i64 { return *this.r; } }
public class H { private w: W; public constructor(w: W) { this.w = w; } public get(): i64 { return this.w.get(); } }
"##,
        expected: &[],
    },
    Case {
        id: "a borrowing value moved out of a tuple part into a call whose result holds it keeps its loans",
        file: "main.en",
        source: r##"let v: i64[] = [1];
const t: [i32, W] = [1, new W(&v[0])];
const k = keep(t[1]);
v.push(2);
console.log(k.get());
public class W { private r: &i64; public constructor(r: &i64) { this.r = r; } public get(): i64 { return *this.r; } }
public function keep(w: W): W { return w; }
"##,
        expected: &[("EN0706", 4)],
    },
    Case {
        id: "a borrowing value moved out of a tuple part into a call, used before the write",
        file: "main.en",
        source: r##"let v: i64[] = [1];
const t: [i32, W] = [1, new W(&v[0])];
const k = keep(t[1]);
console.log(k.get());
v.push(2);
public class W { private r: &i64; public constructor(r: &i64) { this.r = r; } public get(): i64 { return *this.r; } }
public function keep(w: W): W { return w; }
"##,
        expected: &[],
    },
    Case {
        id: "a borrowing tuple moved out of a tuple part into a tuple keeps its loans",
        file: "main.en",
        source: r##"let v: i64[] = [1];
const t: [i32, [W, i32]] = [1, [new W(&v[0]), 2]];
const u: [[W, i32], i32] = [t[1], 2];
v.push(2);
console.log(u[0][0].get());
public class W { private r: &i64; public constructor(r: &i64) { this.r = r; } public get(): i64 { return *this.r; } }
"##,
        expected: &[("EN0706", 4)],
    },
    Case {
        id: "a borrowing tuple moved out of a tuple part into a tuple, used before the write",
        file: "main.en",
        source: r##"let v: i64[] = [1];
const t: [i32, [W, i32]] = [1, [new W(&v[0]), 2]];
const u: [[W, i32], i32] = [t[1], 2];
console.log(u[0][0].get());
v.push(2);
public class W { private r: &i64; public constructor(r: &i64) { this.r = r; } public get(): i64 { return *this.r; } }
"##,
        expected: &[],
    },
    Case {
        id: "the payload `??` reads out of a nullable borrowing value keeps its loans",
        file: "main.en",
        source: r##"let v: i64[] = [1];
const a: W | null = new W(&v[0]);
const d: W | null = null;
const x: W | null = a ?? d;
v.push(2);
if (x != null) { console.log(x.get()); }
public class W { private r: &i64; public constructor(r: &i64) { this.r = r; } public get(): i64 { return *this.r; } public static peek(n: W | null): &i64 | null { return n?.r; } }
"##,
        expected: &[("EN0706", 5)],
    },
    Case {
        id: "the payload `??` reads out of a nullable borrowing value, used before the write",
        file: "main.en",
        source: r##"let v: i64[] = [1];
const a: W | null = new W(&v[0]);
const d: W | null = null;
const x: W | null = a ?? d;
if (x != null) { console.log(x.get()); }
v.push(2);
public class W { private r: &i64; public constructor(r: &i64) { this.r = r; } public get(): i64 { return *this.r; } public static peek(n: W | null): &i64 | null { return n?.r; } }
"##,
        expected: &[],
    },
    Case {
        id: "a reference field `?.` reads keeps its loans in the result",
        file: "main.en",
        source: r##"let v: i64[] = [1];
const a: W | null = new W(&v[0]);
const x = W.peek(a);
v.push(2);
if (x != null) { console.log(*x); }
public class W { private r: &i64; public constructor(r: &i64) { this.r = r; } public get(): i64 { return *this.r; } public static peek(n: W | null): &i64 | null { return n?.r; } }
"##,
        expected: &[("EN0706", 4)],
    },
    Case {
        id: "a reference field `?.` reads, used before the write",
        file: "main.en",
        source: r##"let v: i64[] = [1];
const a: W | null = new W(&v[0]);
const x = W.peek(a);
if (x != null) { console.log(*x); }
v.push(2);
public class W { private r: &i64; public constructor(r: &i64) { this.r = r; } public get(): i64 { return *this.r; } public static peek(n: W | null): &i64 | null { return n?.r; } }
"##,
        expected: &[],
    },
    Case {
        id: "the payload `??` reads out of a nullable reference tuple keeps its loans",
        file: "main.en",
        source: r##"let v: i64[] = [1];
const a: [&i64, i32] | null = [&v[0], 1];
const d: [&i64, i32] | null = null;
const x: [&i64, i32] | null = a ?? d;
v.push(2);
if (x != null) { console.log(*x[0]); }
"##,
        expected: &[("EN0706", 5)],
    },
    Case {
        id: "the payload `??` reads out of a nullable reference tuple, used before the write",
        file: "main.en",
        source: r##"let v: i64[] = [1];
const a: [&i64, i32] | null = [&v[0], 1];
const d: [&i64, i32] | null = null;
const x: [&i64, i32] | null = a ?? d;
if (x != null) { console.log(*x[0]); }
v.push(2);
"##,
        expected: &[],
    },
    Case {
        id: "a reference copied out of a reference field of a value reached through another holds its loans",
        file: "main.en",
        source: r##"let a1: i64[] = [1]; let a2: i64[] = [1];
let n2 = new N(&a2, null);
let n1 = new N(&a1, &n2);
n1.bad();

public class N {
  private v: &i64[];
  private next: &N | null;
  public constructor(v: &i64[], next: &N | null) { this.v = v; this.next = next; }
  public bad(): void {
    if (this.next != null) {
      const e = &this.next.v[0];
      const x = this.next.v;
      x.push(1); x.push(2); x.push(3);
      console.log(*e);
    }
  }
}
"##,
        expected: &[("EN0706", 13)],
    },
    Case {
        id: "a reference copied out of a reference field reached through another, written before the borrow",
        file: "main.en",
        source: r##"let a1: i64[] = [1]; let a2: i64[] = [1];
let n2 = new N(&a2, null);
let n1 = new N(&a1, &n2);
n1.good();
console.log(a2);

public class N {
  private v: &i64[];
  private next: &N | null;
  public constructor(v: &i64[], next: &N | null) { this.v = v; this.next = next; }
  public good(): void {
    if (this.next != null) {
      const x = this.next.v;
      x.push(1); x.push(2); x.push(3);
      const e = &this.next.v[0];
      console.log(*e);
    }
  }
}
"##,
        expected: &[],
    },
    Case {
        id: "a reference copied out through three reference fields holds its loans",
        file: "main.en",
        source: r##"let a1: i64[] = [1]; let a2: i64[] = [1]; let a3: i64[] = [1];
let n3 = new N(&a3, null);
let n2 = new N(&a2, &n3);
let n1 = new N(&a1, &n2);
n1.bad();

public class N {
  private v: &i64[];
  private next: &N | null;
  public constructor(v: &i64[], next: &N | null) { this.v = v; this.next = next; }
  public bad(): void {
    if (this.next != null) { if (this.next.next != null) {
      const e = &this.next.next.v[0];
      const x = this.next.next.v;
      x.push(1); x.push(2); x.push(3);
      console.log(*e);
    } }
  }
}
"##,
        expected: &[("EN0706", 14)],
    },
    Case {
        id: "a reference copied out through three reference fields, written before the borrow",
        file: "main.en",
        source: r##"let a1: i64[] = [1]; let a2: i64[] = [1]; let a3: i64[] = [1];
let n3 = new N(&a3, null);
let n2 = new N(&a2, &n3);
let n1 = new N(&a1, &n2);
n1.good();
console.log(a3);

public class N {
  private v: &i64[];
  private next: &N | null;
  public constructor(v: &i64[], next: &N | null) { this.v = v; this.next = next; }
  public good(): void {
    if (this.next != null) { if (this.next.next != null) {
      const x = this.next.next.v;
      x.push(1); x.push(2); x.push(3);
      const e = &this.next.next.v[0];
      console.log(*e);
    } }
  }
}
"##,
        expected: &[],
    },
    Case {
        id: "an arrow's copy out of a reference field reached through a captured reference holds its loans",
        file: "main.en",
        source: r##"let a1: i64[] = [1]; let a2: i64[] = [1];
let n2 = new N(&a2, null);
let n1 = new N(&a1, &n2);
n1.bad();

public function run(f: () => void): void { f(); }
public class N {
  private v: &i64[];
  private next: &N | null;
  public constructor(v: &i64[], next: &N | null) { this.v = v; this.next = next; }
  public bad(): void {
    const me = this;
    run(() => {
      if (me.next != null) {
        const e = &me.next.v[0];
        const x = me.next.v;
        x.push(1);
        console.log(*e);
      }
    });
  }
}
"##,
        expected: &[("EN0706", 16)],
    },
    Case {
        id: "an arrow's copy out of a reference field reached through a captured reference, written before the borrow",
        file: "main.en",
        source: r##"let a1: i64[] = [1]; let a2: i64[] = [1];
let n2 = new N(&a2, null);
let n1 = new N(&a1, &n2);
n1.bad();

public function run(f: () => void): void { f(); }
public class N {
  private v: &i64[];
  private next: &N | null;
  public constructor(v: &i64[], next: &N | null) { this.v = v; this.next = next; }
  public bad(): void {
    const me = this;
    run(() => {
      if (me.next != null) {
        const x = me.next.v;
        x.push(1);
        const e = &me.next.v[0];
        console.log(*e);
      }
    });
  }
}
"##,
        expected: &[],
    },
    Case {
        id: "a store through two reference fields keeps a reference to a dead local",
        file: "main.en",
        source: r##"let a1: i64 = 1; let a2: i64 = 1; let a3: i64 = 1;
let n3 = new N(&a3, null);
let n2 = new N(&a2, &n3);
let n1 = new N(&a1, &n2);
poke2(&n1);
console.log(n3.get());

public function poke2(n: &N): void {
  let b: i64 = 2;
  n.poke(&b);
}

public class N {
  private r: &i64;
  private next: &N | null;
  public constructor(r: &i64, next: &N | null) { this.r = r; this.next = next; }
  public poke(x: &i64): void {
    if (this.next != null) { if (this.next.next != null) { this.next.next.r = x; } }
  }
  public get(): i64 { return *this.r; }
}
"##,
        expected: &[("EN0711", 11)],
    },
    Case {
        id: "a store through two reference fields holds what it stored",
        file: "main.en",
        source: r##"let a1: i64 = 1; let a2: i64 = 1; let a3: i64 = 1; let b: i64 = 2;
let n3 = new N(&a3, null);
let n2 = new N(&a2, &n3);
let n1 = new N(&a1, &n2);
n1.poke(&b);
b = 5;
console.log(n3.get());

public class N {
  private r: &i64;
  private next: &N | null;
  public constructor(r: &i64, next: &N | null) { this.r = r; this.next = next; }
  public poke(x: &i64): void {
    if (this.next != null) { if (this.next.next != null) { this.next.next.r = x; } }
  }
  public get(): i64 { return *this.r; }
}
"##,
        expected: &[("EN0707", 6)],
    },
    Case {
        id: "a store through two reference fields of a reference that outlives the object",
        file: "main.en",
        source: r##"let a1: i64 = 1; let a2: i64 = 1; let a3: i64 = 1; let b: i64 = 2;
let n3 = new N(&a3, null);
let n2 = new N(&a2, &n3);
let n1 = new N(&a1, &n2);
n1.poke(&b);
console.log(n3.get());

public class N {
  private r: &i64;
  private next: &N | null;
  public constructor(r: &i64, next: &N | null) { this.r = r; this.next = next; }
  public poke(x: &i64): void {
    if (this.next != null) { if (this.next.next != null) { this.next.next.r = x; } }
  }
  public get(): i64 { return *this.r; }
}
"##,
        expected: &[],
    },
    Case {
        id: "an arrow's parameter not marked `let` cannot be assigned (S:774)",
        file: "main.en",
        source: r##"run((x: i64): void => { x = 5; console.log(x); });
function run(f: (x: i64) => void): void { f(1); }
"##,
        expected: &[("EN0613", 1)],
    },
    Case {
        id: "an arrow's by-value parameter not marked `let` cannot be changed (S:774)",
        file: "main.en",
        source: r##"run((p: P): void => { p.n = 5; console.log(p.n); });
function run(f: (p: P) => void): void { f(new P()); }
public class P { public n: i64 = 0; }
"##,
        expected: &[("EN0608", 1)],
    },
    Case {
        id: "an arrow's parameter marked `let` can be assigned",
        file: "main.en",
        source: r##"run((let x: i64): void => { x = 5; console.log(x); });
function run(f: (x: i64) => void): void { f(1); }
"##,
        expected: &[],
    },
    Case {
        id: "an arrow's by-value parameter marked `let` can be changed",
        file: "main.en",
        source: r##"run((let p: P): void => { p.n = 5; console.log(p.n); });
function run(f: (p: P) => void): void { f(new P()); }
public class P { public n: i64 = 0; }
"##,
        expected: &[],
    },
    Case {
        id: "`Formatter.write` writes the formatter, so an alias read later conflicts",
        file: "main.en",
        source: r##"console.log(new P());
public class P implements Display {
  public fmt(let f: &Formatter): void { const g: &Formatter = f; f.write("x"); peek(g); }
}
public function peek(f: &Formatter): void {}
"##,
        expected: &[("EN0706", 3)],
    },
    Case {
        id: "`writeTo` writes its formatter as `write` does (S:1203)",
        file: "main.en",
        source: r##"console.log(new P());
public class P implements Display {
  public fmt(let f: &Formatter): void { const g: &Formatter = f; writeTo(f, "x"); peek(g); }
}
public function peek(f: &Formatter): void {}
"##,
        expected: &[("EN0706", 3)],
    },
    Case {
        id: "`writeTo` with a template writes its formatter as `write` does",
        file: "main.en",
        source: r##"console.log(new P());
public class P implements Display {
  public fmt(let f: &Formatter): void { const g: &Formatter = f; writeTo(f, `x${1}`); peek(g); }
}
public function peek(f: &Formatter): void {}
"##,
        expected: &[("EN0706", 3)],
    },
    Case {
        id: "`writeTo` in a helper makes its formatter parameter written",
        file: "main.en",
        source: r##"console.log(new P());
public class P implements Display {
  public fmt(let f: &Formatter): void { const g: &Formatter = f; show(f); peek(g); }
}
public function show(f: &Formatter): void { writeTo(f, "x"); }
public function peek(f: &Formatter): void {}
"##,
        expected: &[("EN0706", 3)],
    },
    Case {
        id: "`write` in a helper of `fmt` compiles",
        file: "main.en",
        source: r##"console.log(new P());
public class P implements Display {
  public fmt(let f: &Formatter): void { show(f); }
}
public function show(f: &Formatter): void { f.write("x"); }
"##,
        expected: &[],
    },
    Case {
        id: "`writeTo` in a helper of `fmt` compiles",
        file: "main.en",
        source: r##"console.log(new P());
public class P implements Display {
  public fmt(let f: &Formatter): void { show(f); }
}
public function show(f: &Formatter): void { writeTo(f, "x"); }
"##,
        expected: &[],
    },
    Case {
        id: "H40: parts of two tuple locals, one built before a `let` parameter was repointed, returned together",
        file: "main.en",
        source: r##"let root = new Node(); let kid = new Node(); kid.val.push(1); root.kids.push(kid);
const [tk, tv] = snapDown(&root); const k = tk[0]; const f = &tv[0][0];
k.val = [];
console.log(*f);

public class Node { public val: i64[] = []; public kids: Node[] = []; }

public function snapDown(let node: &Node): [[&Node, i32], [&i64[], i32]] { const t: [&Node, i32] = [&node.kids[0], 0]; node = &node.kids[0]; const u: [&i64[], i32] = [&node.val, 0]; return [t, u]; }
"##,
        expected: &[("EN0616", 3)],
    },
    Case {
        id: "H40: parts of two tuple locals returned together, with no repoint",
        file: "main.en",
        source: r##"let root = new Node(); let kid = new Node(); kid.val.push(1); root.kids.push(kid);
const [tk, tv] = snapDown(&root); const k = tk[0]; const f = &tv[0][0];
k.val = [];
console.log(*f);

public class Node { public val: i64[] = []; public kids: Node[] = []; }

public function snapDown(node: &Node): [[&Node, i32], [&i64[], i32]] { const t: [&Node, i32] = [&node.kids[0], 0]; const u: [&i64[], i32] = [&node.val, 0]; return [t, u]; }
"##,
        expected: &[],
    },
    Case {
        id: "H40: parts of two tuple locals, one built before a `let` parameter was repointed, passed to a call",
        file: "main.en",
        source: r##"let root = new Node(); let kid = new Node(); kid.val.push(1); root.kids.push(kid);
const [k, w] = snapDown(&root); const f = &w[0];
k.val = [];
console.log(*f);

public class Node { public val: i64[] = []; public kids: Node[] = []; }

public function pick(t: [&Node, i32], u: [&i64[], i32]): [&Node, &i64[]] { return [t[0], u[0]]; }

public function snapDown(let node: &Node): [&Node, &i64[]] { const t: [&Node, i32] = [&node.kids[0], 0]; node = &node.kids[0]; const u: [&i64[], i32] = [&node.val, 0]; return pick(t, u); }
"##,
        expected: &[("EN0616", 3)],
    },
    Case {
        id: "H40: parts of two tuple locals passed to a call, with no repoint",
        file: "main.en",
        source: r##"let root = new Node(); let kid = new Node(); kid.val.push(1); root.kids.push(kid);
const [k, w] = snapDown(&root); const f = &w[0];
k.val = [];
console.log(*f);

public class Node { public val: i64[] = []; public kids: Node[] = []; }

public function pick(t: [&Node, i32], u: [&i64[], i32]): [&Node, &i64[]] { return [t[0], u[0]]; }

public function snapDown(node: &Node): [&Node, &i64[]] { const t: [&Node, i32] = [&node.kids[0], 0]; const u: [&i64[], i32] = [&node.val, 0]; return pick(t, u); }
"##,
        expected: &[],
    },
    Case {
        id: "`dispose` moves its value",
        file: "main.en",
        source: r##"let a: i64[] = [1];
const w = new W(&a[0]);
dispose(w);
console.log(w.get());
public class W { private r: &i64; public constructor(r: &i64) { this.r = r; } public get(): i64 { return *this.r; } public destructor() { console.log(*this.r); } }
"##,
        expected: &[("EN0601", 4)],
    },
    Case {
        id: "`dispose` of a place behind a reference is a move out of it",
        file: "main.en",
        source: r##"let a: i64[] = [1];
let w = new W(&a[0]);
const r = &w;
dispose(*r);
public class W { private r: &i64; public constructor(r: &i64) { this.r = r; } public get(): i64 { return *this.r; } public destructor() { console.log(*this.r); } }
"##,
        expected: &[("EN0603", 4)],
    },
    Case {
        id: "`dispose` runs the destructor there, ending its loans",
        file: "main.en",
        source: r##"let a: i64[] = [1];
const w = new W(&a[0]);
dispose(w);
a.push(2);
console.log(a);
public class W { private r: &i64; public constructor(r: &i64) { this.r = r; } public get(): i64 { return *this.r; } public destructor() { console.log(*this.r); } }
"##,
        expected: &[],
    },
    Case {
        id: "without `dispose` the destructor at the scope end still holds its loans",
        file: "main.en",
        source: r##"let a: i64[] = [1];
const w = new W(&a[0]);
a.push(2);
console.log(a);
public class W { private r: &i64; public constructor(r: &i64) { this.r = r; } public get(): i64 { return *this.r; } public destructor() { console.log(*this.r); } }
"##,
        expected: &[("EN0706", 3)],
    },
    Case {
        id: "`dispose` of a reference evaluates its argument, a move into a call included",
        file: "main.en",
        source: r##"let a: i64[] = [1];
const s = "x".toString();
dispose(pick(s, &a));
console.log(s);
public function pick(s: string, r: &i64[]): &i64[] { console.log(s); return r; }
"##,
        expected: &[("EN0601", 4)],
    },
    Case {
        id: "`dispose` of a reference ends no loan it does not hold",
        file: "main.en",
        source: r##"let a: i64[] = [1];
const s = "x".toString();
dispose(pick(s, &a));
a.push(2);
console.log(a);
public function pick(s: string, r: &i64[]): &i64[] { console.log(s); return r; }
"##,
        expected: &[],
    },
    Case {
        id: "`mem.forget` moves its value",
        file: "main.en",
        source: r##"let a: i64[] = [1];
const w = new W(&a[0]);
mem.forget(w);
console.log(w.get());
public class W { private r: &i64; public constructor(r: &i64) { this.r = r; } public get(): i64 { return *this.r; } public destructor() { console.log(*this.r); } }
"##,
        expected: &[("EN0601", 4)],
    },
    Case {
        id: "`mem.forget` ends its loans with no destructor",
        file: "main.en",
        source: r##"let a: i64[] = [1];
const w = new W(&a[0]);
mem.forget(w);
a.push(2);
console.log(a);
public class W { private r: &i64; public constructor(r: &i64) { this.r = r; } public get(): i64 { return *this.r; } public destructor() { console.log(*this.r); } }
"##,
        expected: &[],
    },
    Case {
        id: "`mem.replace` writes its target",
        file: "main.en",
        source: r##"let x: i64[] = [1];
const e = &x[0];
const old = mem.replace(&x, [5]);
console.log(*e, old);
"##,
        expected: &[("EN0706", 3)],
    },
    Case {
        id: "`mem.replace` moves its new value",
        file: "main.en",
        source: r##"let x: i64[] = [1];
const v: i64[] = [2];
const old = mem.replace(&x, v);
console.log(v, old);
"##,
        expected: &[("EN0601", 4)],
    },
    Case {
        id: "`mem.replace`'s result holds no loan of the target",
        file: "main.en",
        source: r##"let x: i64[] = [1];
const old = mem.replace(&x, [5]);
x.push(1); x.push(2);
console.log(old, x);
"##,
        expected: &[],
    },
    Case {
        id: "`mem.swap` writes both targets",
        file: "main.en",
        source: r##"let a: i64[] = [1];
let b: i64[] = [2];
const e = &b[0];
mem.swap(&a, &b);
console.log(*e);
"##,
        expected: &[("EN0706", 4)],
    },
    Case {
        id: "`clone` reads its object",
        file: "main.en",
        source: r##"let a: i64[] = [1];
const e = &a[0];
const c = a.clone();
console.log(*e, c);
"##,
        expected: &[],
    },
    Case {
        id: "`clone`'s result holds no loan of its object",
        file: "main.en",
        source: r##"let a: i64[] = [1];
const c = a.clone();
a.push(2); a.push(3);
console.log(c);
"##,
        expected: &[],
    },
    Case {
        id: "a synthesised `clone`'s result holds no loan of its object",
        file: "main.en",
        source: r##"let p = new P();
const c = p.clone();
p.xs.push(2);
console.log(c.xs);
public class P implements Clone { public xs: i64[] = [1]; }
"##,
        expected: &[],
    },
    Case {
        id: "`unbox` uses its box up",
        file: "main.en",
        source: r##"const b = new Box<i64[]>([1]);
const v = b.unbox();
console.log(v, *b);
"##,
        expected: &[("EN0601", 3)],
    },
    Case {
        id: "`unbox`'s result is its own",
        file: "main.en",
        source: r##"let b = new Box<i64[]>([1]);
const v = b.unbox();
b = new Box<i64[]>([2]);
console.log(v, *b);
"##,
        expected: &[],
    },
    Case {
        id: "`unbox` of a type parameter compiles with its class check",
        file: "main.en",
        source: r##"const a = take(new Box<Animal>(new Animal()));
console.log(a.n);
public function take<T>(b: Box<T>): T { return b.unbox(); }
public class Animal { public n: i64 = 1; }
"##,
        expected: &[],
    },
    Case {
        id: "`new Box` moves its value",
        file: "main.en",
        source: r##"const v: i64[] = [1];
const b = new Box<i64[]>(v);
console.log(v, *b);
"##,
        expected: &[("EN0601", 3)],
    },
    Case {
        id: "a box's contents are its own: a write meets a borrow of them",
        file: "main.en",
        source: r##"let b = new Box<i64[]>([1]);
const e = &(*b)[0];
b.push(2);
console.log(*e);
"##,
        expected: &[("EN0706", 3)],
    },
    Case {
        id: "`Slice.fromRaw` inside `unsafe` holds no loan (A:1034)",
        file: "main.en",
        source: r##"let a: i64[] = [1, 2];
const p = a.asPtr();
unsafe { const s = Slice.fromRaw(p, 2); console.log(s); }
"##,
        expected: &[],
    },
    Case {
        id: "`asPtr` holds no loan",
        file: "main.en",
        source: r##"let a: i64[] = [1, 2];
const p = a.asPtr();
a.push(3);
console.log(a);
"##,
        expected: &[],
    },
    Case {
        id: "a `slice` view holds a loan of its array",
        file: "main.en",
        source: r##"let a: i64[] = [1, 2];
const s = a.slice(0, 1);
a.push(3);
console.log(s);
"##,
        expected: &[("EN0706", 3)],
    },
    Case {
        id: "the `splitAt` views hold loans of their array",
        file: "main.en",
        source: r##"let a: i64[] = [1, 2];
const [l, r] = a.splitAt(1);
a.push(3);
console.log(l, r);
"##,
        expected: &[("EN0706", 3)],
    },
    Case {
        id: "the two `splitAt` views of a writable view can each be written",
        file: "main.en",
        source: r##"let a: i64[] = [1, 2, 3];
const [l, r] = a.slice(0).splitAt(1);
l[0] = 7; r[0] = 8;
console.log(a);
"##,
        expected: &[],
    },
    Case {
        id: "`+=` on a string writes it",
        file: "main.en",
        source: r##"let s = "ab".toString();
const v = s.slice(0, 1);
s += "cd";
console.log(v);
"##,
        expected: &[("EN0706", 3)],
    },
    Case {
        id: "`+=` on a string before a view of it",
        file: "main.en",
        source: r##"let s = "ab".toString();
s += "cd";
const v = s.slice(0, 1);
console.log(v);
"##,
        expected: &[],
    },
    Case {
        id: "`+` on strings makes a string of its own",
        file: "main.en",
        source: r##"let s = "ab".toString();
let t = "cd".toString();
const c = s + t;
s = "x".toString(); t = "y".toString();
console.log(c);
"##,
        expected: &[],
    },
    Case {
        id: "`+` on strings reads them",
        file: "main.en",
        source: r##"let s = "ab".toString();
const v = s.slice(0, 1);
const c = s + "z";
console.log(v, c);
"##,
        expected: &[],
    },
    Case {
        id: "`console.log`'s template holes are reads",
        file: "main.en",
        source: r##"let a: i64[] = [1];
log(&a);
public function log(let r: &i64[]): void { const w: &i64[] = r; console.log(`${r[0]}`); w.push(1); }
"##,
        expected: &[("EN0708", 3)],
    },
    Case {
        id: "`console.log`'s template holes and plain arguments are reads",
        file: "main.en",
        source: r##"let a: i64[] = [1];
log(&a);
public function log(let r: &i64[]): void { const w: &i64[] = r; w.push(0); console.log(`${r[0]}`, r); w.push(1); }
"##,
        expected: &[("EN0708", 3), ("EN0708", 3)],
    },
    Case {
        id: "`console.error`'s template holes are reads",
        file: "main.en",
        source: r##"let a: i64[] = [1];
g(&a);
public function g(let r: &i64[]): void { const w: &i64[] = r; w.push(0); console.error(`${r[0]}`); w.push(1); }
"##,
        expected: &[("EN0708", 3)],
    },
    Case {
        id: "`panic`'s template holes are reads",
        file: "main.en",
        source: r##"let a: i64[] = [1];
g(&a);
public function g(let r: &i64[]): void { const w: &i64[] = r; w.push(0); if (r.length() > 5) { panic(`${r[0]}`); } w.push(1); }
"##,
        expected: &[("EN0708", 3)],
    },
    Case {
        id: "`Err` moves its text",
        file: "main.en",
        source: r##"const r = f("x".toString());
console.log(r);
public function f(s: string): Result<i64> { const e: Result<i64> = Err(s); console.log(s); return e; }
"##,
        expected: &[("EN0601", 3)],
    },
    Case {
        id: "`Err` of a text used before",
        file: "main.en",
        source: r##"const r = f("x".toString());
console.log(r);
public function f(s: string): Result<i64> { console.log(s); return Err(s); }
"##,
        expected: &[],
    },
    Case {
        id: "`?` moves its result",
        file: "main.en",
        source: r##"console.log(g());
public function f(): Result<i64[]> { return Ok([1]); }
public function g(): Result<i64> { const r = f(); const v = r?; console.log(r); return Ok(v[0]); }
"##,
        expected: &[("EN0601", 3)],
    },
    Case {
        id: "`?` of a result not used again",
        file: "main.en",
        source: r##"console.log(g());
public function f(): Result<i64[]> { return Ok([1]); }
public function g(): Result<i64> { const r = f(); const v = r?; return Ok(v[0]); }
"##,
        expected: &[],
    },
    Case {
        id: "`failureFromDisplay` reads its value, and the `Failure` holds no loan",
        file: "main.en",
        source: r##"import { failureFromDisplay } from "alloc/string";
let p = new P();
const f = failureFromDisplay(&p);
p.n = 5;
console.log(f, p);
public class P implements Display { public n: i64 = 0; public fmt(let f: &Formatter): void { writeTo(f, "p"); } }
"##,
        expected: &[],
    },
    Case {
        id: "`push` writes its array",
        file: "main.en",
        source: r##"let a: i64[] = [1];
const e = &a[0];
a.push(2);
console.log(*e);
"##,
        expected: &[("EN0706", 3)],
    },
    Case {
        id: "`push` moves its value",
        file: "main.en",
        source: r##"let a: string[] = [];
const s = "x".toString();
a.push(s);
console.log(s);
"##,
        expected: &[("EN0601", 4)],
    },
    Case {
        id: "a spread reads its array",
        file: "main.en",
        source: r##"let a: i64[] = [1];
const e = &a[0];
const b = [...a, 2];
console.log(*e, b);
"##,
        expected: &[],
    },
    Case {
        id: "an array built by a spread holds no loan of the spread array",
        file: "main.en",
        source: r##"let a: i64[] = [1];
const b = [...a, 2];
a.push(3);
console.log(b);
"##,
        expected: &[],
    },
    Case {
        id: "`expect`'s arguments are reads",
        file: "main.test.en",
        source: r##"test("reads", () => {
  let a: i64[] = [1];
  const w: &i64[] = &a;
  w.push(0);
  expect(a[0]).toBe(1);
  w.push(1);
});
"##,
        expected: &[("EN0708", 5)],
    },
    Case {
        id: "`expect` after the writes",
        file: "main.test.en",
        source: r##"test("reads", () => {
  let a: i64[] = [1];
  const w: &i64[] = &a;
  w.push(0);
  w.push(1);
  expect(a[0]).toBe(1);
});
"##,
        expected: &[],
    },
];

pub fn register(h: &mut Harness) {
    for case in CASES {
        h.case(format!("audit/{}", case.id), move || {
            let want: Vec<(String, u32)> = (case.expected.iter())
                .map(|&(code, line)| (code.to_owned(), line))
                .collect();
            assert_eq!(crate::support::phase3_as(case.file, case.source), want);
        });
    }
}
