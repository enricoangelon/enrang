//! The fix stage's phase-3 programs (M3 stage 2 fixes, borrowck side): each
//! finding of the second review that phase 3 now answers as its doc row, rule or
//! `rustc` twin says, pinned as (code, line) in report order; and the programs
//! that kill the review's surviving mutants of `enrang-borrowck`.

use enrang_testkit::Harness;

/// One program, the finding or row it answers, and what phase 3 reports.
struct Fix {
    id: &'static str,
    source: &'static str,
    expected: &'static [(&'static str, u32)],
}

const FIXES: &[Fix] = &[
    Fix {
        id: "T:723 a move beside the held source in a loop (m28)",
        source: r##"let h = new Holder { items: [1, 2], other: "o".toString() };
for (const x of &h.items) { take(h.other); }

function take(x: string): void { console.log(x); }
public class Holder { public items: i64[]; public other: string; }
"##,
        expected: &[("EN0611", 2)],
    },
    Fix {
        id: "T:723 a conditional move beside the held source, then a read (m28d)",
        source: r##"let h = new Holder { items: [1, 2], other: "o".toString() };
for (const x of &h.items) { if (*x > 1) { take(h.other); } }
console.log(h.other);

function take(x: string): void { console.log(x); }
public class Holder { public items: i64[]; public other: string; }
"##,
        expected: &[("EN0611", 2)],
    },
    Fix {
        id: "A:1007 a move of the held source is the hold's EN0709 alone (m27)",
        source: r##"let q = ["a".toString()];
for (const x of &q) { take(q); }

function take(x: string[]): void { console.log(x); }
"##,
        expected: &[("EN0709", 2)],
    },
    Fix {
        id: "A:991 a move out of a class with a destructor in a loop is EN0607 alone (m47)",
        source: r##"let h = new Holder { items: [1, 2], other: "o".toString() };
for (const x of &h.items) { take(h.other); }

function take(x: string): void { console.log(x); }
public class Holder { public items: i64[]; public other: string; public destructor() { console.log("bye"); } }
"##,
        expected: &[("EN0607", 2)],
    },
    Fix {
        id: "A:1005 a field moved and assigned again is no move site of a later whole use (m42)",
        source: r##"let p = new Pair { a: "a".toString(), b: "b".toString() };
if (p.a.length() > 5) { take(p.b); }
let i = 0;
while (i < 2) {
  show(&p);
  take(p.a);
  p.a = "c".toString();
  i++;
}

function take(x: string): void { console.log(x); }
function show(x: &Pair): void { console.log(x.a); }
public class Pair { public a: string; public b: string; }
"##,
        expected: &[("EN0601", 5)],
    },
    Fix {
        id: "V-ME-06-err a move out of an index through a reference",
        source: r##"console.log(firstErr(&["a".toString()]));

public function firstErr(names: &Slice<string>): Result<i64> { return Err(names[0]); }
"##,
        expected: &[("EN0604", 3)],
    },
    Fix {
        id: "T:935 `names[0]` through a `&string[]` parameter (m25)",
        source: r##"const xs = ["a".toString()];
console.log(first(&xs));

function first(names: &string[]): string { const s = names[0]; return s; }
"##,
        expected: &[("EN0604", 4)],
    },
    Fix {
        id: "A:995 an assignment to another parameter inside a default (r10)",
        source: r##"console.log(f(1));

function f(a: i64, b: i64 = (a = 5)): i64 { return a + b; }
"##,
        expected: &[("EN0613", 3)],
    },
    Fix {
        id: "A:937 a default's nested call stores only its own parameter (r15)",
        source: r##"console.log(f(), f("x".toString()));

function f(s: string = g(h())): string { return s; }
function g(x: string): string { return x; }
function h(): string { return "abc".toString(); }
"##,
        expected: &[],
    },
    Fix {
        id: "A:995 a by-value parameter written under a plain `lt` test (m50)",
        source: r##"console.log(f(1));

function f(x: i64): i64 { if (x < 3) { x = 3; } return x; }
"##,
        expected: &[("EN0613", 3)],
    },
    Fix {
        id: "S:981 a local function moving a captured variable (m44)",
        source: r##"let name = "a".toString();
function eat(): void { take(name); }
eat();

function take(x: string): void { console.log(x); }
"##,
        expected: &[("EN0617", 2)],
    },
    Fix {
        id: "T:820 a local function writing a captured `const`, at the write (m41)",
        source: r##"const count = 0;
function inc(): void { count += 1; }
inc();
"##,
        expected: &[("EN0608", 2)],
    },
    Fix {
        id: "T:820 a local function writing a captured `const` through another, at the write",
        source: r##"const count = 0;
function inc(): void { bump(); }
function bump(): void { count += 1; }
inc();
"##,
        expected: &[("EN0608", 3)],
    },
    Fix {
        id: "T:820 a local function writing a captured `let` compiles",
        source: r##"let count = 0;
function inc(): void { count += 1; }
inc();
console.log(count);
"##,
        expected: &[],
    },
    Fix {
        id: "S:1206 a write through a raw pointer (raw1)",
        source: r##"public unsafe function poke(p: *u16, v: u16): void {
  *p = v;
}
"##,
        expected: &[],
    },
    Fix {
        id: "S:756 a write of an `unsafe let` (raw2)",
        source: r##"private unsafe let counter: i64 = 0;
public function bump(): void {
  unsafe { counter += 1; }
}
"##,
        expected: &[],
    },
    Fix {
        id: "plan d.3 a reference made through a raw pointer stays read-only",
        source: r##"public unsafe function peek(p: *i64[]): void {
  const r = &*p;
  r.push(1);
}
"##,
        expected: &[("EN0614", 3)],
    },
    Fix {
        id: "FV-02-upcast-local one EN0706 at an upcast receiver's call",
        source: r##"const tbl: u8[] = [0];
let buf: u8[] = [1];
Sub.demo(&tbl, &buf);
public class Base {
  private src: readonly &u8[];
  public constructor(s: &u8[]) { this.src = s; }
  public peek(): readonly &u8 { return &this.src[0]; }
  public retarget(v: &u8[]): void { this.src = v; }
}
public final class Sub extends Base {
  private dst: &u8[];
  public constructor(s: &u8[], d: &u8[]) { this.dst = d; super(s); }
  public step(): void { this.dst.push(1); }
  public static demo(s: &u8[], d: &u8[]): void {
    let w = new Sub(s, d);
    const p = w.dst;
    w.retarget(p);
    const a = w.peek();
    w.step(); w.step(); w.step(); w.step();
    console.log(*a);
  }
}
"##,
        expected: &[
            ("EN0706", 17),
            ("EN0706", 19),
            ("EN0706", 19),
            ("EN0706", 19),
            ("EN0706", 19),
        ],
    },
    Fix {
        id: "HOLD-through in a method over `&this.items`",
        source: r##"let b = new Bag();
b.tally();
console.log(b.count);

public class Bag {
  public items: i64[] = [1, 2, 3];
  public count: i64 = 0;
  public tally(): void { for (const x of &this.items) { this.count += x; } }
}
"##,
        expected: &[],
    },
    Fix {
        id: "HOLD-through through a local reference `r`",
        source: r##"let s = new S();
let r = &s;
for (const x of &r.items) { r.count += 1; }
console.log(s.count);

public class S { public items: i64[] = [1, 2]; public count: i64 = 0; }
"##,
        expected: &[],
    },
    Fix {
        id: "HOLD-through repointing `r` in the body stays EN0706",
        source: r##"let s = new S();
let t = new S();
let r = &s;
for (const x of &r.items) { r = &t; }
console.log(r.count);

public class S { public items: i64[] = [1, 2]; public count: i64 = 0; }
"##,
        expected: &[("EN0706", 4)],
    },
    Fix {
        id: "HOLD-through writing the source through `r` stays EN0706",
        source: r##"let s = new S();
let r = &s;
for (const x of &r.items) { r.items.push(1); }

public class S { public items: i64[] = [1, 2]; public count: i64 = 0; }
"##,
        expected: &[("EN0706", 3)],
    },
    Fix {
        id: "A:1230 a write of another field in a loop over a reference field",
        source: r##"const data: i64[] = [1, 2, 3];
let b = new Bag(&data);
b.tally();
console.log(b.count);

public class Bag {
  private items: &i64[];
  public count: i64 = 0;
  public constructor(items: &i64[]) { this.items = items; }
  public tally(): void { for (const x of this.items) { this.count += x; } }
}
"##,
        expected: &[],
    },
    Fix {
        id: "LTK-5 repointing the reference field the loop goes through",
        source: r##"const data: i64[] = [1, 2];
const other: i64[] = [3];
let b = new Bag(&data);
b.tally(&other);

public class Bag {
  private view: &i64[];
  public count: i64 = 0;
  public constructor(v: &i64[]) { this.view = v; }
  public tally(o: &i64[]): void { for (const x of this.view) { this.view = o; } }
}
"##,
        expected: &[("EN0706", 10)],
    },
    Fix {
        id: "T:729 repointing the reference slot the loop goes through",
        source: r##"const a: i64[] = [1];
const b: i64[] = [2];
let r = &a;
for (const x of r) { r = &b; }
console.log(r);
"##,
        expected: &[("EN0706", 4)],
    },
    Fix {
        id: "A:1349 stage 4 does not depend on the visit order (s1)",
        source: r##"let v: i64[] = [1];
const p = f(&v, 1);
const e = &p[0][0];
p[1].push(2);
console.log(*e);

public function f(r: &i64[], n: i64): [&i64[], &i64[]] { return g(r, n); }
public function g(r: &i64[], n: i64): [&i64[], &i64[]] { if (n == 0) { return [r, r]; } return f(r, n - 1); }
"##,
        expected: &[("EN0614", 4)],
    },
    Fix {
        id: "A:1349 stage 4 in an SCC, a constant reached through a cycle (a01)",
        source: r##"f(1)[0] = 5;

public function f(n: i64): &Slice<i64> { return g(n); }
public function g(n: i64): &Slice<i64> { if (n == 0) { return &[0, 0]; } return f(n - 1); }
"##,
        expected: &[("EN0616", 1)],
    },
    Fix {
        id: "N12 a part of a `let` tuple parameter in an unsafe function (u1)",
        source: r##"let d: i64[] = [1];
const e = &d[0];
unsafe { grow([&d, 1]); }
console.log(*e);

public unsafe function grow(let p: [&i64[], i32]): void { p[0].push(4); }
"##,
        expected: &[("EN0706", 3)],
    },
    Fix {
        id: "N12 a part of a `let` tuple parameter with an `unsafe` block (u4)",
        source: r##"let d: i64[] = [1];
const e = &d[0];
grow([&d, 1]);
console.log(*e);

public function grow(let p: [&i64[], i32]): void { const x: i64 = 1; const q = &x as *i64; unsafe { console.log(*q); } p[0].push(4); }
"##,
        expected: &[("EN0706", 3)],
    },
    Fix {
        id: "TK-03-tail two turns over a view stay writable",
        source: r##"let q: i64[] = [9, 1, 5, 3, 7];
const p = pairBig(&q);
if (p != null) { *p[0] = 0; *p[1] = 0; }
console.log(q);

public function pairBig(xs: &Slice<i64>): [&i64, &i64] | null {
  let a: &i64 | null = null;
  for (const x of xs.slice(1)) {
    if (a != null && *x > 2) { return [a, x]; }
    if (*x > 2) { a = x; }
  }
  return null;
}
"##,
        expected: &[],
    },
    Fix {
        id: "TK-03-copied-ref two turns over a copied reference stay writable",
        source: r##"let q: i64[] = [1, 5, 3, 7];
const p = pairBig(&q);
if (p != null) { *p[0] = 0; *p[1] = 0; }
console.log(q);

public function pairBig(xs: &Slice<i64>): [&i64, &i64] | null {
  let a: &i64 | null = null;
  const r = xs;
  for (const x of r) {
    if (a != null && *x > 2) { return [a, x]; }
    if (*x > 2) { a = x; }
  }
  return null;
}
"##,
        expected: &[],
    },
    Fix {
        id: "S2-25-pair pairBig over `xs` stays writable (M43)",
        source: r##"let q: i64[] = [1, 5, 3, 7];
const p = pairBig(&q);
if (p != null) { *p[0] = 0; *p[1] = 0; }
console.log(q);

public function pairBig(xs: &Slice<i64>): [&i64, &i64] | null {
  let a: &i64 | null = null;
  for (const x of xs) {
    if (a != null && *x > 2) { return [a, x]; }
    if (*x > 2) { a = x; }
  }
  return null;
}
"##,
        expected: &[],
    },
    Fix {
        id: "C4-super-paths a temporary `new Dog(n)` is no `super(...)` (c33)",
        source: r##"const c = new Cat("x");
console.log(c.name);

public class Animal { public constructor(public name: string) {} }
public class Dog extends Animal {}
public class Cat extends Animal {
  public constructor(n: string) { console.log(new Dog(n).name); }
}
"##,
        expected: &[("EN0619", 7)],
    },
    Fix {
        id: "C4-super-paths an inherited `new` in a constructor that never calls `super` (c32)",
        source: r##"const c = new Cat("x");
console.log(c.name);

public class Animal { public constructor(public name: string) {} }
public class Dog extends Animal {}
public class Cat extends Animal {
  public constructor(n: string) { const d = new Dog(n); console.log(d.name); }
}
"##,
        expected: &[("EN0619", 7)],
    },
    Fix {
        id: "Q31-ctor-order a subclass with no constructor prints (c31)",
        source: r##"{ const d = new Dog("Rex"); console.log(d.describe()); }

public class Animal {
  public constructor(public name: string) { console.log(`ctor: ${this.describe()}`); }
  public describe(): string { return `${this.name} makes a sound`; }
}
public class Dog extends Animal {
  protected tricks: string[] = ["sit", "roll"];
  public override describe(): string { return `${this.name} knows ${this.tricks[0]}`; }
}
"##,
        expected: &[],
    },
    Fix {
        id: "C4-override-nodefault compiles (c28)",
        source: r##"{ const d = new Dog(new Person("Ada")); }
console.log("end");

public class Person { public constructor(public name: string) {} public destructor() { console.log(`bye ${this.name}`); } }
public class Animal {
  protected owner: Person;
  public constructor(o: Person) { this.owner = o; }
}
public class Dog extends Animal {
  protected override owner: Person = new Person("nobody");
}
"##,
        expected: &[],
    },
    Fix {
        id: "A:939 a `super` past an intermediate class with no constructor (p16)",
        source: r##"const c = new C(5);
const b = new B();
const a = new A("x");
console.log(c, b, a);

public class A {
  public tag: string = "a";
  public n: i64 = 1;
  public constructor(public name: string = "anon", public nick?: string) {}
}
public class B extends A {
  public override n: i64 = 2;
}
public class C extends B {
  public override tag: string = "c";
  public w: i64;
  public constructor(w: i64, k: i64 = w + 1) {
    this.w = k;
    super("cc");
  }
}
"##,
        expected: &[],
    },
    Fix {
        id: "A:939 a subclass's string and call defaults stored before the base constructor",
        source: r##"const b = new B("x");
console.log(b.name, b.label, b.tag);

public class A {
  public constructor(public name: string) {}
}
public class B extends A {
  public label: string = "lbl";
  public tag: string = mk();
}
private function mk(): string { return "t".toString(); }
"##,
        expected: &[],
    },
    Fix {
        id: "S:981 an arrow pushing a captured `const` (k3)",
        source: r##"const x: i64[] = [1];
run(() => { x.push(2); });

function run(f: () => void): void { f(); }
"##,
        expected: &[("EN0614", 2)],
    },
    Fix {
        id: "S:981 a closure local pushing a captured `const` (k8)",
        source: r##"const x: i64[] = [1];
const f = () => { x.push(2); };
f();
"##,
        expected: &[("EN0614", 2)],
    },
    Fix {
        id: "S:981 an arrow reading a captured `const` beside a written `let`",
        source: r##"const x: i64[] = [1];
let v: i64[] = [];
run(() => { v.push(x[0]); });
console.log(v);

function run(f: () => void): void { f(); }
"##,
        expected: &[],
    },
    Fix {
        id: "S:981 an arrow pushing through a captured `const` reference",
        source: r##"let d: i64[] = [1];
const p = &d;
run(() => { p.push(3); });
console.log(d);

function run(f: () => void): void { f(); }
"##,
        expected: &[],
    },
    Fix {
        id: "A:970 a literal view a closure writes through stays a temporary (s4)",
        source: r##"const p: &Slice<i64> = &[1, 2];
run(() => { p[0] = 9; });
console.log(p);

function run(f: () => void): void { f(); }
"##,
        expected: &[("EN0712", 1)],
    },
    Fix {
        id: "RO-loop-const a loop over a constant literal view (b01)",
        source: r##"*firstOf() = 1;

public function zeros(): &Slice<i64> { return &[0, 0]; }
public function firstOf(): &i64 { for (const x of zeros()) { return x; } panic("none"); }
"##,
        expected: &[("EN0616", 1)],
    },
    Fix {
        id: "S:964 `return &[0, 0]` from a `&Slice<i64>` function (b02)",
        source: r##"console.log(zeros());

public function zeros(): &Slice<i64> { return &[0, 0]; }
"##,
        expected: &[],
    },
    Fix {
        id: "A:1222 a part copy of a tuple local written through",
        source: r##"let v: i64[] = [1, 2];
let pair: [&i64[], i32] = [&v, 1];
const p2 = pair;
const f = &p2[0][0];
pair[0].push(4);
console.log(*f);
"##,
        expected: &[("EN0706", 5)],
    },
    Fix {
        id: "A:935 a part copy of a tuple local into a written binding",
        source: r##"let v: i64[] = [1, 2];
let pair: [&i64[], i32] = [&v, 1];
const x = &pair[0][0];
const b2 = pair[0];
b2.push(9);
console.log(*x);
"##,
        expected: &[("EN0706", 4)],
    },
    Fix {
        id: "A:935 a second part copy beside a written one (tuple part access)",
        source: r##"let v: i64[] = [1, 2];
let t: [&i64[], i32] = [&v, 1];
const a = t[0];
const b = t[0];
const e = &b[0];
a.push(3);
a.push(4);
console.log(*e);
"##,
        expected: &[("EN0708", 4)],
    },
    Fix {
        id: "A:935 a second part copy beside a written one, the reference-local twin",
        source: r##"let v: i64[] = [1, 2];
const r = &v;
const a = r;
const b = r;
const e = &b[0];
a.push(3);
a.push(4);
console.log(*e);
"##,
        expected: &[("EN0708", 4)],
    },
    Fix {
        id: "FV-02-through-ref the tuple form",
        source: r##"let buf: u8[] = [1];
let t: [&u8[], i32] = [&buf, 1];
const r = &t;
const e = &r[0][0];
t[0].push(9);
t[0].push(9);
console.log(*e);
"##,
        expected: &[("EN0706", 5), ("EN0706", 6)],
    },
    Fix {
        id: "FV-02-through-ref the tuple form through a copy",
        source: r##"let buf: u8[] = [1];
let t: [&u8[], i32] = [&buf, 1];
const r = &t;
const t2 = *r;
t[0].push(9);
t[0].push(9);
console.log(t2[0][0]);
"##,
        expected: &[("EN0706", 5), ("EN0706", 6)],
    },
    Fix {
        id: "FV-02-through-ref the Copier forms (H03)",
        source: r##"Copier.demo();
const t0: u8[] = [3];
let o0: u8[] = [4];
let c0 = new Copier(&t0, &o0);
Copier.f(&c0, &t0);
Copier.g();

public final class Copier {
  private src: readonly &u8[];
  private dst: &u8[];
  public constructor(s: &u8[], d: &u8[]) { this.src = s; this.dst = d; }
  public step(): void { this.dst.push(1); }
  public static demo(): void { let out: u8[] = [1]; const tbl: u8[] = [0]; let c = new Copier(&tbl, &out); const rc = &c; const d0 = &rc.dst[0]; c.step(); c.step(); console.log(*d0); }
  public static f(let o: &Copier, tbl: &u8[]): void { let buf: u8[] = [1]; let c = new Copier(tbl, &buf); o = &c; const d0 = &o.dst[0]; c.step(); c.step(); console.log(*d0); }
  public static g(): void { const tbl: u8[] = [7]; let out: u8[] = []; let c = new Copier(&tbl, &out); const rc = &c; const a = &rc.src[0]; c.step(); c.step(); console.log(*a, out); }
}
"##,
        expected: &[
            ("EN0706", 13),
            ("EN0706", 13),
            ("EN0706", 14),
            ("EN0706", 14),
        ],
    },
    Fix {
        id: "A:1030 a store through a narrowed nullable reference (f)",
        source: r##"let keep: i64[] = [1];
let h = new Holder(&keep);
{
  let tmp: i64[] = [1, 2];
  Holder.setR(&h, &tmp);
}
console.log(h.get());

public class Holder {
  private r: &i64[];
  public constructor(r: &i64[]) { this.r = r; }
  public get(): i64 { return this.r[0]; }
  public static setR(h: &Holder | null, x: &i64[]): void { if (h != null) { h.r = x; } }
}
"##,
        expected: &[("EN0711", 6)],
    },
    Fix {
        id: "A:1030 a copy through a narrowed nullable reference (h2)",
        source: r##"let r: &i64[] | null = null;
{
  let data: i64[] = [1, 2];
  let h = new Holder(&data);
  r = Holder.getR(&h);
}
if (r != null) { console.log(r[0]); }

public class Holder {
  private r: &i64[];
  public constructor(r: &i64[]) { this.r = r; }
  public static getR(h: &Holder | null): &i64[] | null { if (h != null) { const x = h.r; return x; } return null; }
}
"##,
        expected: &[("EN0711", 6)],
    },
    Fix {
        id: "A:1030 the nullable store form's non-nullable twin (d)",
        source: r##"let keep: i64[] = [1];
let h = new Holder(&keep);
let tmp: i64[] = [1, 2];
Holder.setR(&h, &tmp);
tmp = [];
console.log(h.get());

public class Holder {
  private r: &i64[];
  public constructor(r: &i64[]) { this.r = r; }
  public get(): i64 { return this.r[0]; }
  public static setR(h: &Holder, x: &i64[]): void { h.r = x; }
}
"##,
        expected: &[("EN0706", 5)],
    },
    Fix {
        id: "A:1030 the nullable store form (d)",
        source: r##"let keep: i64[] = [1];
let h = new Holder(&keep);
let tmp: i64[] = [1, 2];
Holder.setR(&h, &tmp);
tmp = [];
console.log(h.get());

public class Holder {
  private r: &i64[];
  public constructor(r: &i64[]) { this.r = r; }
  public get(): i64 { return this.r[0]; }
  public static setR(h: &Holder | null, x: &i64[]): void { if (h != null) { h.r = x; } }
}
"##,
        expected: &[("EN0706", 5)],
    },
    Fix {
        id: "TK-01-dup the nullable pair of disjoint arrays",
        source: r##"let x: i64[] = [1];
let y: i64[] = [2];
const p = pair(&x, &y);
if (p != null) { const [a, b] = p; const e = &a[0]; b.push(9); console.log(*e); }

public function pair(a: &i64[], b: &i64[]): [&i64[], &i64[]] | null { return [a, b]; }
"##,
        expected: &[],
    },
    Fix {
        id: "FV-02-skip the `share` form",
        source: r##"let table: u8[] = [7, 8, 9];
const other: u8[] = [1];
let v = new View(&other);
let f = new Feeder(&table, &v);
f.share();
table.push(4);
console.log(v.first());

public final class View { private x: readonly &u8[]; public constructor(x: &u8[]) { this.x = x; } public setX(s: &u8[]): void { this.x = s; } public first(): u8 { return this.x[0]; } }
public final class Feeder { private src: readonly &u8[]; private sink: &View; public constructor(s: &u8[], v: &View) { this.src = s; this.sink = v; } public share(): void { this.sink.setX(this.src); } }
"##,
        expected: &[("EN0706", 6)],
    },
    Fix {
        id: "FV-02-skip the `nudge` form",
        source: r##"const table: u8[3] = [7, 8, 9];
let out: u8[3] = [0, 0, 0];
let c = new Copier(&table, &out);
let w = new Wrapper(&c);
Wrapper.nudge(&w);
c.step();
console.log(out);

public final class Wrapper { private cp: &Copier; public constructor(cp: &Copier) { this.cp = cp; } public static nudge(w: &Wrapper): void { w.cp.skip(); } }
public final class Copier {
  private src: readonly &Slice<u8>;
  private dst: &Slice<u8>;
  private pos: isize = 0;
  public constructor(s: &Slice<u8>, d: &Slice<u8>) { this.src = s; this.dst = d; }
  public static make(s: &Slice<u8>, d: &Slice<u8>): Copier { return new Copier(s, d); }
  public step(): void { this.dst[this.pos] = this.src[0]; this.pos += 1; }
  public skip(): void { this.src = this.src.slice(1, this.src.length()); }
}
"##,
        expected: &[("EN0616", 5), ("EN0707", 6)],
    },
    Fix {
        id: "TK-01-split-wrap",
        source: r##"let v: i64[] = [1, 2, 3, 4];
const [lo, hi] = halves(&v);
lo[0] = hi[0];
hi[1] = 9;
console.log(v);
const [l2, h2] = kept(&v);
l2[0] = 7;
h2[0] = 8;
console.log(v);

public function halves(v: &Slice<i64>): [&Slice<i64>, &Slice<i64>] { return v.splitAt(2); }
public function kept(xs: &Slice<i64>): [&Slice<i64>, &Slice<i64>] { const p = xs.splitAt(1); return p; }
"##,
        expected: &[],
    },
    Fix {
        id: "TK-01-split-written",
        source: r##"let pt = new Pt();
pt.ys.push(1);
const [u, v] = same(&pt);
const e = &u[0];
v.push(2);
v.push(3);
v.push(4);
v.push(5);
console.log(*e);

public class Pt { public xs: i64[] = []; public ys: i64[] = []; }
public function two(a: &i64[], b: &i64[]): [&i64[], &i64[]] { return [a, b]; }
public function same(q: &Pt): [&i64[], &i64[]] { let p = two(&q.xs, &q.ys); p[0] = p[1]; return p; }
"##,
        expected: &[("EN0614", 5), ("EN0614", 6), ("EN0614", 7), ("EN0614", 8)],
    },
    Fix {
        id: "TK-01-two-turns",
        source: r##"let q: i64[] = [1, 5, 3, 7];
const p = pairBig(&q);
if (p != null) { *p[0] = 0; *p[1] = 0; }
console.log(q);

public function two(a: &i64, b: &i64): [&i64, &i64] { return [a, b]; }
public function pairBig(xs: &Slice<i64>): [&i64, &i64] | null {
  let a: &i64 | null = null;
  for (const x of xs) {
    if (*x > 2) {
      if (a != null) { return two(a, x); }
      a = x;
    }
  }
  return null;
}
"##,
        expected: &[],
    },
    Fix {
        id: "TK-01-tuple-arg",
        source: r##"let g: i64[] = [1];
const m = mk(&g);
m[1].push(2);
let h: i64[] = [1];
const p = id2([&h, &h]);
p[0].push(1);

public function id2(t: [&i64[], &i64[]]): [&i64[], &i64[]] { return t; }
public function mk(x: &i64[]): [&i64[], &i64[]] { return id2([x, x]); }
"##,
        expected: &[("EN0614", 3), ("EN0707", 5)],
    },
    Fix {
        id: "TK-01-tuple-arg through a clash",
        source: r##"let g: i64[] = [1];
const p = mk(&g);
clash(p[0], p[1]);

public function clash(a: &i64[], b: &i64[]): void { a.push(1); b.push(2); }
public function id2(t: [&i64[], &i64[]]): [&i64[], &i64[]] { return t; }
public function mk(x: &i64[]): [&i64[], &i64[]] { return id2([x, x]); }
"##,
        // One report per marked argument (SPEC 13, review 3's marks.rs:621).
        expected: &[("EN0616", 3), ("EN0616", 3)],
    },
    Fix {
        id: "TK-03-mark-literal no extra report at the destructure",
        source: r##"let grid: i64[][] = [[1, 2], [3, 4]];
const g = grab(&grid);
if (g != null) { const [rows, row] = g; const e2 = &row[0]; rows[1] = []; console.log(*e2); }

public function grab(xs: &Slice<i64[]>): [&Slice<i64[]>, &i64[]] | null { const whole = xs; const r = xs; let t: [&Slice<i64[]>, &i64[]] | null = null; for (const x of r) { if (t != null) { return [t[0], x]; } t = [whole, x]; } return null; }
"##,
        expected: &[("EN0616", 3)],
    },
    Fix {
        id: "TK-03-whole-join no extra report at the destructure",
        source: r##"let grid: i64[][] = [[1, 2], [3, 4]];
const g = grab(&grid);
if (g != null) { const [rows, row] = g; const e2 = &row[0]; rows[1] = []; console.log(*e2); }

public function grab(xs: &Slice<i64[]>): [&Slice<i64[]>, &i64[]] | null { const whole = xs; let t: [&Slice<i64[]>, &i64[]] | null = null; for (const x of xs) { if (t != null) { return [t[0], x]; } t = [whole, x]; } return null; }
"##,
        expected: &[("EN0616", 3)],
    },
    Fix {
        id: "TK-03-field-join no extra report at the destructure",
        source: r##"let root = new Node();
root.kids.push(new Node());
root.kids.push(new Node());
root.kids[1].val.push(5);
let w = new Walker(&root);
const p = w.pair(false);
if (p != null) { const [top, kid] = p; const e3 = &kid.val[0]; top.kids = []; console.log(*e3); }

public class Node { public val: i64[] = []; public kids: Node[] = []; }
public class Walker { private cur: &Node; public constructor(n: &Node) { this.cur = n; } public pair(c: bool): [&Node, &Node] | null { let a: &Node = this.cur; let n = 0; for (const x of this.cur.kids.slice(0)) { if (n == 1) { return [a, x]; } if (c) { a = x; } n += 1; } return null; } }
"##,
        expected: &[("EN0616", 7)],
    },
    Fix {
        id: "TK-03-stale-join no extra report at the destructure",
        source: r##"let grid: i64[][] = [[1, 2], [3, 4]];
const p = staleJoin(&grid);
if (p != null) { const [p0, p1] = p; const e = &p0[0]; p1.push(9); p1.push(9); console.log(*e); }

public function staleJoin(rows: &Slice<i64[]>): [&i64[], &i64[]] | null { let stale: &i64[] | null = null; let n = 0; while (n < 2) { let a: &i64[] | null = null; for (const x of rows.slice(0)) { if (n == 0) { stale = x; break; } if (a != null) { const v = stale ?? x; return [a, v]; } a = x; } n += 1; } return null; }
"##,
        expected: &[("EN0614", 3), ("EN0614", 3)],
    },
    Fix {
        id: "D20-core-1 one EN0708 at `&data[0]`",
        source: r##"let data: i64[] = [1, 2, 3];
let other: i64[] = [0];
let g = new Grower(&other);
g.setV(&data);
const e = &data[0];
g.grow();
console.log(*e);

private class Grower { private v: &i64[]; public constructor(v: &i64[]) { this.v = v; } public setV(v: &i64[]): void { this.v = v; } public grow(): void { this.v.push(4); } }
"##,
        expected: &[("EN0708", 5)],
    },
    Fix {
        id: "FV-02-upcast-local the constructor form compiles (H14, H19)",
        source: r##"const tbl: u8[] = [7, 8];
let buf: u8[] = [0];
let w = new Sub(&tbl, &buf);
w.retarget(w.peek());
w.step();
console.log(w.peek());
console.log(buf);

public class Base { private src: readonly &Slice<u8>; public constructor(s: &Slice<u8>) { this.src = s; } public peek(): readonly &Slice<u8> { return this.src.slice(0, 1); } public retarget(v: &Slice<u8>): void { this.src = v; } }
public final class Sub extends Base { private dst: &u8[]; public constructor(s: &Slice<u8>, d: &u8[]) { this.dst = d; super(s); } public static make(s: &Slice<u8>, d: &u8[]): Sub { return new Sub(s, d); } public step(): void { this.dst.push(1); } }
"##,
        expected: &[],
    },
    Fix {
        id: "A:1202 a store updates the other slots that meet it (H15)",
        source: r##"const source = "ab".toString();
let lx = new Lexer(&source);
let tok: &string | null = null;
{
  const tmp = "xy" + "z";
  const r = &lx;
  r.setSrc(&tmp);
  tok = r.next();
}
console.log(tok);

private class Lexer {
  private src: &string;
  private pos: isize;
  public constructor(src: &string) { this.src = src; }
  public setSrc(s: &string): void { this.src = s; }
  public next(): &string | null {
    if (this.pos >= this.src.length()) { return null; }
    const start = this.pos;
    this.pos = this.src.length();
    return this.src.slice(start, this.pos);
  }
}
"##,
        expected: &[("EN0711", 9)],
    },
    Fix {
        id: "A:1268 a write in a loop over its own source is EN0706 (A06)",
        source: r##"let q: i64[] = [1, 2];
for (const x of &q) { *x += 1; q.push(1); }
console.log(q);
"##,
        expected: &[("EN0706", 2)],
    },
    Fix {
        id: "A:1242 a write meets the slots live after it (A08)",
        source: r##"let x: i64 = 1;
const r = &x;
x = *r + 1;
console.log(x);
"##,
        expected: &[],
    },
    Fix {
        id: "TK-01-own-view the nullable twin (L01)",
        source: r##"let data: i64[] = [1, 2];
let h = new Holder(&data);
const p = Holder.both(&h);
if (p != null) { p[0].push(3); *p[1] = 9; }
console.log(data);

public class Holder {
  private view: &i64[];
  private own: i64[] = [];
  public constructor(v: &i64[]) { this.view = v; }
  public static both(h: &Holder | null): [&i64[], &i64] | null { if (h != null) { return [&h.own, &h.view[0]]; } return null; }
}
"##,
        expected: &[],
    },
    Fix {
        id: "G18 EN0615 at the write in the body",
        source: r##"public interface Counter {
  inc(): void;
}

public class Clicks implements Counter {
  private n: i64 = 0;
  public inc(): void { this.n += 1; }
}
"##,
        expected: &[("EN0615", 7)],
    },
    Fix {
        id: "FIT-structural EN0615 at the class",
        source: r##"let s = "hello".toString();
let t = new Tally();
f(&t, &s);

function f(z: &Sizer, v: &string): void { console.log(z.size(v)); }
public interface Measured { length(): isize; }
public interface Sizer { size<T extends Measured>(x: &T): isize; }
public class Tally {
  private n: isize = 0;
  public size<T extends Measured>(x: &T): isize { this.n += 1; return this.n; }
}
"##,
        expected: &[("EN0615", 8)],
    },
    Fix {
        id: "d.10 an implementation's EN0714 at its `return`",
        source: r##"let s = new Picker();
const a: i64[] = [1];
const b: i64[] = [2];
console.log(s.pick(&a, &b));

public interface Pick { pick(x: &i64[], y: &i64[]): &i64[]; }
public class Picker implements Pick {
  public constructor() {}
  public pick(x: &i64[], y: &i64[]): &i64[] { return y; }
}
"##,
        expected: &[("EN0714", 9)],
    },
    Fix {
        id: "OQ18-strict (M06)",
        source: r##"const a = "a".toString();
const b = "b".toString();
let s = new Strict();
console.log(s.label(&a, &b));

public class Labeler {
  public constructor() {}
  public label(name: &string, fallback: &string): &string { return name; }
}
public class Strict extends Labeler {
  public constructor() { super(); }
  public override label(name: &string, fallback: &string): &string { return fallback; }
}
"##,
        expected: &[("EN0714", 12)],
    },
    Fix {
        id: "INF-04 a storing function as an `fn` value",
        source: r##"let src = "a".toString();
let h = new Holder(&src);
attachTemp(&h, put);

function attachTemp(h: &Holder, f: fn(let h: &Holder, s: &string) => void): void { const tmp = "temp" + "!"; f(h, &tmp); }
function put(let h: &Holder, s: &string): void { h.setSrc(s); }
public class Holder {
  private src: &string;
  public constructor(s: &string) { this.src = s; }
  public setSrc(s: &string): void { this.src = s; }
}
"##,
        expected: &[("EN0615", 3)],
    },
    Fix {
        id: "INF-04 a storing function as an `fn` value, then used",
        source: r##"let src = "a".toString();
let h = new Holder(&src);
attachTemp(&h, put);
h.show();

function attachTemp(h: &Holder, f: fn(let h: &Holder, s: &string) => void): void { const tmp = "temp" + "!"; f(h, &tmp); }
function put(let h: &Holder, s: &string): void { h.setSrc(s); }
public class Holder {
  private src: &string;
  public constructor(s: &string) { this.src = s; }
  public setSrc(s: &string): void { this.src = s; }
  public show(): void { console.log(this.src); }
}
"##,
        expected: &[("EN0615", 3)],
    },
    Fix {
        id: "INF-04-take with a read-only `text()`",
        source: r##"const text = "hello world".toString();
const base = new Lexer(&text);
let s = new Sub2(&text, &base);
{ const inner = new Lexer(text.slice(6, 11)); relay(&s, &inner); }
console.log(s.peekLx());

function relay(b: &Base, o: &Lexer): void { b.take(o); }
public final class Lexer {
  private src: &string;
  public constructor(src: &string) { this.src = src; }
  public text(): readonly &string { return this.src; }
}
public class Base {
  private w: &string;
  public constructor(w: &string) { this.w = w; }
  public take(o: &Lexer): void { this.w = o.text(); }
}
public class Sub2 extends Base {
  private lx: &Lexer;
  public constructor(w: &string, l: &Lexer) { this.lx = l; super(w); }
  public override take(o: &Lexer): void { this.lx = o; }
  public peekLx(): &string { return this.lx.text(); }
}
"##,
        expected: &[("EN0615", 21)],
    },
    Fix {
        id: "EN0418 without the flag stays silent (M07, pad)",
        source: r##"const k: i64[] = [1];
const p = new Pad(&k);

public final class Pad implements Copy {
  private t: [readonly &i64[], i32];
  public constructor(a: &i64[]) { this.t = [a, 1]; }
}
"##,
        expected: &[],
    },
    Fix {
        id: "EN0418 without the flag stays silent (M07, plain copy)",
        source: r##"const p = new P();
const q = p;
console.log(p.x, q.x);

private class P implements Copy { public x: i64 = 0; }
"##,
        expected: &[],
    },
    Fix {
        id: "stage 4's `through_read` reason in an SCC (M11)",
        source: r##"let t: i64[][] = [[1, 2]];
const f = new Finder(&t);
const v = t[0].slice(0, 1);
*f.find(1) = [9];
console.log(v);

public final class Finder {
  private rows: readonly &Slice<i64[]>;
  public constructor(rows: &Slice<i64[]>) { this.rows = rows; }
  public find(n: i64): &i64[] { return this.helper(n); }
  public helper(n: i64): &i64[] { if (n == 0) { return &this.rows[0]; } return this.find(n - 1); }
}
"##,
        expected: &[("EN0616", 4)],
    },
    Fix {
        id: "FV-02-copier alias and step (M20)",
        source: r##"const table: u8[3] = [7, 8, 9];
let out: u8[3] = [0, 0, 0];
const t2: u8[3] = [1, 2, 3];
let out2: u8[3] = [5, 6, 0];
let c = new Copier(&table, &out);
let b = new Copier(&t2, &out2);
c.alias(&b);
b.step();
console.log(c.peek());

public final class Copier {
  private src: readonly &Slice<u8>;
  private dst: &Slice<u8>;
  private pos: isize = 0;
  public constructor(src: &Slice<u8>, dst: &Slice<u8>) { this.src = src; this.dst = dst; }
  public step(): void { this.dst[this.pos] = this.src[this.pos]; this.pos += 1; }
  public peek(): readonly &Slice<u8> { return this.src.slice(this.pos, this.pos + 1); }
  public alias(other: &Copier): void { this.src = other.dst; }
}
"##,
        expected: &[("EN0706", 8)],
    },
    Fix {
        id: "FV-02-base-flag (M20)",
        source: r##"const tbl: u8[] = [0];
let other: u8[] = [5];
let buf2: u8[] = [1];
let s2 = new Sub(&tbl, &buf2);
let x = new Base(&tbl, &other);
x.adopt(&s2);
const a = x.peek();
s2.step();
s2.step();
console.log(*a);

public class Base {
  private src: readonly &u8[];
  private dst: &u8[];
  public constructor(s: &u8[], d: &u8[]) { this.src = s; this.dst = d; }
  public peek(): readonly &u8 { return &this.src[0]; }
  public step(): void { this.dst.push(1); }
  public static firstOf(o: &Sub): readonly &u8 { return &o.dst[0]; }
  public adopt(o: &Sub): void { this.src = o.dst; }
}
public final class Sub extends Base {
  public constructor(s: &u8[], d: &u8[]) { super(s, d); }
}
"##,
        expected: &[("EN0706", 8), ("EN0706", 9)],
    },
    Fix {
        id: "the `through_fields` EN0714 clause of an override (M25)",
        source: r##"const d: u8[] = [1, 2];
let s = new Sub();
const lx = new Lexer(&d);
console.log(s.m(&lx));

public final class Lexer {
  private src: &Slice<u8>;
  private own: u8[] = [7];
  public constructor(s: &Slice<u8>) { this.src = s; }
  public peek(): readonly &Slice<u8> { return this.src.slice(0, 1); }
  public mine(): readonly &Slice<u8> { return this.own.slice(0, 1); }
}
public class Base {
  public constructor() {}
  public m(o: &Lexer): readonly &Slice<u8> { return o.peek(); }
}
public class Sub extends Base {
  public constructor() { super(); }
  public override m(o: &Lexer): readonly &Slice<u8> { return o.mine(); }
}
"##,
        expected: &[("EN0714", 19)],
    },
    Fix {
        id: "a virtual call keeps `this` out of the through sets (M30)",
        source: r##"let d: u8[] = [1, 2];
let s = new Sub(&d);
const b: &Base = &s;
const t = b.first();
s.reset();
console.log(*t);

public class Base {
  private src: &Slice<u8>;
  public constructor(s: &Slice<u8>) { this.src = s; }
  public first(): readonly &u8 { return &this.src[0]; }
}
public class Sub extends Base {
  private own: u8[] = [7];
  public constructor(s: &Slice<u8>) { super(s); }
  public override first(): readonly &u8 { return &this.own[0]; }
  public reset(): void { this.own = [9]; }
}
"##,
        expected: &[("EN0706", 5)],
    },
    Fix {
        id: "TK-01-copy-join (M41)",
        source: r##"let pt = new Pt();
pt.xs.push(1);
pt.xs.push(2);
const [u, v] = lanes(&pt, false);
const e = &u[0];
v.push(3);
v.push(4);
console.log(*e);

public class Pt { public xs: i64[] = []; public ys: i64[] = []; }
public function lanes(p: &Pt, c: bool): [&i64[], &i64[]] { const s = p; const second = c ? &p.ys : &s.xs; return [&p.xs, second]; }
"##,
        expected: &[("EN0614", 6), ("EN0614", 7)],
    },
    Fix {
        id: "TK-01-local-kill (M41)",
        source: r##"let root = new Node();
let kid = new Node();
kid.val.push(1);
root.kids.push(kid);
const [k, w] = snapDown(&root);
const f = &w[0];
k.val = [];
console.log(*f);

public class Node { public val: i64[] = []; public kids: Node[] = []; }
public function snapDown(let node: &Node): [&Node, &i64[]] { const t: [&Node, i32] = [&node.kids[0], 0]; node = &node.kids[0]; return [t[0], &node.val]; }
"##,
        expected: &[("EN0616", 7)],
    },
    Fix {
        id: "a method's flag through a class-to-body edge (M47)",
        source: r##"let d: i64[] = [1];
let c = new Cur(&d);

private class Cur implements Copy {
  private v: &i64[];
  public constructor(v: &i64[]) { this.v = v; }
  public step(): void { this.put(this.v); }
  public put(x: &i64[]): void { x.push(1); }
}
"##,
        expected: &[("EN0418", 4), ("EN0708", 7)],
    },
    Fix {
        id: "a base's flag before its subclass's (M48)",
        source: r##"let buf: u8[] = [1];
const tbl: u8[] = [0];
let s = new Asub(&tbl, &buf);
s.step();

public final class Asub extends Zbase implements Copy {}
public class Zbase {
  private src: readonly &u8[];
  private dst: &u8[];
  public constructor(s: &u8[], d: &u8[]) { this.src = s; this.dst = d; }
  public step(): void { this.dst.push(1); }
}
"##,
        expected: &[("EN0418", 6)],
    },
    Fix {
        id: "C4-super-paths a second `super(...)` in a loop (M04)",
        source: r##"const d = new Dog(3);

public class Animal {
  public constructor() {}
}
public class Dog extends Animal {
  public constructor(n: i64) { let i = 0; while (i < n) { super(); i++; } }
}
"##,
        expected: &[("EN0619", 7), ("EN0619", 7)],
    },
    Fix {
        id: "a constructor moving a field of `this` (M16)",
        source: r##"const a = new Animal("x".toString());

public class Animal {
  public name: string;
  public other: string = "";
  public constructor(n: string) { this.name = n; this.other = this.name; }
}
"##,
        expected: &[("EN0603", 6)],
    },
    Fix {
        id: "an own field still unset after `super(...)` (M22)",
        source: r##"const d = new Dog("Rex");

public class Animal { public constructor(public name: string) {} }
public class Dog extends Animal {
  public owner: Animal;
  public constructor(n: string) { super(n); console.log(this.owner.name); this.owner = new Animal("x"); }
}
"##,
        expected: &[("EN0610", 6), ("EN0610", 6)],
    },
    Fix {
        id: "C4-ctorless-base an inherited field with no default (M23)",
        source: r##"console.log(new Circle(2, new Person("Ada")).describe());

public class Person { public constructor(public name: string) {} }
public class Shape {
  protected color: string = "red";
  public owner: Person;
  public describe(): string { return `${this.color} shape of ${this.owner.name}`; }
}
public class Circle extends Shape {
  public constructor(public r: i64, o: Person) { super(); }
}
"##,
        expected: &[("EN0610", 10)],
    },
    Fix {
        id: "an implicit `super()` reading an inherited field (M23)",
        source: r##"const c = new Circle(new Person("Ada"));

public class Person { public constructor(public name: string) {} }
public class Shape {
  public owner: Person;
}
public class Circle extends Shape {
  public constructor(o: Person) { super(); console.log(this.owner.name); this.owner = o; }
}
"##,
        expected: &[("EN0610", 8)],
    },
    Fix {
        id: "a nested readonly field written in a constructor (M26)",
        source: r##"const o = new Outer();

public class Inner { public readonly id: i64 = 0; }
public class Outer {
  public inner: Inner;
  public constructor() { this.inner = new Inner {}; this.inner.id = 5; }
}
"##,
        expected: &[("EN0609", 6)],
    },
    Fix {
        id: "a const's accessor result pushed (M30)",
        source: r##"const lib = new Lib { items: [1] };
lib.list().push(2);

public class Lib {
  public items: i64[];
  public list(): &i64[] { return &this.items; }
}
"##,
        expected: &[("EN0608", 2)],
    },
    Fix {
        id: "S2-14-const the loop tag through a call result (M33)",
        source: r##"const K = [1, 2];
for (const x of &K) {
  console.log(*x);
  *id(x) = 0;
}

function id(r: &i64): &i64 { return r; }
"##,
        expected: &[("EN0608", 2)],
    },
    Fix {
        id: "S:974 capturing a closure parameter passed beside it is EN0718",
        source: r##"public function outer(f: () => void): void {
  both(f, () => { f(); });
}
private function both(a: () => void, b: () => void): void { a(); b(); }
"##,
        expected: &[("EN0718", 2)],
    },
    Fix {
        id: "S:974 `twice(f, f)` is EN0718",
        source: r##"public function outer(f: () => void): void {
  twice(f, f);
}
private function twice(a: () => void, b: () => void): void { a(); b(); }
"##,
        expected: &[("EN0718", 2)],
    },
    Fix {
        id: "S:974 `visit(f, n); visit(f, m);` compiles",
        source: r##"public function outer(f: (n: i64) => void): void {
  visit(f, 1);
  visit(f, 2);
}
private function visit(a: (n: i64) => void, n: i64): void { a(n); }
"##,
        expected: &[],
    },
    Fix {
        id: "A:991 a move out of a box behind a reference is EN0603",
        source: r##"public function f(b: &Box<string>): string {
  return **b;
}
"##,
        expected: &[("EN0603", 2)],
    },
    Fix {
        id: "A:991 a move out of a box is EN0605",
        source: r##"public function f(b: Box<string[]>): string[] {
  return *b;
}
"##,
        expected: &[("EN0605", 2)],
    },
    Fix {
        id: "A:1222 a part copy of a nullable tuple local written through",
        source: r##"let v: i64[] = [1, 2];
let pair: [&i64[], i32] | null = [&v, 1];
const p2 = pair;
if (p2 != null) {
  const f = &p2[0][0];
  if (pair != null) { pair[0].push(4); }
  console.log(*f);
}
"##,
        expected: &[("EN0706", 6)],
    },
    Fix {
        id: "A:1281 a growing compound write through a class bound is one EN0706 (gv1)",
        source: r##"let d = new Dog();
const s = pick(&d);
d.name += " grows past its capacity";
console.log(s);

public class Animal {
  public label(): &string { return "animal"; }
}
public class Dog extends Animal {
  public name: string = "rex";
  public override label(): &string { return &this.name; }
}
public function pick<T extends Animal>(a: &T): &string { return a.label(); }
"##,
        expected: &[("EN0706", 3)],
    },
    Fix {
        id: "A:1281 its `&Animal` twin is one EN0706 (gv2)",
        source: r##"let d = new Dog();
const s = pick(&d);
d.name += " grows past its capacity";
console.log(s);

public class Animal {
  public label(): &string { return "animal"; }
}
public class Dog extends Animal {
  public name: string = "rex";
  public override label(): &string { return &this.name; }
}
public function pick(a: &Animal): &string { return a.label(); }
"##,
        expected: &[("EN0706", 3)],
    },
    Fix {
        id: "A:1026 a compound target meets the loan its right side left live",
        source: r##"let s = "ab".toString();
s += s.slice(0, 1);
console.log(s);
"##,
        expected: &[("EN0708", 2)],
    },
    Fix {
        id: "A:995 a third parameter written under a plain `lt` test of the first (M24)",
        source: r##"console.log(f(1, 2, 3));

function f(a: i64, b: i64, c: i64): i64 { if (a < 3) { c = 9; } return a + b + c; }
"##,
        expected: &[("EN0613", 3)],
    },
    Fix {
        id: "A:1243 a tag read through a reference meets an exclusive loan on it",
        source: r##"let h = new Holder();
f(&h);

public class Holder { public v: i64 | null = 1; }
public function f(h: &Holder): void { const w = &h.v; if (h.v != null) { } *w = null; }
"##,
        expected: &[("EN0708", 5)],
    },
    Fix {
        id: "plan d.14 a self-store aliasing two fields, then a write and a read through them",
        source: r##"let v: i64[] = [1, 2];
let w: i64[] = [3];
let h = new H(&v, &w);
h.dup();
h.go();

public class H {
  private a: &i64[];
  private b: &i64[];
  public constructor(a: &i64[], b: &i64[]) { this.a = a; this.b = b; }
  public dup(): void { this.b = this.a; }
  public go(): void { const e = &this.b[0]; this.a.push(3); console.log(*e); }
}
"##,
        expected: &[("EN0707", 5)],
    },
    Fix {
        id: "plan d.14 the same aliasing in one method body",
        source: r##"let v: i64[] = [1, 2];
let w: i64[] = [3];
let h = new H(&v, &w);
h.go();

public class H {
  private a: &i64[];
  private b: &i64[];
  public constructor(a: &i64[], b: &i64[]) { this.a = a; this.b = b; }
  public go(): void { this.b = this.a; const e = &this.b[0]; this.a.push(3); console.log(*e); }
}
"##,
        expected: &[("EN0707", 10)],
    },
    Fix {
        id: "plan d.14 a tuple behind `&` aliased by one function and used by another",
        source: r##"let v: i64[] = [1, 2];
let w: i64[] = [3];
let t: [&i64[], &i64[]] = [&v, &w];
dupt(&t);
use2(&t);

function dupt(t: &[&i64[], &i64[]]): void { t[1] = t[0]; }
function use2(t: &[&i64[], &i64[]]): void { const e = &t[1][0]; t[0].push(3); console.log(*e); }
"##,
        expected: &[("EN0707", 5)],
    },
    Fix {
        id: "plan d.14 a tuple local's parts aliased, then a write and a read",
        source: r##"let v: i64[] = [1, 2];
let w: i64[] = [3];
let t: [&i64[], &i64[]] = [&v, &w];
t[1] = t[0];
const e = &t[1][0];
t[0].push(3);
console.log(*e);
"##,
        expected: &[("EN0706", 6)],
    },
    Fix {
        id: "A:939 a subclass default with `?:` after another default",
        source: r##"const b = new B("x", true);
console.log(b.name, b.p, b.q);

public class A {
  public constructor(public name: string, public flag: bool) {}
}
public class B extends A {
  public p: i64 = 1;
  public q: i64 = make() > 0 ? 2 : 3;
}
private function make(): i64 { return 1; }
"##,
        expected: &[],
    },
    Fix {
        id: "S:981 a local function writing a captured `const`, passed as a closure (C12)",
        source: r##"const count = 0;
function inc(): void { count += 1; }
run(inc);

function run(g: () => void): void { g(); }
"##,
        expected: &[("EN0608", 2)],
    },
    Fix {
        id: "S:682 an arrow writing its parameter where the closure type reads it",
        source: r##"let v: i64 = 1;
call((x: &i64) => { *x = 2; }, &v);
console.log(v);

function call(f: (x: &i64) => void, p: &i64): void { f(p); }
"##,
        expected: &[("EN0615", 2)],
    },
    Fix {
        id: "S:682 an arrow writing its parameter where the closure type says `let`",
        source: r##"let v: i64 = 1;
call((x: &i64) => { *x = 2; }, &v);
console.log(v);

function call(f: (let x: &i64) => void, p: &i64): void { f(p); }
"##,
        expected: &[],
    },
    Fix {
        id: "S:682 an arrow kept in a local writes a parameter its type reads",
        source: r##"let v: i64 = 1;
const inc = (x: &i64) => { *x += 1; };
inc(&v);
console.log(v);
"##,
        expected: &[("EN0615", 2)],
    },
    Fix {
        id: "S:968 an arrow kept in a local that reads its parameter",
        source: r##"const xs: i64[] = [1, 2, 3];
const double = (x: &i64) => x * 2;
console.log(xs.map(double));
"##,
        expected: &[],
    },
    Fix {
        id: "S:682 an arrow as an `fn` value writing its parameter",
        source: r##"let v: i64 = 1;
const g: fn(x: &i64) => void = (x: &i64) => { *x = 2; };
g(&v);
console.log(v);
"##,
        expected: &[("EN0615", 2)],
    },
    Fix {
        id: "T:582 a writing function at `(x: &i64) => void` and as an `fn(x: &i64) => void` local",
        source: r##"let v: i64 = 1;
call(bump, &v);
const g: fn(x: &i64) => void = bump;
console.log(v);

function call(f: (x: &i64) => void, p: &i64): void { f(p); }
function bump(x: &i64): void { *x = 2; }
"##,
        expected: &[("EN0615", 2), ("EN0615", 3)],
    },
    Fix {
        id: "T:582 the same at `(let x: &i64) => void` and `fn(let x: &i64) => void`",
        source: r##"let v: i64 = 1;
call(bump, &v);
const g: fn(let x: &i64) => void = bump;
g(&v);
console.log(v);

function call(f: (let x: &i64) => void, p: &i64): void { f(p); }
function bump(x: &i64): void { *x = 2; }
"##,
        expected: &[],
    },
    Fix {
        id: "D20-core-5 an arrow argument storing `s` into `l`",
        source: r##"let src = "ab".toString();
let lx = new Lexer(&src);
{
  const tmp = "xy" + "z";
  apply((l: &Lexer, s: &string) => { l.setSrc(s); }, &lx, &tmp);
}
console.log(lx.next());

function apply(f: (let l: &Lexer, s: &string) => void, l: &Lexer, s: &string): void { f(l, s); }
private class Lexer {
  private src: &string;
  public constructor(src: &string) { this.src = src; }
  public setSrc(s: &string): void { this.src = s; }
  public next(): &string { return this.src; }
}
"##,
        expected: &[("EN0615", 5)],
    },
    Fix {
        id: "D20-core-5 local an arrow in a local storing `s` into `l`",
        source: r##"let src = "ab".toString();
let lx = new Lexer(&src);
const put = (l: &Lexer, s: &string) => { l.setSrc(s); };
{
  const tmp = "xy" + "z";
  put(&lx, &tmp);
}
console.log(lx.next());

private class Lexer {
  private src: &string;
  public constructor(src: &string) { this.src = src; }
  public setSrc(s: &string): void { this.src = s; }
  public next(): &string { return this.src; }
}
"##,
        expected: &[("EN0615", 3)],
    },
    Fix {
        id: "S:682 an arrow argument that only stores, into a class that never writes through its fields",
        source: r##"let src = "ab".toString();
let h = new Holder(&src);
{
  const tmp = "xy" + "z";
  apply((let k: &Holder, s: &string) => { k.setSrc(s); }, &h, &tmp);
}
h.show();

function apply(f: (let k: &Holder, s: &string) => void, k: &Holder, s: &string): void { f(k, s); }
private class Holder {
  private src: &string;
  public constructor(src: &string) { this.src = src; }
  public setSrc(s: &string): void { this.src = s; }
  public show(): void { console.log(this.src); }
}
"##,
        expected: &[("EN0615", 5)],
    },
];

fn pairs(list: &[(&str, u32)]) -> Vec<(String, u32)> {
    list.iter().map(|(c, l)| (c.to_string(), *l)).collect()
}

/// Every body of `source` checked and elaborated (plan d.12), printed.
fn elaborated(source: &str) -> String {
    let built = crate::support::build(source);
    let mut dcx = enrang_diag::DiagCtx::new();
    enrang_borrowck::infer_contracts(&built.tcx, &built.bodies, &mut dcx);
    let mut list = Vec::new();
    for b in built.bodies.values() {
        let facts = enrang_borrowck::check(&built.tcx, &built.bodies, b, &mut dcx);
        list.push(enrang_borrowck::elaborate_drops(
            &built.tcx,
            b.clone(),
            &facts,
        ));
    }
    enrang_mir::print_module(&built.tcx, &list)
}

/// The programs phase 3 must accept, by case name: hosts of `mutants`' violations
/// (TESTING 14).
pub fn accepted() -> Vec<(String, String)> {
    (FIXES.iter())
        .filter(|fix| fix.expected.is_empty())
        .map(|fix| (format!("fixes/{}", fix.id), fix.source.to_owned()))
        .collect()
}

pub fn register(h: &mut Harness) {
    for fix in FIXES {
        h.case(format!("fixes/{}", fix.id), move || {
            assert_eq!(crate::support::phase3(fix.source), pairs(fix.expected));
        });
    }
    h.case(
        "fixes/A:970 a literal view becomes a static only when nothing writes through it",
        || {
            let kept = elaborated(
                "const p: &Slice<i64> = &[1, 2];\nrun(() => { p[0] = 9; });\nconsole.log(p);\n\n\
                 function run(f: () => void): void { f(); }\n",
            );
            assert!(!kept.contains("static_addr(literal"), "{kept}");
            let made = elaborated(
                "console.log(zeros());\n\nfunction zeros(): &Slice<i64> { return &[0, 0]; }\n",
            );
            assert!(made.contains("static_addr(literal#0)"), "{made}");
        },
    );
    h.case(
        "fixes/A:1354 a `through_read` result names the field it is reached from",
        || {
            let built = crate::support::build(
                "let t: i64[][] = [[1], [2]];\nconst f = new Finder(&t, &t);\nconsole.log(f.find(2));\n\n\
                 public final class Finder {\n  private aa: readonly &Slice<i64[]>;\n  \
                 private rows: readonly &Slice<i64[]>;\n  \
                 public constructor(a: &Slice<i64[]>, r: &Slice<i64[]>) { this.aa = a; this.rows = r; }\n  \
                 public find(first: i64): &i64[] | null { for (const r of this.rows) { if (r[0] == first) { return r; } } return null; }\n}\n",
            );
            let mut dcx = enrang_diag::DiagCtx::new();
            enrang_borrowck::infer_contracts(&built.tcx, &built.bodies, &mut dcx);
            let (find, _) = (built.tcx.defs())
                .find(|(_, d)| d.path.to_string().ends_with("Finder::find"))
                .expect("`find`");
            let result = enrang_borrowck::contract(&built.tcx, find).result.clone();
            assert!(
                matches!(
                    result,
                    enrang_hir::ResultPerm::ReadOnly(enrang_hir::Reason::ReadonlyField(
                        _,
                        enrang_hir::FieldIdx(1)
                    ))
                ),
                "{result:?}"
            );
        },
    );
    h.case(
        "fixes/A:1354 a `through_read` result in an SCC keeps the field as its reason (M11)",
        || {
            let built = crate::support::build(
                "let t: i64[][] = [[1, 2]];\nconst f = new Finder(&t);\nconsole.log(f.find(1));\n\n\
                 public final class Finder {\n  private rows: readonly &Slice<i64[]>;\n  \
                 public constructor(rows: &Slice<i64[]>) { this.rows = rows; }\n  \
                 public find(n: i64): &i64[] { return this.helper(n); }\n  \
                 public helper(n: i64): &i64[] { if (n == 0) { return &this.rows[0]; } return this.find(n - 1); }\n}\n",
            );
            let mut dcx = enrang_diag::DiagCtx::new();
            enrang_borrowck::infer_contracts(&built.tcx, &built.bodies, &mut dcx);
            for name in ["Finder::find", "Finder::helper"] {
                let (def, _) = (built.tcx.defs())
                    .find(|(_, d)| d.path.to_string().ends_with(name))
                    .expect("the method");
                let result = enrang_borrowck::contract(&built.tcx, def).result.clone();
                assert!(
                    matches!(
                        result,
                        enrang_hir::ResultPerm::ReadOnly(enrang_hir::Reason::ReadonlyField(
                            _,
                            enrang_hir::FieldIdx(0)
                        ))
                    ),
                    "{name}: {result:?}"
                );
            }
        },
    );
}
