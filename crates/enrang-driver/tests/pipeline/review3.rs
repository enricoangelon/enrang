//! The third review's phase-3 programs (M3 stage 3 fixes): each finding of the
//! review that phase 3 now answers as its doc row, rule or `rustc` twin says,
//! pinned as (code, line) in report order, and the programs that kill the
//! review's surviving mutants. A program with no expected report is one that
//! failed the verifier (an internal error, exit 3) before its fix.

use enrang_testkit::Harness;

/// One program, the finding or row it answers, and what phase 3 reports.
struct Fix {
    id: &'static str,
    source: &'static str,
    expected: &'static [(&'static str, u32)],
}

const FIXES: &[Fix] = &[
    Fix {
        id: "call.rs:177 `unbox` on a narrowed `Box<C> | null` (ice1)",
        source: r##"let b: Box<Animal> | null = new Box(new Animal("rex"));
if (b != null) { const a = b.unbox(); console.log(a.name); }

private class Animal {
  public constructor(public name: string) {}
}
"##,
        expected: &[],
    },
    Fix {
        id: "call.rs:177 `clone` on a narrowed `&T | null` in generic code",
        source: r##"const x = new Animal("rex");
console.log(f(&x));

private function f<T extends Clone>(r: &T | null): bool { if (r != null) { const c = r.clone(); return true; } return false; }
private class Animal implements Clone {
  public constructor(public name: string) {}
  public clone(): Animal { return new Animal(this.name.clone()); }
}
"##,
        expected: &[],
    },
    Fix {
        id: "call.rs:177 `clone` on a narrowed `&C | null`, and `r?.clone()`",
        source: r##"const a = new Animal("rex");
const r: &Animal | null = &a;
if (r != null) { const c = r.clone(); console.log(c.name); }
const copy = r?.clone();
console.log(copy == null);

private class Animal implements Clone {
  public constructor(public name: string) {}
  public clone(): Animal { return new Animal(this.name.clone()); }
}
"##,
        expected: &[],
    },
    Fix {
        id: "call.rs:177 `unbox` on an enum case payload `Box`",
        source: r##"const s = Shelter.Pet { b: new Box(new Animal("rex")) };
match (s) {
  Shelter.Pet => { const a = s.b.unbox(); console.log(a.name); },
  Shelter.Empty => {},
}

private enum Shelter { Pet { b: Box<Animal> }, Empty }
private class Animal {
  public constructor(public name: string) {}
}
"##,
        expected: &[],
    },
    Fix {
        id: "call.rs:177 an inherited `clone` and methods through `?.` on a narrowed subclass",
        source: r##"const d = new Dog("rex");
const r: &Dog | null = &d;
if (r != null) { const c = r.clone(); console.log(c.name); }
console.log(r?.speak());
const b: Box<Dog> | null = new Box(new Dog("fido"));
console.log(b?.speak());

private class Animal implements Clone {
  public constructor(public name: string) {}
  public clone(): Animal { return new Animal(this.name.clone()); }
  public speak(): string { return this.name.clone(); }
}
private class Dog extends Animal {
  public constructor(name: string) { super(name); }
}
"##,
        expected: &[],
    },
    Fix {
        id: "matches.rs:624 `Slice` methods through `?.` on nullable arrays (ice2)",
        source: r##"const xs: i64[] | null = [1, 2];
const f = xs?.first();
console.log(f == null ? 0 : *f);
let ys: string[] | null = ["a".toString()];
const g = ys?.first();
console.log(g);
console.log(xs?.includes(&2));
const fixed: i64[3] | null = [1, 2, 3];
console.log(fixed?.first());
"##,
        expected: &[],
    },
    Fix {
        id: "matches.rs:624 `this.pets?.first()` in a method",
        source: r##"const k = new Kennel();
console.log(k.firstPet());

private class Kennel {
  public pets: string[] | null = ["rex".toString()];
  public firstPet(): string { const p = this.pets?.first(); return p == null ? "" : p.clone(); }
}
"##,
        expected: &[],
    },
    Fix {
        id: "matches.rs:663 `r!` on a `&(i64 | null)` (ice3)",
        source: r##"let h: i64 | null = 1;
const cur = &h;
console.log(cur! + 1);
"##,
        expected: &[],
    },
    Fix {
        id: "matches.rs:663 `r!` on a `&(Node | null)`, read and written through",
        source: r##"let h: Node | null = new Node(1, null);
const cur = &h;
console.log(cur!.v);
let w = &h;
w!.v = 5;
console.log(h);

private class Node {
  public constructor(public v: i64, public next: Box<Node> | null) {}
}
"##,
        expected: &[],
    },
    Fix {
        id: "matches.rs:663 a linked-list walk through `cur!`",
        source: r##"let l = new List();
l.push(1);
l.push(2);
console.log(l.total());

private class List {
  public head: Box<Node> | null = null;
  public push(v: i64): void { const old = mem.replace(&this.head, null); this.head = new Box(new Node(v, old)); }
  public total(): i64 {
    let total = 0;
    let cur = &this.head;
    while (*cur != null) { total += cur!.v; cur = &cur!.next; }
    return total;
  }
}
private class Node {
  public constructor(public v: i64, public next: Box<Node> | null) {}
}
"##,
        expected: &[],
    },
    Fix {
        id: "fit.rs:216 a writer's fn value converted to a reader's row at the top",
        source: r##"function bump(x: &i64[]): void { x.push(1); x.push(2); x.push(3); x.push(4); }
const w: fn(let x: &i64[]) => void = bump;
const r: fn(x: &i64[]) => void = w;
let data: i64[] = [1, 2, 3];
const e = &data[0];
r(&data);
console.log(*e);
"##,
        expected: &[("EN0615", 3)],
    },
    Fix {
        id: "fit.rs:216 the same conversion with equal rows is the use's EN0706",
        source: r##"function bump(x: &i64[]): void { x.push(1); x.push(2); x.push(3); x.push(4); }
const w: fn(let x: &i64[]) => void = bump;
const r: fn(let x: &i64[]) => void = w;
let data: i64[] = [1, 2, 3];
const e = &data[0];
r(&data);
console.log(*e);
"##,
        expected: &[("EN0706", 6)],
    },
    Fix {
        id: "fit.rs:216 T:583 a writer's row under `| null` stripped",
        source: r##"// exploit: nullable wrapper strips the let row
function bump(x: &i64[]): void { x.push(1); x.push(2); x.push(3); x.push(4); }
const w: (fn(let x: &i64[]) => void) | null = bump;
const r: (fn(x: &i64[]) => void) | null = w;
let data: i64[] = [1, 2, 3];
const e = &data[0];
if (r != null) { r(&data); }
console.log(*e);
"##,
        expected: &[("EN0615", 4)],
    },
    Fix {
        id: "fit.rs:216 T:583 a writer's row under `T[]` stripped",
        source: r##"// exploit (reverse direction): a writer array moved into a reader array; the call through the reader type takes a shared loan
function bump(x: &i64[]): void { x.push(1); x.push(2); x.push(3); x.push(4); }
const writers: (fn(let x: &i64[]) => void)[] = [bump];
const readers: (fn(x: &i64[]) => void)[] = writers;
let data: i64[] = [1, 2, 3];
const e = &data[0];
const f = readers[0];
f(&data);
console.log(*e);
"##,
        expected: &[("EN0615", 4)],
    },
    Fix {
        id: "fit.rs:216 T:583 a reader slot passed where `&(fn(let ..))` stores a writer",
        source: r##"// exploit: a writer stored through &fn(let x) into a fn(x) slot; the call through the reader type takes a shared loan
function rd(x: &i64[]): void { console.log(x.length()); }
function bump(x: &i64[]): void { x.push(1); x.push(2); x.push(3); x.push(4); }
function setW(b: &(fn(let x: &i64[]) => void)): void { *b = bump; }
let a: fn(x: &i64[]) => void = rd;
setW(&a);
let data: i64[] = [1, 2, 3];
const e = &data[0];
a(&data);
console.log(*e);
"##,
        expected: &[("EN0615", 6)],
    },
    Fix {
        id: "fit.rs:216 T:583 a reader array passed where a writer array is pushed to",
        source: r##"// exploit through an array of fn values
function rd(x: &i64[]): void { console.log(x.length()); }
function bump(x: &i64[]): void { x.push(1); x.push(2); x.push(3); x.push(4); }
function addW(ws: &(fn(let x: &i64[]) => void)[]): void { ws.push(bump); }
let readers: (fn(x: &i64[]) => void)[] = [rd];
addW(&readers);
let data: i64[] = [1, 2, 3];
const e = &data[0];
const f = readers[1];
f(&data);
console.log(*e);
"##,
        expected: &[("EN0615", 6)],
    },
    Fix {
        id: "fit.rs:216 T:583 a nullable reader slot passed by reference",
        source: r##"// exploit through nullable
function rd(x: &i64[]): void { console.log(x.length()); }
function bump(x: &i64[]): void { x.push(1); x.push(2); x.push(3); x.push(4); }
function setW(b: &((fn(let x: &i64[]) => void) | null)): void { *b = bump; }
let a: (fn(x: &i64[]) => void) | null = rd;
setW(&a);
let data: i64[] = [1, 2, 3];
const e = &data[0];
if (a != null) { a(&data); }
console.log(*e);
"##,
        expected: &[("EN0615", 6)],
    },
    Fix {
        id: "fit.rs:216 T:583 another fn type's parameter: a function name",
        source: r##"// exploit: fn value whose parameter is itself an fn type, coerced with a narrower nested row
function bump(x: &i64[]): void { x.push(1); x.push(2); x.push(3); x.push(4); }
function runReader(f: fn(x: &i64[]) => void): void { let v: i64[] = [1, 2, 3]; const e = &v[0]; f(&v); console.log(*e); }
const g: fn(f: fn(let x: &i64[]) => void) => void = runReader;
g(bump);
"##,
        expected: &[("EN0615", 4)],
    },
    Fix {
        id: "fit.rs:216 T:583 an implementation's parameter row narrower than the member's",
        source: r##"// exploit: implementation narrows a nested fn row of an interface member
function bump(x: &i64[]): void { x.push(1); x.push(2); x.push(3); x.push(4); }
function go(r: &Runner): void { r.run(bump); }
let s = new Impl(); go(&s);
public interface Runner { run(f: fn(let x: &i64[]) => void): void; }
public class Impl implements Runner { public run(f: fn(x: &i64[]) => void): void { let v: i64[] = [1, 2, 3]; const e = &v[0]; f(&v); console.log(*e); } }
"##,
        expected: &[("EN0615", 6)],
    },
    Fix {
        id: "fit.rs:216 T:583 an override's parameter row narrower than the base's",
        source: r##"// exploit: override narrows a nested fn row (param of a param); callers through Base pass a writer
function bump(x: &i64[]): void { x.push(1); x.push(2); x.push(3); x.push(4); }
let s = new Sub(); const b: &Base = &s; b.apply(bump);
public class Base { public apply(f: fn(let x: &i64[]) => void): void { let v: i64[] = [1]; f(&v); } }
public class Sub extends Base { public override apply(f: fn(x: &i64[]) => void): void { let v: i64[] = [1, 2, 3]; const e = &v[0]; f(&v); console.log(*e); } }
"##,
        expected: &[("EN0615", 5)],
    },
    Fix {
        id: "fit.rs:216 T:583 WD-6 a reader array into a writer array",
        source: r##"const readers: (fn(x: &i64) => void)[] = [rd];
const writers: (fn(let x: &i64) => void)[] = readers;
console.log(writers.length());

private function rd(x: &i64): void { console.log(*x); }
"##,
        expected: &[("EN0615", 2)],
    },
    Fix {
        id: "fit.rs:216 S2-13-value a value converted with a changed `&string` form",
        source: r##"let msg: string = "hi".toString();
run(choose(false), &msg);
run(show, &msg);

private function run(f: fn(let s: &string) => void, s: &string): void { f(s); }
private function show(s: &string): void { console.log(s); }
private function quote(s: &string): void { console.log(`"${s}"`); }
private function choose(loud: bool): fn(s: &string) => void { return loud ? quote : show; }
"##,
        expected: &[("EN0615", 2)],
    },
    Fix {
        id: "fit.rs:216 T:583 a reading function or value at the top of a writer's site compiles",
        source: r##"const r: fn(x: &i64[]) => void = rd;
const w: fn(let x: &i64[]) => void = r;
let data: i64[] = [1];
w(&data);
call(rd, &data);
call(r, &data);
console.log(data);

private function rd(x: &i64[]): void { console.log(x.length()); }
private function call(f: (let x: &i64[]) => void, d: &i64[]): void { f(d); }
"##,
        expected: &[],
    },
    Fix {
        id: "report.rs:2186 EN0608 names the parameter the argument is passed to",
        source: r##"let a: i64[] = [1];
const b: i64[] = [2];
both(&a, &b);

private function both(x: &i64[], y: &i64[]): void { x.push(1); y.push(2); }
"##,
        expected: &[("EN0608", 3)],
    },
    Fix {
        id: "report.rs:2186 EN0608 at a constructor's argument",
        source: r##"const xs: i64[] = [1, 2];
const w = new Wrap(&xs);

private class Wrap {
  private r: &i64[];
  public constructor(r: &i64[]) { this.r = r; this.r.push(3); }
}
"##,
        expected: &[("EN0608", 2)],
    },
    Fix {
        id: "report.rs:2186 EN0608 at a method's argument beside a written `this`",
        source: r##"let counter = new Counter();
const items: i64[] = [1, 2];
counter.absorb(&items);

private class Counter {
  public n: i64 = 0;
  public absorb(xs: &i64[]): void { this.n += 1; xs.push(this.n); }
}
"##,
        expected: &[("EN0608", 3)],
    },
    Fix {
        id: "marks.rs:621 each marked argument of one call is reported",
        source: r##"function both(let a: &i64[], let b: &i64[]): void { console.log(a.length(), b.length()); }
const x: i64[] = [1];
const y: i64[] = [2];
both(&x, &y);
"##,
        expected: &[("EN0608", 4), ("EN0608", 4)],
    },
    Fix {
        id: "marks.rs:722 D20-core-4 a call's store is covered by its Write parameter alone (A:1359)",
        source: r##"function id(t: &Lexer): &Lexer { return t; }
let base = "abc".toString(); let lx = new Lexer(&base);
{ const tmp = "xy" + "z"; const r = id(&lx); r.setSrc(&tmp); } console.log(lx.next());
let w = new Wrapper(&lx);
{ const tmp = "xy" + "z"; w.retarget(&tmp); } console.log(lx.next());
public class Lexer { private src: &string; private pos: isize = 0; public constructor(src: &string) { this.src = src; } public next(): &string | null { if (this.pos >= this.src.length()) { return null; } const start = this.pos; this.pos = this.src.length(); return this.src.slice(start, this.pos); } public setSrc(s: &string): void { this.src = s; } }
public class Wrapper { private lx: &Lexer; public constructor(lx: &Lexer) { this.lx = lx; } public retarget(s: &string): void { this.lx.setSrc(s); } }
"##,
        expected: &[("EN0711", 3), ("EN0711", 5)],
    },
    Fix {
        id: "access.rs:692 T:664 an arrow's capture meeting a loop's hold is the hold's EN0706",
        source: r##"function run(f: () => void): void { f(); }
let q: i64[] = [1]; for (const x of &q) { run(() => { q.push(1); }); }
"##,
        expected: &[("EN0706", 2)],
    },
    Fix {
        id: "report.rs:727 an exclusive borrow of a held source is a change, not a reassignment",
        source: r##"let q: i64[] = [1];
for (const x of &q) { const r = &q; r.push(1); }
"##,
        expected: &[("EN0706", 2)],
    },
    Fix {
        id: "report.rs:727 a local function's hidden argument changing a held source",
        source: r##"let q: i64[] = [1, 2];
function grow(): void { q.push(7); }
for (const x of &q) { grow(); }
"##,
        expected: &[("EN0706", 3)],
    },
    Fix {
        id: "report.rs:959 TK-02-reassign-break as amended (T:732, A:1026)",
        source: r##"let q: i64[] = [1, 5, 3, 7]; let o: i64[] = [0]; let r = &q; let keep: &i64 | null = null; for (const x of r) { if (*x > 2) { keep = x; r = &o; break; } } if (keep != null) { *keep = 0; } console.log(r); console.log(q);
"##,
        expected: &[],
    },
    Fix {
        id: "report.rs:959 TK-02-reassign-break second form as amended",
        source: r##"let q: i64[] = [1, 5, 3, 7]; let o: i64[] = [0]; let r = &q; for (const x of r) { if (*x > 2) { *x = 0; r = &o; break; } } console.log(r); console.log(q);
"##,
        expected: &[],
    },
    Fix {
        id: "report.rs:959 the unsplit read meets the exclusive loan on the path that runs the loop out (A:1026)",
        source: r##"let q: i64[] = [1, 5, 3, 7]; let o: i64[] = [0]; let r = &q; let keep: &i64 | null = null; for (const x of r) { if (*x > 2) { keep = x; r = &o; break; } } if (keep != null) { *keep = 0; } console.log(r, q);
"##,
        expected: &[("EN0708", 1)],
    },
    Fix {
        id: "report.rs:959 T:729 a repointed reference slot under its hold's crossing loan",
        source: r##"let a: i64[] = [1]; let b2: i64[] = [2]; let r = &a; for (const x of r) { r = &b2; }
"##,
        expected: &[("EN0706", 1)],
    },
    Fix {
        id: "fit.rs:258 S:981 a local function passed as a closure that stores through a hidden argument",
        source: r##"function run(f: () => void): void { f(); }
let s = "ab".toString(); let lx = new Lexer(&s); let t = "xy".toString();
function bind(): void { lx.setSrc(&t); }
run(bind);
public class Lexer { private src: &string; public constructor(src: &string) { this.src = src; } public setSrc(s: &string): void { this.src = s; } }
"##,
        expected: &[("EN0616", 4)],
    },
    Fix {
        id: "access.rs:674 T:1109 Q41-written a returned literal is EN0710 alone",
        source: r##"let k = 0;
private function pair(n: i64): &Slice<i64> { return &[n, n]; }
"##,
        expected: &[("EN0710", 2)],
    },
    Fix {
        id: "access.rs:674 a returned slice of a temporary string is EN0710 alone",
        source: r##"public function f(): &string { return ("a" + "b").slice(0, 1); }
"##,
        expected: &[("EN0710", 1)],
    },
    Fix {
        id: "report.rs:2208 T:856 INF-04-upcast one EN0708 in mix, none at the call",
        source: r##"const k: u8[] = [1]; let out: u8[] = [0]; let s = new Sub(&k, &out); s.mix();
public class Base { private src: readonly &Slice<u8>; public constructor(s: &Slice<u8>) { this.src = s; } public retarget(v: &Slice<u8>): void { this.src = v; } }
public final class Sub extends Base { private dst: &Slice<u8>; public constructor(s: &Slice<u8>, d: &Slice<u8>) { this.dst = d; super(s); } public step(): void { this.dst[0] = 1; } public mix(): void { const b: &Base = this; b.retarget(this.dst.slice(0, 1)); } }
"##,
        expected: &[("EN0708", 3)],
    },
    Fix {
        id: "report.rs:2208 T:856 INF-04-upcast second form, one EN0706",
        source: r##"const k: u8[] = [1]; let out: u8[] = [0]; let s = new Sub(&k, &out); s.mix();
public class Base { private src: readonly &Slice<u8>; public constructor(s: &Slice<u8>) { this.src = s; } public retarget(v: &Slice<u8>): void { this.src = v; } }
public final class Sub extends Base { private dst: &Slice<u8>; public constructor(s: &Slice<u8>, d: &Slice<u8>) { this.dst = d; super(s); } public step(): void { this.dst[0] = 1; } public mix(): void { const p = this.dst.slice(0, 1); const b: &Base = this; b.retarget(p); } }
"##,
        expected: &[("EN0706", 3)],
    },
    Fix {
        id: "report.rs:2208 T:995 FV-02-copier store in the body, none at the call",
        source: r##"const table: u8[3] = [7, 8, 9]; let out: u8[3] = [0, 0, 0]; let c = new Copier(&table, &out); c.fuse();
public final class Copier { private src: readonly &Slice<u8>; private dst: &Slice<u8>; private pos: isize = 0; public constructor(s: &Slice<u8>, d: &Slice<u8>) { this.src = s; this.dst = d; } public step(): void { this.dst[this.pos] = this.src[this.pos]; this.pos += 1; } public peek(): readonly &Slice<u8> { return this.src.slice(this.pos, this.pos + 1); } public fuse(): void { this.src = this.dst.slice(0, 1); } }
"##,
        expected: &[("EN0616", 2)],
    },
    Fix {
        id: "report.rs:2208 T:995 FV-02-copier fuse through setSrc, exactly one EN0706",
        source: r##"const table: u8[3] = [7, 8, 9]; let out: u8[3] = [0, 0, 0]; let c = new Copier(&table, &out); c.fuse();
public final class Copier { private src: readonly &Slice<u8>; private dst: &Slice<u8>; private pos: isize = 0; public constructor(s: &Slice<u8>, d: &Slice<u8>) { this.src = s; this.dst = d; } public step(): void { this.dst[this.pos] = this.src[this.pos]; this.pos += 1; } public peek(): readonly &Slice<u8> { return this.src.slice(this.pos, this.pos + 1); } public fuse(): void { this.setSrc(this.dst.slice(0, 1)); } public setSrc(s: &Slice<u8>): void { this.src = s; } }
"##,
        expected: &[("EN0706", 2)],
    },
    Fix {
        id: "access.rs:673 T:1012 FV-02-alias-nested: EN0616 at the store and EN0709 at `return t`",
        source: r##"let buf: u8[] = [1];
const tbl: u8[] = [0];
let r = Copier.nested(&tbl, &buf);
const a = r[0].peek(); r[0].step(); r[0].step(); r[0].step(); r[0].step(); console.log(*a);
public final class Copier { private src: readonly &u8[]; private dst: &u8[]; public constructor(s: &u8[], d: &u8[]) { this.src = s; this.dst = d; } public static make(s: &u8[], d: &u8[]): Copier { return new Copier(s, d); } public peek(): readonly &u8 { return &this.src[0]; } public step(): void { this.dst.push(1); }
  public static nested(s: &u8[], d: &u8[]): [Copier, i32] { let t: [Copier, i32] = [Copier.make(s, d), 0]; const p = t[0].dst; t[0].src = p; return t; } }
"##,
        expected: &[("EN0616", 6), ("EN0709", 6)],
    },
    Fix {
        id: "call.rs:177 an array element's `clone` needs no class check",
        source: r##"let xs: Item[] = [new Item(1)];
const first = xs[0].clone();
xs.push(new Item(2));
console.log(first);

public class Item { public constructor(public v: i64) {} }
"##,
        expected: &[],
    },
    Fix {
        id: "fit.rs:216 S:682 an arrow at an `fn` type with a narrower nested row",
        source: r##"function bump(x: &i64[]): void { x.push(1); x.push(2); x.push(3); x.push(4); }
const g: fn(f: fn(let x: &i64[]) => void) => void = (f: fn(x: &i64[]) => void) => { let v: i64[] = [1, 2, 3]; const e = &v[0]; f(&v); console.log(*e); };
g(bump);
"##,
        expected: &[("EN0615", 2)],
    },
    Fix {
        id: "fit.rs:216 S:682 an arrow at a closure parameter with a narrower nested row",
        source: r##"function bump(x: &i64[]): void { x.push(1); x.push(2); x.push(3); x.push(4); }
function run(g: (f: fn(let x: &i64[]) => void) => void): void { g(bump); }
run((f: fn(x: &i64[]) => void) => { let v: i64[] = [1, 2, 3]; const e = &v[0]; f(&v); console.log(*e); });
"##,
        expected: &[("EN0615", 3)],
    },
    Fix {
        id: "fit.rs:216 T:583 a borrow into a typed reference to a writer's row",
        source: r##"function rd(x: &i64[]): void { console.log(x.length()); }
function bump(x: &i64[]): void { x.push(1); x.push(2); x.push(3); x.push(4); }
let a: fn(x: &i64[]) => void = rd;
const p: &(fn(let x: &i64[]) => void) = &a;
*p = bump;
let data: i64[] = [1, 2, 3];
const e = &data[0];
a(&data);
console.log(*e);
"##,
        expected: &[("EN0615", 4)],
    },
    Fix {
        id: "fit.rs:216 T:583 a view of a reader array as a writer slice (exit 3 before)",
        source: r##"function rd(x: &i64[]): void { console.log(x.length()); }
function bump(x: &i64[]): void { x.push(1); x.push(2); x.push(3); x.push(4); }
let readers: (fn(x: &i64[]) => void)[] = [rd];
const s: &Slice<fn(let x: &i64[]) => void> = &readers;
s[0] = bump;
let data: i64[] = [1, 2, 3];
const e = &data[0];
const f = readers[0];
f(&data);
console.log(*e);
"##,
        expected: &[("EN0615", 4)],
    },
    Fix {
        id: "fit.rs:216 a call's writer result into a reader's row",
        source: r##"function bump(x: &i64[]): void { x.push(1); x.push(2); x.push(3); x.push(4); }
function getWriter(): fn(let x: &i64[]) => void { return bump; }
const r: fn(x: &i64[]) => void = getWriter();
let data: i64[] = [1, 2, 3];
const e = &data[0];
r(&data);
console.log(*e);
"##,
        expected: &[("EN0615", 3)],
    },
    Fix {
        id: "call.rs:177 `clone` of a narrowed `Box<C> | null` (exit 3 before)",
        source: r##"let b: Box<Animal> | null = new Box(new Animal("rex"));
if (b != null) { const c = b.clone(); console.log(c.name); }
private class Animal implements Clone {
  public constructor(public name: string) {}
  public clone(): Animal { return new Animal(this.name.clone()); }
}
"##,
        expected: &[],
    },
    Fix {
        id: "matches.rs:624 `b?.clone()` of a `Box<C> | null` takes the box (exit 3 before)",
        source: r##"let b: Box<Animal> | null = new Box(new Animal("rex"));
const d = b?.clone();
console.log(d == null);
private class Animal implements Clone {
  public constructor(public name: string) {}
  public clone(): Animal { return new Animal(this.name.clone()); }
}
"##,
        expected: &[],
    },
    Fix {
        id: "call.rs:177 `clone` of a `Box<C>` element (exit 3 before)",
        source: r##"let boxes: Box<Animal>[] = [new Box(new Animal("fido"))];
const e = boxes[0].clone();
console.log(e.name);
private class Animal implements Clone {
  public constructor(public name: string) {}
  public clone(): Animal { return new Animal(this.name.clone()); }
}
"##,
        expected: &[],
    },
];

/// A box's `clone` in each place its object is reached from.
const BOX_CLONES: &str = r##"let b: Box<Animal> | null = new Box(new Animal("rex"));
if (b != null) { const c = b.clone(); console.log(c.name); }
const d = b?.clone();
console.log(d == null);
let boxes: Box<Animal>[] = [new Box(new Animal("fido"))];
const e = boxes[0].clone();
console.log(e.name);
const plain: Box<Animal> = new Box(new Animal("plain"));
const f = plain.clone();
console.log(f.name);

private class Animal implements Clone {
  public constructor(public name: string) {}
  public clone(): Animal { return new Animal(this.name.clone()); }
}
"##;

fn pairs(list: &[(&str, u32)]) -> Vec<(String, u32)> {
    list.iter().map(|(c, l)| (c.to_string(), *l)).collect()
}

/// The programs phase 3 must accept, by case name: hosts of `mutants`' violations
/// (TESTING 14).
pub fn accepted() -> Vec<(String, String)> {
    (FIXES.iter())
        .filter(|fix| fix.expected.is_empty())
        .map(|fix| (format!("review3/{}", fix.id), fix.source.to_owned()))
        .collect()
}

pub fn register(h: &mut Harness) {
    for fix in FIXES {
        h.case(format!("review3/{}", fix.id), move || {
            assert_eq!(crate::support::phase3(fix.source), pairs(fix.expected));
        });
    }
    // A:943: the object of a box's `clone` is `*b`, checked through a `box`
    // holder whether the box is a local, a narrowed payload, a `?.` base or an
    // element (the last three named through the receiver, `**a`).
    h.case(
        "review3/call.rs:177 each box's `clone` checks the object it holds",
        || {
            let text = crate::support::build(BOX_CLONES).text();
            assert_eq!(text.matches(", clone, box);").count(), 4, "{text}");
            assert_eq!(text.matches("check_class(**_").count(), 3, "{text}");
        },
    );
    // check.rs:117: phase 3 verifies every body it builds, and a failure is an
    // internal error that names the body and the rule (plan g.3, exit status 3).
    h.case(
        "review3/check.rs:117 a body that fails the verifier is an internal error",
        || {
            let mut built = crate::support::build(
                "const xs: i64[] = [1, 2];\nconst i: isize = 1;\nconsole.log(xs[i]);\n",
            );
            let order: Vec<enrang_mir::BodyOwner> = built.bodies.keys().copied().collect();
            assert_eq!(
                enrang_driver::verify_built(&built.tcx, &built.bodies, &order),
                Ok(())
            );
            let owner = order[0];
            let body = built.bodies.get_mut(&owner).expect("the statements");
            for blk in body.blocks.iter_mut() {
                blk.stmts
                    .retain(|s| !matches!(s.kind, enrang_mir::StatementKind::CheckBounds { .. }));
            }
            let err = enrang_driver::verify_built(&built.tcx, &built.bodies, &order)
                .expect_err("a missing bounds check");
            assert!(
                err.0
                    .starts_with("the MIR of `main statements` fails the verifier: GuardBounds"),
                "{}",
                err.0
            );
        },
    );
}
