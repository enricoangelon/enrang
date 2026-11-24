//! Realistic programs through all of phase 3 (merge-2): SPEC 5's examples and
//! `TESTING.md` rows, built by mirbuild, then `borrowck::infer_contracts`,
//! `check` and `check_module` (plan g.3). Each row pins what phase 3 reports,
//! as (code, line), beside what the doc row expects; a row that differs says so in
//! its name, so a fix that makes it match fails here until the row is updated.

use enrang_testkit::Harness;

/// One program: its doc row, its source, what the row expects and what phase 3
/// reports today.
struct Row {
    id: &'static str,
    source: &'static str,
    expected: &'static [(&'static str, u32)],
    actual: &'static [(&'static str, u32)],
}

const ROWS: &[Row] = &[
    Row {
        id: "S:1022 a loop holds its source",
        source: "let queue = [\"a\", \"b\"];\nfor (const job of &queue) { queue.push(\"retry\"); }\n",
        expected: &[("EN0706", 2)],
        actual: &[("EN0706", 2)],
    },
    Row {
        id: "S:1021 a loop over a copy",
        source: "let queue = [\"a\", \"b\"];\nfor (const job of [...queue]) { queue.push(\"retry\"); }\nconsole.log(queue);\n",
        expected: &[],
        actual: &[],
    },
    Row {
        id: "S:1025 writing through the loop variable",
        source: "let nums: i64[] = [1, 2];\nfor (const n of &nums) { *n *= 2; }\nconsole.log(nums);\n",
        expected: &[],
        actual: &[],
    },
    Row {
        id: "S:1027 a loop that grows its array",
        source: "let q = [1, 2, 3];
for (let i = 0; i < q.length(); i++) {
  if (q[i] < 10) { q.push(q[i] * 10); }
  console.log(q[i]);
}
",
        expected: &[],
        actual: &[],
    },
    Row {
        id: "S:994 a field moved out by destructuring",
        source: "const ada = new Person { name: \"Ada\", age: 36 };
const { name, age } = ada;
console.log(name, age);
console.log(ada.name);

public class Person { public name: string; public age: i64; }
",
        expected: &[("EN0601", 4)],
        actual: &[("EN0601", 4)],
    },
    Row {
        id: "TK-01-local",
        source: "let pr = new Pair { a: 0, b: 0 };
const r = both(&pr);
*r[0] = 1;
*r[1] = 2;
console.log(pr.a, pr.b);

public class Pair { public a: i64; public b: i64; }
private function both(p: &Pair): [&i64, &i64] { const t: [&i64, &i64] = [&p.a, &p.b]; return t; }
",
        expected: &[],
        actual: &[],
    },
    Row {
        // The row names the first push; each later push is its own site.
        id: "TK-01-pick",
        source: "let data: i64[] = [1, 2];
let h = new Holder(&data);
const [arr, e] = h.pick(false);
arr.push(3);
arr.push(4);
arr.push(5);
arr.push(6);
console.log(*e);

public class Holder {
  private view: &i64[];
  private own: i64[] = [];
  public constructor(v: &i64[]) { this.view = v; }
  public pick(c: bool): [&i64[], &i64] { const p = c ? &this.own : this.view; return [p, &this.view[0]]; }
}
",
        expected: &[("EN0614", 4)],
        actual: &[("EN0614", 4), ("EN0614", 5), ("EN0614", 6), ("EN0614", 7)],
    },
    Row {
        // A part of a nullable tuple local takes parts(b)'s choice (A:935), and
        // each part's loan keeps its part step (plan d.14), so the destructure's
        // copies into `a` and `b` no longer meet.
        id: "TK-01-dup",
        source: "let grid: i64[][] = [[1, 2], [3, 4]];
const p = dup(&grid);
if (p != null) { const [a, b] = p; const e = &a[0]; b.push(9); console.log(*e); }

public function two(a: &i64[], b: &i64[]): [&i64[], &i64[]] { return [a, b]; }
public function dup(rows: &Slice<i64[]>): [&i64[], &i64[]] | null { for (const r of rows) { return two(r, r); } return null; }
",
        expected: &[("EN0614", 3)],
        actual: &[("EN0614", 3)],
    },
    Row {
        id: "FV-02-swap",
        source: "const t: u8[] = [1, 2];
const o: u8[] = [3, 4];
let v = new View(&t, &o);
v.swap();
console.log(v.last());

public class View {
  private src: readonly &Slice<u8>;
  private dst: &Slice<u8>;
  public constructor(s: &Slice<u8>, d: &Slice<u8>) { this.src = s; this.dst = d; }
  public swap(): void { this.dst = this.src; }
  public last(): readonly &Slice<u8> { return this.dst.slice(0, 1); }
}
",
        expected: &[],
        actual: &[],
    },
    Row {
        id: "FV-02-main",
        source: "let t: u8[] = [1, 2];
const o: u8[] = [3, 4];
let v = new View(&t, &o);
const d = v.last();
t[0] = 9;
console.log(d);

public class View {
  private src: readonly &Slice<u8>;
  private dst: &Slice<u8>;
  public constructor(s: &Slice<u8>, d: &Slice<u8>) { this.src = s; this.dst = d; }
  public last(): readonly &Slice<u8> { return this.dst.slice(0, 1); }
}
",
        expected: &[("EN0706", 5)],
        actual: &[("EN0706", 5)],
    },
    Row {
        id: "FV-02-alias",
        source: "let buf: u8[] = [1];
const tbl: u8[] = [0];
let c = Copier.alias(&tbl, &buf);
const a = c.peek();
c.step();
c.step();
c.step();
c.step();
console.log(*a);

public final class Copier {
  private src: readonly &u8[];
  private dst: &u8[];
  public constructor(s: &u8[], d: &u8[]) { this.src = s; this.dst = d; }
  public static make(s: &u8[], d: &u8[]): Copier { return new Copier(s, d); }
  public peek(): readonly &u8 { return &this.src[0]; }
  public step(): void { this.dst.push(1); }
  public static alias(s: &u8[], d: &u8[]): Copier {
    let w = Copier.make(s, d);
    const p = w.dst;
    w.src = p;
    return w;
  }
}
",
        expected: &[("EN0616", 21), ("EN0709", 22)],
        actual: &[("EN0616", 21), ("EN0709", 22)],
    },
    Row {
        id: "FV-02-move fused",
        source: "const table: u8[3] = [7, 8, 9];
let out: u8[3] = [0, 0, 0];
let c = new Copier(&table, &out).fused();
c.step();
console.log(out);

public class Copier {
  private src: readonly &Slice<u8>;
  private dst: &Slice<u8>;
  private pos: isize = 0;
  public constructor(s: &Slice<u8>, d: &Slice<u8>) { this.src = s; this.dst = d; }
  public step(): void { this.dst[this.pos] = this.src[this.pos]; this.pos += 1; }
  public move fused(): Copier { this.src = this.dst.slice(0, 1); return this; }
}
",
        expected: &[("EN0616", 13), ("EN0709", 13)],
        actual: &[("EN0616", 13), ("EN0709", 13)],
    },
    Row {
        id: "FV-02-move consume",
        source: "const table: u8[3] = [7, 8, 9];
let out: u8[3] = [0, 0, 0];
console.log(new Copier(&table, &out).consume());

public class Copier {
  private src: readonly &Slice<u8>;
  private dst: &Slice<u8>;
  private pos: isize = 0;
  public constructor(s: &Slice<u8>, d: &Slice<u8>) { this.src = s; this.dst = d; }
  public step(): void { this.dst[this.pos] = this.src[this.pos]; this.pos += 1; }
  public move consume(): u8 { this.src = this.src.slice(1, this.src.length()); return this.src[0]; }
}
",
        expected: &[],
        actual: &[],
    },
    Row {
        // O7: no exclusive loan (the copy is never written through), but a
        // shared one, since the source is write-live (A:935).
        id: "A:935 a reborrow whose source is written takes a shared loan",
        source: "let x = 3;
console.log(f(&x));

function f(let r: &i64): i64 {
  const c = r;
  *r = 1;
  return *c;
}
",
        expected: &[("EN0706", 6)],
        actual: &[("EN0706", 6)],
    },
    Row {
        id: "S2-02-init",
        source: "const p = new Pair {};
console.log(p.b);

private class Pair { public a: i64 = 1; public b: i64 = this.a + 1; }
",
        expected: &[("EN0610", 4)],
        actual: &[("EN0610", 4)],
    },
    Row {
        // fix-2: a `default` after the `null` arm is the non-null fact's test
        // (S:1146), so the write in it does not reach the next turn's use.
        id: "S:1146 a default arm after a null arm sees the subject non-null",
        source: "public class Holder { public v: i64 | null = null; }
public function poke(h: &Holder): void { h.v = null; }
public function loopy(h: &Holder, n: i64): i64 {
  let t: i64 = 0;
  for (const i of 0..n) {
    match (h.v) {
      null => { t += 1; },
      default => {
        t += h.v;
        poke(h);
      },
    }
  }
  return t;
}
",
        expected: &[],
        actual: &[],
    },
    Row {
        // fix-2: a captured closure is called through its env (A:972-973).
        id: "A:973 an arrow calls a captured closure parameter, local and nullable one",
        source: "public function run(g: () => void): void { g(); }
public function outer(f: () => void): void {
  run(() => { f(); });
}
public function local(): i64 {
  let n = 0;
  const inc = () => { n += 1; };
  run(() => { inc(); });
  return n;
}
public function opt(h?: (k: u8) => void): void {
  run(() => { if (h != null) { h(1); } });
}
",
        expected: &[],
        actual: &[],
    },
    Row {
        // fix-2: a `move` method of a Copy class through a `Box`: the object is
        // copied out with its class check, then called directly (A:943).
        id: "A:943 a move method through a Box",
        source: "public class Pt implements Copy {
  public x: i64 = 0;
  public move take(): i64 { return this.x; }
}
public class Animal {
  public name: string = \"a\";
  public move into(): string { return this.name; }
}
public function viaBox(bp: Box<Pt>): i64 { return bp.take(); }
public function intoBox(b: Box<Animal>): string { return b.into(); }
",
        expected: &[("EN0605", 10)],
        actual: &[("EN0605", 10)],
    },
    Row {
        // fix-2: a bound member is called through the table (A:1281), so phase 3
        // applies the declared contract, with `this` among the sources.
        id: "A:1281 a class-bounded receiver applies the declared contract",
        source: "let d = new Dog();
const s = pick(&d);
d.name = \"z\";
console.log(s);

public class Animal {
  public label(): &string { return \"animal\"; }
}
public class Dog extends Animal {
  public name: string = \"rex\";
  public override label(): &string { return &this.name; }
}
public function pick<T extends Animal>(a: &T): &string { return a.label(); }
",
        expected: &[("EN0706", 3)],
        actual: &[("EN0706", 3)],
    },
    Row {
        id: "A:1281 a by-value bound receiver applies the declared contract",
        source: "let s = new Sub();
const o: i64[] = [5];
console.log(*keep(s, &o));

public class Base { public v: i64[] = [1, 2]; public constructor() {} public pick(x: &i64[]): &i64[] { return x; } }
public class Sub extends Base { public constructor() { super(); } public override pick(x: &i64[]): &i64[] { return &this.v; } }
public function keep<T extends Base>(t: T, x: &i64[]): &i64[] { return t.pick(x); }
",
        expected: &[("EN0710", 7)],
        actual: &[("EN0710", 7)],
    },
    Row {
        // fix-2: `!` leaves its tag check to the place's user, after the index.
        id: "INF-04 `!` then an index verifies",
        source: "let s = new Sub();
const a = s.first();
console.log(*a);

public class Sub { private seen: readonly &i64[] | null = null; public constructor() {} public first(): readonly &i64 { return &this.seen![0]; } }
",
        expected: &[],
        actual: &[],
    },
    Row {
        // fix-2: `&CONST` names the constant's static, with no loan (S:756).
        id: "S:756 a reference to a constant outlives its statement",
        source: "let keep: &i64 | null = null;
for (const x of &K) { keep = x; }
if (keep != null) { console.log(*keep); }
console.log(f());

private const K: i64[2] = [1, 2];
private const P: i64[2] = [1, 2];
public function f(): i64 {
  const r = &P;
  return r[0];
}
",
        expected: &[],
        actual: &[],
    },
    Row {
        id: "OQ12-fn the readonly variant returns `&ZERO`",
        source: "const z: fn(xs: &Slice<i64>) => readonly &i64 = firstOrZero;
let v = [1, 2];
console.log(z(&v));

private const ZERO: i64 = 0;
private function firstOrZero(xs: &Slice<i64>): &i64 {
  if (xs.isEmpty()) { return &ZERO; }
  return &xs[0];
}
",
        expected: &[],
        actual: &[],
    },
    Row {
        id: "S2-14-const writing through a loop over `&TABLE`",
        source: "for (const t of &TABLE) { *t = 0; }
bump(&N);

function bump(p: &i64): void { *p += 1; }
private const TABLE: i64[3] = [1, 2, 3];
private const N: i64 = 1;
",
        expected: &[("EN0608", 1), ("EN0608", 2)],
        actual: &[("EN0608", 1), ("EN0608", 2)],
    },
    Row {
        // fix-2: a `super(...)` in an arrow is its one EN0619 (A:939).
        id: "C4-super-paths `super` in an arrow",
        source: "const d = new Dog(\"Rex\");

public class Animal {
  public tricks: string[];
  public constructor(public name: string) {}
}
public class Dog extends Animal {
  public constructor(name: string) {
    const f = () => super(name);
    super(name);
  }
}
",
        expected: &[("EN0619", 9)],
        actual: &[("EN0619", 9)],
    },
    Row {
        // fix-2: C12 on a local holding an arrow (S:968) and on an `fn` value.
        id: "S:968 a local holding an arrow at a closure parameter",
        source: "const xs: i64[] = [1, 2, 3];
const double = (x: &i64) => x * 2;
console.log(xs.map(double));
let k = 2;
const addk = (x: i64) => x + k;
console.log(apply(addk, 4));

private function apply(f: (x: i64) => i64, v: i64): i64 { return f(v); }
",
        expected: &[],
        actual: &[],
    },
    Row {
        // The env holds `&count [closure-capture]` (SHAPES); a named function
        // that writes its hidden arguments makes the capture exclusive, as a
        // writing arrow's does (wlive), so it meets `r`: EN0715, as its sibling
        // `run(() => { inc(); })`.
        id: "C12 a local function with hidden arguments at a closure parameter",
        source: "let count = 0;
function inc(): void { count += 1; }
const r = &count;
run(inc);
console.log(r);

private function run(g: () => void): void { g(); }
",
        expected: &[("EN0715", 4)],
        actual: &[("EN0715", 4)],
    },
    Row {
        // A literal view's temporary ends with its statement (S:964); a view
        // nothing writes through makes no loan (A:970) and becomes a static.
        id: "S:964 a constant literal view kept and returned",
        source: "const primes: &Slice<i64> = &[2, 3, 5, 7];
console.log(total(primes), zeros());

function total(xs: &Slice<i64>): i64 { let s = 0; for (const x of xs) { s += *x; } return s; }
function zeros(): &Slice<i64> { return &[0, 0]; }
",
        expected: &[],
        actual: &[],
    },
    Row {
        id: "S:964 a literal view written through is EN0712",
        source: "const p: &Slice<i64> = &[1, 2];\np[0] = 9;\nconsole.log(p);\n",
        expected: &[("EN0712", 1)],
        actual: &[("EN0712", 1)],
    },
    Row {
        // fix-2: the objects of `mem.swap` and `mem.replace` are checked before
        // their borrows (SHAPES), so the checks read under no loan.
        id: "A:943 mem.swap and mem.replace through references",
        source: "let x = new Animal();
let y = new Animal();
sw(&x, &y);
console.log(x.n, y.n);

public class Animal { public n: i64 = 1; }
public function sw(a: &Animal, b: &Animal): void {
  mem.swap(a, b);
  const old = mem.replace(a, new Animal());
  console.log(old.n);
}
",
        expected: &[],
        actual: &[],
    },
    Row {
        // fix-2: `new B("x")` stores B's initialisers (SHAPES), then calls A's
        // constructor on `convert(upcast, &dest [auto-borrow])`, which phase 3
        // reads as a `new` that initialises the destination, never a `super`.
        id: "Q31 a subclass with no constructor over a base that has one",
        source: "const b = new B(\"x\");
console.log(b.name, b.n, b.extra);

public class A {
  public n: i64 = 1;
  public constructor(public name: string) {}
}
public class B extends A {
  public override n: i64 = 2;
  public extra: i64 = 3;
}
",
        expected: &[],
        actual: &[],
    },
    Row {
        // fix-2: a `for...of` statement's temporaries end with its span, which
        // the EN0712 then carries (a dummy span had made phase 3 panic).
        id: "S:1007 a loop source's temporary kept past the loop",
        source: "let keep: &i64 | null = null;
for (const x of &make()) { keep = x; }
if (keep != null) { console.log(*keep); }

function make(): i64[] { return [1, 2]; }
",
        expected: &[("EN0712", 2)],
        actual: &[("EN0712", 2)],
    },
    Row {
        // The `move` method's scope drop of `*this` (A:638), which `return this`
        // moved out, drops nothing: the access check skips a scope `Drop` of a
        // definitely moved path, as elaboration removes it.
        id: "FV-02-move fused, over a class that needs a drop",
        source: "const table: u8[3] = [7, 8, 9];
let out: u8[3] = [0, 0, 0];
let c = new Copier(&table, &out).fused();
c.step();
console.log(out);

public class Copier {
  private src: readonly &Slice<u8>;
  private dst: &Slice<u8>;
  private pos: isize = 0;
  public tag: string = \"t\";
  public constructor(s: &Slice<u8>, d: &Slice<u8>) { this.src = s; this.dst = d; }
  public step(): void { this.dst[this.pos] = this.src[this.pos]; this.pos += 1; }
  public move fused(): Copier { this.src = this.dst.slice(0, 1); return this; }
}
",
        expected: &[("EN0616", 14), ("EN0709", 14)],
        actual: &[("EN0616", 14), ("EN0709", 14)],
    },
    Row {
        // `mix`'s own body is rejected, so its call adds no read-set report for the
        // store its contract records (review 3, report.rs:2208).
        id: "INF-04-upcast the `retarget` form",
        source: r##"const k: u8[] = [1];
let out: u8[] = [0];
let s = new Sub(&k, &out);
s.mix();

public class Base {
  private src: readonly &Slice<u8>;
  public constructor(s: &Slice<u8>) { this.src = s; }
  public retarget(v: &Slice<u8>): void { this.src = v; }
}
public final class Sub extends Base {
  private dst: &Slice<u8>;
  public constructor(s: &Slice<u8>, d: &Slice<u8>) { this.dst = d; super(s); }
  public step(): void { this.dst[0] = 1; }
  public mix(): void { const b: &Base = this; b.retarget(this.dst.slice(0, 1)); }
}
"##,
        expected: &[("EN0708", 15)],
        actual: &[("EN0708", 15)],
    },
    Row {
        // The same: no read-set report at `s.mix()`.
        id: "INF-04-upcast the `retarget` form through `this`",
        source: r##"const k: u8[] = [1];
let out: u8[] = [0];
let s = new Sub(&k, &out);
s.mix();

public class Base {
  private src: readonly &Slice<u8>;
  public constructor(s: &Slice<u8>) { this.src = s; }
  public retarget(v: &Slice<u8>): void { this.src = v; }
}
public final class Sub extends Base {
  private dst: &Slice<u8>;
  public constructor(s: &Slice<u8>, d: &Slice<u8>) { this.dst = d; super(s); }
  public step(): void { this.dst[0] = 1; }
  public mix(): void { const p = this.dst.slice(0, 1); const b: &Base = this; b.retarget(p); }
}
"##,
        expected: &[("EN0706", 15)],
        actual: &[("EN0706", 15)],
    },
    Row {
        // Only the misfit: the virtual `b.put(&data)` applies `Base.put`'s store,
        // into the main set, and `a`, which `s.first()` reads through the payload
        // of the `readonly &` field `seen`, holds `s`'s read set alone
        // (`through_read`), so `data = [9, 9, 9, 9]` meets no loan.
        id: "INF-04-read-bit-put",
        source: r##"const table: i64[] = [7];
let data: i64[] = [1, 2, 3];
let s = new Sub();
s.seed(&table);
const b: &Base = &s;
b.put(&data);
const a = s.first();
data = [9, 9, 9, 9];
console.log(*a);
public class Base {
  private keep: &i64[] | null = null;
  public constructor() {}
  public put(x: &i64[]): void { this.keep = x; }
}
public class Sub extends Base {
  private seen: readonly &i64[] | null = null;
  public constructor() { super(); }
  public override put(x: &i64[]): void { this.seen = x; }
  public seed(x: &i64[]): void { this.seen = x; }
  public first(): readonly &i64 { return &this.seen![0]; }
}
"##,
        expected: &[("EN0615", 18)],
        actual: &[("EN0615", 18)],
    },
];

fn pairs(list: &[(&str, u32)]) -> Vec<(String, u32)> {
    list.iter().map(|&(c, l)| (c.to_owned(), l)).collect()
}

/// MIR shapes that stages 2B and 2C meet at, built from source: each with the
/// pieces its text must contain.
const SHAPES: &[(&str, &str, &[&str])] = &[
    (
        "operators read through one reference (S:684)",
        "const k = 3;
const s: u8 = 7;
console.log(cmp(&k, 1), neg(&k), add(1, &k), comp(&k), widen(&s), sh(&s));

function cmp(a: &i64, b: i64): bool { return a < b; }
function neg(n: &i64): i64 { return -n; }
function add(a: i64, n: &i64): i64 { return a + n; }
function comp(n: &i64): i64 { let x: i64 = 1; x += n; return x; }
function widen(b: &u8): u32 { return b as u32; }
function sh(r: &u8): u32 { let x: u32 = 1; x <<= r; return x; }
",
        &[
            "_0 = lt(copy *_1, copy _2);",
            "_0 = checked_neg(copy *_1);",
            "_0 = checked_add(copy _1, copy *_2);",
            "_2 = checked_add(copy _3, copy *_1);",
            "_0 = cast(int_to_int, copy *_1, u32);",
            "_2 = checked_shl(copy _3, copy *_1);",
        ],
    ),
    (
        "a destructuring declaration's bindings end with their block (c.15)",
        "const pair: [string, i64] = [\"a\", 1];\n{\n  const [w, n] = pair;\n  console.log(w, n);\n}\n",
        &[
            "_3 = move _2.0;",
            "_4 = copy _2.1;",
            "storage_dead(_4);\n    drop(_3);\n    storage_dead(_3);\n    drop(_2);",
        ],
    ),
    (
        "an arrow body reads a captured local through its env (c.16)",
        "const count = 3;\nconst xs = [1, 2, 3];\nxs.forEach(x => console.log(x + count));\n",
        &["_3 = checked_add(copy *_2, copy *(*_1).0);"],
    ),
    (
        "a reference read out of a field is one `Use(Copy)` (A:935)",
        "const t: u8[] = [1, 2];\nlet v = new View(&t);\nconsole.log(v.first());\n
public class View {
  private src: &Slice<u8>;
  public constructor(s: &Slice<u8>) { this.src = s; }
  public first(): &Slice<u8> { return this.src.slice(0, 1); }
}
",
        &["_3 = copy (*_1).src;\n    _0 = \"core/slice\"::Slice<u8>::slice(move _3,"],
    ),
    (
        "a packed field is copied before a form borrows it (A:977)",
        "const p = new P { a: 1, b: 7 };\nconsole.log(p.b);\nconsole.log(`${p.b}`);\n\n@packed public final class P { public a: u8; public b: u32; }\n",
        &[
            "_6 = copy _2.b;\n    _7 = &_6 [temp-arg];\n    _5 = form log(move _7)",
            "_9 = copy _2.b;\n    _10 = &_9 [temp-arg];",
        ],
    ),
    (
        "a fixed error text is a static descriptor (c.12)",
        "console.log(parse(&\"x\".toString()));\n\npublic function parse(s: &string): Result<i64> {\n  if (s.isEmpty()) { return Err(\"e\"); }\n  return 1;\n}\n",
        &["form failure_text(const \"e\": &string)"],
    ),
    (
        "parameters drop in reverse order, a move method's object last (S:1032, A:638)",
        "two(\"a\".toString(), \"b\".toString());\nconst f = new File { name: \"f\".toString() };\nf.close(\"c\".toString());\n
public function two(a: string, b: string): void { console.log(a, b); }
public final class File {
  public name: string;
  public move close(why: string): void { console.log(why); }
}
",
        &[
            "bb1: {\n    drop(_2);\n    drop(_1);\n    return;",
            "drop(_2);\n    drop(*_1);\n    return;",
        ],
    ),
    (
        "a move method through a Box copies its object out, checked (A:943)",
        "public class Pt implements Copy {\n  public x: i64 = 0;\n  public move take(): i64 { return this.x; }\n}\npublic function viaBox(bp: Box<Pt>): i64 { return bp.take(); }\n",
        &["check_class(*_1, copy_out, box);\n    _2 = copy *_1;\n    _0 = Pt::take(move _2)"],
    ),
    (
        "bound members through the table: a class bound, an interface box (A:1281, V16)",
        "const xs: Box<Shape>[] = [new Box(new Sq())];\nconsole.log(boxes(&xs), gen(&new Sq()));\n
public interface Shape { area(): f64; }
public class Sq implements Shape { public s: f64 = 1.0; public area(): f64 { return this.s; } }
public function boxes(bs: &Box<Shape>[]): f64 { let t = 0.0; for (const b of bs) { t += b.area(); } return t; }
public function gen<T extends Sq>(s: &T): f64 { return s.area(); }
public function iface<T extends Shape>(s: &T): f64 { return s.area(); }
",
        &[
            "virtual Shape::area [copy _9](move _9)",
            "_2 = &*_1 [reborrow];\n    _0 = virtual Sq::area [copy _2](move _2)",
            "_2 = &*_1 [reborrow];\n    _0 = Shape::area(move _2)",
        ],
    ),
    (
        "C12: a closure local reborrowed, an fn value in its env, a local function's hidden arguments captured (c.16)",
        "let count = 0;\nfunction inc(): void { count += 1; }\nrun(inc);\nconst dbl: fn(x: i64) => i64 = (x: i64) => x * 2;\nconsole.log(apply(dbl, 4));\n
public function g(k: i64): i64 {
  const addk = (x: i64) => x + k;
  return apply(addk, 4);
}
private function apply(f: (x: i64) => i64, v: i64): i64 { return f(v); }
private function run(f: () => void): void { f(); }
",
        &[
            "_4 = &_2 [closure-capture];\n    _5 = env(move _4);\n    _6 = closure(fn inc, _5);\n    _3 = run(move _6)",
            "_10 = env(copy _7);\n    _11 = closure(fn_value, _10);",
            "_5 = closure_reborrow(_2);\n    _0 = apply(move _5, const 4: i64)",
        ],
    ),
    (
        "a local function calls a top-level closure through its hidden argument (A:972)",
        "let n = 0;\nconst inc = () => { n += 1; };\nfunction twice(): void { inc(); inc(); }\ntwice();\nconsole.log(n);\n",
        &["_3 = closure_reborrow(*_1);\n    _2 = closure _3() -> bb1;"],
    ),
    (
        "the objects of mem.swap and mem.replace are checked before their borrows (A:943)",
        "public class Animal { public n: i64 = 1; }\npublic function sw(a: &Animal, b: &Animal): void {\n  mem.swap(a, b);\n  const old = mem.replace(a, new Animal());\n}\npublic function boxes(p: Box<Animal>, q: Box<Animal>): void {\n  let a = p; let b = q;\n  mem.swap(&*a, &*b);\n}\n",
        &[
            "check_class(*_1, swap, ref);\n    _4 = &*_1 [reborrow];\n    check_class(*_2, swap, ref);\n    _5 = &*_2 [reborrow];",
            "check_class(*_1, replace, ref);\n    _7 = &*_1 [reborrow];",
            "check_class(*_3, swap, box);\n    _6 = &*_3 [explicit];\n    check_class(*_4, swap, box);\n    _7 = &*_4 [explicit];",
        ],
    ),
    (
        "a subclass's synthesised constructor is inlined: at `new`, and before a `super(...)` that skips it (A:939)",
        "const c = new C(5);\nconst b = new B();\nconsole.log(c.n, b.n);\n
public class A {
  public n: i64 = 1;
  public constructor(public name: string = \"anon\") {}
}
public class B extends A {
  public override n: i64 = 2;
}
public class C extends B {
  public w: i64;
  public constructor(w: i64) { this.w = w; super(\"cc\"); }
}
",
        &[
            "set_table(_5, B);\n    _5.n = const 2: i64;\n    _6 = &_5 [auto-borrow];\n    _7 = convert(upcast, move _6);\n    _8 = A::#ctor(move _7, const 0: isize)",
            "switch const overridden(n): bool [0: bb",
            "field_init((*_1).n, const 2: i64);",
        ],
    ),
    (
        "an arrow in a local function passes its hidden arguments from its env (c.16, A:1360)",
        "let count = 0;\nfunction inc(): void { count += 1; }\nfunction outer(): void { run(() => { inc(); }); }\nouter();\n\nprivate function run(g: () => void): void { g(); }\n",
        &[
            "_4 = &*_1 [closure-capture];\n    _5 = env(move _4);\n    _3 = closure(arrow#0, _5);",
            "capture count: &int path;\n  bb0: {\n    _3 = &*(*_1).0 [hidden-arg];\n    _2 = inc(move _3)",
        ],
    ),
    (
        "a logical operand's temporaries end in its own block; `Ok {}` off a `Result<void>`; a closure parameter's capture; C08's class check",
        "console.log(both(true), ok(), pass(() => {}), rt(null));\n
public function both(a: bool): bool { return a && \"x\".toString().isEmpty(); }
public function ok(): Result<void> { console.log(1); }
public function pass(f: () => void): i64 { run(() => { f(); }); return 1; }
private function run(g: () => void): void { g(); }
public class Pt implements Copy { public x: i64 = 0; }
public function rt(r: &Pt | null): Pt | null { return r; }
",
        &[
            // `_3`, the `toString()` result, is created after `_4`, the literal it
            // is made from, so it ends first (S 5.7 D2).
            "bb5: {\n    drop(_3);\n    storage_dead(_3);\n    drop(_4);\n    storage_dead(_4);\n    goto bb3;",
            "_0 = Result<void>::Ok { value: const void: void };",
            "capture f: &(() => void) closure_param;",
            "check_class(*(_1 as Present).0, copy_out, ref);",
        ],
    ),
    (
        "an inlined synthesised constructor keeps the body's narrowing records (c.20)",
        "public class Holder { public v: i64 | null = null; }
public class A { public n: i64 = 1; public constructor(public name: string) {} }
public class B extends A { public override n: i64 = 2; }
public function poke(h: &Holder): void { h.v = null; }
public function loopy(h: &Holder, n: i64): i64 {
  let t: i64 = 0;
  for (const i of 0..n) {
    if (h.v != null) {
      t += h.v;
      poke(h);
      const b = new B(\"x\");
    }
  }
  return t;
}
",
        &["record f0 at bb6[4] _13 call_arg;"],
    ),
];

/// The programs of the rows that the doc row accepts and phase 3 passes, by case
/// name: hosts of `mutants`' violations (TESTING 14).
pub fn accepted() -> Vec<(String, String)> {
    (ROWS.iter())
        .filter(|row| row.expected.is_empty() && row.actual.is_empty())
        .map(|row| (format!("programs/{}", row.id), row.source.to_owned()))
        .collect()
}

pub fn register(h: &mut Harness) {
    h.case("programs/a capture's record is made once, at its env field (c.20)", || {
        let source = "f(null);\n\nfunction f(n: i64 | null): void {\n  if (n != null) {\n    const c = () => n;\n    c();\n  }\n}\n";
        let text = crate::support::build(source).text();
        let records: Vec<&str> = text.lines().filter(|l| l.contains(" capture;")).collect();
        assert_eq!(records, ["  record f0 at bb1[1] _5 capture;"], "{text}");
    });
    h.case(
        "programs/an optional call evaluates its base once (O6, c.7)",
        || {
            let source = "public class Node {
  public kids: Node[] = [];
  public label(): string { return \"n\"; }
  public find(i: isize): &Node | null { return this.kids.get(i); }
}
public function count(): i64 { return 1; }
public function twice(n: &Node): string | null { return n.find(count() as isize)?.label(); }
";
            let text = crate::support::build(source).text();
            let body = text.split("fn twice(").nth(1).expect("twice's body");
            assert_eq!(body.matches("count()").count(), 1, "{body}");
            assert_eq!(body.matches("Node::find").count(), 1, "{body}");
            assert!(
                body.contains("_8 = &*(_2 as Present).0 [reborrow];"),
                "{body}"
            );
        },
    );
    for &(name, source, pieces) in SHAPES {
        h.case(format!("programs/{name}"), move || {
            let text = crate::support::build(source).text();
            for piece in pieces {
                assert!(text.contains(piece), "no `{piece}` in\n{text}");
            }
        });
    }
    for row in ROWS {
        let status = match row.expected == row.actual {
            true => "matches its doc row",
            false => "differs from its doc row (pinned)",
        };
        h.case(format!("programs/{}: {status}", row.id), move || {
            assert_eq!(crate::support::phase3(row.source), pairs(row.actual));
        });
    }
}
