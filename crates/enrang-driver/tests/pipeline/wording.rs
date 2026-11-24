//! The wording of phase 3's codes beyond SPEC 14's G cases (M3 plan e, d.13;
//! stage 3): one program per message form through `check`, its stderr pinned in
//! `tests/golden/pipeline/wording/<name>.txt`, the code its name starts with among
//! the errors, and every fix-it, applied on its own, removing its diagnostic and
//! adding no error (A:1314, warnings allowed).

use enrang_diag::{Code, Severity, apply_fixes};
use enrang_testkit::{Harness, golden};

use crate::goldens::{of_code, run};

/// Each program, named `<code>-<form>`.
const PROGRAMS: &[(&str, &str)] = &[
    (
        "en0601-assigned",
        "let a = \"x\".toString();\nconst b = a;\nconsole.log(a, b);\n",
    ),
    (
        "en0601-loop",
        "let q = [\"a\", \"b\"];\nfor (const x of q) { console.log(x); }\nconsole.log(q);\n",
    ),
    (
        "en0601-destructured",
        "const ada = new Person { name: \"Ada\", age: 36 };
const { name, age } = ada;
console.log(name, age);
console.log(ada.name);

public class Person { public name: string; public age: i64; }
",
    ),
    (
        "en0601-move-method",
        "const e = new Env { inside: \"a\" };
const l = e.open();
console.log(l, e.inside);

public class Env {
  public inside: string = \"\";
  public move open(): string { return this.inside; }
}
",
    ),
    (
        "en0602",
        "let g: User;\nconsole.log(g.name);\n\npublic class User { public name: string = \"\"; }\n",
    ),
    (
        "en0603-this",
        "public class P {\n  public name: string = \"\";\n  public getName(): string { return this.name; }\n}\n",
    ),
    (
        "en0603-reference",
        "public function f(x: &P): string { return x.name; }\npublic class P { public name: string = \"\"; }\n",
    ),
    (
        "en0603-loop-source",
        "public class Q {\n  public items: string[] = [];\n  public all(): void { for (const x of this.items) { console.log(x); } }\n}\n",
    ),
    (
        "en0604",
        "const names = [\"a\".toString()];\nconst n = names[0];\nconsole.log(n);\n",
    ),
    (
        "en0605",
        "const b: Box<string> = new Box(\"a\".toString());\nconst s = *b;\nconsole.log(s);\n",
    ),
    (
        "en0607",
        "const f = new File { name: \"x\" };
const n = f.name;
console.log(n);

public class File {
  public name: string = \"\";
  public destructor() { console.log(\"closed\"); }
}
",
    ),
    (
        "en0608-argument",
        "const data: i64[] = [1];\nfill(&data);\n\npublic function fill(buf: &i64[]): void { buf.push(1); }\n",
    ),
    ("en0608-write", "const xs = [1, 2];\nxs[0] = 3;\n"),
    (
        "en0608-through-a-reference",
        "const k = 12;\nlet w = &k;\n*w = 13;\n",
    ),
    (
        "en0609",
        "public class R {\n  public readonly id: i64 = 0;\n  public set(): void { this.id = 1; }\n}\n",
    ),
    (
        "en0610-field-initialiser",
        "public class C {\n  public a: i64 = 1;\n  public b: i64 = this.a;\n}\n",
    ),
    (
        "en0610-inherited-unset",
        "public class Person { public constructor(public name: string) {} }
public class Shape { public color: string = \"red\"; public owner: Person; }
public class Circle extends Shape {
  public constructor(public r: i64, o: Person) {
    super();
  }
}
",
    ),
    (
        "en0610-before-super",
        "public class A { public constructor(public name: string) {} }
public class B extends A {
  public age: i64;
  public constructor(n: string) {
    console.log(this.name);
    this.age = 1;
    super(n);
  }
}
",
    ),
    (
        "en0611",
        "let q = [\"a\"];\nlet n = 0;\nwhile (n < 2) {\n  console.log(q);\n  const t = q;\n  n++;\n}\n",
    ),
    (
        "en0613-parameter",
        "public function clamp(x: i64): i64 { if (x > 10) { x = 10; } return x; }\n",
    ),
    ("en0613-const", "const x = 1;\nx = 2;\n"),
    (
        "en0614-parameter",
        "public function f(xs: i64[]): void { xs.push(1); }\n",
    ),
    (
        "en0614-readonly-result",
        "let c = new Counter();
c.view().push(3);

public class Counter {
  private xs: i64[] = [];
  public view(): readonly &i64[] { return &this.xs; }
}
",
    ),
    (
        "en0615-parameter",
        "public interface Sink {\n  put(xs: &i64[]): void;\n}\n\npublic class S implements Sink {\n  public put(xs: &i64[]): void { xs.push(1); }\n}\n",
    ),
    (
        "en0615-library-member",
        "let a = new P { n: 1 };
let b = new P { n: 1 };
console.log(a == b);

public class P implements Eq {
  public n: i64 = 0;
  public equals(o: &P): bool { this.n = 2; return this.n == o.n; }
}
",
    ),
    (
        "en0616-readonly-result",
        "let c = new Counter();
*c.count() = 2;

public class Counter {
  private n: i64 = 0;
  public count(): readonly &i64 { return &this.n; }
}
",
    ),
    (
        "en0617",
        "const name = \"a\".toString();\nconst f = () => { const n = name; console.log(n); };\nf();\n",
    ),
    (
        "en0619-not-every-path",
        "public class A { public constructor(public name: string) {} }
public class B extends A {
  public constructor(quiet: bool) {
    if (quiet) { super(\"anon\"); }
  }
}
",
    ),
    (
        "en0619-twice",
        "public class A { public constructor(public age: i64) {} }
public class B extends A {
  public constructor(age: i64) {
    super(age);
    super(age);
  }
}
",
    ),
    (
        "en0621",
        "let s = \"a\".toString();\nconst t = (s += \"?\");\nconsole.log(t);\n",
    ),
    (
        "en0706-view",
        "let list = [1, 2];\nconst v = list.slice(0, 1);\nlist.push(3);\nconsole.log(v);\n",
    ),
    (
        "en0707-reassigned",
        "let xs = [1, 2];\nconst r = &xs;\nxs = [3];\nr.push(1);\n",
    ),
    (
        "en0707-compound-target",
        "function reset(t: &string): &string { *t = \"b\".toString(); return \"!\"; }\nlet s: string = \"a\".toString();\ns += reset(&s);\nconsole.log(s);\n",
    ),
    (
        "en0708-read",
        "let players: i64[] = [1];\nconst q = &players;\nconsole.log(players.length());\nq.push(1);\n",
    ),
    (
        "en0708-compound-target",
        "let s = \"ab\".toString();\ns += s.slice(0, 1);\nconsole.log(s);\n",
    ),
    (
        "en0709",
        "let q = [1];\nconst r = &q;\nconst m = q;\nconsole.log(r, m);\n",
    ),
    (
        "en0709-held-source",
        "let q = [1];\nfor (const x of &q) { const m = q; console.log(m); }\n",
    ),
    (
        "en0710-consumed-this",
        "public class P {\n  public pos: i64 = 0;\n  public move posRef(): &i64 { return &this.pos; }\n}\n",
    ),
    (
        "en0712",
        "const r = first(&\"a\".toString());\nconsole.log(r);\n\npublic function first(s: &string): &string { return s; }\n",
    ),
    (
        "en0714-override",
        "public class Labeler {
  public label(name: &string, fallback: &string): &string { return name; }
}
public class Strict extends Labeler {
  public override label(name: &string, fallback: &string): &string { return fallback; }
}
",
    ),
    (
        "en0715",
        "let count = 0;\nconst inc = () => { count += 1; };\ncount = 5;\ninc();\n",
    ),
    (
        "en0718",
        "let n = 0;\nconst f = () => { n += 1; };\nboth(f, () => { f(); });\n\npublic function both(f: () => void, g: () => void): void { f(); g(); }\n",
    ),
    (
        "en0418",
        "let data: i64[] = [1];
let c = new Cursor(&data);
const c2 = c;
c.all().push(4);

private class Cursor implements Copy {
  private xs: &i64[];
  public constructor(xs: &i64[]) { this.xs = xs; }
  public all(): &i64[] { return this.xs; }
}
",
    ),
    (
        "en0804",
        "let p = new P { a: 1, b: 2 };\nconst r = &p.b;\nconsole.log(*r);\n\n@packed\npublic final class P { public a: u8; public b: u32; }\n",
    ),
    (
        "en0401-narrowing",
        "public class H { public v: i64 | null = null; }
public function poke(h: &H): void { h.v = null; }
public function f(h: &H): i64 {
  if (h.v != null) { poke(h); return h.v; }
  return 0;
}
",
    ),
    (
        "en0615-value-row",
        r##"function bump(x: &i64[]): void { x.push(1); x.push(2); x.push(3); x.push(4); }
const w: fn(let x: &i64[]) => void = bump;
const r: fn(x: &i64[]) => void = w;
let data: i64[] = [1, 2, 3];
const e = &data[0];
r(&data);
console.log(*e);
"##,
    ),
    (
        "en0615-nested-row",
        r##"const readers: (fn(x: &i64) => void)[] = [rd];
const writers: (fn(let x: &i64) => void)[] = readers;
console.log(writers.length());

private function rd(x: &i64): void { console.log(*x); }
"##,
    ),
    (
        "en0615-string-form",
        r##"let msg: string = "hi".toString();
run(choose(false), &msg);
run(show, &msg);

private function run(f: fn(let s: &string) => void, s: &string): void { f(s); }
private function show(s: &string): void { console.log(s); }
private function quote(s: &string): void { console.log(`"${s}"`); }
private function choose(loud: bool): fn(s: &string) => void { return loud ? quote : show; }
"##,
    ),
    (
        "en0615-signature-row",
        r##"function bump(x: &i64[]): void { x.push(1); x.push(2); x.push(3); x.push(4); }
let s = new Sub(); const b: &Base = &s; b.apply(bump);
public class Base { public apply(f: fn(let x: &i64[]) => void): void { let v: i64[] = [1]; f(&v); } }
public class Sub extends Base { public override apply(f: fn(x: &i64[]) => void): void { let v: i64[] = [1, 2, 3]; const e = &v[0]; f(&v); console.log(*e); } }
"##,
    ),
    (
        "en0608-two-parameters",
        r##"let a: i64[] = [1];
const b: i64[] = [2];
both(&a, &b);

private function both(x: &i64[], y: &i64[]): void { x.push(1); y.push(2); }
"##,
    ),
    (
        "en0608-constructor",
        r##"const xs: i64[] = [1, 2];
const w = new Wrap(&xs);

private class Wrap {
  private r: &i64[];
  public constructor(r: &i64[]) { this.r = r; this.r.push(3); }
}
"##,
    ),
    (
        "en0608-method",
        r##"let counter = new Counter();
const items: i64[] = [1, 2];
counter.absorb(&items);

private class Counter {
  public n: i64 = 0;
  public absorb(xs: &i64[]): void { this.n += 1; xs.push(this.n); }
}
"##,
    ),
    (
        "en0706-hold-capture",
        r##"function run(f: () => void): void { f(); }
let q: i64[] = [1]; for (const x of &q) { run(() => { q.push(1); }); }
"##,
    ),
    (
        "en0706-hold-borrow",
        r##"let q: i64[] = [1];
for (const x of &q) { const r = &q; r.push(1); }
"##,
    ),
    (
        "en0706-hold-hidden-arg",
        r##"let q: i64[] = [1, 2];
function grow(): void { q.push(7); }
for (const x of &q) { grow(); }
"##,
    ),
    (
        "en0706-reassign-crossing",
        r##"let a: i64[] = [1]; let b2: i64[] = [2]; let r = &a; for (const x of r) { r = &b2; }
"##,
    ),
    (
        "en0708-later-read",
        r##"let q: i64[] = [1, 5, 3, 7];
let r = &q;
r.push(1);
console.log(r, q);
"##,
    ),
    (
        "en0616-local-function-closure",
        r##"function run(f: () => void): void { f(); }
let s = "ab".toString(); let lx = new Lexer(&s); let t = "xy".toString();
function bind(): void { lx.setSrc(&t); }
run(bind);
public class Lexer { private src: &string; public constructor(src: &string) { this.src = src; } public setSrc(s: &string): void { this.src = s; } }
"##,
    ),
    (
        "en0710-temporary",
        r##"let k = 0;
private function pair(n: i64): &Slice<i64> { return &[n, n]; }
"##,
    ),
    (
        "en0617-call",
        r##"function take(s: string): void { console.log(s); }
function run(f: () => void): void { f(); }
let name = "a".toString();
run(() => { take(name); });
"##,
    ),
    (
        "en0618",
        r##"report();
let count = 0;
function report(): void { console.log(`count = ${count}`); }
"##,
    ),
    (
        "en0614-aliased-parts",
        r##"let pt = new Pt(); pt.xs.push(1); pt.xs.push(2);
const [u, v] = lanes(&pt, false); const e = &u[0];
v.push(3); console.log(*e);
public class Pt { public xs: i64[] = []; public ys: i64[] = []; }
public function lanes(p: &Pt, c: bool): [&i64[], &i64[]] { const s = p; const second = c ? &p.ys : &s.xs; return [&p.xs, second]; }
"##,
    ),
    (
        "en0614-readonly-field",
        r##"let t: i64[][] = [[1], [2]];
const f = new Finder(&t);
const r = f.find(2);
if (r != null) { r.push(5); }
public final class Finder { private rows: readonly &Slice<i64[]>; public constructor(r: &Slice<i64[]>) { this.rows = r; } public find(first: i64): &i64[] | null { for (const r of this.rows) { if (r[0] == first) { return r; } } return null; } }
"##,
    ),
    (
        "en0616-tuple-part",
        r##"let buf: u8[] = [1];
const tbl: u8[] = [0];
let r = Copier.nested(&tbl, &buf);
const a = r[0].peek(); r[0].step(); r[0].step(); r[0].step(); r[0].step(); console.log(*a);
public final class Copier { private src: readonly &u8[]; private dst: &u8[]; public constructor(s: &u8[], d: &u8[]) { this.src = s; this.dst = d; } public static make(s: &u8[], d: &u8[]): Copier { return new Copier(s, d); } public peek(): readonly &u8 { return &this.src[0]; } public step(): void { this.dst.push(1); }
  public static nested(s: &u8[], d: &u8[]): [Copier, i32] { let t: [Copier, i32] = [Copier.make(s, d), 0]; const p = t[0].dst; t[0].src = p; return t; } }
"##,
    ),
    (
        "en0603-deref",
        r##"const a = new Animal("rex");
console.log(f(&a));

private class Animal implements Clone {
  public constructor(public name: string) {}
  public clone(): Animal { return new Animal(this.name.clone()); }
}

private function f(r: &Animal): string {
  const c = *r;
  return c.name;
}
"##,
    ),
    (
        "en0706-reassign-deref",
        r##"let b: Box<i64[]> = new Box([1, 2]);
for (const x of &*b) { b = new Box([3]); }
"##,
    ),
    (
        "en0706-shown-by-hand",
        r##"let xs: i64[] = [1, 2, 3];
const first = &xs[0];
xs.push(4);
console.log(*first);
"##,
    ),
    (
        "en0706-hold-exclusive",
        r##"let q: i64[] = [1, 2];
for (const x of &q) { *x = 5; q.push(1); }
"##,
    ),
    (
        "en0706-hold-deref-by-hand",
        r##"let q: i64[] = [1, 2];
for (const x of &q) { console.log(*x); q.push(1); }
"##,
    ),
    (
        "en0706-copy-not-clone",
        r##"let xs: Item[] = [new Item(1)];
const first = &xs[0];
xs.push(new Item(2));
console.log(first);

public class Item { public constructor(public v: i64) {} public destructor() { console.log("bye"); } }
"##,
    ),
    (
        "en0706-copy-let-holder",
        r##"let xs: i64[] = [1, 2, 3];
let first = &xs[0];
xs.push(4);
console.log(first);
"##,
    ),
    (
        "en0710-readonly-result",
        r##"public function longest(): readonly &string {
  const s = "owned" + "!";
  return &s;
}
"##,
    ),
    (
        "en0710-parenthesised",
        r##"public function longest(): &string {
  const s = "owned" + "!";
  return &(s);
}
"##,
    ),
    (
        "en0610-value-reads-this",
        r##"public class Person {
  public constructor(public name: string) {}
}
public class Animal {
  public constructor(public name: string) {}
}
public class Dog extends Animal {
  public owner: Person;
  public constructor(name: string, owner: Person) {
    super(name);
    this.owner = this.name.length() > 0 ? owner : owner;
  }
}
"##,
    ),
    (
        "en0610-code-between",
        r##"public class Person {
  public constructor(public name: string) {}
}
public class Animal {
  public constructor(public name: string) {}
}
public class Dog extends Animal {
  public owner: Person;
  public constructor(name: string, owner: Person) {
    super(name);
    console.log("built");
    this.owner = owner;
  }
}
"##,
    ),
    (
        "en0616-by-value",
        r##"let buf: u8[] = [1];
const tbl: u8[] = [0];
public final class Copier { private src: readonly &u8[]; private dst: &u8[]; public constructor(s: &u8[], d: &u8[]) { this.src = s; this.dst = d; } public retarget(s: &u8[]): void { this.src = s; } }
public final class Wrapper { private cp: Copier; public constructor(cp: Copier) { this.cp = cp; } public static relinkBy(let w: Wrapper, s: &u8[]): void { w.cp.retarget(s); } }
"##,
    ),
    (
        "en0616-captured-call",
        r##"function run(f: () => void): void { f(); }
let s = "ab".toString(); let lx = new Lexer(&s); let t = "xy".toString();
run(() => { lx.setSrc(&t); });
public class Lexer { private src: &string; public constructor(src: &string) { this.src = src; } public setSrc(s: &string): void { this.src = s; } }
"##,
    ),
    (
        "en0616-read-set-fields",
        r##"let buf: u8[] = [1];
const tbl: u8[] = [0];
let c = Copier.alias(&tbl, &buf);
const a = c.peek(); c.step(); c.step(); c.step(); c.step(); console.log(*a);
public final class Copier { private src: readonly &u8[]; private dst: &u8[]; public constructor(s: &u8[], d: &u8[]) { this.src = s; this.dst = d; } public static make(s: &u8[], d: &u8[]): Copier { return new Copier(s, d); } public peek(): readonly &u8 { return &this.src[0]; } public step(): void { this.dst.push(1); }
  public static alias(s: &u8[], d: &u8[]): Copier { let w = Copier.make(s, d); const p = w.dst; w.src = p; return w; } }
"##,
    ),
    (
        "en0616-string-part",
        r##"let s = "ab".toString();
let t = "cd".toString();
*longest(&s, &t) += "!";
console.log(s, t);
public function longest(a: &string, b: &string): &string { return a.length() > b.length() ? a : b; }
"##,
    ),
    (
        "en0706-hold-exclusive-method",
        r##"let q: i64[][] = [[1]];
for (const x of &q) { x.push(1); q.push([2]); }
"##,
    ),
    (
        "en0706-loop-source",
        r##"let xs: i64[] = [1, 2];
const fst = xs.first();
for (const x of &xs) { *x = 1; }
console.log(fst);
"##,
    ),
    // The fix-it rewrites the return type, never a parameter's `&string` (A:1314).
    (
        "en0710-reference-parameter",
        r##"console.log(greeting("Ada"));

private function greeting(name: &string): &string {
  const s = `hello, ${name}`;
  return &s;
}
"##,
    ),
    // A:1003's own example: the note names the branch that skips `super`, the
    // `!` of its condition read off (`` when `quiet` is true ``).
    (
        "en0619-negated-branch",
        r##"public class A { public constructor(public name: string) {} }
public class B extends A {
  public constructor(name: string, quiet: bool) {
    if (!quiet) { super(name); }
  }
}
"##,
    ),
    // S:1436: a string's part, and a change that is not a growing one's label.
    (
        "en0706-string-view",
        r##"let line = "hello, wonderful world".toString();
const root = line.slice(5, 14);
line += "!";
console.log(root);
"##,
    ),
    // The write through a narrowed copy is the line the labels name (4D.18).
    (
        "en0708-narrowed-writer",
        r##"let v: i64[] = [1, 2];
let o: &i64[] | null = &v;
const a = o;
const b = o;
if (a != null && b != null) {
  const e = &b[0];
  a.push(3);
  console.log(*e);
}
"##,
    ),
    // The whole local moved after a named construction is the one named (4K.5).
    (
        "en0601-named-construction",
        r##"const ada = new User { name: "Ada" };
const other = ada;
console.log(ada.name);
private class User { public name: string; }
"##,
    ),
    // The help's `&q` would make a moved binding a reference: no edit then.
    (
        "en0601-loop-moved-binding",
        r##"let q = ["a".toString(), "b".toString()];
for (const x of q) { take(x); }
console.log(q.length());
private function take(s: string): void { console.log(s); }
"##,
    ),
    (
        "en0601-destructured-moved-binding",
        r##"const ada = new Person { name: "Ada", age: 36 };
const { name, age } = ada;
keep(name);
console.log(age, ada.name);
private function keep(s: string): void { console.log(s); }
public class Person { public name: string; public age: i64; }
"##,
    ),
    // A second `return` keeps its reference type: the help has no edit.
    (
        "en0710-view-two-returns",
        r##"console.log(head(true, &[1]));
public function head(c: bool, o: &Slice<i64>): &Slice<i64> {
  const xs: i64[] = [1, 2, 3];
  if (c) {
    return o;
  }
  return xs.slice(0, 2);
}
"##,
    ),
];

/// The code a program's name starts with.
fn code_of(name: &str) -> Code {
    let code = name.split('-').next().expect("a code").to_uppercase();
    Code::from_name(&code).unwrap_or_else(|| panic!("{name} names no code"))
}

pub fn register(h: &mut Harness) {
    for &(name, source) in PROGRAMS {
        h.case(format!("wording/{name}"), move || {
            let ran = run("main.en", source);
            let code = code_of(name);
            assert!(
                (ran.diags.iter()).any(|d| d.code == code && d.severity == Severity::Error),
                "{name}: no {code}\n{}",
                ran.text
            );
            golden("pipeline", &format!("wording/{name}.txt"), &ran.text)
        });
        h.case(
            format!("wording/{name}: each fix-it removes its diagnostic and adds no error"),
            move || {
                let ran = run("main.en", source);
                for d in &ran.diags {
                    for help in d.helps.iter().filter(|h| !h.edits.is_empty()) {
                        let fixed = apply_fixes(source, ran.base, &help.edits)
                            .unwrap_or_else(|e| panic!("{name}: {e}"));
                        let after = run("main.en", &fixed);
                        let added = (after.diags.iter())
                            .filter(|x| x.severity == Severity::Error)
                            .any(|x| of_code(&after, x.code) > of_code(&ran, x.code));
                        assert!(
                            of_code(&after, d.code) < of_code(&ran, d.code) && !added,
                            "{name}: `{}` leaves\n{fixed}\n{}",
                            help.message,
                            after.text
                        );
                    }
                }
            },
        );
    }
}
