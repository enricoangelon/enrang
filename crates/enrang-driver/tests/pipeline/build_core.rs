//! Stage 2B's pipeline tests of the core constructs (M3 plan c.1-c.10): programs
//! checked through phases 1 and 2, every user body built by mirbuild and verified,
//! the printed MIR compared with `tests/golden/pipeline/mir/core/<name>.mir`; and
//! verifier-clean runs, with stage 2C's constructs, over the M2 corpus
//! (`tests/compile/*/*.pass.en`) and SPEC's single-file cases.

use std::path::Path;
use std::sync::Arc;

use enrang_diag::RenderOpts;
use enrang_driver::{Session, Typed, check_types};
use enrang_mir::{Bodies, Body, VerifyError, print_module, verify};
use enrang_target::{TargetOpts, host_target, resolve};
use enrang_testkit::{Harness, TempDir, extract_cases, golden, workspace_root};

/// The suite directory of these goldens, under `tests/golden/pipeline/`.
const DIR: &str = "mir/core";

/// Phases 1 and 2 of `source` as `main.en`, or the rendered diagnostics.
fn checked(source: &str) -> Result<Typed, String> {
    let dir = TempDir::new("pipeline");
    dir.write("main.en", source);
    let mut session = Session::new();
    let target = Arc::new(
        resolve(host_target(), &TargetOpts::default())
            .expect("a target")
            .0,
    );
    check_types(&mut session, dir.path(), Path::new("main.en"), target)
        .map_err(|e| format!("{e:?}\n{}", session.render(&RenderOpts::default())))
}

/// Every user body of a checked program, built, printed, and the verifier's errors.
fn build(c: &Typed) -> (String, Vec<VerifyError>) {
    let (tcx, program) = (&c.tcx, &c.program);
    let mut dcx = enrang_diag::DiagCtx::new();
    let mut bodies = Bodies::new();
    for &m in program.modules.iter().filter(|&&m| !tcx.module(m).library) {
        bodies.extend(enrang_mirbuild::build_program(tcx, program, m, &mut dcx));
    }
    let list: Vec<Body> = bodies.values().cloned().collect();
    let errors = bodies
        .values()
        .flat_map(|b| {
            let run = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| verify(tcx, b)));
            run.unwrap_or_else(|_| {
                Err(vec![VerifyError {
                    rule: enrang_mir::Rule::Types,
                    at: None,
                    message: "the verifier panicked".to_owned(),
                }])
            })
            .err()
            .unwrap_or_default()
        })
        .collect();
    (print_module(tcx, &list), errors)
}

/// `source`'s MIR; panics when phases 1-2 reject it or a body fails the verifier.
pub fn built(source: &str) -> String {
    let c = checked(source).unwrap_or_else(|e| panic!("{e}"));
    let (text, errors) = build(&c);
    assert!(errors.is_empty(), "{errors:#?}\n{text}");
    text
}

/// The corpus programs mirbuild cannot build yet, each with the reason: a fix
/// makes the corpus case fail until the entry is removed.
const KNOWN_GAPS: &[(&str, &str)] = &[];

/// Builds and verifies `source` when it checks: `None` when phases 1-2 reject
/// it, the errors otherwise.
fn corpus_run(source: &str) -> Option<Result<Vec<VerifyError>, String>> {
    let c = checked(source).ok()?;
    let run = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| build(&c).1));
    Some(run.map_err(|p| {
        p.downcast_ref::<String>()
            .cloned()
            .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
            .unwrap_or_default()
    }))
}

/// One golden: `name`'s program, its MIR compared byte for byte.
fn case(h: &mut Harness, name: &'static str, source: &'static str) {
    h.case(format!("build_core/{name}"), move || {
        let text = built(source);
        golden("pipeline", &format!("{DIR}/{name}.mir"), &text)
    });
}

pub fn register(h: &mut Harness) {
    for &(name, source) in GOLDENS {
        case(h, name, source);
    }
    h.case("build_core/the M2 corpus builds verifier-clean", || {
        let root = workspace_root().join("tests/compile");
        let mut files: Vec<_> = std::fs::read_dir(&root)
            .expect("tests/compile")
            .flatten()
            .flat_map(|d| std::fs::read_dir(d.path()).into_iter().flatten().flatten())
            .map(|e| e.path())
            .filter(|p| p.to_string_lossy().ends_with(".pass.en"))
            .collect();
        files.sort();
        let (mut ran, mut failed) = (0, Vec::new());
        for f in files {
            let source = std::fs::read_to_string(&f).expect("a fixture");
            // A fixture for another target or loaded as a library is checked
            // differently; a `covers` or `row` header changes nothing.
            if source
                .lines()
                .any(|l| l.starts_with("//! target:") || l.starts_with("//! library"))
            {
                continue;
            }
            let name = f.to_string_lossy().replace('\\', "/");
            let known = KNOWN_GAPS.iter().any(|(k, _)| name.ends_with(k));
            match (corpus_run(&source), known) {
                (Some(Ok(errors)), false) if errors.is_empty() => ran += 1,
                (Some(Ok(errors)), true) if errors.is_empty() => {
                    failed.push(format!("{name}: builds now, remove it from KNOWN_GAPS"))
                }
                (Some(_), true) => {}
                (Some(outcome), false) => failed.push(format!("{name}: {outcome:?}")),
                (None, _) => {}
            }
        }
        assert!(
            failed.is_empty(),
            "{} failed:\n{}",
            failed.len(),
            failed.join("\n")
        );
        assert!(ran >= 260, "only {ran} corpus programs built");
    });
    h.case("build_core/SPEC's cases build verifier-clean", || {
        let spec = std::fs::read_to_string(workspace_root().join("docs/SPEC.md")).expect("SPEC");
        let cases = extract_cases(&spec).unwrap_or_else(|e| panic!("{e}"));
        let (mut ran, mut failed) = (0, Vec::new());
        for c in cases.iter().filter(|c| c.exit == 0 && c.files.len() == 1) {
            match corpus_run(&c.files[0].contents) {
                Some(Ok(errors)) if errors.is_empty() => ran += 1,
                Some(outcome) => failed.push(format!("{}: {outcome:?}", c.id)),
                None => {}
            }
        }
        assert!(failed.is_empty(), "{}", failed.join("\n"));
        assert!(ran >= 9, "only {ran} SPEC cases built");
    });
}

/// The golden programs, one per construct group of plan c.1-c.10.
const GOLDENS: &[(&str, &str)] = &[
    // c.1: locals, arguments, a local function's hidden arguments, `#supplied`, a `WholeBody` region
    (
        "bodies",
        r#"let total: i64 = 0;
const words: string[] = ["a", "b"];
const first = &words[0];
function add(n: i64): void { total += n; }
function show(): void { console.log(first, total); }
add(2);
show();
console.log(scale(3), scale(3, 4));

public function scale(x: i64, by: i64 = 2): i64 {
  return x * by;
}
public unsafe function peek(p: *u8): u8 {
  return *p;
}
public class Cell {
  public v: i64;
  public constructor(v: i64) { this.v = v; }
  public get(): i64 { return this.v; }
}
"#,
    ),
    // c.2: O6, the receiver's borrow after the arguments, an assignment's target first, a compound target
    (
        "order",
        r#"let xs: i64[] = [1, 2];
let i: isize = 0;
xs.push(xs.length() as i64);
xs[i] = i as i64;
let k: i64 = 1;
console.log(pair(k, k = 5));
let s = "ab";
s += s.length().toString();
xs[1] += k;

public function pair(a: i64, b: i64): i64 {
  return a - b;
}
"#,
    ),
    // c.3: scheduled drops at fall-through, `return`, `break`, `continue`; parameters last
    (
        "scopes",
        r#"public function f(n: i64, label: string): string {
  let out = "x";
  {
    const inner = "y";
    if (n > 0) {
      return inner;
    }
  }
  while (n > 2) {
    const t = "loop";
    if (n == 3) {
      break;
    }
    if (n == 4) {
      continue;
    }
    out = t;
  }
  return out;
}
"#,
    ),
    // c.4: fields, indexes with their guard runs, a fixed array's constant index, a narrowed payload, a raw deref, a class copy out
    (
        "places",
        r#"public class Pair {
  public a: i64 = 0;
  public b: i64[] = [];
}
public class Pt implements Copy {
  public x: i64 = 0;
}
public function places(p: &Pair, xs: &i64[], grid: i64[][], fixed: i64[3], o: i64 | null, raw: *i64): i64 {
  let t = p.a + xs[1] + grid[0][1] + fixed[2] + p.b[0];
  if (o != null) {
    t += o;
  }
  if (o == null) {
    return t;
  }
  t += o;
  unsafe {
    t += *raw;
  }
  return t;
}
public function copyOut(r: &Pt): Pt {
  return *r;
}
"#,
    ),
    // c.5: constants, operators, comparisons, logical operators, ternaries, literals, casts, templates
    (
        "exprs",
        r#"const a: i64 = 7;
const b = -a;
const c = !(a > 3);
const d = a / 2 + a % 3 - (a << 1);
const e = a & 3 | 4 ^ 1;
const f = 1.5 * 2.0 / 3.0;
const g = a > 2 && b < 0 || c;
const h = a > 5 ? "big" : "small";
const s = h + "!";
const same = s == "big!";
const fx: i64[3] = [1, 2, 3];
const rep: i64[4] = [0; 4];
const tup: [i64, string] = [1, "x"];
const obj = { x: 1, y: true };
const col = Color.Green;
const casted = a as f64;
const tpl = `${a}-${s}`;
const w: u8 = 3;
const mixed = w < a;
const n: i64 | null = null;
const isNull = n == null;

public enum Color { Red, Green }
"#,
    ),
    // c.6: every adjust step but the spread's reborrow
    (
        "adjust",
        r#"const d = new Dog {};
take(&d);
const xs: i64[] = [1, 2];
console.log(total(&xs));
const fx: i64[2] = [3, 4];
console.log(total(&fx));
const n: i64 | null = 5;
const lit: &string = "hi";
const r: &i64 = &xs[0];
const v: i64 = r;
const named: &Named = &d;
const boxed: Box<Named> = new Box<Dog>(new Dog {});
const op: &i64 | null = r;
const copied: i64 | null = op;
const f: fn(x: i64) => i64 = twice;
console.log(n, lit, v, named.label(), boxed.label(), copied, f(1));

public interface Named {
  label(): string;
}
public class Animal {
  public name: string = "a";
}
public class Dog extends Animal implements Named {
  public label(): string { return "dog"; }
}
public function take(a: &Animal): void {
  console.log(a.name);
}
public function total(s: &Slice<i64>): isize {
  return s.length();
}
public function twice(x: i64): i64 {
  return x * 2;
}
"#,
    ),
    // c.7: direct, virtual, `super`, `fn` values, forms, intrinsics, `never`
    (
        "calls",
        r#"const k = new Kid {};
call(&k, new Kid {}, twice);
let s = "bye";
dispose(s);
let t = "gone";
mem.forget(t);
const size = sizeOf<i64>();
console.error("size", size);
assert(size > 0);

public class Base {
  public greet(): string { return "b"; }
}
public class Kid extends Base {
  public override greet(): string { return super.greet() + "k"; }
}
public final class Solo {
  public v: i64 = 1;
  public get(): i64 { return this.v; }
}
public function call(b: &Base, k: Kid, f: fn(x: i64) => i64): i64 {
  console.log(b.greet(), k.greet());
  const s = new Solo {};
  const n = s.get() + f(2);
  if (n > 10) {
    panic("big");
  }
  return n;
}
public function twice(x: i64): i64 {
  return x * 2;
}
"#,
    ),
    // c.8: D3, compound and append, `++`/`--`, assignment values and EN0621's record, repointing
    (
        "assign",
        r#"let n: i64 = 1;
let m: i64 = 0;
m = n = 4;
const pre = ++n;
const post = n--;
let s = "a";
s = "b";
s += "c";
console.log(s += "!");
const kept = (s = "d");
let h = new Holder();
const r = &h;
*r = new Holder();
let q = &n;
q = &m;
h.items[0] += 2;
console.log(m, pre, post, kept, q);

public class Holder {
  public items: i64[] = [1];
}
"#,
    ),
    // c.9: defaults, loops, `break`, `continue`, `unsafe`
    (
        "stmts",
        r#"let count: i64;
let flag: bool;
let text: string;
let list: i64[];
let maybe: i64 | null;
let ptr: *u8;
let pair: [i64, bool];
for (let i: i64 = 0; i < 3; i += 1) {
  if (i == 1) {
    continue;
  }
  count += i;
}
let j: i64 = 0;
do {
  j += 1;
} while (j < 2);
while (true) {
  if (count > 5) {
    break;
  } else {
    count += 2;
  }
}
unsafe {
  ptr = ptr;
}
console.log(count, flag, text, list, maybe, pair);
"#,
    ),
    // c.10: `new`, named forms, the prologue, `overridden`, `super(...)`, implicit constructors, `MoveThis`
    (
        "construct",
        r#"const a = new Animal("Rex");
const d = new Dog("Fido", 3);
const p = new Point { x: 1 };
const c = new Counter();
const l = new Leaf(2);
console.log(a.into().name, d, p, c, l);

public class Animal {
  public name: string;
  public sound: string = "...";
  public legs: i64 = 4;
  public constructor(name: string, public loud: bool = false) {
    this.name = name;
  }
  public move into(): Animal { return this; }
}
public class Dog extends Animal {
  public override sound: string = "woof";
  public age: i64;
  public constructor(name: string, age: i64) {
    this.age = age;
    super(name);
  }
}
public class Point {
  public x: i64;
  public y: i64 = 7;
}
public class Counter {
  public count: i64 = 0;
}
public class Shape {
  public tag: string = "shape";
}
public class Circle extends Shape {
  public r: i64;
  public constructor(r: i64) { super(); this.r = r; }
}
public final class Leaf {
  public v: i64;
  public w: i64 = 1;
  public constructor(v: i64) { this.v = v; }
}
"#,
    ),
    // c.20 at the core constructs: the records of a call argument, a binding, a
    // receiver and a hidden argument, a narrowed use, a fact's test
    (
        "records",
        r#"let count = 0;
let h = new Holder();
function bump(): void { count += 1; console.log(h); }
if (h.v != null) {
  peek(&h);
  const r = &h;
  h.show();
  bump();
  console.log(h.v + 1);
}

public class Holder {
  public v: i64 | null = 3;
  public show(): void { console.log(this.v); }
}
public function peek(h: &Holder): void { console.log(h.v); }
"#,
    ),
    // c.4's class checks on the object of `clone` and `unbox`, a narrowed left
    // operand of `&&`, a default built apart from its parameter, `args`
    (
        "checks",
        r#"const b: Box<Animal> = new Box<Animal>(new Animal());
const r = &b;
const c = r.clone();
const a = b.unbox();
const x: i64 | null = 3;
if (x != null && x > 2) {
  console.log(x);
}
console.log(make(), args.length());

public class Animal implements Clone {
  public n: i64 = 1;
  public clone(): Animal { return new Animal(); }
}
public function make(c: Animal = new Animal()): i64 {
  const d = c.clone();
  return d.n;
}
"#,
    ),
    // c.10, S:829: `x?: T` is `x: T | null = null`, its prologue explicit, as a
    // written default's is (A:937), for a function, a closure parameter and a
    // parameter property
    (
        "optional_params",
        r#"h();
onKey(65);
const o = new Opt("a");
console.log(o.width ?? 8);

private function h(s?: string): void {}

private function onKey(key: u8, handler?: (k: u8) => void): void {
  if (handler != null) { handler(key); }
}

private class Opt {
  public constructor(public name: string, public width?: i64) {}
}
"#,
    ),
    // O6: an object literal's and a case literal's values as written, the
    // aggregate in shape order; a `move` receiver before the arguments; a template
    // beside other arguments of `console.log`, its parts counted (A:976)
    (
        "eval_order",
        r#"const o = { b: f("b"), a: f("a") };
const r = Shape.Rect { h: f("h"), w: f("w") };
let c = new C { n: 1 };
c.show(bump(&c));
const x: i64 = 1;
console.log(`${x}`, o.a, `z`);
console.log(`${x}${x}z`, r);

private enum Shape { Rect { w: string, h: string } }

private class C implements Copy {
  public n: i64;
  public move show(x: i64): void { console.log(this.n, x); }
}

private function bump(c: &C): i64 { c.n = 2; return 0; }
private function f(s: string): string { console.log(s); return s; }
"#,
    ),
];
