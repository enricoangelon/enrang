//! The sema suite's cases for SPEC's examples through phase 2 (owner 5A, plan g.1).
//! SPEC 1's tour, `Ownership in three lines` and every M1 near-miss pass `analyze`
//! in process with the embedded library, with no diagnostic at all (plan 0.3, h.3).
//! Then SPEC 4's inline programs that state an outcome, each written out whole as
//! the sentence describes it, accepted or rejected with exactly its code: the
//! closures of S:968, S:977 and S:1812, whose arrows take their parameter types
//! from the call (an integer still being inferred reads through `&` as any number
//! does), the class bounds of S:764, written types inside bodies included, and the
//! overloads of S:829. The areas' own suites hold the rest of plan g.2's lists.

use enrang_sema::LibSource;
use enrang_testkit::{Harness, extract_cases, fixture_header, workspace_root};

/// SPEC's inline programs: where SPEC says it, what it shows, the program, and the
/// codes it reports (none for an accepted program).
const INLINE: &[(&str, &str, &str, &[&str])] = &[
    (
        "S:968",
        "an arrow stored in a local, passed to `map`, and one changing a variable it uses",
        "const xs = [1, 2, 3];
const double = (x: &i64) => x * 2;
console.log(xs.map(double));
let count = 0;
const inc = () => { count += 1; };
inc();
inc();
console.log(count);
",
        &[],
    ),
    (
        "S:968",
        "an arrow that uses an outer variable can't be stored in a field",
        "let count = 0;
const b = new Button { on: () => console.log(count) };

public final class Button {
  public on: fn() => void;
}
",
        &["EN1007"],
    ),
    (
        "S:968",
        "an arrow that uses none is an `fn` value; an optional callback narrowed before its call",
        "const b = new Button { on: () => console.log(\"hi\") };
onKey((k: u8) => console.log(k));
onKey();

public final class Button {
  public on: fn() => void;
}

public function onKey(handler?: (k: u8) => void): void {
  if (handler != null) {
    handler(1);
  }
}
",
        &[],
    ),
    (
        "S:977",
        "`users.map(u => u)` makes `U` a reference",
        "const users = [new User(\"Ada\"), new User(\"Bo\")];
const same = users.map(u => u);

public class User {
  public constructor(public name: string) {}
}
",
        &["EN0703"],
    ),
    (
        "S:1812",
        "`xs.map(x => x * 2)` over an array whose integer type is still being inferred",
        "const xs = [1, 2, 3];
console.log(xs.map(x => x * 2));
const squares = xs.map(x => x * x);
console.log(squares);
const big = xs.find(x => x > 2);
if (big != null) { console.log(big); }
let sum = 0;
xs.forEach(x => { sum += x; });
console.log(xs.map(x => -x), sum);
",
        &[],
    ),
    (
        "S:1812",
        "the same over an array whose float type is still being inferred (review 5A, mutant O1)",
        "const ys = [1.5, 2.5];
console.log(ys.map(y => y * y));
const big = ys.find(y => y > 2.0);
console.log(big);
let total = 0.0;
ys.forEach(y => { total += y; });
console.log(ys.map(y => -y), total);
",
        &[],
    ),
    (
        "S:764",
        "`oldest(&dogs).fetch()` through a class bound",
        "const dogs = [new Dog(\"Rex\", 3), new Dog(\"Fido\", 7)];
console.log(oldest(&dogs).fetch());

public class Animal {
  public constructor(public name: string, public age: i64) {}
}

public class Dog extends Animal {
  public fetch(): string { return `${this.name} fetches`; }
}

public function oldest<T extends Animal>(xs: &Slice<T>): &T {
  let best = &xs[0];
  for (const x of xs) {
    if (x.age > best.age) {
      best = x;
    }
  }
  return best;
}
",
        &[],
    ),
    (
        "S:764",
        "the same function over `&Slice<Animal>` makes `.fetch()` EN0303",
        "const dogs: Animal[] = [new Animal(\"Rex\", 3), new Animal(\"Fido\", 7)];
console.log(oldest(&dogs).fetch());

public class Animal {
  public constructor(public name: string, public age: i64) {}
}

public function oldest(xs: &Slice<Animal>): &Animal {
  return &xs[0];
}
",
        &["EN0303"],
    ),
    (
        "S:764",
        "any other type argument of a class bound is EN0419, in a body's written type too",
        "const pen: Pen<i64> | null = null;
const size = sizeOf<Pen<bool>>();
const take = (p: Pen<u8> | null): void => {};

public class Animal {}

public class Pen<T extends Animal> {
  public constructor(public x: T) {}
}
",
        &["EN0419", "EN0419", "EN0419"],
    ),
    (
        "S:764",
        "a written type in a body may rely on a bound its method's `where` adds (review 5A, mutant G2)",
        "public class Animal {}
public class Pen<T extends Animal> {}
public class Holder<T> {
  public constructor(public x: T) {}
  public pen(): void where T extends Animal {
    const p: Pen<T> | null = null;
    console.log(p == null);
  }
}
",
        &[],
    ),
    (
        "S:764",
        "a construction's written type argument gets one EN0419, the construction's",
        "const pen = new Pen<i64>(5);
const named = Box2.Box2<string> { x: \"s\" };

public class Animal {}

public class Pen<T extends Animal> {
  public constructor(public x: T) {}
}

public enum Box2<T extends Animal> {
  Box2 { x: T },
}
",
        &["EN0419", "EN0419"],
    ),
    (
        "S:829",
        "`describe(42)` and `describe(\"hi\")` pick their overloads; an expected type picks one",
        "console.log(describe(42), describe(\"hi\"));
const g: fn(n: int) => string = describe;
console.log(g(1));

public function describe(n: int): string { return `number ${n}`; }
public function describe(s: &string): string { return `text ${s}`; }
",
        &[],
    ),
    (
        "S:829",
        "the bare name of an overloaded function needs an expected type",
        "const f = describe;

public function describe(n: int): string { return `number ${n}`; }
public function describe(s: &string): string { return `text ${s}`; }
",
        &["EN0410"],
    ),
];

use crate::support::{run_entry, run_with};

pub fn register(h: &mut Harness) {
    for &(at, what, source, codes) in INLINE {
        h.case(format!("spec_examples/{at}: {what}"), move || {
            for target in ["x86_64-linux", "i386-linux"] {
                let r = run_with(&[("m.en", source)], LibSource::Embedded, target);
                assert_eq!(r.codes(), codes, "{at} on {target}:\n{}", r.rendered());
            }
        });
    }
    h.case(
        "spec_examples/plan h.3: the tour and `Ownership in three lines` analyze clean on both widths",
        || {
            let spec =
                std::fs::read_to_string(workspace_root().join("docs/SPEC.md")).expect("SPEC");
            let mut seen = 0;
            for c in extract_cases(&spec).expect("cases") {
                if c.id != "tour" && c.id != "ownership" {
                    continue;
                }
                let files: Vec<(&str, &str)> = c
                    .files
                    .iter()
                    .map(|f| (f.name.as_str(), f.contents.as_str()))
                    .collect();
                for target in ["x86_64-linux", "i386-linux"] {
                    let r = run_with(&files, LibSource::Embedded, target);
                    assert!(r.diags.is_empty(), "{} on {target}: {}", c.id, r.rendered());
                    assert!(r.program.is_some(), "{} on {target}", c.id);
                }
                seen += 1;
            }
            assert_eq!(seen, 2);
        },
    );
    h.case(
        "spec_examples/plan h.3: every M1 near-miss analyzes clean (plan 0.3)",
        || {
            let root = workspace_root().join("tests/compile");
            let mut files = Vec::new();
            for dir in std::fs::read_dir(&root).expect("tests/compile") {
                let dir = dir.expect("an entry").path();
                for f in std::fs::read_dir(&dir).expect("a code's directory") {
                    let f = f.expect("an entry").path();
                    if f.to_string_lossy().ends_with(".pass.en") {
                        files.push(f);
                    }
                }
            }
            files.sort();
            // Every near-miss of every code's directory (fix-5: 305 when written), so a
            // runner that skips a family of directories trips.
            assert!(files.len() >= 305, "{}", files.len());
            let mut bad = Vec::new();
            for f in &files {
                let text = std::fs::read_to_string(f).expect("a near-miss");
                let name = f
                    .file_name()
                    .expect("a name")
                    .to_string_lossy()
                    .into_owned();
                // A near-miss runs as `enrang check` runs it: for the target its first
                // line names, `//! target: <name>`, as the CLI fixture runner and the meta
                // gate run it, and beside the other near-misses of its directory, so an
                // import of a sibling module resolves (the fixtures of EN0304, EN0305,
                // EN0311, EN0312 and the attack rows import their own helpers).
                let header =
                    fixture_header(&text).unwrap_or_else(|why| panic!("{} {why}", f.display()));
                let target = header
                    .target
                    .clone()
                    .unwrap_or_else(|| "x86_64-linux".to_owned());
                let mut sources = vec![(name, text)];
                let mut siblings: Vec<_> = std::fs::read_dir(f.parent().expect("a directory"))
                    .expect("a code's directory")
                    .map(|entry| entry.expect("an entry").path())
                    .filter(|p| p != f && p.to_string_lossy().ends_with(".pass.en"))
                    .collect();
                siblings.sort();
                for p in siblings {
                    let text = std::fs::read_to_string(&p).expect("a near-miss");
                    let name = p.file_name().expect("a name").to_string_lossy();
                    sources.push((name.into_owned(), text));
                }
                let sources: Vec<(&str, &str)> = sources
                    .iter()
                    .map(|(name, text)| (name.as_str(), text.as_str()))
                    .collect();
                // `//! library` loads it as a library module (G50).
                let r = run_entry(&sources, LibSource::Embedded, &target, header.library);
                if !r.diags.is_empty() || r.program.is_none() {
                    bad.push(format!("{}: {}", f.display(), r.rendered()));
                }
            }
            assert!(bad.is_empty(), "{}", bad.join("\n"));
        },
    );
}
