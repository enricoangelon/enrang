//! Determinism (M3 plan f.1, stage 4M; ARCHITECTURE 1): `check` of the same
//! program twice, each time in a fresh session, gives the same bytes: the
//! diagnostics as text and as JSON, and for a program that passes, its elaborated
//! MIR and its contracts as `--emit=mir` and `--emit=summary` print them. Every
//! input of `no_panic` runs so, group by group.
//!
//! The summary goldens of the pipeline suite live here too (plan f.1 names them
//! `tests/golden/pipeline/summary/<name>.txt`): each is `--emit=summary` of a
//! program whose contract one rule of SPEC 5.3 and 5.4 decides, and each run of
//! it twice gives the golden.

use enrang_diag::RenderOpts;
use enrang_driver::{CheckError, Emit, emit};
use enrang_testkit::{Harness, golden, scale};

use crate::no_panic::{Input, Text, check_input, groups, runnable};

/// What one run of `check` printed: the text and JSON reports, then, for a program
/// that passed, its MIR and its summary.
fn run_once(input: &Input) -> Vec<String> {
    let (mut session, checked) = check_input(input);
    let mut out = Vec::new();
    match checked {
        Ok(checked) => {
            let mir = emit(&checked, Emit::Mir).unwrap_or_else(|e| e.0);
            let summary = emit(&checked, Emit::Summary).unwrap_or_else(|e| e.0);
            drop(checked);
            // Warnings render, as JSON too.
            let diags = session.dcx.take();
            out.push(enrang_diag::render_text(
                &diags,
                &session.map,
                &RenderOpts::default(),
            ));
            out.push(enrang_diag::render_json(&diags, &session.map));
            out.push(mir);
            out.push(summary);
        }
        Err(CheckError::Internal(internal)) => out.push(format!("internal: {}", internal.0)),
        Err(_) => {
            let diags = session.dcx.take();
            out.push(enrang_diag::render_text(
                &diags,
                &session.map,
                &RenderOpts::default(),
            ));
            out.push(enrang_diag::render_json(&diags, &session.map));
        }
    }
    out
}

/// The first part two runs of an input disagree on, if any.
fn difference(input: &Input) -> Option<String> {
    let (first, second) = (run_once(input), run_once(input));
    let parts = ["text report", "JSON report", "MIR", "summary"];
    for (at, (a, b)) in first.iter().zip(&second).enumerate() {
        if a != b {
            return Some(format!("{}: the {} differs", input.name, parts[at]));
        }
    }
    (first.len() != second.len()).then(|| format!("{}: one run passed", input.name))
}

/// The inputs of a group that run twice: at scale 1, every fourth of the
/// fixtures, the first included, and every other input; from scale 4 on, all of
/// them. Two runs cost two checks, beside the one each of `no_panic` and
/// `verify_all` makes of every input, and the suite keeps to TESTING 22's
/// budget.
fn sample(inputs: Vec<&Input>) -> Vec<&Input> {
    let stride = usize::try_from(4 / scale().max(1)).unwrap_or(1).max(1);
    inputs
        .into_iter()
        .enumerate()
        .filter(|(at, input)| !input.name.starts_with("tests/compile/") || at % stride == 0)
        .map(|(_, input)| input)
        .collect()
}

/// The summary goldens: a name and a program.
const SUMMARIES: &[(&str, &str)] = &[
    (
        "sources_one_parameter",
        // SPEC 5.4: `first` returns `&xs[0]`, so only `names` stays borrowed.
        "let names: string[] = [\"ada\".toString()];
let label = \"x\".toString();
const f = first(&names, &label);
label = \"people\".toString();
console.log(f, label);

public function first(xs: &Slice<string>, label: &string): &string {
  console.log(`reading ${label}`);
  return &xs[0];
}
",
    ),
    (
        "readonly_result",
        // SPEC 5.4: `readonly` before the return type keeps callers from writing.
        "let c = new Counter();
console.log(*c.count());

public class Counter {
  private n: isize = 0;
  public count(): readonly &isize { return &this.n; }
}
",
    ),
    (
        "stored_source",
        // SPEC 5.4 (N6): a result from a parameter the function also stores is
        // read-only (`keep` also keeps a reference from `x` in `this`), in a class
        // that only reads through its reference field.
        "let data: i64[] = [1, 2];
let other: i64[] = [3];
let v = new View(&data);
const r = v.keep(&other);
console.log(*r, v.first());

public final class View {
  private xs: &i64[];
  public constructor(xs: &i64[]) { this.xs = xs; }
  public keep(x: &i64[]): &i64 { this.xs = x; return &x[0]; }
  public first(): i64 { return this.xs[0]; }
}
",
    ),
    (
        "tuple_parts",
        // SPEC 5.4 (N6): two parts from different parameters stay writable; two
        // parts that may point at the same data fall to read-only.
        "let a: i64[] = [1];
let b: i64[] = [2];
const p = two(&a, &b);
p[0].push(3);
console.log(same(&a));

public function two(a: &i64[], b: &i64[]): [&i64[], &i64[]] { return [a, b]; }

public function same(a: &i64[]): [&i64[], &i64[]] { return [a, a]; }
",
    ),
    (
        "let_parameter",
        // SPEC 5.3: a `let` reference parameter is Write even if the body only
        // reads it; a parameter the body writes through is Write too.
        "let xs: i64[] = [1];
peek(&xs);
grow(&xs);
console.log(xs);

public function peek(let xs: &i64[]): void { console.log(xs.length()); }

public function grow(xs: &i64[]): void { xs.push(2); }
",
    ),
    (
        "override_contracts",
        // SPEC 5.4: an override may return into `this` where its base body does
        // not; each body states its own sources, and a call through the method
        // table, as `a.label()` here, widens the base body's with `this`.
        "let d = new Dog();
show(&d);

public function show(a: &Animal): void { console.log(a.label()); }

public class Animal {
  public label(): &string { return \"animal\"; }
}

public class Dog extends Animal {
  private name: string = \"Rex\";
  public override label(): &string { return &this.name; }
}
",
    ),
];

/// `--emit=summary` of a program.
fn summary_of(name: &str, source: &str) -> String {
    let input = Input {
        name: format!("summary/{name}"),
        text: Text::Memory(source.to_owned()),
        target: None,
        library: false,
        broken: None,
    };
    let (mut session, checked) = check_input(&input);
    match checked {
        Ok(checked) => emit(&checked, Emit::Summary).expect("a summary"),
        Err(e) => panic!("{name}: {e:?}\n{}", session.render(&RenderOpts::default())),
    }
}

pub fn register(h: &mut Harness) {
    for (group, inputs) in groups() {
        h.case(
            format!("determinism/{group}: two runs of check print the same bytes"),
            move || {
                let failures: Vec<String> = sample(runnable(&inputs).collect())
                    .into_iter()
                    .filter_map(difference)
                    .collect();
                assert!(failures.is_empty(), "\n{}", failures.join("\n"));
            },
        );
    }
    for &(name, source) in SUMMARIES {
        h.case(
            format!("determinism/summary {name}: twice the golden"),
            move || {
                let first = summary_of(name, source);
                assert_eq!(summary_of(name, source), first, "a second run differs");
                golden("pipeline", &format!("summary/{name}.txt"), &first)
            },
        );
    }
    h.case("determinism/a run that differs is found", || {
        let input = Input {
            name: "main.en".to_owned(),
            text: Text::Memory("console.log(1);\n".to_owned()),
            target: None,
            library: false,
            broken: None,
        };
        assert_eq!(difference(&input), None);
        assert_eq!(
            run_once(&input).len(),
            4,
            "a program that passes prints all four"
        );
        let broken = Input {
            text: Text::Memory("const x = 1\n".to_owned()),
            ..input
        };
        let report = run_once(&broken);
        assert_eq!(report.len(), 2);
        assert!(report[0].contains("error[EN0101]"), "{report:?}");
    });
}
