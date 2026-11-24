//! Drop traces (M3 plan f.8, stage 4M; TESTING 23's M3 item "drop-trace fixtures
//! for the D2 temporary table and for partly moved `T | null`, `Result` and a user
//! enum"). No VM runs before M4, so a trace is the elaborated MIR of one function,
//! as `check --emit=mir` prints it, a golden under `tests/golden/pipeline/drops/`:
//! where each temporary's `drop_glue` and `storage_dead` stand is where it ends.
//!
//! One program per boundary of SPEC 5.7's D2 table of temporaries (the condition of
//! `if`, `while`, `do...while`, `for` and a ternary; the step of a `for`; the right
//! operand of `&&` and of `||`; the subject of `match` and the source of
//! `for...of`; a `let` initialiser, an expression statement, an assignment and a
//! `return`), each with a `string` temporary that the boundary ends, and the three
//! partly moved values of ARCHITECTURE 5.4's elaboration table: A:605's `f(o:
//! string | null, c: bool)`, a `Result` and a user enum case, each of whose drops
//! switches on the tag before the ladder of the active case's fields.
//!
//! Each golden was read against its row before it was kept. A program whose
//! temporaries nest, `show(&mk(&("a" + "b")))` and a `for...of` source over
//! `&words(&("c" + "d"))`, pins D2's "reverse creation order": `mk`'s result, declared
//! before the temporaries of its argument but created after them, ends first, and
//! every trace's temporaries end in the reverse order of their first assignment.

use std::collections::BTreeMap;

use enrang_driver::{Emit, emit};
use enrang_testkit::{Harness, golden};

use crate::no_panic::{Input, check_input};

/// Helpers the D2 programs share.
const HELPERS: &str = "
private function ok(s: &string): bool {
  return s.length() > 0;
}

private function len(s: &string): i64 {
  return s.length() as i64;
}

private function show(s: &string): void {
  console.log(s);
}

private function words(n: i64): string[] {
  return [n.toString()];
}
";

/// The D2 boundaries: the golden's name and the statements of `demo`'s body that
/// hold the temporary, between `let n = 0;` and `return n;`.
const D2: &[(&str, &str)] = &[
    (
        "if_condition",
        "  if (ok(&(\"a\" + \"b\"))) {\n    n += 1;\n  }\n",
    ),
    (
        "while_condition",
        "  while (ok(&(\"a\" + \"b\")) && n < 3) {\n    n += 1;\n  }\n",
    ),
    (
        "do_while_condition",
        "  do {\n    n += 1;\n  } while (ok(&(\"a\" + \"b\")) && n < 3);\n",
    ),
    (
        "for_condition",
        "  for (let i = 0; ok(&(\"a\" + \"b\")) && i < 3; i += 1) {\n    n += i;\n  }\n",
    ),
    ("ternary_condition", "  n = ok(&(\"a\" + \"b\")) ? 1 : 2;\n"),
    (
        "for_step",
        "  for (let i = 0; i < 3; i += len(&(\"a\" + \"b\"))) {\n    n += 1;\n  }\n",
    ),
    (
        "and_right_operand",
        "  const both = n == 0 && ok(&(\"a\" + \"b\"));\n  if (both) {\n    n = 1;\n  }\n",
    ),
    (
        "or_right_operand",
        "  const either = n > 0 || ok(&(\"a\" + \"b\"));\n  if (either) {\n    n = 1;\n  }\n",
    ),
    (
        "match_subject",
        "  match (len(&(\"a\" + \"b\"))) {\n    2 => { n = 1; },\n    default => { n = 2; },\n  }\n",
    ),
    (
        "for_of_source",
        "  for (const w of &words(7)) {\n    n += len(w);\n  }\n",
    ),
    (
        "let_initialiser",
        "  const k = len(&(\"a\" + \"b\"));\n  n = k;\n",
    ),
    ("expression_statement", "  show(&(\"a\" + \"b\"));\n"),
    ("assignment", "  n = len(&(\"a\" + \"b\"));\n"),
];

/// A D2 program: `demo` runs `body` between `let n = 0;` and `return n;`.
fn d2_program(body: &str) -> String {
    format!(
        "console.log(demo());\n\npublic function demo(): i64 {{\n  let n = 0;\n{body}  return n;\n}}\n{HELPERS}"
    )
}

/// The `return` row: the temporary is in the returned expression.
fn return_program() -> String {
    format!(
        "console.log(demo());\n\npublic function demo(): i64 {{\n  return len(&(\"a\" + \"b\"));\n}}\n{HELPERS}"
    )
}

/// A:605: `f(null, true)` is safe because the drop of `o` switches on its tag.
const NULLABLE: &str = "f(null, true);

public function f(o: string | null, c: bool): void {
  if (o != null && c) {
    take(o);
  }
}

private function take(s: string): void {
  console.log(s);
}
";

/// A partly moved `Result`: the `Ok` arm may move the value out.
const RESULT: &str = "f(Ok(\"a\".toString()), true);

public function f(r: Result<string, Shape>, c: bool): void {
  match (r) {
    Ok => { if (c) { take(r.value); } },
    Err => {},
  }
}

private function take(s: string): void {
  console.log(s);
}

public enum Shape {
  Circle { label: string },
  Empty,
}
";

/// A partly moved user enum case: `label` may be moved out, `tag` never is, and
/// the case's fields go in reverse declaration order (SPEC 5.7 D2).
const ENUM: &str = "f(Shape.Circle { label: \"a\".toString(), tag: \"b\".toString() }, true);

public function f(s: Shape, c: bool): void {
  match (s) {
    Shape.Circle => { if (c) { take(s.label); } },
    Shape.Empty => {},
  }
}

private function take(t: string): void {
  console.log(t);
}

public enum Shape {
  Circle { label: string, tag: string },
  Empty,
}
";

/// Temporaries that nest: `mk`'s result is created after the concatenation it is
/// made from, so D2 ends it first, and so does the array `words` returns as a
/// `for...of` source, after the whole statement.
const NESTED: &str = "demo();

public function demo(): void {
  show(&mk(&(\"a\" + \"b\")));
  for (const w of &wordsOf(&(\"c\" + \"d\"))) {
    show(w);
  }
}

private function show(s: &string): void {
  console.log(s);
}

private function mk(s: &string): string {
  return s.toString();
}

private function wordsOf(s: &string): string[] {
  return [s.toString()];
}
";

/// Temporaries built in place by `new`, each created when its constructor ends,
/// after its arguments' temporaries, so D2 ends it before them: the `View` before
/// the `Tracer` it borrows, as the factory form `View.make` ends them, and the
/// `Holder` before the `Tracer` its argument was read from.
const NESTED_NEW: &str = "demo();

public function demo(): void {
  show(&new View(&new Tracer(\"t\")));
  keep(&new Holder(size(&new Tracer(\"u\"))));
}

private final class Tracer {
  public constructor(public name: string) {}
  public destructor() { console.log(`drop ${this.name}`); }
}

private final class View {
  public constructor(private t: &Tracer) {}
  public label(): &string { return &this.t.name; }
  public destructor() { console.log(`drop view of ${this.t.name}`); }
}

private final class Holder {
  public constructor(public n: isize) {}
  public destructor() { console.log(\"drop holder\"); }
}

private function show(v: &View): void { console.log(v.label()); }
private function keep(h: &Holder): void { console.log(h.n); }
private function size(t: &Tracer): isize { return t.name.length(); }
";

/// A partly moved anonymous object: what is left of it drops field by field, its
/// moved field never again (D4, A:602), as a class's does.
const OBJECT: &str = "f();

public function f(): void {
  const o = { name: \"a\".toString(), other: \"b\".toString() };
  const s = o.name;
  console.log(s);
}
";

/// That a partly moved object `local`'s drop is a ladder over its remaining
/// fields: `drop_glue(local.field)`, and never the whole of it.
pub fn object_ladder(body: &str, local: &str) -> Result<(), String> {
    let lines: Vec<&str> = body.lines().map(str::trim).collect();
    if lines.contains(&format!("drop_glue({local});").as_str()) {
        return Err(format!("{local} is dropped whole after a field moved out"));
    }
    match lines
        .iter()
        .any(|l| l.starts_with(&format!("drop_glue({local}.")))
    {
        true => Ok(()),
        false => Err(format!("no field of {local} is dropped")),
    }
}

/// Every drop trace: its golden's name, the function it shows and its program.
fn traces() -> Vec<(String, &'static str, String)> {
    let mut found: Vec<(String, &'static str, String)> = D2
        .iter()
        .map(|(name, body)| ((*name).to_owned(), "demo", d2_program(body)))
        .collect();
    found.push(("return".to_owned(), "demo", return_program()));
    found.push(("nested_temporaries".to_owned(), "demo", NESTED.to_owned()));
    found.push((
        "nested_new_temporaries".to_owned(),
        "demo",
        NESTED_NEW.to_owned(),
    ));
    found.push(("partly_moved_object".to_owned(), "f", OBJECT.to_owned()));
    for (name, source) in [
        ("partly_moved_nullable", NULLABLE),
        ("partly_moved_result", RESULT),
        ("partly_moved_enum", ENUM),
    ] {
        found.push((name.to_owned(), "f", source.to_owned()));
    }
    found
}

/// The elaborated MIR of `source`, as `check --emit=mir` prints it.
pub fn elaborated(source: &str) -> String {
    let input = Input {
        name: "main.en".to_owned(),
        text: crate::no_panic::Text::Memory(source.to_owned()),
        target: None,
        library: false,
        broken: None,
    };
    let (mut session, checked) = check_input(&input);
    match checked {
        Ok(checked) => emit(&checked, Emit::Mir).expect("the MIR verifies"),
        Err(e) => panic!(
            "{e:?}\n{}",
            session.render(&enrang_diag::RenderOpts::default())
        ),
    }
}

/// The text of the body of the function `name` in a printed module: its header
/// line through the `}` that closes it.
pub fn function(module: &str, name: &str) -> String {
    let lines: Vec<&str> = module.lines().collect();
    let start = lines
        .iter()
        .position(|line| {
            let line = line.trim_start_matches('@').trim_start();
            line.starts_with(&format!("fn {name}("))
                || line
                    .split_once(' ')
                    .is_some_and(|(_, rest)| rest.starts_with(&format!("fn {name}(")))
        })
        .unwrap_or_else(|| panic!("no fn {name} in\n{module}"));
    let end = (start..lines.len())
        .find(|at| lines[*at] == "}")
        .expect("the body closes");
    let mut text = lines[start..=end].join("\n");
    text.push('\n');
    text
}

/// A body's blocks by name, each its lines, the terminator last.
fn blocks(body: &str) -> BTreeMap<String, Vec<String>> {
    let mut found: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut open: Option<String> = None;
    for line in body.lines().map(str::trim) {
        if let Some(name) = line.strip_suffix(": {")
            && name.starts_with("bb")
        {
            open = Some(name.to_owned());
            found.insert(name.to_owned(), Vec::new());
        } else if line == "}" {
            open = None;
        } else if let Some(name) = &open {
            found.get_mut(name).expect("open").push(line.to_owned());
        }
    }
    found
}

/// The targets of a `switch` terminator.
fn targets(terminator: &str) -> Vec<String> {
    let Some((_, list)) = terminator.split_once('[') else {
        return Vec::new();
    };
    list.trim_end_matches("];")
        .split(", ")
        .filter_map(|arm| arm.split_once(": ").map(|(_, to)| to.to_owned()))
        .collect()
}

/// What is wrong with the drop of the partly moved local `local` in an elaborated
/// body: a block reads its tag and switches on it, one of its arms switches on a
/// drop flag, and that flag's arm drops a field of the active case, `drop_glue((_N
/// as Case).field)` (ARCHITECTURE 5.4, A:605): the tag `switch` comes before the
/// ladder, and the flag means something only inside its case's arm.
pub fn tag_before_ladder(body: &str, local: &str) -> Result<(), String> {
    let flags: Vec<String> = body
        .lines()
        .filter_map(|line| line.trim().strip_prefix("let "))
        .filter(|line| line.ends_with(": bool flag;"))
        .map(|line| line.split(':').next().unwrap_or("").to_owned())
        .collect();
    if flags.is_empty() {
        return Err("no drop flag".to_owned());
    }
    let blocks = blocks(body);
    let case_drop = format!("drop_glue(({local} as ");
    for lines in blocks.values() {
        let Some(tag) = lines
            .iter()
            .find(|line| line.ends_with(&format!(" = discriminant({local});")))
        else {
            continue;
        };
        let read = tag.split(" = ").next().unwrap_or("");
        let Some(switch) = lines
            .last()
            .filter(|t| t.starts_with(&format!("switch move {read} ")))
        else {
            continue;
        };
        for arm in targets(switch) {
            let Some(arm_lines) = blocks.get(&arm) else {
                continue;
            };
            let Some(flag_switch) = arm_lines.last().filter(|t| {
                flags
                    .iter()
                    .any(|flag| t.starts_with(&format!("switch copy {flag} ")))
            }) else {
                continue;
            };
            let drops = targets(flag_switch).iter().any(|to| {
                blocks
                    .get(to)
                    .is_some_and(|ls| ls.iter().any(|l| l.starts_with(&case_drop)))
            });
            if drops {
                return Ok(());
            }
        }
    }
    Err(format!(
        "no block switches on the tag of {local} before a flagged drop"
    ))
}

/// What is wrong with a D2 trace: each `string` temporary of `demo` is dropped,
/// once, and right before its `storage_dead`.
fn temporaries_end(body: &str) -> Result<(), String> {
    let strings: Vec<String> = body
        .lines()
        .filter_map(|line| line.trim().strip_prefix("let "))
        .filter(|line| line.ends_with(": string temp;") || line.ends_with(": string[] temp;"))
        .map(|line| line.split(':').next().unwrap_or("").to_owned())
        .collect();
    if strings.is_empty() {
        return Err("no temporary with a destructor".to_owned());
    }
    let lines: Vec<&str> = body.lines().map(str::trim).collect();
    for temp in &strings {
        let drop = format!("drop_glue({temp});");
        let dead = format!("storage_dead({temp});");
        let at: Vec<usize> = (0..lines.len()).filter(|i| lines[*i] == drop).collect();
        let [at] = at[..] else {
            return Err(format!("{temp} is dropped {} times", at.len()));
        };
        if lines.get(at + 1) != Some(&dead.as_str()) {
            return Err(format!(
                "{temp}'s storage does not end right after its drop"
            ));
        }
    }
    Ok(())
}

/// What is wrong with the order a trace's temporaries end in: in each run of
/// `drop_glue` and `storage_dead` lines, the temporaries must end in the reverse
/// order of their first assignment, which is their creation (SPEC 5.7 D2), not of
/// their locals' numbers; a temporary built in place, by `new` or a named form, is
/// created where its constructor gets it, `&_t [auto-borrow]` or `addr_of _t`,
/// after every argument. Blocks print in the order they were built, so within one
/// statement a line's place is its order.
pub fn reverse_creation(body: &str) -> Result<(), String> {
    let lines: Vec<&str> = body.lines().map(str::trim).collect();
    let created = |temp: &str| {
        let head = format!("{temp} = ");
        let this = format!("= &{temp} [auto-borrow];");
        let addr = format!("= addr_of {temp};");
        lines.iter().position(|line| {
            line.starts_with(&head) || line.ends_with(&this) || line.ends_with(&addr)
        })
    };
    let mut run: Vec<(String, usize)> = Vec::new();
    for line in lines.iter().copied().chain(std::iter::once("")) {
        let ended = line
            .strip_prefix("storage_dead(")
            .and_then(|rest| rest.strip_suffix(");"));
        match ended {
            Some(temp) => {
                if let Some(at) = created(temp) {
                    run.push((temp.to_owned(), at));
                }
            }
            None if line.starts_with("drop_glue(") => {}
            None => {
                if let Some(pair) = run.windows(2).find(|pair| pair[0].1 < pair[1].1) {
                    return Err(format!(
                        "{} ends before {}, which was created after it",
                        pair[0].0, pair[1].0
                    ));
                }
                run.clear();
            }
        }
    }
    Ok(())
}

pub fn register(h: &mut Harness) {
    for (name, function_name, source) in traces() {
        h.case(
            format!("drops/{name}: the elaborated MIR is the golden"),
            move || {
                let body = function(&elaborated(&source), function_name);
                if name == "partly_moved_object" {
                    let o = (body.lines())
                        .find_map(|l| l.trim().strip_suffix("; // o"))
                        .and_then(|l| l.strip_prefix("let "))
                        .and_then(|l| l.split(':').next())
                        .expect("the object's local");
                    object_ladder(&body, o).unwrap_or_else(|e| panic!("{e}\n{body}"));
                } else if name.starts_with("partly_moved") {
                    tag_before_ladder(&body, "_1").unwrap_or_else(|e| panic!("{e}\n{body}"));
                } else if name == "nested_new_temporaries" {
                    // Its temporaries are objects built in place, moved into no
                    // call: their order is what it pins.
                    reverse_creation(&body).unwrap_or_else(|e| panic!("{e}\n{body}"));
                } else {
                    temporaries_end(&body).unwrap_or_else(|e| panic!("{e}\n{body}"));
                    reverse_creation(&body).unwrap_or_else(|e| panic!("{e}\n{body}"));
                }
                golden("pipeline", &format!("drops/{name}.mir"), &body)
            },
        );
    }
    h.case(
        "drops/one trace per row of D2's table, and three partly moved values",
        || {
            let spec =
                std::fs::read_to_string(enrang_testkit::workspace_root().join("docs/SPEC.md"))
                    .expect("SPEC");
            let rows: Vec<&str> = spec
                .lines()
                .map(str::trim)
                .skip_while(|line| *line != "| Temporaries created in | End |")
                .skip(2)
                .take_while(|line| line.starts_with('|'))
                .collect();
            // Each row's boundary has at least one program here, named after it.
            let words = [
                ("`if`", "if_condition"),
                ("`while`", "while_condition"),
                ("`do...while`", "do_while_condition"),
                ("`for`, or", "for_condition"),
                ("ternary", "ternary_condition"),
                ("Step of a `for`", "for_step"),
                ("`&&`", "and_right_operand"),
                ("`\\|\\|`", "or_right_operand"),
                ("`match`", "match_subject"),
                ("`for...of`", "for_of_source"),
                ("`let`/`const` initialiser", "let_initialiser"),
                ("expression statement", "expression_statement"),
                ("assignment", "assignment"),
                ("`return`", "return"),
            ];
            let names: Vec<String> = traces().into_iter().map(|(name, _, _)| name).collect();
            for row in &rows {
                let covered = words
                    .iter()
                    .filter(|(word, _)| row.contains(word))
                    .map(|(_, name)| *name)
                    .collect::<Vec<&str>>();
                assert!(!covered.is_empty(), "no program for {row}");
                for name in covered {
                    assert!(names.iter().any(|have| have == name), "{name}");
                }
            }
            assert_eq!(rows.len(), 5, "{rows:?}");
            assert_eq!(names.len(), D2.len() + 7);
        },
    );
    h.case(
        "drops/the order check refuses temporaries ended by their numbers",
        || {
            // `_2` is declared first but created last, so it must end first.
            let by_number = "  bb0: {\n    _3 = const \"a\": string;\n    _2 = mk(move _3) -> bb1;\n  }\n  \
                             bb1: {\n    drop_glue(_3);\n    storage_dead(_3);\n    drop_glue(_2);\n    \
                             storage_dead(_2);\n    return;\n  }\n";
            assert_eq!(
                reverse_creation(by_number),
                Err("_3 ends before _2, which was created after it".to_owned())
            );
            let by_creation = by_number
                .replace("drop_glue(_3);\n    storage_dead(_3);\n    drop_glue(_2);\n    storage_dead(_2);",
                    "drop_glue(_2);\n    storage_dead(_2);\n    drop_glue(_3);\n    storage_dead(_3);");
            assert_ne!(by_creation, by_number);
            assert_eq!(reverse_creation(&by_creation), Ok(()));
            // A `new` temporary is created where its constructor takes it, after
            // its argument's: `_2`, declared first, must end first.
            let built = "  bb0: {\n    _3 = const \"a\": string;\n    _4 = &_2 [auto-borrow];\n    \
                         _5 = C::#ctor(move _4, move _3) -> bb1;\n  }\n  bb1: {\n    drop_glue(_3);\n    \
                         storage_dead(_3);\n    drop_glue(_2);\n    storage_dead(_2);\n    return;\n  }\n";
            assert_eq!(
                reverse_creation(built),
                Err("_3 ends before _2, which was created after it".to_owned())
            );
            assert_eq!(object_ladder("    drop_glue(_2);\n", "_2").is_err(), true);
            assert_eq!(object_ladder("    drop_glue(_2.other);\n", "_2"), Ok(()));
        },
    );
    h.case(
        "drops/the tag check finds a ladder and refuses a flag outside it",
        || {
            let good = function(&elaborated(NULLABLE), "f");
            assert_eq!(tag_before_ladder(&good, "_1"), Ok(()));
            // The same drop with the tag switch taken away: the flag guards the field
            // whatever the case.
            let lines: Vec<&str> = good.lines().collect();
            let read = lines
                .iter()
                .rev()
                .find_map(|line| line.trim().strip_suffix(" = discriminant(_1);"))
                .expect("the drop reads the tag");
            let switch = lines
                .iter()
                .find(|line| line.trim().starts_with(&format!("switch move {read} ")))
                .expect("and switches on it");
            let arm = targets(switch.trim())[0].clone();
            let flat = good.replace(switch.trim(), &format!("goto {arm};"));
            assert_ne!(flat, good);
            assert!(tag_before_ladder(&flat, "_1").is_err());
            assert!(tag_before_ladder(&good, "_2").is_err());
            assert!(temporaries_end(&good).is_err(), "f has no string temporary");
        },
    );
}
