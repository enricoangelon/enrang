//! The MIR text round trip of every body the pipeline builds (M3 plan f.4;
//! TESTING 23's M3 item "`.mir` module round trip"): for every input of
//! `no_panic` that passes phases 1 and 2, each user module's bodies, as mirbuild
//! built them and as drop elaboration rewrote them, print, parse back and print
//! the same text, `print_module(parse_module(print_module(b))) == print_module(b)`.
//!
//! The mir suite's hand-written modules round-trip what a person wrote; this
//! suite round-trips what the compiler writes, implicit parameters and the type
//! arguments of a member called through a bound included (A:562). The text names
//! an implicit parameter (D5) by the interface or object type it stands for, so a
//! body parsed back is not verified here: one that also holds that type itself
//! reads both as one, which loading an interface file's bodies (M4, ARCHITECTURE
//! 6.8) must tell apart.

use enrang_mir::{Body, parse_module, print_module};
use enrang_testkit::{Harness, catch_panic};

use crate::no_panic::{Input, groups, runnable, through_phase3};

/// Why `bodies`, printed as `what`, does not round-trip; `None` when it does.
pub fn roundtrip_problem(tcx: &enrang_hir::Tcx, bodies: &[Body], what: &str) -> Option<String> {
    let text = print_module(tcx, bodies);
    let (tcx2, list) = match parse_module(&text) {
        Ok(parsed) => parsed,
        Err(e) => return Some(format!("{what}: does not parse: {e}\n{text}")),
    };
    let again = print_module(&tcx2, &list);
    if again == text {
        return None;
    }
    let line = again
        .lines()
        .zip(text.lines())
        .position(|(a, b)| a != b)
        .unwrap_or_else(|| again.lines().count().min(text.lines().count()));
    Some(format!(
        "{what}: differs at line {}: printed {:?}, printed again {:?}",
        line + 1,
        text.lines().nth(line),
        again.lines().nth(line)
    ))
}

/// How many modules of an input round-tripped, built and elaborated; `None` when
/// phases 1 and 2 reject it.
fn roundtrip_input(input: &Input) -> Result<Option<usize>, String> {
    let ran = through_phase3(input).map_err(|e| format!("{}: internal error: {e}", input.name))?;
    let Some((mut session, typed, out)) = ran else {
        return Ok(None);
    };
    let _ = std::mem::take(&mut session.dcx);
    let tcx = &typed.tcx;
    let mut modules = 0;
    for (_, owners) in &out.modules {
        if owners.is_empty() {
            continue;
        }
        let built: Vec<Body> = owners.iter().map(|o| out.mir[o].clone()).collect();
        let elaborated: Vec<Body> = owners
            .iter()
            .map(|o| enrang_borrowck::elaborate_drops(tcx, out.mir[o].clone(), &out.facts[o]))
            .collect();
        for (what, bodies) in [("built", &built), ("elaborated", &elaborated)] {
            if let Some(problem) = roundtrip_problem(tcx, bodies, what) {
                return Err(format!("{}: {problem}", input.name));
            }
        }
        modules += 1;
    }
    Ok(Some(modules))
}

/// The gate's two programs (M3 stage 5 gate, the DoD audit): a parameter of an
/// object type, whose implicit parameter its body's `let` restates, and a generic
/// interface member called through a parameter, whose own type argument the call
/// keeps; with the text each must print.
const PROGRAMS: [(&str, &str, &str); 2] = [
    (
        "an implicit object parameter restated by its body's `let`",
        "show({ name: \"Ada\".toString() });\n\n\
         private function show(o: { name: string }): void {\n  console.log(o.name);\n}\n",
        "  let _1: { name: string }; // o\n",
    ),
    (
        "a generic member called through an interface parameter keeps its own type argument",
        "private function f(z: &Sizer, v: &string): isize {\n  return z.size(v);\n}\n\n\
         public interface Measured {\n  length(): isize;\n}\n\n\
         public interface Sizer {\n  size<T extends Measured>(x: &T): isize;\n}\n",
        " = Sizer::size<string>(",
    ),
];

pub fn register(h: &mut Harness) {
    for (what, source, printed) in PROGRAMS {
        h.case(format!("roundtrip/{what}"), move || {
            let built = crate::support::build(source);
            let bodies: Vec<Body> = built.bodies.values().cloned().collect();
            let text = print_module(&built.tcx, &bodies);
            assert!(text.contains(printed), "{text}");
            if let Some(problem) = roundtrip_problem(&built.tcx, &bodies, "built") {
                panic!("{problem}");
            }
        });
    }
    for (group, inputs) in groups() {
        h.case(
            format!("roundtrip/{group}: every body built and elaborated prints back the same"),
            move || {
                let mut failures = Vec::new();
                for input in runnable(&inputs) {
                    let mut result = None;
                    if let Some(panic) = catch_panic(|| result = Some(roundtrip_input(input))) {
                        failures.push(format!("{}: panicked: {panic}", input.name));
                        continue;
                    }
                    if let Err(failure) = result.expect("ran") {
                        failures.push(failure);
                    }
                }
                assert!(failures.is_empty(), "\n{}", failures.join("\n---\n"));
            },
        );
    }
}
