//! The MIR verifier after every pass (M3 plan f.1, stage 4M; TESTING 23's M3 item
//! "MIR verifier after every pass"): for every input of `no_panic` that passes
//! phases 1 and 2, every body of every user module, as mirbuild built it and as
//! drop elaboration rewrote it, passes `enrang_mir::verify`.
//!
//! Phase 3 runs as `check` runs it (`run_phase3`), which verifies each built body
//! and reports a failure as an internal error; this suite verifies each body again
//! and then elaborates it with what checking it found, as `--emit=mir` and the
//! later milestones do, and verifies the result. A program that phase 3 rejects
//! still has its bodies built and checked, so a firing fixture's MIR is verified
//! too, elaborated included: elaboration reads the init dataflow, which a use
//! after a move or a borrow error leaves well defined.

use enrang_mir::verify;
use enrang_testkit::{Harness, catch_panic};

use crate::no_panic::{Input, groups, runnable, through_phase3};

/// How many bodies of an input were verified, built and elaborated; `None` when
/// phases 1 and 2 reject it.
fn verify_input(input: &Input) -> Result<Option<usize>, String> {
    let ran = through_phase3(input).map_err(|e| format!("{}: internal error: {e}", input.name))?;
    let Some((mut session, typed, out)) = ran else {
        return Ok(None);
    };
    // Phase 3's own report stays in the session; this suite reads only the MIR.
    let _ = std::mem::take(&mut session.dcx);
    let tcx = &typed.tcx;
    let mut bodies = 0;
    for (_, owners) in &out.modules {
        for owner in owners {
            let built = &out.mir[owner];
            if let Err(errors) = verify(tcx, built) {
                return Err(format!("{}: {owner:?} as built: {errors:?}", input.name));
            }
            let facts = &out.facts[owner];
            let elaborated = enrang_borrowck::elaborate_drops(tcx, built.clone(), facts);
            if let Err(errors) = verify(tcx, &elaborated) {
                return Err(format!("{}: {owner:?} elaborated: {errors:?}", input.name));
            }
            bodies += 1;
        }
    }
    Ok(Some(bodies))
}

/// Whether no input of a group has a statement or a body to build: every fixture
/// of a code about declarations (sizes, layouts, enum values) may be so.
fn group_of_declarations(inputs: &[Input]) -> bool {
    inputs
        .iter()
        .all(|input| input.name.starts_with("tests/compile/"))
}

/// A module whose body the verifier rejects: `_2 = copy _1` puts an `i64` into a
/// `bool` (rule Types).
const BROKEN: &str = "fn f(_1: i64) -> i64 {
  let _1: i64;
  let _2: bool temp;
  bb0: {
    _2 = copy _1;
    _0 = copy _1;
    return;
  }
}
";

/// The same module, verifier-clean.
const CLEAN: &str = "fn f(_1: i64) -> i64 {
  let _1: i64;
  bb0: {
    _0 = copy _1;
    return;
  }
}
";

/// A program whose function `f` has a local `x`, which the seams below retype.
const SEAM: &str = "function f(): i64 {\n  const x: i64 = 1;\n  return x;\n}\nconsole.log(f());\n";

/// The seam of `run_phase3`: `typed` with `f`'s local `x` retyped `bool` in the
/// typed program, so that the MIR mirbuild builds for `f` fails the verifier.
fn retype_x(typed: &mut enrang_driver::Typed) {
    let boolean = typed.tcx.common().bool;
    let tcx = &typed.tcx;
    let (_, body) = (typed.program.bodies.iter_mut())
        .find(|(d, _)| tcx.def(**d).name().is_some_and(|n| n.as_str() == "f"))
        .expect("the function `f`");
    let body = std::sync::Arc::make_mut(body);
    let x = (body.locals.iter_mut())
        .find(|l| l.name.is_some_and(|n| n.as_str() == "x"))
        .expect("the local `x`");
    x.ty = boolean;
}

pub fn register(h: &mut Harness) {
    // TESTING 23's M3 item "MIR verifier after every pass", through the driver
    // itself: a built body that fails the verifier is never checked, and an
    // elaborated one is never printed; each is an internal error (exit status 3).
    h.case(
        "verify_all/seam: run_phase3 verifies each body mirbuild built, and one that fails is an internal error",
        || {
            let (mut session, mut typed) = crate::support::typed(SEAM);
            assert!(
                enrang_driver::run_phase3(&mut session, &typed).is_ok(),
                "the program as typed passes phase 3"
            );
            let (mut session, _) = crate::support::typed(SEAM);
            retype_x(&mut typed);
            let internal = enrang_driver::run_phase3(&mut session, &typed)
                .err()
                .expect("a body that fails the verifier is an internal error");
            assert!(
                internal.0.contains("the MIR of `main::f` fails the verifier"),
                "{}",
                internal.0
            );
        },
    );
    h.case(
        "verify_all/seam: --emit=mir verifies each elaborated body again, and one that fails is an internal error",
        || {
            let mut checked = crate::support::checked_program(SEAM);
            assert!(enrang_driver::emit(&checked, enrang_driver::Emit::Mir).is_ok());
            let boolean = checked.tcx.common().bool;
            let tcx = &checked.tcx;
            let (_, body) = (checked.mir.iter_mut())
                .find(|(o, _)| {
                    matches!(o, enrang_mir::BodyOwner::Fn(d) if tcx.def(*d).name().is_some_and(|n| n.as_str() == "f"))
                })
                .expect("the body of `f`");
            let x = (body.locals.iter_mut())
                .find(|l| l.name.is_some_and(|n| n.as_str() == "x"))
                .expect("the local `x`");
            x.ty = boolean;
            let internal = enrang_driver::emit(&checked, enrang_driver::Emit::Mir)
                .expect_err("an elaborated body that fails the verifier is never printed");
            assert!(
                internal.0.contains("the elaborated MIR of `main::f` fails the verifier"),
                "{}",
                internal.0
            );
        },
    );
    h.case(
        "verify_all/phase 3 orders a module's built bodies only once each passes the \
         verifier, and an elaborated body is printed only once it passes again",
        || {
            for (text, clean) in [(CLEAN, true), (BROKEN, false)] {
                let (tcx, list) = enrang_mir::parse_module(text).expect("the module parses");
                let bodies: enrang_mir::Bodies =
                    (list.iter().cloned()).map(|b| (b.owner, b)).collect();
                let order = enrang_driver::verified_order(&tcx, &bodies);
                let printed = enrang_driver::print_elaborated(&tcx, &list);
                match clean {
                    true => {
                        assert_eq!(order.map(|o| o.len()), Ok(1));
                        assert!(printed.is_ok_and(|t| t.contains("fn f(")));
                    }
                    false => {
                        let order = order.expect_err("a broken body is an internal error");
                        assert!(order.0.contains("fails the verifier"), "{}", order.0);
                        let printed = printed.expect_err("a broken body is never printed");
                        assert!(printed.0.contains("fails the verifier"), "{}", printed.0);
                    }
                }
            }
        },
    );
    for (group, inputs) in groups() {
        h.case(
            format!("verify_all/{group}: every body verifies as built and as elaborated"),
            move || {
                let mut failures = Vec::new();
                let mut bodies = 0;
                let mut reached = 0;
                for input in runnable(&inputs) {
                    let mut result = None;
                    if let Some(panic) = catch_panic(|| result = Some(verify_input(input))) {
                        failures.push(format!("{}: panicked: {panic}", input.name));
                        continue;
                    }
                    match result.expect("ran") {
                        Ok(Some(n)) => {
                            reached += 1;
                            bodies += n;
                        }
                        Ok(None) => {}
                        Err(failure) => failures.push(failure),
                    }
                }
                assert!(failures.is_empty(), "\n{}", failures.join("\n"));
                // Every near-miss passes phase 2 and has a statements body at least.
                let near_misses = inputs
                    .iter()
                    .filter(|input| input.name.ends_with(".pass.en"))
                    .count();
                assert!(reached >= near_misses, "{reached} reached phase 3");
                // A program of declarations alone, or a library module, has no body.
                assert!(
                    reached == 0 || bodies > 0 || group_of_declarations(&inputs),
                    "no body"
                );
            },
        );
    }
}
