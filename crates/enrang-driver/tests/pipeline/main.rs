//! The pipeline suite of enrang-driver (M3 plan g.1): programs checked through
//! phases 1 and 2, every user module's bodies built by mirbuild and verified
//! (plan g.3); the core constructs are stage 2B's module, the control constructs
//! stage 2C's, realistic programs through all of phase 3 merge-2's, the fix
//! stage's programs (`fixes`), every compile fixture's fix-its applied and checked
//! again (`fixits`), the third review's (`review3`) and the first fixture
//! wave's compiler disagreements (`soundfix`), SPEC 14's M3 cases through `check` (`goldens`), and
//! what turning phase 3 on found in the M2 corpus (`integrate`), and the wording of
//! every other message form, pinned in goldens (`wording`); stage 4M's drop traces
//! (`drops`), interface files (`interface`), and every fixture, corpus program,
//! SPEC block and page example with no panic (`no_panic`), its MIR verified after
//! every pass (`verify_all`) and two runs alike (`determinism`); and TESTING 14's
//! `Mutants` generator, one violation inserted into each accepted program, which
//! `check` must reject with its intended code (`mutants`); and the close audit's
//! programs, the holes catch-all arms left and each specially lowered form's
//! effects (`audit`).

#![forbid(unsafe_code)]

mod audit;
mod build_control;
mod build_core;
mod determinism;
mod drops;
mod fixes;
mod fixits;
mod goldens;
mod integrate;
mod interface;
mod mutants;
mod no_panic;
mod programs;
mod review3;
mod roundtrip;
mod scc;
mod soundfix;
mod support;
mod verify_all;
mod wording;

// The hand-built diagnostics of SPEC 14 from `enrang-diag`'s suite, the reference
// `goldens` compares the G cases with (M3 plan f.2); its own cases are not run here.
#[allow(dead_code)]
#[path = "../../../enrang-diag/tests/diag/support.rs"]
mod diag_support;
#[allow(dead_code)]
#[path = "../../../enrang-diag/tests/diag/goldens.rs"]
mod hand;

use std::process::ExitCode;

use enrang_testkit::Harness;

/// This suite's share of the 4,000 more cases TESTING 23 asks of M3 (M3 plan f.9,
/// which forecast 750): every case it registers, all of them M3's, each host of
/// `mutants` one. `enrang-suite`'s meta-tests check that the shares of M3's suites
/// add up.
pub const M3_SHARE: usize = 2_750;

fn main() -> ExitCode {
    let mut h = Harness::new("pipeline");
    h.case("pipeline/a program's bodies build and verify", || {
        let built = support::build("function f(a: i64): i64 {\n  return a;\n}\nf(1);\n");
        assert_eq!(built.bodies.len(), 2, "the statements and `f`");
        assert!(
            built.text().contains(" fn f(_1: i64) -> i64 {"),
            "{}",
            built.text()
        );
    });
    // The orphan check of `tests/golden/pipeline/`: an unused golden fails it.
    h.goldens("pipeline");
    build_core::register(&mut h);
    audit::register(&mut h);
    build_control::register(&mut h);
    programs::register(&mut h);
    review3::register(&mut h);
    fixes::register(&mut h);
    fixits::register(&mut h);
    soundfix::register(&mut h);
    scc::register(&mut h);
    goldens::register(&mut h);
    integrate::register(&mut h);
    wording::register(&mut h);
    drops::register(&mut h);
    interface::register(&mut h);
    no_panic::register(&mut h);
    verify_all::register(&mut h);
    roundtrip::register(&mut h);
    determinism::register(&mut h);
    mutants::register(&mut h);
    let m3 = h.len();
    h.case(
        "count/this suite holds its share of M3's cases",
        move || {
            assert!(m3 >= M3_SHARE, "{m3} cases, short of {M3_SHARE}");
        },
    );
    h.run()
}
