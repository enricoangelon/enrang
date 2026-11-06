//! The testkit's own suite, run by the harness it tests.
//!
//! A harness that checks itself cannot be trusted on its verdict alone, so the
//! cases that matter also run a child copy of this binary, selected by
//! `ENRANG_TESTKIT_CHILD`, and judge its exit status and output from outside.
//! Children are also how the environment knobs are tested, because `set_var` is
//! `unsafe` in this edition.

#![forbid(unsafe_code)]

mod children;
mod doc_cases;
mod gating;
mod goldens;
mod harness;
mod prng;
mod rows;
mod shrinking;
mod skips;
mod support;

use std::env;
use std::process::ExitCode;

use enrang_testkit::Harness;

fn main() -> ExitCode {
    if let Ok(scenario) = env::var(support::CHILD_VAR) {
        return children::run(&scenario);
    }
    let mut h = Harness::new("testkit");
    h.goldens("testkit");
    prng::register(&mut h);
    harness::register(&mut h);
    shrinking::register(&mut h);
    goldens::register(&mut h);
    skips::register(&mut h);
    doc_cases::register(&mut h);
    rows::register(&mut h);
    gating::register(&mut h);
    h.run()
}
