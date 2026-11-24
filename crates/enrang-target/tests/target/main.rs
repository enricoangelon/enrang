//! The acceptance suite of enrang-target.
//!
//! Every case registers on the testkit harness, so `--list` shows the whole suite
//! and a filter can select any row of any table. Where a document states a table,
//! the suite reads it from `docs/`, so code and document cannot drift apart.

#![forbid(unsafe_code)]

mod aliases;
mod chips;
mod features;
mod floats;
mod layout;
mod levels;
mod output;
mod properties;
mod regs;
mod rejects;
mod support;
mod targets;
mod usize;

use std::process::ExitCode;

use enrang_testkit::Harness;

fn main() -> ExitCode {
    let mut h = Harness::new("target");
    features::register(&mut h);
    levels::register(&mut h);
    chips::register(&mut h);
    aliases::register(&mut h);
    rejects::register(&mut h);
    floats::register(&mut h);
    output::register(&mut h);
    targets::register(&mut h);
    regs::register(&mut h);
    usize::register(&mut h);
    layout::register(&mut h);
    properties::register(&mut h);
    h.run()
}
