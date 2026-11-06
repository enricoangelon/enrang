//! The acceptance suite of the `enrang` binary.
//!
//! Golden cases run the real binary as a process. The broad tables run the same
//! function in-process, since they ask the same question hundreds of times.

#![forbid(unsafe_code)]

mod arguments;
mod evidence;
mod explain;
mod goldens;
mod help;
mod internal;
mod streams;
mod support;
mod targets;
mod typos;

use std::process::ExitCode;

use enrang_testkit::Harness;

fn main() -> ExitCode {
    let mut h = Harness::new("cli");
    h.goldens(support::SUITE);
    h.goldens(support::INPROCESS_SUITE);
    goldens::register(&mut h);
    help::register(&mut h);
    explain::register(&mut h);
    targets::register(&mut h);
    evidence::register(&mut h);
    arguments::register(&mut h);
    typos::register(&mut h);
    streams::register(&mut h);
    internal::register(&mut h);
    h.run()
}
