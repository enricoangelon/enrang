//! A process whose body panics, so a meta-test can see what a bug in the compiler
//! looks like from outside: exit status 3 and no panic report.

#![forbid(unsafe_code)]

use std::process::ExitCode;

use enrang_cli::{Outcome, entry};

fn main() -> ExitCode {
    entry(|| -> Outcome { panic!("a deliberate panic") })
}
