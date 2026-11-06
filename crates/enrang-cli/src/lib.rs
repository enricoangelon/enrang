//! The `enrang` command line (ARCHITECTURE 11).
//!
//! [`run`] is the whole command line as a function from arguments to an [`Outcome`],
//! so a test can drive it in-process, and [`main`] connects it to a real process.
//! Arguments are parsed by hand and nothing here reads the environment, a clock or
//! a file, so equal arguments print equal bytes.
//!
//! No compiler exists at this milestone. `explain` and `targets` work; every other
//! name reports what it is and does nothing.

#![forbid(unsafe_code)]

mod commands;
mod evidence;
mod explain;
mod help;
mod outcome;
mod report;
mod table;
mod targets;

use std::env;
use std::io::{self, IsTerminal};
use std::panic::{self, AssertUnwindSafe};
use std::process::ExitCode;

pub use commands::{ALIASES, Alias, DEFERRED, LATER, LaterCommand, WORKING, Working};
pub use evidence::{CLASSES, FAMILIES, Family};
pub use outcome::{EXIT_FAILURE, EXIT_INTERNAL, EXIT_SUCCESS, EXIT_USAGE, Outcome};

/// Runs the command line. `color` paints diagnostics, and it is for the caller to
/// decide: the rule of SPEC 13.1 depends on what stderr is.
pub fn run(args: &[String], color: bool) -> Outcome {
    let Some((first, rest)) = args.split_first() else {
        return report::complaint(
            "no command given",
            Some("run `enrang --help` to see the commands"),
            Some(help::USAGE),
        );
    };
    match first.as_str() {
        "--help" | "-h" => global_flag(first, rest, help::text),
        "--version" | "-V" => global_flag(first, rest, help::version),
        "explain" => explain::command(rest),
        "targets" => targets::command(rest),
        name => report::not_a_working_command(name, color),
    }
}

fn global_flag(flag: &str, rest: &[String], print: fn() -> String) -> Outcome {
    if rest.is_empty() {
        Outcome::print(print())
    } else {
        report::complaint(
            &format!("`{flag}` takes no arguments"),
            None,
            Some(help::USAGE),
        )
    }
}

/// Runs `body`, turning a panic into the report of an internal error: a panic is a
/// bug in the compiler, never the user's mistake.
pub fn guarded(body: impl FnOnce() -> Outcome) -> Outcome {
    panic::catch_unwind(AssertUnwindSafe(body)).unwrap_or_else(|payload| {
        let message = payload
            .downcast_ref::<&str>()
            .map(|text| (*text).to_owned())
            .or_else(|| payload.downcast_ref::<String>().cloned())
            .unwrap_or_else(|| "a panic with no message".to_owned());
        Outcome::internal(&message)
    })
}

/// Runs `body` as a whole process: no panic report but the [`guarded`] one, the
/// output written to the real streams, and its status returned.
pub fn entry(body: impl FnOnce() -> Outcome) -> ExitCode {
    panic::set_hook(Box::new(|_| {}));
    let outcome = guarded(body);
    ExitCode::from(outcome.emit(&mut io::stdout(), &mut io::stderr()))
}

/// The `enrang` binary. An argument that is not Unicode cannot name anything, so it
/// goes through lossily and is reported like any other unknown name.
pub fn main() -> ExitCode {
    let args: Vec<String> = env::args_os()
        .skip(1)
        .map(|arg| arg.to_string_lossy().into_owned())
        .collect();
    let color = io::stderr().is_terminal();
    entry(|| run(&args, color))
}
