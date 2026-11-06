//! What the test modules share: running a child copy of this binary, reading the
//! real documents, and running a small harness in-process.

use std::env;
use std::fs;
use std::path::Path;
use std::process::Command;
use std::sync::Arc;

use enrang_testkit::{Harness, RunOptions, RunReport, SkipLedger, workspace_root};

/// Selects a scenario of `children.rs` in a child process.
pub const CHILD_VAR: &str = "ENRANG_TESTKIT_CHILD";

/// Everything the testkit reads from the environment. A child starts without
/// them, so the suite also passes under `ENRANG_SCALE=10` or `CI=1`, and each test
/// states the ones it means.
const KNOBS: [&str; 5] = [
    "ENRANG_SEED",
    "ENRANG_SCALE",
    "ENRANG_BLESS",
    "ENRANG_REQUIRE",
    "CI",
];

pub struct ChildOutput {
    pub code: Option<i32>,
    pub stdout: String,
    pub stderr: String,
}

/// Runs a scenario with these command-line arguments and environment variables.
pub fn child(scenario: &str, args: &[&str], vars: &[(&str, &str)]) -> ChildOutput {
    spawn(child_command(scenario, args, vars))
}

/// [`child`], with these variables removed from what it would have inherited.
pub fn child_without(scenario: &str, removed: &[&str]) -> ChildOutput {
    let mut command = child_command(scenario, &[], &[]);
    for name in removed {
        command.env_remove(name);
    }
    spawn(command)
}

/// [`child`], from another working directory.
pub fn child_in(dir: &Path, scenario: &str, vars: &[(&str, &str)]) -> ChildOutput {
    let mut command = child_command(scenario, &[], vars);
    command.current_dir(dir);
    spawn(command)
}

fn child_command(scenario: &str, args: &[&str], vars: &[(&str, &str)]) -> Command {
    let exe = env::current_exe().expect("the running test binary has a path");
    let mut command = Command::new(exe);
    command.env(CHILD_VAR, scenario).args(args);
    for knob in KNOBS {
        command.env_remove(knob);
    }
    for (name, value) in vars {
        command.env(name, value);
    }
    command
}

fn spawn(mut command: Command) -> ChildOutput {
    let output = command.output().expect("the test binary can run itself");
    ChildOutput {
        code: output.status.code(),
        stdout: String::from_utf8(output.stdout).expect("child stdout is UTF-8"),
        stderr: String::from_utf8(output.stderr).expect("child stderr is UTF-8"),
    }
}

/// A document of `docs/`.
pub fn read_doc(name: &str) -> String {
    let path = workspace_root().join("docs").join(name);
    fs::read_to_string(&path).unwrap_or_else(|error| panic!("cannot read docs/{name}: {error}"))
}

/// Runs a harness built by `build`, with its own skip ledger, capturing its output.
pub fn run_harness(build: impl FnOnce(&mut Harness), options: &RunOptions) -> (RunReport, String) {
    let mut harness = Harness::new("demo");
    harness.ledger(Arc::new(SkipLedger::new()));
    build(&mut harness);
    let mut out = Vec::new();
    let report = harness.run_with(options, &mut out);
    (
        report,
        String::from_utf8(out).expect("harness output is UTF-8"),
    )
}

/// The last line of some output, which for a harness is its verdict.
pub fn last_line(text: &str) -> &str {
    text.lines().last().unwrap_or("")
}
