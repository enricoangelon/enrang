//! Running the command line, and writing down what it did.

use std::path::Path;
use std::process::Command;

use enrang_cli::{Outcome, run};

/// The golden directory of whole-process transcripts. `enrang-suite` reads it too,
/// so a golden here is also a firing fixture and a determinism case.
pub const SUITE: &str = "cli";

/// The golden directory of what no process can show today.
pub const INPROCESS_SUITE: &str = "cli-inprocess";

pub const BIN: &str = env!("CARGO_BIN_EXE_enrang");

/// A finished process.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Ran {
    pub stdout: String,
    pub stderr: String,
    pub code: i32,
}

pub fn finished(command: &mut Command) -> Ran {
    let output = command.output().expect("the binary runs");
    Ran {
        stdout: String::from_utf8(output.stdout).expect("stdout is UTF-8"),
        stderr: String::from_utf8(output.stderr).expect("stderr is UTF-8"),
        code: output.status.code().expect("the binary exits normally"),
    }
}

pub fn enrang(args: &[String]) -> Ran {
    finished(Command::new(BIN).args(args))
}

pub fn enrang_in(dir: &Path, args: &[String]) -> Ran {
    finished(Command::new(BIN).args(args).current_dir(dir))
}

pub fn strings(args: &[&str]) -> Vec<String> {
    args.iter().map(|arg| (*arg).to_owned()).collect()
}

/// The command line in this process, with no colour.
pub fn inproc(args: &[&str]) -> Outcome {
    run(&strings(args), false)
}

/// A golden's whole text: the command, then what it did. Nothing about it is
/// normalised, and an output with no final newline shows on the next marker's line.
pub fn transcript(args: &[String], ran: &Ran) -> String {
    let mut text = String::from("$ enrang");
    for arg in args {
        text.push(' ');
        text.push_str(&quote(arg));
    }
    text.push_str(&format!(
        "\n[exit {}]\n[stdout]\n{}[stderr]\n{}",
        ran.code, ran.stdout, ran.stderr
    ));
    text
}

/// Shell quoting, so that a golden's first line is a command one can paste, and one
/// `enrang-suite` can run again.
fn quote(arg: &str) -> String {
    let plain = |c: char| c.is_ascii_alphanumeric() || "-_./=:+,@%".contains(c);
    if !arg.is_empty() && arg.chars().all(plain) {
        return arg.to_owned();
    }
    assert!(
        !arg.contains(['\'', '\\']),
        "no golden needs a quote or a backslash in an argument: {arg:?}"
    );
    if arg.chars().any(char::is_control) {
        let escaped: String = arg
            .chars()
            .map(|c| {
                if c.is_control() {
                    format!("\\x{:02x}", u32::from(c))
                } else {
                    c.to_string()
                }
            })
            .collect();
        return format!("$'{escaped}'");
    }
    format!("'{arg}'")
}

/// The rows of a table in the listing: the lines after `heading` and a blank line
/// up to the next blank line, split into cells.
pub fn table_rows(text: &str, heading: &str) -> Vec<Vec<String>> {
    let mut lines = text.lines();
    assert!(
        lines.any(|line| line == heading),
        "no heading {heading:?} in:\n{text}"
    );
    assert_eq!(lines.next(), Some(""), "no blank line after {heading:?}");
    lines
        .take_while(|line| !line.is_empty())
        .map(|line| {
            line.split("  ")
                .map(str::trim)
                .filter(|cell| !cell.is_empty())
                .map(str::to_owned)
                .collect()
        })
        .collect()
}
