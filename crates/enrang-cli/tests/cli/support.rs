//! Running the command line, and writing down what it did.

use std::io::{self, Write};
use std::path::Path;
use std::process::{Command, Stdio};

use enrang_cli::{Env, Outcome, run_in};

/// The golden directory of whole-process transcripts. `enrang-suite` reads it too,
/// so a golden here is also a firing fixture and a determinism case: each one runs
/// in any directory, with empty standard input, and fires no code of a milestone
/// above the current one.
pub const SUITE: &str = "cli";

/// The golden directory of what no process can show today.
pub const INPROCESS_SUITE: &str = "cli-inprocess";

/// The golden directory of the whole-process transcripts of `check`, `fmt` and `init`
/// that need a directory holding files, or standard input: each runs in a fresh
/// directory holding the files `project.rs` lists. Those under `initialised/` run in a
/// project that `enrang init` made and hold nothing else, so the gating meta-test runs
/// them again as firing fixtures; the meta-tests only read the others.
pub const PROJECT_SUITE: &str = "cli-project";

/// The golden directory of the rendered output of the anchored compile fixtures in
/// `tests/compile/`, one transcript of `enrang check` per firing fixture.
pub const COMPILE_SUITE: &str = "compile";

/// The codes SPEC 13.2 retired, and why `enrang explain` says each one went,
/// written by hand in code order. Codes are never reused, so each stays answerable.
pub const RETIRED: [(&str, &str); 18] = [
    ("EN0204", "classes may extend a class now; see EN0442"),
    (
        "EN0212",
        "`protected`, `abstract` and `super` are valid now",
    ),
    (
        "EN0217",
        "an object literal without a class is an anonymous object now",
    ),
    ("EN0223", "`x?: T` is valid now, on fields and parameters"),
    (
        "EN0306",
        "user folders have namespaces now; a private item is EN0311",
    ),
    ("EN0407", "object types are valid everywhere now"),
    (
        "EN0431",
        "`length()` is a method now; a bare `.length` is EN0441",
    ),
    ("EN0505", "`match` arms bind no variables now"),
    (
        "EN0620",
        "a method with type parameters of its own is never overridden; an override of one is EN0460",
    ),
    (
        "EN0704",
        "R3's rule 3 with EN0710 and EN0712 covers what it named",
    ),
    (
        "EN0716",
        "`from` is removed; returned-reference sources are inferred",
    ),
    (
        "EN0719",
        "a `for...of` source is locked for the loop; changing it is EN0706",
    ),
    (
        "EN0720",
        "a part of an array is a `&Slice<T>`, and one passed where a growable `&T[]` is expected is EN0401",
    ),
    ("EN0810", "there is one raw pointer kind, `*T`"),
    ("EN1008", "`match` guards and ranges are supported now"),
    (
        "EN1016",
        "default parameters and overloads are supported now",
    ),
    (
        "EN1020",
        "`--float=x87` is accepted; it is the default at `i586` and `i686`",
    ),
    (
        "EN1040",
        "enum cases may carry texts now: `Negative = \"negative age\"`",
    ),
];

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

/// The binary in `dir`, reading `stdin`.
pub fn enrang_fed(dir: &Path, args: &[String], stdin: &[u8]) -> Ran {
    let mut child = Command::new(BIN)
        .args(args)
        .current_dir(dir)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("the binary runs");
    let mut input = child.stdin.take().expect("a pipe");
    input.write_all(stdin).expect("the input is taken");
    drop(input);
    let output = child.wait_with_output().expect("the binary exits");
    Ran {
        stdout: String::from_utf8(output.stdout).expect("stdout is UTF-8"),
        stderr: String::from_utf8(output.stderr).expect("stderr is UTF-8"),
        code: output.status.code().expect("the binary exits normally"),
    }
}

pub fn strings(args: &[&str]) -> Vec<String> {
    args.iter().map(|arg| (*arg).to_owned()).collect()
}

/// The command line in this process, in the working directory, with empty standard
/// input and no colour. The test's own standard input may be a terminal, which `fmt`
/// with no path would wait on.
pub fn inproc(args: &[&str]) -> Outcome {
    inproc_at(Path::new("."), args, b"")
}

/// The command line in this process, in `dir`, reading `stdin`, with no colour.
pub fn inproc_at(dir: &Path, args: &[&str], stdin: &[u8]) -> Outcome {
    run_in(
        &strings(args),
        false,
        &mut Env {
            dir,
            stdin: &mut io::Cursor::new(stdin),
        },
    )
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
