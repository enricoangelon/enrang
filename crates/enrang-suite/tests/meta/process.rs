//! What can be seen only from outside a process: every exit status, and a panic.

use std::fs::OpenOptions;
use std::path::Path;
use std::process::{Command, Stdio};

use enrang_testkit::{Harness, skip};

use crate::support::{CLI, ICE, finished, read, run_cli};

/// A device every write to which fails.
const FULL: &str = "/dev/full";

/// A root file's code, without the doc comments that say which binary it is.
fn code_of(source: &str) -> String {
    source
        .lines()
        .filter(|line| !line.starts_with("//!"))
        .collect::<Vec<_>>()
        .join("\n")
}

pub fn register(h: &mut Harness) {
    h.case("process/the stand-in is the real main", || {
        assert_eq!(
            code_of(&read("crates/enrang-suite/src/bin/enrang-suite-cli.rs")),
            code_of(&read("crates/enrang-cli/src/main.rs"))
        );
    });
    h.case("process/the exit statuses a command gives today", || {
        let args =
            |list: &[&str]| -> Vec<String> { list.iter().map(|a| (*a).to_owned()).collect() };
        assert_eq!(run_cli(&args(&["--version"])).code, 0);
        assert_eq!(run_cli(&args(&["explain", "EN9999"])).code, 2);
        assert_eq!(run_cli(&args(&["build"])).code, 2);
        assert_eq!(run_cli(&args(&["check", "--bogus"])).code, 2);
        assert_eq!(
            run_cli(&args(&["fmt"])).code,
            0,
            "nothing on standard input"
        );
        assert_eq!(finished(&mut Command::new(ICE)).code, 3);
    });
    // Lost output is status 1 whatever the command; `cli-project` shows the others.
    if Path::new(FULL).exists() {
        h.case("process/lost output is exit status 1", || {
            let full = OpenOptions::new().write(true).open(FULL).expect("it opens");
            let mut command = Command::new(CLI);
            let ran = finished(command.arg("--version").stdout(Stdio::from(full)));
            assert_eq!(ran.code, 1, "{ran:?}");
        });
    } else {
        skip(FULL, 1, "no such device on this system");
    }
    h.case("process/a panic reports as an internal error and nothing else", || {
        let ran = finished(&mut Command::new(ICE));
        assert_eq!(ran.code, 3);
        assert_eq!(ran.stdout, "");
        assert_eq!(
            ran.stderr,
            "error: internal compiler error: a deliberate panic\nnote: this is a bug in enrang, not in your command\n"
        );
    });
    h.case(
        "process/a backtrace request changes nothing about a panic",
        || {
            let plain = finished(&mut Command::new(ICE));
            let with = finished(Command::new(ICE).env("RUST_BACKTRACE", "full"));
            assert_eq!(with, plain);
        },
    );
}
