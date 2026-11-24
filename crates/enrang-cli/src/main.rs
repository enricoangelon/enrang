//! The `enrang` binary.

#![forbid(unsafe_code)]

use std::process::ExitCode;

fn main() -> ExitCode {
    enrang_cli::main()
}
