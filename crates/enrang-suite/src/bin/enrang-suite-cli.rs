//! The `enrang` binary, under a name the meta-tests' package can build.

#![forbid(unsafe_code)]

use std::process::ExitCode;

fn main() -> ExitCode {
    enrang_cli::main()
}
