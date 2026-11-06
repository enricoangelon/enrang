//! What a run of the command line prints and returns.

use std::io::{self, Write};

use enrang_diag::shown;

/// Exit statuses (SPEC 13.2).
pub const EXIT_SUCCESS: u8 = 0;
pub const EXIT_FAILURE: u8 = 1;
pub const EXIT_USAGE: u8 = 2;
pub const EXIT_INTERNAL: u8 = 3;

/// The two streams and the exit status of a run.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Outcome {
    pub stdout: String,
    pub stderr: String,
    pub code: u8,
}

impl Outcome {
    /// A success that prints `stdout`.
    pub(crate) fn print(stdout: String) -> Outcome {
        Outcome {
            stdout,
            stderr: String::new(),
            code: EXIT_SUCCESS,
        }
    }

    /// A failure that reports `stderr`.
    pub(crate) fn fail(stderr: String, code: u8) -> Outcome {
        Outcome {
            stdout: String::new(),
            stderr,
            code,
        }
    }

    /// The report of a bug in the compiler.
    pub fn internal(message: &str) -> Outcome {
        Outcome::fail(
            format!(
                "error: internal compiler error: {}\nnote: this is a bug in enrang, not in your command\n",
                shown(message)
            ),
            EXIT_INTERNAL,
        )
    }

    /// Writes both streams and returns the exit status. A reader that went away, as
    /// in `enrang targets | head -n 1`, is no failure. Any other lost output is one:
    /// a run must not report success for output nobody got. A run that already failed
    /// keeps its status (SPEC 13.2).
    pub fn emit(&self, stdout: &mut dyn Write, stderr: &mut dyn Write) -> u8 {
        let mut code = self.code;
        if let Err(error) = write_flushed(stdout, &self.stdout)
            && error.kind() != io::ErrorKind::BrokenPipe
        {
            let _ = writeln!(stderr, "error: cannot write to stdout: {error}");
            if code == EXIT_SUCCESS {
                code = EXIT_FAILURE;
            }
        }
        if let Err(error) = write_flushed(stderr, &self.stderr)
            && error.kind() != io::ErrorKind::BrokenPipe
            && code == EXIT_SUCCESS
        {
            code = EXIT_FAILURE;
        }
        code
    }
}

fn write_flushed(out: &mut dyn Write, text: &str) -> io::Result<()> {
    out.write_all(text.as_bytes())?;
    out.flush()
}
