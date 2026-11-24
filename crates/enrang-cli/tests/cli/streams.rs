//! What reaches each stream, and what the process does when a stream misbehaves.

use std::fs::OpenOptions;
use std::io::{self, Write};
use std::path::Path;
use std::process::{Command, Stdio};
use std::sync::Arc;

use enrang_cli::{EXIT_FAILURE, EXIT_INTERNAL, EXIT_SUCCESS, EXIT_USAGE, Outcome, run};
use enrang_testkit::{
    Harness, RunOptions, SkipLedger, TempDir, ToolPath, global_ledger, golden, tool,
};

use crate::support::{BIN, INPROCESS_SUITE, Ran, enrang, finished, inproc, strings};

/// A writer that fails every write the same way, recording what it was given.
struct Broken(io::ErrorKind);

impl Write for Broken {
    fn write(&mut self, _: &[u8]) -> io::Result<usize> {
        Err(self.0.into())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// A writer that takes every write and fails when it is flushed.
struct FailsOnFlush;

impl Write for FailsOnFlush {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Err(io::Error::from(io::ErrorKind::StorageFull))
    }
}

fn outcome(stdout: &str, stderr: &str, code: u8) -> Outcome {
    Outcome {
        stdout: stdout.to_owned(),
        stderr: stderr.to_owned(),
        code,
    }
}

/// Makes ANSI escapes visible in a golden, which stays reviewable text.
fn visible(text: &str) -> String {
    text.replace('\x1b', "<ESC>")
}

pub(crate) fn without_escapes(text: &str) -> String {
    let mut out = String::new();
    let mut rest = text;
    while let Some(start) = rest.find('\x1b') {
        out.push_str(&rest[..start]);
        let tail = &rest[start..];
        let end = tail.find('m').expect("an escape ends in m");
        rest = &tail[end + 1..];
    }
    out.push_str(rest);
    out
}

pub fn register(h: &mut Harness) {
    h.case(
        "streams/the exit statuses are the numbers of SPEC 13.2",
        || {
            assert_eq!(
                [EXIT_SUCCESS, EXIT_FAILURE, EXIT_USAGE, EXIT_INTERNAL],
                [0, 1, 2, 3]
            );
        },
    );
    let statuses: &[(&[&str], u8)] = &[
        (&["--help"], 0),
        (&["--version"], 0),
        (&["explain", "EN1301"], 0),
        (&["explain", "EN0601"], 0),
        (&["targets"], 0),
        (&["targets", "--evidence"], 0),
        (&["explain", "EN9999"], 2),
        (&["explain", "EN0704"], 2),
        (&["explain", "en1301"], 2),
        (&["explain", ""], 2),
        (&[], 2),
        (&["explain"], 2),
        (&["targets", "x"], 2),
        (&["lsp"], 2),
        (&["fmt", "--help"], 0),
        (&["check", "--help"], 0),
        (&["init", "--help"], 0),
        (&["check", "--bogus"], 2),
        (&["init", "--kernel"], 2),
        (&["tsc"], 2),
        (&["build"], 2),
        (&["frobnicate"], 2),
    ];
    for (args, status) in statuses {
        let (args, status) = (*args, *status);
        h.case(format!("streams/{args:?} exits {status}"), move || {
            let ran = enrang(&strings(args));
            assert_eq!(ran.code, i32::from(status), "{ran:?}");
            if status == 0 {
                assert!(!ran.stdout.is_empty(), "{ran:?}");
                assert_eq!(ran.stderr, "");
            } else {
                assert_eq!(ran.stdout, "");
                assert!(!ran.stderr.is_empty(), "{ran:?}");
            }
        });
    }

    h.case("streams/a pipe gets no colour", || {
        let ran = enrang(&strings(&["lsp"]));
        assert!(!ran.stderr.contains('\x1b'), "{:?}", ran.stderr);
    });
    let environments: &[(&str, &str)] = &[
        ("CLICOLOR_FORCE", "1"),
        ("TERM", "xterm-256color"),
        ("NO_COLOR", "1"),
        ("LANG", "it_IT.UTF-8"),
        ("LC_ALL", "C"),
        ("RUST_BACKTRACE", "full"),
        ("COLUMNS", "20"),
        ("ENRANG_BLESS", "1"),
    ];
    for (name, value) in environments {
        let (name, value) = (*name, *value);
        h.case(
            format!("streams/{name}={value} changes nothing"),
            move || {
                for args in [
                    &["--help"][..],
                    &["lsp"],
                    &["explain", "EN0601"],
                    &["targets"],
                ] {
                    let args = strings(args);
                    let mut command = Command::new(BIN);
                    let with = finished(command.args(&args).env(name, value));
                    assert_eq!(with, enrang(&args), "{args:?}");
                }
            },
        );
    }
    h.case("streams/an empty environment changes nothing", || {
        for args in [&["--help"][..], &["tsc"], &["targets", "--evidence"]] {
            let args = strings(args);
            let mut command = Command::new(BIN);
            let bare = finished(command.args(&args).env_clear());
            assert_eq!(bare, enrang(&args), "{args:?}");
        }
    });
    h.case("streams/the working directory changes nothing", || {
        let directory = TempDir::new("cwd");
        for args in [&["--help"][..], &["build", "main.en"], &["targets"]] {
            let args = strings(args);
            let mut command = Command::new(BIN);
            let elsewhere = finished(command.args(&args).current_dir(directory.path()));
            assert_eq!(elsewhere, enrang(&args), "{args:?}");
        }
    });

    h.case("colour/stripping the escapes gives the plain text", || {
        for args in [&["lsp"][..], &["tsc"], &["frobnicate"]] {
            let args = strings(args);
            let painted = run(&args, true);
            let plain = run(&args, false);
            assert!(painted.stderr.contains('\x1b'), "{args:?}");
            assert_eq!(without_escapes(&painted.stderr), plain.stderr, "{args:?}");
            assert_eq!(painted.code, plain.code);
        }
    });
    h.case("colour/what is not a diagnostic never has it", || {
        for args in [
            &["--help"][..],
            &["--version"],
            &["explain", "EN1301"],
            &["explain", "EN0601"],
            &["explain", "EN9999"],
            &["targets"],
            &["targets", "--evidence"],
            &["build"],
            &[],
        ] {
            let args = strings(args);
            assert_eq!(run(&args, true), run(&args, false), "{args:?}");
        }
    });
    for (file, args) in [
        ("color/deferred.txt", &["lsp"][..]),
        ("color/alias.txt", &["tsc"]),
        ("color/unknown.txt", &["buidl"]),
    ] {
        h.case(format!("golden/{file}"), move || {
            let painted = run(&strings(args), true);
            golden(INPROCESS_SUITE, file, &visible(&painted.stderr))
        });
    }

    h.case("emit/both streams are written in full", || {
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();
        let code = outcome("out\n", "err\n", 7).emit(&mut stdout, &mut stderr);
        assert_eq!(code, 7);
        assert_eq!(stdout, b"out\n");
        assert_eq!(stderr, b"err\n");
    });
    h.case("emit/a reader that went away is no failure", || {
        let mut stderr = Vec::new();
        let mut gone = Broken(io::ErrorKind::BrokenPipe);
        let code = outcome("lost\n", "", 0).emit(&mut gone, &mut stderr);
        assert_eq!(code, 0);
        assert_eq!(stderr, b"");
    });
    h.case("emit/other lost output turns success into failure", || {
        let mut stderr = Vec::new();
        let mut full = Broken(io::ErrorKind::StorageFull);
        let code = outcome("lost\n", "", 0).emit(&mut full, &mut stderr);
        assert_eq!(code, 1);
        let text = String::from_utf8(stderr).expect("UTF-8");
        assert!(
            text.starts_with("error: cannot write to stdout: "),
            "{text}"
        );
    });
    h.case("emit/a failed flush is lost output too", || {
        let mut stderr = Vec::new();
        let code = outcome("x\n", "", 0).emit(&mut FailsOnFlush, &mut stderr);
        assert_eq!(code, 1);
        let text = String::from_utf8(stderr).expect("UTF-8");
        assert!(
            text.starts_with("error: cannot write to stdout: "),
            "{text}"
        );
    });
    h.case("golden/write_failure.txt", || {
        let mut stderr = Vec::new();
        let mut denied = Broken(io::ErrorKind::PermissionDenied);
        outcome("lost\n", "", 0).emit(&mut denied, &mut stderr);
        let text = String::from_utf8(stderr).expect("UTF-8");
        golden(INPROCESS_SUITE, "write_failure.txt", &text)
    });
    h.case("emit/lost output never hides a worse status", || {
        for status in [EXIT_FAILURE, EXIT_USAGE, EXIT_INTERNAL] {
            let mut stderr = Vec::new();
            let mut full = Broken(io::ErrorKind::StorageFull);
            let code = outcome("lost\n", "the report\n", status).emit(&mut full, &mut stderr);
            assert_eq!(code, status);
            let text = String::from_utf8(stderr).expect("UTF-8");
            assert!(text.ends_with("the report\n"), "{text}");
        }
    });
    h.case(
        "emit/a report lost on a successful run is a failure",
        || {
            let mut stdout = Vec::new();
            let mut full = Broken(io::ErrorKind::StorageFull);
            let code = outcome("kept\n", "warning\n", EXIT_SUCCESS).emit(&mut stdout, &mut full);
            assert_eq!(code, EXIT_FAILURE);
        },
    );
    h.case("emit/a reader that left stderr is no failure", || {
        let mut stdout = Vec::new();
        let mut gone = Broken(io::ErrorKind::BrokenPipe);
        let code = outcome("kept\n", "warning\n", EXIT_SUCCESS).emit(&mut stdout, &mut gone);
        assert_eq!(code, EXIT_SUCCESS);
    });
    h.case("emit/a broken stderr changes no status", || {
        let mut stdout = Vec::new();
        let mut broken = Broken(io::ErrorKind::BrokenPipe);
        let code = outcome("kept\n", "lost\n", 2).emit(&mut stdout, &mut broken);
        assert_eq!(code, 2);
        assert_eq!(stdout, b"kept\n");
    });

    full_disk_case(h, "/dev/full", &global_ledger());
    h.case(
        "skip/a missing device registers no case and notes a skip",
        || {
            let ledger = SkipLedger::new();
            let mut inner = Harness::new("inner");
            full_disk_case(&mut inner, "/dev/enrang-no-such-device", &ledger);
            assert_eq!(inner.len(), 0, "a skipped case is never counted as passed");
            assert_eq!(
                ledger.lines(),
                ["SKIP /dev/enrang-no-such-device no such device on this system: 1 test not run"]
            );
        },
    );
    h.case("skip/a device that exists registers its case", || {
        let ledger = SkipLedger::new();
        let mut inner = Harness::new("inner");
        inner.ledger(Arc::new(SkipLedger::new()));
        full_disk_case(&mut inner, "/dev/null", &ledger);
        assert_eq!(inner.len(), 1);
        assert_eq!(ledger.total_tests(), 0);
        // `/dev/null` takes the output, so this one reports what the real case fails on.
        let mut out = Vec::new();
        let report = inner.run_with(&RunOptions::default(), &mut out);
        assert_eq!(report.failed.len(), 1, "{}", String::from_utf8_lossy(&out));
    });
    h.case("process/a bidi override in an argument is escaped", || {
        let ran = enrang(&strings(&["\u{202e}evil"]));
        assert_eq!(ran.code, 2, "{ran:?}");
        assert!(!ran.stderr.contains('\u{202e}'), "{ran:?}");
        assert!(
            ran.stderr.starts_with("error[EN1302]: `\\u{202e}evil` "),
            "{ran:?}"
        );
    });
    h.case("process/a line separator in an argument is escaped", || {
        let ran = enrang(&strings(&["a\u{2028}b"]));
        assert!(!ran.stderr.contains('\u{2028}'), "{ran:?}");
        assert!(
            ran.stderr.starts_with("error[EN1302]: `a\\u{2028}b` "),
            "{ran:?}"
        );
    });
    h.case("process/a closed stdout and stderr do not panic", || {
        let status = Command::new(BIN)
            .arg("--help")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .expect("it runs");
        assert_eq!(status.code(), Some(0));
    });
    h.case(
        "process/a reader that closes the pipe at once is no failure",
        || {
            for args in [&["--help"][..], &["targets"], &["targets", "--evidence"]] {
                let mut child = Command::new(BIN)
                    .args(args)
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped())
                    .spawn()
                    .expect("it runs");
                drop(child.stdout.take());
                let output = child.wait_with_output().expect("it finishes");
                assert_eq!(output.status.code(), Some(0), "{args:?}");
                assert_eq!(String::from_utf8_lossy(&output.stderr), "", "{args:?}");
            }
        },
    );
    register_non_unicode(h);
    terminal_cases(h);

    h.case("inproc/no arguments is a usage error naming the way out", || {
        let outcome = inproc(&[]);
        assert_eq!(outcome.code, EXIT_USAGE);
        assert_eq!(
            outcome.stderr,
            "error: no command given\nhelp: run `enrang --help` to see the commands\nusage: enrang <command> [arguments]\n"
        );
    });
}

/// The case that needs a full disk, or a note that it cannot run: decided here, so
/// that a skipped case is never counted as passed (TESTING 20).
fn full_disk_case(h: &mut Harness, device: &'static str, ledger: &SkipLedger) {
    if !Path::new(device).exists() {
        ledger.record(device, 1, "no such device on this system");
        return;
    }
    h.case(
        "process/a full disk is a failure with a message",
        move || {
            let full = OpenOptions::new()
                .write(true)
                .open(device)
                .expect("it opens");
            let mut command = Command::new(BIN);
            let ran = finished(command.args(["--help"]).stdout(Stdio::from(full)));
            assert_eq!(ran.code, 1, "{ran:?}");
            assert!(
                ran.stderr.starts_with("error: cannot write to stdout: "),
                "{ran:?}"
            );
        },
    );
}

#[cfg(unix)]
fn register_non_unicode(h: &mut Harness) {
    use std::ffi::OsStr;
    use std::os::unix::ffi::OsStrExt;

    h.case(
        "process/an argument that is not Unicode is an unknown name",
        || {
            let mut command = Command::new(BIN);
            let ran = finished(command.arg(OsStr::from_bytes(b"bu\xffild")));
            assert_eq!(ran.code, 2, "{ran:?}");
            assert_eq!(
                ran.stderr.lines().next(),
                Some("error[EN1302]: `bu\u{fffd}ild` is not an `enrang` command"),
                "{ran:?}"
            );
            let mut explain = Command::new(BIN);
            let ran = finished(explain.arg("explain").arg(OsStr::from_bytes(b"\xff\xfe")));
            assert_eq!(ran.code, 2, "{ran:?}");
            assert!(ran.stderr.contains("is not a diagnostic code"), "{ran:?}");
        },
    );
}

#[cfg(not(unix))]
fn register_non_unicode(_: &mut Harness) {
    enrang_testkit::skip("unix", 1, "non-Unicode arguments are only built on unix");
}

/// `script`, if it is here and can give a command a pseudo-terminal. BSD's has other
/// flags, and a sandbox may have no pseudo-terminals, and each shows here.
fn working_script() -> Option<ToolPath> {
    let script = tool("script")?;
    let status = script
        .command()
        .args(["-qec", "exit 7", "/dev/null"])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status();
    status
        .is_ok_and(|status| status.code() == Some(7))
        .then_some(script)
}

/// Runs a shell line with its streams on a pseudo-terminal, unless it redirects them,
/// and returns what the terminal showed, in the line endings a pipe would have.
fn on_terminal(script: &ToolPath, line: &str) -> Ran {
    let mut command = script.command();
    command
        .args(["-qec", line, "/dev/null"])
        .stdin(Stdio::null());
    let mut ran = finished(&mut command);
    ran.stdout = ran.stdout.replace("\r\n", "\n");
    ran
}

/// SPEC 13.1: colour needs a terminal, and a diagnostic goes to stderr, so stderr is
/// the stream that decides. Nothing else may decide, so `NO_COLOR` changes nothing
/// here either, as it changes nothing on a pipe: SPEC 13.1 does not name it, and the
/// command line reads no environment.
fn terminal_cases(h: &mut Harness) {
    const CASES: usize = 5;
    let Some(script) = working_script() else {
        global_ledger().record("script", CASES, "cannot give a command a pseudo-terminal");
        return;
    };
    let plain = run(&strings(&["lsp"]), false).stderr;
    let environments: [(&str, &str); 3] = [
        ("with stderr on a terminal", ""),
        ("whatever NO_COLOR says", "NO_COLOR=1 "),
        ("whatever TERM says", "TERM=dumb "),
    ];
    for (name, prefix) in environments {
        let (script, plain) = (script.clone(), plain.clone());
        h.case(
            format!("terminal/a diagnostic is painted {name}"),
            move || {
                let ran = on_terminal(&script, &format!("{prefix}'{BIN}' lsp >/dev/null"));
                assert_eq!(ran.code, 2, "{ran:?}");
                assert!(ran.stdout.contains('\x1b'), "{ran:?}");
                assert_eq!(without_escapes(&ran.stdout), plain);
            },
        );
    }
    {
        let (script, plain) = (script.clone(), plain.clone());
        h.case("terminal/stdout on a terminal paints nothing", move || {
            let directory = TempDir::new("terminal");
            let file = directory.join("stderr");
            let line = format!("'{BIN}' lsp 2>'{}'", file.display());
            let ran = on_terminal(&script, &line);
            assert_eq!(ran.code, 2, "{ran:?}");
            let written = std::fs::read_to_string(file).expect("the redirection wrote it");
            assert_eq!(written, plain);
        });
    }
    h.case(
        "terminal/a diagnostic is painted with both streams on a terminal",
        move || {
            let ran = on_terminal(&script, &format!("'{BIN}' lsp"));
            assert_eq!(ran.code, 2, "{ran:?}");
            assert!(ran.stdout.contains('\x1b'), "{ran:?}");
        },
    );
}
