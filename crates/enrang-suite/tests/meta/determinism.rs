//! Two runs of the command line give byte-identical output (ARCHITECTURE 1).
//!
//! Every transcript is a case, so a new golden needs no new line here. Each run is
//! a new process, because that is where a hash seed or an address would differ.

use std::process::Command;

use enrang_testkit::{Harness, TempDir};

use crate::support::{CLI, Golden, finished, golden_args, run_cli, transcripts};

/// Which bytes of two runs differ, if any. It exists so the check itself can be seen
/// to fail on output that does vary.
fn difference(first: &[u8], second: &[u8]) -> Option<usize> {
    if first == second {
        return None;
    }
    let common = first.iter().zip(second).take_while(|(a, b)| a == b).count();
    Some(common)
}

fn assert_identical(golden: &Golden) {
    let args = golden_args(golden).expect("a command line");
    let first = run_cli(&args);
    let second = run_cli(&args);
    assert_eq!(
        difference(first.stdout.as_bytes(), second.stdout.as_bytes()),
        None,
        "stdout of {args:?}"
    );
    assert_eq!(
        difference(first.stderr.as_bytes(), second.stderr.as_bytes()),
        None,
        "stderr of {args:?}"
    );
    assert_eq!(first.code, second.code, "status of {args:?}");

    let (_, claimed) = golden.text.split_once('\n').expect("a body");
    assert_eq!(first.body(), claimed, "the golden of {args:?}");
}

pub fn register(h: &mut Harness) {
    for golden in transcripts() {
        let name = golden.name.clone();
        h.case(format!("determinism/{name}"), move || {
            assert_identical(&golden)
        });
    }
    h.case(
        "determinism/another directory and no environment change nothing",
        || {
            let directory = TempDir::new("determinism");
            for golden in transcripts() {
                let args = golden_args(&golden).expect("a command line");
                let mut command = Command::new(CLI);
                command
                    .args(&args)
                    .env_clear()
                    .current_dir(directory.path());
                let elsewhere = finished(&mut command);
                assert_eq!(elsewhere, run_cli(&args), "{}", golden.name);
            }
        },
    );
    h.case(
        "determinism/a hundred runs of the longest outputs agree",
        || {
            for args in [&["--help"][..], &["targets"], &["targets", "--evidence"]] {
                let args: Vec<String> = args.iter().map(|arg| (*arg).to_owned()).collect();
                let first = run_cli(&args);
                for _ in 0..100 {
                    assert_eq!(run_cli(&args), first, "{args:?}");
                }
            }
        },
    );
    h.case("determinism/the comparison finds a difference", || {
        assert_eq!(difference(b"same", b"same"), None);
        assert_eq!(difference(b"abc", b"abd"), Some(2));
        assert_eq!(difference(b"abc", b"abcd"), Some(3));
        assert_eq!(difference(b"", b"x"), Some(0));
    });
}
