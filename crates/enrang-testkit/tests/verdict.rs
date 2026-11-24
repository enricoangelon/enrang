//! Whether a run reports its failures, judged from outside the harness.
//!
//! Every suite of the workspace runs through `Harness`, whose exit status is what
//! CI sees. The self-tests judge that status through the same harness, and a broken
//! runner cannot vouch for itself (TESTING 10), so a wrong line here could turn CI
//! green for all of them. This file is a plain libtest binary: nothing in it goes
//! through the harness for its own verdict.

#![forbid(unsafe_code)]

use std::env;
use std::io::{self, Write};
use std::process::{Command, ExitCode};
use std::sync::Arc;

use enrang_testkit::{Harness, RunOptions, RunReport, SkipLedger};

/// Selects the role of the child process in the process tests below.
const CHILD: &str = "ENRANG_VERDICT_CHILD";

fn run(build: impl FnOnce(&mut Harness), out: &mut dyn Write) -> RunReport {
    let mut harness = Harness::new("verdict");
    harness.ledger(Arc::new(SkipLedger::new()));
    build(&mut harness);
    harness.run_with(&RunOptions::default(), out)
}

fn report_of(cases: &[(&'static str, bool)]) -> RunReport {
    let cases = cases.to_vec();
    run(
        move |h| {
            for (name, passes) in cases {
                h.case(name, move || if passes { Ok(()) } else { Err("declined") });
            }
        },
        &mut Vec::new(),
    )
}

fn assert_fails(report: &RunReport) {
    assert!(!report.success(), "{report:?}");
    assert_eq!(report.exit_code(), ExitCode::FAILURE, "{report:?}");
}

#[test]
fn a_run_of_passing_cases_succeeds() {
    let report = report_of(&[("good", true), ("also_good", true)]);
    assert!(report.success(), "{report:?}");
    assert_eq!(report.exit_code(), ExitCode::SUCCESS);
    assert_eq!(report.passed, 2);
    assert_eq!(report.failed, Vec::<String>::new());
}

#[test]
fn a_failed_case_fails_the_run() {
    let report = report_of(&[("bad", false)]);
    assert_fails(&report);
    assert_eq!(report.failed, ["bad"]);
}

#[test]
fn one_failed_case_among_many_fails_the_run() {
    let report = report_of(&[("good", true), ("bad", false), ("also_good", true)]);
    assert_fails(&report);
    assert_eq!(report.passed, 2);
    assert_eq!(report.failed, ["bad"]);
}

#[test]
fn a_panicking_case_fails_the_run() {
    let report = run(
        |h| h.case("panics", || -> () { panic!("a panic in a case") }),
        &mut Vec::new(),
    );
    assert_fails(&report);
    assert_eq!(report.failed, ["panics"]);
}

#[test]
fn an_empty_suite_fails_the_run() {
    let report = report_of(&[]);
    assert!(report.no_cases);
    assert_fails(&report);
}

/// Each cause of failure alone, with every other field as a clean run leaves it.
#[test]
fn each_cause_of_failure_fails_the_report_alone() {
    let clean = RunReport {
        total: 1,
        passed: 1,
        ..RunReport::default()
    };
    assert!(clean.success());
    assert_eq!(clean.exit_code(), ExitCode::SUCCESS);
    let causes = [
        RunReport {
            failed: vec!["bad".to_owned()],
            ..clean.clone()
        },
        RunReport {
            required_skips: vec!["SKIP as not found: 1 test not run".to_owned()],
            ..clean.clone()
        },
        RunReport {
            orphans: vec!["tests/golden/s/forgotten.txt".to_owned()],
            ..clean.clone()
        },
        RunReport {
            over_budget: true,
            ..clean.clone()
        },
        RunReport {
            no_cases: true,
            ..clean.clone()
        },
    ];
    for cause in &causes {
        assert_fails(cause);
    }
}

/// A writer like a closed pipe.
struct Refuses;

impl Write for Refuses {
    fn write(&mut self, _: &[u8]) -> io::Result<usize> {
        Err(io::ErrorKind::BrokenPipe.into())
    }

    fn flush(&mut self) -> io::Result<()> {
        Err(io::ErrorKind::BrokenPipe.into())
    }
}

#[test]
fn a_closed_output_does_not_change_the_verdict() {
    let bad = run(|h| h.case("bad", || Err::<(), _>("declined")), &mut Refuses);
    assert_eq!(bad.failed, ["bad"]);
    assert_fails(&bad);
    let good = run(|h| h.case("good", || ()), &mut Refuses);
    assert_eq!(good.passed, 1);
    assert_eq!(good.exit_code(), ExitCode::SUCCESS);
}

/// What `Harness::run` does, the way a suite's `main` uses it. A libtest test may
/// return an exit code, which libtest turns into its own status, so a real process
/// shows the status from outside. The harness reads this process's arguments, so its
/// one case has the name of the test that `--exact` selects.
#[test]
fn a_process_exits_as_its_harness_says() -> ExitCode {
    const NAME: &str = "a_process_exits_as_its_harness_says";
    if let Ok(role) = env::var(CHILD) {
        let mut harness = Harness::new("verdict-child");
        harness.ledger(Arc::new(SkipLedger::new()));
        harness.case(NAME, move || {
            if role == "pass" {
                Ok(())
            } else {
                Err("declined")
            }
        });
        return harness.run();
    }
    let status = |role: &str| {
        Command::new(env::current_exe().expect("the test binary has a path"))
            .args(["--exact", NAME, "--nocapture"])
            .env(CHILD, role)
            .output()
            .expect("the test binary runs itself")
    };
    let passing = status("pass");
    let failing = status("fail");
    assert!(
        passing.status.success(),
        "{}",
        String::from_utf8_lossy(&passing.stdout)
    );
    assert!(
        !failing.status.success(),
        "{}",
        String::from_utf8_lossy(&failing.stdout)
    );
    let printed = String::from_utf8_lossy(&failing.stdout);
    assert!(printed.contains("test result: FAILED."), "{printed}");
    ExitCode::SUCCESS
}
