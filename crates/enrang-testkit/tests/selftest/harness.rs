//! The harness: counts, verdicts, filters, determinism, and panics caught per case.

use std::collections::BTreeSet;
use std::panic;
use std::process::ExitCode;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use enrang_testkit::{
    GoldenDiff, GoldenFailure, Harness, IntoOutcome, RunOptions, SkipLedger, catch_panic, golden,
    workspace_root,
};

use crate::support::{child, last_line, run_harness};

fn options() -> RunOptions {
    RunOptions::default()
}

fn args(list: &[&str]) -> Vec<String> {
    list.iter().map(|&arg| arg.to_owned()).collect()
}

const NAMES: [&str; 5] = ["prng::a", "prng::b", "golden::a", "golden::b::c", "skip"];

/// Runs passing cases named `NAMES` and returns the names that ran.
fn run_names(options: &RunOptions) -> Vec<String> {
    let ran = Arc::new(Mutex::new(Vec::new()));
    let log = Arc::clone(&ran);
    let (report, _) = run_harness(
        move |h| {
            for name in NAMES {
                let log = Arc::clone(&log);
                h.case(name, move || log.lock().unwrap().push(name.to_owned()));
            }
        },
        options,
    );
    assert!(report.success(), "{report:?}");
    let mut names = ran.lock().unwrap().clone();
    assert_eq!(report.passed, names.len());
    assert_eq!(report.filtered, NAMES.len() - names.len());
    names.sort();
    names
}

/// Twenty-four cases that finish out of order, some failing, for a given thread count.
fn scrambled_output(threads: usize) -> String {
    let (_, output) = run_harness(
        |h| {
            for index in 0..24u64 {
                h.case(format!("case_{index:02}"), move || {
                    thread::sleep(Duration::from_micros((24 - index) * 200));
                    if index % 5 == 0 {
                        Err(format!("case {index} declined"))
                    } else {
                        Ok(())
                    }
                });
            }
        },
        &RunOptions {
            threads,
            ..options()
        },
    );
    output
}

/// Recurses until 4 MiB of stack is in use, which is measured rather than assumed
/// because frame sizes depend on the build. A default spawned thread has only 2 MiB.
fn burn_stack(start: usize) -> usize {
    let frame = [1u8; 1024];
    let here = std::hint::black_box(&frame) as *const [u8; 1024] as usize;
    if start.abs_diff(here) >= 4 * 1024 * 1024 {
        return usize::from(frame[0]);
    }
    burn_stack(start) + usize::from(frame[1023])
}

fn start_burning_stack() -> usize {
    let marker = 0u8;
    burn_stack(std::hint::black_box(&marker) as *const u8 as usize)
}

pub fn register(h: &mut Harness) {
    register_verdicts(h);
    register_filters(h);
    register_options(h);
    register_parallel(h);
    register_panics(h);
    register_budget(h);
    register_children(h);
}

fn register_verdicts(h: &mut Harness) {
    // Passing, failing by panic, failing by `Err`.
    let counts: &[(usize, usize, usize)] = &[
        (1, 0, 0),
        (3, 0, 0),
        (0, 1, 0),
        (0, 0, 1),
        (2, 1, 1),
        (5, 3, 2),
        (0, 4, 4),
    ];
    for &(passing, panicking, erring) in counts {
        h.case(format!("harness::counts::{passing}+{panicking}+{erring}"), move || {
            let (report, output) = run_harness(
                |h| {
                    for index in 0..passing {
                        h.case(format!("ok{index}"), || ());
                    }
                    for index in 0..panicking {
                        h.case(format!("panic{index}"), || -> () { panic!("boom") });
                    }
                    for index in 0..erring {
                        h.case(format!("err{index}"), || Err::<(), _>("no"));
                    }
                },
                &options(),
            );
            let total = passing + panicking + erring;
            let failed = panicking + erring;
            assert_eq!(report.total, total);
            assert_eq!(report.passed, passing);
            assert_eq!(report.failed.len(), failed);
            assert_eq!(report.success(), failed == 0);
            let verdict = if failed == 0 { "ok" } else { "FAILED" };
            assert_eq!(
                last_line(&output),
                format!(
                    "test result: {verdict}. {passing} passed; {failed} failed; 0 filtered out; {total} total; 0 tests skipped"
                )
            );
            assert!(
                output.starts_with(&format!("running {total} cases of suite demo ({total} total, 0 filtered out)")),
                "{output}"
            );
        });
    }
    h.case("harness::exit_code_follows_the_verdict", || {
        let (good, _) = run_harness(|h| h.case("a", || ()), &options());
        let (bad, _) = run_harness(|h| h.case("a", || -> () { panic!("no") }), &options());
        assert_eq!(good.exit_code(), ExitCode::SUCCESS);
        assert_eq!(bad.exit_code(), ExitCode::FAILURE);
    });
    h.case("harness::failure_text_reaches_the_report", || {
        let (report, output) = run_harness(
            |h| h.case("the_case", || Err::<(), _>("the reason")),
            &options(),
        );
        assert_eq!(report.failed, ["the_case"]);
        assert!(output.contains("test the_case ... FAILED"), "{output}");
        assert!(
            output.contains("---- the_case ----\nthe reason\n"),
            "{output}"
        );
        assert!(output.contains("failed cases:\n    the_case\n"), "{output}");
    });
    h.case("harness::a_failure_names_the_seed_and_scale", || {
        let (_, output) = run_harness(
            |h| h.case("a", || -> () { panic!("no") }),
            &RunOptions {
                seed: 987,
                scale: 10,
                ..options()
            },
        );
        assert!(
            output.contains("ENRANG_SEED=987 ENRANG_SCALE=10"),
            "{output}"
        );
    });
    h.case("harness::passing_runs_do_not_print_a_reproduction", || {
        let (_, output) = run_harness(|h| h.case("a", || ()), &options());
        assert!(!output.contains("reproduce"), "{output}");
        assert!(!output.contains("failures:"), "{output}");
    });
    h.case("harness::an_empty_suite_fails", || {
        let (report, output) = run_harness(|_| (), &options());
        assert!(!report.success());
        assert!(report.no_cases);
        assert!(output.contains("no cases registered"), "{output}");
        assert!(
            last_line(&output).starts_with("test result: FAILED."),
            "{output}"
        );
    });
    h.case("harness::a_filter_may_explain_an_empty_run", || {
        let (report, output) = run_harness(
            |_| (),
            &RunOptions {
                filters: args(&["x"]),
                ..options()
            },
        );
        assert!(report.success(), "{output}");
    });
    h.case(
        "harness::a_filter_matching_nothing_passes_and_shows_the_total",
        || {
            let (report, output) = run_harness(
                |h| {
                    h.case("a", || ());
                    h.case("b", || ());
                },
                &RunOptions {
                    filters: args(&["nothing"]),
                    ..options()
                },
            );
            assert!(report.success());
            assert_eq!(report.passed, 0);
            assert_eq!(
                last_line(&output),
                "test result: ok. 0 passed; 0 failed; 2 filtered out; 2 total; 0 tests skipped"
            );
        },
    );
    h.case("harness::a_name_can_be_registered_once", || {
        let mut harness = Harness::new("demo");
        harness.case("twin", || ());
        let message = catch_panic(move || harness.case("twin", || ())).expect("it must panic");
        assert!(message.contains("duplicate case name `twin`"), "{message}");
    });
    h.case("harness::len_counts_registrations", || {
        let mut harness = Harness::new("demo");
        assert!(harness.is_empty());
        harness.case("a", || ());
        harness.case("b", || ());
        assert_eq!(harness.len(), 2);
        assert!(!harness.is_empty());
    });
    h.case("harness::output_names_no_time_and_no_absolute_path", || {
        let (_, output) = run_harness(
            |h| {
                h.case("a", || ());
                h.case("b", || -> () { panic!("no") });
            },
            &options(),
        );
        assert!(!output.contains("finished in"), "{output}");
        assert!(!output.contains(" s\n"), "{output}");
        let root = workspace_root();
        assert!(!output.contains(root.to_str().unwrap()), "{output}");
    });
    h.case("harness::skips_are_counted_and_printed_last", || {
        let ledger = Arc::new(SkipLedger::new());
        ledger.record("OVMF", 40, "not found");
        let mut harness = Harness::new("demo");
        harness.ledger(ledger);
        harness.case("a", || ());
        let mut out = Vec::new();
        let report = harness.run_with(&options(), &mut out);
        let output = String::from_utf8(out).unwrap();
        assert!(report.success());
        assert_eq!(report.tests_skipped, 40);
        assert!(
            output.contains("SKIP OVMF not found: 40 tests not run\n"),
            "{output}"
        );
        assert!(last_line(&output).ends_with("40 tests skipped"), "{output}");
    });
    h.case("harness::real_golden::output_of_a_mixed_run", || {
        let ledger = Arc::new(SkipLedger::new());
        ledger.record_oracle("as", 2, "not found");
        let mut harness = Harness::new("demo");
        harness.ledger(ledger);
        harness.case("first", || ());
        harness.case("second", || Err::<(), _>("it broke"));
        harness.case("third", || ());
        harness.case("not_selected", || ());
        let mut out = Vec::new();
        let run = RunOptions {
            seed: 7,
            skips: args(&["not_selected"]),
            ..options()
        };
        harness.run_with(&run, &mut out);
        golden(
            "testkit",
            "harness_output.txt",
            &String::from_utf8(out).unwrap(),
        )
    });
    h.case("harness::outcome::unit_passes", || {
        assert_eq!(().into_outcome(), Ok(()));
    });
    h.case("harness::outcome::ok_passes", || {
        assert_eq!(Ok::<(), String>(()).into_outcome(), Ok(()));
    });
    h.case("harness::outcome::err_fails_with_its_text", || {
        assert_eq!(Err::<(), _>("why").into_outcome(), Err("why".to_owned()));
    });
    h.case(
        "harness::outcome::a_golden_diff_fails_with_its_report",
        || {
            let diff = GoldenDiff {
                path: "tests/golden/s/n".to_owned(),
                failure: GoldenFailure::Mismatch,
                detail: "the diff\n".to_owned(),
            };
            let text = Err::<(), _>(diff).into_outcome().unwrap_err();
            assert!(text.contains("tests/golden/s/n"), "{text}");
        },
    );
}

fn register_filters(h: &mut Harness) {
    // Filters, skips, exact, and the names that must run.
    let table: &[(&[&str], &[&str], bool, &[&str])] = &[
        (
            &[],
            &[],
            false,
            &["golden::a", "golden::b::c", "prng::a", "prng::b", "skip"],
        ),
        (&["prng"], &[], false, &["prng::a", "prng::b"]),
        (&["golden::a"], &[], false, &["golden::a"]),
        (&["::a"], &[], false, &["golden::a", "prng::a"]),
        (
            &["prng", "skip"],
            &[],
            false,
            &["prng::a", "prng::b", "skip"],
        ),
        (&["b"], &[], false, &["golden::b::c", "prng::b"]),
        (&[], &["golden"], false, &["prng::a", "prng::b", "skip"]),
        (&["prng"], &["::b"], false, &["prng::a"]),
        (&[], &["golden", "prng"], false, &["skip"]),
        (&["prng::a"], &[], true, &["prng::a"]),
        (&["prng"], &[], true, &[]),
        (&["prng::a", "skip"], &[], true, &["prng::a", "skip"]),
        (&["prng::a"], &["prng"], true, &[]),
        (&["nothing"], &[], false, &[]),
        (&["PRNG"], &[], false, &[]),
    ];
    for (index, &(filters, skips, exact, expected)) in table.iter().enumerate() {
        h.case(format!("harness::filter[{index}]"), move || {
            let ran = run_names(&RunOptions {
                filters: args(filters),
                skips: args(skips),
                exact,
                ..options()
            });
            assert_eq!(ran, expected);
        });
    }
    h.case("harness::list::runs_nothing_and_counts", || {
        let ran = Arc::new(AtomicUsize::new(0));
        let log = Arc::clone(&ran);
        let (report, output) = run_harness(
            move |h| {
                for name in ["a", "b", "c"] {
                    let log = Arc::clone(&log);
                    h.case(name, move || {
                        log.fetch_add(1, Ordering::Relaxed);
                    });
                }
            },
            &RunOptions {
                list: true,
                skips: args(&["c"]),
                ..options()
            },
        );
        assert_eq!(ran.load(Ordering::Relaxed), 0);
        assert_eq!(output, "a: test\nb: test\n\n2 cases\n");
        assert!(report.success());
    });
    h.case("harness::quiet::hides_passes_but_not_failures", || {
        let (_, output) = run_harness(
            |h| {
                h.case("good", || ());
                h.case("bad", || -> () { panic!("no") });
            },
            &RunOptions {
                quiet: true,
                ..options()
            },
        );
        assert!(!output.contains("test good"), "{output}");
        assert!(output.contains("test bad ... FAILED"), "{output}");
    });
}

fn register_options(h: &mut Harness) {
    let parsed: &[(&[&str], fn(&RunOptions) -> bool)] = &[
        (&[], |o| *o == RunOptions::default()),
        (&["abc"], |o| o.filters == ["abc"]),
        (&["a", "b"], |o| o.filters == ["a", "b"]),
        (&["a=b"], |o| o.filters == ["a=b"]),
        (&["--exact"], |o| o.exact),
        (&["--list"], |o| o.list),
        (&["--quiet"], |o| o.quiet),
        (&["-q"], |o| o.quiet),
        (&["--nocapture"], |o| *o == RunOptions::default()),
        (&["--skip", "x"], |o| {
            o.skips == ["x"] && o.filters.is_empty()
        }),
        (&["--skip=x"], |o| o.skips == ["x"]),
        (&["--skip=x", "--skip", "y"], |o| o.skips == ["x", "y"]),
        (&["--test-threads=4"], |o| o.threads == 4),
        (&["--test-threads", "16"], |o| o.threads == 16),
        (&["f", "--exact", "--list", "-q"], |o| {
            o.filters == ["f"] && o.exact && o.list && o.quiet
        }),
    ];
    for &(input, check) in parsed {
        h.case(format!("harness::options::parse::{input:?}"), move || {
            let options = RunOptions::parse(&args(input)).expect("valid arguments");
            assert!(check(&options), "{options:?}");
        });
    }
    let refused: &[(&[&str], &str)] = &[
        (&["--bogus"], "unknown flag `--bogus`"),
        (&["-x"], "unknown flag `-x`"),
        (&["--exact=1"], "unknown flag `--exact=1`"),
        (&["--list=yes"], "unknown flag `--list=yes`"),
        (&["--quiet=no"], "unknown flag `--quiet=no`"),
        (&["--nocapture=1"], "unknown flag `--nocapture=1`"),
        (&["--ignored"], "unknown flag `--ignored`"),
        (&["--skip"], "--skip needs a value"),
        (&["--test-threads"], "--test-threads needs a value"),
        (
            &["--test-threads=0"],
            "--test-threads needs a positive integer, not `0`",
        ),
        (
            &["--test-threads=x"],
            "--test-threads needs a positive integer, not `x`",
        ),
        (
            &["--test-threads", "-1"],
            "--test-threads needs a positive integer, not `-1`",
        ),
    ];
    for &(input, message) in refused {
        h.case(format!("harness::options::refuse::{input:?}"), move || {
            assert_eq!(RunOptions::parse(&args(input)), Err(message.to_owned()));
        });
    }
}

fn register_parallel(h: &mut Harness) {
    for threads in [2, 3, 4, 8, 24, 100] {
        h.case(
            format!("harness::parallel::output_equals_serial::{threads}"),
            move || {
                assert_eq!(scrambled_output(threads), scrambled_output(1));
            },
        );
        h.case(
            format!("harness::parallel::runs_each_case_once::{threads}"),
            move || {
                let hits = Arc::new((0..200).map(|_| AtomicUsize::new(0)).collect::<Vec<_>>());
                let log = Arc::clone(&hits);
                let (report, _) = run_harness(
                    move |h| {
                        for index in 0..200 {
                            let log = Arc::clone(&log);
                            h.case(format!("c{index}"), move || {
                                log[index].fetch_add(1, Ordering::Relaxed);
                            });
                        }
                    },
                    &RunOptions {
                        threads,
                        ..options()
                    },
                );
                assert_eq!(report.passed, 200);
                assert!(hits.iter().all(|hit| hit.load(Ordering::Relaxed) == 1));
            },
        );
    }
    h.case("harness::parallel::really_runs_cases_together", || {
        // Each case waits to see the other start, which serial running can't show.
        let (a_started, b_started) = (
            Arc::new(AtomicBool::new(false)),
            Arc::new(AtomicBool::new(false)),
        );
        let wait = |mine: Arc<AtomicBool>, other: Arc<AtomicBool>| {
            move || {
                mine.store(true, Ordering::SeqCst);
                let deadline = Instant::now() + Duration::from_secs(30);
                while !other.load(Ordering::SeqCst) {
                    assert!(Instant::now() < deadline, "the other case never started");
                    thread::yield_now();
                }
            }
        };
        let first = wait(Arc::clone(&a_started), Arc::clone(&b_started));
        let second = wait(b_started, a_started);
        let (report, output) = run_harness(
            |h| {
                h.case("a", first);
                h.case("b", second);
            },
            &RunOptions {
                threads: 2,
                ..options()
            },
        );
        assert!(report.success(), "{output}");
    });
    h.case(
        "harness::parallel::one_thread_keeps_registration_order",
        || {
            let order = Arc::new(Mutex::new(Vec::new()));
            let log = Arc::clone(&order);
            run_harness(
                move |h| {
                    for index in 0..50 {
                        let log = Arc::clone(&log);
                        h.case(format!("c{index}"), move || log.lock().unwrap().push(index));
                    }
                },
                &options(),
            );
            assert_eq!(*order.lock().unwrap(), (0..50).collect::<Vec<_>>());
        },
    );
    h.case("harness::parallel::more_threads_than_cases_is_fine", || {
        let (report, _) = run_harness(
            |h| h.case("only", || ()),
            &RunOptions {
                threads: 64,
                ..options()
            },
        );
        assert_eq!(report.passed, 1);
    });
    for threads in [1, 4] {
        h.case(
            format!("harness::parallel::workers_have_a_deep_stack::{threads}"),
            move || {
                let (report, output) = run_harness(
                    |h| h.case("deep", || assert!(start_burning_stack() > 1000)),
                    &RunOptions {
                        threads,
                        ..options()
                    },
                );
                assert!(report.success(), "{output}");
            },
        );
    }
}

fn register_panics(h: &mut Harness) {
    h.case("harness::panic::later_cases_still_run", || {
        let ran = Arc::new(AtomicUsize::new(0));
        let log = Arc::clone(&ran);
        let (report, _) = run_harness(
            move |h| {
                h.case("first", || -> () { panic!("first") });
                h.case("second", move || {
                    log.fetch_add(1, Ordering::Relaxed);
                });
            },
            &options(),
        );
        assert_eq!(ran.load(Ordering::Relaxed), 1);
        assert_eq!(report.passed, 1);
        assert_eq!(report.failed, ["first"]);
    });
    h.case(
        "harness::panic::the_message_is_reported_with_its_place",
        || {
            let (_, output) = run_harness(
                |h| h.case("a", || -> () { panic!("kaboom {}", 7) }),
                &options(),
            );
            assert!(output.contains("kaboom 7"), "{output}");
            assert!(
                output.contains(&format!("panicked at {}", file!())),
                "{output}"
            );
        },
    );
    h.case("harness::panic::another_threads_panic_still_prints", || {
        let output = child("other_thread_panic", &[], &[]);
        assert_eq!(output.code, Some(0), "{}", output.stdout);
        assert!(
            output.stderr.contains("boom on another thread"),
            "{}",
            output.stderr
        );
    });
    h.case(
        "harness::panic::with_no_report_it_still_has_a_message",
        || {
            let output = child("foreign_hook", &[], &[]);
            assert_eq!(output.stdout, "Some(\"panicked\")\n");
        },
    );
    h.case("harness::panic::the_place_is_relative", || {
        assert!(!file!().starts_with('/'), "{}", file!());
    });
    h.case("harness::panic::assert_eq_shows_both_sides", || {
        let (_, output) = run_harness(|h| h.case("a", || assert_eq!(2 + 2, 5)), &options());
        assert!(output.contains("left: 4"), "{output}");
        assert!(output.contains("right: 5"), "{output}");
    });
    h.case(
        "harness::panic::a_non_string_payload_is_still_a_failure",
        || {
            let (report, output) = run_harness(
                |h| h.case("a", || -> () { panic::panic_any(42_i32) }),
                &options(),
            );
            assert_eq!(report.failed, ["a"]);
            assert!(output.contains("non-string payload"), "{output}");
        },
    );
    h.case("harness::panic::each_failure_keeps_its_own_message", || {
        let (_, output) = run_harness(
            |h| {
                for index in 0..16 {
                    h.case(format!("c{index:02}"), move || -> () {
                        panic!("message of {index:02}")
                    });
                }
            },
            &RunOptions {
                threads: 8,
                ..options()
            },
        );
        for index in 0..16 {
            let wanted = format!("---- c{index:02} ----\n");
            let at = output.find(&wanted).unwrap_or_else(|| panic!("{output}"));
            let section = &output[at..];
            let body = section.split("\n\n").next().unwrap();
            assert!(body.contains(&format!("message of {index:02}")), "{body}");
        }
    });
    h.case("harness::catch_panic::returns_the_message", || {
        let message = catch_panic(|| -> () { panic!("just this") }).expect("it panicked");
        assert!(message.contains("just this"), "{message}");
    });
    h.case("harness::catch_panic::returns_none_without_a_panic", || {
        assert_eq!(catch_panic(|| 1 + 1), None);
    });
    h.case("harness::catch_panic::is_reusable_and_nests", || {
        let outer = catch_panic(|| {
            assert!(catch_panic(|| -> () { panic!("inner") }).is_some());
            assert_eq!(catch_panic(|| ()), None);
            panic!("outer");
        });
        let message = outer.expect("the outer panic is caught");
        assert!(
            message.contains("outer") && !message.contains("inner"),
            "{message}"
        );
    });
    h.case(
        "harness::catch_panic::a_case_that_catches_its_own_panic_passes",
        || {
            let (report, output) = run_harness(
                |h| {
                    h.case("a", || {
                        assert!(catch_panic(|| -> () { panic!("handled") }).is_some());
                    });
                },
                &options(),
            );
            assert!(report.success(), "{output}");
        },
    );
    h.case(
        "harness::panic::a_stale_report_does_not_outlive_its_case",
        || {
            let (report, output) = run_harness(
                |h| {
                    h.case("first", || {
                        assert!(catch_panic(|| -> () { panic!("private note") }).is_some());
                    });
                    h.case("second", || Err::<(), _>("declined"));
                },
                &options(),
            );
            assert_eq!(report.failed, ["second"]);
            assert!(!output.contains("private note"), "{output}");
        },
    );
}

fn register_budget(h: &mut Harness) {
    let slow = |h: &mut Harness| {
        h.case("slow", || thread::sleep(Duration::from_millis(3)));
    };
    h.case("harness::budget::overrun_warns", move || {
        let (report, output) = run_harness(
            slow,
            &RunOptions {
                budget: Some(Duration::ZERO),
                ..options()
            },
        );
        assert!(report.success(), "{output}");
        assert!(output.contains("WARN speed: suite demo"), "{output}");
    });
    h.case(
        "harness::budget::require_speed_fails_an_overrun",
        move || {
            let (report, output) = run_harness(
                slow,
                &RunOptions {
                    budget: Some(Duration::ZERO),
                    require: args(&["speed"]),
                    ..options()
                },
            );
            assert!(!report.success());
            assert!(report.over_budget);
            assert!(output.contains("FAILED speed: suite demo"), "{output}");
        },
    );
    h.case("harness::budget::within_budget_says_nothing", move || {
        let (report, output) = run_harness(
            slow,
            &RunOptions {
                budget: Some(Duration::from_secs(3600)),
                require: args(&["speed"]),
                ..options()
            },
        );
        assert!(report.success(), "{output}");
        assert!(!output.contains("speed"), "{output}");
    });
    h.case("harness::budget::no_budget_says_nothing", move || {
        let (report, output) = run_harness(slow, &options());
        assert!(report.success(), "{output}");
        assert!(!output.contains("speed"), "{output}");
    });
    h.case(
        "harness::budget::other_requirements_do_not_turn_it_into_a_failure",
        move || {
            let (report, output) = run_harness(
                slow,
                &RunOptions {
                    budget: Some(Duration::ZERO),
                    require: args(&["qemu", "as"]),
                    ..options()
                },
            );
            assert!(report.success(), "{output}");
            assert!(output.contains("WARN speed"), "{output}");
        },
    );
    // The scale, and the budget `from_env` makes of it: TESTING 22's tiers.
    let scales: &[(Option<&str>, &str)] = &[
        (None, "Some(60)"),
        (Some("1"), "Some(60)"),
        (Some("2"), "Some(600)"),
        (Some("10"), "Some(600)"),
        (Some("11"), "None"),
        (Some("100"), "None"),
    ];
    for &(scale, budget) in scales {
        h.case(format!("harness::from_env::budget::{scale:?}"), move || {
            let vars: Vec<(&str, &str)> = scale.map(|s| ("ENRANG_SCALE", s)).into_iter().collect();
            let output = child("run_options", &[], &vars);
            assert_eq!(output.code, Some(0), "{}", output.stderr);
            assert!(
                output.stdout.ends_with(&format!(" budget={budget}\n")),
                "{}",
                output.stdout
            );
        });
    }
    h.case("harness::from_env::threads_default_to_the_machine", || {
        let machine = thread::available_parallelism().map_or(1, usize::from);
        let output = child("run_options", &[], &[]);
        assert!(
            output.stdout.starts_with(&format!("threads={machine} ")),
            "{}",
            output.stdout
        );
    });
    // A number no machine here has, so the flag and the machine cannot agree by luck.
    for arguments in [&["--test-threads=257"][..], &["--test-threads", "257"]] {
        h.case(
            format!("harness::from_env::threads_obey_the_flag::{arguments:?}"),
            move || {
                let output = child("run_options", arguments, &[]);
                assert!(
                    output.stdout.starts_with("threads=257 "),
                    "{}",
                    output.stdout
                );
            },
        );
    }
    h.case("harness::budget::child_warns_by_default", || {
        let output = child("speed", &[], &[]);
        assert_eq!(output.code, Some(0), "{}", output.stdout);
        assert!(output.stdout.contains("WARN speed"), "{}", output.stdout);
    });
    h.case("harness::budget::child_fails_under_require_speed", || {
        let output = child("speed", &[], &[("ENRANG_REQUIRE", "speed")]);
        assert_eq!(output.code, Some(1), "{}", output.stdout);
        assert!(output.stdout.contains("FAILED speed"), "{}", output.stdout);
    });
}

fn register_children(h: &mut Harness) {
    h.case("harness::child::all_passing_exits_zero", || {
        let output = child("all_pass", &[], &[]);
        assert_eq!(output.code, Some(0), "{}", output.stderr);
        assert_eq!(
            last_line(&output.stdout),
            "test result: ok. 3 passed; 0 failed; 0 filtered out; 3 total; 0 tests skipped"
        );
    });
    h.case("harness::child::a_failure_exits_one", || {
        let output = child("mixed", &[], &[]);
        assert_eq!(output.code, Some(1));
        assert_eq!(
            last_line(&output.stdout),
            "test result: FAILED. 2 passed; 3 failed; 0 filtered out; 5 total; 0 tests skipped"
        );
    });
    h.case(
        "harness::child::every_failure_is_listed_and_its_text_shown",
        || {
            let output = child("mixed", &[], &[]);
            for name in ["asserts", "panics", "returns_err"] {
                assert!(
                    output.stdout.contains(&format!("test {name} ... FAILED")),
                    "{}",
                    output.stdout
                );
                assert!(
                    output.stdout.contains(&format!("    {name}\n")),
                    "{}",
                    output.stdout
                );
            }
            assert!(
                output.stdout.contains("test after_the_failures ... ok"),
                "{}",
                output.stdout
            );
            for text in ["arithmetic moved", "boom from a case", "declined"] {
                assert!(output.stdout.contains(text), "{}", output.stdout);
            }
        },
    );
    h.case(
        "harness::child::a_captured_panic_prints_nothing_to_stderr",
        || {
            let output = child("mixed", &[], &[]);
            assert_eq!(output.stderr, "");
        },
    );
    h.case(
        "harness::child::the_panic_hook_leaves_other_panics_alone",
        || {
            // Refused scenario: the panic happens outside any case, on the main thread.
            let output = child("no_such_scenario", &[], &[]);
            assert_eq!(output.code, Some(101));
            assert!(
                output.stderr.contains("unknown child scenario"),
                "{}",
                output.stderr
            );
        },
    );
    h.case("harness::child::an_empty_suite_exits_one", || {
        let output = child("empty", &[], &[]);
        assert_eq!(output.code, Some(1));
        assert!(
            output.stdout.contains("no cases registered"),
            "{}",
            output.stdout
        );
    });
    h.case(
        "harness::child::a_failing_case_outside_a_filter_does_not_fail",
        || {
            let output = child("mixed", &["passes"], &[]);
            assert_eq!(output.code, Some(0), "{}", output.stdout);
            assert_eq!(
                last_line(&output.stdout),
                "test result: ok. 1 passed; 0 failed; 4 filtered out; 5 total; 0 tests skipped"
            );
        },
    );
    // Arguments, exit status, passed, filtered out.
    let invocations: &[(&[&str], i32, usize, usize)] = &[
        (&[], 0, 3, 0),
        (&["beta"], 0, 1, 2),
        (&["a"], 0, 3, 0),
        (&["--exact", "a"], 0, 0, 3),
        (&["--exact", "gamma"], 0, 1, 2),
        (&["--skip", "beta"], 0, 2, 1),
        (&["--skip=a"], 0, 0, 3),
        (&["--test-threads=1"], 0, 3, 0),
        (&["--test-threads", "2", "alpha"], 0, 1, 2),
        (&["--quiet"], 0, 3, 0),
    ];
    for (index, &(arguments, code, passed, filtered)) in invocations.iter().enumerate() {
        h.case(format!("harness::child::arguments[{index}]"), move || {
            let output = child("all_pass", arguments, &[]);
            assert_eq!(output.code, Some(code), "{}", output.stderr);
            assert_eq!(
                last_line(&output.stdout),
                format!(
                    "test result: ok. {passed} passed; 0 failed; {filtered} filtered out; 3 total; 0 tests skipped"
                )
            );
        });
    }
    h.case("harness::child::list_runs_nothing", || {
        let output = child("all_pass", &["--list"], &[]);
        assert_eq!(output.code, Some(0));
        assert_eq!(
            output.stdout,
            "alpha: test\nbeta: test\ngamma: test\n\n3 cases\n"
        );
    });
    let usage_errors: &[&[&str]] = &[&["--bogus"], &["--test-threads=0"], &["--skip"]];
    for &arguments in usage_errors {
        h.case(
            format!("harness::child::usage_error_exits_two::{arguments:?}"),
            move || {
                let output = child("all_pass", arguments, &[]);
                assert_eq!(output.code, Some(2));
                assert!(output.stderr.contains("usage:"), "{}", output.stderr);
                assert_eq!(output.stdout, "");
            },
        );
    }
    h.case("harness::child::output_is_the_same_on_every_run", || {
        let runs: BTreeSet<String> = (0..3)
            .map(|_| child("mixed", &["--test-threads=4"], &[]).stdout)
            .collect();
        assert_eq!(runs.len(), 1, "{runs:?}");
    });
}
