//! The dynamic test harness of `harness = false` suites (TESTING 10).
//!
//! Cases run in parallel and report in registration order, so output is the same
//! for any thread count. It has no timings: a suite's output is as deterministic
//! as the suite. Everything that makes a run fail is on the last lines, with the
//! case count, so a total is visible even in a long log.

use std::cell::RefCell;
use std::collections::{BTreeSet, VecDeque};
use std::env;
use std::fmt::Display;
use std::io::{self, Write};
use std::panic::{self, AssertUnwindSafe};
use std::process::ExitCode;
use std::sync::{Arc, Mutex, Once, PoisonError, mpsc};
use std::thread;
use std::time::{Duration, Instant};

use crate::golden::{GoldenStore, default_store};
use crate::rng::{DEFAULT_SEED, parse_scale, parse_seed};
use crate::skip::{SkipLedger, counted_tests, global_ledger, parse_require, require_matches};

/// The stack of a worker: what a main thread gets, and more than the 2 MiB a
/// spawned thread gets by default, so that a case passes on any thread count.
const WORKER_STACK: usize = 8 * 1024 * 1024;

const USAGE: &str =
    "usage: <suite> [FILTER...] [--exact] [--skip FILTER] [--list] [--quiet] [--test-threads N]";

/// An environment variable as text. A non-Unicode value stays visibly wrong
/// instead of reading as unset.
pub(crate) fn env_value(name: &str) -> Option<String> {
    env::var_os(name).map(|value| value.to_string_lossy().into_owned())
}

/// What a case body can return: nothing, where failing means panicking, or a
/// `Result` whose error text is the failure. A body that does nothing but panic
/// has type `!`, so it must say which it means: `|| -> () { panic!("...") }`.
pub trait IntoOutcome {
    fn into_outcome(self) -> Result<(), String>;
}

impl IntoOutcome for () {
    fn into_outcome(self) -> Result<(), String> {
        Ok(())
    }
}

impl<E: Display> IntoOutcome for Result<(), E> {
    fn into_outcome(self) -> Result<(), String> {
        self.map_err(|error| error.to_string())
    }
}

type Body = Box<dyn FnOnce() -> Result<(), String> + Send>;

struct Registered {
    name: String,
    body: Body,
}

/// A suite: named cases, and what must hold once they have run.
pub struct Harness {
    suite: String,
    names: BTreeSet<String>,
    cases: Vec<Registered>,
    golden_suites: Vec<(Arc<GoldenStore>, String)>,
    ledger: Arc<SkipLedger>,
}

impl Harness {
    pub fn new(suite: impl Into<String>) -> Harness {
        Harness {
            suite: suite.into(),
            names: BTreeSet::new(),
            cases: Vec::new(),
            golden_suites: Vec::new(),
            ledger: global_ledger(),
        }
    }

    /// Registers a case.
    ///
    /// # Panics
    ///
    /// If the name is taken: two cases with one name could not be told apart in a
    /// report or selected separately.
    pub fn case<R: IntoOutcome>(
        &mut self,
        name: impl Into<String>,
        body: impl FnOnce() -> R + Send + 'static,
    ) {
        let name = name.into();
        assert!(
            self.names.insert(name.clone()),
            "duplicate case name `{name}`"
        );
        self.cases.push(Registered {
            name,
            body: Box::new(|| body().into_outcome()),
        });
    }

    /// How many cases are registered.
    pub fn len(&self) -> usize {
        self.cases.len()
    }

    /// Whether no case is registered.
    pub fn is_empty(&self) -> bool {
        self.cases.is_empty()
    }

    /// Fails the run on any orphan in `tests/golden/<suite>`. One test binary must
    /// own the suite directory, since only its own calls count as uses.
    pub fn goldens(&mut self, suite: &str) {
        self.goldens_in(default_store(), suite);
    }

    /// [`Harness::goldens`] over another store.
    pub fn goldens_in(&mut self, store: Arc<GoldenStore>, suite: &str) {
        self.golden_suites.push((store, suite.to_owned()));
    }

    /// Summarises this ledger instead of the global one.
    pub fn ledger(&mut self, ledger: Arc<SkipLedger>) {
        self.ledger = ledger;
    }

    /// Runs the suite as this process's arguments and environment ask, printing to
    /// stdout. An invalid invocation exits with status 2.
    pub fn run(self) -> ExitCode {
        match RunOptions::from_env() {
            Ok(options) => self.run_with(&options, &mut io::stdout()).exit_code(),
            Err(message) => {
                eprintln!("error: {message}");
                eprintln!("{USAGE}");
                ExitCode::from(2)
            }
        }
    }

    /// Runs the suite with explicit options, printing to `out`.
    pub fn run_with(self, options: &RunOptions, out: &mut dyn Write) -> RunReport {
        let Harness {
            suite,
            cases,
            golden_suites,
            ledger,
            ..
        } = self;
        let started = Instant::now();
        let total = cases.len();
        let mut selected = cases;
        selected.retain(|case| options.selects(&case.name));
        let filtered = total - selected.len();

        let mut report = RunReport {
            total,
            filtered,
            ..RunReport::default()
        };
        if options.list {
            for case in &selected {
                say(out, format_args!("{}: test", case.name));
            }
            say(out, format_args!("\n{} cases", selected.len()));
            return report;
        }

        say(
            out,
            format_args!(
                "running {} cases of suite {suite} ({total} total, {filtered} filtered out); seed {}, scale {}",
                selected.len(),
                options.seed,
                options.scale
            ),
        );
        let failures = execute(selected, options, out);
        report.passed = total - filtered - failures.len();
        print_failures(&failures, options, out);
        report.failed = failures.into_iter().map(|failure| failure.name).collect();

        for line in ledger.lines() {
            say(out, format_args!("{line}"));
        }
        report.tests_skipped = ledger.total_tests();

        for (store, _) in &golden_suites {
            for blessed in store.take_blessed() {
                say(out, format_args!("{blessed}"));
            }
        }

        // An unused golden proves nothing unless every case ran to its golden
        // call, so a filtered or failing run cannot judge orphans.
        if filtered == 0 && report.failed.is_empty() {
            for (store, golden_suite) in &golden_suites {
                report.orphans.extend(store.orphans(golden_suite));
            }
        }
        for orphan in &report.orphans {
            say(
                out,
                format_args!("FAILED orphaned golden: {orphan} is used by no case"),
            );
        }

        report.required_skips = ledger.required_failures(&options.require);
        for line in &report.required_skips {
            say(
                out,
                format_args!("FAILED required by ENRANG_REQUIRE: {line}"),
            );
        }

        report.no_cases = total == 0 && options.filters.is_empty();
        if report.no_cases {
            say(
                out,
                format_args!("FAILED no cases registered: an empty suite tests nothing"),
            );
        }

        check_budget(&mut report, &suite, options, started.elapsed(), out);

        let verdict = if report.success() { "ok" } else { "FAILED" };
        say(
            out,
            format_args!(
                "test result: {verdict}. {} passed; {} failed; {filtered} filtered out; {total} total; {} skipped",
                report.passed,
                report.failed.len(),
                counted_tests(report.tests_skipped)
            ),
        );
        report
    }
}

fn check_budget(
    report: &mut RunReport,
    suite: &str,
    options: &RunOptions,
    elapsed: Duration,
    out: &mut dyn Write,
) {
    let Some(budget) = options.budget else {
        return;
    };
    if elapsed <= budget {
        return;
    }
    let required = options
        .require
        .iter()
        .any(|name| require_matches(name, "speed"));
    let level = if required { "FAILED" } else { "WARN" };
    say(
        out,
        format_args!(
            "{level} speed: suite {suite} ran for {} s, over its budget of {} s",
            elapsed.as_secs(),
            budget.as_secs()
        ),
    );
    report.over_budget = required;
}

fn say(out: &mut dyn Write, line: std::fmt::Arguments<'_>) {
    // A closed pipe must not turn a verdict into a panic: the exit code still says
    // what happened.
    let _ = writeln!(out, "{line}");
}

struct Failure {
    name: String,
    message: String,
}

fn print_failures(failures: &[Failure], options: &RunOptions, out: &mut dyn Write) {
    if failures.is_empty() {
        return;
    }
    say(out, format_args!("\nfailures:"));
    for failure in failures {
        say(
            out,
            format_args!("\n---- {} ----\n{}", failure.name, failure.message),
        );
    }
    say(out, format_args!("\nfailed cases:"));
    for failure in failures {
        say(out, format_args!("    {}", failure.name));
    }
    say(
        out,
        format_args!(
            "\nreproduce with ENRANG_SEED={} ENRANG_SCALE={} and the case name as a filter\n",
            options.seed, options.scale
        ),
    );
}

/// Runs the cases on worker threads and returns the failures, printing each result
/// as soon as all the earlier ones are known.
fn execute(selected: Vec<Registered>, options: &RunOptions, out: &mut dyn Write) -> Vec<Failure> {
    let count = selected.len();
    let mut names = Vec::with_capacity(count);
    let mut queue = VecDeque::with_capacity(count);
    for (index, case) in selected.into_iter().enumerate() {
        names.push(case.name);
        queue.push_back((index, case.body));
    }
    let queue = Mutex::new(queue);
    let (sender, receiver) = mpsc::channel();
    let workers = options.threads.clamp(1, count.max(1));

    let mut failures = Vec::new();
    thread::scope(|scope| {
        for _ in 0..workers {
            let sender = sender.clone();
            let queue = &queue;
            thread::Builder::new()
                .stack_size(WORKER_STACK)
                .spawn_scoped(scope, move || {
                    loop {
                        let next = queue
                            .lock()
                            .unwrap_or_else(PoisonError::into_inner)
                            .pop_front();
                        let Some((index, body)) = next else { break };
                        let outcome = capture_panic(body).and_then(|outcome| outcome);
                        if sender.send((index, outcome)).is_err() {
                            break;
                        }
                    }
                })
                .expect("cannot start a test worker");
        }
        drop(sender);

        let mut results: Vec<Option<Result<(), String>>> = vec![None; count];
        let mut next_to_print = 0;
        for (index, outcome) in receiver {
            results[index] = Some(outcome);
            while let Some(outcome) = results.get_mut(next_to_print).and_then(Option::take) {
                let name = &names[next_to_print];
                match outcome {
                    Ok(()) if options.quiet => {}
                    Ok(()) => say(out, format_args!("test {name} ... ok")),
                    Err(message) => {
                        say(out, format_args!("test {name} ... FAILED"));
                        failures.push(Failure {
                            name: name.clone(),
                            message,
                        });
                    }
                }
                next_to_print += 1;
            }
        }
    });
    failures
}

thread_local! {
    /// The report of the last panic on this thread, while a capture is active.
    static CAPTURE: RefCell<Option<CaptureSlot>> = const { RefCell::new(None) };
}

#[derive(Default)]
struct CaptureSlot {
    last: Option<String>,
}

/// Replaces the printing panic hook with one that keeps a captured panic's report
/// for the case's failure section. Other threads' panics print as usual.
fn install_panic_hook() {
    static ONCE: Once = Once::new();
    ONCE.call_once(|| {
        let previous = panic::take_hook();
        panic::set_hook(Box::new(move |info| {
            let message = info
                .payload_as_str()
                .unwrap_or("panic with a non-string payload");
            let report = match info.location() {
                Some(at) => format!(
                    "panicked at {}:{}:{}:\n{message}",
                    at.file(),
                    at.line(),
                    at.column()
                ),
                None => format!("panicked:\n{message}"),
            };
            let captured = CAPTURE
                .try_with(|slot| match slot.borrow_mut().as_mut() {
                    Some(slot) => {
                        slot.last = Some(report);
                        true
                    }
                    None => false,
                })
                .unwrap_or(false);
            if !captured {
                previous(info);
            }
        }));
    });
}

/// Runs `body`, returning its value or the report of its panic.
fn capture_panic<R>(body: impl FnOnce() -> R) -> Result<R, String> {
    install_panic_hook();
    let outer = CAPTURE.with(|slot| slot.borrow_mut().replace(CaptureSlot::default()));
    let result = panic::catch_unwind(AssertUnwindSafe(body));
    let inner = CAPTURE.with(|slot| std::mem::replace(&mut *slot.borrow_mut(), outer));
    result.map_err(|_| {
        inner
            .and_then(|slot| slot.last)
            .unwrap_or_else(|| "panicked".to_owned())
    })
}

/// Runs `body` and returns the report of its panic, or `None` if it did not panic.
/// The panic is not printed. It reads well as a shrink predicate.
pub fn catch_panic<R>(body: impl FnOnce() -> R) -> Option<String> {
    capture_panic(body).err()
}

/// The budget of a run's tier (TESTING 22): 60 s at the default scale, 10 minutes
/// up to the full scale, and no limit past it.
pub fn speed_budget(scale: u64) -> Option<Duration> {
    match scale {
        0..=1 => Some(Duration::from_secs(60)),
        2..=10 => Some(Duration::from_secs(600)),
        _ => None,
    }
}

/// How to run a suite.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct RunOptions {
    /// Run the cases matching any of these, or all cases if empty.
    pub filters: Vec<String>,
    /// Exclude the cases matching any of these.
    pub skips: Vec<String>,
    /// Filters match a whole name rather than part of it.
    pub exact: bool,
    /// Print the selected names and run nothing.
    pub list: bool,
    /// Do not print passing cases.
    pub quiet: bool,
    pub threads: usize,
    /// The seed to print for reproduction.
    pub seed: u64,
    /// The scale to print for reproduction.
    pub scale: u64,
    /// The names of `ENRANG_REQUIRE`.
    pub require: Vec<String>,
    pub budget: Option<Duration>,
}

impl Default for RunOptions {
    fn default() -> RunOptions {
        RunOptions {
            filters: Vec::new(),
            skips: Vec::new(),
            exact: false,
            list: false,
            quiet: false,
            threads: 1,
            seed: DEFAULT_SEED,
            scale: 1,
            require: Vec::new(),
            budget: None,
        }
    }
}

impl RunOptions {
    /// The options of this process: its arguments and environment.
    pub fn from_env() -> Result<RunOptions, String> {
        let args: Vec<String> = env::args().skip(1).collect();
        let mut options = RunOptions::parse(&args)?;
        options.seed = parse_seed(env_value("ENRANG_SEED").as_deref())?;
        options.scale = parse_scale(env_value("ENRANG_SCALE").as_deref())?;
        options.require = parse_require(env_value("ENRANG_REQUIRE").as_deref());
        options.budget = speed_budget(options.scale);
        if !args.iter().any(|arg| arg.starts_with("--test-threads")) {
            options.threads = thread::available_parallelism().map_or(1, usize::from);
        }
        Ok(options)
    }

    /// Parses command-line arguments, accepting the libtest flags people type.
    /// Everything else keeps its default.
    pub fn parse(args: &[String]) -> Result<RunOptions, String> {
        let mut options = RunOptions::default();
        let mut rest = args.iter();
        while let Some(arg) = rest.next() {
            let (flag, inline) = match arg.split_once('=') {
                Some((flag, value)) if flag.starts_with("--") => (flag, Some(value.to_owned())),
                _ => (arg.as_str(), None),
            };
            let mut value = |what: &str| {
                inline
                    .clone()
                    .or_else(|| rest.next().cloned())
                    .ok_or_else(|| format!("{what} needs a value"))
            };
            match flag {
                "--exact" if inline.is_none() => options.exact = true,
                "--list" if inline.is_none() => options.list = true,
                "--quiet" | "-q" if inline.is_none() => options.quiet = true,
                // Nothing is captured, so this has nothing to turn off.
                "--nocapture" if inline.is_none() => {}
                "--skip" => options.skips.push(value("--skip")?),
                "--test-threads" => {
                    let text = value("--test-threads")?;
                    options.threads = match text.parse() {
                        Ok(0) | Err(_) => {
                            return Err(format!(
                                "--test-threads needs a positive integer, not `{text}`"
                            ));
                        }
                        Ok(threads) => threads,
                    };
                }
                _ if arg.starts_with('-') => return Err(format!("unknown flag `{arg}`")),
                _ => options.filters.push(arg.clone()),
            }
        }
        Ok(options)
    }

    fn selects(&self, name: &str) -> bool {
        let matches = |filter: &String| {
            if self.exact {
                name == filter
            } else {
                name.contains(filter.as_str())
            }
        };
        (self.filters.is_empty() || self.filters.iter().any(matches))
            && !self.skips.iter().any(|skip| name.contains(skip.as_str()))
    }
}

/// What a run did.
#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub struct RunReport {
    /// The cases registered, selected or not.
    pub total: usize,
    pub passed: usize,
    /// The names of the failed cases, in registration order.
    pub failed: Vec<String>,
    /// The cases the options excluded.
    pub filtered: usize,
    /// The tests the skip ledger holds.
    pub tests_skipped: usize,
    /// The skip notices that `ENRANG_REQUIRE` made failures.
    pub required_skips: Vec<String>,
    /// The golden files no case used.
    pub orphans: Vec<String>,
    /// The run was over its budget and `ENRANG_REQUIRE` names `speed`.
    pub over_budget: bool,
    /// The suite registered nothing, and no filter explains that.
    pub no_cases: bool,
}

impl RunReport {
    pub fn success(&self) -> bool {
        self.failed.is_empty()
            && self.required_skips.is_empty()
            && self.orphans.is_empty()
            && !self.over_budget
            && !self.no_cases
    }

    pub fn exit_code(&self) -> ExitCode {
        if self.success() {
            ExitCode::SUCCESS
        } else {
            ExitCode::FAILURE
        }
    }
}
