//! Tool lookup and skip accounting (TESTING 20).
//!
//! A missing tool never fails silently and never fails the build by default.
//! The usual shape is to register a tool's cases only when it is present, so a
//! skipped case is never counted as passed:
//!
//! ```no_run
//! # use enrang_testkit::{Harness, skip_oracle, tool};
//! # let mut h = Harness::new("demo");
//! # let vectors = vec![1, 2, 3];
//! match tool("as") {
//!     Some(_) => { /* register one case per vector */ }
//!     None => skip_oracle("as", vectors.len(), "not found"),
//! }
//! ```

use std::collections::BTreeMap;
use std::env;
use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Arc, Mutex, OnceLock, PoisonError};

/// An executable found on the search path.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct ToolPath(PathBuf);

impl ToolPath {
    pub fn path(&self) -> &Path {
        &self.0
    }

    /// A [`Command`] that runs the tool.
    pub fn command(&self) -> Command {
        Command::new(&self.0)
    }
}

/// Looks `name` up on `PATH`.
pub fn tool(name: &str) -> Option<ToolPath> {
    find_tool(name, &env::var_os("PATH")?)
}

/// Looks `name` up in a `PATH`-style list. Only a bare name is looked up, and an
/// empty list entry is ignored rather than meaning the current directory, so a
/// tool cannot be picked up from wherever the test happens to run.
pub fn find_tool(name: &str, search_path: &OsStr) -> Option<ToolPath> {
    if name.contains(['/', '\\']) {
        return None;
    }
    env::split_paths(search_path)
        .filter(|dir| !dir.as_os_str().is_empty())
        .map(|dir| dir.join(name))
        .find(|candidate| is_executable(candidate))
        .map(ToolPath)
}

#[cfg(unix)]
fn is_executable(path: &Path) -> bool {
    use std::os::unix::fs::PermissionsExt;
    path.metadata()
        .is_ok_and(|meta| meta.is_file() && meta.permissions().mode() & 0o111 != 0)
}

#[cfg(not(unix))]
fn is_executable(path: &Path) -> bool {
    path.is_file()
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
struct SkipKey {
    tool: String,
    reason: String,
    oracle: bool,
}

/// Skipped tests, summed per tool and reason. Sorted, not in first-seen order,
/// because parallel cases have no stable order and the summary must.
#[derive(Debug, Default)]
pub struct SkipLedger {
    entries: Mutex<BTreeMap<SkipKey, usize>>,
}

impl SkipLedger {
    pub fn new() -> SkipLedger {
        SkipLedger::default()
    }

    /// Notes `tests` tests that will not run. Printed as
    /// `SKIP <tool> <reason>: <tests> tests not run`, or `1 test` for one.
    pub fn record(&self, tool: &str, tests: usize, reason: &str) {
        self.add(tool, tests, reason, false);
    }

    /// Like [`SkipLedger::record`], for the wording TESTING 20 uses for oracle
    /// tests: `SKIP <tool> <reason>: <tests> oracle tests not run`.
    pub fn record_oracle(&self, tool: &str, tests: usize, reason: &str) {
        self.add(tool, tests, reason, true);
    }

    fn add(&self, tool: &str, tests: usize, reason: &str, oracle: bool) {
        assert!(!tool.is_empty(), "skip: the tool name is empty");
        assert!(!reason.is_empty(), "skip of {tool}: the reason is empty");
        let key = SkipKey {
            tool: tool.to_owned(),
            reason: reason.to_owned(),
            oracle,
        };
        *self.lock().entry(key).or_insert(0) += tests;
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, BTreeMap<SkipKey, usize>> {
        self.entries.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// The final summary, one line per tool and reason.
    pub fn lines(&self) -> Vec<String> {
        self.lock()
            .iter()
            .map(|(key, &tests)| render(key, tests))
            .collect()
    }

    /// How many tests were skipped in all.
    pub fn total_tests(&self) -> usize {
        self.lock().values().sum()
    }

    /// The summary lines that `required`, the names of `ENRANG_REQUIRE`, turn
    /// into failures.
    pub fn required_failures(&self, required: &[String]) -> Vec<String> {
        self.lock()
            .iter()
            .filter(|(key, _)| required.iter().any(|name| require_matches(name, &key.tool)))
            .map(|(key, &tests)| render(key, tests))
            .collect()
    }
}

fn render(key: &SkipKey, tests: usize) -> String {
    let SkipKey {
        tool,
        reason,
        oracle,
    } = key;
    let kind = if *oracle { "oracle " } else { "" };
    let noun = counted_tests(tests);
    let noun = noun.strip_prefix(&format!("{tests} ")).unwrap_or(&noun);
    format!("SKIP {tool} {reason}: {tests} {kind}{noun} not run")
}

/// `1 test`, or `N tests`.
pub(crate) fn counted_tests(tests: usize) -> String {
    let plural = if tests == 1 { "" } else { "s" };
    format!("{tests} test{plural}")
}

/// Parses `ENRANG_REQUIRE`, a comma-separated list of names.
pub fn parse_require(value: Option<&str>) -> Vec<String> {
    value
        .unwrap_or("")
        .split(',')
        .map(str::trim)
        .filter(|name| !name.is_empty())
        .map(str::to_owned)
        .collect()
}

/// Whether a required name covers a tool: the same name, or a family of tools
/// whose names continue it after a `-`. So `qemu` requires `qemu-system-i386`,
/// as `ENRANG_REQUIRE=qemu,as` in TESTING 20 needs, and `as` does not require
/// `asm`. Case does not matter: `ovmf` requires `OVMF`.
pub fn require_matches(required: &str, tool: &str) -> bool {
    let required = required.to_ascii_lowercase();
    let tool = tool.to_ascii_lowercase();
    tool == required
        || tool
            .strip_prefix(&required)
            .is_some_and(|rest| rest.starts_with('-'))
}

/// The ledger behind [`skip`] and [`skip_oracle`], which a [`crate::Harness`]
/// summarises unless told otherwise.
pub fn global_ledger() -> Arc<SkipLedger> {
    static LEDGER: OnceLock<Arc<SkipLedger>> = OnceLock::new();
    LEDGER.get_or_init(|| Arc::new(SkipLedger::new())).clone()
}

/// Notes `tests` tests of this run that cannot run, usually because `tool` is
/// absent, with `reason` as the rest of the notice: `skip("OVMF", 40, "not found")`.
pub fn skip(tool: &str, tests: usize, reason: &str) {
    global_ledger().record(tool, tests, reason);
}

/// [`skip`], counted as oracle tests in the notice.
pub fn skip_oracle(tool: &str, tests: usize, reason: &str) {
    global_ledger().record_oracle(tool, tests, reason);
}
