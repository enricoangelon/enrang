//! Goldens and bless (TESTING 17).
//!
//! `tests/golden/<suite>/<name>` holds rendered output. `ENRANG_BLESS=1` rewrites
//! a golden and prints the diff, and is refused under `CI`. A golden file that no
//! case asked for is an orphan: [`crate::Harness::goldens`] fails the run on one.
//!
//! [`golden()`] and [`golden_in`] print a bless report as it happens. A
//! [`GoldenStore`] of your own keeps them until a harness it is registered with, or
//! [`GoldenStore::take_blessed`], collects them.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock, PoisonError};

use crate::diff::line_diff;
use crate::harness::env_value;

/// How goldens appear in messages. The real root stays out of them, because
/// test output never contains absolute paths.
const DISPLAY_ROOT: &str = "tests/golden";

/// What a golden comparison does with a difference.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum BlessMode {
    /// A difference is a failure.
    Check,
    /// A difference rewrites the golden and prints the diff.
    Bless,
    /// Blessing was asked for under CI: every golden fails and none is written.
    Refuse,
}

impl BlessMode {
    /// The mode for the given values of `ENRANG_BLESS` and `CI`.
    ///
    /// Blessing needs exactly `ENRANG_BLESS=1`. CI counts as on for any value but
    /// empty, `0` and `false`: TESTING 17 names `CI=1`, and services also set
    /// `CI=true`, which must not be a way around the refusal.
    pub fn from_values(bless: Option<&str>, ci: Option<&str>) -> BlessMode {
        let under_ci = ci.is_some_and(|value| {
            !value.is_empty() && value != "0" && !value.eq_ignore_ascii_case("false")
        });
        match (bless == Some("1"), under_ci) {
            (false, _) => BlessMode::Check,
            (true, false) => BlessMode::Bless,
            (true, true) => BlessMode::Refuse,
        }
    }

    /// The mode this process's environment asks for.
    pub fn from_env() -> BlessMode {
        BlessMode::from_values(
            env_value("ENRANG_BLESS").as_deref(),
            env_value("CI").as_deref(),
        )
    }
}

/// Why a golden comparison failed.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum GoldenFailure {
    Mismatch,
    Missing,
    BlessRefused,
    InvalidName,
    Io,
}

/// A failed golden comparison. Its `Display` is the whole report.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct GoldenDiff {
    /// The golden's path, relative to the workspace root.
    pub path: String,
    pub failure: GoldenFailure,
    /// The line diff, or the reason when there is nothing to compare.
    pub detail: String,
}

impl fmt::Display for GoldenDiff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { path, detail, .. } = self;
        match self.failure {
            GoldenFailure::Mismatch => write!(
                f,
                "golden mismatch: {path}\n{detail}rerun with ENRANG_BLESS=1 to accept the new output"
            ),
            GoldenFailure::Missing => write!(
                f,
                "golden missing: {path}\n{detail}rerun with ENRANG_BLESS=1 to create it"
            ),
            GoldenFailure::BlessRefused => write!(
                f,
                "bless refused under CI: {path} was not written. {detail}"
            ),
            GoldenFailure::InvalidName => write!(f, "invalid golden name {path}: {detail}"),
            GoldenFailure::Io => write!(f, "cannot access golden {path}: {detail}"),
        }
    }
}

impl Error for GoldenDiff {}

/// A directory of goldens in one bless mode, remembering which ones were used.
#[derive(Debug)]
pub struct GoldenStore {
    root: PathBuf,
    mode: BlessMode,
    used: Mutex<BTreeSet<(String, String)>>,
    blessed: Mutex<BTreeMap<String, String>>,
}

impl GoldenStore {
    pub fn new(root: impl Into<PathBuf>, mode: BlessMode) -> GoldenStore {
        GoldenStore {
            root: root.into(),
            mode,
            used: Mutex::new(BTreeSet::new()),
            blessed: Mutex::new(BTreeMap::new()),
        }
    }

    /// Compares `actual` byte for byte with `<root>/<suite>/<name>`.
    pub fn check(&self, suite: &str, name: &str, actual: &str) -> Result<(), GoldenDiff> {
        let path = format!("{DISPLAY_ROOT}/{suite}/{name}");
        let fail = |failure, detail: String| GoldenDiff {
            path: path.clone(),
            failure,
            detail,
        };
        validate_component(suite, "suite")
            .and_then(|()| validate_name(name))
            .map_err(|detail| fail(GoldenFailure::InvalidName, detail))?;
        self.used
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .insert((suite.to_owned(), name.to_owned()));
        if self.mode == BlessMode::Refuse {
            return Err(fail(
                GoldenFailure::BlessRefused,
                "unset ENRANG_BLESS or CI".to_owned(),
            ));
        }
        let file = self.root.join(suite).join(name);
        let existing = match fs::read(&file) {
            Ok(bytes) => Some(bytes),
            Err(error) if error.kind() == io::ErrorKind::NotFound => None,
            Err(error) => return Err(fail(GoldenFailure::Io, error.to_string())),
        };
        if existing.as_deref() == Some(actual.as_bytes()) {
            return Ok(());
        }
        let previous = existing
            .as_ref()
            .map(|bytes| String::from_utf8_lossy(bytes).into_owned());
        let diff = line_diff(previous.as_deref().unwrap_or(""), actual);
        match (self.mode, &previous) {
            (BlessMode::Bless, _) => {
                write_golden(&file, actual).map_err(|e| fail(GoldenFailure::Io, e.to_string()))?;
                self.blessed
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .insert(path.clone(), diff);
                Ok(())
            }
            (_, None) => Err(fail(GoldenFailure::Missing, diff)),
            (_, Some(_)) => Err(fail(GoldenFailure::Mismatch, diff)),
        }
    }

    /// The reports of the goldens rewritten since the last call, sorted by path:
    /// each is a `blessed <path>` line and the diff.
    pub fn take_blessed(&self) -> Vec<String> {
        let mut blessed = self.blessed.lock().unwrap_or_else(PoisonError::into_inner);
        std::mem::take(&mut *blessed)
            .into_iter()
            .map(|(path, diff)| format!("blessed {path}\n{diff}"))
            .collect()
    }

    /// The golden files of `suite` that no [`GoldenStore::check`] asked for, as
    /// sorted workspace-relative paths. Hidden files are not goldens.
    pub fn orphans(&self, suite: &str) -> Vec<String> {
        let mut found = BTreeSet::new();
        collect_files(&self.root.join(suite), "", &mut found);
        let used = self.used.lock().unwrap_or_else(PoisonError::into_inner);
        found
            .into_iter()
            .filter(|name| !used.contains(&(suite.to_owned(), name.clone())))
            .map(|name| format!("{DISPLAY_ROOT}/{suite}/{name}"))
            .collect()
    }
}

fn write_golden(file: &Path, actual: &str) -> io::Result<()> {
    if let Some(parent) = file.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(file, actual)
}

fn collect_files(dir: &Path, prefix: &str, found: &mut BTreeSet<String>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let name = entry.file_name().to_string_lossy().into_owned();
        if name.starts_with('.') {
            continue;
        }
        let relative = format!("{prefix}{name}");
        let path = entry.path();
        if path.is_dir() {
            collect_files(&path, &format!("{relative}/"), found);
        } else {
            found.insert(relative);
        }
    }
}

fn validate_name(name: &str) -> Result<(), String> {
    if name.is_empty() {
        return Err("the name is empty".to_owned());
    }
    name.split('/')
        .try_for_each(|component| validate_component(component, "name"))
}

/// One path component. Hidden names are refused because they would never be seen
/// by the orphan check, and `..` because it would escape the golden directory.
fn validate_component(component: &str, what: &str) -> Result<(), String> {
    if component.is_empty() {
        return Err(format!("the {what} has an empty path component"));
    }
    if component.starts_with('.') {
        return Err(format!("the {what} has a component starting with `.`"));
    }
    if component.contains(['/', '\\']) {
        return Err(format!("the {what} has a path separator in a component"));
    }
    Ok(())
}

/// The workspace root, where `docs/` and `tests/golden/` live.
pub fn workspace_root() -> PathBuf {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    manifest
        .parent()
        .and_then(Path::parent)
        .expect("enrang-testkit lives in <workspace>/crates/enrang-testkit")
        .to_path_buf()
}

/// The workspace's goldens, in the mode this process's environment asks for.
pub fn default_store() -> Arc<GoldenStore> {
    static STORE: OnceLock<Arc<GoldenStore>> = OnceLock::new();
    STORE
        .get_or_init(|| {
            Arc::new(GoldenStore::new(
                workspace_root().join(DISPLAY_ROOT),
                BlessMode::from_env(),
            ))
        })
        .clone()
}

/// Compares `actual` with `tests/golden/<suite>/<name>`.
pub fn golden(suite: &str, name: &str, actual: &str) -> Result<(), GoldenDiff> {
    golden_in(&default_store(), suite, name, actual)
}

/// [`golden()`] over another store: compares, and prints any bless report to stderr.
pub fn golden_in(
    store: &GoldenStore,
    suite: &str,
    name: &str,
    actual: &str,
) -> Result<(), GoldenDiff> {
    let outcome = store.check(suite, name, actual);
    for report in store.take_blessed() {
        eprintln!("{report}");
    }
    outcome
}
