//! No panic and no internal error (M3 plan f.1 and f.7, stage 4M): every compile
//! fixture, near-misses included, every corpus program, every `ts` block of SPEC
//! and every source example of an explain page goes through `check` in this
//! process, phases 1 to 4, with the target and the library flag its header asks
//! for. Whatever the program, the compiler reports diagnostics or passes it: it
//! never panics, and it never ends in [`CheckError::Internal`], the verifier
//! failing on MIR it built (exit 3, plan i.4).
//!
//! The inputs and the in-process front end live here, and `verify_all` and
//! `determinism` run the same inputs. A case runs one group, a code directory of
//! `tests/compile/` or one of the other sources, and reports every input of the
//! group that fails, so a run names them all at once.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use enrang_diag::{Code, FixtureKind, Milestone, RenderOpts, explain};
use enrang_driver::{
    CheckError, CheckOptions, Checked, Phase3Output, Session, Typed, check_with, run_phase3,
};
use enrang_hir::Tcx;
use enrang_sema::{LibSource, LoadError, ProgramInput};
use enrang_syntax::ParseMode;
use enrang_target::{TargetOpts, TargetSpec, host_target, resolve};
use enrang_testkit::{
    Harness, TempDir, catch_panic, fenced_blocks, fixture_header, workspace_root,
};

/// Where an input's text is.
#[derive(Clone, Debug)]
pub enum Text {
    /// A file of the workspace, by its path from the root, where `check` runs, as
    /// the CLI suite runs a fixture.
    Disk(String),
    /// A program of a document, checked as `main.en` in a fresh directory.
    Memory(String),
}

/// One program the pipeline suites run.
#[derive(Clone, Debug)]
pub struct Input {
    /// How a failure names it: its path, or its document and line.
    pub name: String,
    pub text: Text,
    /// The `//! target:` of its header; the host's otherwise.
    pub target: Option<String>,
    /// Its header's `//! library`: the entry loads as a library module.
    pub library: bool,
    /// Why the input cannot run: its file cannot be read or its header is
    /// broken. `no_panic` fails on it; the other suites leave it out.
    pub broken: Option<String>,
}

impl Input {
    fn disk(path: String) -> Input {
        // A fixture of EN0001 is not UTF-8: its header is read as `check` decodes it.
        // A file that cannot be read, or a broken header, fails its group's case
        // rather than the registration of every case.
        let header = std::fs::read(workspace_root().join(&path))
            .map_err(|e| e.to_string())
            .and_then(|bytes| fixture_header(&String::from_utf8_lossy(&bytes)));
        let (header, broken) = match header {
            Ok(header) => (header, None),
            Err(error) => (Default::default(), Some(error)),
        };
        Input {
            name: path.clone(),
            text: Text::Disk(path),
            target: header.target,
            library: header.library,
            broken,
        }
    }

    fn memory(name: String, source: &str) -> Input {
        Input {
            name,
            text: Text::Memory(source.to_owned()),
            target: None,
            library: false,
            broken: None,
        }
    }

    /// The target the input is checked for.
    pub fn target(&self) -> Arc<TargetSpec> {
        let name = self.target.as_deref().unwrap_or(host_target());
        let spec = resolve(name, &TargetOpts::default())
            .unwrap_or_else(|_| panic!("{}: no target `{name}`", self.name))
            .0;
        Arc::new(spec)
    }

    /// The directory `check` runs in and the entry's path in it; the directory is
    /// kept alive by the returned [`TempDir`] for a program of a document.
    pub fn place(&self) -> (Option<TempDir>, PathBuf, PathBuf) {
        match &self.text {
            Text::Disk(path) => (None, workspace_root(), PathBuf::from(path)),
            Text::Memory(source) => {
                let dir = TempDir::new("pipeline-input");
                dir.write("main.en", source);
                let root = dir.path().to_path_buf();
                (Some(dir), root, PathBuf::from("main.en"))
            }
        }
    }
}

/// The `.en` files under `dir`, a directory of the workspace, recursively, as
/// sorted paths from the root.
fn en_files(dir: &str) -> Vec<String> {
    fn walk(dir: &Path, rel: &str, found: &mut Vec<String>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            let path = format!("{rel}/{name}");
            if entry.path().is_dir() {
                walk(&entry.path(), &path, found);
            } else if name.ends_with(".en") {
                found.push(path);
            }
        }
    }
    let mut found = Vec::new();
    walk(&workspace_root().join(dir), dir, &mut found);
    found.sort();
    found
}

/// The inputs, in groups: one per code directory of `tests/compile/`, then the
/// corpus programs, SPEC's `ts` blocks and the explain pages' source examples.
pub fn groups() -> Vec<(String, Vec<Input>)> {
    let mut groups: Vec<(String, Vec<Input>)> = Vec::new();
    let mut fixtures: Vec<(String, Vec<Input>)> = Vec::new();
    for path in en_files("tests/compile") {
        let dir = path.rsplit_once('/').map_or("", |(dir, _)| dir).to_owned();
        let input = Input::disk(path);
        match fixtures.last_mut() {
            Some((last, inputs)) if *last == dir => inputs.push(input),
            _ => fixtures.push((dir, vec![input])),
        }
    }
    groups.extend(fixtures);
    let corpus: Vec<Input> = en_files("corpus").into_iter().map(Input::disk).collect();
    groups.push(("corpus".to_owned(), corpus));
    groups.push(("docs/SPEC.md".to_owned(), spec_blocks()));
    groups.push(("explain".to_owned(), explain_examples()));
    groups
}

/// Every `ts` block of SPEC, as a program of its own.
fn spec_blocks() -> Vec<Input> {
    let spec = std::fs::read_to_string(workspace_root().join("docs/SPEC.md")).expect("SPEC");
    fenced_blocks(&spec)
        .unwrap_or_else(|errors| panic!("{errors}"))
        .into_iter()
        .filter(|block| block.lang == "ts")
        .map(|block| Input::memory(format!("docs/SPEC.md:{}", block.line), &block.contents))
        .collect()
}

/// The failing and fixed examples of every page of a code `check` reports (a
/// `Compile` code of milestone M3 or earlier), each a program of its own.
fn explain_examples() -> Vec<Input> {
    let mut found = Vec::new();
    for &code in Code::ALL {
        if code.fixture() != FixtureKind::Compile || code.since() > Milestone::M3 {
            continue;
        }
        let Some(page) = explain(code) else {
            continue;
        };
        found.push(Input::memory(
            format!("explain {code} failing"),
            page.failing,
        ));
        found.push(Input::memory(format!("explain {code} fixed"), page.fixed));
    }
    found
}

/// The inputs of a group that can run: those with no [`Input::broken`] reason.
pub fn runnable(inputs: &[Input]) -> impl Iterator<Item = &Input> {
    inputs.iter().filter(|input| input.broken.is_none())
}

/// `check` of an input, as the command line runs it: phases 1 to 4.
pub fn check_input(input: &Input) -> (Session, Result<Checked, CheckError>) {
    let (_dir, root, entry) = input.place();
    let mut session = Session::new();
    let options = CheckOptions {
        library_entry: input.library,
        project: None,
    };
    let checked = check_with(&mut session, &root, &entry, input.target(), &options);
    (session, checked)
}

/// Phases 1 and 2 of an input, as `check` runs them, in `mode`: the typed program,
/// or `None` when they reject it. `enrang_driver::check_types` takes no library
/// flag and no parse mode, so the suites that need them load the program here.
pub fn front(input: &Input, mode: ParseMode) -> (Session, Option<Typed>) {
    let (_dir, root, entry) = input.place();
    front_at(&root, &entry, input.target(), input.library, mode)
}

/// Phases 1 and 2 of `entry`, read relative to `root`, as `check` runs them
/// (`enrang_driver`'s own front end, with the parse mode a choice): the typed
/// program, or `None` when they reject it, with their diagnostics in the session.
pub fn front_at(
    root: &Path,
    entry: &Path,
    target: Arc<TargetSpec>,
    library: bool,
    mode: ParseMode,
) -> (Session, Option<Typed>) {
    let mut session = Session::new();
    session.target = Some(Arc::clone(&target));
    let program = ProgramInput {
        entry: entry.to_path_buf(),
        mode,
        overrides: Default::default(),
        dir: root.to_path_buf(),
        lib: LibSource::Embedded,
        library_entry: library,
    };
    let map = Arc::get_mut(&mut session.map).expect("a fresh session's map");
    let loaded = match enrang_sema::load(&program, &target, map, &mut session.ids, &mut session.dcx)
    {
        Ok(loaded) => loaded,
        Err(LoadError::Unreadable { path, error }) => {
            panic!("cannot read {}: {error}", path.display())
        }
        Err(LoadError::Aborted(_)) => return (session, None),
    };
    let mut tcx = Tcx::new(target, Arc::clone(&session.map));
    match enrang_sema::analyze(&loaded, &mut tcx, &mut session.dcx) {
        Ok(program) => (session, Some(Typed { program, tcx })),
        Err(_) => (session, None),
    }
}

/// Phases 1 to 3 of an input in [`ParseMode::Test`], as `check` runs them: the
/// typed program and what phase 3 made of it, with phase 3's diagnostics left in
/// the session; `None` when phases 1 and 2 reject it, and the internal error's
/// message when MIR it built fails the verifier.
pub fn through_phase3(input: &Input) -> Result<Option<(Session, Typed, Phase3Output)>, String> {
    let (mut session, typed) = front(input, ParseMode::Test);
    let Some(typed) = typed else {
        return Ok(None);
    };
    match run_phase3(&mut session, &typed) {
        Ok(out) => Ok(Some((session, typed, out))),
        Err(internal) => Err(internal.0),
    }
}

/// What a run of `check` on an input came to, when it is no failure of this
/// suite: whether the program passed.
fn no_panic(input: &Input) -> Result<bool, String> {
    if let Some(why) = &input.broken {
        return Err(format!("{}: cannot run: {why}", input.name));
    }
    let mut outcome = None;
    if let Some(panic) = catch_panic(|| outcome = Some(check_input(input))) {
        return Err(format!("{}: panicked: {panic}", input.name));
    }
    let (mut session, checked) = outcome.expect("ran");
    match checked {
        Ok(_) => Ok(true),
        Err(CheckError::Aborted(_)) => {
            // The report renders: a label at a span in no file would panic.
            let rendered = catch_panic(|| session.render(&RenderOpts::default()));
            match rendered {
                Some(panic) => Err(format!("{}: rendering panicked: {panic}", input.name)),
                None => Ok(false),
            }
        }
        Err(CheckError::Internal(internal)) => {
            Err(format!("{}: internal error: {}", input.name, internal.0))
        }
        Err(CheckError::Unreadable { path, error }) => Err(format!(
            "{}: cannot read {}: {error}",
            input.name,
            path.display()
        )),
    }
}

pub fn register(h: &mut Harness) {
    let groups = groups();
    let total: usize = groups.iter().map(|(_, inputs)| inputs.len()).sum();
    h.case(
        "no_panic/the inputs are every fixture, corpus program, SPEC block and page example",
        move || {
            assert!(total >= 1_000, "only {total} inputs");
            let spec = spec_blocks().len();
            assert!(spec >= 40, "only {spec} SPEC blocks");
            let pages = explain_examples().len();
            assert!(pages >= 100, "only {pages} page examples");
        },
    );
    for (group, inputs) in groups {
        h.case(
            format!(
                "no_panic/{group}: phases 1 to 4 never panic and never end in an internal error"
            ),
            move || {
                let mut failures = Vec::new();
                let mut passed = 0;
                for input in &inputs {
                    match no_panic(input) {
                        Ok(true) => passed += 1,
                        Ok(false) => {}
                        Err(failure) => failures.push(failure),
                    }
                }
                assert!(failures.is_empty(), "\n{}", failures.join("\n"));
                // A near-miss passes `check`, so a group of fixtures with near-misses
                // reached the end of phase 4 at least once.
                let near_misses = inputs
                    .iter()
                    .filter(|input| input.name.ends_with(".pass.en"))
                    .count();
                assert!(
                    passed >= near_misses,
                    "{passed} passed, {near_misses} near-misses"
                );
            },
        );
    }
}
