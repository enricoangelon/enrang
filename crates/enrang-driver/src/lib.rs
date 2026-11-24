//! Compilation sessions and pipelines (ARCHITECTURE 3 and 11).
//!
//! A [`Session`] is where every source of a run is kept and every diagnostic goes,
//! and where both are rendered from. [`check`] is the pipeline of ARCHITECTURE 11 as
//! far as milestone M3 has it, for the target the command line resolved: phase 1
//! loads the entry, its `.test.en` part and every module its imports reach, with the
//! library embedded in `enrang-rtlib`, all parsed in [`ParseMode::Test`]; phase 2
//! resolves names and checks types; phase 3 builds every user module's MIR, infers
//! its contracts and checks its borrows (M3 plan g.3); phase 4 checks packed fields
//! and sizes. Inside a project, each user module's interface file is written once
//! phase 3 passed ([`interface`]). [`emit`] prints a checked program's MIR or
//! contracts. [`format`] parses one file and prints it in the canonical style of
//! SPEC 12.5. The command line resolves the target and reports the problems of the
//! command line itself before it calls either.

#![forbid(unsafe_code)]

pub mod emit;
pub mod interface;
mod phase3;

use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use enrang_base::{FileId, FileOrigin, SourceMap};
use enrang_borrowck::{BorrowFacts, ContractSet};
use enrang_diag::{Aborted, DiagCtx, RenderOpts, render_json, render_text};
use enrang_hir::{CheckedProgram, ModuleId, ModulePath, Tcx};
use enrang_mir::{Bodies, BodyOwner};
use enrang_sema::{ImportTarget, LibSource, LoadError, LoadedProgram, ProgramInput};
use enrang_syntax::{
    NodeIdGen, ParseMode, ast, decode_source, parse_file, parse_input, print_file,
    report_invalid_utf8,
};
use enrang_target::TargetSpec;

/// One run of the compiler: its sources, its diagnostics and the ids of its trees.
/// The fields of ARCHITECTURE 3 that are missing come with the crates that define
/// their types; the type context of a checked program is returned by [`check`] in
/// [`Checked`], since it shares the map.
#[derive(Debug, Default)]
pub struct Session {
    pub map: Arc<SourceMap>,
    pub dcx: DiagCtx,
    /// Node ids, unique across every file of the session.
    pub ids: NodeIdGen,
    /// The target [`check`] ran for, once it has run.
    pub target: Option<Arc<TargetSpec>>,
}

impl Session {
    /// A session with no sources and no diagnostics.
    pub fn new() -> Session {
        Session::default()
    }

    /// Adds the bytes of a file under `path`, the name diagnostics show. Invalid UTF-8
    /// becomes U+FFFD and is EN0001, reported here, before anything lexes the file
    /// (SPEC 2), so each such place gets exactly one diagnostic.
    ///
    /// Panics if something else holds the map, which nothing does while a session
    /// loads its sources.
    pub fn add_source(&mut self, path: PathBuf, bytes: &[u8]) -> FileId {
        let decoded = decode_source(bytes);
        let map = Arc::get_mut(&mut self.map).expect("no one else holds the map while loading");
        let id = map.add(path, Arc::from(decoded.text), FileOrigin::User);
        report_invalid_utf8(map.file(id), &decoded.invalid, &mut self.dcx);
        id
    }

    /// Reads `path` relative to `dir` and adds it as [`Session::add_source`] does,
    /// under `path` as written.
    pub fn load(&mut self, dir: &Path, path: &Path) -> io::Result<FileId> {
        let bytes = fs::read(dir.join(path))?;
        Ok(self.add_source(path.to_path_buf(), &bytes))
    }

    /// The tree of a loaded file; its syntax errors go to the session's diagnostics.
    pub fn parse(&mut self, file: FileId, mode: ParseMode) -> ast::File {
        parse_file(self.map.file(file), &mut self.ids, mode, &mut self.dcx)
    }

    /// Renders what was emitted since the last call, sorted, as stderr shows it, with
    /// the `aborting` line of SPEC 13.1 when any of it is an error.
    pub fn render(&mut self, opts: &RenderOpts) -> String {
        render_text(&self.dcx.take(), &self.map, opts)
    }

    /// Renders what was emitted since the last call, sorted, as `--error-format=json`
    /// shows it: one object per line, notes included.
    pub fn render_json(&mut self) -> String {
        render_json(&self.dcx.take(), &self.map)
    }
}

pub use emit::{Emit, emit, print_elaborated};
pub use phase3::{Internal, verified_order, verify_built};

/// A program [`check`] passed: its typed bodies, the type context they refer to,
/// and what phase 3 made of its user modules.
pub struct Checked {
    pub program: CheckedProgram,
    pub tcx: Tcx,
    /// Every user body as mirbuild built it (M3 plan a.5).
    pub mir: Bodies,
    /// What borrow checking each body found that drop elaboration needs.
    pub facts: BTreeMap<BodyOwner, BorrowFacts>,
    /// The witnesses of every user module's contracts and flags; the contracts
    /// themselves are in `tcx`'s memo.
    pub contracts: ContractSet,
    /// The user modules in topological order, each with its bodies in owner order.
    pub modules: Vec<(ModuleId, Vec<BodyOwner>)>,
}

/// Why [`check`] stopped.
#[derive(Debug)]
pub enum CheckError {
    /// The entry could not be read, or its `.test.en` part exists and could not be
    /// read. `path` is as diagnostics show it.
    Unreadable { path: PathBuf, error: io::Error },
    /// A phase reported an error; the diagnostics are in the session.
    Aborted(Aborted),
    /// A bug in the compiler: MIR it built fails the verifier (exit status 3).
    Internal(Internal),
}

/// How [`check_with`] runs.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CheckOptions {
    /// Load the entry as a library module: a compile fixture of a library-only
    /// rule (its `//! library` header, G50), which `check`'s hidden `--library`
    /// flag asks for. No user program is one.
    pub library_entry: bool,
    /// The root of the project `check` runs in, the directory holding
    /// `enrang.json`: each user module's interface file is written under it once
    /// phase 3 passed (M3 plan b.9). `None` outside a project.
    pub project: Option<PathBuf>,
}

/// The `.test.en` part of the module whose file is `path`: `math.en` has
/// `math.test.en`. A test part, or a file that is not `.en`, has none.
pub fn test_part_of(path: &Path) -> Option<PathBuf> {
    let name = path.file_name()?.to_str()?;
    let stem = name.strip_suffix(".en")?;
    if stem.is_empty() || stem.ends_with(".test") {
        return None;
    }
    Some(path.with_file_name(format!("{stem}.test.en")))
}

/// The module file whose `.test.en` part `path` is, when `path` names a part and
/// that file exists under `dir`: `math.test.en` is a part of `math.en`.
fn module_of_part(dir: &Path, path: &Path) -> Option<PathBuf> {
    let name = path.file_name()?.to_str()?;
    let stem = name.strip_suffix(".test.en")?;
    if stem.is_empty() {
        return None;
    }
    let module = path.with_file_name(format!("{stem}.en"));
    dir.join(&module).is_file().then_some(module)
}

/// `enrang check` (ARCHITECTURE 11) for `target`: phase 1 loads `entry`, read
/// relative to `dir`, its `.test.en` part when that file exists, every module their
/// imports reach and the target's library layers, and parses them all in
/// [`ParseMode::Test`], so the errors of test items are never skipped; phase 2
/// resolves and type-checks them; phase 4's size check (EN0435) runs when phase 2
/// passed. Each phase reports all its errors before it ends (SPEC 13.1). User files
/// are shown by their path relative to `dir`, normalised (`./src/main.en` is
/// `src/main.en`), so a module has one name however the entry was spelled; an
/// absolute entry keeps its root, and its relative imports are read beside it.
///
/// An entry that is a `.test.en` part of a module file that exists checks that
/// module, the part with it, since the part sees its module's items (SPEC 3.1,
/// TESTING 1), as `enrang test` names a module by its part (plan choice: the docs
/// do not say what `check` of a part does); a part with no module file is checked
/// alone.
///
/// Panics if something else holds the session's map, which nothing does before a
/// session is checked. The returned [`Checked`] shares the map, so sources can be
/// added to the session again only once it is dropped.
pub fn check(
    session: &mut Session,
    dir: &Path,
    entry: &Path,
    target: Arc<TargetSpec>,
) -> Result<Checked, CheckError> {
    check_with(session, dir, entry, target, &CheckOptions::default())
}

/// [`check`], with the entry loaded as a library module when `library_entry`
/// ([`CheckOptions::library_entry`]).
pub fn check_entry(
    session: &mut Session,
    dir: &Path,
    entry: &Path,
    target: Arc<TargetSpec>,
    library_entry: bool,
) -> Result<Checked, CheckError> {
    let options = CheckOptions {
        library_entry,
        project: None,
    };
    check_with(session, dir, entry, target, &options)
}

/// [`check`] as `options` say: phases 1 to 4 (M3 plan g.3), and inside a project
/// the interface files of the user modules, written once phase 4 passed.
pub fn check_with(
    session: &mut Session,
    dir: &Path,
    entry: &Path,
    target: Arc<TargetSpec>,
    options: &CheckOptions,
) -> Result<Checked, CheckError> {
    let (loaded, program, tcx) = front(session, dir, entry, target, options.library_entry)?;
    let done = phase3::run(&tcx, &program, &mut session.dcx).map_err(CheckError::Internal)?;
    session.dcx.finish_phase().map_err(CheckError::Aborted)?;
    enrang_borrowck::check_packed(&tcx, &done.mir, &mut session.dcx);
    enrang_sema::check_sizes(&program, &tcx, &mut session.dcx).map_err(CheckError::Aborted)?;
    // The files of a check that passed, phase 4 included: an erroring check writes
    // none (A:1376, "after checking the module").
    if let Some(root) = &options.project {
        write_interfaces(root, &session.map, &tcx, &loaded, &done);
    }
    Ok(Checked {
        program,
        tcx,
        mir: done.mir,
        facts: done.facts,
        contracts: done.contracts,
        modules: done.modules,
    })
}

/// A program phases 1 and 2 passed: its typed bodies and their type context.
pub struct Typed {
    pub program: CheckedProgram,
    pub tcx: Tcx,
}

/// Phases 1 and 2 of [`check`] alone, for the suites that test phase 3 apart
/// ([`run_phase3`]).
pub fn check_types(
    session: &mut Session,
    dir: &Path,
    entry: &Path,
    target: Arc<TargetSpec>,
) -> Result<Typed, CheckError> {
    let (_, program, tcx) = front(session, dir, entry, target, false)?;
    Ok(Typed { program, tcx })
}

/// What [`run_phase3`] made of a typed program's user modules.
pub struct Phase3Output {
    pub mir: Bodies,
    pub facts: BTreeMap<BodyOwner, BorrowFacts>,
    pub contracts: ContractSet,
    pub modules: Vec<(ModuleId, Vec<BodyOwner>)>,
}

/// Phase 3 exactly as [`check`] runs it (M3 plan g.3), its diagnostics in the
/// session and the phase not yet ended.
pub fn run_phase3(session: &mut Session, typed: &Typed) -> Result<Phase3Output, Internal> {
    let done = phase3::run(&typed.tcx, &typed.program, &mut session.dcx)?;
    Ok(Phase3Output {
        mir: done.mir,
        facts: done.facts,
        contracts: done.contracts,
        modules: done.modules,
    })
}

/// Phases 1 and 2: the program loaded, then analysed.
fn front(
    session: &mut Session,
    dir: &Path,
    entry: &Path,
    target: Arc<TargetSpec>,
    library_entry: bool,
) -> Result<(LoadedProgram, CheckedProgram, Tcx), CheckError> {
    session.target = Some(Arc::clone(&target));
    let entry = module_of_part(dir, entry).unwrap_or_else(|| entry.to_path_buf());
    let input = ProgramInput {
        entry,
        mode: ParseMode::Test,
        overrides: Default::default(),
        dir: dir.to_path_buf(),
        lib: LibSource::Embedded,
        library_entry,
    };
    let map = Arc::get_mut(&mut session.map).expect("no one else holds the map while loading");
    let loaded = enrang_sema::load(&input, &target, map, &mut session.ids, &mut session.dcx)
        .map_err(|error| match error {
            LoadError::Unreadable { path, error } => CheckError::Unreadable { path, error },
            LoadError::Aborted(aborted) => CheckError::Aborted(aborted),
        })?;
    let mut tcx = Tcx::new(target, Arc::clone(&session.map));
    let program =
        enrang_sema::analyze(&loaded, &mut tcx, &mut session.dcx).map_err(CheckError::Aborted)?;
    Ok((loaded, program, tcx))
}

/// Writes each user module's interface file under `root`, in topological order,
/// so each direct import's API hash is known before its importers' (plan b.9).
fn write_interfaces(
    root: &Path,
    map: &SourceMap,
    tcx: &Tcx,
    loaded: &LoadedProgram,
    done: &phase3::Phase3,
) {
    let cx = interface::Inputs {
        tcx,
        map,
        contracts: &done.contracts,
        bodies: &done.mir,
    };
    let mut api: BTreeMap<ModulePath, u64> = BTreeMap::new();
    for (module, owners) in &done.modules {
        let path = tcx.module(*module).path;
        let imports: Vec<(ModulePath, u64)> = direct_imports(loaded, path)
            .into_iter()
            .filter_map(|p| api.get(&p).map(|h| (p, *h)))
            .collect();
        let made = interface::text(&cx, *module, owners, &imports);
        interface::write(root, path, &made.text);
        api.insert(path, made.api);
    }
}

/// The modules `path`'s own file imports, by path, in path order; its `.test.en`
/// part's imports are not the module's (A:1376).
fn direct_imports(loaded: &LoadedProgram, path: ModulePath) -> Vec<ModulePath> {
    let Some(module) = loaded.modules.iter().find(|m| m.path == path) else {
        return Vec::new();
    };
    let mut out: Vec<ModulePath> = Vec::new();
    for edge in &module.imports {
        if let Some(ImportTarget::Module(i)) = &edge.target {
            out.push(loaded.modules[*i].path);
        }
        out.extend(edge.children.iter().map(|c| loaded.modules[*c].path));
    }
    out.sort();
    out.dedup();
    out
}

/// `enrang fmt` of one file (SPEC 12.5): its text in the canonical style, or
/// `Aborted` when it does not parse, with its errors in the session. A file of any
/// name parses as `check` parses it, so a `.test.en` file may hold tests.
///
/// The phase is the file: diagnostics emitted before the call and not yet ended by
/// [`DiagCtx::finish_phase`] count against it.
pub fn format(session: &mut Session, path: PathBuf, bytes: &[u8]) -> Result<String, Aborted> {
    let file = session.add_source(path, bytes);
    let tree = session.parse(file, ParseMode::Test);
    session.dcx.finish_phase()?;
    Ok(print_file(session.map.file(file), &tree))
}

/// [`format`] of a source that is no file, standard input to `enrang fmt`, shown
/// under `name`. It belongs to no module, so it takes test items and anything else
/// a module's own file or its `.test.en` part takes ([`parse_input`]): an editor
/// can pipe either kind of file through `fmt`.
pub fn format_input(session: &mut Session, name: PathBuf, bytes: &[u8]) -> Result<String, Aborted> {
    let file = session.add_source(name, bytes);
    let tree = parse_input(
        session.map.file(file),
        &mut session.ids,
        ParseMode::Test,
        &mut session.dcx,
    );
    session.dcx.finish_phase()?;
    Ok(print_file(session.map.file(file), &tree))
}
