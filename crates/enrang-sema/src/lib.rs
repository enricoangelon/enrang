//! Phase 2 (ARCHITECTURE 1, 3, 4): module loading, name resolution, declaration
//! lowering into `Tcx`, type checking with inference, member lookup, coercions,
//! narrowing, exhaustiveness, const eval, interfaces, `extend`, `where`, compiler
//! forms and the R1/R2 position checks.
//!
//! The API is ARCHITECTURE 3's with departure D10 (plan b.11): loading is its own
//! phase-1 call, [`load`], run with `&mut SourceMap` before the `Tcx` exists, since
//! loading adds files to the map that a `Tcx` shares behind an `Arc` (plan doc gap
//! G6). [`analyze`] then runs phase 2 over the loaded program and returns the
//! checked program; [`check_sizes`] is phase 4's size check (EN0435). A:772's
//! `check_body` is left to M4, its first caller (plan choice): `analyze` types every
//! user body eagerly and never a library body.
//!
//! The pass order is the plan's d.1, in [`analyze`]. Each pass lives in the module
//! of the stage that owns it (plan section a.4), behind the fixed seam signatures of
//! plan h.2. Bodies are typed module by module in load order, each module's in
//! declaration order; an unannotated constant that a body typed earlier reads is
//! typed at that use, and its body waits for its own turn's passes.
//!
//! `enrang-driver`'s `check` runs the three calls in order for the target the
//! command line resolved, with the library `enrang-rtlib` embeds; each ends its
//! phase on the `DiagCtx` it is given, so a phase that reported an error stops the
//! run (SPEC 13.1).

#![forbid(unsafe_code)]

mod classes;
mod consteval;
mod cx;
mod entry;
mod exhaust;
mod load;
mod lower;
mod passes;
mod resolve;
mod typeck;

use std::collections::BTreeMap;
use std::io;
use std::path::PathBuf;
use std::sync::Arc;

use enrang_base::SourceMap;
use enrang_diag::{Aborted, DiagCtx};
use enrang_hir::{BodyOwner, CheckedProgram, Tcx};
use enrang_syntax::{NodeIdGen, ParseMode};
use enrang_target::TargetSpec;

pub use load::{ImportEdge, ImportTarget, LoadedModule, LoadedPart, LoadedProgram};
// The const interpreter (plan d.14), public so its cases run on hand-built HIR in
// the sema suite (plan h.1, stage 2E).
pub use consteval::{ConstBodies, ConstError, ConstState, MAX_VALUES};

/// What a command checks (A:770, plus where user files are read and which library
/// to use).
#[derive(Clone, Debug)]
pub struct ProgramInput {
    /// The entry file, relative to `dir` (`src/main.en`).
    pub entry: PathBuf,
    pub mode: ParseMode,
    /// Texts that replace files, keyed by path relative to `dir`, as `enrang dev`
    /// and the tests use them.
    pub overrides: BTreeMap<PathBuf, Arc<str>>,
    /// Where user paths are read.
    pub dir: PathBuf,
    pub lib: LibSource,
    /// The entry is loaded as a library module, so the library-only forms are
    /// allowed in it: a compile fixture's `//! library` header (G50), never a
    /// user's program.
    pub library_entry: bool,
}

impl ProgramInput {
    /// A program read entirely from `sources` (path relative to a virtual directory,
    /// text), with the embedded library. Nothing is read from disk.
    pub fn in_memory(entry: &str, sources: &[(&str, &str)], mode: ParseMode) -> ProgramInput {
        ProgramInput {
            entry: PathBuf::from(entry),
            mode,
            overrides: sources
                .iter()
                .map(|(path, text)| (PathBuf::from(path), Arc::from(*text)))
                .collect(),
            dir: PathBuf::from("/nonexistent/enrang-in-memory"),
            lib: LibSource::Embedded,
            library_entry: false,
        }
    }
}

/// Where library modules come from: the table `enrang-rtlib` embeds, or, for tests,
/// a map from module key (`core/prelude`) to text.
#[derive(Clone, Debug)]
pub enum LibSource {
    Embedded,
    Fake(BTreeMap<String, Arc<str>>),
}

/// Why loading stopped.
#[derive(Debug)]
pub enum LoadError {
    /// The entry file could not be read.
    Unreadable { path: PathBuf, error: io::Error },
    /// Phase 1 reported errors (SPEC 13.1).
    Aborted(Aborted),
}

/// Phase 1: reads and parses the entry, its `.test.en` part in `ParseMode::Test`,
/// every module its imports reach, and every module of the target's library layers,
/// adding each file to `map`; then ends phase 1 on `dcx`. An import path that names
/// nothing is recorded and reported at the start of phase 2 (EN0305 is a phase-2
/// code).
pub fn load(
    input: &ProgramInput,
    target: &TargetSpec,
    map: &mut SourceMap,
    ids: &mut NodeIdGen,
    dcx: &mut DiagCtx,
) -> Result<LoadedProgram, LoadError> {
    load::load(input, target, map, ids, dcx)
}

/// Phase 2 over a loaded program, in the plan's d.1 order; ends phase 2 on `dcx`.
pub fn analyze(
    program: &LoadedProgram,
    tcx: &mut Tcx,
    dcx: &mut DiagCtx,
) -> Result<CheckedProgram, Aborted> {
    let checked = {
        let mut sema = cx::Sema::new(tcx, dcx, program);
        sema.emit_pending();
        let order = load::graph::check(&mut sema);
        resolve::items::collect(&mut sema);
        resolve::imports::resolve(&mut sema);
        lower::decls(&mut sema);
        classes::check_decls(&mut sema);
        typeck::overload::check_decls(&mut sema);
        passes::positions::check_decls(&mut sema);
        consteval::check_items(&mut sema);
        for &module in &order {
            for owner in sema.decls.owners_of(module) {
                let early = match owner {
                    BodyOwner::Const(def) => sema.early_consts.remove(&def),
                    _ => None,
                };
                let body = match early {
                    Some(body) => body,
                    None => typeck::check_body(&mut sema, owner),
                };
                passes::matches::check(&mut sema, &body);
                classes::calls::check(&mut sema, &body);
                passes::unsafety::check(&mut sema, &body);
                passes::positions::check_body(&mut sema, &body);
                passes::positions::hidden_fn_values(&mut sema, &body);
                passes::deferred::check(&mut sema, &body);
                sema.store_body(owner, body);
            }
        }
        passes::views::compute_and_check(&mut sema);
        entry::check(&mut sema);
        sema.finish(order)
    };
    dcx.finish_phase()?;
    Ok(checked)
}

/// Phase 4's subset at M2: the size check of types, statics and frames (EN0435);
/// ends the phase on `dcx`.
pub fn check_sizes(program: &CheckedProgram, tcx: &Tcx, dcx: &mut DiagCtx) -> Result<(), Aborted> {
    passes::sizes::check(program, tcx, dcx);
    dcx.finish_phase()
}
