//! What the pipeline suites share (M3 plan g.1, stage 1B): a program checked
//! through phases 1 and 2 for the host target in a temporary directory, then every
//! user module's bodies built by mirbuild, each verified (plan g.3); and phase 3's
//! borrow checking of them (merge-2).

use std::path::Path;
use std::sync::Arc;

use enrang_diag::RenderOpts;
use enrang_driver::{Session, Typed, check_types, run_phase3};
use enrang_hir::Tcx;
use enrang_mir::{Bodies, Body, print_module, verify};
use enrang_target::{TargetOpts, host_target, resolve};
use enrang_testkit::TempDir;

/// A checked program's MIR, before elaboration.
pub struct Built {
    pub tcx: Tcx,
    pub bodies: Bodies,
}

impl Built {
    /// The bodies in the text form, in owner order.
    pub fn text(&self) -> String {
        let list: Vec<Body> = self.bodies.values().cloned().collect();
        print_module(&self.tcx, &list)
    }
}

/// Phases 1 and 2 of `source` as `main.en`; panics with the diagnostics when they
/// reject it.
fn checked(source: &str) -> (Session, Typed) {
    checked_as("main.en", source)
}

/// Phases 1 and 2 of `source` as the file `name` (`main.test.en` for a program
/// with tests); panics with the diagnostics when they reject it.
fn checked_as(name: &str, source: &str) -> (Session, Typed) {
    let dir = TempDir::new("pipeline");
    dir.write(name, source);
    let mut session = Session::new();
    let target = Arc::new(
        resolve(host_target(), &TargetOpts::default())
            .expect("a target")
            .0,
    );
    match check_types(&mut session, dir.path(), Path::new(name), target) {
        Ok(checked) => (session, checked),
        Err(e) => panic!("{e:?}\n{}", session.render(&RenderOpts::default())),
    }
}

/// Phases 1 and 2 of `source` as `main.en`, for a case that changes the typed
/// program before phase 3 sees it; panics with the diagnostics when they reject it.
pub fn typed(source: &str) -> (Session, Typed) {
    checked(source)
}

/// Phases 1 to 4 of `source` as `main.en`, as `check` runs them; panics with the
/// diagnostics when they reject it.
pub fn checked_program(source: &str) -> enrang_driver::Checked {
    let dir = TempDir::new("pipeline");
    dir.write("main.en", source);
    let mut session = Session::new();
    let target = Arc::new(
        resolve(host_target(), &TargetOpts::default())
            .expect("a target")
            .0,
    );
    match enrang_driver::check(&mut session, dir.path(), Path::new("main.en"), target) {
        Ok(checked) => checked,
        Err(e) => panic!("{e:?}\n{}", session.render(&RenderOpts::default())),
    }
}

/// One user module's bodies, each verified; panics with the verifier's errors.
fn module_bodies(session: &mut Session, c: &Typed, m: enrang_hir::ModuleId) -> Bodies {
    let bodies = enrang_mirbuild::build_program(&c.tcx, &c.program, m, &mut session.dcx);
    for b in bodies.values() {
        if let Err(e) = verify(&c.tcx, b) {
            panic!("{e:#?}");
        }
    }
    bodies
}

fn user_modules(c: &Typed) -> Vec<enrang_hir::ModuleId> {
    let user = |m: &&enrang_hir::ModuleId| !c.tcx.module(**m).library;
    c.program.modules.iter().filter(user).copied().collect()
}

/// Checks `source` as `main.en` and builds every user module's bodies; panics
/// with the diagnostics when phases 1 and 2 reject it, and with the errors when a
/// body fails the verifier.
pub fn build(source: &str) -> Built {
    let (mut session, c) = checked(source);
    let mut bodies = Bodies::new();
    for m in user_modules(&c) {
        bodies.extend(module_bodies(&mut session, &c, m));
    }
    Built { tcx: c.tcx, bodies }
}

/// Phase 3 of `source` as plan g.3 runs it, exactly as `check` does
/// (`enrang_driver::run_phase3`): module by module, the bodies built and
/// verified, the contracts inferred, each body checked in owner order, then the
/// module's checks; each diagnostic's code and line, in report order.
pub fn phase3(source: &str) -> Vec<(String, u32)> {
    phase3_as("main.en", source)
}

/// [`phase3`] of `source` as the file `name`.
pub fn phase3_as(name: &str, source: &str) -> Vec<(String, u32)> {
    let (mut session, c) = checked_as(name, source);
    if let Err(e) = run_phase3(&mut session, &c) {
        panic!("internal: {}", e.0);
    }
    let map = session.map.clone();
    let diags = session.dcx.take();
    // Every report renders, as text and as JSON, and every fix-it applies to the
    // source it was made for: a label or an edit at a span in no file, or two
    // edits that overlap, would panic here.
    let _ = enrang_diag::render_text(&diags, &map, &RenderOpts::default());
    let _ = enrang_diag::render_json(&diags, &map);
    for d in &diags {
        for help in d.helps.iter().filter(|h| !h.edits.is_empty()) {
            let mut files: Vec<enrang_base::FileId> = (help.edits.iter())
                .map(|e| map.file_of(e.span.lo).id)
                .collect();
            files.dedup();
            for id in files {
                let file = map.file(id);
                let edits: Vec<enrang_diag::Edit> = (help.edits.iter())
                    .filter(|e| map.file_of(e.span.lo).id == id)
                    .cloned()
                    .collect();
                if let Err(e) = enrang_diag::apply_fixes(&file.text, file.start, &edits) {
                    panic!("{}: `{}`: {e}", d.code, help.message);
                }
            }
        }
    }
    (diags.into_iter())
        .map(|d| (d.code.to_string(), map.loc(d.primary.span.lo).line))
        .collect()
}

// What `enrang-diag`'s hand-built goldens, included as `hand`, read from their own
// suite's `support` module.
pub use crate::diag_support::{Src, doc, same, strip_ansi};
