//! HIR to MIR: evaluation order, scopes, scheduled drops, match lowering,
//! closures, test forms (ARCHITECTURE 1, 3, 5; M3 plan c).
//!
//! Skeleton (stage 1B): the API and the seams of plan g.2 are final; `build` makes
//! each body's locals and arguments and a lone `return`, and the lowering modules
//! are placeholders owned by stages 2B (`builder`, `scope`, `place`, `expr`,
//! `adjust`, `call`, `assign`, `stmt`, `construct`) and 2C (`matches`, `result`,
//! `forof`, `spread`, `pattern`, `closure`, `consts`, `tests_forms`). 2C's entry
//! points are called by 2B's `expr.rs` and `stmt.rs`; 2C calls only `Builder`
//! methods.
//!
//! **Departure.** ARCHITECTURE 3's `build(tcx, hir, dcx)` takes no program, but a
//! local function's hidden arguments live in `CheckedProgram::hidden_args` (M3
//! plan K7), so both entry points take it.

#![forbid(unsafe_code)]

mod adjust;
mod assign;
mod builder;
mod call;
mod closure;
mod construct;
mod consts;
mod expr;
mod forof;
mod matches;
mod pattern;
mod place;
mod result;
mod scope;
mod spread;
mod stmt;
mod tests_forms;

use std::sync::Arc;

use enrang_diag::DiagCtx;
use enrang_hir::{self as hir, CheckedProgram, ModuleId, Tcx};
use enrang_mir::{Bodies, Body};

pub use builder::Builder;
pub use closure::{build_arrow_body, lower_arrow_value};
pub use consts::{lower_const_read, lower_literal_view};
pub use forof::lower_for_of;
pub use matches::{lower_coalesce, lower_match, lower_non_null, lower_opt_chain};
pub use pattern::lower_destructure;
pub use result::{lower_err, lower_try};
pub use scope::{ExitTarget, ScopeKind};
pub use spread::lower_array_build;
pub use tests_forms::lower_expect;

/// What every body of one build shares.
pub struct BuildCx<'a> {
    pub tcx: &'a Tcx,
    pub program: &'a CheckedProgram,
}

impl BuildCx<'_> {
    /// The HIR body of `owner`.
    pub fn hir_body(&self, owner: hir::BodyOwner) -> Option<&Arc<hir::Body>> {
        match owner {
            hir::BodyOwner::Statements(_) => self.program.statements.as_ref(),
            hir::BodyOwner::Fn(d) | hir::BodyOwner::Const(d) | hir::BodyOwner::Test(d) => {
                self.program.bodies.get(&d)
            }
        }
    }
}

/// Builds one HIR body and its arrows: the parent first, then one body per arrow
/// in `ArrowId` order (A:803).
pub fn build(
    tcx: &Tcx,
    program: &CheckedProgram,
    body: &hir::Body,
    dcx: &mut DiagCtx,
) -> Vec<Body> {
    let cx = BuildCx { tcx, program };
    let mut out = vec![Builder::build(&cx, body, dcx)];
    for arrow in body.arrows.indices() {
        out.push(build_arrow_body(&cx, body.owner, arrow));
    }
    out
}

/// Builds every body of one user module (plan c.1): functions, methods,
/// constructors, destructors, local functions, the statements body, test bodies,
/// and their arrows; constants' initialisers get none (D18).
pub fn build_program(
    tcx: &Tcx,
    program: &CheckedProgram,
    module: ModuleId,
    dcx: &mut DiagCtx,
) -> Bodies {
    let mut out = Bodies::new();
    let mut owned: Vec<&Arc<hir::Body>> = program
        .bodies
        .iter()
        .filter(|(d, b)| {
            tcx.def(**d).module == module && !matches!(b.owner, hir::BodyOwner::Const(_))
        })
        .map(|(_, b)| b)
        .collect();
    if let Some(s) = &program.statements
        && s.owner == hir::BodyOwner::Statements(module)
    {
        owned.push(s);
    }
    for b in owned {
        for m in build(tcx, program, b, dcx) {
            out.insert(m.owner, m);
        }
    }
    out
}
