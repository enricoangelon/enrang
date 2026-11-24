//! Phase 3 (ARCHITECTURE 5 and 6; M3 plan g.3): for every user module in
//! topological order, its bodies built by mirbuild and verified, the contracts of
//! its functions inferred, each body borrow-checked in owner order, then the
//! module's own checks (fitting, EN0418, a field initialiser's `this`).
//!
//! The verifier's failure on compiler-built MIR is a bug in the compiler (plan
//! i.4): [`Internal`], which the command line reports with exit status 3.

use std::collections::BTreeMap;

use enrang_borrowck::{BorrowFacts, ContractSet};
use enrang_diag::DiagCtx;
use enrang_hir::{CheckedProgram, ItemPath, ModuleId, Tcx};
use enrang_mir::{Bodies, Body, BodyOwner, verify};

/// A bug in the compiler that phase 3 found: its message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Internal(pub String);

/// What phase 3 keeps of a program that passed it.
#[derive(Default)]
pub(crate) struct Phase3 {
    /// Every user body, as built.
    pub mir: Bodies,
    /// What checking each body found that elaboration needs.
    pub facts: BTreeMap<BodyOwner, BorrowFacts>,
    /// The witnesses of every user module's contracts and flags.
    pub contracts: ContractSet,
    /// The user modules in topological order, each with its bodies in owner order.
    pub modules: Vec<(ModuleId, Vec<BodyOwner>)>,
}

/// The user modules of `program`, in its topological order.
pub(crate) fn user_modules(tcx: &Tcx, program: &CheckedProgram) -> Vec<ModuleId> {
    let user = |m: &&ModuleId| !tcx.module(**m).library;
    program.modules.iter().filter(user).copied().collect()
}

/// Owner order (plan b.6): the statements body and its arrows first, then by the
/// owner's path, an arrow after its parent in `ArrowId` order. Never an id's
/// interning order (ARCHITECTURE 1).
pub(crate) fn owner_key(tcx: &Tcx, owner: BodyOwner) -> (u8, Option<ItemPath>, u32) {
    let parent = |o: enrang_hir::BodyOwner| match o {
        enrang_hir::BodyOwner::Fn(d)
        | enrang_hir::BodyOwner::Const(d)
        | enrang_hir::BodyOwner::Test(d) => (1, Some(tcx.def(d).path.clone())),
        enrang_hir::BodyOwner::Statements(_) => (0, None),
    };
    match owner {
        BodyOwner::Statements(_) => (0, None, 0),
        BodyOwner::Fn(d) | BodyOwner::Test(d) => (1, Some(tcx.def(d).path.clone()), 0),
        BodyOwner::Arrow(o, a) => {
            let (rank, path) = parent(o);
            (rank, path, a.0 + 1)
        }
        BodyOwner::Shim(_) => (2, None, 0),
    }
}

/// The bodies of `bodies` in owner order.
pub(crate) fn in_owner_order<'a>(tcx: &Tcx, bodies: &'a Bodies) -> Vec<&'a Body> {
    let mut list: Vec<&Body> = bodies.values().collect();
    list.sort_by_cached_key(|b| owner_key(tcx, b.owner));
    list
}

/// Runs phase 3 over every user module; its diagnostics go to `dcx`, and the
/// caller ends the phase.
pub(crate) fn run(
    tcx: &Tcx,
    program: &CheckedProgram,
    dcx: &mut DiagCtx,
) -> Result<Phase3, Internal> {
    let mut out = Phase3::default();
    for module in user_modules(tcx, program) {
        let bodies = enrang_mirbuild::build_program(tcx, program, module, dcx);
        let order = verified_order(tcx, &bodies)?;
        let set = enrang_borrowck::infer_contracts(tcx, &bodies, dcx);
        for owner in &order {
            let facts = enrang_borrowck::check(tcx, &bodies, &bodies[owner], dcx);
            out.facts.insert(*owner, facts);
        }
        enrang_borrowck::check_module(tcx, program, &bodies, module, dcx);
        out.contracts.witnesses.extend(set.witnesses);
        out.contracts.class_witnesses.extend(set.class_witnesses);
        out.mir.extend(bodies);
        out.modules.push((module, order));
    }
    Ok(out)
}

/// The owners of a module's built `bodies` in owner order, each body verified
/// first ([`verify_built`]): phase 3 checks them in that order, so none is checked
/// unverified.
pub fn verified_order(tcx: &Tcx, bodies: &Bodies) -> Result<Vec<BodyOwner>, Internal> {
    let order: Vec<BodyOwner> = in_owner_order(tcx, bodies)
        .iter()
        .map(|b| b.owner)
        .collect();
    verify_built(tcx, bodies, &order)?;
    Ok(order)
}

/// Each body of `order` verified (plan g.3): compiler-built MIR that fails the
/// verifier is a bug in the compiler, [`Internal`], reported with exit status 3.
pub fn verify_built(tcx: &Tcx, bodies: &Bodies, order: &[BodyOwner]) -> Result<(), Internal> {
    for owner in order {
        if let Err(errors) = verify(tcx, &bodies[owner]) {
            let shown: Vec<String> = errors.iter().map(|e| e.to_string()).collect();
            return Err(Internal(format!(
                "the MIR of `{}` fails the verifier: {}",
                owner_name(tcx, *owner),
                shown.join("; ")
            )));
        }
    }
    Ok(())
}

/// A body's owner as an internal error names it.
pub(crate) fn owner_name(tcx: &Tcx, owner: BodyOwner) -> String {
    let path = |d| {
        let data = tcx.def(d);
        let segs: Vec<String> = data.path.segments.iter().map(|s| s.to_string()).collect();
        format!("{}::{}", data.path.module.as_str(), segs.join("::"))
    };
    match owner {
        BodyOwner::Fn(d) | BodyOwner::Test(d) => path(d),
        BodyOwner::Statements(m) => format!("{} statements", tcx.module(m).path.as_str()),
        BodyOwner::Arrow(o, a) => {
            let parent = match o {
                enrang_hir::BodyOwner::Fn(d)
                | enrang_hir::BodyOwner::Const(d)
                | enrang_hir::BodyOwner::Test(d) => path(d),
                enrang_hir::BodyOwner::Statements(m) => {
                    format!("{} statements", tcx.module(m).path.as_str())
                }
            };
            format!("{parent} arrow #{}", a.0)
        }
        BodyOwner::Shim(k) => format!("{k:?}"),
    }
}
