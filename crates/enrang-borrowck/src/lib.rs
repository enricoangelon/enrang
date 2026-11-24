//! Borrow checking: contract inference, move and init dataflow, read-only marks,
//! loans, liveness, returned-reference sources, explanations and fix-its, drop
//! elaboration (ARCHITECTURE 1, 3, 6; M3 plan d).
//!
//! Skeleton (stage 1B): the public API of plan d.0 and the seams of plan g.2 are
//! final; the analyses are placeholders that report nothing, owned by stages 2D
//! (moves, marks, elaboration), 2E (loans) and 2F (contracts), and the wording by
//! stage 3 (`report.rs`).
//!
//! **Departure D21.** ARCHITECTURE 3's `contract(tcx, def, dcx)` cannot reach a
//! callee's MIR, and at M3 every library item is body-less: [`infer_contracts`]
//! takes a module's bodies and stores every contract in `Tcx`'s memo, and
//! [`contract`] returns the memo or the declared contract.
//!
//! Determinism: no hash map; SCCs, bodies and reports in `ItemPath` and point
//! order, never by an id (ARCHITECTURE 1).

#![forbid(unsafe_code)]

mod access;
mod cx;
mod declared;
mod elaborate;
mod fit;
mod graph;
mod held;
mod infer;
mod init;
mod liveness;
mod loans;
mod marks;
mod movepaths;
mod moves;
mod narrowing;
mod packed;
mod parts;
mod r3;
mod rebind;
mod report;
mod rows;
mod slots;
mod witness;
mod wlive;

pub mod summary;

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use enrang_diag::{Code, DiagCtx};
use enrang_hir::{AdtId, CheckedProgram, ClassContract, Contract, DefId, ItemPath, ModuleId, Tcx};

pub use access::{
    Access, AccessKind, BorrowConflict, check as access_check, loans_overlap, overlap,
};
pub use cx::{BodyCx, CallInfo, SccState, call_info};
pub use enrang_mir::Bodies;
pub use fit::FitError;
pub use graph::Node;
pub use held::{HeldResults, KeyBits, Set, State, StoreError, StoreErrorKind};
pub use init::InitResults;
pub use liveness::LiveSlots;
pub use loans::{Loan, LoanId, LoanKey, LoanKind, LoanPath, Loans, Step, Turn};
pub use marks::{MarkError, MarkOrigin, MarkResults};
pub use movepaths::{MoveData, MovePath, MovePathIdx};
pub use moves::MoveError;
pub use report::{report_conflict, report_contract, report_mark, report_move, report_store};
pub use slots::{SlotId, SlotKind, Slots};
pub use witness::{Witness, WitnessStep};
pub use wlive::{Modes, compute_modes};

/// What inference found, for summaries (plan d.0).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ContractSet {
    /// Per function: one witness per Write permission.
    pub witnesses: BTreeMap<ItemPath, Vec<Witness>>,
    /// Per borrowing class whose flag is set.
    pub class_witnesses: BTreeMap<ItemPath, Witness>,
}

/// Infers the contracts and class flags of one module's bodies, SCC by SCC, and
/// stores each in `Tcx`'s memo (A:1336-1364, D21); reports nothing itself.
pub fn infer_contracts(tcx: &Tcx, bodies: &Bodies, dcx: &mut DiagCtx) -> ContractSet {
    infer::infer(tcx, bodies, dcx)
}

/// A definition's contract: the memo, else the declared one (A:1354, D21).
pub fn contract(tcx: &Tcx, def: DefId) -> Arc<Contract> {
    tcx.contract_memo(def)
        .unwrap_or_else(|| Arc::new(declared::declared(tcx, def)))
}

/// A borrowing class's flag: the memo, else not set.
pub fn class_contract(tcx: &Tcx, adt: AdtId) -> ClassContract {
    tcx.class_contract_memo(adt).unwrap_or(ClassContract {
        writes_through_fields: false,
    })
}

/// What checking a body found that elaboration needs (A:808).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BorrowFacts {
    pub moves: MoveData,
    pub init: InitResults,
    /// The constant literal views (`[literal-view]` `Ref`s) whose loan N4 does
    /// not give, nothing writing through the slot they fill: elaboration makes
    /// each a static (A:970, plan d.12). **Departure:** A:808 lists only `moves`
    /// and `init`; the decision needs the module's bodies (a writing closure's
    /// arrow), which elaboration does not get.
    pub static_views: std::collections::BTreeSet<enrang_mir::Point>,
}

/// Checks one body (plan d.1-d.7, d.9's definition check, d.11).
pub fn check(tcx: &Tcx, bodies: &Bodies, b: &enrang_mir::Body, dcx: &mut DiagCtx) -> BorrowFacts {
    let cx = BodyCx::new(tcx, bodies, b, None);
    let init = InitResults::compute(b, &cx.moves);
    for e in moves::check(&cx, &init) {
        dcx.emit(report_move(&cx, &e));
    }
    let held = HeldResults::run(&cx, false);
    let mark_errors = marks::check(&cx, &MarkResults::run(&cx, &held));
    let live = LiveSlots::compute(&cx);
    let modes = compute_modes(&cx, &held);
    let conflicts = access::check(&cx, &held, &live, &modes);
    // One report per mistake (A:1270): a conflict of mode (EN0706-EN0708) at a
    // marked argument's borrow, or with the loan it makes, follows from the mark
    // error, the one reported; a change of a loop's held source is a mistake of
    // its own (T:667), and so is a move or a drop under that loan.
    let marked = marks::marked_loans(&cx, &mark_errors);
    let follows = |c: &BorrowConflict| {
        let loan = &cx.loans.table[c.loan];
        let mode = matches!(c.code, Code::EN0706 | Code::EN0707 | Code::EN0708);
        let hold = !mode
            || matches!(loan.kind, LoanKind::Hold(_) | LoanKind::HoldCrossing(_))
            || loan.origin == enrang_mir::BorrowOrigin::ForOfHidden;
        let at_borrow = marked
            .iter()
            .find(|(l, _)| cx.loans.table[**l].site == c.at)
            .map(|(_, k)| *k);
        (!hold).then(|| marked.get(&c.loan).copied().or(at_borrow))?
    };
    // A mark error that silenced a conflict loses its edits: making the root
    // writable would leave the conflict, so no fix-it of it compiles (A:1314).
    let silenced: BTreeSet<usize> = conflicts.iter().filter_map(follows).collect();
    for (k, e) in mark_errors.iter().enumerate() {
        let mut d = report_mark(&cx, e);
        if silenced.contains(&k) {
            d.helps.retain(|h| h.edits.is_empty());
        }
        dcx.emit(d);
    }
    for c in conflicts.iter().filter(|c| follows(c).is_none()) {
        dcx.emit(report_conflict(&cx, c));
    }
    for e in access::store_errors(&cx, &held, &conflicts) {
        dcx.emit(report_store(&cx, &e));
    }
    for r in rebind::check(tcx, b) {
        dcx.emit(rebind::report(&r));
    }
    r3::check_definition(&cx, &held, dcx);
    narrowing::check(&cx, dcx);
    let static_views = (cx.loans.table.iter_enumerated())
        .filter(|(id, l)| {
            l.origin == enrang_mir::BorrowOrigin::LiteralView
                && l.kind == LoanKind::Site
                && !modes.exclusive(*id)
        })
        .map(|(_, l)| l.site)
        .collect();
    BorrowFacts {
        moves: cx.moves,
        init,
        static_views,
    }
}

/// The module-level checks: fitting, EN0418, roles, and EN0610 at each `this` of
/// a field initialiser (plan d.10, K8).
pub fn check_module(
    tcx: &Tcx,
    program: &CheckedProgram,
    bodies: &Bodies,
    module: ModuleId,
    dcx: &mut DiagCtx,
) {
    for f in fit::fit_module(tcx, program, bodies, module, dcx) {
        dcx.emit(report_contract(tcx, &f));
    }
    let mut rows = rows::check_signatures(tcx, program, module);
    rows.extend(rows::check_bodies(tcx, bodies));
    for e in rows {
        dcx.emit(report::report_row(tcx, &e));
    }
    // K8 (A:998): `this` in a field initialiser or a subclass's new default.
    for inits in program.field_inits.values() {
        if tcx.def(tcx.adt(inits.adt).def).module == module {
            for &span in &inits.this_spans {
                dcx.emit(report::report_init_this(span));
            }
        }
    }
}

/// Drop elaboration (A:595-605, plan d.12).
pub fn elaborate_drops(tcx: &Tcx, b: enrang_mir::Body, facts: &BorrowFacts) -> enrang_mir::Body {
    elaborate::elaborate(tcx, b, facts)
}

/// EN0804, phase 4 (plan d.6).
pub fn check_packed(tcx: &Tcx, bodies: &Bodies, dcx: &mut DiagCtx) {
    packed::check(tcx, bodies, dcx);
}

/// The default of a reference result, for stage 4 (plan d.8).
pub fn result_default(tcx: &Tcx, ret: enrang_hir::Ty) -> enrang_hir::ResultPerm {
    parts::result_perm(tcx, ret)
}
