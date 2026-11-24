//! The per-body context of phase 3 and the call seam (M3 plan g.2; owner 1B):
//! what every analysis reads, and `call_info`, a callee's contract with each
//! contract index mapped to its argument.

use std::cell::RefCell;
use std::collections::BTreeMap;

use enrang_hir::{AdtId, Contract, DefId, Perm, ResultPerm, RetSources, Store, Tcx};
use enrang_mir::{Bodies, Body, Callee, Operand};

use crate::loans::Loans;
use crate::movepaths::MoveData;
use crate::slots::Slots;

/// The contracts and flags of the SCC being inferred, read before the memo
/// (plan d.8).
#[derive(Clone, Debug, Default)]
pub struct SccState {
    pub current: BTreeMap<DefId, Contract>,
    pub flags: BTreeMap<AdtId, bool>,
}

/// One body under check.
pub struct BodyCx<'a> {
    pub tcx: &'a Tcx,
    pub body: &'a Body,
    pub bodies: &'a Bodies,
    pub scc: Option<&'a SccState>,
    pub slots: Slots,
    pub loans: Loans,
    pub moves: MoveData,
    /// Whether a call's store may look at its user callee's own body (held's
    /// `callee_rejects`); off in that look itself, so it never recurses.
    pub probe: bool,
    /// What that look found, per callee.
    pub rejects: RefCell<BTreeMap<DefId, bool>>,
}

impl<'a> BodyCx<'a> {
    pub fn new(
        tcx: &'a Tcx,
        bodies: &'a Bodies,
        body: &'a Body,
        scc: Option<&'a SccState>,
    ) -> BodyCx<'a> {
        BodyCx {
            tcx,
            body,
            bodies,
            scc,
            slots: Slots::collect(tcx, body),
            loans: Loans::collect(tcx, body),
            moves: MoveData::build(tcx, body),
            probe: true,
            rejects: RefCell::new(BTreeMap::new()),
        }
    }
}

/// A callee's contract at one call, `args_map[i]` the argument of contract index
/// `i` (plan g.2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallInfo {
    pub perms: Vec<Perm>,
    pub sources: RetSources,
    pub through_fields: Vec<u32>,
    pub through_read: Vec<u32>,
    pub stores: Vec<Store>,
    pub result: ResultPerm,
    pub args_map: Vec<usize>,
}

/// The contract a call sees, mapped to its arguments (plan d.8, A:1176-1179):
/// stage 2F's `declared::call_info` (contract index = argument position).
pub fn call_info(cx: &BodyCx, callee: &Callee, args: &[Operand]) -> CallInfo {
    crate::declared::call_info(cx.tcx, cx.body, cx.scc, callee, args)
}
