//! R3 (A:1275-1299; M3 plan d.9; owner 2F): sources and through sets from
//! `held(_0)`, stores from `held(Caller(m))`, and the definition check EN0710,
//! EN0712, EN0714 at each `Return`.

use std::collections::BTreeMap;

use enrang_diag::{Code, DiagCtx};
use enrang_hir::{AdtId, Contract, DefId, Receiver, RetSources, Store, Tcx, Ty, TyKind};
use enrang_mir::{Body, BodyOwner, Place};

use crate::access::{Access, AccessKind, BorrowConflict};
use crate::cx::BodyCx;
use crate::declared::{declared, sig_args};
use crate::fit::{FitError, base_decl};
use crate::held::HeldResults;
use crate::loans::LoanKey;
use crate::report::{report_conflict, report_contract};

/// The argument types of a body, `_1.._arg_count`.
pub fn arg_tys(b: &Body) -> Vec<Ty> {
    b.args().map(|l| b.locals[l].ty).collect()
}

/// The class behind a borrowing argument type, or `None` for a tuple (whose flag
/// is always set).
pub fn class_behind(tcx: &Tcx, ty: Ty) -> Option<AdtId> {
    match tcx.kind(ty) {
        TyKind::Ref(t) | TyKind::Nullable(t) => class_behind(tcx, t),
        TyKind::Adt(a, _) => Some(a),
        _ => None,
    }
}

/// Stage 2's answer for one body (A:1279, A:1281): the sources, `through_fields`
/// (only where the class behind is off, by `flag`), `through_read`, the stores.
pub fn found(
    cx: &BodyCx,
    held: &HeldResults,
    flag: &dyn Fn(AdtId) -> bool,
) -> (Vec<u32>, Vec<u32>, Vec<u32>, Vec<Store>) {
    let tys = arg_tys(cx.body);
    let off = |j: u32| {
        tys.get(j as usize)
            .and_then(|&t| class_behind(cx.tcx, t))
            .is_some_and(|a| !flag(a))
    };
    // Per index: Param, Fields, RFields reached.
    let reach = |set: &crate::held::Set| {
        let mut m: BTreeMap<u32, [bool; 3]> = BTreeMap::new();
        for k in set.keys() {
            match *k {
                LoanKey::Param(i) => m.entry(i).or_default()[0] = true,
                LoanKey::Fields(i) => m.entry(i).or_default()[1] = true,
                LoanKey::RFields(i) => m.entry(i).or_default()[2] = true,
                _ => {}
            }
        }
        m
    };
    let mut ret = crate::held::Set::new();
    for (_, s) in held.ret_at_returns() {
        ret.extend(s);
    }
    let r = reach(&ret);
    let sources = r.keys().copied().collect();
    let tf = r
        .iter()
        .filter(|(j, b)| b[1] && !b[0] && off(**j))
        .map(|(j, _)| *j);
    let tr = r
        .iter()
        .filter(|(_, b)| b[2] && !b[0] && !b[1])
        .map(|(j, _)| *j);
    let mut stores = Vec::new();
    for m in 0..tys.len() as u32 {
        let (h, rf) = held.caller_at_returns(m);
        let read = reach(&rf);
        for (j, b) in reach(&h) {
            let read_set_only = b[2] && !b[0] && !b[1];
            stores.push(Store {
                from: j,
                into: m,
                fields_only: !read_set_only && (b[1] || b[2]) && !b[0] && off(j),
                read: read.contains_key(&j),
                read_set_only,
            });
        }
    }
    (sources, tf.collect(), tr.collect(), stores)
}

/// Whether `b` is trusted for its sources: no `unsafe`, `asm`, `unsafe function` or
/// `@naked` (A:1279; N12).
pub fn is_unsafe(tcx: &Tcx, b: &Body) -> bool {
    !b.unsafe_regions.is_empty()
        || match b.owner {
            BodyOwner::Fn(d) => {
                tcx.def(d).attrs.naked || tcx.sig_opt(d).is_some_and(|s| s.unsafety)
            }
            _ => false,
        }
}

/// The contract indices of a local function's hidden arguments in `b`.
pub(crate) fn hidden(tcx: &Tcx, d: DefId, b: &Body) -> Vec<u32> {
    let declared = sig_args(tcx, d).len();
    let end = b.arg_count as usize - usize::from(b.meta.defaults_count.is_some());
    (declared as u32..end as u32).collect()
}

/// The definition check at each `Return` (A:1287 table).
pub fn check_definition(cx: &BodyCx, held: &HeldResults, dcx: &mut DiagCtx) {
    let tcx = cx.tcx;
    let def = match cx.body.owner {
        BodyOwner::Fn(d) => Some(d),
        _ => None,
    };
    let own = def.is_some_and(|d| {
        tcx.sig_opt(d)
            .is_some_and(|s| s.receiver == Some(Receiver::Move))
    });
    // Sources fixed elsewhere: a base declaration's (with `this`), or the
    // signature defaults of an unsafe body.
    let base = def.and_then(|d| base_decl(tcx, d));
    let fixed: Option<Contract> = match (def, base) {
        (_, Some(b)) => Some(crate::declared::as_virtual(
            (*crate::contract(tcx, b)).clone(),
        )),
        (Some(d), None) if is_unsafe(tcx, cx.body) => Some(declared(tcx, d)),
        _ => None,
    };
    let hidden = def.map_or_else(Vec::new, |d| hidden(tcx, d, cx.body));
    let mut outside_once = false;
    for (p, set) in held.ret_at_returns() {
        let span = cx.body.blocks[p.block].term.span;
        for k in set.keys() {
            let (i, param) = match *k {
                LoanKey::Param(i) => (i, true),
                LoanKey::Fields(i) | LoanKey::RFields(i) => (i, false),
                LoanKey::Site(l, _) => {
                    let loan = &cx.loans.table[l];
                    if loan.path.through_ref {
                        continue;
                    }
                    // A returned reference to a local or a temporary alike is
                    // EN0710, as the access check maps the drop it meets (A:1298,
                    // T:1109 `Q41-written`), so the two are one report.
                    let c = BorrowConflict {
                        code: Code::EN0710,
                        access: Access {
                            place: Place::local(enrang_mir::Local::RETURN),
                            kind: AccessKind::StorageDead,
                            span: loan.span,
                            method: None,
                        },
                        loan: l,
                        holder: Some(enrang_mir::Local::RETURN),
                        later_use: None,
                        at: p,
                        others: Vec::new(),
                    };
                    dcx.emit(report_conflict(cx, &c));
                    continue;
                }
                LoanKey::Hold(_) => continue,
            };
            let Some(d) = def else { continue };
            let code = if own && param && i == 0 {
                Code::EN0710
            } else if !outside_once
                && (hidden.contains(&i) || fixed.as_ref().is_some_and(|c| outside(c, i, param, *k)))
            {
                outside_once = true;
                Code::EN0714
            } else {
                continue;
            };
            let f = FitError {
                code,
                found: d,
                member: base.unwrap_or(d),
                site: span,
                captured: None,
                marked: None,
                slot: None,
            };
            dcx.emit(report_contract(tcx, &f));
        }
    }
}

/// Whether key `k` of index `i` lies outside the fixed contract `c` (A:1287).
pub(crate) fn outside(c: &Contract, i: u32, param: bool, k: LoanKey) -> bool {
    let srcs = match &c.sources {
        RetSources::Params(s) => s.as_slice(),
        RetSources::NoLoans => &[],
    };
    !srcs.contains(&i)
        || (param && i != 0 && c.through_fields.contains(&i))
        || (!matches!(k, LoanKey::RFields(_)) && c.through_read.contains(&i))
}
