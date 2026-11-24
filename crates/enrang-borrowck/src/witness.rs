//! Witnesses (A:1364; M3 plan d.8; owner 2F): for each Write permission and each
//! set flag, the shortest chain of calls ending at a direct write, ties broken by
//! the smallest span start of the first step; a call into another module that
//! makes the argument Write is one terminal step, so a chain never leaves its
//! module. Kept in `ContractSet`, printed by `--emit=summary`.
//!
//! A step is found by replaying N3 seeded with one event at a time (a direct
//! write, or one Write argument of one call) and asking whether the parameter is
//! then write-live at entry.

use std::collections::BTreeMap;

use enrang_base::Span;
use enrang_hir::{DefId, ItemPath, Perm, Tcx};
use enrang_mir::{Bodies, BodyOwner, Callee, Local, Point, Rvalue, StatementKind, TerminatorKind};

use crate::cx::SccState;
use crate::wlive::{Seed, WLive};

/// One step: a call into `callee`, or the direct write when `callee` is `None`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessStep {
    pub callee: Option<ItemPath>,
    pub span: Span,
    pub text: String,
    /// For a call into another module, the callee's contract index the argument
    /// is passed to: the witness `--emit=summary` appends (A:1373).
    pub param: Option<u32>,
}

/// The chain behind a Write permission (`param`) or a class flag (`None`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Witness {
    pub param: Option<u32>,
    pub steps: Vec<WitnessStep>,
}

/// The witness of contract index `param` (at `local`, part `path`) of `f`, given
/// the witnesses `known` of the module so far, by (function, index).
pub fn of_param(
    tcx: &Tcx,
    bodies: &Bodies,
    scc: &SccState,
    f: DefId,
    (param, local, path): (u32, Local, &[u32]),
    known: &BTreeMap<(DefId, u32), Witness>,
) -> Option<Witness> {
    let b = &bodies[&BodyOwner::Fn(f)];
    let live = |seed: Seed| {
        WLive::compute(tcx, b, bodies, Some(scc), Some(seed)).live_at_entry(local, path)
    };
    let mut best: Option<Vec<WitnessStep>> = None;
    let mut offer = |steps: Vec<WitnessStep>| {
        let key = |s: &Vec<WitnessStep>| (s.len(), s[0].span.lo);
        if best.as_ref().is_none_or(|b| key(&steps) < key(b)) {
            best = Some(steps);
        }
    };
    for (bb, blk) in b.blocks.iter_enumerated() {
        for (i, st) in blk.stmts.iter().enumerate() {
            // Only a write through a place, a store or a closure can be direct.
            let direct = match &st.kind {
                StatementKind::Assign { dest, value } => {
                    b.has_deref(*dest)
                        || !b.projs(*dest).is_empty()
                        || matches!(value, Rvalue::ClosureValue { .. })
                }
                StatementKind::FieldInit { .. } => true,
                StatementKind::Intrinsic { dest, .. } | StatementKind::HostCall { dest, .. } => {
                    dest.is_some_and(|d| b.has_deref(d))
                }
                _ => false,
            };
            if direct && live((Point::new(bb, i), None)) {
                offer(vec![step(None, st.span, "writes through it".into())]);
            }
        }
        let TerminatorKind::Call { callee, args, .. } = &blk.term.kind else {
            continue;
        };
        let at = b.terminator_point(bb);
        if live((at, Some(usize::MAX))) {
            offer(vec![step(None, blk.term.span, "writes through it".into())]);
        }
        let g = match callee {
            Callee::Fn(r) | Callee::Virtual { method: r, .. } => Some(r.def),
            Callee::Foreign(r) => Some(r.def),
            _ => None,
        };
        let ci = crate::declared::call_info(tcx, b, Some(scc), callee, args);
        for q in 0..ci.perms.len() {
            if ci.perms[q] != Perm::Write || !live((at, Some(q))) {
                continue;
            }
            let span = blk.term.span;
            let mut steps = match g {
                Some(g) if tcx.def(g).module != tcx.def(f).module => {
                    let text = format!(
                        "passes it to `{}` from `{}`, which changes it",
                        last(tcx, g),
                        tcx.def(g).path.module
                    );
                    let mut s = step(Some(tcx.def(g).path.clone()), span, text);
                    s.param = Some(q as u32);
                    vec![s]
                }
                Some(g) => {
                    let text = format!("passes it to `{}`", last(tcx, g));
                    vec![step(Some(tcx.def(g).path.clone()), span, text)]
                }
                None => vec![step(None, span, "passes it to a writing parameter".into())],
            };
            if let Some(w) = g.and_then(|g| known.get(&(g, q as u32))) {
                if w.steps
                    .iter()
                    .any(|s| s.callee.as_ref() == Some(&tcx.def(f).path))
                {
                    continue;
                }
                steps.extend(w.steps.iter().cloned());
            }
            offer(steps);
        }
    }
    best.map(|steps| Witness {
        param: Some(param),
        steps,
    })
}

fn last(tcx: &Tcx, d: DefId) -> String {
    let p = &tcx.def(d).path;
    p.segments
        .iter()
        .map(|s| s.to_string())
        .collect::<Vec<_>>()
        .join(".")
}

pub fn step(callee: Option<ItemPath>, span: Span, text: String) -> WitnessStep {
    WitnessStep {
        callee,
        span,
        text,
        param: None,
    }
}

/// The text of a witness: its steps joined.
pub fn text(w: &Witness) -> String {
    w.steps
        .iter()
        .map(|s| s.text.as_str())
        .collect::<Vec<_>>()
        .join(", which ")
}
