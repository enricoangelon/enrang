//! Stage 4's part test (A:1345, S:939; M3 plan d.8; owner 2F): a result with two
//! or more parts (reference parts at any depth, a nullable's payload, a borrowing
//! class value as one part) falls to read-only when two parts may alias.
//!
//! Each part's compared loans come from where `_0` was defined in the return's
//! block or, for a call result, its predecessor: an `Aggregate`'s operands (looking
//! through temporaries defined by `Aggregate`s in the same block and not written
//! or borrowed before), a call whose source arguments pass the test against each
//! other (one part), a by-value tuple parameter the body never writes or borrows
//! (one part); otherwise every part holds `_0`'s whole set (O9). **Choice:** "only
//! reaching definition" is looked for in the same block, and any borrow of the
//! local counts as exclusive.

use enrang_hir::{ResultPerm, Tcx, Ty, TyKind};
use enrang_mir::{
    AggregateKind, Body, Local, LocalKind, Operand, Point, Rvalue, StatementKind, TerminatorKind,
};

use crate::cx::BodyCx;
use crate::held::{HeldResults, KeyBits, Set};
use crate::loans::{LoanKey, Step, Turn};
use crate::slots::SlotId;

pub fn result_perm(tcx: &Tcx, ret: Ty) -> ResultPerm {
    match crate::declared::carrying(tcx, ret) {
        true => ResultPerm::Writable,
        false => ResultPerm::None,
    }
}

/// The parts of a returned type: reference parts and borrowing class values.
fn part_paths(tcx: &Tcx, ty: Ty, path: &mut Vec<u32>, out: &mut Vec<Vec<u32>>) {
    match tcx.kind(ty) {
        TyKind::Nullable(t) => part_paths(tcx, t, path, out),
        TyKind::Tuple(ps) => {
            for (k, &p) in tcx.list(ps).iter().enumerate() {
                path.push(k as u32);
                part_paths(tcx, p, path, out);
                path.pop();
            }
        }
        _ if crate::declared::carrying(tcx, ty) => out.push(path.clone()),
        _ => {}
    }
}

/// One compared loan: its key and bits, and its path in normal form (`None` a
/// leading deref, `through_ref`).
type Cl = (LoanKey, KeyBits, (Local, Vec<Option<Step>>));

fn compared(cx: &BodyCx, set: &Set) -> Vec<Cl> {
    let arg = |i: u32| Local(i + 1);
    set.iter()
        .filter_map(|(&k, &bits)| {
            let path = match k {
                LoanKey::Site(l, _) => {
                    let p = &cx.loans.table[l].path;
                    let lead = p.through_ref.then_some(None);
                    (
                        p.root,
                        lead.into_iter()
                            .chain(p.steps.iter().map(|s| Some(*s)))
                            .collect(),
                    )
                }
                LoanKey::Param(i) if bits.bare => (arg(i), vec![None]),
                LoanKey::Fields(i) | LoanKey::RFields(i) if bits.bare => {
                    (arg(i), vec![None, Some(Step::Fields)])
                }
                _ => return None,
            };
            Some((k, bits, path))
        })
        .collect()
}

/// The bind loan of loop `l`'s site.
fn bind_loan(cx: &BodyCx, l: enrang_hir::LoopId) -> Option<crate::loans::LoanId> {
    let lp = cx.body.meta.loops.iter().find(|x| x.id == l)?;
    cx.loans
        .table
        .iter_enumerated()
        .find(|(_, x)| x.site == lp.bind && x.kind == crate::loans::LoanKind::Site)
        .map(|(id, _)| id)
}

fn conflict(cx: &BodyCx, a: &[Cl], b: &[Cl]) -> bool {
    let holds_bind = |s: &[Cl], l| {
        let lb = bind_loan(cx, l);
        s.iter()
            .any(|(k, _, _)| matches!(k, LoanKey::Site(x, _) if Some(*x) == lb))
    };
    a.iter().any(|(ka, ba, pa)| {
        b.iter().any(|(kb, bb, pb)| {
            if ka == kb
                && let (Some(l), Some(m)) = (ba.mark, bb.mark)
                && l == m
            {
                return !(holds_bind(a, l) && holds_bind(b, l));
            }
            if let (LoanKey::Site(x, s), LoanKey::Site(y, t)) = (ka, kb)
                && x == y
                && *s != *t
            {
                return !matches!(
                    (s, t),
                    (Turn::This, Turn::EarlierThisRun) | (Turn::EarlierThisRun, Turn::This)
                );
            }
            let ((ra, sa), (rb, sb)) = (pa, pb);
            ra == rb && (sa.starts_with(sb) || sb.starts_with(sa))
        })
    })
}

/// The statement or call defining whole local `l` last before `p` in its block,
/// or in the single predecessor's call; `None` when written otherwise first.
fn def_of(b: &Body, l: Local, p: Point) -> Option<(Point, Option<&Rvalue>)> {
    for i in (0..p.index as usize).rev() {
        let at = Point::new(p.block, i);
        match &b.blocks[p.block].stmts[i].kind {
            StatementKind::Assign { dest, value } if dest.local == l => {
                return dest.is_local().then_some((at, Some(value)));
            }
            StatementKind::Assign {
                value: Rvalue::Ref { place, .. },
                ..
            } if place.local == l => {
                return None;
            }
            _ => {}
        }
    }
    let preds: Vec<_> = b
        .blocks
        .iter_enumerated()
        .filter(|(_, x)| x.term.kind.successors().contains(&p.block))
        .collect();
    match preds.as_slice() {
        [(bb, x)] if matches!(&x.term.kind, TerminatorKind::Call { dest, .. } if dest.local == l && dest.is_local()) => {
            Some((b.terminator_point(*bb), None))
        }
        _ => None,
    }
}

/// A part's compared sets, outermost level first (A:1356): at each level, the
/// part's position in that level's tuple, or its argument's position at a call,
/// and the set its operand there held where that level's value was built or used.
/// Two parts meet at the first level where their positions differ, or where
/// either trace ends. So the parts of one local meet by what its literal's
/// operands held when it was built, and a part of it meets every other part by
/// what the local holds where it is used, after every rename, mark change and kill
/// since (O9): a borrow made before a `let` parameter was repointed, kept in a
/// tuple local returned or passed beside a borrow through its new target, meets
/// that borrow as the whole parameter (`TK-01-local-kill`).
type Trace = Vec<(u32, Set)>;

/// Whether two traced parts may alias.
fn traces_meet(cx: &BodyCx, a: &Trace, b: &Trace) -> bool {
    let mut i = 0;
    while a[i].0 == b[i].0 && i + 1 < a.len() && i + 1 < b.len() {
        i += 1;
    }
    conflict(cx, &compared(cx, &a[i].1), &compared(cx, &b[i].1))
}

/// Whether any two of `traces` may alias.
fn any_meet(cx: &BodyCx, traces: &[Trace]) -> bool {
    (0..traces.len())
        .any(|i| (i + 1..traces.len()).any(|j| traces_meet(cx, &traces[i], &traces[j])))
}

/// Extends `trace` with the levels of the part below `rel` of operand `op`, at
/// position `pos` of a value built, or a call made, at `at`.
fn operand_trace(
    cx: &BodyCx,
    held: &HeldResults,
    op: &Operand,
    at: Point,
    pos: u32,
    rel: &[u32],
    trace: &mut Trace,
) {
    let Some(p) = op.place().filter(|p| p.is_local()) else {
        trace.push((pos, Set::new()));
        return;
    };
    let whole = held.held_at(at, SlotId::Local(p.local));
    trace.push((pos, whole.clone()));
    if rel.is_empty() {
        return;
    }
    match def_of(cx.body, p.local, at) {
        Some((d, Some(rv))) => value_trace(cx, held, rv, d, rel, trace),
        // A call result kept in a temporary counts as one part when its source
        // arguments pass the part test (A:1356): its first part holds its whole
        // set, the others nothing, so it meets every other part of the value
        // once and none of its own (`return two(a, x)` at `[&i64, &i64] | null`).
        Some((d, None)) if one_part_call(cx, held, d) => {
            let mut paths = Vec::new();
            part_paths(
                cx.tcx,
                cx.body.locals[p.local].ty,
                &mut Vec::new(),
                &mut paths,
            );
            match paths.first().is_some_and(|f| f.as_slice() == rel) {
                true => trace.push((0, whole)),
                false => trace.push((1, Set::new())),
            }
        }
        _ => {}
    }
}

/// Whether the call at `at` passes the part test: its arguments for the callee's
/// sources, each reference part of a by-value tuple argument counting as an
/// argument of its own, pass it against each other (A:1356, `TK-01-tuple-arg`).
/// Parts of one tuple argument meet by what its literal's operands held, and
/// different arguments by what each holds at the call, so a tuple local built
/// before a `let` parameter was repointed meets a borrow through its new target
/// as the whole parameter (`TK-01-local-kill`, H40).
fn one_part_call(cx: &BodyCx, held: &HeldResults, at: Point) -> bool {
    let b = cx.body;
    let TerminatorKind::Call { callee, args, .. } = &b.blocks[at.block].term.kind else {
        return false;
    };
    let ci = crate::declared::call_info(cx.tcx, b, cx.scc, callee, args);
    let enrang_hir::RetSources::Params(s) = &ci.sources else {
        return true;
    };
    let mut traces: Vec<Trace> = Vec::new();
    for (k, &i) in s.iter().enumerate() {
        let Some(op) = ci.args_map.get(i as usize).and_then(|&pos| args.get(pos)) else {
            continue;
        };
        let Some(pl) = op.place().filter(|p| p.is_local()) else {
            continue;
        };
        let ty = b.locals[pl.local].ty;
        let by_value_tuple = matches!(
            cx.tcx.kind(crate::loans::strip_null(cx.tcx, ty)),
            TyKind::Tuple(_)
        );
        match by_value_tuple {
            true => {
                let mut paths = Vec::new();
                part_paths(cx.tcx, ty, &mut Vec::new(), &mut paths);
                for path in paths {
                    let mut trace = Trace::new();
                    operand_trace(cx, held, op, at, k as u32, &path, &mut trace);
                    traces.push(trace);
                }
            }
            false => traces.push(vec![(k as u32, held.held_at(at, SlotId::Local(pl.local)))]),
        }
    }
    !any_meet(cx, &traces)
}

/// Extends `trace` with the levels of the part below `rel` of `rv`, built at `at`.
fn value_trace(
    cx: &BodyCx,
    held: &HeldResults,
    rv: &Rvalue,
    at: Point,
    rel: &[u32],
    trace: &mut Trace,
) {
    match (rv, rel) {
        (Rvalue::Aggregate(AggregateKind::Present, ops), _) => {
            if let Some(o) = ops.first() {
                operand_trace(cx, held, o, at, 0, rel, trace);
            }
        }
        (Rvalue::Aggregate(AggregateKind::Tuple, ops), [k, rest @ ..]) => {
            if let Some(o) = ops.get(*k as usize) {
                operand_trace(cx, held, o, at, *k, rest, trace);
            }
        }
        _ => {}
    }
}

/// Whether two parts of the value returned at some `Return` may alias.
pub fn aliased(cx: &BodyCx, held: &HeldResults) -> bool {
    let b = cx.body;
    let mut paths = Vec::new();
    part_paths(cx.tcx, b.ret_ty(), &mut Vec::new(), &mut paths);
    if paths.len() < 2 {
        return false;
    }
    held.ret_at_returns().iter().any(|(p, whole)| {
        let mut def = def_of(b, Local::RETURN, *p);
        // Look through `_0 = move t` to t's own definition.
        if let Some((at, Some(Rvalue::Use(Operand::Move(t) | Operand::Copy(t))))) = def
            && t.is_local()
        {
            if b.locals[t.local].kind == LocalKind::Arg
                && t.local.0 <= b.arg_count
                && !written(b, t.local)
            {
                return false;
            }
            def = def_of(b, t.local, at);
        }
        let all_whole = || vec![vec![(0, whole.clone())]; paths.len()];
        let traces: Vec<Trace> = match def {
            Some((at, Some(rv))) => (paths.iter())
                .map(|path| {
                    let mut trace = Trace::new();
                    value_trace(cx, held, rv, at, path, &mut trace);
                    if trace.is_empty() {
                        trace.push((0, whole.clone()));
                    }
                    trace
                })
                .collect(),
            Some((at, None)) => {
                if !matches!(&b.blocks[at.block].term.kind, TerminatorKind::Call { .. }) {
                    return true;
                }
                if one_part_call(cx, held, at) {
                    return false;
                }
                all_whole()
            }
            None => all_whole(),
        };
        any_meet(cx, &traces)
    })
}

/// Whether the body writes local `l` (whole or a part) or borrows it.
fn written(b: &Body, l: Local) -> bool {
    b.blocks
        .iter()
        .flat_map(|x| x.stmts.iter())
        .any(|s| match &s.kind {
            StatementKind::Assign { dest, value } => {
                (dest.local == l && !b.projs(*dest).contains(&enrang_mir::Proj::Deref))
                    || matches!(value, Rvalue::Ref { place, .. } if place.local == l)
            }
            _ => false,
        })
}
