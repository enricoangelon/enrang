//! Contract inference by the stages of ARCHITECTURE 6.7 (A:1336-1364; M3 plan d.8;
//! owner 2F), SCC by SCC, callees first.
//!
//! Stages 2 (sources and stores, from `held` in keys-only mode) and 3
//! (permissions by N3 at entry, class flags) repeat together until neither
//! changes, every member reading the others' current sets through `SccState`;
//! stage 4 then fixes each result. A definition whose contract or flag the memo
//! already holds keeps it (a stated contract pins it). **Choice:** each round
//! recomputes the sets from the last round's, bounded at 64 rounds.

use std::collections::BTreeMap;

use enrang_diag::DiagCtx;
use enrang_hir::{
    AdtId, ClassContract, Contract, DefId, Mark, Perm, Reason, ResultPerm, RetSources, Tcx, TyKind,
};
use enrang_mir::{
    Bodies, Body, BodyOwner, Local, Operand, Place, PlaceTy, Point, Proj, Rvalue, StatementKind,
    TerminatorKind,
};

use crate::ContractSet;
use crate::cx::{BodyCx, SccState};
use crate::declared::{carrying, declared, is_role, perm_of, perm_slots, ref_parts, sig_args};
use crate::graph::{self, Node};
use crate::held::HeldResults;
use crate::loans::LoanKey;
use crate::marks::{MarkOrigin, MarkResults};
use crate::r3::{arg_tys, class_behind, found, is_unsafe};
use crate::slots::SlotId;
use crate::witness::{self, Witness, WitnessStep, step};
use crate::wlive::WLive;

/// Infers every SCC of `bodies`, callees first, and stores each contract and flag.
pub fn infer(tcx: &Tcx, bodies: &Bodies, _dcx: &mut DiagCtx) -> ContractSet {
    let mut set = ContractSet::default();
    let mut known: BTreeMap<(DefId, u32), Witness> = BTreeMap::new();
    for scc in graph::sccs(tcx, bodies) {
        let fns: Vec<DefId> = scc
            .iter()
            .filter_map(|n| match *n {
                Node::Fn(d) if tcx.contract_memo(d).is_none() => Some(d),
                _ => None,
            })
            .collect();
        let classes: Vec<AdtId> = scc
            .iter()
            .filter_map(|n| match *n {
                Node::Class(a) if tcx.class_contract_memo(a).is_none() => Some(a),
                _ => None,
            })
            .collect();
        let mut st = SccState::default();
        for &f in &fns {
            st.current.insert(f, start(tcx, f));
        }
        let mut whys: BTreeMap<AdtId, Option<WitnessStep>> = BTreeMap::new();
        // Stages 2 and 3 only grow (stores and their bits, Read to Write, a flag
        // off to on), so each round that changes anything adds a fact, and the
        // facts are finite: at most 8 bit sets per (j, m) store pair and one
        // permission per parameter of each member, plus one flag per class. A
        // round past that bound means a transfer that is not monotone, a bug
        // reported as an internal error rather than a silently partial contract.
        let facts: usize = fns
            .iter()
            .map(|&f| {
                let n = tcx.sig_opt(f).map_or(0, |s| s.params.len()) + 1;
                8 * n * n + n
            })
            .sum::<usize>()
            + classes.len();
        let mut rounds = 0usize;
        loop {
            let before = (st.current.clone(), st.flags.clone());
            for &f in &fns {
                let c = stage2(tcx, bodies, &st, f);
                st.current.insert(f, c);
            }
            for &f in &fns {
                let perms = perms(tcx, bodies, &st, f);
                st.current.get_mut(&f).expect("a member").perms = perms;
            }
            for &a in &classes {
                let why = own_flag(tcx, bodies, &st, a);
                let on = why.is_some() || base_flag(tcx, &st, a);
                st.flags.insert(a, on);
                whys.insert(a, why);
            }
            if before == (st.current.clone(), st.flags.clone()) {
                break;
            }
            rounds += 1;
            assert!(
                rounds <= facts + 1,
                "contract inference (stages 2 and 3) did not converge in {rounds} rounds over an SCC of {} functions",
                fns.len()
            );
        }
        // Stage 4 is a greatest fixed point (A:1349, A:1354): every member starts
        // writable and falls, rerun against the others' current results until
        // none changes, so the answer cannot depend on the visit order. A member
        // falls once and its first reason can change only as more reasons apply,
        // so a bound of one round per member and reason kind, plus one, is never
        // reached by a monotone transfer; past it the bug is an internal error.
        let mut rounds = 0usize;
        loop {
            let mut changed = false;
            for &f in &fns {
                let r = result(tcx, bodies, &st, f);
                let c = st.current.get_mut(&f).expect("a member");
                changed |= c.result != r;
                c.result = r;
            }
            if !changed {
                break;
            }
            rounds += 1;
            assert!(
                rounds <= 16 * fns.len() + 1,
                "contract inference (stage 4) did not converge in {rounds} rounds over an SCC of {} functions",
                fns.len()
            );
        }
        for &f in &fns {
            let b = &bodies[&BodyOwner::Fn(f)];
            let mw = moves_or_writes(tcx, f, b);
            st.current.get_mut(&f).expect("a member").moves_or_writes = mw;
        }
        // Witnesses: callees' first, members until none changes.
        for _ in 0..fns.len().max(1) {
            let before = known.clone();
            for &f in &fns {
                let b = &bodies[&BodyOwner::Fn(f)];
                let slots = perm_slots(tcx, &arg_tys(b));
                for (q, (i, path)) in slots.iter().enumerate() {
                    let l = Local(*i as u32 + 1);
                    if st.current[&f].perms.get(q) != Some(&Perm::Write) {
                        continue;
                    }
                    let w = witness::of_param(tcx, bodies, &st, f, (q as u32, l, path), &known)
                        .unwrap_or_else(|| Witness {
                            param: Some(q as u32),
                            steps: vec![step(None, b.span, "is declared writable".into())],
                        });
                    known.insert((f, q as u32), w);
                }
            }
            if known == before {
                break;
            }
        }
        for &f in &fns {
            let ws: Vec<Witness> = known
                .range((f, 0)..=(f, u32::MAX))
                .map(|(_, w)| w.clone())
                .collect();
            if !ws.is_empty() {
                set.witnesses.insert(tcx.def(f).path.clone(), ws);
            }
            let c = st.current[&f].clone();
            tcx.contract_or_insert_with(f, || c);
        }
        for &a in &classes {
            let on = st.flags[&a];
            tcx.class_contract_or_insert_with(a, || ClassContract {
                writes_through_fields: on,
            });
            if on {
                let path = tcx.def(tcx.adt(a).def).path.clone();
                let why = whys.get(&a).cloned().flatten().unwrap_or_else(|| {
                    step(
                        None,
                        tcx.def(tcx.adt(a).def).span,
                        "its base writes through its fields".into(),
                    )
                });
                set.class_witnesses.insert(
                    path,
                    Witness {
                        param: None,
                        steps: vec![why],
                    },
                );
            }
        }
    }
    set
}

/// A member's contract before the first round: its marks, no sources, no stores,
/// and as result what its signature says (a same-SCC call counts as writable
/// unless `readonly`, A:1344).
fn start(tcx: &Tcx, f: DefId) -> Contract {
    let mut c = declared(tcx, f);
    c.sources = RetSources::NoLoans;
    if matches!(c.result, ResultPerm::ReadOnly(Reason::StringPart)) {
        c.result = ResultPerm::Writable;
    }
    c
}

fn flag_of(tcx: &Tcx, st: &SccState, a: AdtId) -> bool {
    match st.flags.get(&a) {
        Some(&f) => f,
        None => crate::class_contract(tcx, a).writes_through_fields,
    }
}

fn base_flag(tcx: &Tcx, st: &SccState, a: AdtId) -> bool {
    match tcx
        .adt(a)
        .as_class()
        .and_then(|c| c.base)
        .map(|t| tcx.kind(t))
    {
        Some(TyKind::Adt(b, _)) => flag_of(tcx, st, b),
        _ => false,
    }
}

/// Stage 2 (A:1343, A:1279-1281): sources and through sets from `held(_0)`,
/// stores from `held(Caller(m))`; an unsafe body takes the signature's default
/// sources.
fn stage2(tcx: &Tcx, bodies: &Bodies, st: &SccState, f: DefId) -> Contract {
    let b = &bodies[&BodyOwner::Fn(f)];
    let mut c = st.current[&f].clone();
    let cx = BodyCx::new(tcx, bodies, b, Some(st));
    let held = HeldResults::run(&cx, true);
    let (srcs, tf, tr, stores) = found(&cx, &held, &|a| flag_of(tcx, st, a));
    if is_unsafe(tcx, b) {
        c.sources = declared(tcx, f).sources;
    } else {
        c.sources = match srcs.is_empty() || !carrying(tcx, b.ret_ty()) {
            true => RetSources::NoLoans,
            false => RetSources::Params(srcs),
        };
        c.through_fields = tf;
        c.through_read = tr;
    }
    c.stores = stores;
    c
}

/// Stage 3's permissions (A:1344): Write iff write-live at entry, `let` always,
/// Own for `move`; in an unsafe body every reference starts Write and `const`
/// lowers one to Read (N12), but never for a role (N11).
fn perms(tcx: &Tcx, bodies: &Bodies, st: &SccState, f: DefId) -> Vec<Perm> {
    let b = &bodies[&BodyOwner::Fn(f)];
    let w = WLive::compute(tcx, b, bodies, Some(st), None);
    let marks = sig_args(tcx, f);
    let unsafe_ = is_unsafe(tcx, b) && !is_role(tcx, f);
    let perm = |pos: usize, path: &[u32]| {
        let (mark, own) = marks.get(pos).map_or((Mark::None, false), |a| (a.1, a.2));
        match (own, mark) {
            (true, _) => Perm::Own,
            (_, Mark::Let) if path.is_empty() => Perm::Write,
            // N12: in an unsafe body every reference, a part of a `let` tuple
            // included, starts Write; only `const` lowers it.
            (_, m) if unsafe_ && m != Mark::Const => Perm::Write,
            _ if !unsafe_ && w.live_at_entry(Local(pos as u32 + 1), path) => Perm::Write,
            _ => Perm::Read,
        }
    };
    perm_slots(tcx, &arg_tys(b))
        .iter()
        .map(|(i, path)| perm(*i, path))
        .collect()
}

/// Whether place `p` reads a reference out of a field of class `a` not declared
/// `readonly` (the field itself, or the tuple part it reaches), and whether it
/// then dereferences it.
fn field_read(tcx: &Tcx, b: &Body, p: Place, a: AdtId) -> Option<bool> {
    let mut pt = PlaceTy::of(b.locals[p.local].ty);
    let mut field: Option<(&enrang_hir::FieldDef, Vec<u32>)> = None;
    for &proj in b.projs(p) {
        match (proj, tcx.kind(pt.ty), &mut field) {
            (Proj::Field(f), TyKind::Adt(x, _), None) if x == a && pt.variant.is_none() => {
                field = Some((tcx.field_def(a, None, f), Vec::new()));
            }
            (Proj::Field(k), TyKind::Tuple(_), Some((_, path))) => path.push(k.0),
            (Proj::Deref, _, Some((fd, path))) => return readable(tcx, fd, path).then_some(true),
            _ => {}
        }
        pt = pt.project(tcx, proj)?;
    }
    let (fd, path) = field?;
    readable(tcx, fd, &path).then_some(false)
}

fn readable(tcx: &Tcx, fd: &enrang_hir::FieldDef, path: &[u32]) -> bool {
    ref_parts(tcx, fd.ty)
        .iter()
        .any(|q| q.starts_with(path) && !fd.readonly_refs.contains(q))
}

/// Why class `a` writes through its own fields, if it does (A:1338): a tuple
/// field with a writable part, a reference read from a field that is write-live
/// where read (in an unsafe body of a method not `const`, any read), or a
/// writable result reached through its fields.
fn own_flag(tcx: &Tcx, bodies: &Bodies, st: &SccState, a: AdtId) -> Option<WitnessStep> {
    let class = tcx.adt(a).as_class()?;
    for fd in &class.fields {
        let t = match tcx.kind(fd.ty) {
            TyKind::Nullable(t) => t,
            _ => fd.ty,
        };
        if matches!(tcx.kind(t), TyKind::Tuple(_)) && readable(tcx, fd, &[]) {
            return Some(step(
                None,
                fd.span,
                format!("its field `{}` holds writable parts", fd.name),
            ));
        }
    }
    let mut best: Option<WitnessStep> = None;
    for b in graph::class_bodies(tcx, bodies, a) {
        let def = graph::owner_def(b.owner);
        let konst = def.is_some_and(|d| {
            tcx.sig_opt(d)
                .is_some_and(|s| s.receiver == Some(enrang_hir::Receiver::Ref(Mark::Const)))
        });
        let unsafe_ = is_unsafe(tcx, b) && !konst;
        let w = WLive::compute(tcx, b, bodies, Some(st), None);
        for (bb, blk) in b.blocks.iter_enumerated() {
            for (i, s) in blk.stmts.iter().enumerate() {
                let StatementKind::Assign { dest, value } = &s.kind else {
                    continue;
                };
                let at = Point::new(bb, i);
                let read = match value {
                    Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                    | Rvalue::Convert(_, Operand::Copy(p) | Operand::Move(p))
                    | Rvalue::Ref { place: p, .. } => field_read(tcx, b, *p, a).is_some(),
                    _ => false,
                };
                let written = (read
                    && (unsafe_
                        || w.dest_live(at, *dest, &[])
                        || w.res.analysis.writes_through(*dest)))
                    || field_read(tcx, b, *dest, a) == Some(true);
                if written && best.as_ref().is_none_or(|x| s.span.lo < x.span.lo) {
                    best = Some(step(
                        None,
                        s.span,
                        "writes through a reference read from its fields".into(),
                    ));
                }
            }
        }
        if best.is_none() && returns_field(tcx, bodies, st, a, b) {
            best = Some(step(
                None,
                b.span,
                "returns a writable reference read from its fields".into(),
            ));
        }
    }
    best
}

/// Whether `b` returns a reference reached through the fields of a class `a`
/// value, in a result that may be writable (A:1338; held and marks).
fn returns_field(tcx: &Tcx, bodies: &Bodies, st: &SccState, a: AdtId, b: &Body) -> bool {
    let ret = b.ret_ty();
    let ro = graph::owner_def(b.owner)
        .filter(|_| matches!(b.owner, BodyOwner::Fn(_)))
        .and_then(|d| tcx.sig_opt(d))
        .is_some_and(|s| s.ret_readonly);
    if ro || ref_parts(tcx, ret).is_empty() {
        return false;
    }
    let tys = arg_tys(b);
    let cx = BodyCx::new(tcx, bodies, b, Some(st));
    let held = HeldResults::run(&cx, true);
    let marks = MarkResults::run(&cx, &held);
    held.ret_at_returns().iter().any(|(p, set)| {
        marks.marks_at(*p, SlotId::Local(Local::RETURN)).is_empty()
            && set.keys().any(|k| {
                matches!(k, LoanKey::Fields(i)
                    if tys.get(*i as usize).and_then(|&t| class_behind(tcx, t)) == Some(a))
            })
    })
}

/// The reason a mark gives a result (plan d.8 stage 4).
fn mark_reason(tcx: &Tcx, m: MarkOrigin) -> Reason {
    let path = |d: DefId| tcx.def(d).path.clone();
    #[allow(unreachable_patterns)]
    match m {
        MarkOrigin::ConstRoot(_) | MarkOrigin::ByValueParam(_) => Reason::ConstRoot,
        MarkOrigin::TopConst(d) | MarkOrigin::ConstPointing(d) => Reason::Constant(path(d)),
        MarkOrigin::ConstLiteral(_) => Reason::ConstLiteral,
        MarkOrigin::ReadonlyField(a, f) | MarkOrigin::ReadonlyRef(a, f) => {
            Reason::ReadonlyField(path(tcx.adt(a).def), f)
        }
        MarkOrigin::RawDerived(_) => Reason::RawDeref,
        MarkOrigin::ReadOnlyResult(d) => Reason::ReadonlyResult(path(d)),
        _ => Reason::StringPart,
    }
}

/// Stage 4 (A:1345), a greatest fixed point from writable, the first cause in this
/// order (choice): `readonly` written; a `through_read` source of a reference
/// result; a read-only mark on a returned value; a `&string` result from a Read
/// `&string` source; a stored source; two aliased parts.
fn result(tcx: &Tcx, bodies: &Bodies, st: &SccState, f: DefId) -> ResultPerm {
    let b = &bodies[&BodyOwner::Fn(f)];
    let c = &st.current[&f];
    let ret = b.ret_ty();
    if !carrying(tcx, ret) {
        return ResultPerm::None;
    }
    if tcx.sig_opt(f).is_some_and(|s| s.ret_readonly) {
        return ResultPerm::ReadOnly(Reason::Declared);
    }
    let refs = !ref_parts(tcx, ret).is_empty();
    let tys = arg_tys(b);
    // The full `held`, bind marks included: N6's part test reads them (A:1234).
    let cx = BodyCx::new(tcx, bodies, b, Some(st));
    let held = HeldResults::run(&cx, false);
    let marks = MarkResults::run(&cx, &held);
    if refs && let Some(&j) = c.through_read.first() {
        let a = tys.get(j as usize).and_then(|&t| class_behind(tcx, t));
        let path = |a: AdtId| tcx.def(tcx.adt(a).def).path.clone();
        // The `readonly &` field the result is reached from, by the mark a
        // returned value carries; else the class's first such field.
        let marked = held.ret_at_returns().into_iter().find_map(|(p, _)| {
            (marks.marks_at(p, SlotId::Local(Local::RETURN)).into_keys()).find_map(|m| match m {
                MarkOrigin::ReadonlyRef(x, f) | MarkOrigin::ReadonlyField(x, f) => {
                    Some(Reason::ReadonlyField(path(x), f))
                }
                _ => None,
            })
        });
        let field = marked.or_else(|| {
            let a = a?;
            let class = tcx.adt(a).as_class()?;
            let f = class
                .fields
                .iter()
                .position(|fd| fd.readonly_refs.contains(&Vec::new()))?;
            Some(Reason::ReadonlyField(
                path(a),
                enrang_hir::FieldIdx(f as u32),
            ))
        });
        if let Some(r) = field {
            return ResultPerm::ReadOnly(r);
        }
    }
    let srcs = match &c.sources {
        RetSources::Params(s) => s.clone(),
        RetSources::NoLoans => Vec::new(),
    };
    // S:773: a body containing `unsafe` returns a raw-derived `&*p`, or the view
    // a `fromRaw` makes, under the signature-default sources, so the result is as
    // changeable as they are; with no reference parameter, so no source (rule
    // 3), it keeps a read-only mark, as a reference to a static does, whatever
    // made it, and this lives in the contract, so an importer sees it too.
    let unsafe_ = is_unsafe(tcx, b);
    if unsafe_ && srcs.is_empty() {
        return ResultPerm::ReadOnly(Reason::RawDeref);
    }
    for (p, _) in held.ret_at_returns() {
        if let Some((&m, _)) = marks
            .marks_at(p, SlotId::Local(Local::RETURN))
            .iter()
            .find(|(m, _)| !(unsafe_ && matches!(m, MarkOrigin::RawDerived(_))))
        {
            return ResultPerm::ReadOnly(mark_reason(tcx, m));
        }
    }
    let string = |t| matches!(tcx.kind(t), TyKind::Ref(s) if matches!(tcx.kind(s), TyKind::Str));
    let plain = |t| match tcx.kind(t) {
        TyKind::Nullable(x) => string(x),
        _ => string(t),
    };
    let slots = perm_slots(tcx, &tys);
    let string_src = srcs.iter().any(|&j| {
        let j = j as usize;
        (plain(tys[j]) && perm_of(&slots, &c.perms, j) == Some(Perm::Read))
            || slots.iter().enumerate().any(|(k, (i, path))| {
                *i == j
                    && !path.is_empty()
                    && c.perms.get(k) == Some(&Perm::Read)
                    && part_ty(tcx, tys[j], path).is_some_and(string)
            })
    });
    if string_src
        && ref_parts(tcx, ret)
            .iter()
            .any(|p| part_ty(tcx, ret, p).is_some_and(plain))
    {
        return ResultPerm::ReadOnly(Reason::StringPart);
    }
    if let Some(s) = c.stores.iter().find(|s| srcs.contains(&s.from)) {
        return ResultPerm::ReadOnly(Reason::StoredSource(s.from));
    }
    if crate::parts::aliased(&cx, &held) {
        return ResultPerm::ReadOnly(Reason::AliasedParts);
    }
    ResultPerm::Writable
}

/// The type of part `path` of `ty`, a nullable looked through.
pub fn part_ty(tcx: &Tcx, ty: enrang_hir::Ty, path: &[u32]) -> Option<enrang_hir::Ty> {
    let mut t = ty;
    for &k in path {
        if let TyKind::Nullable(x) = tcx.kind(t) {
            t = x;
        }
        t = match tcx.kind(t) {
            TyKind::Tuple(ps) => *tcx.list(ps).get(k as usize)?,
            _ => return None,
        };
    }
    Some(t)
}

/// [K2]: per by-value parameter, whether the body moves it or writes it.
fn moves_or_writes(tcx: &Tcx, f: DefId, b: &Body) -> Vec<bool> {
    let first = usize::from(tcx.takes_this(f));
    let Some(sig) = tcx.sig_opt(f) else {
        return Vec::new();
    };
    let by_value: Vec<Local> = (0..sig.params.len())
        .filter(|&i| !matches!(tcx.kind(sig.params[i].ty), TyKind::Ref(_)))
        .map(|i| Local((first + i) as u32 + 1))
        .collect();
    let touched = |l: Local, p: Place, write: bool| {
        p.local == l && (!write || !b.projs(p).contains(&Proj::Deref))
    };
    by_value
        .iter()
        .map(|&l| {
            b.blocks.iter().any(|blk| {
                let ops = |op: &Operand| matches!(op, Operand::Move(p) if touched(l, *p, false));
                blk.stmts.iter().any(|s| match &s.kind {
                    StatementKind::Assign { dest, value } => {
                        touched(l, *dest, true)
                            || match value {
                                Rvalue::Use(op) | Rvalue::Convert(_, op) => ops(op),
                                Rvalue::Aggregate(_, xs) => xs.iter().any(ops),
                                _ => false,
                            }
                    }
                    _ => false,
                }) || matches!(&blk.term.kind, TerminatorKind::Call { args, .. } if args.iter().any(ops))
            })
        })
        .collect()
}
