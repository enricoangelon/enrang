//! The access check (A:1241-1266; M3 plan d.6; owner 2E): each access against
//! every live loan that overlaps it, O11, the hold exception, closures and
//! compound targets, one report per conflict.
//!
//! Reads (operands, borrows) meet the loans of the slots live before the point;
//! writes, drops and storage ends those live after it, minus a whole-local
//! destination (A:1241), plus the dropped local's own slot when a destructor runs
//! on it, at a scope end or as an assignment drops the old value (O11, H05); both
//! read the `held` sets as they stand before the point (choice: a statement's own
//! unions never reach its own check).

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use enrang_base::{Span, Symbol};
use enrang_diag::Code;
use enrang_hir::{LoopId, Receiver};
use enrang_mir::{
    BodyOwner, BorrowOrigin, Callee, DropOrigin, FormCall, Local, LocalKind, LoopSource, Operand,
    Place, Point, Proj, Rvalue, StatementKind, TerminatorKind, statement_places, terminator_places,
};

use crate::cx::BodyCx;
use crate::held::{HeldResults, StoreError};
use crate::liveness::{LiveSlots, drop_runs};
use crate::loans::{Loan, LoanId, LoanKey, LoanKind, LoanPath, Step, Turn, normalize};
use crate::slots::{SlotId, closure_ty, ref_carrying};
use crate::wlive::Modes;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum AccessKind {
    Read,
    Copy,
    SharedBorrow,
    Write,
    ExclusiveBorrow,
    Move,
    Drop,
    StorageDead,
    /// A whole write of a ref-carrying local: shallow, like a storage end.
    Reassign,
}

/// An access: the place, how, where, and the method when through a receiver.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Access {
    pub place: Place,
    pub kind: AccessKind,
    pub span: Span,
    pub method: Option<Symbol>,
}

/// A conflict between an access and a live loan (plan d.13). For EN0710 and a
/// compound target's EN0708 the access's span is the loan's site, their primary
/// span (A:1289, A:1026).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BorrowConflict {
    pub code: Code,
    pub access: Access,
    pub loan: LoanId,
    pub holder: Option<Local>,
    /// The "still in use here" label.
    pub later_use: Option<(Local, Span)>,
    pub at: Point,
    /// The other live loans the access meets, reported with this one (one report
    /// per access): a fix-it that frees it from `loan` alone leaves them.
    pub others: Vec<LoanId>,
}

/// A loop's own access, which skips the loop's hold and bind keys (A:1225).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Role {
    Hold(LoopId),
    Head(LoopId),
    Bind(LoopId),
}

struct Acc {
    place: Place,
    kind: AccessKind,
    span: Span,
    after: bool,
    dest: Option<Local>,
    role: Option<Role>,
    origin: Option<BorrowOrigin>,
    /// A capture or `ClosureReborrow` of a closure, or a call of one (EN0718).
    closure: bool,
    /// A compound target's store: an exclusive borrow reported at the other loan.
    compound: bool,
    /// A copy's new loan (O7): a borrow of what the copied reference points at.
    path: Option<LoanPath>,
    /// The compound target's own reservation, which its store does not meet.
    own: Option<LoanId>,
    /// A read of a nullable's tag (`CheckTag`, `Discriminant`): a tag in the slot
    /// itself never meets a loan through the reference the slot holds, as a
    /// storage end does not (shallow).
    tag: bool,
    /// The holder's own place is never exempt (O11, H05): a drop that runs a
    /// destructor, at a scope end or of the old value an assignment replaces,
    /// uses the loans the value holds on its own parts, so its own slot meets it.
    own_slot: bool,
}

/// The scope drops of a path nothing of which may be initialised there: a
/// definitely moved path, such as `*_1` after a `move` method's `return this`,
/// drops nothing, so it is no access (elaboration removes it, A:595), and no use
/// of the slot for liveness either, so a guard `dispose(g)` moved away keeps no
/// loan live to its scope's end (`D20E-10`), and nor does D3's drop of the old
/// value before `g = new Guard(&s)` on a `g` moved away.
pub(crate) fn moved_drops(cx: &BodyCx) -> BTreeSet<Point> {
    let b = cx.body;
    let md = &cx.moves;
    let init = crate::init::InitResults::compute(b, md);
    let mut out = BTreeSet::new();
    init.replay(b, md, |p, maybe_init, _| {
        if let Some(StatementKind::Drop(pl, DropOrigin::Scope | DropOrigin::Assign)) =
            b.stmt_at(p).map(|s| &s.kind)
            && let Some(&(n, true)) = md.lookup.get(pl)
            && !md.subtree(n).into_iter().any(|m| maybe_init.contains(m))
        {
            out.insert(p);
        }
    });
    out
}

/// Whether `p` lies in the storage of a variable an arrow captures by path,
/// `*(*_1).k` and its fields, crossing no reference of its own.
fn in_path_capture(b: &enrang_mir::Body, p: Place) -> bool {
    if p.local != Local(1) || !matches!(b.owner, BodyOwner::Arrow(..)) {
        return false;
    }
    match b.projs(p) {
        [Proj::Deref, Proj::Field(k), Proj::Deref, rest @ ..] => {
            !rest.contains(&Proj::Deref)
                && (b.captures.get(k.0 as usize))
                    .is_some_and(|c| c.kind == enrang_mir::CaptureKind::Path)
        }
        _ => false,
    }
}

/// `prefix(a, b)`: one root, `through_ref` a leading deref, `a`'s steps a prefix of
/// `b`'s; `Elem` matches `Elem`, other steps by equality, so different fields,
/// different cases (choice, plan d.6) and `Fields` against any field are disjoint.
fn prefix(a: &LoanPath, b: &LoanPath) -> bool {
    let seq = |p: &LoanPath| {
        let d = p.through_ref.then_some(None);
        d.into_iter()
            .chain(p.steps.iter().map(|s| Some(*s)))
            .collect::<Vec<Option<Step>>>()
    };
    let (x, y) = (seq(a), seq(b));
    a.root == b.root && x.len() <= y.len() && x.iter().zip(&y).all(|(s, t)| s == t)
}

/// `overlap(loan, path, kind)` (A:1243).
pub fn overlap(loan: &LoanPath, path: &LoanPath, shallow: bool) -> bool {
    if shallow && loan.through_ref && loan.root == path.root {
        return false;
    }
    prefix(loan, path) || prefix(path, loan)
}

/// A hold's crossing loans are shallow on their own side (A:1230, A:1249, ledger
/// 86): one on a reference slot `r`, `(r, false, [])`, never meets an access that
/// goes on through `r`. One on a reference field already never does, since an
/// access through a field's reference is `Fields` or a fresh crossing in normal
/// form (A:1032), which `prefix` keeps apart from the field's own path.
fn through_crossing(loan: &LoanPath, path: &LoanPath) -> bool {
    !loan.through_ref && loan.steps.is_empty() && path.root == loan.root && path.through_ref
}

/// `loans_overlap(a, b)`, N6's part test (A:1244): two keys of one bind site are
/// disjoint only for `This` against `EarlierThisRun`.
pub fn loans_overlap(cx: &BodyCx, a: (LoanId, Turn), b: (LoanId, Turn)) -> bool {
    if a.0 == b.0
        && cx
            .body
            .meta
            .loops
            .iter()
            .any(|l| cx.loans.at(l.bind).any(|(id, _)| id == a.0))
    {
        let pair = [a.1, b.1];
        return pair != [Turn::This, Turn::EarlierThisRun]
            && pair != [Turn::EarlierThisRun, Turn::This];
    }
    let t = &cx.loans.table;
    prefix(&t[a.0].path, &t[b.0].path) || prefix(&t[b.0].path, &t[a.0].path)
}

/// Every conflict of `cx.body`, in point order.
pub fn check(
    cx: &BodyCx,
    held: &HeldResults,
    live: &LiveSlots,
    modes: &Modes,
) -> Vec<BorrowConflict> {
    let b = cx.body;
    let mut found: Vec<(LoanId, Span, u8, BorrowConflict)> = Vec::new();
    let mut seen_0 = BTreeSet::new();
    let gone = moved_drops(cx);
    // A `move` method's object dropped under a returned loan into it: the
    // definition check reports that EN0710 at the `return` (D4, A:1287), so the
    // drop's conflict would be a second report of one mistake (A:1270).
    let own_this = |c: &BorrowConflict| {
        let path = &cx.loans.table[c.loan].path;
        let BodyOwner::Fn(d) = b.owner else {
            return false;
        };
        path.root == Local(1)
            && cx
                .tcx
                .sig_opt(d)
                .is_some_and(|s| s.receiver == Some(Receiver::Move))
    };
    for (block, data) in b.blocks.iter_enumerated() {
        for i in 0..=data.stmts.len() {
            let at = Point::new(block, i);
            for acc in accesses(cx, held, modes, at, &gone) {
                if let Some(c) = check_one(cx, held, live, modes, at, &acc) {
                    if c.code == Code::EN0710 && (own_this(&c) || !seen_0.insert(c.loan)) {
                        continue;
                    }
                    let prio = match acc.role {
                        Some(Role::Bind(_)) if acc.origin.is_some() => 0,
                        Some(Role::Hold(_)) => 1,
                        _ => 2,
                    };
                    // At one span, a write's report comes before its own guard
                    // reads: `xs[1] = 5` reads `len(xs)` for its bounds check
                    // under the write's span, and O11 gives the write EN0707
                    // (A:1262), never the guard's EN0708.
                    let read = matches!(
                        c.access.kind,
                        AccessKind::Read | AccessKind::Copy | AccessKind::SharedBorrow
                    );
                    found.push((c.loan, c.access.span, prio * 2 + u8::from(read), c));
                }
            }
        }
    }
    found.sort_by(|x, y| (x.0, x.1.lo, x.1.hi, x.2).cmp(&(y.0, y.1.lo, y.1.hi, y.2)));
    found.dedup_by(|x, y| x.0 == y.0 && x.1 == y.1);
    // One report per mistake (A:1270): a conflict of one loan inside the span of
    // another of the same loan and code is the same mistake, as an index's
    // bounds read `data[0]` inside the borrow `&data[0]`; the outer one stays.
    let inner = |f: &(LoanId, Span, u8, BorrowConflict)| {
        found.iter().any(|g| {
            g.0 == f.0 && g.3.code == f.3.code && g.1 != f.1 && g.1.lo <= f.1.lo && f.1.hi <= g.1.hi
        })
    };
    let keep: Vec<bool> = found.iter().map(|f| !inner(f)).collect();
    let mut out: Vec<BorrowConflict> = (found.into_iter().zip(keep))
        .filter_map(|(f, k)| k.then_some(f.3))
        .collect();
    out.sort_by_key(|c| (c.at, c.access.span.lo));
    out
}

/// The read-set EN0616s of `held` that survive the one-report rule: at one call,
/// only where no borrow the call takes conflicted (A:1265).
pub fn store_errors(
    cx: &BodyCx,
    held: &HeldResults,
    conflicts: &[BorrowConflict],
) -> Vec<StoreError> {
    let b = cx.body;
    let silenced = |e: &StoreError| {
        let Some(TerminatorKind::Call { args, .. }) = b
            .stmt_at(e.at)
            .is_none()
            .then(|| &b.blocks[e.at.block].term.kind)
        else {
            return false;
        };
        // Each argument local, and the locals it was moved or converted from in
        // the call's block: an upcast receiver's `Ref` is the call's borrow too.
        let mut taken: BTreeSet<Local> = BTreeSet::new();
        let mut work: Vec<Local> = args
            .iter()
            .filter_map(|a| a.place())
            .filter(|p| p.is_local())
            .map(|p| p.local)
            .collect();
        while let Some(l) = work.pop() {
            if !taken.insert(l) {
                continue;
            }
            if let Some((_, Rvalue::Convert(_, op) | Rvalue::Use(op @ Operand::Move(_)))) =
                crate::movepaths::def_of(b, e.at, l)
                && let Some(p) = op.place().filter(|p| p.is_local())
            {
                work.push(p.local);
            }
        }
        conflicts.iter().any(|c| {
            c.at == e.at
                || matches!(b.stmt_at(c.at).map(|s| &s.kind),
                    Some(StatementKind::Assign { dest, value: Rvalue::Ref { .. } })
                        if dest.is_local() && taken.contains(&dest.local))
        })
    };
    held.store_errors
        .iter()
        .filter(|e| !(e.call && e.kind == crate::held::StoreErrorKind::ReadSet && silenced(e)))
        .copied()
        .collect()
}

/// Whether the statement before `at` drops the old value of local `l`, which the
/// assignment at `at` replaces (D3), and a destructor runs on it (O10, I5).
fn assign_drop_runs(cx: &BodyCx, at: Point, l: Local, gone: &BTreeSet<Point>) -> bool {
    let Some(prev) = at
        .index
        .checked_sub(1)
        .map(|i| Point::new(at.block, i as usize))
    else {
        return false;
    };
    matches!(
        cx.body.stmt_at(prev).map(|s| &s.kind),
        Some(StatementKind::Drop(p, DropOrigin::Assign)) if *p == Place::local(l)
    ) && !gone.contains(&prev)
        && drop_runs(cx.tcx, cx.body.locals[l].ty)
}

fn op_acc(op: &Operand, span: Span) -> Option<Acc> {
    let (place, kind) = match op {
        Operand::Copy(p) => (*p, AccessKind::Copy),
        Operand::Move(p) => (*p, AccessKind::Move),
        Operand::Const(_) => return None,
    };
    Some(Acc::new(place, kind, span))
}

impl Acc {
    fn new(place: Place, kind: AccessKind, span: Span) -> Acc {
        Acc {
            place,
            kind,
            span,
            after: false,
            dest: None,
            role: None,
            origin: None,
            closure: false,
            compound: false,
            path: None,
            own: None,
            tag: false,
            own_slot: false,
        }
    }

    fn write(cx: &BodyCx, place: Place, span: Span) -> Acc {
        let whole = place.is_local();
        let kind = match whole && ref_carrying(cx.tcx, cx.body.locals[place.local].ty) {
            true => AccessKind::Reassign,
            false => AccessKind::Write,
        };
        Acc {
            after: true,
            dest: whole.then_some(place.local),
            ..Acc::new(place, kind, span)
        }
    }
}

/// The accesses of the statement or terminator at `at`, in operand order, then
/// the write.
fn accesses(
    cx: &BodyCx,
    held: &HeldResults,
    modes: &Modes,
    at: Point,
    gone: &BTreeSet<Point>,
) -> Vec<Acc> {
    let (b, tcx) = (cx.body, cx.tcx);
    let mut out = Vec::new();
    let role = |kind_ok: bool| -> Option<Role> {
        b.meta.loops.iter().find_map(|l| {
            if at.block == l.head && kind_ok {
                Some(Role::Head(l.id))
            } else if at.block == l.bind.block && at.index <= l.bind.index {
                Some(Role::Bind(l.id))
            } else {
                None
            }
        })
    };
    match b.stmt_at(at) {
        Some(st) => {
            let span = st.span;
            match &st.kind {
                StatementKind::Assign { dest, value } => {
                    match value {
                        Rvalue::Use(op) | Rvalue::Unary(_, op) | Rvalue::CheckedNeg(op) => {
                            out.extend(op_acc(op, span));
                            // Each new loan a copy takes, when N4 gives it, borrows
                            // what the reference points at (O7, A:935).
                            let after = held.held_at(
                                Point::new(at.block, at.index as usize + 1),
                                SlotId::Local(dest.local),
                            );
                            // A part or payload copy N4 gives no loan still reads
                            // what the copied reference points at, as `&*r` of a
                            // reference local does: a shared borrow of it.
                            for (id, l) in cx.loans.at(at) {
                                let given = after.contains_key(&LoanKey::Site(id, Turn::Any));
                                let reads = matches!(l.kind, LoanKind::Part(_) | LoanKind::Payload);
                                if (given || reads) && l.kind != LoanKind::Site {
                                    let kind = match given && modes.exclusive(id) {
                                        true => AccessKind::ExclusiveBorrow,
                                        false => AccessKind::SharedBorrow,
                                    };
                                    out.push(Acc {
                                        path: Some(l.path.clone()),
                                        ..Acc::new(*dest, kind, span)
                                    });
                                }
                            }
                        }
                        Rvalue::Cast(_, op, _) | Rvalue::Convert(_, op) => {
                            out.extend(op_acc(op, span))
                        }
                        Rvalue::Binary(_, x, y) | Rvalue::Checked(_, x, y) => {
                            out.extend(op_acc(x, span));
                            out.extend(op_acc(y, span));
                        }
                        Rvalue::Aggregate(_, ops) => {
                            out.extend(ops.iter().filter_map(|o| op_acc(o, span)))
                        }
                        Rvalue::Ref { place, origin } => {
                            let own = cx.loans.at(at).find(|(_, l)| l.kind == LoanKind::Site);
                            let excl = own.is_some_and(|(id, _)| modes.exclusive(id));
                            let kind = match excl {
                                true => AccessKind::ExclusiveBorrow,
                                false => AccessKind::SharedBorrow,
                            };
                            let r = role(false).filter(|r| matches!(r, Role::Bind(_)));
                            out.push(Acc {
                                role: r,
                                origin: Some(*origin),
                                // Capturing a closure value, a closure local `f`
                                // or `*f` of a reference to one, a nullable one
                                // included (EN0718, S:974, A:973).
                                closure: *origin == BorrowOrigin::ClosureCapture
                                    && matches!(b.projs(*place), [] | [Proj::Deref])
                                    && b.place_ty(tcx, *place)
                                        .is_some_and(|t| closure_ty(tcx, t.ty)),
                                ..Acc::new(*place, kind, span)
                            });
                        }
                        Rvalue::ClosureReborrow(f) => out.push(Acc {
                            closure: true,
                            ..Acc::new(*f, AccessKind::ExclusiveBorrow, span)
                        }),
                        Rvalue::Discriminant(p) | Rvalue::Len(p) => out.push(Acc {
                            role: role(matches!(value, Rvalue::Len(_))),
                            tag: matches!(value, Rvalue::Discriminant(_)),
                            ..Acc::new(*p, AccessKind::Read, span)
                        }),
                        Rvalue::ClosureValue { env, .. } => {
                            out.push(Acc::new(*env, AccessKind::Read, span))
                        }
                        Rvalue::AddrOf(_) | Rvalue::ArrowFn(_) => {}
                    }
                    let mut w = Acc::write(cx, *dest, span);
                    w.own_slot = dest.is_local() && assign_drop_runs(cx, at, dest.local, gone);
                    out.push(w);
                }
                StatementKind::CheckBounds { index, len } => {
                    let r = role(false).filter(|r| matches!(r, Role::Bind(_)));
                    for op in [index, len] {
                        out.extend(op_acc(op, span).map(|a| Acc { role: r, ..a }));
                    }
                }
                StatementKind::CheckTag { place, .. } => out.push(Acc {
                    role: role(true),
                    tag: true,
                    ..Acc::new(*place, AccessKind::Read, span)
                }),
                StatementKind::CheckClass { place, .. } => {
                    out.push(Acc::new(*place, AccessKind::Read, span))
                }
                StatementKind::SetTable { place, .. } => out.push(Acc::write(cx, *place, span)),
                StatementKind::FieldInit { field, value } => {
                    out.extend(op_acc(value, span));
                    out.push(Acc::write(cx, *field, span));
                }
                StatementKind::StorageDead(l) => out.push(Acc {
                    after: true,
                    ..Acc::new(Place::local(*l), AccessKind::StorageDead, span)
                }),
                StatementKind::Drop(p, DropOrigin::Scope) if !gone.contains(&at) => out.push(Acc {
                    after: true,
                    own_slot: p.is_local() && drop_runs(tcx, b.locals[p.local].ty),
                    ..Acc::new(*p, AccessKind::Drop, span)
                }),
                StatementKind::Intrinsic { args, dest, .. }
                | StatementKind::HostCall { args, dest, .. } => {
                    out.extend(args.iter().filter_map(|o| op_acc(o, span)));
                    out.extend(dest.map(|d| Acc::write(cx, d, span)));
                }
                StatementKind::Asm(asm) => {
                    out.extend(asm.ins.iter().filter_map(|(_, o)| op_acc(o, span)));
                    out.extend(
                        asm.outs
                            .iter()
                            .filter_map(|(_, p)| *p)
                            .map(|p| Acc::write(cx, p, span)),
                    );
                }
                _ => {}
            }
        }
        None => {
            let t = &b.blocks[at.block].term;
            let span = t.span;
            match &t.kind {
                TerminatorKind::Switch { value, .. } => out.extend(op_acc(value, span)),
                TerminatorKind::Call {
                    callee, args, dest, ..
                } => {
                    match callee {
                        Callee::FnPtr(op) | Callee::Virtual { table: op, .. } => {
                            out.extend(op_acc(op, span))
                        }
                        Callee::ClosureLocal(l) => out.push(Acc {
                            closure: true,
                            ..Acc::new(Place::local(*l), AccessKind::ExclusiveBorrow, span)
                        }),
                        _ => {}
                    }
                    out.extend(args.iter().filter_map(|o| op_acc(o, span)));
                    if matches!(callee, Callee::Form(FormCall::Append))
                        && let Some((target, own)) =
                            args.first().and_then(|a| compound_target(cx, a))
                    {
                        out.push(Acc {
                            compound: true,
                            own,
                            ..Acc::new(target, AccessKind::ExclusiveBorrow, span)
                        });
                    }
                    out.push(Acc::write(cx, *dest, span));
                }
                _ => {}
            }
            for lp in b.meta.loops.iter().filter(|l| l.preheader == at.block) {
                let (LoopSource::Path(src), Some((id, _))) = (
                    &lp.source,
                    cx.loans
                        .at(at)
                        .find(|(_, l)| l.kind == LoanKind::Hold(lp.id)),
                ) else {
                    continue;
                };
                let kind = match modes.exclusive(id) {
                    true => AccessKind::ExclusiveBorrow,
                    false => AccessKind::SharedBorrow,
                };
                out.push(Acc {
                    role: Some(Role::Hold(lp.id)),
                    ..Acc::new(*src, kind, lp.span)
                });
            }
        }
    }
    out
}

/// The place a compound target `_p = &place [compound-target]` reserved, and its
/// loan, for the store that uses `_p`.
fn compound_target(cx: &BodyCx, op: &Operand) -> Option<(Place, Option<LoanId>)> {
    let l = op.place().filter(|p| p.is_local())?.local;
    for (block, data) in cx.body.blocks.iter_enumerated() {
        for (i, st) in data.stmts.iter().enumerate() {
            if let StatementKind::Assign {
                dest,
                value:
                    Rvalue::Ref {
                        place,
                        origin: BorrowOrigin::CompoundTarget,
                    },
            } = &st.kind
                && *dest == Place::local(l)
            {
                let id = cx.loans.at(Point::new(block, i)).map(|(id, _)| id).next();
                return Some((*place, id));
            }
        }
    }
    None
}

/// The first conflicting live loan of one access, by O11 and its exceptions.
fn check_one(
    cx: &BodyCx,
    held: &HeldResults,
    live: &LiveSlots,
    modes: &Modes,
    at: Point,
    acc: &Acc,
) -> Option<BorrowConflict> {
    let (b, tcx) = (cx.body, cx.tcx);
    let path = match &acc.path {
        Some(p) => p.clone(),
        None => normalize(tcx, b, acc.place.local, b.projs(acc.place))?.0,
    };
    let state = held.at.get(&at)?;
    let mut slots: Vec<SlotId> = match acc.after {
        true => live
            .live_after(at)
            .iter()
            .filter(|s| acc.dest.map(SlotId::Local) != Some(**s))
            .copied()
            .collect(),
        false => live.live_before(at).iter().copied().collect(),
    };
    let own = SlotId::Local(acc.place.local);
    if acc.own_slot && cx.slots.has(own) && !slots.contains(&own) {
        slots.push(own);
    }
    let hold_loan = |l: LoopId| {
        cx.loans
            .table
            .iter_enumerated()
            .find(|(_, x)| x.kind == LoanKind::Hold(l))
            .map(|(id, _)| id)
    };
    // Live loans with their holders, holds first, then by LoanId.
    let mut cands: BTreeMap<(bool, LoanId), BTreeSet<SlotId>> = BTreeMap::new();
    let own_loop = acc.role.map(|r| match r {
        Role::Hold(l) | Role::Head(l) | Role::Bind(l) => l,
    });
    let exempt_bind = own_loop
        .filter(|_| !matches!(acc.role, Some(Role::Hold(_))))
        .and_then(|l| b.meta.loops.iter().find(|x| x.id == l))
        .and_then(|lp| {
            cx.loans
                .at(lp.bind)
                .find(|(_, x)| x.kind == LoanKind::Site)
                .map(|(id, _)| id)
        });
    for s in &slots {
        for k in state.held.get(s).into_iter().flat_map(|set| set.keys()) {
            let id = match k {
                LoanKey::Site(l, _) => *l,
                LoanKey::Hold(l) => {
                    if own_loop == Some(*l) && !matches!(acc.role, Some(Role::Hold(_))) {
                        continue;
                    }
                    match hold_loan(*l) {
                        Some(id) => id,
                        None => continue,
                    }
                }
                _ => continue,
            };
            // At a loop's own head and bind: its hold's loans and its bind site's.
            let own_hold = matches!(cx.loans.table[id].kind, LoanKind::HoldCrossing(l) if Some(l) == own_loop)
                && !matches!(acc.role, Some(Role::Hold(_)));
            if Some(id) == exempt_bind || own_hold || Some(id) == acc.own {
                continue;
            }
            // A compound target's store meets only the loans its right side left
            // live (A:1026); one live before the reservation is the
            // reservation's own conflict, one report per mistake.
            if acc.compound && acc.own.is_some_and(|r| id < r) {
                continue;
            }
            let is_hold = matches!(cx.loans.table[id].kind, LoanKind::Hold(_));
            cands.entry((!is_hold, id)).or_default().insert(*s);
        }
    }
    let local_ty = b.locals[acc.place.local].ty;
    // A tag read of a slot itself (`check_tag(_5)`), never one through a
    // reference (`check_tag((*h).v)`), which reads what `h` points at. In an
    // arrow, a variable it captures by path is a slot too, `check_tag(*(*_1).0)`,
    // though its normal form crosses the environment (A:1031, T:628).
    let shallow = (acc.tag && (!path.through_ref || in_path_capture(b, acc.place)))
        || match acc.kind {
            AccessKind::StorageDead | AccessKind::Reassign => true,
            AccessKind::Drop => {
                acc.place.is_local() && ref_carrying(tcx, local_ty) && !drop_runs(tcx, local_ty)
            }
            _ => false,
        };
    let mut found: Option<BorrowConflict> = None;
    for ((_, id), holders) in cands {
        let loan = &cx.loans.table[id];
        let crossing = matches!(loan.kind, LoanKind::HoldCrossing(_));
        if (crossing && through_crossing(&loan.path, &path)) || !overlap(&loan.path, &path, shallow)
        {
            continue;
        }
        let code = if acc.compound {
            Code::EN0708
        } else {
            match code_of(cx, modes, acc, id, loan) {
                Some(c) => c,
                None => continue,
            }
        };
        if let Some(first) = found.as_mut() {
            first.others.push(id);
            continue;
        }
        // A loan the return place holds when its referent dies is EN0710, the
        // definition check's report, deduped per loan (A:1298), whatever else
        // still holds it there (Q41-written: one report per mistake).
        let only_ret = holders.contains(&SlotId::Local(Local::RETURN));
        let (code, span) = match code {
            Code::EN0711 | Code::EN0712 if only_ret => (Code::EN0710, loan.span),
            _ if acc.compound => (code, loan.span),
            _ => (code, acc.span),
        };
        let holder = pick_holder(cx, &holders);
        let later_use = match loan.kind {
            LoanKind::Hold(_) => None,
            _ => later_use(cx, at, &holders),
        };
        found = Some(BorrowConflict {
            code,
            access: Access {
                place: acc.place,
                kind: acc.kind,
                span,
                method: method_of(cx, at, acc),
            },
            loan: id,
            holder,
            later_use,
            at,
            others: Vec::new(),
        });
    }
    found
}

/// O11 with the hold, closure and compound-target exceptions; `None` when the
/// access may pass.
fn code_of(cx: &BodyCx, modes: &Modes, acc: &Acc, id: LoanId, loan: &Loan) -> Option<Code> {
    let b = cx.body;
    use AccessKind as K;
    let reservation = loan.origin == BorrowOrigin::CompoundTarget;
    let excl = match acc.kind {
        K::Read | K::Copy | K::SharedBorrow if reservation => false,
        _ if reservation => true,
        _ => modes.exclusive(id),
    };
    let mut code = match acc.kind {
        K::Read | K::Copy | K::SharedBorrow => excl.then_some(Code::EN0708)?,
        K::Write | K::ExclusiveBorrow | K::Reassign => match excl {
            true => Code::EN0707,
            false => Code::EN0706,
        },
        K::Move => Code::EN0709,
        K::Drop | K::StorageDead => match b.locals[loan.path.root].kind == LocalKind::Temp {
            true => Code::EN0712,
            false => Code::EN0711,
        },
    };
    if matches!(loan.kind, LoanKind::Hold(_)) && acc.role.is_none() && code == Code::EN0707 {
        code = Code::EN0706;
    }
    let closure_loan = closure_ty(cx.tcx, b.locals[loan.path.root].ty)
        && !loan.path.through_ref
        && loan.kind != LoanKind::Closure;
    // A hold keeps its own code and wording: an arrow's capture that meets it is
    // the hold's EN0706, tried first (A:1268, A:1272, T:664).
    let hold = matches!(loan.kind, LoanKind::Hold(_) | LoanKind::HoldCrossing(_));
    if matches!(
        code,
        Code::EN0706 | Code::EN0707 | Code::EN0708 | Code::EN0709
    ) && !hold
    {
        if acc.closure && closure_loan {
            code = Code::EN0718;
        } else if loan.origin == BorrowOrigin::ClosureCapture
            || acc.origin == Some(BorrowOrigin::ClosureCapture)
        {
            code = Code::EN0715;
        }
    }
    Some(code)
}

/// A user-named holder before a hidden one, then the lowest slot.
fn pick_holder(cx: &BodyCx, holders: &BTreeSet<SlotId>) -> Option<Local> {
    let locals = holders.iter().filter_map(|s| match s {
        SlotId::Local(l) => Some(*l),
        _ => None,
    });
    let named: Vec<Local> = locals
        .clone()
        .filter(|l| cx.body.locals[*l].name.is_some())
        .collect();
    named.first().copied().or_else(|| locals.clone().next())
}

/// The first later use of a holder, user-named holders first, by a forward BFS
/// from just after `at` (A:1310).
fn later_use(cx: &BodyCx, at: Point, holders: &BTreeSet<SlotId>) -> Option<(Local, Span)> {
    let b = cx.body;
    let locals: Vec<Local> = holders
        .iter()
        .filter_map(|s| match s {
            SlotId::Local(l) => Some(*l),
            _ => None,
        })
        .collect();
    let (named, hidden): (Vec<Local>, Vec<Local>) =
        locals.iter().partition(|l| b.locals[**l].name.is_some());
    for group in [named, hidden] {
        if group.is_empty() {
            continue;
        }
        let uses = |p: Point| -> Option<(Local, Span)> {
            let (places, span, dest) = match b.stmt_at(p) {
                Some(s) => {
                    let dest = match &s.kind {
                        StatementKind::Assign { dest, .. } if dest.is_local() => Some(dest.local),
                        StatementKind::StorageDead(_) | StatementKind::StorageLive(_) => {
                            return None;
                        }
                        _ => None,
                    };
                    (statement_places(&s.kind), s.span, dest)
                }
                None => {
                    let t = &b.blocks[p.block].term;
                    let mut places = terminator_places(&t.kind);
                    if let TerminatorKind::Call {
                        callee: Callee::ClosureLocal(l),
                        ..
                    } = &t.kind
                    {
                        places.push(Place::local(*l));
                    }
                    (places, t.span, None)
                }
            };
            places
                .iter()
                .filter(|pl| !(pl.is_local() && Some(pl.local) == dest))
                .find(|pl| group.contains(&pl.local))
                .map(|pl| (pl.local, span))
        };
        let mut queue = VecDeque::from([(at.block, at.index as usize + 1)]);
        let mut seen = BTreeSet::new();
        while let Some((block, from)) = queue.pop_front() {
            let n = b.blocks[block].stmts.len();
            for i in from..=n {
                if let Some(u) = uses(Point::new(block, i)) {
                    return Some(u);
                }
            }
            for s in b.blocks[block].term.kind.successors() {
                if seen.insert(s) {
                    queue.push_back((s, 0));
                }
            }
        }
    }
    None
}

/// The method a receiver's borrow is for: the call of the same block that takes
/// the borrow's temporary first.
fn method_of(cx: &BodyCx, at: Point, acc: &Acc) -> Option<Symbol> {
    let b = cx.body;
    if !matches!(
        acc.origin,
        Some(BorrowOrigin::AutoBorrow | BorrowOrigin::Reborrow)
    ) {
        return None;
    }
    let Some(StatementKind::Assign { dest, .. }) = b.stmt_at(at).map(|s| &s.kind) else {
        return None;
    };
    let TerminatorKind::Call { callee, args, .. } = &b.blocks[at.block].term.kind else {
        return None;
    };
    let def = match callee {
        Callee::Fn(f) | Callee::Virtual { method: f, .. } => f.def,
        _ => return None,
    };
    let first = args.first().and_then(|a| a.place());
    (first == Some(*dest)).then(|| cx.tcx.def(def).path.segments.last().copied())?
}
