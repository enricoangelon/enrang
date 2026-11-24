//! `match`, `??`, `?.`, `!` and the narrowing records (A:947, A:1362; M3 plan c.11,
//! c.20; owner 2C), with the helpers the other 2C modules share.
//!
//! A subject is used in place, or an rvalue goes into a statement temporary (X1);
//! its guard run is emitted before every use.
//! Arms are tried top to bottom: a run of unguarded `null` and case arms, and the
//! guarded arm that may end it, share one `discriminant` and one `switch` per
//! nullable level (arms with several values share a target); literals and ranges
//! are compares; `match (true)` conditions are evaluated in turn; a failed guard
//! goes on to the next arm. Each arm's block is the test of the facts its case made.

use enrang_base::{Idx, Span};
use enrang_hir::{
    self as hir, ArmBody, ArmValue, ConstValue, ExprKind, Fact, FieldIdx, FnRef, LocalId,
    OptMember, Ty, TyKind, VariantIdx,
};
use enrang_mir::{
    AggregateKind, BinOp, BlockId, BorrowOrigin, Callee, ConvKind, Local, Operand, Place, Proj,
    Rvalue, StatementKind, TerminatorKind, tag_value,
};

use crate::builder::Builder;
use crate::scope::{ExitTarget, ScopeKind};

// ---------------------------------------------------------------------------------
// Helpers every 2C module shares.

pub(crate) fn op_ty(b: &Builder, op: &Operand) -> Ty {
    match op {
        Operand::Copy(p) | Operand::Move(p) => b.place_ty(*p),
        Operand::Const(c) => c.ty,
    }
}

/// A copy of a Copy place, a move of any other (O1).
pub(crate) fn read(b: &Builder, p: Place) -> Operand {
    match b.is_copy(b.place_ty(p)) {
        true => Operand::Copy(p),
        false => Operand::Move(p),
    }
}

pub(crate) fn temp(b: &mut Builder, t: Ty, span: Span) -> Place {
    Place::local(b.new_temp(t, span))
}

/// A temporary holding `value`.
pub(crate) fn to_temp(b: &mut Builder, value: Rvalue, t: Ty, span: Span) -> Place {
    let p = temp(b, t, span);
    b.assign(p, value, span);
    p
}

pub(crate) fn proj(b: &mut Builder, p: Place, x: Proj) -> Place {
    b.body.project(p, x)
}

/// `(p as v).0`, with no check: the caller emits the guard.
pub(crate) fn field0(b: &mut Builder, p: Place, v: VariantIdx) -> Place {
    let q = proj(b, p, Proj::Variant(v));
    proj(b, q, Proj::Field(FieldIdx::new(0)))
}

/// `check_tag(p, v)` and `(p as v).0`, used by the next statement.
pub(crate) fn payload(b: &mut Builder, p: Place, v: VariantIdx, span: Span) -> Place {
    b.push(
        StatementKind::CheckTag {
            place: p,
            variant: v,
        },
        span,
    );
    field0(b, p, v)
}

pub(crate) fn switch(
    b: &mut Builder,
    v: Operand,
    arms: Vec<(u128, BlockId)>,
    other: BlockId,
    span: Span,
) {
    b.terminate(
        TerminatorKind::Switch {
            value: v,
            arms,
            otherwise: Some(other),
        },
        span,
    );
}

/// A `bool` switch (plan b.4): `[0: no, otherwise: yes]`.
pub(crate) fn branch(b: &mut Builder, c: Operand, yes: BlockId, no: BlockId, span: Span) {
    switch(b, c, vec![(0, no)], yes, span);
}

/// A call returning to a new block, which becomes the cursor.
pub(crate) fn call(b: &mut Builder, callee: Callee, args: Vec<Operand>, dest: Place, span: Span) {
    let next = b.new_block();
    b.terminate(
        TerminatorKind::Call {
            callee,
            args,
            dest,
            next: Some(next),
        },
        span,
    );
    b.switch_to(next);
}

/// `_d = discriminant(p)`.
pub(crate) fn discr(b: &mut Builder, p: Place, span: Span) -> Operand {
    let t = b.cx.tcx.common().isize;
    Operand::Move(to_temp(b, Rvalue::Discriminant(p), t, span))
}

/// Whether `e` names a place (c.4) with nothing applied to it.
pub(crate) fn is_place(e: &hir::Expr) -> bool {
    e.adjust.is_empty()
        && matches!(
            e.kind,
            ExprKind::Local(_)
                | ExprKind::Field(..)
                | ExprKind::Deref(_)
                | ExprKind::Index(..)
                | ExprKind::NarrowedPayload(..)
        )
}

/// `e`'s value in a new temporary, its adjust chain applied.
pub(crate) fn value_temp(b: &mut Builder, e: &hir::Expr) -> Place {
    if e.adjust.is_empty() {
        let t = temp(b, e.ty, e.span);
        b.expr_into(e, t);
        return t;
    }
    let op = b.as_operand(e);
    let t = op_ty(b, &op);
    to_temp(b, Rvalue::Use(op), t, e.span)
}

/// A place used in place, its guard run emitted before each use by
/// `Builder::guard` (A:582, c.4).
pub(crate) struct Subject {
    pub place: Place,
}

impl Subject {
    pub(crate) fn at(place: Place) -> Subject {
        Subject { place }
    }

    /// `e` used in place; an rvalue goes into a statement temporary, dropped with
    /// the statement.
    pub(crate) fn of(b: &mut Builder, e: &hir::Expr) -> Subject {
        let place = match is_place(e) {
            true => b.adjusted_place(e),
            false => {
                let t = value_temp(b, e);
                t
            }
        };
        Subject { place }
    }

    /// The guards a use of `p`, the subject or a place below it, needs directly
    /// before it.
    pub(crate) fn guard(&mut self, b: &mut Builder, p: Place, span: Span) {
        b.guard(p, span);
    }
}

/// The nullable levels below `p` (each tested for `null`), references and boxes
/// looked through, and the value under the last one.
pub(crate) fn levels(b: &mut Builder, mut p: Place) -> (Vec<Place>, Place) {
    let mut nulls = Vec::new();
    loop {
        match b.cx.tcx.kind(b.place_ty(p)) {
            TyKind::Ref(_) | TyKind::Boxed(_) => p = proj(b, p, Proj::Deref),
            TyKind::Nullable(_) => {
                nulls.push(p);
                p = field0(b, p, VariantIdx::PRESENT);
            }
            _ => return (nulls, p),
        }
    }
}

/// From the cursor: to `outer` when the outermost level is `null` (where a `null`
/// arm matches, S:1145), to `inner` when a deeper one is; on, in a new block,
/// when every level is present.
fn test_nulls(b: &mut Builder, s: &mut Subject, nulls: &[Place], to: [BlockId; 2], span: Span) {
    for (k, &n) in nulls.iter().enumerate() {
        s.guard(b, n, span);
        let d = discr(b, n, span);
        let next = b.new_block();
        switch(b, d, vec![(0, to[(k > 0) as usize])], next, span);
        b.switch_to(next);
    }
}

// ---------------------------------------------------------------------------------
// `match`.

/// Lowers `match subject { arms }` into `dest` (A:947).
pub fn lower_match(
    b: &mut Builder,
    subject: &hir::Expr,
    arms: &[hir::Arm],
    dest: Place,
    span: Span,
) {
    let conds = arms
        .iter()
        .any(|a| a.values.iter().any(|v| matches!(v, ArmValue::Cond(_))));
    let mut s = match conds {
        true => None,
        false => Some(Subject::of(b, subject)),
    };
    let lv = s.as_ref().map(|s| s.place).map(|p| levels(b, p));
    let join = b.new_block();
    let mut i = 0;
    while i < arms.len() {
        // A run of unguarded `null` and case arms, ended by a guarded one.
        let run_end = match (&mut s, &lv) {
            (Some(s), Some(lv)) => case_run(b, s, lv, arms, i, span),
            _ => None,
        };
        let (bodies, end) = match run_end {
            Some(r) => r,
            None => {
                let (body, next) = (b.new_block(), b.new_block());
                match arms[i].values.is_empty() {
                    true => b.goto(body, span),
                    false => {
                        let vals = &arms[i].values;
                        for (k, v) in vals.iter().enumerate() {
                            let no = match k + 1 == vals.len() {
                                true => next,
                                false => b.new_block(),
                            };
                            let (s, lv) = (s.as_mut(), lv.as_ref());
                            test_value(b, s, lv, v, body, no, arms[i].value_spans[k]);
                            b.switch_to(no);
                        }
                    }
                }
                b.switch_to(next);
                (vec![(i, body)], i + 1)
            }
        };
        let next = b.cursor.expect("the next arm's block");
        for (k, body) in bodies {
            b.switch_to(body);
            // The arms after an unguarded `null` arm see the subject without
            // `null` (S:1146).
            let after_null =
                (arms[..k].iter()).any(|a| a.guard.is_none() && a.values.contains(&ArmValue::Null));
            fact_tests(b, subject.span, &arms[k], body, after_null);
            lower_arm(b, &arms[k], dest, next, join);
        }
        b.switch_to(next);
        i = end;
    }
    b.terminate(TerminatorKind::Unreachable, span);
    b.switch_to(join);
}

/// The run of arms from `i` whose values are all `null` or cases, up to and with
/// the first guarded one: one switch per level, the arms' bodies, and the run's
/// end; the cursor is then where no arm of the run matched.
fn case_run(
    b: &mut Builder,
    s: &mut Subject,
    (nulls, base): &(Vec<Place>, Place),
    arms: &[hir::Arm],
    i: usize,
    span: Span,
) -> Option<(Vec<(usize, BlockId)>, usize)> {
    let simple = |a: &hir::Arm| {
        !a.values.is_empty()
            && a.values
                .iter()
                .all(|v| matches!(v, ArmValue::Null | ArmValue::Case(_)))
    };
    let mut end = i;
    while end < arms.len() && simple(&arms[end]) {
        end += 1;
        if arms[end - 1].guard.is_some() {
            break;
        }
    }
    if end == i {
        return None;
    }
    let bodies: Vec<(usize, BlockId)> = (i..end).map(|k| (k, b.new_block())).collect();
    let next = b.new_block();
    let first = |pred: &dyn Fn(&ArmValue) -> bool| {
        bodies
            .iter()
            .find(|(k, _)| arms[*k].values.iter().any(pred))
            .map(|&(_, bb)| bb)
    };
    let on_null = first(&|v| matches!(v, ArmValue::Null)).unwrap_or(next);
    test_nulls(b, s, nulls, [on_null, next], span);
    let mut cases: Vec<(u128, BlockId)> = Vec::new();
    for &(k, bb) in &bodies {
        for v in &arms[k].values {
            if let ArmValue::Case(c) = v {
                let tag = tag_value(b.cx.tcx, b.place_ty(*base), *c);
                if !cases.iter().any(|&(t, _)| t == tag) {
                    cases.push((tag, bb));
                }
            }
        }
    }
    match cases.is_empty() {
        true => b.goto(next, span),
        false => {
            s.guard(b, *base, span);
            let d = discr(b, *base, span);
            switch(b, d, cases, next, span);
        }
    }
    b.switch_to(next);
    Some((bodies, end))
}

/// From the cursor: to `yes` when `v` matches, else to `no`.
fn test_value(
    b: &mut Builder,
    s: Option<&mut Subject>,
    lv: Option<&(Vec<Place>, Place)>,
    v: &ArmValue,
    yes: BlockId,
    no: BlockId,
    span: Span,
) {
    if let ArmValue::Cond(e) = v {
        let c = cond(b, e);
        return branch(b, c, yes, no, e.span);
    }
    let (Some(s), Some((nulls, base))) = (s, lv) else {
        return b.goto(no, span);
    };
    let base = *base;
    match v {
        ArmValue::Null => {
            test_nulls(b, s, &nulls[..nulls.len().min(1)], [yes; 2], span);
            b.goto(no, span);
        }
        ArmValue::Const(c) => {
            test_nulls(b, s, nulls, [no; 2], span);
            let t = compare(b, s, base, BinOp::Eq, *c, span);
            branch(b, t, yes, no, span);
        }
        ArmValue::Range(lo, hi) => {
            test_nulls(b, s, nulls, [no; 2], span);
            let t = compare(b, s, base, BinOp::Le, *lo, span);
            let mid = b.new_block();
            branch(b, t, mid, no, span);
            b.switch_to(mid);
            let t = compare(b, s, base, BinOp::Lt, *hi, span);
            branch(b, t, yes, no, span);
        }
        ArmValue::Case(_) | ArmValue::Cond(_) => unreachable!("a case run, or above"),
    }
}

/// `base op c` (`c op base` for `Le`, a range's low end) as a `bool` operand; a
/// string literal through `string`'s `equals` on two shared borrows (plan c.5).
fn compare(
    b: &mut Builder,
    s: &mut Subject,
    base: Place,
    op: BinOp,
    c: ConstValue,
    sp: Span,
) -> Operand {
    let tcx = b.cx.tcx;
    let (bt, bool_) = (b.place_ty(base), tcx.common().bool);
    let out = temp(b, bool_, sp);
    s.guard(b, base, sp);
    if let (ConstValue::Str(_), Some((def, args))) = (c, str_equals(b, bt)) {
        let r = tcx.mk_ref(bt);
        let a = to_temp(b, borrow(base, BorrowOrigin::AutoBorrow), r, sp);
        let f = FnRef { def, args };
        let lit = Operand::constant(c, r);
        call(b, Callee::Fn(f), vec![Operand::Move(a), lit], out, sp);
        return Operand::Move(out);
    }
    let k = Operand::constant(c, bt);
    let value = match op {
        BinOp::Le => Rvalue::Binary(op, k, Operand::Copy(base)),
        _ => Rvalue::Binary(op, Operand::Copy(base), k),
    };
    b.assign(out, value, sp);
    Operand::Move(out)
}

/// `string`'s `equals`, which `Eq.equals` at `string` is (choice: the class's own
/// member, known statically).
fn str_equals(b: &Builder, t: Ty) -> Option<(hir::DefId, hir::TyList)> {
    let tcx = b.cx.tcx;
    let (adt, args) = tcx.lang_class_of(t)?;
    Some((
        tcx.find_method(adt, args, enrang_base::intern("equals"))?,
        args,
    ))
}

pub(crate) fn borrow(place: Place, origin: BorrowOrigin) -> Rvalue {
    Rvalue::Ref { place, origin }
}

/// A condition in its own temporary scope (D2), as a `bool` operand.
pub(crate) fn cond(b: &mut Builder, e: &hir::Expr) -> Operand {
    b.open(ScopeKind::Statement, e.span);
    let c = temp(b, b.cx.tcx.common().bool, e.span);
    b.expr_into(e, c);
    b.pop_scope();
    Operand::Move(c)
}

/// An arm's guard and body, from its block; a failed guard goes to `next`.
fn lower_arm(b: &mut Builder, arm: &hir::Arm, dest: Place, next: BlockId, join: BlockId) {
    if let Some(g) = &arm.guard {
        let c = cond(b, g);
        let then = b.new_block();
        branch(b, c, then, next, g.span);
        b.switch_to(then);
    }
    b.open(ScopeKind::Arm, arm.span);
    match &arm.body {
        ArmBody::Expr(e) => {
            let tcx = b.cx.tcx;
            let statement = matches!(tcx.kind(b.place_ty(dest)), TyKind::Void | TyKind::Never);
            match statement && e.ty != b.place_ty(dest) {
                true => {
                    let t = temp(b, e.ty, e.span);
                    b.expr_into(e, t);
                }
                false => b.expr_into(e, dest),
            }
        }
        ArmBody::Block(blk) => b.lower_block(blk),
        ArmBody::Return(e) => {
            if let Some(e) = e {
                b.expr_into(e, Place::local(Local::RETURN));
            } else {
                b.return_void_ok(arm.span);
            }
            b.exit_to(ExitTarget::Return, arm.span);
        }
        ArmBody::Break(l) => b.exit_to(ExitTarget::Break(*l), arm.span),
        ArmBody::Continue(l) => b.exit_to(ExitTarget::Continue(*l), arm.span),
    }
    b.pop_scope();
    if b.cursor.is_some() {
        b.goto(join, arm.span);
    }
}

/// The facts an arm's values made hold in its block (c.20): sema gives each the
/// subject's span; any value but `null` on a nullable subject makes it non-null,
/// and so does a `default` after an unguarded `null` arm (`after_null`).
fn fact_tests(b: &mut Builder, subject: Span, arm: &hir::Arm, block: BlockId, after_null: bool) {
    for (f, info) in b.hir.facts.iter_enumerated() {
        let holds = match info.fact {
            Fact::Case(v) => arm.values.contains(&ArmValue::Case(v)),
            Fact::NonNull => {
                let present = |v: &ArmValue| !matches!(v, ArmValue::Null | ArmValue::Cond(_));
                match arm.values.is_empty() {
                    true => after_null,
                    false => arm.values.iter().all(present),
                }
            }
        };
        if (info.span == subject || info.retests.contains(&subject)) && holds {
            b.body.meta.fact_tests.push((f, block));
        }
    }
}

// ---------------------------------------------------------------------------------
// `??`, `?.`, `!`.

/// Lowers `a ?? d` into `dest` (c.11).
pub fn lower_coalesce(b: &mut Builder, a: &hir::Expr, d: &hir::Expr, dest: Place) {
    let mut s = Subject::of(b, a);
    let (none, join) = (b.new_block(), b.new_block());
    s.guard(b, s.place, a.span);
    let tag = discr(b, s.place, a.span);
    let some = b.new_block();
    switch(b, tag, vec![(0, none)], some, a.span);
    b.switch_to(some);
    let p = field0(b, s.place, VariantIdx::PRESENT);
    s.guard(b, p, a.span);
    let mut value = Rvalue::Use(read(b, p));
    if b.place_ty(dest) != b.place_ty(p)
        && matches!(b.cx.tcx.kind(b.place_ty(dest)), TyKind::Nullable(_))
    {
        // The payload is read into a slot first: phase 3 reads an aggregate's
        // operands from locals only (V09).
        let pt = b.place_ty(p);
        let v = to_temp(b, Rvalue::Use(read(b, p)), pt, a.span);
        value = Rvalue::Aggregate(AggregateKind::Present, vec![Operand::Move(v)]);
    }
    b.assign(dest, value, a.span);
    b.goto(join, a.span);
    b.switch_to(none);
    b.expr_into(d, dest);
    b.goto(join, d.span);
    b.switch_to(join);
}

/// Lowers `base?.member` into `dest` (c.11, c.7): `present(..)` of the member's
/// reference or of the call's result, `null` when a level of `base` is `null`.
pub fn lower_opt_chain(b: &mut Builder, c: &hir::OptChain, dest: Place, span: Span) {
    let tcx = b.cx.tcx;
    let mut s = Subject::of(b, &c.base);
    let (none, join) = (b.new_block(), b.new_block());
    let (nulls, obj) = levels(b, s.place);
    test_nulls(b, &mut s, &nulls, [none; 2], span);
    let dt = b.place_ty(dest);
    let inner = match tcx.kind(dt) {
        TyKind::Nullable(t) => t,
        _ => dt,
    };
    match &c.member {
        OptMember::Field(f) => {
            let fp = proj(b, obj, Proj::Field(*f));
            s.guard(b, fp, span);
            let v = match tcx.kind(b.place_ty(fp)) {
                // A reference read out of a field is one `Use(Copy)` into a slot,
                // where phase 3 gives it its loan (A:935, V09).
                TyKind::Ref(_) => {
                    let ft = b.place_ty(fp);
                    Operand::Move(to_temp(b, Rvalue::Use(Operand::Copy(fp)), ft, span))
                }
                _ => Operand::Move(to_temp(
                    b,
                    borrow(fp, BorrowOrigin::AutoBorrow),
                    inner,
                    span,
                )),
            };
            b.assign(
                dest,
                Rvalue::Aggregate(AggregateKind::Present, vec![v]),
                span,
            );
        }
        OptMember::Call { callee, args } => {
            // The receiver reads the payload already evaluated: the base is
            // evaluated once (O6). It is the last level's payload, narrowed through
            // every level, so `a.next?.next?.label()` calls on the `Node` (S:752).
            let last = *nulls
                .last()
                .expect("an optional chain has a nullable level");
            let payload = field0(b, last, VariantIdx::PRESENT);
            b.payloads.insert(c.base.id, payload);
            let pay_ty = b.place_ty(payload);
            let recv = receiver(b, &c.base, pay_ty, obj, callee, span);
            // The chain is the call's own type when that is nullable (or `void`).
            let ret = callee_ret(b, callee).unwrap_or(inner);
            let own = c.void_result || matches!(tcx.kind(ret), TyKind::Nullable(_));
            let kind = ExprKind::Call {
                callee: callee.clone(),
                receiver: recv.map(Box::new),
                args: args.clone(),
            };
            let call = hir::Expr::new(c.base.id, if own { dt } else { inner }, span, kind);
            match own {
                true => b.expr_into(&call, dest),
                false => {
                    let v = temp(b, inner, span);
                    b.expr_into(&call, v);
                    let op = read(b, v);
                    b.assign(
                        dest,
                        Rvalue::Aggregate(AggregateKind::Present, vec![op]),
                        span,
                    );
                }
            }
            b.payloads.remove(&c.base.id);
        }
    }
    b.goto(join, span);
    b.switch_to(none);
    if !c.void_result {
        b.assign(dest, Rvalue::Aggregate(AggregateKind::Null, vec![]), span);
    }
    b.goto(join, span);
    b.switch_to(join);
}

/// The receiver `call_receiver` would make for an optional call (G37): the
/// narrowed payload of the last level, of type `pay_ty`, auto-borrowed when owned (a reference is the receiver
/// itself), then upcast when the method is declared in a base of its class. The
/// payload is the place `Builder::payloads` holds for the base, read once.
fn receiver(
    b: &mut Builder,
    base: &hir::Expr,
    pay_ty: Ty,
    obj: Place,
    callee: &hir::Callee,
    span: Span,
) -> Option<hir::Expr> {
    let tcx = b.cx.tcx;
    let def = match callee {
        hir::Callee::Fn(f) => f.def,
        hir::Callee::BoundMember { found, .. } => *found,
        _ => return None,
    };
    let recv = tcx.sig_opt(def)?.receiver?;
    if !matches!(tcx.kind(base.ty), TyKind::Nullable(_)) {
        return None;
    }
    let id = base.id;
    let nn = hir::Expr::new(id, pay_ty, span, ExprKind::NonNull(Box::new(base.clone())));
    let owner = tcx.def(def).parent.and_then(|p| tcx.adt_of(p));
    // A method of `Box` itself (`clone`) takes the box, not what it holds.
    let on_box = owner.is_some_and(|o| tcx.is_lang_adt(o, hir::LangItem::Boxed));
    let mut e = match (recv, tcx.kind(pay_ty)) {
        (hir::Receiver::Static, _) => return None,
        (hir::Receiver::Move, _) => return Some(nn),
        (_, TyKind::Ref(_)) => {
            let mut nn = nn;
            nn.adjust.push(hir::Adjust::Reborrow);
            nn
        }
        (_, TyKind::Boxed(_)) if on_box => {
            let mut nn = nn;
            nn.adjust.push(hir::Adjust::AutoBorrow);
            return Some(nn);
        }
        (_, TyKind::Boxed(t)) => {
            let mut e = hir::Expr::new(id, t, span, ExprKind::Deref(Box::new(nn)));
            e.adjust.push(hir::Adjust::AutoBorrow);
            e
        }
        _ => {
            let mut nn = nn;
            nn.adjust.push(hir::Adjust::AutoBorrow);
            nn
        }
    };
    let mut at = b.place_ty(obj);
    while let TyKind::Ref(t) | TyKind::Boxed(t) = tcx.kind(at) {
        at = t;
    }
    match (owner, tcx.kind(at)) {
        (Some(owner), TyKind::Adt(adt, _)) if owner != adt && tcx.adt(owner).is_class() => {
            e.adjust.push(hir::Adjust::Upcast);
        }
        // A `Slice<T>` method on an array: the view of it, as C18 makes one.
        (Some(owner), TyKind::Array(_) | TyKind::Fixed(..))
            if tcx.is_lang_adt(owner, hir::LangItem::Slice) =>
        {
            let fixed = matches!(tcx.kind(at), TyKind::Fixed(..));
            e.adjust.push(match fixed {
                true => hir::Adjust::FixedToSlice,
                false => hir::Adjust::ArrayToSlice,
            });
        }
        _ => {}
    }
    Some(e)
}

/// The return type of a method an optional call names, at its arguments.
fn callee_ret(b: &Builder, callee: &hir::Callee) -> Option<Ty> {
    let tcx = b.cx.tcx;
    let (def, args) = match callee {
        hir::Callee::Fn(f) => (f.def, f.args),
        hir::Callee::BoundMember { found, args, .. } => (*found, *args),
        _ => return None,
    };
    let sig = tcx.sig_opt(def)?;
    let params = tcx.all_params(sig.generics);
    let args = tcx.list(args);
    (params.len() == args.len()).then(|| tcx.subst(sig.ret, &params, &args))
}

/// Lowers `e!` to the place of its payload (c.5). Its user emits the guard run,
/// so the tag check lands directly before the statement that uses the place,
/// after any index operand a projection below it evaluates (V08).
///
/// On a reference to a nullable, `r!` is a reference to the payload (S:752):
/// `&(*r as Present).0`, a reborrow in a temporary, which is the place.
pub fn lower_non_null(b: &mut Builder, e: &hir::Expr) -> Place {
    if let Some(p) = b.payloads.remove(&e.id) {
        return p;
    }
    let s = Subject::of(b, e);
    let tcx = b.cx.tcx;
    let ty = b.place_ty(s.place);
    let TyKind::Ref(inner) = tcx.kind(ty) else {
        return field0(b, s.place, VariantIdx::PRESENT);
    };
    let target = proj(b, s.place, Proj::Deref);
    let payload = field0(b, target, VariantIdx::PRESENT);
    let pay_ty = match tcx.kind(inner) {
        TyKind::Nullable(t) => t,
        _ => inner,
    };
    b.guard(payload, e.span);
    let rv = Rvalue::Ref {
        place: payload,
        origin: enrang_mir::BorrowOrigin::Reborrow,
    };
    to_temp(b, rv, tcx.mk_ref(pay_ty), e.span)
}

// ---------------------------------------------------------------------------------
// Narrowing records (c.20).

impl Builder<'_> {
    /// The place of a local an arrow body captures (c.16): `*((*_1).i)` for a
    /// path or a closure parameter, `(*_1).i`, the reference itself, for a
    /// reference local.
    pub fn captured_place(&mut self, l: LocalId) -> Option<Place> {
        let enrang_mir::BodyOwner::Arrow(_, k) = self.body.owner else {
            return None;
        };
        let i = self.hir.arrows[k]
            .captures
            .iter()
            .position(|c| c.local == l)?;
        let field = self
            .body
            .place(Local(1), &[Proj::Deref, Proj::Field(FieldIdx::new(i))]);
        Some(match self.body.captures.get(i)?.kind {
            enrang_mir::CaptureKind::ThroughRef => field,
            _ => self.body.project(field, Proj::Deref),
        })
    }
}

/// `ConvKind` of a spread or literal view's reference to `t`, if one is needed.
pub(crate) fn slice_conv(b: &Builder, t: Ty) -> Option<ConvKind> {
    let tcx = b.cx.tcx;
    match tcx.kind(t) {
        TyKind::Ref(x) => match tcx.kind(x) {
            TyKind::Array(_) => Some(ConvKind::ArrayToSlice),
            TyKind::Fixed(..) => Some(ConvKind::FixedToSlice),
            _ => None,
        },
        _ => None,
    }
}
