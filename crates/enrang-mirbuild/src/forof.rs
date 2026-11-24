//! `for...of` (A:949-964, S:998-1027; M3 plan c.13; owner 2C): the pre-header,
//! head and bind of each source shape, the hidden locals, `ForOfLoop` in
//! `PhaseMeta`, and an owned array source as a `HiddenLoop(IntoIter)` local.
//!
//! A `Path` and a `Once` source in `Ref` mode share one shape, recorded in
//! `meta.loops`: `S` is the path, or `*_src`; the head reads `Len(S)` every turn;
//! the bind is unconditional, `x = &S[_i] [for-of-element]` (no array holds a
//! reference, EN0701), then the wrapping `_i + 1`. The binding and its parts are
//! entries of the turn's scope, so every exit ends them once; `continue` and the
//! fall-through land on a latch block, `goto head`. An owned `T[]` moves into `_iter`, dropped with the statement, and each
//! element moves out of it (X2); an owned `T[N]` is copied element by element; a
//! range counts `_cur` up to `_end`. None of these three has a `for-of-element`
//! borrow, so none is recorded.

use enrang_base::Span;
use enrang_hir::{self as hir, BindingMode, ExprKind, ForSource, LoopId, TyKind};
use enrang_mir::{
    BinOp, BorrowOrigin, ForOfLoop, LocalKind, LoopRole, LoopSource, Operand, Place, Point, Proj,
    Rvalue, StatementKind,
};

use crate::builder::Builder;
use crate::matches::{Subject, borrow, branch, is_place, op_ty, read, temp};
use crate::pattern::{bind_parts, binds};
use crate::scope::ScopeKind;

/// A hidden local of a loop.
fn hidden(b: &mut Builder, t: enrang_hir::Ty, role: LoopRole, span: Span) -> Place {
    let p = temp(b, t, span);
    b.body.locals[p.local].kind = LocalKind::HiddenLoop(role);
    p
}

fn add_one(b: &mut Builder, p: Place, span: Span) {
    let t = b.place_ty(p);
    let one = Operand::constant(enrang_hir::ConstValue::Int(1, t), t);
    b.assign(p, Rvalue::Binary(BinOp::Add, Operand::Copy(p), one), span);
}

/// Lowers one `for...of` loop (A:949-964).
pub fn lower_for_of(
    b: &mut Builder,
    id: LoopId,
    pat: &hir::Pat,
    src: &ForSource,
    body: &hir::Block,
    span: Span,
) {
    let tcx = b.cx.tcx;
    let isize = tcx.common().isize;
    b.open(ScopeKind::Statement, span);
    let (head, bind, latch, exit) = (b.new_block(), b.new_block(), b.new_block(), b.new_block());
    // The binding: the pattern's local, or a temporary its parts are bound from.
    let elem_of = |b: &Builder, s: Place| match tcx.kind(b.place_ty(s)) {
        TyKind::Array(e) | TyKind::Fixed(e, _) | TyKind::Slice(e) => e,
        _ => tcx.common().error,
    };
    // The loop's scope and the turn's, entered at the bind, so a binding and its
    // parts drop at every exit of the turn.
    let binding = |b: &mut Builder, t| {
        let loop_ = ScopeKind::Loop {
            id,
            head: latch,
            exit,
        };
        b.open(loop_, span);
        b.open(ScopeKind::Block, crate::builder::closing(body.span));
        let x = match pat {
            hir::Pat::Bind(l) => Place::local(b.local(*l)),
            _ => temp(b, t, span),
        };
        // The turn's scope ends the binding at every exit (c.3, c.13).
        b.scope_local(x.local);
        x
    };
    let x = match src {
        ForSource::Range { lo, hi } => {
            let sp = lo.span.to(hi.span);
            let cur = hidden(b, lo.ty, LoopRole::RangeCursor, sp);
            b.expr_into(lo, cur);
            let end = hidden(b, lo.ty, LoopRole::RangeEnd, sp);
            b.expr_into(hi, end);
            b.goto(head, sp);
            b.switch_to(head);
            let c = temp(b, tcx.common().bool, sp);
            b.assign(c, lt(cur, end), sp);
            branch(b, Operand::Move(c), bind, exit, sp);
            b.switch_to(bind);
            let x = binding(b, lo.ty);
            b.push(StatementKind::StorageLive(x.local), span);
            b.assign(x, Rvalue::Use(Operand::Copy(cur)), sp);
            add_one(b, cur, sp);
            x
        }
        ForSource::Path { place: e } | ForSource::Once { value: e, .. } => {
            let sp = e.span;
            let mode = match src {
                ForSource::Once { mode, .. } => Some(*mode),
                _ => None,
            };
            // `_src` or `_iter`, set before the pre-header.
            let once = match mode {
                None => None,
                Some(BindingMode::Ref) => {
                    let (p, t) = match &e.kind {
                        ExprKind::Borrow(inner) if e.adjust.is_empty() && is_place(inner) => {
                            let place = b.as_place(inner);
                            (borrow(place, BorrowOrigin::ForOfHidden), e.ty)
                        }
                        _ => {
                            let op = b.as_operand(e);
                            let t = op_ty(b, &op);
                            (Rvalue::Use(op), t)
                        }
                    };
                    let s = hidden(b, t, LoopRole::Source, sp);
                    b.assign(s, p, sp);
                    Some(s)
                }
                Some(BindingMode::Owned) => {
                    let role = match tcx.kind(e.ty) {
                        TyKind::Array(_) => LoopRole::IntoIter,
                        _ => LoopRole::Source,
                    };
                    let s = hidden(b, e.ty, role, sp);
                    b.expr_into(e, s);
                    Some(s)
                }
            };
            let pre = b.new_block();
            b.goto(pre, sp);
            b.switch_to(pre);
            let i = hidden(b, isize, LoopRole::Index, sp);
            b.push(StatementKind::StorageLive(i.local), sp);
            let zero = enrang_hir::ConstValue::Int(0, isize);
            b.assign(i, Rvalue::Use(Operand::constant(zero, isize)), sp);
            b.goto(head, sp);
            b.switch_to(head);
            let mut s = match (mode, once) {
                (None, _) => Subject::of(b, e),
                (Some(BindingMode::Ref), Some(o)) => {
                    let place = b.body.project(o, Proj::Deref);
                    Subject::at(place)
                }
                (_, o) => Subject::at(o.expect("a source local")),
            };
            let n = hidden(b, isize, LoopRole::Length, sp);
            s.guard(b, s.place, sp);
            b.assign(n, Rvalue::Len(s.place), sp);
            let c = temp(b, tcx.common().bool, sp);
            b.assign(c, lt(i, n), sp);
            branch(b, Operand::Move(c), bind, exit, sp);
            b.switch_to(bind);
            let elem = elem_of(b, s.place);
            let by_ref = mode != Some(BindingMode::Owned);
            let x = binding(b, if by_ref { tcx.mk_ref(elem) } else { elem });
            b.push(StatementKind::StorageLive(x.local), span);
            let bounds = StatementKind::CheckBounds {
                index: Operand::Copy(i),
                len: Operand::Copy(n),
            };
            b.push(bounds, sp);
            s.guard(b, s.place, sp);
            let at = b.body.project(s.place, Proj::Index(i.local));
            let value = match by_ref {
                true => borrow(at, BorrowOrigin::ForOfElement),
                false => Rvalue::Use(read(b, at)),
            };
            let point = Point::new(bind, b.body.blocks[bind].stmts.len());
            b.assign(x, value, sp);
            add_one(b, i, sp);
            if by_ref {
                let source = match once {
                    Some(o) => LoopSource::Once(o.local),
                    None => LoopSource::Path(s.place),
                };
                b.body.meta.loops.push(ForOfLoop {
                    id,
                    preheader: pre,
                    head,
                    bind: point,
                    source,
                    binding: x.local,
                    span: sp,
                });
            }
            x
        }
    };
    let first = b.new_block();
    b.goto(first, span);
    b.switch_to(first);
    let mut bound = Vec::new();
    if !matches!(pat, hir::Pat::Bind(_)) {
        let mut s = Subject::at(x);
        bind_parts(b, &mut s, pat, x, false, span);
        binds(pat, &mut bound);
    }
    let owned: Vec<Place> = bound.iter().map(|l| Place::local(b.locals[l])).collect();
    for p in &owned {
        b.scope_local(p.local);
    }
    b.lower_block(body);
    b.pop_scope();
    b.pop_scope();
    if b.cursor.is_some() {
        b.goto(latch, body.span);
    }
    b.switch_to(latch);
    b.goto(head, body.span);
    b.switch_to(exit);
    b.pop_scope();
}

fn lt(a: Place, n: Place) -> Rvalue {
    Rvalue::Binary(BinOp::Lt, Operand::Copy(a), Operand::Copy(n))
}
