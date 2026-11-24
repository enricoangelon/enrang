//! Destructuring (A:948, S:987-996; M3 plan c.15; owner 2C): binding the parts of
//! an object or tuple by reference or by value, and destructuring assignments
//! (D9, D17).
//!
//! At each level a reference value gives references, `l = &place.f [destructure]`,
//! or a copy of a part that is itself a reference (O7); an owned value copies each
//! Copy part and moves the others out of the place (a partial move). An assignment
//! evaluates its right side into a temporary (the pointee of a reference is read in
//! place) and assigns each part to its target in source order as D3 does: the
//! target's operands, the part into a temporary, `drop(target) [assign]`, the
//! store, the target's guards again before each. Which of the two a pattern is: an
//! assignment names a `Pat::Place`, or a local already declared (bindings of a
//! declaration are new; choice).

use enrang_base::Span;
use enrang_hir::{self as hir, BindingMode, ClassModifier, ExprKind, FieldIdx, TyKind};
use enrang_mir::{
    BorrowOrigin, ClassHolder, ClassOp, DropOrigin, Place, Proj, Rvalue, StatementKind,
};

use crate::builder::Builder;
use crate::matches::{Subject, borrow, read, temp, to_temp};

/// Lowers `const { a, b } = init` in `mode`, or a destructuring assignment.
pub fn lower_destructure(b: &mut Builder, pat: &hir::Pat, mode: BindingMode, init: &hir::Expr) {
    let span = init.span;
    if is_assignment(b, pat) {
        let mut s = match &init.kind {
            ExprKind::Deref(r) if init.adjust.is_empty() && is_ref(b, r.ty) => {
                let s = Subject::of(b, r);
                let at = b.body.project(s.place, Proj::Deref);
                Subject::at(at)
            }
            _ => {
                let t = temp(b, init.ty, span);
                b.expr_into(init, t);
                Subject::at(t)
            }
        };
        let at = s.place;
        return store_parts(b, &mut s, pat, at, span);
    }
    // `&place` is read through in place; any other reference is dereferenced.
    let mut s = match (&init.kind, mode) {
        (ExprKind::Borrow(inner), BindingMode::Ref)
            if init.adjust.is_empty() && crate::matches::is_place(inner) =>
        {
            Subject::of(b, inner)
        }
        _ => Subject::of(b, init),
    };
    let at = s.place;
    let outer = b.destructure.replace(init.id);
    bind_parts(b, &mut s, pat, at, mode == BindingMode::Ref, span);
    b.destructure = outer;
}

fn is_ref(b: &Builder, t: enrang_hir::Ty) -> bool {
    matches!(b.cx.tcx.kind(t), TyKind::Ref(_))
}

/// Whether `pat` assigns rather than declares: a local already declared here, or
/// captured by the arrow being built.
fn is_assignment(b: &mut Builder, pat: &hir::Pat) -> bool {
    match pat {
        hir::Pat::Place(_) => true,
        hir::Pat::Bind(l) => b.locals.contains_key(l) || b.captured_place(*l).is_some(),
        hir::Pat::Object(fs) => fs.iter().any(|(_, p)| is_assignment(b, p)),
        hir::Pat::Tuple(ps) => ps.iter().any(|p| is_assignment(b, p)),
    }
}

/// The locals a pattern binds, in order.
pub(crate) fn binds(pat: &hir::Pat, out: &mut Vec<hir::LocalId>) {
    match pat {
        hir::Pat::Bind(l) => out.push(*l),
        hir::Pat::Object(fs) => fs.iter().for_each(|(_, p)| binds(p, out)),
        hir::Pat::Tuple(ps) => ps.iter().for_each(|p| binds(p, out)),
        hir::Pat::Place(_) => {}
    }
}

/// The part `k` of `place`: a field of a class or object, or a tuple part.
fn part(b: &mut Builder, place: Place, k: FieldIdx) -> Place {
    b.body.project(place, Proj::Field(k))
}

/// Binds the parts of `place` (c.15); `by_ref` when reached through a reference.
pub(crate) fn bind_parts(
    b: &mut Builder,
    s: &mut Subject,
    pat: &hir::Pat,
    place: Place,
    by_ref: bool,
    span: Span,
) {
    let t = b.place_ty(place);
    match (b.cx.tcx.kind(t), pat) {
        (_, hir::Pat::Bind(l)) => {
            let x = Place::local(b.local(*l));
            b.push(StatementKind::StorageLive(x.local), span);
            s.guard(b, place, span);
            let (value, referent) = match (by_ref && !is_ref(b, t), is_ref(b, t)) {
                (true, _) => (borrow(place, BorrowOrigin::Destructure), Some(place)),
                (false, true) => (
                    Rvalue::Use(read(b, place)),
                    Some(b.body.project(place, Proj::Deref)),
                ),
                (false, false) => (Rvalue::Use(read(b, place)), None),
            };
            b.assign(x, value, span);
            if let Some(r) = referent {
                binding_records(b, x.local, r);
            }
        }
        (TyKind::Ref(_) | TyKind::Boxed(_), _) => {
            let inner = b.body.project(place, Proj::Deref);
            let by_ref = by_ref || is_ref(b, t);
            bind_parts(b, s, pat, inner, by_ref, span);
        }
        (_, hir::Pat::Object(fields)) => {
            for (f, sub) in fields {
                let at = part(b, place, *f);
                bind_parts(b, s, sub, at, by_ref, span);
            }
        }
        (_, hir::Pat::Tuple(parts)) => {
            for (k, sub) in parts.iter().enumerate() {
                let at = part(b, place, FieldIdx(k as u32));
                bind_parts(b, s, sub, at, by_ref, span);
            }
        }
        (_, hir::Pat::Place(_)) => {}
    }
}

/// The narrowing records of the destructured expression (`Binding`, S:744) that
/// the reference `x` just bound to `referent` carries: each fact whose path
/// `referent` is a prefix of, or is, since a pattern never binds a payload, so a
/// reference to the fact's own path has its nullable type. A binding beside the
/// fact's path, `other` of `const { other } = h` under `h.items != null`, carries
/// none (c.20).
fn binding_records(b: &mut Builder, x: enrang_mir::Local, referent: Place) {
    let Some(origin) = b.destructure else {
        return;
    };
    let Some(at) = b.last_assign(x) else {
        return;
    };
    let steps = |b: &Builder, p: Place| -> Vec<hir::PathStep> {
        b.body
            .projs(p)
            .iter()
            .map(|x| match x {
                Proj::Field(f) => hir::PathStep::Field(*f),
                _ => hir::PathStep::Deref,
            })
            .collect()
    };
    let mine = steps(b, referent);
    let hir = b.hir;
    for r in hir.records.iter() {
        if r.expr != origin || r.kind != hir::RecordKind::Binding {
            continue;
        }
        let root = hir.facts[r.fact].path.root;
        if !b.locals.contains_key(&root) && b.captured_place(root).is_none() {
            continue;
        }
        let base = b.local_place(root);
        if base.local != referent.local {
            continue;
        }
        let mut fact = steps(b, base);
        fact.extend(hir.facts[r.fact].path.steps.iter().copied());
        let known = (b.body.meta.records.iter()).any(|m| m.fact == r.fact && m.at == at);
        if fact.starts_with(&mine) && !known {
            b.body.meta.records.push(enrang_mir::MirRecord {
                fact: r.fact,
                at,
                slot: x,
                kind: r.kind,
                span: r.span,
            });
        }
    }
}

/// Assigns each part of `place` to its target, in source order (A:948).
fn store_parts(b: &mut Builder, s: &mut Subject, pat: &hir::Pat, place: Place, span: Span) {
    let target = match pat {
        hir::Pat::Object(fields) => {
            for (f, sub) in fields {
                let at = part(b, place, *f);
                store_parts(b, s, sub, at, span);
            }
            return;
        }
        hir::Pat::Tuple(parts) => {
            for (k, sub) in parts.iter().enumerate() {
                let at = part(b, place, FieldIdx(k as u32));
                store_parts(b, s, sub, at, span);
            }
            return;
        }
        hir::Pat::Bind(l) => {
            let decl = &b.hir.locals[*l];
            let e = hir::Expr::new(hir::ExprId(0), decl.ty, decl.span, ExprKind::Local(*l));
            Subject::of(b, &e)
        }
        hir::Pat::Place(e) => Subject::of(b, e),
    };
    let mut target = target;
    let tt = b.place_ty(place);
    s.guard(b, place, span);
    let v = read(b, place);
    let v = to_temp(b, Rvalue::Use(v), tt, span);
    let dest = target.place;
    let check = class_check(b, dest);
    if b.cx.tcx.needs_drop(b.place_ty(dest)) || check.is_some() {
        target.guard(b, dest, span);
        if let Some(c) = check.clone() {
            b.push(c, span);
        }
        if b.cx.tcx.needs_drop(b.place_ty(dest)) {
            b.push(StatementKind::Drop(dest, DropOrigin::Assign), span);
        }
    }
    target.guard(b, dest, span);
    b.assign(dest, Rvalue::Use(read(b, v)), span);
}

/// `check_class(*a, assign, via)` before a whole-object write through a reference
/// or box of a class that can be extended, or of a type parameter (A:943).
fn class_check(b: &mut Builder, p: Place) -> Option<StatementKind> {
    let tcx = b.cx.tcx;
    let projs = b.body.projs(p).to_vec();
    if projs.last() != Some(&Proj::Deref) {
        return None;
    }
    let holder = b.body.place(p.local, &projs[..projs.len() - 1]);
    let via = match tcx.kind(b.place_ty(holder)) {
        TyKind::Ref(_) => ClassHolder::Ref,
        TyKind::Boxed(_) => ClassHolder::Box,
        _ => return None,
    };
    let open = match tcx.kind(b.place_ty(p)) {
        TyKind::Param(_) => true,
        TyKind::Adt(a, _) => tcx
            .adt(a)
            .as_class()
            .is_some_and(|c| c.modifier != ClassModifier::Final),
        _ => false,
    };
    open.then_some(StatementKind::CheckClass {
        place: p,
        op: ClassOp::Assign,
        via,
    })
}
