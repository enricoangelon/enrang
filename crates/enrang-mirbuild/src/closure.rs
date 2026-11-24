//! Arrows, captures and closure values (A:971-973; M3 plan c.16; owner 2C).
//!
//! At the creation site each capture, in the HIR's order, is one `[closure-capture]`
//! borrow: `&l` of an owned path, `&*r` through a reference local, `&f` of a closure
//! parameter; then `_env = env(..)` and `closure(arrow#k, _env)`. A non-capturing
//! arrow at an `fn` type is `arrow_fn#k` (D24). The arrow's body is its own MIR body,
//! `_1: &Env` (an anonymous tuple of the capture references), then its parameters;
//! a captured local is `*((*_1).i)`, or `(*_1).i` for a reference local
//! (`Builder::captured_place`). The local functions' hidden arguments (c.17) are
//! 2B's: `call.rs` passes them, `builder.rs` declares them.

use enrang_base::{Span, intern};
use enrang_hir::{self as hir, ArrowBodyKind, ArrowId, ExprKind, TyKind};
use enrang_mir::{
    AggregateKind, Block, Body, BodyOwner, BorrowOrigin, Capture, CaptureKind, ClosureFn, Local,
    LocalDecl, LocalKind, MirRecord, Place, Point, Proj, Rvalue, Terminator, TerminatorKind,
};

use crate::BuildCx;
use crate::builder::Builder;
use crate::matches::{borrow, to_temp};
use crate::scope::ScopeKind;

/// How `l` is captured, and the type of its environment field.
fn capture(b: &Builder, l: hir::LocalId) -> (CaptureKind, hir::Ty) {
    let tcx = b.cx.tcx;
    let decl = &b.hir.locals[l];
    let param = matches!(
        decl.kind,
        hir::LocalKind::Param(_) | hir::LocalKind::Arrow(_)
    );
    let closure = |t| matches!(tcx.kind(t), TyKind::Closure(_));
    match tcx.kind(decl.ty) {
        TyKind::Ref(_) => (CaptureKind::ThroughRef, decl.ty),
        TyKind::Nullable(t) if param && closure(t) => {
            (CaptureKind::ClosureParam, tcx.mk_ref(decl.ty))
        }
        _ if param && closure(decl.ty) => (CaptureKind::ClosureParam, tcx.mk_ref(decl.ty)),
        _ => (CaptureKind::Path, tcx.mk_ref(decl.ty)),
    }
}

/// Lowers the arrow `arrow` as a value into `dest` (c.16).
pub fn lower_arrow_value(b: &mut Builder, arrow: ArrowId, dest: Place, span: Span) {
    let tcx = b.cx.tcx;
    if matches!(tcx.kind(b.place_ty(dest)), TyKind::FnPtr(..)) {
        return b.assign(dest, Rvalue::ArrowFn(arrow), span);
    }
    let mut ops = Vec::new();
    let mut tys = Vec::new();
    for c in b.hir.arrows[arrow].captures.clone() {
        let (kind, field) = capture(b, c.local);
        let decl = &b.hir.locals[c.local];
        let e = hir::Expr::new(hir::ExprId(0), decl.ty, c.span, ExprKind::Local(c.local));
        let mut place = b.as_place(&e);
        if kind == CaptureKind::ThroughRef {
            place = b.body.project(place, Proj::Deref);
        }
        let at = b
            .cursor
            .map(|bb| Point::new(bb, b.body.blocks[bb].stmts.len()));
        let r = to_temp(
            b,
            borrow(place, BorrowOrigin::ClosureCapture),
            field,
            c.span,
        );
        let recs = b
            .hir
            .records
            .iter()
            .filter(|x| x.kind == hir::RecordKind::Capture);
        for x in recs.filter(|x| x.span == c.span) {
            if let Some(at) = at {
                let rec = MirRecord {
                    fact: x.fact,
                    at,
                    slot: r.local,
                    kind: x.kind,
                    span: x.span,
                };
                b.body.meta.records.push(rec);
            }
        }
        ops.push(enrang_mir::Operand::Move(r));
        tys.push(field);
    }
    let env = to_temp(
        b,
        Rvalue::Aggregate(AggregateKind::ClosureEnv, ops),
        tcx.mk_tuple(&tys),
        span,
    );
    let value = Rvalue::ClosureValue {
        func: ClosureFn::Arrow(arrow),
        env,
    };
    b.assign(dest, value, span);
}

/// Builds arrow `arrow` of `parent`'s body (c.16): `_1` its environment, then
/// its parameters, its expression into `_0` or its block.
pub fn build_arrow_body(cx: &BuildCx, parent: hir::BodyOwner, arrow: ArrowId) -> Body {
    let owner = BodyOwner::Arrow(parent, arrow);
    let Some(hir_body) = cx.hir_body(parent) else {
        let mut body = Body::new(owner, cx.tcx.common().void, Span::DUMMY);
        let term = Terminator::new(TerminatorKind::Return, Span::DUMMY);
        body.blocks.push(Block {
            stmts: Vec::new(),
            term,
        });
        return body;
    };
    let a = &hir_body.arrows[arrow];
    // `Builder::new` makes the parent's arguments: an arrow has its own.
    let mut b = Builder::new(cx, hir_body);
    b.body = Body::new(owner, a.ret, a.span);
    b.locals.clear();
    b.scopes.clear();
    b.expr_points.clear();
    b.hidden.clear();
    b.facts_of.clear();
    b.record_points.clear();
    b.valued.clear();
    b.region = None;
    let mut tys = Vec::new();
    for c in &a.captures {
        let (kind, ty) = capture(&b, c.local);
        let name = hir_body.locals[c.local].name.unwrap_or_else(|| intern("_"));
        let span = c.span;
        b.body.captures.push(Capture {
            name,
            ty,
            kind,
            span,
        });
        tys.push(ty);
    }
    let env = cx.tcx.mk_ref(cx.tcx.mk_tuple(&tys));
    b.body
        .locals
        .push(LocalDecl::new(env, LocalKind::ClosureEnv, a.span));
    // A parameter written `let` is changeable, as a `let` local is; the mark is
    // the arrow's signature's (S:444), and phase 3 freezes every other (S:774).
    let marks: Vec<bool> = (cx.tcx.fn_sig(a.sig).params.iter())
        .map(|&(_, m)| m == hir::Mark::Let)
        .collect();
    for (i, &p) in a.params.iter().enumerate() {
        let d = &hir_body.locals[p];
        let l = b.body.locals.push(LocalDecl {
            ty: d.ty,
            mutable: d.mutable || marks.get(i).copied().unwrap_or(false),
            name: d.name,
            span: d.span,
            kind: LocalKind::Arg,
        });
        b.locals.insert(p, l);
    }
    b.body.arg_count = a.params.len() as u32 + 1;
    let entry = b.new_block();
    b.switch_to(entry);
    b.open(ScopeKind::Body, crate::builder::closing(a.span));
    for &p in &a.params {
        if cx.tcx.needs_drop(hir_body.locals[p].ty) {
            let l = b.locals[&p];
            b.schedule_drop(Place::local(l));
        }
    }
    match &a.body {
        ArrowBodyKind::Expr(e) => b.expr_into(e, Place::local(Local::RETURN)),
        ArrowBodyKind::Block(blk) => b.lower_block(blk),
    }
    b.pop_scope();
    if b.cursor.is_some() {
        if matches!(a.body, ArrowBodyKind::Block(_)) {
            b.return_void_ok(a.span);
        }
        b.terminate(TerminatorKind::Return, a.span);
    }
    b.finish();
    b.body
}
