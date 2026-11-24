//! The walk over a finished body's expressions that the passes share. It needs
//! nothing of sema but `enrang-hir`, so the sema suite includes this file as it is
//! (as it includes `src/exhaust/`) to test it on hand-built bodies.

use enrang_hir::{
    ArmBody, ArmValue, ArrayPart, ArrowBodyKind, Block, Body, Callee, ExpectArg, Expr, ExprKind,
    ForSource, OptMember, StmtKind, TplPart,
};

/// Calls `f` on every expression of `body`, its arrows and parameter defaults
/// included, parents before children; a `match` arm's conditions come before its
/// guard and its body.
pub(crate) fn for_each_expr(body: &Body, f: &mut dyn FnMut(&Expr)) {
    for (_, default) in &body.param_defaults {
        walk_expr(default, f);
    }
    walk_block(&body.root, f);
    for arrow in &body.arrows {
        match &arrow.body {
            ArrowBodyKind::Expr(e) => walk_expr(e, f),
            ArrowBodyKind::Block(b) => walk_block(b, f),
        }
    }
}

fn walk_block(b: &Block, f: &mut dyn FnMut(&Expr)) {
    for stmt in &b.stmts {
        walk_stmt(&stmt.kind, f);
    }
}

fn walk_stmt(s: &StmtKind, f: &mut dyn FnMut(&Expr)) {
    match s {
        StmtKind::Let { init, .. } => init.iter().for_each(|e| walk_expr(e, f)),
        StmtKind::Destructure { init, .. } => walk_expr(init, f),
        StmtKind::If { cond, then_, else_ } => {
            walk_expr(cond, f);
            walk_block(then_, f);
            if let Some(b) = else_ {
                walk_block(b, f);
            }
        }
        StmtKind::While { cond, body, .. } | StmtKind::DoWhile { body, cond, .. } => {
            walk_expr(cond, f);
            walk_block(body, f);
        }
        StmtKind::For {
            init,
            cond,
            step,
            body,
            ..
        } => {
            if let Some(s) = init {
                walk_stmt(&s.kind, f);
            }
            cond.iter().for_each(|e| walk_expr(e, f));
            if let Some(s) = step {
                walk_stmt(&s.kind, f);
            }
            walk_block(body, f);
        }
        StmtKind::ForOf { source, body, .. } => {
            match source {
                ForSource::Path { place } => walk_expr(place, f),
                ForSource::Once { value, .. } => walk_expr(value, f),
                ForSource::Range { lo, hi } => {
                    walk_expr(lo, f);
                    walk_expr(hi, f);
                }
            }
            walk_block(body, f);
        }
        StmtKind::Return(e) => e.iter().for_each(|e| walk_expr(e, f)),
        StmtKind::Break(_) | StmtKind::Continue(_) => {}
        StmtKind::Block(b) | StmtKind::Unsafe(b) => walk_block(b, f),
        StmtKind::Expr(e) => walk_expr(e, f),
        StmtKind::Expect(x) => {
            walk_expr(&x.actual, f);
            for arg in &x.args {
                match arg {
                    ExpectArg::Expr(e) => walk_expr(e, f),
                    ExpectArg::Arm(v) => walk_arm_value(v, f),
                }
            }
        }
    }
}

/// A `match (true)` arm's condition is an expression; other arm values are not.
fn walk_arm_value(v: &ArmValue, f: &mut dyn FnMut(&Expr)) {
    if let ArmValue::Cond(e) = v {
        walk_expr(e, f);
    }
}

fn walk_callee(c: &Callee, f: &mut dyn FnMut(&Expr)) {
    if let Callee::FnPtr(e) = c {
        walk_expr(e, f);
    }
}

fn walk_expr(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    f(e);
    match &e.kind {
        ExprKind::Field(b, _)
        | ExprKind::Deref(b)
        | ExprKind::NarrowedPayload(b, _, _)
        | ExprKind::Repeat(b, _)
        | ExprKind::Unary(_, b)
        | ExprKind::Cast(b, _)
        | ExprKind::Borrow(b)
        | ExprKind::AddrOf(b)
        | ExprKind::Try(b, _)
        | ExprKind::NonNull(b)
        | ExprKind::VoidOp(b)
        | ExprKind::IncDec { target: b, .. } => walk_expr(b, f),
        ExprKind::Destructure { pat, value } => {
            pat.places().into_iter().for_each(|p| walk_expr(p, f));
            walk_expr(value, f);
        }
        ExprKind::Index(a, b)
        | ExprKind::Binary(_, a, b)
        | ExprKind::Logical(_, a, b)
        | ExprKind::Coalesce(a, b)
        | ExprKind::Assign {
            target: a,
            value: b,
            ..
        } => {
            walk_expr(a, f);
            walk_expr(b, f);
        }
        ExprKind::Ternary(a, b, c) => {
            walk_expr(a, f);
            walk_expr(b, f);
            walk_expr(c, f);
        }
        ExprKind::Template(parts) => {
            for part in parts {
                if let TplPart::Hole(e) = part {
                    walk_expr(e, f);
                }
            }
        }
        ExprKind::ArrayLit(items)
        | ExprKind::TupleLit(items)
        | ExprKind::ObjectLit { fields: items, .. }
        | ExprKind::VariantLit { fields: items, .. }
        | ExprKind::New { values: items, .. } => items.iter().for_each(|e| walk_expr(e, f)),
        ExprKind::ArrayBuild { parts, .. } => {
            for part in parts {
                match part {
                    ArrayPart::Item(e) | ArrayPart::Spread(e, _) => walk_expr(e, f),
                }
            }
        }
        ExprKind::NewNamed { fields, .. } => fields.iter().for_each(|(_, e)| walk_expr(e, f)),
        ExprKind::Call {
            callee,
            receiver,
            args,
        } => {
            walk_callee(callee, f);
            if let Some(r) = receiver {
                walk_expr(r, f);
            }
            args.iter().for_each(|e| walk_expr(e, f));
        }
        ExprKind::OptionalChain(chain) => {
            walk_expr(&chain.base, f);
            if let OptMember::Call { callee, args } = &chain.member {
                walk_callee(callee, f);
                args.iter().for_each(|e| walk_expr(e, f));
            }
        }
        ExprKind::Match { subject, arms } => {
            walk_expr(subject, f);
            for arm in arms {
                for value in &arm.values {
                    walk_arm_value(value, f);
                }
                if let Some(g) = &arm.guard {
                    walk_expr(g, f);
                }
                match &arm.body {
                    ArmBody::Expr(e) => walk_expr(e, f),
                    ArmBody::Block(b) => walk_block(b, f),
                    ArmBody::Return(e) => e.iter().for_each(|e| walk_expr(e, f)),
                    ArmBody::Break(_) | ArmBody::Continue(_) => {}
                }
            }
        }
        ExprKind::Asm(asm) => {
            asm.ins.iter().for_each(|(_, e)| walk_expr(e, f));
            asm.outs
                .iter()
                .filter_map(|(_, e)| e.as_ref())
                .for_each(|e| walk_expr(e, f));
        }
        ExprKind::Local(_)
        | ExprKind::Static(_)
        | ExprKind::Const(_)
        | ExprKind::Arrow(_)
        | ExprKind::Never
        | ExprKind::NullLit => {}
    }
}
