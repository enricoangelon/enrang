//! Passes over declarations and finished bodies (plan d.13, d.15, d.17): R1/R2
//! positions (`positions.rs`), the view and string facts (`views.rs`), the five
//! unsafe powers (`unsafety.rs`), deferred names in expressions (`deferred.rs`),
//! exhaustiveness (`matches.rs`), and phase 4's size check (`sizes.rs`).
//!
//! Besides the HIR walk of `walk.rs`, the passes that need what HIR does not keep,
//! the types as written with their spans and the names as written, walk a body's
//! AST with [`walk_body_ast`]: there is no general AST visitor (plan 0.1).

pub(crate) mod deferred;
pub(crate) mod matches;
pub(crate) mod positions;
pub(crate) mod sizes;
pub(crate) mod unsafety;
pub(crate) mod views;

pub(crate) mod walk;

pub(crate) use walk::for_each_expr;

use enrang_syntax::ast;

use crate::lower::BodyAst;

/// A node of a body's AST that a pass looks at.
#[derive(Copy, Clone)]
pub(crate) enum AstNode<'a> {
    /// A `let` or `const`, a `for` loop's included.
    VarDecl(&'a ast::VarDecl),
    /// Every expression, parents before children.
    Expr(&'a ast::Expr),
    /// An arrow, before its body.
    Arrow(&'a ast::ArrowFn),
}

/// Calls `f` on the nodes of `body` in source order: parameter defaults, then the
/// statements. A local function's body is its own body, so it is not entered; a
/// parameter's type is the signature's, which `positions::check_decls` reads.
pub(crate) fn walk_body_ast<'a>(body: BodyAst<'a>, f: &mut dyn FnMut(AstNode<'a>)) {
    match body {
        BodyAst::Function(d) => {
            params(&d.params, f);
            block(&d.body, f);
        }
        BodyAst::Method(m) => {
            params(&m.params, f);
            if let Some(b) = &m.body {
                block(b, f);
            }
        }
        BodyAst::Ctor(c) => {
            for p in &c.params {
                if let Some(d) = &p.default {
                    expr(d, f);
                }
            }
            block(&c.body, f);
        }
        BodyAst::Dtor(d) => block(&d.body, f),
        BodyAst::Statements(stmts) => stmts.iter().for_each(|s| stmt(s, f)),
        BodyAst::Const(e) => expr(e, f),
        BodyAst::Test(a) => arrow(a, f),
    }
}

fn params<'a>(ps: &'a [ast::Param], f: &mut dyn FnMut(AstNode<'a>)) {
    for p in ps {
        if let Some(d) = &p.default {
            expr(d, f);
        }
    }
}

fn block<'a>(b: &'a ast::Block, f: &mut dyn FnMut(AstNode<'a>)) {
    b.stmts.iter().for_each(|s| stmt(s, f));
}

fn var_decl<'a>(d: &'a ast::VarDecl, f: &mut dyn FnMut(AstNode<'a>)) {
    f(AstNode::VarDecl(d));
    if let Some(init) = &d.init {
        expr(init, f);
    }
}

fn if_stmt<'a>(i: &'a ast::IfStmt, f: &mut dyn FnMut(AstNode<'a>)) {
    expr(&i.cond, f);
    block(&i.then_block, f);
    match &i.else_branch {
        Some(ast::ElseBranch::If(next)) => if_stmt(next, f),
        Some(ast::ElseBranch::Block(b)) => block(b, f),
        None => {}
    }
}

fn stmt<'a>(s: &'a ast::Stmt, f: &mut dyn FnMut(AstNode<'a>)) {
    match &s.kind {
        ast::StmtKind::VarDecl(d) => var_decl(d, f),
        ast::StmtKind::If(i) => if_stmt(i, f),
        ast::StmtKind::While(w) | ast::StmtKind::DoWhile(w) => {
            expr(&w.cond, f);
            block(&w.body, f);
        }
        ast::StmtKind::For(fs) => {
            match &fs.init {
                Some(ast::ForInit::VarDecl(d)) => var_decl(d, f),
                Some(ast::ForInit::Expr(e)) => expr(e, f),
                None => {}
            }
            if let Some(c) = &fs.cond {
                expr(c, f);
            }
            if let Some(e) = &fs.step {
                expr(e, f);
            }
            block(&fs.body, f);
        }
        ast::StmtKind::ForOf(fo) => {
            match &fo.source {
                ast::ForOfSource::Range(lo, hi) => {
                    expr(lo, f);
                    expr(hi, f);
                }
                ast::ForOfSource::Expr(e) => expr(e, f),
            }
            block(&fo.body, f);
        }
        ast::StmtKind::Return(e) => {
            if let Some(e) = e {
                expr(e, f);
            }
        }
        ast::StmtKind::Break(_) | ast::StmtKind::Continue(_) | ast::StmtKind::LocalFn { .. } => {}
        ast::StmtKind::Block(b) | ast::StmtKind::Unsafe(b) => block(b, f),
        ast::StmtKind::Labeled(_, inner) => stmt(inner, f),
        ast::StmtKind::Expr(e) => expr(e, f),
        ast::StmtKind::Expect(x) => {
            expr(&x.actual, f);
            for arg in &x.args {
                match arg {
                    ast::MatcherArg::Expr(e) => expr(e, f),
                    ast::MatcherArg::Arm(v) => arm_value(v, f),
                }
            }
        }
        ast::StmtKind::Assert { cond, .. } => expr(cond, f),
    }
}

fn arm_value<'a>(v: &'a ast::ArmValue, f: &mut dyn FnMut(AstNode<'a>)) {
    match v {
        ast::ArmValue::Value(e) => expr(e, f),
        ast::ArmValue::Range(lo, hi) => {
            expr(lo, f);
            expr(hi, f);
        }
        ast::ArmValue::Null(_)
        | ast::ArmValue::Case(_)
        | ast::ArmValue::Ok(_)
        | ast::ArmValue::Err(_) => {}
    }
}

fn arrow<'a>(a: &'a ast::ArrowFn, f: &mut dyn FnMut(AstNode<'a>)) {
    f(AstNode::Arrow(a));
    match &a.body {
        ast::ArrowBody::Expr(e) => expr(e, f),
        ast::ArrowBody::Block(b) => block(b, f),
    }
}

fn fields<'a>(fs: &'a [ast::FieldInit], f: &mut dyn FnMut(AstNode<'a>)) {
    for field in fs {
        if let Some(v) = &field.value {
            expr(v, f);
        }
    }
}

fn expr<'a>(e: &'a ast::Expr, f: &mut dyn FnMut(AstNode<'a>)) {
    f(AstNode::Expr(e));
    match &e.kind {
        ast::ExprKind::Int { .. }
        | ast::ExprKind::Float(_)
        | ast::ExprKind::Str(_)
        | ast::ExprKind::RawTemplate(_)
        | ast::ExprKind::Bool(_)
        | ast::ExprKind::Null
        | ast::ExprKind::Ident(_)
        | ast::ExprKind::This
        | ast::ExprKind::Super
        | ast::ExprKind::TypeMember { .. }
        | ast::ExprKind::SizeForm(_)
        | ast::ExprKind::Error => {}
        ast::ExprKind::Template(parts) => {
            for part in parts {
                if let ast::TplPart::Expr(e) = part {
                    expr(e, f);
                }
            }
        }
        ast::ExprKind::Paren(inner)
        | ast::ExprKind::Unary(_, inner)
        | ast::ExprKind::Borrow(inner)
        | ast::ExprKind::Deref(inner)
        | ast::ExprKind::VoidOp(inner)
        | ast::ExprKind::Cast(inner, _)
        | ast::ExprKind::Try(inner)
        | ast::ExprKind::NonNull(inner) => expr(inner, f),
        ast::ExprKind::Member { base, .. } => expr(base, f),
        ast::ExprKind::IncDec { target, .. } => expr(target, f),
        ast::ExprKind::Array(elems) => {
            for elem in elems {
                match elem {
                    ast::ArrayElem::Item(e) | ast::ArrayElem::Spread { expr: e, .. } => expr(e, f),
                }
            }
        }
        ast::ExprKind::Repeat(a, b)
        | ast::ExprKind::Binary(_, a, b)
        | ast::ExprKind::Logical(_, a, b)
        | ast::ExprKind::Coalesce(a, b)
        | ast::ExprKind::Index(a, b)
        | ast::ExprKind::Assign {
            target: a,
            value: b,
            ..
        } => {
            expr(a, f);
            expr(b, f);
        }
        ast::ExprKind::Ternary(a, b, c) => {
            expr(a, f);
            expr(b, f);
            expr(c, f);
        }
        ast::ExprKind::New { init, .. } => match init {
            ast::NewInit::Args(args) => args.iter().for_each(|a| expr(a, f)),
            ast::NewInit::Fields(fs) => fields(fs, f),
        },
        ast::ExprKind::CaseLit { fields: fs, .. } | ast::ExprKind::ObjectLit(fs) => fields(fs, f),
        ast::ExprKind::Match { subject, arms } => {
            expr(subject, f);
            for arm in arms {
                arm.values.iter().for_each(|v| arm_value(v, f));
                if let Some(g) = &arm.guard {
                    expr(g, f);
                }
                match &arm.body {
                    ast::ArmBody::Expr(e) => expr(e, f),
                    ast::ArmBody::Block(b) => block(b, f),
                    ast::ArmBody::Return(Some(e)) => expr(e, f),
                    ast::ArmBody::Return(None)
                    | ast::ArmBody::Break(_)
                    | ast::ArmBody::Continue(_) => {}
                }
            }
        }
        ast::ExprKind::Asm(asm) => {
            expr(&asm.template, f);
            for option in asm.options.iter().flatten() {
                match &option.kind {
                    ast::AsmOptionKind::In(regs) | ast::AsmOptionKind::Out(regs) => {
                        for reg in regs {
                            if let Some(v) = &reg.value {
                                expr(v, f);
                            }
                        }
                    }
                    ast::AsmOptionKind::Clobbers(_) => {}
                }
            }
        }
        ast::ExprKind::Call { callee, args, .. } => {
            expr(callee, f);
            args.iter().for_each(|a| expr(a, f));
        }
        ast::ExprKind::Arrow(a) => arrow(a, f),
    }
}
