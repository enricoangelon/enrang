//! Deferred features in expressions (plan d.17; SPEC 16 S:3455-3482; owner 4E):
//! `Worker` and `spawn` (EN1003), `Math` (EN1026), `JSON` (EN1027), `fetch` and
//! `WebSocket` (EN1028), `Object` and `Reflect` (EN1029), `union` and `transmute`
//! (EN1033), each when the name resolves to nothing else (plan choice: a program's
//! own `Math` wins), with SPEC 16's message, note and help (`suggest::deferred`).
//!
//! Typing reports such a name where it resolves a path (`Math.floor(x)`,
//! `spawn(f)`, `JSON` alone) and lowering where it resolves a type (`const m:
//! Math`), both through `suggest::unresolved`. This pass walks the body's AST once
//! more for the places neither reaches, the class of a `new` (`new Worker()`, `new
//! WebSocket(url)`), and for every name in an expression, so that no deferred name
//! in an expression goes unreported whatever path typing took; a name already
//! reported at the same place is not reported twice (`DiagCtx` keeps the first
//! diagnostic per code and span). A name some local of the body declares is left
//! alone.

use std::collections::BTreeSet;

use enrang_hir::{Body, BodyOwner, Res};
use enrang_syntax::ast::{self, Ident};

use crate::cx::Sema;
use crate::passes::{AstNode, walk_body_ast};
use crate::resolve::scope;
use crate::resolve::suggest::{deferred, deferred_code};

/// Reports the deferred names of `b`'s expressions.
pub(crate) fn check(sema: &mut Sema, b: &Body) {
    let module = match b.owner {
        BodyOwner::Statements(m) => m,
        BodyOwner::Fn(d) | BodyOwner::Const(d) | BodyOwner::Test(d) => sema.tcx.def(d).module,
    };
    if sema.tcx.module(module).library {
        return;
    }
    let (Some(ast_body), Some(at)) = (sema.decls.body_ast(b.owner), sema.decls.scope_of(b.owner))
    else {
        return;
    };
    let locals: BTreeSet<&str> = b
        .locals
        .iter()
        .filter_map(|l| l.name.map(|n| n.as_str()))
        .collect();
    // The names to check, in source order: whether each is a type (`new X`).
    let mut names: Vec<(Ident, bool)> = Vec::new();
    walk_body_ast(ast_body, &mut |node| {
        let AstNode::Expr(e) = node else {
            return;
        };
        match &e.kind {
            ast::ExprKind::Ident(name) => names.push((
                Ident {
                    name: *name,
                    span: e.span,
                },
                false,
            )),
            ast::ExprKind::New { ty, .. } => {
                if let ast::TypeExprKind::Named { path, .. } = &ty.kind
                    && let [name] = path.as_slice()
                {
                    names.push((*name, true));
                }
            }
            _ => {}
        }
    });
    for (name, is_type) in names {
        let Some(code) = deferred_code(name.name.as_str()) else {
            continue;
        };
        if locals.contains(name.name.as_str()) {
            continue;
        }
        let res = if is_type {
            scope::lookup_type(sema, at, &[name])
        } else {
            scope::lookup_value(sema, at, name)
        };
        if matches!(res, Res::Err) && !sema.res.import_failed(at, name.name) {
            sema.emit(deferred(code, name.span));
        }
    }
}
