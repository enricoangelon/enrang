//! A class's field initialisers (D6, `hir::FieldInits`; SPEC 4.3 S:581-585; owner
//! 4D): each `= e` of a field the class declares, and each override's new
//! default, typed at the field's type as an initialiser at an annotation
//! (`Site::Init`, plan choice: the coercion is the same as at `Site::Field`, and
//! only an initialiser's site names its annotation as EN0401's secondary).
//!
//! All the initialisers of one class are typed in one `FnCtxt`, so their
//! expression ids are unique within the class's `FieldInits`. Its owner is
//! `BodyOwner::Const` of the class, the class-level body that is no function, where
//! `this` types as `Error` with no report: `this` in a field initialiser is EN0610,
//! phase 3's (plan e, EN0219's row). The end of typing is `FnCtxt::finish`, as for
//! any body: defaults, the integer divisions, the deferred checks in order, then
//! every type resolved. The passes that run on each finished body
//! (exhaustiveness, these call rules, the five powers, positions, deferred names)
//! run on the initialisers too. An
//! override that does not match its inherited field (EN0443) is typed at its own
//! written type, so the mismatch is reported once.

use enrang_base::Span;
use enrang_hir::{self as hir, BodyOwner, FieldIdx, FieldInits, Vis};
use enrang_syntax::ast;

use crate::classes::members::ClassAst;
use crate::cx::Sema;
use crate::lower::types::{lower_ty, optional};
use crate::typeck::{Expect, FnCtxt, Site};

/// The field each written initialiser of `cx` sets: the order lowering pushes a
/// class's own fields in (fields and parameter properties in member order), an
/// `override` naming a visible inherited field taking that field's index.
fn slots(sema: &Sema, cx: &ClassAst) -> Vec<(FieldIdx, bool, usize)> {
    let Some(class) = sema.tcx.adt(cx.adt).as_class() else {
        return Vec::new();
    };
    let own_from = class.own_from as usize;
    let mut next = own_from;
    let mut out = Vec::new();
    for (i, member) in cx.decl.members.iter().enumerate() {
        match &member.kind {
            ast::ClassMemberKind::Field(f) => {
                let inherited = class.fields[..own_from]
                    .iter()
                    .position(|old| old.name == f.name.name && old.vis != Vis::Private);
                match (f.is_override, inherited) {
                    (true, Some(j)) => out.push((FieldIdx(j as u32), true, i)),
                    _ => {
                        out.push((FieldIdx(next as u32), false, i));
                        next += 1;
                    }
                }
            }
            ast::ClassMemberKind::Constructor(c) => {
                next += c.params.iter().filter(|p| p.property.is_some()).count();
            }
            _ => {}
        }
    }
    out
}

/// Types the written initialisers of class `cx` into `sema.field_inits`.
pub(crate) fn check(sema: &mut Sema, cx: &ClassAst) {
    let Some(at) = sema.decls.scopes.get(&cx.def).copied() else {
        return;
    };
    let mut todo: Vec<(FieldIdx, hir::Ty, &ast::Expr, Span)> = Vec::new();
    for (field, is_override, member) in slots(sema, cx) {
        let ast::ClassMemberKind::Field(f) = &cx.decl.members[member].kind else {
            continue;
        };
        let Some(value) = &f.default else {
            continue;
        };
        let ty = match is_override {
            false => match sema.tcx.adt(cx.adt).as_class() {
                Some(class) if field.0 as usize >= class.fields.len() => continue,
                Some(class) => class.fields[field.0 as usize].ty,
                None => continue,
            },
            // As written: equal to the inherited field's type unless EN0443 says
            // otherwise.
            true => {
                let lowered = lower_ty(sema, at, &f.ty);
                match f.optional {
                    true => optional(sema, lowered),
                    false => lowered,
                }
            }
        };
        todo.push((field, ty, value, f.ty.span));
    }
    if todo.is_empty() {
        return;
    }
    let owner = BodyOwner::Const(cx.def);
    let span = cx.decl.span;
    let void = sema.tcx.common().void;
    let mut fcx = FnCtxt::new(sema, owner, at, void);
    fcx.scopes.push();
    let mut stmts = Vec::new();
    let mut fields = Vec::new();
    let values: Vec<&ast::Expr> = todo.iter().map(|&(_, _, value, _)| value).collect();
    for (field, ty, value, annotation) in todo {
        fcx.init_annotation = Some((value.span, annotation));
        let e = fcx.check_expr(value, Expect::Coerce(ty, Site::Init));
        fcx.init_annotation = None;
        stmts.push(hir::Stmt {
            span: value.span,
            kind: hir::StmtKind::Expr(e),
        });
        fields.push(field);
    }
    let mut this_spans = std::mem::take(&mut fcx.this_spans);
    this_spans.sort();
    this_spans.dedup();
    let body = fcx.finish(hir::Block { stmts, span }, span);
    crate::passes::matches::check(sema, &body);
    crate::classes::calls::check(sema, &body);
    crate::passes::unsafety::check(sema, &body);
    crate::passes::positions::check_field_inits(sema, &body, &values);
    crate::passes::deferred::check(sema, &body);
    let body = std::sync::Arc::new(body);
    sema.field_init_bodies
        .insert(cx.adt, std::sync::Arc::clone(&body));
    let inits = fields
        .into_iter()
        .zip(body.root.stmts.iter().cloned())
        .filter_map(|(field, stmt)| match stmt.kind {
            hir::StmtKind::Expr(e) => Some((field, e)),
            _ => None,
        })
        .collect();
    sema.field_inits.insert(
        cx.adt,
        FieldInits {
            adt: cx.adt,
            inits,
            this_spans,
        },
    );
}
