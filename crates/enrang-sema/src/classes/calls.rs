//! Call rules on a finished body (plan d.16; SPEC 4.3; A:896; owner 4D).
//!
//! - `super.m()` whose target, the nearest `m` above the calling class, is
//!   abstract is EN0457 at the call: `` `Shape.area` is abstract, so it has no body
//!   to call `` (S:586).
//! - A `move` method called on a receiver whose static type is a class `D`, not a
//!   type parameter or an interface, that reaches a body declared in a proper base
//!   of `D` (which `D` inherits without overriding it; `this.m()` included, and
//!   through `Box` auto-deref), is EN0458 at the call, labelled `` `Dog` inherits
//!   `into` from `Animal` `` with the help `` override `into` in `Dog` ``; and so is
//!   every `super.m()` whose target is a `move` method, with the helper help of
//!   A:896 when the target's body returns one field of `this` (S:605).

use enrang_diag::{Code, Diagnostic, Help};
use enrang_hir::{
    AdtId, Body, BodyOwner, Callee, DefId, Expr, ExprKind, FnRef, OptMember, Receiver, Tcx, Ty,
    TyKind,
};
use enrang_syntax::ast;

use crate::cx::Sema;
use crate::lower::BodyAst;
use crate::passes::for_each_expr;

pub(crate) fn check(sema: &mut Sema, b: &Body) {
    let tcx = &*sema.tcx;
    let mut diags = Vec::new();
    for_each_expr(b, &mut |e| {
        let (callee, receiver) = match &e.kind {
            ExprKind::Call {
                callee, receiver, ..
            } => (callee, receiver.as_deref()),
            ExprKind::OptionalChain(chain) => match &chain.member {
                OptMember::Call { callee, .. } => (callee, Some(&chain.base)),
                OptMember::Field(_) => return,
            },
            _ => return,
        };
        match callee {
            Callee::Super(FnRef { def, .. }) => {
                if let Some(diag) = super_call(sema, b, e, *def) {
                    diags.push(diag);
                }
            }
            Callee::Fn(FnRef { def, .. }) => {
                if let Some(r) = receiver
                    && let Some(diag) = inherited_move(tcx, e, r, *def)
                {
                    diags.push(diag);
                }
            }
            _ => {}
        }
    });
    for diag in diags {
        sema.emit(diag);
    }
}

/// The class that declares method `def`.
fn class_of(tcx: &Tcx, def: DefId) -> Option<AdtId> {
    let adt = tcx.adt_of(tcx.def(def).parent?)?;
    tcx.adt(adt).is_class().then_some(adt)
}

fn is_move(tcx: &Tcx, def: DefId) -> bool {
    tcx.sig_opt(def)
        .is_some_and(|s| s.receiver == Some(Receiver::Move))
}

/// The class a receiver's static type names, through references, nullables and
/// `Box` (S:605: the receiver's static type); `None` for anything else, a type
/// parameter or an interface included.
fn static_class(tcx: &Tcx, t: Ty) -> Option<AdtId> {
    match tcx.kind(t) {
        TyKind::Ref(inner) | TyKind::Boxed(inner) | TyKind::Nullable(inner) => {
            static_class(tcx, inner)
        }
        TyKind::Adt(adt, _) if tcx.adt(adt).is_class() => Some(adt),
        _ => None,
    }
}

/// Whether `base` is a proper base of class `class`.
fn inherits_from(tcx: &Tcx, class: AdtId, base: AdtId) -> bool {
    let mut seen = vec![class];
    let mut at = class;
    while let Some(b) = tcx.adt(at).as_class().and_then(|c| c.base) {
        let TyKind::Adt(adt, _) = tcx.kind(b) else {
            return false;
        };
        if adt == base {
            return true;
        }
        if seen.contains(&adt) {
            return false;
        }
        seen.push(adt);
        at = adt;
    }
    false
}

/// EN0458 for `recv.m()` with `m` a `move` method declared above `recv`'s class.
fn inherited_move(tcx: &Tcx, call: &Expr, receiver: &Expr, def: DefId) -> Option<Diagnostic> {
    if !is_move(tcx, def) {
        return None;
    }
    let declared = class_of(tcx, def)?;
    let static_ty = static_class(tcx, receiver.ty)?;
    // A method of `Box` itself (`unbox`) is no inherited one of the boxed class.
    if !inherits_from(tcx, static_ty, declared) {
        return None;
    }
    let (d, a) = (tcx.adt(static_ty).name, tcx.adt(declared).name);
    let m = tcx.def(def).name()?;
    Some(
        Diagnostic::new(
            Code::EN0458,
            "`move` method not declared in the receiver's class",
            call.span,
            format!("`{d}` inherits `{m}` from `{a}`"),
        )
        .with_help(Help::text(format!("override `{m}` in `{d}`"))),
    )
}

/// EN0457 or EN0458 for `super.m()` reaching method `def`.
fn super_call(sema: &Sema, b: &Body, call: &Expr, def: DefId) -> Option<Diagnostic> {
    let tcx = &*sema.tcx;
    let data = tcx.def(def);
    let m = data.name()?;
    let declared = class_of(tcx, def)?;
    let owner = tcx.adt(declared).name;
    if data.flags.is_abstract {
        let calling = match b.owner {
            BodyOwner::Fn(f) => tcx
                .def(f)
                .parent
                .and_then(|p| tcx.adt_of(p))
                .map(|a| tcx.adt(a).name),
            _ => None,
        };
        let label = match calling {
            Some(c) => format!("the nearest `{m}` above `{c}` is abstract"),
            None => format!("`{owner}.{m}` is abstract"),
        };
        return Some(Diagnostic::new(
            Code::EN0457,
            format!("`{owner}.{m}` is abstract, so it has no body to call"),
            call.span,
            label,
        ));
    }
    if !is_move(tcx, def) {
        return None;
    }
    let help = match helper(sema, def) {
        Some(helper) => format!("move the state out with a helper the base shares, `{helper}`"),
        None => "move the state out with a helper the base shares: a `protected` method that is not `move` and takes it with `mem.replace`".to_owned(),
    };
    Some(
        Diagnostic::new(
            Code::EN0458,
            "`move` method not declared in the receiver's class",
            call.span,
            format!("`{m}` is a `move` method of `{owner}`"),
        )
        .with_help(Help::text(help)),
    )
}

/// A:896's helper for a `move` method whose body is `return this.f;` with `f` of a
/// type that has a literal default: `` protected takeF(): T { return
/// mem.replace(&this.f, d); } ``.
fn helper(sema: &Sema, def: DefId) -> Option<String> {
    let Some(BodyAst::Method(m)) = sema.decls.body_ast(BodyOwner::Fn(def)) else {
        return None;
    };
    let [stmt] = m.body.as_ref()?.stmts.as_slice() else {
        return None;
    };
    let ast::StmtKind::Return(Some(value)) = &stmt.kind else {
        return None;
    };
    let ast::ExprKind::Member {
        base,
        name,
        optional: false,
    } = &value.kind
    else {
        return None;
    };
    if !matches!(base.kind, ast::ExprKind::This) {
        return None;
    }
    let tcx = &*sema.tcx;
    let class = tcx.adt(class_of(tcx, def)?).as_class()?;
    let (_, field) = class.field_named(name.name)?;
    let default = match tcx.kind(field.ty) {
        TyKind::Array(_) => "[]",
        TyKind::Str => "\"\"",
        TyKind::Int(_) | TyKind::Float(_) => "0",
        TyKind::Bool => "false",
        TyKind::Nullable(_) => "null",
        _ => return None,
    };
    let field_name = name.name.as_str();
    let mut chars = field_name.chars();
    let first = chars.next()?.to_uppercase().collect::<String>();
    Some(format!(
        "protected take{first}{}(): {} {{ return mem.replace(&this.{field_name}, {default}); }}",
        chars.as_str(),
        tcx.ty_string(field.ty)
    ))
}
