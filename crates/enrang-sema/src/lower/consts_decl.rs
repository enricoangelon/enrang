//! The types of top-level constants and `unsafe let` statics (plan c.1; SPEC 4.9).
//!
//! A constant's annotation may be omitted when its initialiser decides the type
//! (S:756); then its type is the typed initialiser's, set once its body is typed.
//! Const eval (2E, 4F) evaluates the initialisers.
//!
//! EN0802 (S:758, T:865): an `unsafe let` of `void`, or holding a reference, a
//! `string`, a `T[]`, a `Box` or a class with a destructor; with no initialiser, a
//! type that is not zeroable (integers, floats, `bool`, raw pointers, fixed arrays
//! and `final` classes with no base of those), a class that can be extended getting
//! the helps `` write `public final class Stats` `` and `` or give it a value:
//! `= new Stats {}` ``; and under `@at`, which the compiler never fills, a class that
//! carries a hidden pointer, whatever the initialiser.

use std::collections::BTreeSet;

use enrang_diag::{Code, Diagnostic, Help};
use enrang_hir::{AdtId, AdtKind, ClassModifier, DefId, Tcx, Ty, TyKind, Vis};

use crate::cx::Sema;
use crate::lower::types::lower_ty;
use crate::lower::{ItemAst, ItemAstKind};
use crate::resolve::ScopeAt;

pub(crate) fn lower(sema: &mut Sema, item: &ItemAst) {
    let at = ScopeAt {
        owner: Some(item.def),
        ..ScopeAt::module(item.module, item.test_part)
    };
    match &item.kind {
        ItemAstKind::Const(c) => {
            sema.decls.scopes.insert(item.def, at);
            if let Some(t) = &c.ty {
                let ty = lower_ty(sema, at, t);
                sema.tcx.set_item_ty(item.def, ty);
            }
        }
        ItemAstKind::Static(u) => {
            sema.decls.scopes.insert(item.def, at);
            let ty = lower_ty(sema, at, &u.ty);
            sema.tcx.set_item_ty(item.def, ty);
            check_static(sema, item.def, u, ty);
        }
        ItemAstKind::StaticAssert | ItemAstKind::Test => {
            sema.decls.scopes.insert(item.def, at);
        }
        _ => {}
    }
}

/// Why a part of a static's type is refused.
enum Refused {
    Void,
    Reference(Ty),
    Heap(Ty),
    Destructor(Ty),
    /// A class that carries a hidden pointer, which zero would leave null.
    Extendable(AdtId),
    NotZeroable(Ty),
}

/// EN0802 for the `unsafe let` `def` of type `ty`.
fn check_static(sema: &mut Sema, def: DefId, u: &enrang_syntax::ast::UnsafeLet, ty: Ty) {
    let tcx = &*sema.tcx;
    if tcx.references_error(ty) {
        return;
    }
    let at = tcx.def(def).attrs.at.is_some();
    let refused = if tcx.kind(ty) == TyKind::Void {
        Some(Refused::Void)
    } else {
        held(tcx, ty, &mut BTreeSet::new()).or_else(|| {
            if u.value.is_none() {
                not_zeroable(tcx, ty, &mut BTreeSet::new())
            } else if at {
                extendable_inline(tcx, ty)
            } else {
                None
            }
        })
    };
    let Some(refused) = refused else { return };
    let shown = tcx.ty_string(ty);
    let message = if tcx.kind(ty) == TyKind::Void {
        "an `unsafe let` can't hold `void`".to_owned()
    } else {
        format!(
            "an `unsafe let` can't hold {}",
            crate::classes::sig::a_ty(&shown)
        )
    };
    let mut helps = Vec::new();
    let label = match refused {
        Refused::Void => "`void` holds nothing".to_owned(),
        Refused::Reference(t) => format!("`{}` is a reference", tcx.ty_string(t)),
        Refused::Heap(t) => format!("`{}` owns heap memory", tcx.ty_string(t)),
        Refused::Destructor(t) => format!("`{}` has a destructor", tcx.ty_string(t)),
        Refused::Extendable(adt) => {
            let name = tcx.adt(adt).name;
            let class = tcx.adt(adt).as_class().expect("a class");
            if class.modifier != ClassModifier::Final {
                let vis = match tcx.def(tcx.adt(adt).def).vis {
                    Vis::Private => "private",
                    _ => "public",
                };
                helps.push(format!("write `{vis} final class {name}`"));
                helps.push(format!("or give it a value: `= new {name} {{}}`"));
            } else {
                helps.push(format!("give it a value: `= new {name} {{}}`"));
            }
            format!(
                "`{name}` can be extended, so it carries a hidden pointer that zero would leave null"
            )
        }
        Refused::NotZeroable(t) => {
            helps.push("give it a value".to_owned());
            format!("`{}` has no all-zero value", tcx.ty_string(t))
        }
    };
    let mut diag = Diagnostic::new(Code::EN0802, message, u.ty.span, label);
    for help in helps {
        diag = diag.with_help(Help::text(help));
    }
    sema.emit(diag);
}

/// The first part of `ty` an `unsafe let` may never hold: a reference, heap memory
/// or a destructor.
fn held(tcx: &Tcx, ty: Ty, visiting: &mut BTreeSet<AdtId>) -> Option<Refused> {
    match tcx.kind(ty) {
        TyKind::Ref(_) | TyKind::Slice(_) => Some(Refused::Reference(ty)),
        TyKind::Str | TyKind::Array(_) | TyKind::Boxed(_) => Some(Refused::Heap(ty)),
        TyKind::Fixed(inner, _) | TyKind::Nullable(inner) => held(tcx, inner, visiting),
        TyKind::Tuple(parts) => tcx.list(parts).iter().find_map(|&p| held(tcx, p, visiting)),
        TyKind::Object(shape) => tcx
            .shape(shape)
            .fields
            .iter()
            .find_map(|&(_, f)| held(tcx, f, visiting)),
        TyKind::Adt(adt, args) => {
            if !visiting.insert(adt) {
                return None;
            }
            match &tcx.adt(adt).kind {
                AdtKind::Class(_) if tcx.class_dtor(adt, args).is_some() => {
                    Some(Refused::Destructor(ty))
                }
                AdtKind::Class(_) | AdtKind::Enum(_) => tcx
                    .adt_field_tys(adt, args)
                    .into_iter()
                    .find_map(|f| held(tcx, f, visiting)),
                AdtKind::Interface(_) => None,
            }
        }
        _ => None,
    }
}

/// The first part of `ty` that is not zeroable (S:758).
fn not_zeroable(tcx: &Tcx, ty: Ty, visiting: &mut BTreeSet<AdtId>) -> Option<Refused> {
    match tcx.kind(ty) {
        TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Raw(_) | TyKind::Error => None,
        TyKind::Fixed(inner, _) => not_zeroable(tcx, inner, visiting),
        TyKind::Adt(adt, args) => match tcx.adt(adt).as_class() {
            Some(class) if class.hidden_table => Some(Refused::Extendable(adt)),
            Some(_) => {
                if !visiting.insert(adt) {
                    return None;
                }
                tcx.adt_field_tys(adt, args)
                    .into_iter()
                    .find_map(|f| not_zeroable(tcx, f, visiting))
            }
            None => Some(Refused::NotZeroable(ty)),
        },
        _ => Some(Refused::NotZeroable(ty)),
    }
}

/// A class carrying a hidden pointer that `ty` holds inline.
fn extendable_inline(tcx: &Tcx, ty: Ty) -> Option<Refused> {
    match tcx.kind(ty) {
        TyKind::Adt(adt, _) => match tcx.adt(adt).as_class() {
            Some(class) if class.hidden_table => Some(Refused::Extendable(adt)),
            _ => None,
        },
        TyKind::Fixed(inner, _) => extendable_inline(tcx, inner),
        _ => None,
    }
}
