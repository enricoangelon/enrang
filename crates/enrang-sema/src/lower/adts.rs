//! Classes, enums and interfaces (plan c.1-c.2, d.4; SPEC 4.3, 4.4): headers
//! (generics, an interface's `Self`), then bounds, bases and `implements`, then
//! fields, flattened with the base's first, and enum cases.
//!
//! A class's fields come after its base's, with the base's field types at the
//! arguments the class gives its base, so a `FieldIdx` names one field in the whole
//! chain (A:896); an `override` field adds no `FieldDef` but an `overrides` entry for
//! the inherited index. A constructor parameter with a visibility is a field too,
//! placed where the constructor is (SPEC 4.3). A class has a hidden table pointer
//! unless it is `final` and its base has none (SPEC 11).
//!
//! Codes: a class or enum holding itself inline, through fields, cases, tuples,
//! fixed arrays, objects or `T | null`, with no `Box` or `T[]` between, is EN0408,
//! once per cycle, at the first field that starts it, with the fix-it `Box<Node> |
//! null` (S:603); an enum whose `=` values mix numbers and texts EN0456 at the first
//! value of the second kind (S:591); an `extends` that names no class EN0401 (plan
//! choice), and so is one that makes a class its own base, through any number of
//! classes. A case value that is no literal is const eval's (2E, 4F); EN0442-EN0444
//! and the rest of d.16 are the classes stage's (4D).

use std::collections::BTreeSet;

use enrang_base::{Idx, Span, intern};
use enrang_diag::{Code, Diagnostic, Edit, Help};
use enrang_hir::{
    AdtId, AdtKind, Bound, EnumValues, FieldDef, FieldIdx, Implicit, LangItem, Ty, TyKind,
    TyParamDef, VariantValue, Vis,
};
use enrang_syntax::ast;

use crate::cx::Sema;
use crate::lower::sigs::{define_type_params, lower_bounds};
use crate::lower::types::{lower_ty, optional};
use crate::lower::{ItemAst, ItemAstKind};
use crate::resolve::ScopeAt;

/// Generics of ADTs and `extend` blocks, an interface's `Self`, and their scopes.
pub(crate) fn header(sema: &mut Sema, item: &ItemAst) {
    let base = ScopeAt::module(item.module, item.test_part);
    let (adt, params) = match &item.kind {
        ItemAstKind::Class(adt, c, _) => (Some(*adt), &c.type_params),
        ItemAstKind::Enum(adt, e, _) => (Some(*adt), &e.type_params),
        ItemAstKind::Interface(adt, i, _) => (Some(*adt), &i.type_params),
        ItemAstKind::Extend(x, _) => (None, &x.type_params),
        ItemAstKind::StrUnion => {
            sema.decls.scopes.insert(item.def, base);
            return;
        }
        _ => return,
    };
    let generics = define_type_params(sema, item.def, None, params);
    let mut at = ScopeAt {
        generics: Some(generics),
        ..base
    };
    if let Some(adt) = adt {
        sema.tcx.adt_mut(adt).generics = generics;
        match &sema.tcx.adt(adt).kind {
            AdtKind::Class(_) => at.class = Some(adt),
            AdtKind::Interface(_) => {
                let args = sema.tcx.identity_args(generics);
                let bound = sema.tcx.define_bound(Bound::Iface { adt, args });
                let self_param = sema.tcx.define_param(TyParamDef {
                    name: intern("Self"),
                    owner: item.def,
                    index: 0,
                    bounds: vec![bound],
                    implicit: Some(Implicit::Interface(adt)),
                    span: Span::DUMMY,
                });
                if let AdtKind::Interface(iface) = &mut sema.tcx.adt_mut(adt).kind {
                    iface.self_param = self_param;
                }
                at.self_param = Some(self_param);
            }
            AdtKind::Enum(_) => {}
        }
    }
    sema.decls.scopes.insert(item.def, at);
}

/// Bounds of ADT and `extend` parameters; a class's base and `implements`.
pub(crate) fn bounds(sema: &mut Sema, item: &ItemAst) {
    let params = match &item.kind {
        ItemAstKind::Class(_, c, _) => &c.type_params,
        ItemAstKind::Enum(_, e, _) => &e.type_params,
        ItemAstKind::Interface(_, i, _) => &i.type_params,
        ItemAstKind::Extend(x, _) => &x.type_params,
        _ => return,
    };
    let at = sema.decls.scopes[&item.def];
    let generics = at.generics.expect("a header defined the generics");
    lower_bounds(sema, at, generics, params);
    let ItemAstKind::Class(adt, c, _) = &item.kind else {
        return;
    };
    // A base that names no class was reported here, so what the class would
    // inherit is unknown and its uses stay silent (`ClassTables::unknown_base`).
    let base = match &c.extends {
        Some(t) => {
            let ty = lower_ty(sema, at, t);
            match sema.tcx.kind(ty) {
                TyKind::Adt(a, _) if sema.tcx.adt(a).is_class() => Some(ty),
                TyKind::Error => {
                    sema.classes.unknown_base.insert(*adt);
                    None
                }
                _ => {
                    let shown = sema.tcx.ty_string(ty);
                    sema.err(
                        Code::EN0401,
                        format!("mismatched types: expected a class, found `{shown}`"),
                        t.span,
                        "`extends` takes a class",
                    );
                    sema.classes.unknown_base.insert(*adt);
                    None
                }
            }
        }
        None => None,
    };
    let implements: Vec<_> = c.implements.iter().map(|t| lower_ty(sema, at, t)).collect();
    let copy = sema.tcx.lang_adt(LangItem::Copy);
    let is_copy = implements
        .iter()
        .any(|&t| matches!(sema.tcx.kind(t), TyKind::Adt(a, _) if Some(a) == copy));
    if let AdtKind::Class(class) = &mut sema.tcx.adt_mut(*adt).kind {
        class.base = base;
        class.implements = implements;
        class.copy = is_copy;
    }
}

/// EN0401 for a class whose `extends` chain comes back to it (plan choice: no
/// document names a code). Classes are visited in collection order, and the first
/// one found on a cycle is reported at its `extends` type and loses its base, so the
/// cycle is reported once and every later walk up a base chain ends.
pub(crate) fn base_cycles(sema: &mut Sema, items: &[ItemAst]) {
    let base_of = |sema: &Sema, adt: AdtId| -> Option<AdtId> {
        let base = sema.tcx.adt(adt).as_class()?.base?;
        match sema.tcx.kind(base) {
            TyKind::Adt(b, _) => Some(b),
            _ => None,
        }
    };
    for item in items {
        let ItemAstKind::Class(adt, decl, _) = &item.kind else {
            continue;
        };
        let (adt, Some(written)) = (*adt, &decl.extends) else {
            continue;
        };
        let mut seen = vec![adt];
        let mut at = base_of(sema, adt);
        while let Some(next) = at {
            if next == adt {
                let name = decl.name.name;
                sema.err(
                    Code::EN0401,
                    format!("`{name}` can't extend itself"),
                    written.span,
                    format!("this makes `{name}` a base of itself"),
                );
                if let AdtKind::Class(class) = &mut sema.tcx.adt_mut(adt).kind {
                    class.base = None;
                }
                sema.classes.unknown_base.insert(adt);
                break;
            }
            if seen.contains(&next) {
                // A cycle above this class, reported at its own first class.
                break;
            }
            seen.push(next);
            at = base_of(sema, next);
        }
    }
}

/// Fields of every class (a base before its subclasses) and the cases of every
/// enum.
pub(crate) fn fields(sema: &mut Sema, items: &[ItemAst]) {
    for item in items {
        match &item.kind {
            ItemAstKind::Class(adt, _, _) => class_fields(sema, items, *adt),
            ItemAstKind::Enum(adt, e, _) => enum_cases(sema, item, *adt, e),
            _ => {}
        }
    }
}

/// The fields of every class `ty` holds by value, lowered now when their turn has
/// not come: a length that lays a class out while declarations are lowered sees
/// its whole layout, whatever the order of the declarations (SPEC 4.9 sets none).
/// `Err` names a class whose fields are being lowered, which the layout would need
/// before it is complete: a constant cycle.
pub(crate) fn ensure_fields(sema: &mut Sema, ty: Ty) -> Result<(), AdtId> {
    let mut seen = BTreeSet::new();
    ensure_fields_in(sema, ty, &mut seen)
}

fn ensure_fields_in(sema: &mut Sema, ty: Ty, seen: &mut BTreeSet<Ty>) -> Result<(), AdtId> {
    if !seen.insert(ty) || seen.len() > 4096 {
        return Ok(());
    }
    match sema.tcx.kind(ty) {
        TyKind::Fixed(e, _) | TyKind::Nullable(e) => ensure_fields_in(sema, e, seen),
        TyKind::Tuple(parts) => {
            for p in sema.tcx.list(parts).to_vec() {
                ensure_fields_in(sema, p, seen)?;
            }
            Ok(())
        }
        TyKind::Adt(adt, args) if sema.tcx.adt(adt).as_class().is_some() => {
            if sema.decls.fields_active.contains(&adt) {
                return Err(adt);
            }
            if !sema.decls.fields_done.contains(&adt) {
                let items = sema.decls.items.clone();
                class_fields(sema, &items, adt);
            }
            let count = sema.tcx.adt(adt).as_class().map_or(0, |c| c.fields.len());
            for i in 0..count {
                let field = sema.tcx.field_ty(adt, None, FieldIdx::new(i), args);
                ensure_fields_in(sema, field, seen)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

fn class_fields(sema: &mut Sema, items: &[ItemAst], adt: AdtId) {
    if sema.decls.fields_done.contains(&adt) || !sema.decls.fields_active.insert(adt) {
        return;
    }
    let Some(item) = items
        .iter()
        .find(|i| matches!(i.kind, ItemAstKind::Class(a, _, _) if a == adt))
    else {
        // A class of no item here cannot happen; nothing to lower.
        sema.decls.fields_active.remove(&adt);
        return;
    };
    let ItemAstKind::Class(_, decl, _) = &item.kind else {
        return;
    };
    let class = sema.tcx.adt(adt).as_class().cloned().expect("a class");
    let mut inherited = Vec::new();
    let mut base_hidden = false;
    if let Some(base) = class.base
        && let TyKind::Adt(base_adt, base_args) = sema.tcx.kind(base)
    {
        class_fields(sema, items, base_adt);
        let base_class = sema.tcx.adt(base_adt).as_class().cloned().expect("a class");
        base_hidden = base_class.hidden_table;
        let params = sema
            .tcx
            .generics(sema.tcx.adt(base_adt).generics)
            .params
            .clone();
        let args = sema.tcx.list(base_args);
        for field in &base_class.fields {
            let ty = sema.tcx.subst(field.ty, &params, &args);
            inherited.push(FieldDef {
                ty,
                ..field.clone()
            });
        }
    }
    let at = sema.decls.scopes[&item.def];
    let own_from = inherited.len() as u32;
    let mut fields = inherited;
    let mut overrides = Vec::new();
    for member in &decl.members {
        match &member.kind {
            ast::ClassMemberKind::Field(f) => {
                if f.is_override
                    && let Some(i) = fields[..own_from as usize]
                        .iter()
                        .position(|old| old.name == f.name.name && old.vis != Vis::Private)
                {
                    // S:585: the named form and a subclass with no constructor use
                    // the override's new default, so this class's copy of the slot
                    // (and every subclass's, which copies it) has one.
                    if f.default.is_some() {
                        fields[i].has_default = true;
                    }
                    overrides.push(FieldIdx::new(i));
                    continue;
                }
                let lowered = lower_ty(sema, at, &f.ty);
                let ty = if f.optional {
                    optional(sema, lowered)
                } else {
                    lowered
                };
                let mut field = FieldDef::new(f.name.name, ty, adt);
                field.vis = vis_of(f.visibility);
                field.readonly = f.is_readonly;
                field.readonly_refs = readonly_refs(&f.ty);
                field.has_default = f.default.is_some() || f.optional;
                field.span = member.span;
                field.optional = f.optional;
                fields.push(field);
            }
            ast::ClassMemberKind::Constructor(c) => {
                for p in c.params.iter().filter(|p| p.property.is_some()) {
                    let lowered = lower_ty(sema, at, &p.ty);
                    let ty = if p.optional {
                        optional(sema, lowered)
                    } else {
                        lowered
                    };
                    let mut field = FieldDef::new(p.name.name, ty, adt);
                    field.vis = vis_of(p.property);
                    field.readonly = p.is_readonly;
                    field.readonly_refs = readonly_refs(&p.ty);
                    field.has_default = p.default.is_some() || p.optional;
                    field.span = p.span;
                    field.optional = p.optional;
                    fields.push(field);
                }
            }
            _ => {}
        }
    }
    if let AdtKind::Class(class) = &mut sema.tcx.adt_mut(adt).kind {
        class.fields = fields;
        class.own_from = own_from;
        class.overrides = overrides;
        class.hidden_table = class.modifier != enrang_hir::ClassModifier::Final || base_hidden;
    }
    sema.decls.fields_active.remove(&adt);
    sema.decls.fields_done.insert(adt);
}

fn vis_of(v: Option<ast::Visibility>) -> Vis {
    match v {
        Some(ast::Visibility::Private) => Vis::Private,
        Some(ast::Visibility::Protected) => Vis::Protected,
        Some(ast::Visibility::Public) | None => Vis::Public,
    }
}

/// The tuple positions of each `readonly &` part of a field's type (A:326): `[]`
/// for the field itself.
fn readonly_refs(t: &ast::TypeExpr) -> Vec<Vec<u32>> {
    fn walk(t: &ast::TypeExpr, at: &mut Vec<u32>, out: &mut Vec<Vec<u32>>) {
        match &t.kind {
            ast::TypeExprKind::ReadonlyRef(_) => out.push(at.clone()),
            ast::TypeExprKind::Paren(inner) | ast::TypeExprKind::Nullable(inner) => {
                walk(inner, at, out)
            }
            ast::TypeExprKind::Tuple(parts) => {
                for (i, part) in parts.iter().enumerate() {
                    at.push(i as u32);
                    walk(part, at, out);
                    at.pop();
                }
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    walk(t, &mut Vec::new(), &mut out);
    out
}

/// An enum's case fields, and the values its cases write as literals.
fn enum_cases(sema: &mut Sema, item: &ItemAst, adt: AdtId, decl: &ast::EnumDecl) {
    let at = sema.decls.scopes[&item.def];
    let mut variants = sema
        .tcx
        .adt(adt)
        .as_enum()
        .expect("an enum")
        .variants
        .clone();
    let mut values = EnumValues::None;
    let mut first: Option<(bool, enrang_base::Span)> = None;
    let mut mixed = false;
    for (variant, written) in variants.iter_mut().zip(&decl.variants) {
        match &written.payload {
            ast::VariantPayload::Unit => {}
            ast::VariantPayload::Fields(fields) => {
                for f in fields {
                    let ty = lower_ty(sema, at, &f.ty);
                    let mut field = FieldDef::new(f.name.name, ty, adt);
                    field.span = f.name.span;
                    variant.fields.push(field);
                }
            }
            ast::VariantPayload::Value(e) => {
                // A value a length computed already (`consteval::ensure_enum`, for a
                // class above that reads this enum) is kept, never overwritten.
                variant.value = literal_value(sema, e).or(variant.value.clone());
                let text = is_text(e);
                match first {
                    None => {
                        first = Some((text, e.span));
                        values = if text {
                            EnumValues::Texts
                        } else {
                            EnumValues::Ints
                        };
                    }
                    Some((first_text, first_span)) if first_text != text && !mixed => {
                        mixed = true;
                        let (label, earlier) = if text {
                            ("a text after number values", "the first value is a number")
                        } else {
                            ("a number after text values", "the first value is a text")
                        };
                        sema.emit(
                            Diagnostic::new(
                                Code::EN0456,
                                format!("`{}` mixes number and text values", decl.name.name),
                                e.span,
                                label,
                            )
                            .with_secondary(first_span, earlier),
                        );
                    }
                    Some(_) => {}
                }
            }
        }
    }
    if let AdtKind::Enum(e) = &mut sema.tcx.adt_mut(adt).kind {
        e.variants = variants;
        e.values = values;
    }
}

/// Whether a case value is a text: only a string literal is (S:591).
fn is_text(e: &ast::Expr) -> bool {
    match &e.kind {
        ast::ExprKind::Str(_) => true,
        ast::ExprKind::Paren(inner) => is_text(inner),
        _ => false,
    }
}

/// EN0408: each class or enum that holds itself inline, once per cycle, at the
/// first field that starts it (S:603). A class's fields are the flattened list, so
/// a field it inherits counts (A:896), reported where its base declares it.
pub(crate) fn recursion(sema: &mut Sema, items: &[ItemAst]) {
    let mut reported: BTreeSet<AdtId> = BTreeSet::new();
    for item in items {
        let adt = match &item.kind {
            ItemAstKind::Class(adt, _, _) | ItemAstKind::Enum(adt, _, _) => *adt,
            _ => continue,
        };
        if reported.contains(&adt) {
            continue;
        }
        let tcx = &*sema.tcx;
        // Each field: its name, its type here, and the class or enum declaring it.
        let fields: Vec<(enrang_base::Symbol, enrang_hir::Ty, AdtId)> = match &tcx.adt(adt).kind {
            AdtKind::Class(class) => class
                .fields
                .iter()
                .map(|f| (f.name, f.ty, f.declared_in))
                .collect(),
            AdtKind::Enum(e) => e
                .variants
                .iter()
                .flat_map(|v| v.fields.iter().map(|f| (f.name, f.ty, f.declared_in)))
                .collect(),
            AdtKind::Interface(_) => continue,
        };
        let Some(index) = fields
            .iter()
            .position(|&(_, ty, _)| holds(tcx, adt, ty, &mut BTreeSet::new()))
        else {
            continue;
        };
        let (name, ty, declared_in) = fields[index];
        let found = match &item.kind {
            ItemAstKind::Class(..) => items.iter().find_map(|i| match &i.kind {
                ItemAstKind::Class(a, c, _) if *a == declared_in => class_field_spans(c)
                    .into_iter()
                    .find(|(n, _, _)| *n == name)
                    .map(|(_, a, b)| (a, b)),
                _ => None,
            }),
            ItemAstKind::Enum(_, e, _) => enum_field_spans(e).get(index).map(|&(_, a, b)| (a, b)),
            _ => None,
        };
        let Some((span, inner_span)) = found else {
            continue;
        };
        // Every class or enum of the same cycle is reported here.
        reported.insert(adt);
        let mut reach = BTreeSet::new();
        holds_any(tcx, ty, &mut reach);
        for other in reach {
            if other != adt
                && tcx
                    .adt_field_tys(other, tcx.identity_args(tcx.adt(other).generics))
                    .into_iter()
                    .any(|t| holds(tcx, adt, t, &mut BTreeSet::new()))
            {
                reported.insert(other);
            }
        }
        let name = tcx.adt(adt).name;
        let inner = sema.tcx.map().text(inner_span).to_owned();
        let fix = format!("Box<{inner}> | null");
        sema.emit(
            Diagnostic::new(
                Code::EN0408,
                format!("recursive type `{name}` needs `Box`"),
                span,
                format!(
                    "this holds {} `{name}` inline",
                    crate::classes::sig::article(name.as_str())
                ),
            )
            .with_help(Help::machine(
                format!("write `{fix}`"),
                vec![Edit::replace(span, fix.clone())],
            )),
        );
    }
}

/// Whether `ty` holds an `adt` inline: through classes' fields, enums' cases,
/// tuples, fixed arrays, objects and `T | null`, never behind a pointer.
fn holds(
    tcx: &enrang_hir::Tcx,
    adt: AdtId,
    ty: enrang_hir::Ty,
    visiting: &mut BTreeSet<AdtId>,
) -> bool {
    match tcx.kind(ty) {
        TyKind::Adt(a, args) => {
            if a == adt {
                return true;
            }
            if tcx.adt(a).is_interface() || !visiting.insert(a) {
                return false;
            }
            tcx.adt_field_tys(a, args)
                .into_iter()
                .any(|t| holds(tcx, adt, t, visiting))
        }
        TyKind::Fixed(inner, _) | TyKind::Nullable(inner) => holds(tcx, adt, inner, visiting),
        TyKind::Tuple(parts) => tcx
            .list(parts)
            .iter()
            .any(|&p| holds(tcx, adt, p, visiting)),
        TyKind::Object(shape) => tcx
            .shape(shape)
            .fields
            .iter()
            .any(|&(_, f)| holds(tcx, adt, f, visiting)),
        _ => false,
    }
}

/// Every class and enum `ty` holds inline, itself included.
fn holds_any(tcx: &enrang_hir::Tcx, ty: enrang_hir::Ty, out: &mut BTreeSet<AdtId>) {
    match tcx.kind(ty) {
        TyKind::Adt(a, args) => {
            if tcx.adt(a).is_interface() || !out.insert(a) {
                return;
            }
            for t in tcx.adt_field_tys(a, args) {
                holds_any(tcx, t, out);
            }
        }
        TyKind::Fixed(inner, _) | TyKind::Nullable(inner) => holds_any(tcx, inner, out),
        TyKind::Tuple(parts) => {
            for &p in tcx.list(parts).iter() {
                holds_any(tcx, p, out);
            }
        }
        TyKind::Object(shape) => {
            for &(_, f) in tcx.shape(shape).fields.iter() {
                holds_any(tcx, f, out);
            }
        }
        _ => {}
    }
}

/// The written type of each field a class declares, in `ClassDef.fields` order, and
/// the part a `Box` would wrap (under a `| null`).
type FieldSpans = Vec<(enrang_base::Symbol, Span, Span)>;

fn class_field_spans(c: &ast::ClassDecl) -> FieldSpans {
    let mut out = Vec::new();
    for member in &c.members {
        match &member.kind {
            ast::ClassMemberKind::Field(f) => out.push(spans_of(f.name, &f.ty)),
            ast::ClassMemberKind::Constructor(ctor) => {
                for p in ctor.params.iter().filter(|p| p.property.is_some()) {
                    out.push(spans_of(p.name, &p.ty));
                }
            }
            _ => {}
        }
    }
    out
}

fn enum_field_spans(e: &ast::EnumDecl) -> FieldSpans {
    e.variants
        .iter()
        .flat_map(|v| match &v.payload {
            ast::VariantPayload::Fields(fields) => {
                fields.iter().map(|f| spans_of(f.name, &f.ty)).collect()
            }
            _ => Vec::new(),
        })
        .collect()
}

fn spans_of(name: ast::Ident, t: &ast::TypeExpr) -> (enrang_base::Symbol, Span, Span) {
    let inner = match &t.kind {
        ast::TypeExprKind::Nullable(inner) => inner.span,
        _ => t.span,
    };
    (name.name, t.span, inner)
}

/// A case value written as a literal: an integer, a negated one, or a text.
fn literal_value(sema: &Sema, e: &ast::Expr) -> Option<VariantValue> {
    match &e.kind {
        ast::ExprKind::Int { value, .. } => i128::try_from(*value).ok().map(VariantValue::Int),
        ast::ExprKind::Unary(ast::UnOp::Neg, inner) => match &inner.kind {
            ast::ExprKind::Int { value, .. } => {
                i128::try_from(*value).ok().map(|v| VariantValue::Int(-v))
            }
            _ => None,
        },
        ast::ExprKind::Str(s) => Some(VariantValue::Text(sema.tcx.intern_str(s.as_str()))),
        ast::ExprKind::Paren(inner) => literal_value(sema, inner),
        _ => None,
    }
}
