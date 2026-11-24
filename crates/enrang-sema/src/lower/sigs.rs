//! Signatures (plan c.1-c.2, d.4): type parameters and bounds, parameters with
//! their marks and `?` collapse, results with `readonly`, receivers, `where`
//! clauses, and the implicit type parameters of interface- and object-typed
//! parameters (departure D5, A:892-894).
//!
//! A by-value or `&` parameter of a method-interface type or of an object type (a
//! fields-only interface included) gets an implicit type parameter appended to the
//! function's generics, so its body sees "a class of its own": `Implicit::Interface`
//! bounded by the interface, or `Implicit::Shape`. One copy of the function per shape
//! or class passed resolves it (SPEC 4.5 C20 "by value or by reference ... one copy of
//! the function per shape", S:601, A:599), and the copy reads a class at its own
//! offsets. An `&I | null` or `&{ .. } | null` parameter does not (A:599), nor does
//! any parameter of a `declare function`, since foreign code is never generic: its
//! interface or object type is an FFI error instead (EN1030, EN0816).

use std::collections::BTreeMap;

use enrang_base::{Span, intern};
use enrang_hir::{
    Abi, Bound, BoundId, DefId, DefKind, FnSig, Generics, GenericsId, Implicit, ItemPath, LangItem,
    Mark, ParamSig, Receiver, Ty, TyKind, TyParamDef,
};
use enrang_syntax::ast;

use crate::cx::Sema;
use crate::lower::types::{lower_param_ty, lower_ty, optional};
use crate::lower::{ItemAst, ItemAstKind};
use crate::resolve::ScopeAt;
use crate::resolve::suggest::{NameKind, unresolved};

/// Defines `params` as type parameters owned by `owner`, under `parent`; their
/// bounds come later (`lower_bounds`), once every ADT exists. A name given twice in
/// one list is EN0307.
pub(crate) fn define_type_params(
    sema: &mut Sema,
    owner: DefId,
    parent: Option<GenericsId>,
    params: &[ast::TypeParam],
) -> GenericsId {
    let names: Vec<ast::Ident> = params.iter().map(|p| p.name).collect();
    twice(sema, &names);
    let ids = params
        .iter()
        .enumerate()
        .map(|(i, p)| {
            sema.tcx.define_param(TyParamDef {
                name: p.name.name,
                owner,
                index: i as u32,
                bounds: Vec::new(),
                implicit: None,
                span: p.name.span,
            })
        })
        .collect();
    sema.tcx.define_generics(Generics::new(parent, ids))
}

/// Lowers each written bound of `params`, the own parameters of `generics`.
pub(crate) fn lower_bounds(
    sema: &mut Sema,
    at: ScopeAt,
    generics: GenericsId,
    params: &[ast::TypeParam],
) {
    let ids = sema.tcx.generics(generics).params.clone();
    for (p, written) in ids.iter().zip(params) {
        let bounds: Vec<BoundId> = written
            .bounds
            .iter()
            .filter_map(|b| lower_bound(sema, at, b))
            .collect();
        sema.tcx.param_mut(*p).bounds.extend(bounds);
    }
}

/// A bound: an interface or a class with its arguments (SPEC 3.1's `Bound`).
/// Anything else, a primitive, an enum or an alias of either, is EN0419 at the
/// bound (plan c.1 choice) and is dropped; a type already reported is dropped
/// quietly.
pub(crate) fn lower_bound(sema: &mut Sema, at: ScopeAt, t: &ast::TypeExpr) -> Option<BoundId> {
    let ty = lower_ty(sema, at, t);
    let bound = match sema.tcx.kind(ty) {
        TyKind::Adt(adt, args) if sema.tcx.adt(adt).is_interface() => Bound::Iface { adt, args },
        TyKind::Adt(adt, args) if sema.tcx.adt(adt).is_class() => Bound::Class { adt, args },
        TyKind::Error => return None,
        _ => {
            let shown = sema.tcx.ty_string(ty);
            sema.err(
                enrang_diag::Code::EN0419,
                format!("`{shown}` can't be a bound"),
                t.span,
                "a bound names an interface or a class",
            );
            return None;
        }
    };
    Some(sema.tcx.define_bound(bound))
}

/// The scope of an ADT's or `extend` block's members.
fn member_scope(sema: &Sema, parent: DefId) -> ScopeAt {
    sema.decls.scopes[&parent]
}

/// EN0307 for each name of `names` given again after its first.
pub(crate) fn twice(sema: &mut Sema, names: &[ast::Ident]) {
    for (i, name) in names.iter().enumerate() {
        if let Some(first) = names[..i].iter().find(|n| n.name == name.name) {
            sema.emit(
                enrang_diag::Diagnostic::new(
                    enrang_diag::Code::EN0307,
                    format!("`{}` is defined twice", name.name),
                    name.span,
                    "defined again here",
                )
                .with_secondary(first.span, format!("the first `{}` is here", name.name)),
            );
        }
    }
}

/// The names a parameter list binds, destructured ones included.
fn param_names(params: &[ast::Param]) -> Vec<ast::Ident> {
    fn walk(b: &ast::Binding, out: &mut Vec<ast::Ident>) {
        match b {
            ast::Binding::Name(n) => out.push(*n),
            ast::Binding::Object { fields, .. } => {
                for (f, sub) in fields {
                    match sub {
                        Some(sub) => walk(sub, out),
                        None => out.push(*f),
                    }
                }
            }
            ast::Binding::Tuple { elems, .. } => {
                for e in elems {
                    walk(e, out);
                }
            }
        }
    }
    let mut out = Vec::new();
    for p in params {
        walk(&p.binding, &mut out);
    }
    out
}

/// Lowers the signatures `item` declares.
pub(crate) fn lower(sema: &mut Sema, item: &ItemAst) {
    let base = ScopeAt::module(item.module, item.test_part);
    match &item.kind {
        ItemAstKind::Function(f) | ItemAstKind::LocalFn(f) => {
            let sig = function(sema, item.def, base, &FnAst::of_function(f));
            sema.tcx.set_sig(item.def, sig);
        }
        ItemAstKind::Declare(d) => {
            let mut sig = function(sema, item.def, base, &FnAst::of_declare(d));
            sig.unsafety = true;
            sema.tcx.set_sig(item.def, sig);
        }
        ItemAstKind::Class(adt, class, members) => {
            let at = member_scope(sema, item.def);
            for (member, def) in class.members.iter().zip(members) {
                let Some(def) = *def else { continue };
                let sig = match &member.kind {
                    ast::ClassMemberKind::Method(m) => {
                        function(sema, def, at, &FnAst::of_method(m))
                    }
                    ast::ClassMemberKind::Constructor(c) => constructor(sema, def, at, c),
                    ast::ClassMemberKind::Destructor(_) => {
                        let generics = sema.tcx.adt(*adt).generics;
                        sema.decls.scopes.insert(
                            def,
                            ScopeAt {
                                generics: Some(generics),
                                owner: Some(def),
                                ..at
                            },
                        );
                        let mut sig = FnSig::new(generics, Vec::new(), sema.tcx.common().void);
                        sig.receiver = Some(Receiver::Ref(Mark::None));
                        sig
                    }
                    ast::ClassMemberKind::Field(_) => continue,
                };
                sema.tcx.set_sig(def, sig);
            }
        }
        ItemAstKind::Enum(_, e, methods) => {
            let at = member_scope(sema, item.def);
            for (m, &def) in e.methods.iter().zip(methods) {
                let sig = function(sema, def, at, &FnAst::of_method(m));
                sema.tcx.set_sig(def, sig);
            }
        }
        ItemAstKind::Interface(_, i, members) => {
            let at = member_scope(sema, item.def);
            for (member, def) in i.members.iter().zip(members) {
                if let (ast::IfaceMember::Method(m), Some(def)) = (member, def) {
                    let sig = function(sema, *def, at, &FnAst::of_method(m));
                    sema.tcx.set_sig(*def, sig);
                }
            }
        }
        ItemAstKind::Extend(x, members) => {
            let at = member_scope(sema, item.def);
            for (member, &def) in x.members.iter().zip(members) {
                let sig = function(sema, def, at, &FnAst::of_method(&member.method));
                sema.tcx.set_sig(def, sig);
            }
        }
        _ => {}
    }
}

/// The parts of a function, method or `declare` that a signature reads.
struct FnAst<'f> {
    type_params: &'f [ast::TypeParam],
    params: &'f [ast::Param],
    ret: Option<&'f ast::TypeExpr>,
    ret_readonly: bool,
    unsafety: bool,
    receiver: Option<ast::Receiver>,
    where_clause: &'f [ast::WherePred],
    /// A `declare function`: its parameters take no implicit type parameter (D5),
    /// since foreign code is never generic, and `ffi_check` reads them as written.
    foreign: bool,
}

impl<'f> FnAst<'f> {
    fn of_function(f: &'f ast::FunctionDecl) -> FnAst<'f> {
        FnAst {
            type_params: &f.type_params,
            params: &f.params,
            ret: f.ret.as_ref().map(|r| &r.ty),
            ret_readonly: f.ret.as_ref().is_some_and(|r| r.readonly),
            unsafety: f.is_unsafe,
            receiver: None,
            where_clause: &[],
            foreign: false,
        }
    }

    fn of_declare(d: &'f ast::DeclareFn) -> FnAst<'f> {
        FnAst {
            type_params: &d.type_params,
            params: &d.params,
            ret: d.ret.as_ref(),
            ret_readonly: false,
            unsafety: true,
            receiver: None,
            where_clause: &[],
            foreign: true,
        }
    }

    fn of_method(m: &'f ast::MethodDecl) -> FnAst<'f> {
        FnAst {
            type_params: &m.type_params,
            params: &m.params,
            ret: m.ret.as_ref().map(|r| &r.ty),
            ret_readonly: m.ret.as_ref().is_some_and(|r| r.readonly),
            unsafety: m.is_unsafe,
            receiver: Some(m.receiver),
            where_clause: &m.where_clause,
            foreign: false,
        }
    }
}

fn mark_of(mark: ast::ParamMark) -> Mark {
    match mark {
        ast::ParamMark::Plain => Mark::None,
        ast::ParamMark::Let => Mark::Let,
        ast::ParamMark::Const => Mark::Const,
    }
}

fn receiver_of(r: ast::Receiver) -> Receiver {
    match r {
        ast::Receiver::Plain => Receiver::Ref(Mark::None),
        ast::Receiver::Let => Receiver::Ref(Mark::Let),
        ast::Receiver::Const => Receiver::Ref(Mark::Const),
        ast::Receiver::Move => Receiver::Move,
        ast::Receiver::Static => Receiver::Static,
    }
}

/// A signature: own generics under `base`'s, bounds, parameters, result, `where`.
fn function(sema: &mut Sema, def: DefId, base: ScopeAt, f: &FnAst) -> FnSig {
    let generics = define_type_params(sema, def, base.generics, f.type_params);
    let at = ScopeAt {
        generics: Some(generics),
        owner: Some(def),
        ..base
    };
    lower_bounds(sema, at, generics, f.type_params);
    sema.decls.scopes.insert(def, at);
    twice(sema, &param_names(f.params));
    let params: Vec<ParamSig> = f
        .params
        .iter()
        .map(|p| {
            let name = match &p.binding {
                ast::Binding::Name(ident) => ident.name,
                _ => intern("_"),
            };
            let implicit = (!f.foreign).then_some((def, generics));
            param(
                sema,
                implicit,
                at,
                name,
                &p.ty,
                p.optional,
                p.default.is_some(),
                mark_of(p.mark),
                p.span,
            )
        })
        .collect();
    let ret = match f.ret {
        Some(t) => lower_ty(sema, at, t),
        None => sema.tcx.common().void,
    };
    let attrs = sema.tcx.def(def).attrs.clone();
    let written: Vec<Ty> = params.iter().map(|p| p.ty).chain([ret]).collect();
    implied_error_bounds(sema, generics, &written);
    let mut sig = FnSig::new(generics, params, ret);
    sig.ret_fn_names = f.ret.and_then(fn_names);
    sig.ret_readonly = f.ret_readonly;
    sig.unsafety = f.unsafety;
    sig.receiver = f.receiver.map(receiver_of);
    sig.requires = attrs.requires;
    // C16: `@dll` functions have `@abi("win64")` (S:674).
    let dll_abi = attrs.dll.map(|_| Abi::Win64);
    sig.abi = attrs.abi.or(dll_abi).unwrap_or(Abi::Enrang);
    sig.where_bounds = where_bounds(sema, at, base.generics, f.where_clause);
    sig
}

/// S:1140: writing `Result<T, E>` implies `E extends Error`. Each own parameter of
/// `generics` that a `Result` in `written` takes as its error type, with no `Error`
/// bound of its own, gets one, so the body and its callers read it bounded.
fn implied_error_bounds(sema: &mut Sema, generics: GenericsId, written: &[Ty]) {
    let (Some(result), Some(error)) = (
        sema.tcx.lang_adt(LangItem::Result),
        sema.tcx.lang_adt(LangItem::Error),
    ) else {
        return;
    };
    let own = sema.tcx.generics(generics).params.clone();
    let mut implied = Vec::new();
    for &t in written {
        sema.tcx.any_ty(t, &mut |tcx, t| {
            if let TyKind::Adt(adt, args) = tcx.kind(t)
                && adt == result
                && let Some(&err) = tcx.list(args).get(1)
                && let TyKind::Param(q) = tcx.kind(err)
                && own.contains(&q)
                && !implied.contains(&q)
            {
                implied.push(q);
            }
            false
        });
    }
    for q in implied {
        let bounded = sema
            .tcx
            .param(q)
            .bounds
            .iter()
            .any(|&b| matches!(sema.tcx.bound(b), Bound::Iface { adt, .. } if *adt == error));
        if !bounded {
            let args = sema.tcx.intern_list(&[]);
            let b = sema.tcx.define_bound(Bound::Iface { adt: error, args });
            sema.tcx.param_mut(q).bounds.push(b);
        }
    }
}

/// A constructor: no receiver, a `void` result (plan c.2).
fn constructor(sema: &mut Sema, def: DefId, base: ScopeAt, c: &ast::Constructor) -> FnSig {
    let generics = sema
        .tcx
        .define_generics(Generics::new(base.generics, Vec::new()));
    let at = ScopeAt {
        generics: Some(generics),
        owner: Some(def),
        ..base
    };
    sema.decls.scopes.insert(def, at);
    let names: Vec<ast::Ident> = c.params.iter().map(|p| p.name).collect();
    twice(sema, &names);
    let params = c
        .params
        .iter()
        .map(|p| {
            param(
                sema,
                Some((def, generics)),
                at,
                p.name.name,
                &p.ty,
                p.optional,
                p.default.is_some(),
                mark_of(p.mark),
                p.span,
            )
        })
        .collect();
    FnSig::new(generics, params, sema.tcx.common().void)
}

/// One parameter: its type with `?` collapsed and, for an interface or object
/// type, its implicit type parameter (D5) appended to `implicit`'s generics, unless
/// `implicit` is `None` (a `declare function`).
#[allow(clippy::too_many_arguments)]
fn param(
    sema: &mut Sema,
    implicit_in: Option<(DefId, GenericsId)>,
    at: ScopeAt,
    name: enrang_base::Symbol,
    t: &ast::TypeExpr,
    is_optional: bool,
    has_default: bool,
    mark: Mark,
    span: Span,
) -> ParamSig {
    let lowered = lower_param_ty(sema, at, t);
    let ty = match implicit_in {
        _ if is_optional => optional(sema, lowered),
        Some((def, generics)) => implicit(sema, def, generics, lowered),
        None => lowered,
    };
    ParamSig {
        name,
        ty,
        mark,
        has_default: has_default || is_optional,
        fn_names: fn_names(t),
        span,
    }
}

/// D14: the parameter names of a function or closure type written as `t`, under
/// parentheses and at most one `| null`; `None` for any other type, an alias of one
/// included.
fn fn_names(t: &ast::TypeExpr) -> Option<Vec<enrang_base::Symbol>> {
    let mut t = t;
    let mut nullable = false;
    loop {
        match &t.kind {
            ast::TypeExprKind::Paren(inner) => t = inner,
            ast::TypeExprKind::Nullable(inner) if !nullable => {
                nullable = true;
                t = inner;
            }
            ast::TypeExprKind::FnPtr(f) => {
                return Some(f.params.iter().map(|p| p.name.name).collect());
            }
            ast::TypeExprKind::Closure(c) => {
                return Some(c.params.iter().map(|p| p.name.name).collect());
            }
            _ => return None,
        }
    }
}

/// D5: `I` or `&I` of a method interface, or an object type by value or behind `&`,
/// becomes an implicit type parameter appended to `generics`.
fn implicit(sema: &mut Sema, def: DefId, generics: GenericsId, ty: Ty) -> Ty {
    let tcx = &*sema.tcx;
    let (inner, behind_ref) = match tcx.kind(ty) {
        TyKind::Ref(inner) => (inner, true),
        _ => (ty, false),
    };
    let (implicit, bound, name) = match tcx.kind(inner) {
        TyKind::Adt(adt, args) if tcx.adt(adt).is_interface() => (
            Implicit::Interface(adt),
            Some(Bound::Iface { adt, args }),
            tcx.adt(adt).name,
        ),
        TyKind::Object(shape) => (Implicit::Shape(shape), None, intern(&tcx.ty_string(inner))),
        _ => return ty,
    };
    let bounds = bound
        .map(|b| vec![sema.tcx.define_bound(b)])
        .unwrap_or_default();
    let index = sema.tcx.generics(generics).params.len() as u32;
    let p = sema.tcx.define_param(TyParamDef {
        name,
        owner: def,
        index,
        bounds,
        implicit: Some(implicit),
        span: Span::DUMMY,
    });
    sema.tcx.generics_mut(generics).params.push(p);
    let param = sema.tcx.mk_param(p);
    if behind_ref {
        sema.tcx.mk_ref(param)
    } else {
        param
    }
}

/// A method's `where` clause: bounds on its class's or `extend`'s parameters; a name
/// that is none of them is EN0302 (plan choice).
fn where_bounds(
    sema: &mut Sema,
    at: ScopeAt,
    parent: Option<GenericsId>,
    preds: &[ast::WherePred],
) -> Vec<(enrang_hir::ParamId, Vec<BoundId>)> {
    let mut out = Vec::new();
    let candidates = parent.map(|g| sema.tcx.all_params(g)).unwrap_or_default();
    for pred in preds {
        let Some(&p) = candidates
            .iter()
            .find(|&&p| sema.tcx.param(p).name == pred.param.name)
        else {
            unresolved(sema, at, pred.param, NameKind::Type);
            continue;
        };
        let bounds = pred
            .bounds
            .iter()
            .filter_map(|b| lower_bound(sema, at, b))
            .collect();
        out.push((p, bounds));
    }
    out
}

/// Names each overload by its parameter types (ARCHITECTURE 6.8): every group of
/// functions, methods or constructors sharing a path gets `ItemPath.overload`, each
/// type spelled with its classes' own paths (`Tcx::ty_path_string`), so overloads
/// over two same-named classes of two modules get two paths.
pub(crate) fn overload_paths(sema: &mut Sema) {
    let mut groups: BTreeMap<ItemPath, Vec<DefId>> = BTreeMap::new();
    for (def, data) in sema.tcx.defs() {
        if data.kind.has_sig() && data.kind != DefKind::Dtor && sema.tcx.sig_opt(def).is_some() {
            groups.entry(data.path.clone()).or_default().push(def);
        }
    }
    for defs in groups.into_values().filter(|defs| defs.len() > 1) {
        for def in defs {
            let params: Vec<String> = sema
                .tcx
                .sig(def)
                .params
                .iter()
                .map(|p| sema.tcx.ty_path_string(p.ty))
                .collect();
            let path = sema.tcx.def(def).path.clone().with_overload(params);
            sema.tcx.def_mut(def).path = path;
        }
    }
}
