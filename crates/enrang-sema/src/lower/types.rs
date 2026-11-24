//! Type expressions to `Ty` (plan c.3; SPEC 3.2, 4.1, 4.2).
//!
//! A name resolves by `Res`: a primitive (`int` is `i32`); a lang class to its kind
//! (`string` `Str`, `Slice<T>` `Slice`, the array class `Array`, `Box<T>` `Boxed`,
//! A:758); a class, enum or method interface to `Adt` with its arguments; a type
//! parameter to `Param`; an alias to its expansion; `Self` to the interface's
//! implicit parameter. `Result<T>` is `Result<T, Failure>` (SPEC 4.4). A fixed
//! array's length is a constant expression (`consteval::eval_len`, which reports its
//! own failure). `x?: T` is `T | null`, or `T` when `T` already is nullable (A:888):
//! [`optional`]; an object type also records which fields were written `x?: T`
//! (D13), the ones a literal may leave out.
//!
//! Codes: an unresolved name EN0302 with "did you mean", or the SPEC 16 code of a
//! deferred name (`suggest.rs`); a wrong number of type arguments EN0309; type
//! arguments on a type parameter or a member of one (`T<i64>`, `T.Item`) EN1014; a
//! union other than `T | null` EN0406 (SPEC 4.2); an alias that reaches itself
//! EN0437; `&&T` and `&(&T | null)` EN0702 (S:847); a closure type anywhere but at
//! the top of a parameter's type, `| null` and parentheses included, EN0705 (S:367,
//! S:968): [`lower_param_ty`] is the parameter's entry; `Result<T, E>` whose `E` is no
//! error type EN0454 (S:638), unless `E` is a reference, a borrowing class or
//! anything else EN0701 or EN1006 rejects, checked once every class's fields are
//! known; a field named twice in an object type EN0307; an `@abi` function type that
//! passes anything but a scalar, a raw pointer or an `fn` pointer EN0816, or a class
//! or another aggregate by value EN1030 (S:1357-1360, [`ffi_check`]).
//! A type that an error made is `Error`, which absorbs every later check.

use enrang_base::Span;
use enrang_diag::{Code, Diagnostic, Help};
use enrang_hir::{
    Abi, AdtKind, AliasDef, DefId, DefKind, FnPtrSig, LangItem, Mark, PrimTy, Res, Shape, Ty,
    TyKind,
};
use enrang_syntax::ast;

use crate::consteval;
use crate::cx::Sema;
use crate::lower::{AliasKind, decorators, sigs};
use crate::resolve::suggest::{self, NameKind, unresolved};
use crate::resolve::{ScopeAt, scope};

/// Where a type is written, for EN0705.
#[derive(Copy, Clone, PartialEq, Eq)]
enum Place {
    /// Anywhere a closure type is not allowed.
    Plain,
    /// The top of a parameter's type, or under its parentheses or its `| null`.
    Param,
    /// Inside a closure type's parameters or result.
    InClosure,
}

/// The type `t` written at `at`, anywhere but at the top of a parameter's type.
pub(crate) fn lower_ty(sema: &mut Sema, at: ScopeAt, t: &ast::TypeExpr) -> Ty {
    lower_in(sema, at, t, Place::Plain)
}

/// The type `t` of a parameter (a function's, a method's, a constructor's or an
/// arrow's), where a closure type may stand at the top (S:367).
pub(crate) fn lower_param_ty(sema: &mut Sema, at: ScopeAt, t: &ast::TypeExpr) -> Ty {
    lower_in(sema, at, t, Place::Param)
}

/// The type `t` of an arrow's parameter: the arrow is a closure, so a closure type
/// there, at the top or below, is inside another closure type (EN0705, S:968).
pub(crate) fn lower_arrow_param_ty(sema: &mut Sema, at: ScopeAt, t: &ast::TypeExpr) -> Ty {
    lower_in(sema, at, t, Place::InClosure)
}

fn lower_in(sema: &mut Sema, at: ScopeAt, t: &ast::TypeExpr, place: Place) -> Ty {
    let error = sema.tcx.common().error;
    // Below this node, only parentheses and `| null` keep a parameter's top.
    let inner_place = match place {
        Place::Param => Place::Plain,
        other => other,
    };
    match &t.kind {
        ast::TypeExprKind::Named { path, args } => named(sema, at, t, path, args, inner_place),
        ast::TypeExprKind::Nullable(inner) => {
            let inner = lower_in(sema, at, inner, place);
            if sema.tcx.kind(inner) == TyKind::Error {
                return error;
            }
            sema.tcx.mk_nullable(inner)
        }
        ast::TypeExprKind::Ref(inner) | ast::TypeExprKind::ReadonlyRef(inner) => {
            let inner = lower_in(sema, at, inner, inner_place);
            reference(sema, t, inner)
        }
        ast::TypeExprKind::Raw(inner) => {
            let inner = lower_in(sema, at, inner, inner_place);
            sema.tcx.mk_raw(inner)
        }
        ast::TypeExprKind::Array(inner) => {
            let inner = lower_in(sema, at, inner, inner_place);
            sema.tcx.mk_array(inner)
        }
        ast::TypeExprKind::Fixed(inner, len) => {
            let inner = lower_in(sema, at, inner, inner_place);
            match consteval::eval_len(sema, at, len) {
                Some(n) => sema.tcx.mk_fixed(inner, n),
                None => error,
            }
        }
        ast::TypeExprKind::Tuple(parts) => {
            let parts: Vec<Ty> = parts
                .iter()
                .map(|p| lower_in(sema, at, p, inner_place))
                .collect();
            sema.tcx.mk_tuple(&parts)
        }
        ast::TypeExprKind::FnPtr(f) => {
            let abi = decorators::fn_type_abi(sema, &f.decorators);
            let mut sig = typed_sig(sema, at, &f.params, &f.ret.ty, inner_place);
            sig.unsafety = f.is_unsafe;
            sig.ret_readonly = f.ret.readonly;
            if abi != Abi::Enrang {
                for (p, &(ty, _)) in f.params.iter().zip(&sig.params) {
                    ffi_check(sema, ty, p.ty.span);
                }
                ffi_check(sema, sig.ret, f.ret.ty.span);
            }
            sema.tcx.mk_fn_ptr(abi, sig)
        }
        ast::TypeExprKind::Closure(c) => {
            if place != Place::Param {
                let label = if place == Place::InClosure {
                    "inside another closure type"
                } else {
                    "not a parameter's type"
                };
                sema.err(
                    Code::EN0705,
                    "a closure type can be written only as a parameter's type",
                    t.span,
                    label,
                );
                return error;
            }
            let sig = typed_sig(sema, at, &c.params, &c.ret, Place::InClosure);
            if closure_result_holds_refs(sema, sig.ret) {
                closure_result_error(sema, sig.ret, c.ret.span);
                return error;
            }
            sema.tcx.mk_closure(sig)
        }
        ast::TypeExprKind::Object(fields) => object(sema, at, fields, inner_place),
        ast::TypeExprKind::Union(_) => {
            sema.err(
                Code::EN0406,
                Code::EN0406.title(),
                t.span,
                "only `T | null` is a union",
            );
            error
        }
        ast::TypeExprKind::Paren(inner) => lower_in(sema, at, inner, place),
        ast::TypeExprKind::Void => sema.tcx.common().void,
        ast::TypeExprKind::Never => sema.tcx.common().never,
        ast::TypeExprKind::NullLit => {
            sema.err(
                Code::EN0401,
                "mismatched types: `null` is no type on its own",
                t.span,
                "write `T | null`",
            );
            error
        }
        // A string-literal union outside an alias is EN0216 in phase 1.
        ast::TypeExprKind::StrUnion(_) | ast::TypeExprKind::Error => error,
    }
}

/// `&T`; a reference to a reference is EN0702 (S:847).
fn reference(sema: &mut Sema, t: &ast::TypeExpr, inner: Ty) -> Ty {
    let error = sema.tcx.common().error;
    let to_ref = match sema.tcx.kind(inner) {
        TyKind::Error => return error,
        TyKind::Ref(_) => true,
        TyKind::Nullable(n) => matches!(sema.tcx.kind(n), TyKind::Ref(_)),
        _ => false,
    };
    if to_ref {
        let shown = sema.tcx.ty_string(inner);
        sema.err(
            Code::EN0702,
            "a reference can't point to a reference",
            t.span,
            format!("this points to `{shown}`"),
        );
        return error;
    }
    sema.tcx.mk_ref(inner)
}

/// An object type: fields sorted by name, `x?: T` collapsed and recorded (D13); a
/// field named twice is EN0307.
fn object(
    sema: &mut Sema,
    at: ScopeAt,
    fields: &[(ast::Ident, bool, ast::TypeExpr)],
    place: Place,
) -> Ty {
    let mut seen: Vec<ast::Ident> = Vec::new();
    let mut lowered = Vec::new();
    let mut optional_names = Vec::new();
    for (name, is_optional, ty) in fields {
        let ty = lower_in(sema, at, ty, place);
        if let Some(first) = seen.iter().find(|n| n.name == name.name) {
            sema.emit(
                Diagnostic::new(
                    Code::EN0307,
                    format!("`{}` is defined twice", name.name),
                    name.span,
                    "defined again here",
                )
                .with_secondary(first.span, format!("the first `{}` is here", name.name)),
            );
            continue;
        }
        seen.push(*name);
        let ty = if *is_optional {
            optional_names.push(name.name);
            optional(sema, ty)
        } else {
            ty
        };
        lowered.push((name.name, ty));
    }
    sema.tcx
        .mk_object_shape(Shape::with_optional(lowered, optional_names))
}

/// `x?: T`: `T | null`, or `T` when it already is nullable (A:888).
pub(crate) fn optional(sema: &Sema, t: Ty) -> Ty {
    match sema.tcx.kind(t) {
        TyKind::Nullable(_) | TyKind::Error => t,
        _ => sema.tcx.mk_nullable(t),
    }
}

/// A function pointer's or closure type's signature: `let` marks a parameter, and
/// names are dropped (A:288).
/// Whether `ret` may not be a closure's result: a reference or a borrowing value,
/// or either one nullable, outside `V` (S:557's `F ::= (S..) => V`, S:979).
pub(crate) fn closure_result_holds_refs(sema: &Sema, ret: Ty) -> bool {
    sema.tcx.is_slot_type(ret) && !sema.tcx.is_value_type(ret)
}

/// EN0703 for a closure type or a capturing arrow whose result `ret` holds a
/// reference (S:979): what it returns may point into its captures, which no
/// contract names, so the caller would keep no loan on them.
pub(crate) fn closure_result_error(sema: &mut Sema, ret: Ty, span: Span) {
    let shown = sema.tcx.ty_string(ret);
    sema.err(
        Code::EN0703,
        format!("a closure can't return `{shown}`, which holds a reference"),
        span,
        "the result of a closure is a value that holds no reference",
    );
}

fn typed_sig(
    sema: &mut Sema,
    at: ScopeAt,
    params: &[ast::TypedParam],
    ret: &ast::TypeExpr,
    place: Place,
) -> FnPtrSig {
    let params = params
        .iter()
        .map(|p| {
            let ty = lower_in(sema, at, &p.ty, place);
            (ty, if p.is_let { Mark::Let } else { Mark::None })
        })
        .collect();
    let ret = lower_in(sema, at, ret, place);
    FnPtrSig {
        unsafety: false,
        params,
        ret,
        ret_readonly: false,
    }
}

/// What may cross into foreign code (S:1357-1360) is an allowlist: integers, floats,
/// `bool`, `void` and `never` (as results), enums without fields, raw pointers,
/// `fn` pointers, and a raw or `fn` pointer `| null`. A class by value (`Box`,
/// an interface's value and an enum with fields included) or another aggregate by
/// value, an object type or a tuple, is EN1030 (SPEC 16: "struct by value in FFI");
/// anything else, `string`, `T[]`, `T[N]`, a reference, a view, a closure, a type
/// parameter or a nullable of something else, is EN0816.
pub(crate) fn ffi_check(sema: &mut Sema, ty: Ty, span: Span) {
    let Some((bad, by_value)) = ffi_offender(sema, ty) else {
        return;
    };
    if let Some(label) = by_value {
        sema.emit(suggest::deferred_labeled(Code::EN1030, span, label));
        return;
    }
    let shown = sema.tcx.ty_string(bad);
    sema.err(
        Code::EN0816,
        format!("`{shown}` can't cross into foreign code"),
        span,
        "foreign code takes scalars, raw pointers and `fn` pointers",
    );
}

/// The part of `ty` that may not cross into foreign code, with EN1030's label when
/// it is a class or an aggregate by value.
fn ffi_offender(sema: &Sema, ty: Ty) -> Option<(Ty, Option<&'static str>)> {
    let tcx = &*sema.tcx;
    match tcx.kind(ty) {
        TyKind::Bool
        | TyKind::Int(_)
        | TyKind::Float(_)
        | TyKind::Void
        | TyKind::Never
        | TyKind::Raw(_)
        | TyKind::FnPtr(..)
        | TyKind::Infer(_)
        | TyKind::Error => None,
        TyKind::Nullable(inner) => match tcx.kind(inner) {
            TyKind::Raw(_) | TyKind::FnPtr(..) | TyKind::Error => None,
            _ => match ffi_offender(sema, inner) {
                Some(found @ (_, Some(_))) => Some(found),
                _ => Some((ty, None)),
            },
        },
        TyKind::Adt(adt, _) => match &tcx.adt(adt).kind {
            AdtKind::Enum(e) if e.variants.iter().all(|v| v.fields.is_empty()) => None,
            AdtKind::Enum(_) => Some((ty, Some("an enum with fields passed by value"))),
            AdtKind::Class(_) => Some((ty, Some("a class passed by value"))),
            AdtKind::Interface(_) => Some((ty, Some("an interface passed by value"))),
        },
        TyKind::Boxed(_) => Some((ty, Some("a class passed by value"))),
        TyKind::Object(_) | TyKind::Tuple(_) => Some((ty, Some("a struct passed by value"))),
        TyKind::Str
        | TyKind::Array(_)
        | TyKind::Fixed(..)
        | TyKind::Slice(_)
        | TyKind::Ref(_)
        | TyKind::Closure(_)
        | TyKind::Param(_) => Some((ty, None)),
    }
}

fn prim_ty(sema: &Sema, prim: PrimTy) -> Ty {
    let common = sema.tcx.common();
    match prim {
        PrimTy::Bool => common.bool,
        PrimTy::Int(int) => common.int(int),
        PrimTy::Float(float) => common.float(float),
        PrimTy::Void => common.void,
        PrimTy::Never => common.never,
        PrimTy::Str => common.str,
    }
}

fn named(
    sema: &mut Sema,
    at: ScopeAt,
    t: &ast::TypeExpr,
    path: &[ast::Ident],
    args: &[ast::TypeExpr],
    place: Place,
) -> Ty {
    let error = sema.tcx.common().error;
    let (Some(first), Some(last)) = (path.first(), path.last()) else {
        return error;
    };
    // `T.Item`: a member of a type parameter (EN1014).
    if path.len() > 1
        && let Res::TyParam(_) = scope::lookup_type(sema, at, &path[..1])
    {
        sema.emit(suggest::deferred(Code::EN1014, t.span));
        return error;
    }
    let res = if path.len() > 1 {
        match qualified(sema, at, path) {
            Some(res) => res,
            None => return error,
        }
    } else {
        scope::lookup_type(sema, at, path)
    };
    let lowered: Vec<Ty> = args.iter().map(|a| lower_in(sema, at, a, place)).collect();
    let name = ast::Ident {
        name: last.name,
        span: first.span.to(last.span),
    };
    let args_span = match (args.first(), args.last()) {
        (Some(a), Some(b)) => a.span.to(b.span),
        _ => t.span,
    };
    let site = Site {
        name,
        args_span,
        arg_spans: args.iter().map(|a| a.span).collect(),
        given: lowered.len(),
    };
    match res {
        Res::PrimType(prim) => {
            if arity(sema, &site, 0) {
                prim_ty(sema, prim)
            } else {
                error
            }
        }
        Res::TyParam(p) => {
            if args.is_empty() {
                sema.tcx.mk_param(p)
            } else {
                sema.emit(suggest::deferred(Code::EN1014, t.span));
                error
            }
        }
        Res::SelfTy => match at.self_param {
            Some(p) if arity(sema, &site, 0) => sema.tcx.mk_param(p),
            _ => error,
        },
        Res::Def(def) => match sema.tcx.def(def).kind {
            DefKind::Adt(adt) | DefKind::StrUnion(adt) => adt_ty(sema, adt, lowered, &site),
            DefKind::TypeAlias => alias_ty(sema, def, &lowered, &site),
            _ => {
                unresolved(sema, at, name, NameKind::Type);
                error
            }
        },
        _ => {
            unresolved(sema, at, name, NameKind::Type);
            error
        }
    }
}

/// What a path through namespaces names (`d.serial.Port`). A segment that is no
/// public member of the namespace before it is reported at that segment, and the
/// path gives `None`: EN0311 for a `private` item (S:801), else EN0302 with "did you
/// mean" over the namespace's members (`suggest::unresolved_member`); a first name
/// that names nothing is EN0302 at it, over the namespaces in scope. Any other path
/// (a type's member, a namespace used as a type) is left to the caller, as a
/// one-name path is.
fn qualified(sema: &mut Sema, at: ScopeAt, path: &[ast::Ident]) -> Option<Res> {
    let mut module = match scope::lookup_type(sema, at, &path[..1]) {
        Res::Namespace(m) => m,
        Res::Err => {
            unresolved(sema, at, path[0], NameKind::Namespace);
            return None;
        }
        _ => return Some(scope::lookup_type(sema, at, path)),
    };
    for (i, segment) in path.iter().enumerate().skip(1) {
        let index = sema.res.index(module);
        let last = i + 1 == path.len();
        match scope::public_member(sema, index, segment.name) {
            Some(Res::Namespace(next)) if !last => module = next,
            Some(res) if last => return Some(res),
            Some(_) => return Some(Res::Err),
            None => {
                let prefix: Vec<&str> = path[..i].iter().map(|s| s.name.as_str()).collect();
                suggest::unresolved_member(sema, index, &prefix.join("."), *segment, last);
                return None;
            }
        }
    }
    Some(Res::Err)
}

/// Where a named type is written, for EN0309 and EN0454.
#[derive(Clone)]
struct Site {
    name: ast::Ident,
    args_span: Span,
    arg_spans: Vec<Span>,
    given: usize,
}

/// Whether `site` gives `expected` type arguments; EN0309 when not.
fn arity(sema: &mut Sema, site: &Site, expected: usize) -> bool {
    if site.given == expected {
        return true;
    }
    let plural = if expected == 1 { "" } else { "s" };
    let were = if site.given == 1 { "was" } else { "were" };
    sema.err(
        Code::EN0309,
        format!(
            "`{}` takes {expected} type argument{plural}, but {} {were} given",
            site.name.name, site.given
        ),
        site.args_span,
        format!("expected {expected} type argument{plural}"),
    );
    false
}

/// An ADT at its arguments, a lang class normalised to its kind (A:758).
fn adt_ty(sema: &mut Sema, adt: enrang_hir::AdtId, mut args: Vec<Ty>, site: &Site) -> Ty {
    let error = sema.tcx.common().error;
    let lang = sema.tcx.lang_item_of(sema.tcx.adt(adt).def);
    let normalised = match lang {
        Some(LangItem::Str) => Some((0, TyKind::Str)),
        Some(LangItem::Slice) => args.first().map(|&a| (1, TyKind::Slice(a))),
        Some(LangItem::Array) => args.first().map(|&a| (1, TyKind::Array(a))),
        Some(LangItem::Boxed) => args.first().map(|&a| (1, TyKind::Boxed(a))),
        _ => None,
    };
    if let Some((expected, kind)) = normalised {
        return if arity(sema, site, expected) {
            sema.tcx.intern_ty(kind)
        } else {
            error
        };
    }
    let expected = sema.tcx.generics(sema.tcx.adt(adt).generics).params.len();
    if lang == Some(LangItem::Result)
        && args.len() == 1
        && let Some(failure) = sema.tcx.lang_adt(LangItem::Failure)
    {
        args.push(sema.tcx.mk_adt(failure, &[]));
    }
    let site = Site {
        given: args.len(),
        ..site.clone()
    };
    if !arity(sema, &site, expected) {
        return error;
    }
    if lang == Some(LangItem::Result)
        && let (Some(&ok), Some(&err), Some(&span)) =
            (args.first(), args.get(1), site.arg_spans.get(1))
    {
        // `Result<T, Error>` is EN1006 with SPEC 16's help for errors, and its `E`
        // is then `Error`, the type, so nothing typed against it reports the same
        // mistake again (S:1140).
        if let TyKind::Adt(e, _) = sema.tcx.kind(err)
            && sema.tcx.is_lang_adt(e, LangItem::Error)
        {
            let ok = sema.tcx.ty_string(ok);
            let help = format!(
                "for errors, `Result<{ok}>`, because `Error` is a family of types, not a type"
            );
            crate::passes::positions::report_iface(sema, err, span, "a type argument", Some(help));
            args[1] = error;
            return sema.tcx.mk_adt(adt, &args);
        }
        if sema.decls.lowered {
            check_error_type(sema, ok, err, span);
        } else {
            sema.decls.error_args.push((ok, err, span));
        }
    }
    sema.tcx.mk_adt(adt, &args)
}

/// EN0454 for `Result<ok, err>` written with `err` at `span`, when `err` is no
/// error type: an enum, `Failure`, a class that `implements Error`, or a type
/// parameter (whose bound the position implies, S:762). A reference, a borrowing
/// class or anything else outside `V` is EN0701's (A:892), and an interface EN1006's,
/// so neither is also EN0454 (S:638).
pub(crate) fn check_error_type(sema: &mut Sema, ok: Ty, err: Ty, span: Span) {
    let tcx = &*sema.tcx;
    if tcx.references_error(err) || !tcx.is_value_type(err) {
        return;
    }
    match tcx.kind(err) {
        TyKind::Param(_) | TyKind::Infer(_) | TyKind::Error => return,
        TyKind::Adt(adt, _) => match &tcx.adt(adt).kind {
            AdtKind::Enum(_) | AdtKind::Interface(_) => return,
            AdtKind::Class(class) => {
                let error_iface = tcx.lang_adt(LangItem::Error);
                let implements = class
                    .implements
                    .iter()
                    .any(|&i| matches!(tcx.kind(i), TyKind::Adt(a, _) if Some(a) == error_iface));
                if tcx.is_lang_adt(adt, LangItem::Failure) || implements {
                    return;
                }
            }
        },
        _ => {}
    }
    let shown = tcx.ty_string(err);
    let help = if tcx.kind(err) == TyKind::Str {
        format!(
            "return `Result<{}>` and write the text in `Err(\"...\")`",
            tcx.ty_string(ok)
        )
    } else {
        "an error type is an enum, `Failure`, or a class that `implements Error`".to_owned()
    };
    sema.emit(
        Diagnostic::new(
            Code::EN0454,
            format!("`{shown}` is not an error type"),
            span,
            "the error type of this `Result`",
        )
        .with_help(Help::text(help)),
    );
}

/// An alias expanded at its arguments.
fn alias_ty(sema: &mut Sema, def: DefId, args: &[Ty], site: &Site) -> Ty {
    let error = sema.tcx.common().error;
    let Some(alias) = ensure_alias(sema, def) else {
        return error;
    };
    let params = sema.tcx.generics(alias.generics).params.clone();
    if !arity(sema, site, params.len()) {
        return error;
    }
    sema.tcx.subst(alias.ty, &params, args)
}

/// The lowered alias `def`, lowering it on first use; `None` while it is being
/// lowered, when a use inside its own body reaches it (EN0437, reported once at its
/// name).
pub(crate) fn ensure_alias(sema: &mut Sema, def: DefId) -> Option<AliasDef> {
    if let Some(done) = sema.tcx.alias(def) {
        return Some(done.clone());
    }
    let ast = *sema.decls.aliases.get(&def)?;
    if let Some(reported) = sema.decls.alias_visiting.get_mut(&def) {
        if !*reported {
            *reported = true;
            let name = sema.tcx.def(def).name().map(|n| n.as_str()).unwrap_or("");
            let span = sema.tcx.def(def).name_span;
            sema.err(
                Code::EN0437,
                format!("type alias `{name}` refers to itself"),
                span,
                "this alias reaches itself",
            );
        }
        return None;
    }
    sema.decls.alias_visiting.insert(def, false);
    let (type_params, module, test_part) = match ast.kind {
        AliasKind::Alias(a) => (&a.type_params, ast.module, ast.test_part),
        AliasKind::Fields(i) => (&i.type_params, ast.module, ast.test_part),
    };
    let generics = sigs::define_type_params(sema, def, None, type_params);
    let at = ScopeAt {
        generics: Some(generics),
        owner: Some(def),
        ..ScopeAt::module(module, test_part)
    };
    sigs::lower_bounds(sema, at, generics, type_params);
    sema.decls.scopes.insert(def, at);
    let ty = match ast.kind {
        AliasKind::Alias(a) => lower_ty(sema, at, &a.ty),
        AliasKind::Fields(i) => {
            let fields: Vec<(ast::Ident, bool, ast::TypeExpr)> = i
                .members
                .iter()
                .filter_map(|m| match m {
                    ast::IfaceMember::Field(f) => Some((f.name, f.optional, f.ty.clone())),
                    ast::IfaceMember::Method(_) => None,
                })
                .collect();
            // Duplicate names were reported where the interface was collected.
            let mut unique: Vec<(ast::Ident, bool, ast::TypeExpr)> = Vec::new();
            for f in fields {
                if !unique.iter().any(|u| u.0.name == f.0.name) {
                    unique.push(f);
                }
            }
            object(sema, at, &unique, Place::Plain)
        }
    };
    let reported = sema.decls.alias_visiting.remove(&def).unwrap_or(false);
    let ty = if reported {
        sema.tcx.common().error
    } else {
        ty
    };
    let alias = AliasDef { generics, ty };
    sema.tcx.set_alias(def, alias.clone());
    Some(alias)
}
