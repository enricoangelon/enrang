//! Exact satisfaction of an interface (plan d.16, g.5; SPEC 4.4 S:609-617; owner
//! 4D), the engine EN0416 (`implements`, here) and EN0419 (a bound, 4A's) share.
//!
//! After substituting `Self`, lookup on the type itself finds, for every member of
//! the interface, a member that is `public`, has the same unsafety, has no
//! `@requires`, is a method, and has equal type parameters and bounds, equal
//! parameter types and an equal return type (marks never compared, N1). Own,
//! inherited and `extend` members count; `Box` auto-deref never does, so a member
//! found only on `V` of a `Box<V>` is its own clause. Of the members found with the
//! interface member's signature, the first decides which clause fails; with none,
//! the signature does. The prelude's nominal interfaces keep their own rules:
//! `Copy` by `Tcx::is_copy`, `Error` by enum, `Failure` or a written `implements
//! Error`, `Display` always (S:642), `Clone` by `Tcx::is_clone` unless user code
//! writes a `clone`, which is checked as any member (S:639), and `Eq` also by a
//! written `implements Eq` with no `equals`, which synthesises one (S:640). A
//! sealed interface is met by the compiler's implementer table (b.9), a class bound
//! by name: the class or a subclass at the same arguments (S:764). A type parameter
//! bounded by the interface meets it.
//!
//! The declaration checks: `implements I` unmet is EN0416 at that `I`, naming the
//! first member that fails and its clause (wording of plan e); `implements` of a
//! sealed interface is EN0419 (S:650); `implements Copy` is EN0418's (members.rs);
//! `implements` of something that is no interface (a class, an enum, a primitive)
//! is EN0401 (plan choice, as `extends` of a non-class is in lowering). A
//! fields-only interface is an object type: `implements Point` checks the class's
//! public fields (S:629), each present with an equal type.
//!
//! Satisfaction is one relation, checked wherever a type is used as an interface
//! (SPEC 4.4, A:899): an `implements` entry, a C22 conversion, an argument to a
//! non-null `&I` or by-value `I` parameter, and a bound met by a written or inferred
//! type argument. Each of those sites calls [`satisfy`], the one satisfaction
//! routine, which records every member lookup found, own, inherited or `extend`,
//! with the interface member it satisfies and the site ([`Satisfaction`]). Once
//! every body's facts are known, [`check_recorded`] runs the string clause over the
//! recorded set, through `views.rs`'s `check_implementations`, once per member found
//! and interface member, at the first site that recorded it; phase 3's contract
//! fitting reads the same set. A probe that typing rolls back drops what it recorded.

use std::collections::BTreeSet;

use enrang_base::{Span, Symbol, intern};
use enrang_diag::{Code, Diagnostic};
use enrang_hir::{
    AdtId, AdtKind, Bound, DefId, FoundMethod, IfaceDef, LangItem, MemberKind, ParamEnv, ShapeId,
    Tcx, Ty, TyKind, TyList, Vis,
};
use enrang_target::FeatureSet;

use crate::classes::members::ClassAst;
use crate::classes::sig::{is_static, same_bounds, same_params, same_ret, sig_string, view};
use crate::cx::Sema;
use crate::passes::views;

/// Why a type does not satisfy an interface: the interface member that fails (when
/// one does), the clause, and the member found that fails it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Unmet {
    pub member: Option<DefId>,
    /// The clause as messages word it: `` `m` is private ``.
    pub reason: String,
    pub clause: Clause,
    /// The member lookup found that fails the clause.
    pub found: Option<DefId>,
}

/// One member a satisfaction relies on (SPEC 4.4, A:899): the type used as the
/// interface `iface` at `site`, the interface member `member`, and the member
/// lookup found for it on that type, own, inherited or `extend`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Satisfaction {
    pub ty: Ty,
    pub iface: Ty,
    pub member: DefId,
    pub found: DefId,
    pub site: Span,
}

/// The clauses of S:611-617, and the nominal rules.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Clause {
    Private,
    Protected,
    /// The interface member is `unsafe` and the method is not.
    NotUnsafe,
    /// The method is `unsafe` and the interface member is not.
    Unsafe,
    Requires,
    Field,
    /// The method matches but is `static`, or is not when the member is.
    Static,
    Signature,
    OnlyThroughBox,
    Missing,
    /// A fields-only interface's field has another type.
    FieldType,
    /// A nominal interface, a sealed one or a class bound is not met.
    Nominal,
}

impl Unmet {
    fn new(member: Option<DefId>, name: Symbol, clause: Clause, found: Option<DefId>) -> Unmet {
        let what = match clause {
            Clause::Private => "is private",
            Clause::Protected => "is protected",
            Clause::NotUnsafe => "is not `unsafe`",
            Clause::Unsafe => "is `unsafe`",
            Clause::Requires => "has `@requires`",
            Clause::Field => "is a field",
            Clause::Static => "is `static`",
            Clause::Signature => "has another signature",
            Clause::OnlyThroughBox => "is found only through `Box`",
            Clause::Missing => "is missing",
            Clause::FieldType => "has another type",
            Clause::Nominal => "is not met",
        };
        Unmet {
            member,
            reason: format!("`{name}` {what}"),
            clause,
            found,
        }
    }

    fn nominal(reason: String) -> Unmet {
        Unmet {
            member: None,
            reason,
            clause: Clause::Nominal,
            found: None,
        }
    }
}

/// Whether `ty` satisfies the interface (or class bound) `iface` under `env`, as a
/// question that records nothing: a site that uses `ty` as `iface` calls
/// [`satisfy`].
pub(crate) fn satisfies(tcx: &Tcx, ty: Ty, iface: Ty, env: &ParamEnv) -> Result<(), Unmet> {
    satisfaction(tcx, ty, iface, env).map(|_| ())
}

/// The one satisfaction routine (module doc): whether `ty`, used as `iface` at
/// `site`, satisfies it, recording each member lookup found for the satisfaction.
pub(crate) fn satisfy(
    sema: &mut Sema,
    ty: Ty,
    iface: Ty,
    env: &ParamEnv,
    site: Span,
) -> Result<(), Unmet> {
    let found = satisfaction(sema.tcx, ty, iface, env)?;
    for (member, found) in found {
        sema.classes.satisfactions.push(Satisfaction {
            ty,
            iface,
            member,
            found,
            site,
        });
    }
    Ok(())
}

/// The string clause of satisfaction over every recorded satisfaction, once every
/// body's facts are known (module doc): `views.rs`'s `check_implementations` over
/// one entry per member found and interface member, the first recorded.
pub(crate) fn check_recorded(sema: &mut Sema, facts: &views::Facts) {
    let mut seen = BTreeSet::new();
    let set: Vec<Satisfaction> = sema
        .classes
        .satisfactions
        .iter()
        .filter(|s| seen.insert((s.found, s.member)))
        .cloned()
        .collect();
    views::check_implementations(sema, facts, &set);
}

/// [`satisfies`] with what it relies on: each interface member with the member
/// lookup found for it. An interface met by the compiler's own rules, a sealed one,
/// a class bound, a fields-only interface and a type parameter bounded by the
/// interface rely on no member.
fn satisfaction(
    tcx: &Tcx,
    ty: Ty,
    iface: Ty,
    env: &ParamEnv,
) -> Result<Vec<(DefId, DefId)>, Unmet> {
    if tcx.references_error(ty) || tcx.references_error(iface) {
        return Ok(Vec::new());
    }
    match tcx.kind(iface) {
        TyKind::Adt(adt, args) => match &tcx.adt(adt).kind {
            AdtKind::Interface(i) => interface(tcx, ty, adt, args, i, env),
            AdtKind::Class(_) => class_bound(tcx, ty, adt, args, env).map(|()| Vec::new()),
            // No bound or `implements` names an enum past lowering's checks.
            AdtKind::Enum(_) => Ok(Vec::new()),
        },
        TyKind::Object(shape) => object(tcx, ty, shape).map(|()| Vec::new()),
        _ => Ok(Vec::new()),
    }
}

fn interface(
    tcx: &Tcx,
    ty: Ty,
    adt: AdtId,
    args: TyList,
    iface: &IfaceDef,
    env: &ParamEnv,
) -> Result<Vec<(DefId, DefId)>, Unmet> {
    if let TyKind::Param(p) = tcx.kind(ty)
        && bounded_by(tcx, p, env, adt, args)
    {
        return Ok(Vec::new());
    }
    let shown = tcx.ty_string(ty);
    let iface_name = tcx.adt(adt).name;
    match tcx.lang_item_of(tcx.adt(adt).def) {
        Some(LangItem::Copy) => {
            return match tcx.is_copy(ty, env) {
                true => Ok(Vec::new()),
                false => Err(Unmet::nominal(format!("`{shown}` is not Copy"))),
            };
        }
        Some(LangItem::Display) => return Ok(Vec::new()),
        // A `clone` that user code writes always wins (S:639), so it is checked as
        // any member is; with none, `is_clone` says whether one is synthesised.
        Some(LangItem::Clone) if !writes_clone(tcx, ty) => {
            if tcx.is_clone(ty, env) {
                return Ok(Vec::new());
            }
            let clone = iface.methods.first().copied();
            return Err(Unmet::new(clone, intern("clone"), Clause::Missing, None));
        }
        Some(LangItem::Error) => {
            return match is_error_type(tcx, ty, env) {
                true => Ok(Vec::new()),
                false => Err(Unmet::nominal(format!("`{shown}` is not an error type"))),
            };
        }
        Some(LangItem::Eq) if synthesised_eq(tcx, ty, adt) => return Ok(Vec::new()),
        _ => {}
    }
    if let Some(item) = iface.sealed {
        return match tcx.sealed_implements(item, ty) {
            true => Ok(Vec::new()),
            false => Err(Unmet::nominal(format!(
                "`{shown}` is not one of `{iface_name}`'s implementers"
            ))),
        };
    }
    let args = tcx.list(args).to_vec();
    let mut found = Vec::new();
    for &m in &iface.methods {
        let Some(name) = tcx.def(m).name() else {
            continue;
        };
        // A destructor is never a member (S:648); declaring one is EN0606.
        if name.as_str() == "destructor" {
            continue;
        }
        if let Some(def) = member(tcx, ty, m, name, &args)? {
            found.push((m, def));
        }
    }
    Ok(found)
}

/// Whether type parameter `p` is bounded by `adt` at `args`, by its own bounds or
/// by `env`.
fn bounded_by(tcx: &Tcx, p: enrang_hir::ParamId, env: &ParamEnv, adt: AdtId, args: TyList) -> bool {
    tcx.param(p)
        .bounds
        .iter()
        .copied()
        .chain(env.bounds_of(p))
        .any(|b| match tcx.bound(b) {
            Bound::Iface { adt: a, args: x } => *a == adt && same_lists(tcx, *x, args),
            Bound::Class { .. } => false,
        })
}

fn same_lists(tcx: &Tcx, x: TyList, y: TyList) -> bool {
    let (x, y) = (tcx.list(x), tcx.list(y));
    x.len() == y.len()
        && x.iter()
            .zip(y.iter())
            .all(|(&a, &b)| tcx.same_ignoring_rows(a, b))
}

/// An error type (S:638): an enum, `Failure`, a class that writes `implements
/// Error`, or a parameter bounded by `Error`.
pub(crate) fn is_error_type(tcx: &Tcx, ty: Ty, env: &ParamEnv) -> bool {
    match tcx.kind(ty) {
        TyKind::Error => true,
        TyKind::Param(p) => tcx.param_bounded_by(p, env, LangItem::Error),
        TyKind::Adt(adt, _) => match &tcx.adt(adt).kind {
            AdtKind::Enum(_) => true,
            AdtKind::Class(class) => {
                let error = tcx.lang_adt(LangItem::Error);
                tcx.is_lang_adt(adt, LangItem::Failure)
                    || class
                        .implements
                        .iter()
                        .any(|&i| matches!(tcx.kind(i), TyKind::Adt(a, _) if Some(a) == error))
            }
            AdtKind::Interface(_) => false,
        },
        _ => false,
    }
}

/// Whether `ty` is a class or enum with a `clone` of its own or inherited, written
/// in a user module (the library's are trusted, as its `extend` blocks may add
/// `where` bounds that a signature does not show).
fn writes_clone(tcx: &Tcx, ty: Ty) -> bool {
    let TyKind::Adt(adt, args) = tcx.kind(ty) else {
        return false;
    };
    tcx.find_method(adt, args, intern("clone"))
        .is_some_and(|m| !tcx.module(tcx.def(m).module).library)
}

/// A class that writes `implements Eq` and has no `equals`, own or inherited, gets
/// one synthesised memberwise (S:640).
pub(crate) fn synthesised_eq(tcx: &Tcx, ty: Ty, eq: AdtId) -> bool {
    let TyKind::Adt(adt, args) = tcx.kind(ty) else {
        return false;
    };
    let Some(class) = tcx.adt(adt).as_class() else {
        return false;
    };
    let writes = class
        .implements
        .iter()
        .any(|&i| matches!(tcx.kind(i), TyKind::Adt(a, _) if a == eq));
    writes && tcx.find_method(adt, args, intern("equals")).is_none()
}

/// The first field of class `adt`, its bases' included, whose type has no `==`
/// for a synthesised memberwise `equals` to use (S:640), with that type.
fn field_without_eq(tcx: &Tcx, adt: AdtId) -> Option<(Symbol, Ty)> {
    let class = tcx.adt(adt).as_class()?;
    let module = tcx.def(tcx.adt(adt).def).module;
    let args = tcx.list(match tcx.kind(tcx.adt_identity(adt)) {
        TyKind::Adt(_, args) => args,
        _ => return None,
    });
    let args = tcx.intern_list(&args);
    (0..class.fields.len()).find_map(|i| {
        let ty = tcx.field_ty(adt, None, enrang_hir::FieldIdx(i as u32), args);
        (!has_eq(tcx, ty, module, 0)).then(|| (class.fields[i].name, ty))
    })
}

/// Whether `==` compares two values of `t` (S:640, S:688): numbers, `bool`,
/// `string`, raw pointers, payload-free enums, classes that implement `Eq` or have
/// an `equals`, and nullables, references and tuples of those.
fn has_eq(tcx: &Tcx, t: Ty, module: enrang_hir::ModuleId, depth: u32) -> bool {
    if depth > 16 {
        return true;
    }
    match tcx.kind(t) {
        TyKind::Bool
        | TyKind::Int(_)
        | TyKind::Float(_)
        | TyKind::Str
        | TyKind::Raw(_)
        | TyKind::Error => true,
        TyKind::Nullable(inner) | TyKind::Ref(inner) => has_eq(tcx, inner, module, depth + 1),
        TyKind::Tuple(parts) => tcx
            .list(parts)
            .iter()
            .all(|&p| has_eq(tcx, p, module, depth + 1)),
        TyKind::Param(p) => tcx.param_bounded_by(p, &ParamEnv::empty(), LangItem::Eq),
        TyKind::Adt(adt, _) => {
            if let AdtKind::Enum(e) = &tcx.adt(adt).kind
                && e.is_payload_free()
            {
                return true;
            }
            let eq = tcx.lang_adt(LangItem::Eq);
            let mut cur = Some(adt);
            let mut steps = 0;
            while let Some(c) = cur {
                let Some(class) = tcx.adt(c).as_class() else {
                    break;
                };
                if class
                    .implements
                    .iter()
                    .any(|&i| matches!(tcx.kind(i), TyKind::Adt(x, _) if Some(x) == eq))
                {
                    return true;
                }
                steps += 1;
                if steps > 64 {
                    break;
                }
                cur = class.base.and_then(|b| match tcx.kind(b) {
                    TyKind::Adt(x, _) => Some(x),
                    _ => None,
                });
            }
            tcx.member(t, intern("equals"), module).is_some()
        }
        _ => tcx.member(t, intern("equals"), module).is_some(),
    }
}

/// What lookup on a type itself finds of one name.
enum Found {
    Field,
    Methods(Vec<FoundMethod>),
}

/// Lookup on `ty` itself (S:607 without `Box` auto-deref): own and inherited
/// members, then the members of every `extend` block whose pattern matches. A user
/// module's import closure holds every library module (plan d.3), and only the
/// library may write `extend`, so every block counts.
fn lookup(tcx: &Tcx, ty: Ty, name: Symbol, from: enrang_hir::ModuleId) -> Option<Found> {
    let mut methods = match tcx.member(ty, name, from).map(|m| m.kind) {
        Some(MemberKind::Field { .. }) => return Some(Found::Field),
        Some(MemberKind::Methods(methods)) => methods,
        None => Vec::new(),
    };
    for ext in tcx.extends() {
        let Some(args) = tcx.match_extend(ext, ty) else {
            continue;
        };
        for &m in &ext.members {
            if tcx.def(m).name() == Some(name) && !methods.iter().any(|f| f.def == m) {
                methods.push(FoundMethod {
                    def: m,
                    owner: ext.def,
                    args,
                });
            }
        }
    }
    match methods.is_empty() {
        true => None,
        false => Some(Found::Methods(methods)),
    }
}

/// One interface member `m` against what lookup on `ty` finds: the member that
/// meets it, if its signature could be read.
fn member(
    tcx: &Tcx,
    ty: Ty,
    m: DefId,
    name: Symbol,
    iface_args: &[Ty],
) -> Result<Option<DefId>, Unmet> {
    let Some(want) = view(tcx, m, iface_args, Some(ty)) else {
        return Ok(None);
    };
    let from = tcx.def(m).module;
    let methods = match lookup(tcx, ty, name, from) {
        Some(Found::Methods(methods)) => methods,
        Some(Found::Field) => return Err(Unmet::new(Some(m), name, Clause::Field, None)),
        None => {
            let through_box = match tcx.kind(ty) {
                TyKind::Boxed(inner) => lookup(tcx, inner, name, from).is_some(),
                _ => false,
            };
            let clause = match through_box {
                true => Clause::OnlyThroughBox,
                false => Clause::Missing,
            };
            return Err(Unmet::new(Some(m), name, clause, None));
        }
    };
    let want_sig = tcx.sig(m);
    let mut failed: Option<(Clause, DefId)> = None;
    let mut static_only: Option<DefId> = None;
    for found in &methods {
        let args = tcx.list(found.args).to_vec();
        let Some(have) = view(tcx, found.def, &args, Some(ty)) else {
            continue;
        };
        let same = same_params(tcx, &want, &have)
            && same_ret(tcx, &want, &have)
            && same_bounds(tcx, &want, &have);
        if !same {
            continue;
        }
        if is_static(tcx, m) != is_static(tcx, found.def) {
            static_only.get_or_insert(found.def);
            continue;
        }
        let sig = tcx.sig(found.def);
        let clause = match tcx.def(found.def).vis {
            Vis::Private => Some(Clause::Private),
            Vis::Protected => Some(Clause::Protected),
            Vis::Public if want_sig.unsafety && !sig.unsafety => Some(Clause::NotUnsafe),
            Vis::Public if !want_sig.unsafety && sig.unsafety => Some(Clause::Unsafe),
            Vis::Public if sig.requires != FeatureSet::EMPTY => Some(Clause::Requires),
            Vis::Public => None,
        };
        match clause {
            None => return Ok(Some(found.def)),
            Some(clause) => {
                failed.get_or_insert((clause, found.def));
            }
        }
    }
    Err(match (failed, static_only) {
        (Some((clause, found)), _) => Unmet::new(Some(m), name, clause, Some(found)),
        (None, Some(found)) => {
            let mut unmet = Unmet::new(Some(m), name, Clause::Static, Some(found));
            if is_static(tcx, m) {
                unmet.reason = format!("`{name}` is not `static`");
            }
            unmet
        }
        (None, None) => Unmet::new(
            Some(m),
            name,
            Clause::Signature,
            methods.first().map(|f| f.def),
        ),
    })
}

/// A class bound (S:764): the class itself or a subclass, at the same arguments;
/// a parameter whose class bound is one of those.
fn class_bound(tcx: &Tcx, ty: Ty, adt: AdtId, args: TyList, env: &ParamEnv) -> Result<(), Unmet> {
    let ok = match tcx.kind(ty) {
        TyKind::Adt(c, cargs) => reaches(tcx, c, cargs, adt, args),
        TyKind::Param(p) => tcx
            .param(p)
            .bounds
            .iter()
            .copied()
            .chain(env.bounds_of(p))
            .any(|b| match tcx.bound(b) {
                Bound::Class {
                    adt: c,
                    args: cargs,
                } => reaches(tcx, *c, *cargs, adt, args),
                Bound::Iface { .. } => false,
            }),
        _ => false,
    };
    match ok {
        true => Ok(()),
        false => Err(Unmet::nominal(format!(
            "`{}` is not `{}` or a subclass of it",
            tcx.ty_string(ty),
            tcx.adt(adt).name
        ))),
    }
}

/// Whether class `c` at `cargs`, or a base of it, is `adt` at `args`.
fn reaches(tcx: &Tcx, c: AdtId, cargs: TyList, adt: AdtId, args: TyList) -> bool {
    let mut at = Some((c, cargs));
    let mut seen = Vec::new();
    while let Some((c, cargs)) = at {
        if seen.contains(&c) {
            return false;
        }
        seen.push(c);
        if c == adt && same_lists(tcx, cargs, args) {
            return true;
        }
        at = tcx.base_of(c, cargs);
    }
    false
}

/// A fields-only interface (S:629): each of its fields a field of the class that
/// is visible from outside it, with an equal type.
fn object(tcx: &Tcx, ty: Ty, shape: ShapeId) -> Result<(), Unmet> {
    let TyKind::Adt(adt, args) = tcx.kind(ty) else {
        return Ok(());
    };
    let Some(class) = tcx.adt(adt).as_class() else {
        return Ok(());
    };
    for &(name, want) in &tcx.shape(shape).fields {
        let field = class
            .fields
            .iter()
            .enumerate()
            .rev()
            .find(|(_, f)| f.name == name && (f.declared_in == adt || f.vis != Vis::Private));
        let Some((i, field)) = field else {
            return Err(Unmet::new(None, name, Clause::Missing, None));
        };
        let clause = match field.vis {
            Vis::Private => Some(Clause::Private),
            Vis::Protected => Some(Clause::Protected),
            Vis::Public => {
                let have = tcx.field_ty(adt, None, enrang_hir::FieldIdx(i as u32), args);
                (!tcx.same_ignoring_rows(have, want)).then_some(Clause::FieldType)
            }
        };
        if let Some(clause) = clause {
            return Err(Unmet::new(None, name, clause, None));
        }
    }
    Ok(())
}

/// The `implements` list of a user class: EN0401 for what is no interface, EN0419
/// for a sealed interface, EN0416 for an unmet one; `Copy` is EN0418's.
pub(crate) fn check_implements(sema: &mut Sema, cx: &ClassAst) {
    let tcx = &*sema.tcx;
    let Some(class) = tcx.adt(cx.adt).as_class() else {
        return;
    };
    let written: Vec<(Ty, Span)> = class
        .implements
        .iter()
        .zip(&cx.decl.implements)
        .map(|(&t, ast)| (t, ast.span))
        .collect();
    let ty = tcx.adt_identity(cx.adt);
    let name = cx.decl.name.name;
    let unknown_base = sema.base_unknown(cx.adt);
    let mut diags = Vec::new();
    let mut failed = Vec::new();
    for (iface, span) in written {
        let met = satisfy(sema, ty, iface, &ParamEnv::empty(), span);
        let tcx = &*sema.tcx;
        if tcx.references_error(iface) {
            continue;
        }
        // As written: a fields-only interface's type is its object type.
        let shown = tcx.map().text(span).to_owned();
        match tcx.kind(iface) {
            TyKind::Adt(a, _) if tcx.adt(a).is_interface() => {
                let def = tcx.adt(a);
                if tcx.lang_item_of(def.def) == Some(LangItem::Copy) {
                    continue;
                }
                if def.as_interface().is_some_and(|i| i.sealed.is_some()) {
                    diags.push(
                        Diagnostic::new(
                            Code::EN0419,
                            format!("`{shown}` is sealed, so `{name}` can't implement it"),
                            span,
                            "a sealed interface",
                        )
                        .note(
                            "only the compiler's own list of types implements a sealed interface",
                        ),
                    );
                    continue;
                }
                if let Err(unmet) = met {
                    failed.push((cx.adt, a));
                    // A member missing from a class whose base is unknown may be
                    // the base's: EN0302 was reported at its `extends`.
                    if !(unknown_base && unmet.clause == Clause::Missing) {
                        diags.push(unmet_diag(tcx, name, ty, iface, &shown, span, &unmet));
                    }
                } else if tcx.lang_item_of(def.def) == Some(LangItem::Eq)
                    && synthesised_eq(tcx, ty, a)
                    && let Some((field, field_ty)) = field_without_eq(tcx, cx.adt)
                {
                    // The memberwise `equals` compares every field (S:640): one with
                    // no equality leaves nothing to synthesise (plan choice, doc gap:
                    // the docs name no code).
                    failed.push((cx.adt, a));
                    let field_shown = tcx.ty_string(field_ty);
                    let unmet = Unmet::nominal(format!(
                        "`{field}` is {} `{field_shown}`, which has no `==`",
                        crate::classes::sig::article(&field_shown)
                    ));
                    diags.push(unmet_diag(tcx, name, ty, iface, &shown, span, &unmet));
                }
            }
            TyKind::Object(_) => {
                if let Err(unmet) = met {
                    diags.push(unmet_diag(tcx, name, ty, iface, &shown, span, &unmet));
                }
            }
            _ => diags.push(Diagnostic::new(
                Code::EN0401,
                format!("mismatched types: expected an interface, found `{shown}`"),
                span,
                "`implements` takes an interface",
            )),
        }
    }
    sema.classes.failed_implements.extend(failed);
    for diag in diags {
        sema.emit(diag);
    }
}

/// EN0416 for `implements` of `iface` (spelled `shown`) by class `name`, whose
/// type is `ty`.
fn unmet_diag(
    tcx: &Tcx,
    name: Symbol,
    ty: Ty,
    iface: Ty,
    shown: &str,
    span: Span,
    unmet: &Unmet,
) -> Diagnostic {
    let mut diag = Diagnostic::new(
        Code::EN0416,
        format!("`{name}` does not satisfy `{shown}`: {}", unmet.reason),
        span,
        "required by this `implements`",
    );
    let user = |d: DefId| !tcx.module(tcx.def(d).module).library;
    if let Some(found) = unmet.found
        && user(found)
    {
        let data = tcx.def(found);
        let member = data.name().map_or_else(String::new, |n| n.to_string());
        let owner = data
            .parent
            .and_then(|p| tcx.def(p).name())
            .map_or_else(String::new, |n| format!("{n}."));
        let text = match unmet.clause {
            Clause::Private => format!("`{owner}{member}` is `private`"),
            Clause::Protected => format!("`{owner}{member}` is `protected`"),
            Clause::Unsafe => format!("`{owner}{member}` is `unsafe`"),
            Clause::NotUnsafe => format!("`{owner}{member}` is not `unsafe`"),
            Clause::Requires => format!("`{owner}{member}` has `@requires`"),
            Clause::Static
                if tcx.sig_opt(found).and_then(|s| s.receiver)
                    == Some(enrang_hir::Receiver::Static) =>
            {
                format!("`{owner}{member}` is `static`, so no value has it")
            }
            _ => format!("`{owner}{member}` is declared here"),
        };
        diag = diag.with_secondary(data.name_span, text);
    } else if let Some(m) = unmet.member
        && unmet.clause == Clause::Missing
        && user(m)
    {
        let member = tcx
            .def(m)
            .name()
            .map_or_else(String::new, |n| n.to_string());
        diag = diag.with_secondary(
            tcx.def(m).name_span,
            format!("`{shown}.{member}` is declared here"),
        );
    }
    if unmet.clause == Clause::Signature
        && let Some(m) = unmet.member
        && let TyKind::Adt(_, args) = tcx.kind(iface)
        && let Some(want) = view(tcx, m, &tcx.list(args), Some(ty))
    {
        diag = diag.note(format!("`{shown}` declares `{}`", sig_string(tcx, &want)));
    }
    diag
}
