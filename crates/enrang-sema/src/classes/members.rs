//! A user class's members (plan d.16; SPEC 4.3; A:896; owner 4D).
//!
//! - `extends` of a `final` class is EN0442 at the base.
//! - Field overrides: an `override` field names a visible inherited field and keeps
//!   its type, `readonly` and visibility, else EN0443 (which also covers a field
//!   that replaces nothing, or only a `private` base field, invisible here); a field
//!   with the name of a visible inherited one and no `override` is EN0444, and so
//!   is a parameter property of that name. A `private` base field of the name
//!   leaves a new field.
//! - Methods: an `override` method matches one visible base overload exactly, its
//!   parameter types with own type parameters by position, then its result and
//!   unsafety, else EN0443 (the first `fmt` of a chain included, S:646,
//!   since the synthesised printer is no member); a method with a visible base
//!   overload's parameters and no `override` is EN0444. A `private` base method is
//!   never replaced. A `static` method has no table slot: it never overrides, and
//!   `override` on one is EN0443. A method with a visible base method's parameters
//!   where that method is compiled once per type is EN0460 at the subclass method,
//!   whatever `override` says; an `abstract` method compiled once per type is EN0460
//!   at its declaration.
//! - A class that is not `abstract` lacking an abstract method, its own or one
//!   above it that nothing between implements, is EN0446 at the class, once, naming
//!   every such method. A `move` method with a body in an `abstract` class is
//!   warning EN0459.
//! - No constructor while a `private` field, or a field of a class with a base, has
//!   neither a written default nor a type default is EN0448 at the class.
//! - `implements Copy` with a destructor in the chain, or a field (inherited ones
//!   included) that is not Copy, is EN0418 at the `Copy` (the flag condition is
//!   phase 3's).
//! - A `destructor` declared in an interface is EN0606 at its name.

use enrang_base::{BytePos, Span, Symbol};
use enrang_diag::{Code, Diagnostic, Edit, Help};
use enrang_hir::{
    AdtId, ClassDef, ClassModifier, DefId, FieldDef, LangItem, ParamEnv, Receiver, Tcx, Ty, TyKind,
    TyList, Vis,
};
use enrang_syntax::ast;

use crate::classes::sig::{
    SigView, article, has_type_default, is_static, same_params, same_ret, view,
};
use crate::cx::Sema;
use crate::lower::types::{lower_ty, optional};

/// A user class being checked: its definition, its ADT, its AST, and the
/// definition of each AST member (`None` for a field).
#[derive(Copy, Clone)]
pub(crate) struct ClassAst<'a> {
    pub def: DefId,
    pub adt: AdtId,
    pub decl: &'a ast::ClassDecl,
    pub members: &'a [Option<DefId>],
}

/// Every member rule of one user class.
pub(crate) fn check_class(sema: &mut Sema, cx: &ClassAst) {
    let Some(class) = sema.tcx.adt(cx.adt).as_class().cloned() else {
        return;
    };
    final_base(sema, cx, &class);
    fields(sema, cx, &class);
    methods(sema, cx, &class);
    abstract_missing(sema, cx, &class);
    needs_ctor(sema, cx, &class);
    copy(sema, cx, &class);
}

/// The name of an ADT.
fn adt_name(tcx: &Tcx, adt: AdtId) -> Symbol {
    tcx.adt(adt).name
}

/// The direct base class and its arguments.
fn base(tcx: &Tcx, class: &ClassDef) -> Option<(AdtId, TyList)> {
    match tcx.kind(class.base?) {
        TyKind::Adt(b, args) => Some((b, args)),
        _ => None,
    }
}

/// The class's own type arguments, its identity.
fn identity(tcx: &Tcx, adt: AdtId) -> TyList {
    tcx.identity_args(tcx.adt(adt).generics)
}

/// Whether a definition is in a user module, where a secondary label may point.
fn in_user_code(tcx: &Tcx, def: DefId) -> bool {
    !tcx.module(tcx.def(def).module).library
}

/// EN0442 (S:584).
fn final_base(sema: &mut Sema, cx: &ClassAst, class: &ClassDef) {
    let tcx = &*sema.tcx;
    let (Some((b, _)), Some(written)) = (base(tcx, class), &cx.decl.extends) else {
        return;
    };
    let is_final = tcx
        .adt(b)
        .as_class()
        .is_some_and(|c| c.modifier == ClassModifier::Final);
    if !is_final {
        return;
    }
    let name = adt_name(tcx, b);
    sema.emit(Diagnostic::new(
        Code::EN0442,
        format!("`{name}` is `final`, so no class can extend it"),
        written.span,
        format!("`{name}` is declared `final`"),
    ));
}

/// Where `override ` goes in a member written from `member` to its name at `name`:
/// after its visibility or `abstract`, before any other modifier (SPEC 3.1's
/// order; a `static` method never replaces one, so it never needs `override`).
fn override_at(tcx: &Tcx, member: Span, name: Span) -> Option<BytePos> {
    if member.is_dummy() || name.is_dummy() || name.lo < member.lo {
        return None;
    }
    let prefix = tcx.map().text(Span {
        lo: member.lo,
        hi: name.lo,
    });
    let mut end = None;
    let mut word_start = None;
    for (i, c) in prefix
        .char_indices()
        .chain(std::iter::once((prefix.len(), ' ')))
    {
        let in_word = c.is_alphanumeric() || c == '_';
        match (in_word, word_start) {
            (true, None) => word_start = Some(i),
            (false, Some(start)) => {
                if matches!(
                    &prefix[start..i],
                    "public" | "private" | "protected" | "abstract"
                ) {
                    end = Some(i);
                }
                word_start = None;
            }
            _ => {}
        }
    }
    let end = end?;
    let skip = prefix[end..].len() - prefix[end..].trim_start().len();
    Some(BytePos(member.lo.0 + (end + skip) as u32))
}

/// EN0444's help: write `override`.
fn override_help(tcx: &Tcx, member: Span, name: Span) -> Help {
    match override_at(tcx, member, name) {
        Some(at) => Help::suggest("add `override`", vec![Edit::insert(at, "override ")]),
        None => Help::text("add `override`"),
    }
}

/// Field overrides and fields hiding inherited ones (EN0443, EN0444).
fn fields(sema: &mut Sema, cx: &ClassAst, class: &ClassDef) {
    let Some(at) = sema.decls.scopes.get(&cx.def).copied() else {
        return;
    };
    let inherited = &class.fields[..class.own_from as usize];
    let class_name = cx.decl.name.name;
    let base_name = base(sema.tcx, class).map(|(b, _)| adt_name(sema.tcx, b));
    for member in &cx.decl.members {
        match &member.kind {
            ast::ClassMemberKind::Field(f) => {
                let name = f.name.name;
                let visible = inherited
                    .iter()
                    .find(|old| old.name == name && old.vis != Vis::Private);
                let hidden = inherited
                    .iter()
                    .find(|old| old.name == name && old.vis == Vis::Private);
                match (f.is_override, visible) {
                    // The field may be the unknown base's (EN0302 at `extends`).
                    (true, None) if hidden.is_none() && sema.base_unknown(cx.adt) => {}
                    (true, None) => {
                        let label = match (base_name, hidden) {
                            (None, _) => format!("`{class_name}` extends no class"),
                            (Some(_), Some(old)) => format!(
                                "`{}.{name}` is private, so `{class_name}` can't see it",
                                adt_name(sema.tcx, old.declared_in)
                            ),
                            (Some(_), None) => {
                                format!("no class above `{class_name}` has a field `{name}`")
                            }
                        };
                        sema.emit(Diagnostic::new(
                            Code::EN0443,
                            overrides_nothing(name, base_name),
                            f.name.span,
                            label,
                        ));
                    }
                    (true, Some(old)) => {
                        let old = old.clone();
                        let lowered = lower_ty(sema, at, &f.ty);
                        let ty = match f.optional {
                            true => optional(sema, lowered),
                            false => lowered,
                        };
                        field_mismatch(sema, f, ty, &old, base_name);
                    }
                    (false, Some(old)) => {
                        let owner = adt_name(sema.tcx, old.declared_in);
                        let help = override_help(sema.tcx, member.span, f.name.span);
                        sema.emit(
                            Diagnostic::new(
                                Code::EN0444,
                                format!("`{name}` replaces `{owner}.{name}` without `override`"),
                                f.name.span,
                                format!("`{owner}` already has a field `{name}`"),
                            )
                            .with_help(help),
                        );
                    }
                    (false, None) => {}
                }
            }
            ast::ClassMemberKind::Constructor(c) => {
                for p in c.params.iter().filter(|p| p.property.is_some()) {
                    let name = p.name.name;
                    let Some(old) = inherited
                        .iter()
                        .find(|old| old.name == name && old.vis != Vis::Private)
                    else {
                        continue;
                    };
                    let owner = adt_name(sema.tcx, old.declared_in);
                    sema.emit(
                        Diagnostic::new(
                            Code::EN0444,
                            format!("`{name}` replaces `{owner}.{name}` without `override`"),
                            p.name.span,
                            format!("`{owner}` already has a field `{name}`"),
                        )
                        .with_help(Help::text(format!(
                            "a parameter property can't override: rename it, or assign `this.{name}` in the constructor's body"
                        ))),
                    );
                }
            }
            _ => {}
        }
    }
}

/// `` `sound` overrides nothing in `Animal` ``.
fn overrides_nothing(name: Symbol, base: Option<Symbol>) -> String {
    match base {
        Some(base) => format!("`{name}` overrides nothing in `{base}`"),
        None => format!("`{name}` overrides nothing"),
    }
}

/// EN0443 for an `override` field whose type (`ty`, as written), `readonly` or
/// visibility differs from the inherited field `old` (S:585).
fn field_mismatch(
    sema: &mut Sema,
    f: &ast::FieldDecl,
    ty: Ty,
    old: &FieldDef,
    base: Option<Symbol>,
) {
    let tcx = &*sema.tcx;
    let name = f.name.name;
    let owner = adt_name(tcx, old.declared_in);
    let written_vis = match f.visibility {
        Some(ast::Visibility::Private) => Vis::Private,
        Some(ast::Visibility::Protected) => Vis::Protected,
        Some(ast::Visibility::Public) | None => Vis::Public,
    };
    let known = !tcx.references_error(ty) && !tcx.references_error(old.ty);
    let label = if known && !tcx.same_ignoring_rows(ty, old.ty) {
        format!("`{owner}.{name}` has type `{}`", tcx.ty_string(old.ty))
    } else if f.is_readonly != old.readonly {
        match old.readonly {
            true => format!("`{owner}.{name}` is `readonly`"),
            false => format!("`{owner}.{name}` is not `readonly`"),
        }
    } else if f.visibility.is_some() && written_vis != old.vis {
        let vis = match old.vis {
            Vis::Public => "public",
            Vis::Private => "private",
            Vis::Protected => "protected",
        };
        format!("`{owner}.{name}` is `{vis}`")
    } else {
        return;
    };
    let mut diag = Diagnostic::new(
        Code::EN0443,
        overrides_nothing(name, base),
        f.name.span,
        label,
    )
    .note("an `override` keeps the inherited field's type, `readonly` and visibility");
    if !old.span.is_dummy() && in_user_code(tcx, tcx.adt(old.declared_in).def) {
        diag = diag.with_secondary(old.span, format!("`{owner}.{name}` is declared here"));
    }
    sema.emit(diag);
}

/// One method of a class above, as the class being checked sees it.
struct BaseMethod {
    view: SigView,
    class: AdtId,
}

/// The visible methods named `name` above class `adt`, nearest first, one per
/// parameter list (a nearer one overrides a farther one), with no `static` and no
/// `private` one; and the first `private` one met, for a label.
fn base_methods(tcx: &Tcx, adt: AdtId, name: Symbol) -> (Vec<BaseMethod>, Option<DefId>) {
    let mut out: Vec<BaseMethod> = Vec::new();
    let mut private = None;
    let mut at = tcx.base_of(adt, identity(tcx, adt));
    let mut seen = vec![adt];
    while let Some((b, args)) = at {
        if seen.contains(&b) {
            break;
        }
        seen.push(b);
        let args_v = tcx.list(args).to_vec();
        let methods = tcx
            .adt(b)
            .as_class()
            .map(|c| c.methods.clone())
            .unwrap_or_default();
        for m in methods {
            let data = tcx.def(m);
            if data.name() != Some(name) || is_static(tcx, m) {
                continue;
            }
            if data.vis == Vis::Private {
                private.get_or_insert(m);
                continue;
            }
            let Some(v) = view(tcx, m, &args_v, None) else {
                continue;
            };
            if !out.iter().any(|o| same_params(tcx, &o.view, &v)) {
                out.push(BaseMethod { view: v, class: b });
            }
        }
        at = tcx.base_of(b, args);
    }
    (out, private)
}

/// `Animal.speak`.
fn qualified(tcx: &Tcx, class: AdtId, def: DefId) -> String {
    let name = tcx
        .def(def)
        .name()
        .map_or_else(String::new, |n| n.to_string());
    format!("{}.{name}", adt_name(tcx, class))
}

/// The method rules (EN0443, EN0444, EN0459, EN0460).
fn methods(sema: &mut Sema, cx: &ClassAst, class: &ClassDef) {
    for (member, def) in cx.decl.members.iter().zip(cx.members) {
        let (ast::ClassMemberKind::Method(m), Some(def)) = (&member.kind, def) else {
            continue;
        };
        method(sema, cx, class, member, m, *def);
    }
}

fn method(
    sema: &mut Sema,
    cx: &ClassAst,
    class: &ClassDef,
    member: &ast::ClassMember,
    m: &ast::MethodDecl,
    def: DefId,
) {
    let tcx = &*sema.tcx;
    let name = m.name.name;
    let class_name = cx.decl.name.name;
    let base_name = base(tcx, class).map(|(b, _)| adt_name(tcx, b));
    let mut diags = Vec::new();
    if is_static(tcx, def) {
        if m.is_override {
            diags.push(Diagnostic::new(
                Code::EN0443,
                overrides_nothing(name, base_name),
                m.name.span,
                "a `static` method has no method-table slot to replace",
            ));
        }
        for diag in diags {
            sema.emit(diag);
        }
        return;
    }
    let receiver = tcx.sig_opt(def).and_then(|s| s.receiver);
    if class.modifier == ClassModifier::Abstract
        && receiver == Some(Receiver::Move)
        && m.body.is_some()
    {
        diags.push(
            Diagnostic::new(
                Code::EN0459,
                "`move` method of an abstract class can never run",
                m.name.span,
                format!(
                    "no object is ever exactly {} `{class_name}`",
                    crate::classes::sig::article(class_name.as_str())
                ),
            )
            .with_help(Help::text("declare it `abstract`")),
        );
    }
    if m.is_abstract
        && let Some(why) = tcx.once_per_type(def)
    {
        diags.push(
            Diagnostic::new(
                Code::EN0460,
                why.message(name),
                m.name.span,
                "no subclass could implement it",
            )
            .with_help(Help::text(format!("give `{name}` a body"))),
        );
    }
    let identity = tcx.list(identity(tcx, cx.adt)).to_vec();
    if let Some(mine) = view(tcx, def, &identity, None) {
        let (cands, private) = base_methods(tcx, cx.adt, name);
        let exact = cands.iter().find(|c| same_params(tcx, &mine, &c.view));
        let once = exact.and_then(|c| tcx.once_per_type(c.view.def));
        match (exact, once) {
            (Some(c), Some(why)) => {
                let base = qualified(tcx, c.class, c.view.def);
                let mut diag = Diagnostic::new(
                    Code::EN0460,
                    why.message(name),
                    m.name.span,
                    format!("`{base}` is compiled once per type, so it has no method-table slot"),
                )
                .with_help(Help::text(format!(
                    "give {class_name}'s method another name"
                )));
                if in_user_code(tcx, c.view.def) {
                    diag = diag.with_secondary(
                        tcx.def(c.view.def).name_span,
                        format!("`{base}` is declared here"),
                    );
                }
                diags.push(diag);
            }
            (Some(c), None) if m.is_override => {
                let base = qualified(tcx, c.class, c.view.def);
                let (mine_sig, base_sig) = (tcx.sig(def), tcx.sig(c.view.def));
                let label = if !same_ret(tcx, &c.view, &mine) {
                    Some(format!("`{base}` returns `{}`", tcx.ty_string(c.view.ret)))
                } else if mine_sig.unsafety != base_sig.unsafety {
                    Some(match base_sig.unsafety {
                        true => format!("`{base}` is `unsafe`"),
                        false => format!("`{base}` is not `unsafe`"),
                    })
                } else {
                    None
                };
                if let Some(label) = label {
                    let mut diag = Diagnostic::new(
                        Code::EN0443,
                        overrides_nothing(name, base_name),
                        m.name.span,
                        label,
                    );
                    if in_user_code(tcx, c.view.def) {
                        diag = diag.with_secondary(
                            tcx.def(c.view.def).name_span,
                            format!("`{base}` is declared here"),
                        );
                    }
                    diags.push(diag);
                }
            }
            (Some(c), None) => {
                let base = qualified(tcx, c.class, c.view.def);
                let mut diag = Diagnostic::new(
                    Code::EN0444,
                    format!("`{name}` replaces `{base}` without `override`"),
                    m.name.span,
                    format!("`{base}` has the same parameters"),
                )
                .with_help(override_help(tcx, member.span, m.name.span));
                if in_user_code(tcx, c.view.def) {
                    diag = diag.with_secondary(
                        tcx.def(c.view.def).name_span,
                        format!("`{base}` is declared here"),
                    );
                }
                diags.push(diag);
            }
            // The method may be the unknown base's (EN0302 at `extends`).
            (None, _) if m.is_override && cands.is_empty() && sema.base_unknown(cx.adt) => {}
            (None, _) if m.is_override => {
                let label = match (base_name, cands.first(), private) {
                    (None, _, _) => format!("`{class_name}` extends no class"),
                    (Some(_), Some(_), _) => {
                        format!("no `{name}` above `{class_name}` takes these parameters")
                    }
                    (Some(_), None, Some(p)) => {
                        let owner = tcx
                            .def(p)
                            .parent
                            .and_then(|d| tcx.adt_of(d))
                            .map_or_else(String::new, |a| adt_name(tcx, a).to_string());
                        format!("`{owner}.{name}` is private, so `{class_name}` can't see it")
                    }
                    (Some(_), None, None) if name.as_str() == "fmt" => format!(
                        "no class above `{class_name}` writes `fmt`: the printer is synthesised, not a member"
                    ),
                    (Some(_), None, None) => match static_above(tcx, cx.adt, name) {
                        // A `static` method has no method-table slot to replace.
                        Some(owner) => format!(
                            "`{owner}.{name}` is `static`, so it has no method-table slot to replace"
                        ),
                        None => format!("no class above `{class_name}` has a method `{name}`"),
                    },
                };
                let mut diag = Diagnostic::new(
                    Code::EN0443,
                    overrides_nothing(name, base_name),
                    m.name.span,
                    label,
                );
                if let Some(c) = cands.first()
                    && in_user_code(tcx, c.view.def)
                {
                    let base = qualified(tcx, c.class, c.view.def);
                    diag = diag.with_secondary(
                        tcx.def(c.view.def).name_span,
                        format!("`{base}` is declared here"),
                    );
                }
                diags.push(diag);
            }
            (None, _) => {}
        }
    }
    for diag in diags {
        sema.emit(diag);
    }
}

/// The class above `adt` that declares a `static` method `name`, if one does.
fn static_above(tcx: &Tcx, adt: AdtId, name: Symbol) -> Option<Symbol> {
    let mut at = tcx.adt(adt).as_class()?.base;
    let mut steps = 0;
    while let Some(base) = at {
        let TyKind::Adt(b, _) = tcx.kind(base) else {
            return None;
        };
        let class = tcx.adt(b).as_class()?;
        if class
            .methods
            .iter()
            .any(|&m| tcx.def(m).name() == Some(name) && is_static(tcx, m))
        {
            return Some(adt_name(tcx, b));
        }
        steps += 1;
        if steps > 64 {
            return None;
        }
        at = class.base;
    }
    None
}

/// EN0446 (S:586): the abstract methods a class that is not `abstract` leaves
/// unimplemented, its own included. Walking up from the class, a method hides a
/// farther one with its parameters; a `private` abstract method above can never be
/// implemented. Methods are matched by name and parameters.
fn abstract_missing(sema: &mut Sema, cx: &ClassAst, class: &ClassDef) {
    if class.modifier == ClassModifier::Abstract {
        return;
    }
    let tcx = &*sema.tcx;
    let mut entries: Vec<(SigView, bool, AdtId)> = Vec::new();
    let mut at = Some((cx.adt, identity(tcx, cx.adt)));
    let mut seen = Vec::new();
    while let Some((a, args)) = at {
        if seen.contains(&a) {
            break;
        }
        seen.push(a);
        let args_v = tcx.list(args).to_vec();
        let methods = tcx
            .adt(a)
            .as_class()
            .map(|c| c.methods.clone())
            .unwrap_or_default();
        for m in methods {
            if is_static(tcx, m) {
                continue;
            }
            let data = tcx.def(m);
            let Some(v) = view(tcx, m, &args_v, None) else {
                continue;
            };
            if a != cx.adt && data.vis == Vis::Private {
                if data.flags.is_abstract {
                    entries.push((v, true, a));
                }
                continue;
            }
            let hidden = entries
                .iter()
                .any(|(e, _, _)| tcx.def(e.def).name() == data.name() && same_params(tcx, e, &v));
            if hidden {
                continue;
            }
            entries.push((v, data.flags.is_abstract, a));
        }
        at = tcx.base_of(a, args);
    }
    let missing: Vec<(DefId, AdtId)> = entries
        .iter()
        .filter(|(_, is_abstract, _)| *is_abstract)
        .map(|(v, _, a)| (v.def, *a))
        .collect();
    if missing.is_empty() {
        return;
    }
    let names: Vec<String> = missing
        .iter()
        .map(|&(def, a)| format!("`{}`", qualified(tcx, a, def)))
        .collect();
    let list = match names.as_slice() {
        [one] => one.clone(),
        [init @ .., last] => format!("{} and {last}", init.join(", ")),
        [] => return,
    };
    let class_name = cx.decl.name.name;
    let pronoun = if missing.len() == 1 { "it" } else { "them" };
    // An abstract method of the class's own is given a body, never overridden.
    // A `private` abstract method above is invisible to every subclass: no
    // `override` can reach it (S:584).
    let private_above = missing
        .iter()
        .find(|&&(def, a)| a != cx.adt && tcx.def(def).vis == Vis::Private);
    let help = match (private_above, missing.iter().any(|&(_, a)| a == cx.adt)) {
        (Some(&(def, a)), _) => format!(
            "`{}` is `private`, so no subclass can implement it: declare `{class_name}` `abstract`, or make it `protected` in `{}`",
            qualified(tcx, a, def),
            adt_name(tcx, a)
        ),
        (None, true) => format!("declare `{class_name}` `abstract`, or give {pronoun} a body"),
        (None, false) => {
            format!("implement {pronoun} with `override`, or declare `{class_name}` `abstract`")
        }
    };
    let mut diag = Diagnostic::new(
        Code::EN0446,
        format!("`{class_name}` does not implement {list}"),
        cx.decl.name.span,
        format!("`{class_name}` is not `abstract`"),
    )
    .with_help(Help::text(help));
    for &(def, a) in &missing {
        if in_user_code(tcx, def) {
            diag = diag.with_secondary(
                tcx.def(def).name_span,
                format!("`{}` is declared `abstract` here", qualified(tcx, a, def)),
            );
        }
    }
    sema.emit(diag);
}

/// EN0448 (S:582, S:587): no constructor, while a `private` field, or a field of a
/// class with a base, can start at no default.
fn needs_ctor(sema: &mut Sema, cx: &ClassAst, class: &ClassDef) {
    if !class.ctors.is_empty() {
        return;
    }
    let tcx = &*sema.tcx;
    let class_name = cx.decl.name.name;
    let subclass = class.base.is_some();
    for (_, f) in class.own_fields() {
        if f.has_default || has_type_default(tcx, f.ty) {
            continue;
        }
        let label = match (f.vis, subclass) {
            (Vis::Private, _) => format!("`{}` is `private`, so no named form can set it", f.name),
            (_, true) => "a subclass with no constructor needs a default for each field of its own"
                .to_owned(),
            (_, false) => continue,
        };
        let mut diag = Diagnostic::new(
            Code::EN0448,
            format!(
                "`{class_name}` needs a constructor: `{}` has no default",
                f.name
            ),
            cx.decl.name.span,
            label,
        )
        .with_help(Help::text(format!(
            "give `{}` a default, or write a constructor that sets it",
            f.name
        )));
        if !f.span.is_dummy() {
            diag = diag.with_secondary(
                f.span,
                format!(
                    "`{}` has type `{}`, which has no default",
                    f.name,
                    tcx.ty_string(f.ty)
                ),
            );
        }
        sema.emit(diag);
        return;
    }
}

/// EN0418's phase 2 part (S:589, S:637, A:896): no destructor in the chain, every
/// field Copy.
fn copy(sema: &mut Sema, cx: &ClassAst, class: &ClassDef) {
    if !class.copy {
        return;
    }
    let tcx = &*sema.tcx;
    let copy = tcx.lang_adt(LangItem::Copy);
    if !class
        .implements
        .iter()
        .any(|t| matches!(tcx.kind(*t), TyKind::Adt(a, _) if Some(a) == copy))
    {
        return;
    }
    // "EN0418 at `Snapshot`" (S:589, T:996): the class that may not be Copy.
    let span = cx.decl.name.span;
    let class_name = cx.decl.name.name;
    let help = Help::text(format!(
        "remove `implements Copy`; to copy {} `{class_name}`, write `clone()`",
        crate::classes::sig::article(class_name.as_str())
    ));
    if let Some(dtor) = tcx.class_dtor(cx.adt, identity(tcx, cx.adt)) {
        let owner = tcx
            .def(dtor)
            .parent
            .and_then(|p| tcx.def(p).name())
            .unwrap_or(class_name);
        sema.emit(
            Diagnostic::new(
                Code::EN0418,
                format!(
                    "`{owner}`'s destructor runs for every `{class_name}`, so copying one would run it twice"
                ),
                span,
                "a Copy class can have no destructor",
            )
            .with_help(help),
        );
        return;
    }
    for f in &class.fields {
        if tcx.is_copy(f.ty, &ParamEnv::empty()) {
            continue;
        }
        let shown = tcx.ty_string(f.ty);
        let mut diag = Diagnostic::new(
            Code::EN0418,
            format!(
                "`{class_name}` can't be Copy: `{}` is {} `{shown}`",
                f.name,
                article(&shown)
            ),
            span,
            format!("`{}` is not Copy", f.name),
        )
        .with_help(help);
        if !f.span.is_dummy() && in_user_code(tcx, tcx.adt(f.declared_in).def) {
            diag = diag.with_secondary(f.span, format!("`{}` is declared here", f.name));
        }
        sema.emit(diag);
        return;
    }
}

/// EN0606 (S:648): a `destructor` declared in a user interface.
pub(crate) fn check_interface(sema: &mut Sema, decl: &ast::InterfaceDecl) {
    for member in &decl.members {
        let ast::IfaceMember::Method(m) = member else {
            continue;
        };
        if m.name.name.as_str() != "destructor" {
            continue;
        }
        sema.emit(
            Diagnostic::new(
                Code::EN0606,
                "an interface can't declare a `destructor`",
                m.name.span,
                "a destructor is never a member",
            )
            .with_help(Help::text(
                "remove it: a class's own `destructor` runs by itself, and `dispose(x)` ends a value early",
            )),
        );
    }
}
