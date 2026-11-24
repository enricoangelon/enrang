//! Interface types in bodies (plan d.12; SPEC 4.4, 4.5 C22; A:894; owner 4C).
//!
//! **A class of its own.** Each interface-typed parameter is its implicit `X extends
//! I` (D5, lowered with the signature), and each two-word `&I` value a member is
//! called on, read from a local, a field, a result, a box or a nullable, gets a fresh
//! `Implicit::Opaque` parameter bounded by `I` (`self_of`), so `Self` in that member
//! means that value's class. A value standing for one class where another's is
//! expected, by value or behind `&`, is EN0401 `` `b` may hold another class than
//! `a` ``, with `help: use one type for both: same<T extends Eq>(a: &T, b: &T)` when
//! both are parameters of the function (S2-09-self, VI-03-swap), else `help: use one
//! type for both, a type parameter `T extends Eq`` (plan choice).
//!
//! **C22** (`coerce_iface`, once unification and the other chains failed): `&C` to
//! `&I` records `RefToInterface`, the two-word form, for a class, enum or other value
//! type that satisfies `I` (4D's `satisfies`, the conversion then given to the one
//! satisfaction routine, which records what it relies on) and for a type parameter
//! bounded by `I`; `Box<C>` to `Box<I>` records `BoxToInterface`, a `Box<string>` included. A
//! borrowing class there is EN0701 `` a `Speaker` can't hold a `View`, because `View`
//! holds a reference `` (S:631, A:892), and a `&string`, whole, a part, a literal or a
//! parameter, never becomes an `&I`: EN0401 `` a `&string` can't become a
//! `&Measured`, because it may be a part of a string `` with the two helps of S:631
//! (VI-01-part). A value converted to a by-value `I` outside a parameter is left to
//! the position check of its written type, which reports EN1006 once (plan choice),
//! and so are a written `Box<I>` and a written `&I` that needs the two-word form of an
//! interface no table can serve (`two_word_need`, for that check). A by-value
//! interface value, as `b.unbox()` on a `Box<Speaker>` gives, is EN1006 where it is
//! used as a statement or meets a site of another type (T:862).
//!
//! **EN1006** is SPEC 16's: one head, `an interface type by value outside a parameter
//! is not supported yet`, with a note naming the case (`iface_unsupported`).
//!
//! **Tables.** An interface none of whose members needs the class (one taking or
//! returning `Self` by value, or compiled once per type: with type parameters of its
//! own, a by-value interface parameter or an object-type parameter) can be reached
//! through its two-word form; `class_need` names the member that cannot (A:894).
//!
//! **For generic calls** (4A's binding of an implicit interface parameter): a by-value
//! `I` parameter takes a whole argument of one class, so `by_value_iface_arg` types a
//! ternary, `??` or `match` argument branch by branch and reports EN1006 with `` note:
//! this `Speaker` may be a `Dog` or a `Robot`, so its class isn't known `` and `help:
//! call relay in each branch` when their classes differ (VI-03-branches);
//! `iface_type_arg` is EN1006 for a type parameter bound to an interface, with
//! A:894's helps for `&*b` arguments (`swap the boxes: mem.swap(&a, &b)`, `show(&a)`,
//! S2-10-swap); `report_part_of_string` is the `&string` EN0401 (VI-01-part).

use enrang_base::{Span, Symbol};
use enrang_diag::{Code, Diagnostic, Help};
use enrang_hir::{
    self as hir, Adjust, AdtId, Bound, ConstValue, DefId, ExprKind, Implicit, ParamId, Tcx, Ty,
    TyKind, TyParamDef,
};
use enrang_syntax::ast;

use crate::classes::satisfy;
use crate::typeck::expr::strip_parens;
use crate::typeck::{Expect, FnCtxt, Site};

/// SPEC 16's head of EN1006, shared by every case.
pub(crate) const IFACE_VALUE_HEAD: &str =
    "an interface type by value outside a parameter is not supported yet";

/// EN1006 at `span`, with its label, the note naming the case, and a help.
pub(crate) fn iface_unsupported(
    span: Span,
    label: impl Into<String>,
    note: impl Into<String>,
    help: Option<String>,
) -> Diagnostic {
    let diag = Diagnostic::new(Code::EN1006, IFACE_VALUE_HEAD, span, label).note(note);
    match help {
        Some(help) => diag.with_help(Help::text(help)),
        None => diag,
    }
}

/// Why a member needs the class of the value it is called on (A:894).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum ClassNeed {
    /// It takes or returns `Self` by value.
    SelfByValue,
    /// It is compiled once per type: type parameters of its own, a by-value interface
    /// parameter or an object-type parameter.
    PerType,
}

/// The member of interface `adt` that needs the class, so no table can serve it.
pub(crate) fn class_need(tcx: &Tcx, adt: AdtId) -> Option<(Symbol, ClassNeed)> {
    let iface = tcx.adt(adt).as_interface()?;
    let self_ty = tcx.mk_param(iface.self_param);
    for &m in &iface.methods {
        let Some(sig) = tcx.sig_opt(m) else {
            continue;
        };
        let Some(name) = tcx.def(m).name() else {
            continue;
        };
        if sig.ret == self_ty || sig.params.iter().any(|p| p.ty == self_ty) {
            return Some((name, ClassNeed::SelfByValue));
        }
        for &own in &tcx.generics(sig.generics).params {
            let per_type = match tcx.param(own).implicit {
                None | Some(Implicit::Shape(_)) => true,
                Some(Implicit::Interface(_)) => {
                    let by_value = tcx.mk_param(own);
                    sig.params.iter().any(|p| p.ty == by_value)
                }
                Some(Implicit::Opaque) => false,
            };
            if per_type {
                return Some((name, ClassNeed::PerType));
            }
        }
    }
    None
}

/// The note of EN1006 for interface `adt`, whose `member` needs the class.
pub(crate) fn need_note(tcx: &Tcx, adt: AdtId, member: Symbol, need: ClassNeed) -> String {
    let iface = tcx.adt(adt).name;
    match need {
        ClassNeed::SelfByValue => format!(
            "`{iface}.{member}` takes or returns `Self` by value, which can't run where the class is unknown"
        ),
        ClassNeed::PerType => format!(
            "`{iface}.{member}` is compiled once per type, so no table can hold it where the class is unknown"
        ),
    }
}

/// For the position check of written types (4E): the interface whose table a type
/// `Box<I>` (`boxed`), or `&I` / `&I | null` outside a non-null `&I` parameter, would
/// need, with the member no table can serve (S:631, A:894, T:1000, T:1007).
pub(crate) fn two_word_need(tcx: &Tcx, ty: Ty) -> Option<(AdtId, Symbol, ClassNeed)> {
    let inner = match tcx.kind(ty) {
        TyKind::Nullable(inner) => inner,
        _ => ty,
    };
    let iface = match tcx.kind(inner) {
        TyKind::Boxed(i) | TyKind::Ref(i) => i,
        _ => return None,
    };
    match tcx.kind(iface) {
        TyKind::Adt(adt, _) if tcx.is_interface_ty(iface) => {
            let (member, need) = class_need(tcx, adt)?;
            Some((adt, member, need))
        }
        _ => None,
    }
}

impl FnCtxt<'_, '_> {
    /// C22 at `to`, or the class-of-its-own, `&string` and borrowing-class errors;
    /// `None` when no interface rule applies, which leaves the mismatch to `coerce`.
    pub(crate) fn coerce_iface(
        &mut self,
        mut e: hir::Expr,
        to: Ty,
        site: Site,
    ) -> Option<hir::Expr> {
        let _ = site;
        let target = self.shallow(to);
        let from = self.shallow(e.ty);
        let tcx = &*self.sema.tcx;
        let (f, t, behind) = match (tcx.kind(from), tcx.kind(target)) {
            (TyKind::Ref(f), TyKind::Ref(t)) => (self.shallow(f), self.shallow(t), Behind::Ref),
            (TyKind::Boxed(f), TyKind::Boxed(t)) => {
                (self.shallow(f), self.shallow(t), Behind::Boxed)
            }
            _ => (from, target, Behind::Value),
        };
        if behind != Behind::Boxed && self.own_class(t).is_some() && self.stands_for_class(f) {
            self.report_other_class(&e, t);
            e.ty = self.error_ty();
            return Some(e);
        }
        // A string literal is a `&string` wherever a reference is expected (C13).
        if let (TyKind::Str, TyKind::Ref(want)) = (tcx.kind(from), tcx.kind(target))
            && matches!(e.kind, ExprKind::Const(ConstValue::Str(_)))
            && let Some(iface) = self.iface_of(self.shallow(want))
        {
            self.report_part_of_string(&e, iface);
            e.ty = self.error_ty();
            return Some(e);
        }
        if behind == Behind::Value && self.sema.tcx.is_interface_ty(f) {
            self.report_iface_value(&e);
            e.ty = self.error_ty();
            return Some(e);
        }
        let iface = self.iface_of(t)?;
        if behind == Behind::Value {
            // A by-value `I` outside a parameter: its written type is EN1006. The
            // `I` a generic instantiation gives (`new Box(v)` at `Box<I>`) still
            // takes only a value type (C22, EF-08's F1).
            if !self.satisfied(f, t) {
                return None;
            }
            if self.sema.tcx.is_borrowing(f) {
                self.report_borrowing(&e, iface, f);
                e.ty = self.error_ty();
            } else {
                self.satisfy_at(f, t, e.span);
            }
            return Some(e);
        }
        let tcx = &*self.sema.tcx;
        match tcx.kind(f) {
            TyKind::Str if behind == Behind::Ref => {
                self.report_part_of_string(&e, iface);
                e.ty = self.error_ty();
                return Some(e);
            }
            TyKind::Adt(adt, _) if tcx.adt(adt).is_interface() => return None,
            _ if !tcx.is_value_type(f) && !matches!(tcx.kind(f), TyKind::Param(_)) => {
                if !tcx.is_borrowing(f) {
                    return None;
                }
                self.report_borrowing(&e, iface, f);
                e.ty = self.error_ty();
                return Some(e);
            }
            // A parameter bounded by the interface at equal arguments (S:762).
            TyKind::Param(_) => {
                if !self.satisfied(f, t) {
                    return None;
                }
            }
            TyKind::Ref(_) | TyKind::Nullable(_) | TyKind::Infer(_) | TyKind::Closure(_) => {
                return None;
            }
            _ => {
                if !self.satisfied(f, t) {
                    return None;
                }
            }
        }
        self.satisfy_at(f, t, e.span);
        e.adjust.push(match behind {
            Behind::Boxed => Adjust::BoxToInterface,
            _ => Adjust::RefToInterface,
        });
        Some(e)
    }

    /// The class `Self` stands for in a member called on `recv`, a value of an
    /// interface type: a fresh `Implicit::Opaque` parameter bounded by it, one per
    /// value (A:894); any other receiver's own type.
    pub(crate) fn self_of(&mut self, recv: &hir::Expr) -> Ty {
        let t = self.shallow(recv.ty);
        let tcx = &*self.sema.tcx;
        let TyKind::Adt(adt, args) = tcx.kind(t) else {
            return recv.ty;
        };
        let data = tcx.adt(adt);
        if !data.is_interface() {
            return recv.ty;
        }
        let (name, owner) = (data.name, data.def);
        let bound = self.sema.tcx.define_bound(Bound::Iface { adt, args });
        let param = self.sema.tcx.define_param(TyParamDef {
            name,
            owner,
            index: 0,
            bounds: vec![bound],
            implicit: Some(Implicit::Opaque),
            span: recv.span,
        });
        self.sema.tcx.mk_param(param)
    }

    /// The interface `t` is: its ADT, when `t` is an interface type.
    fn iface_of(&self, t: Ty) -> Option<AdtId> {
        let tcx = &*self.sema.tcx;
        match tcx.kind(t) {
            TyKind::Adt(adt, _) if tcx.is_interface_ty(t) => Some(adt),
            _ => None,
        }
    }

    /// The parameter `t` is when it stands for a class of its own: an implicit
    /// interface parameter or an opaque one.
    fn own_class(&self, t: Ty) -> Option<ParamId> {
        let tcx = &*self.sema.tcx;
        let TyKind::Param(p) = tcx.kind(t) else {
            return None;
        };
        match tcx.param(p).implicit {
            Some(Implicit::Interface(adt)) if !self.is_self_param(p, adt) => Some(p),
            Some(Implicit::Opaque) => Some(p),
            _ => None,
        }
    }

    /// Whether `p` is interface `adt`'s own `Self`.
    fn is_self_param(&self, p: ParamId, adt: AdtId) -> bool {
        self.sema.tcx.adt(adt).as_interface().map(|i| i.self_param) == Some(p)
    }

    /// Whether a value of `f` stands for a class known only at run time: another
    /// interface parameter, an opaque one, or a two-word interface value.
    fn stands_for_class(&self, f: Ty) -> bool {
        self.own_class(f).is_some() || self.sema.tcx.is_interface_ty(f)
    }

    /// Whether `ty` satisfies the interface type `iface` (4D, S:611).
    fn satisfied(&self, ty: Ty, iface: Ty) -> bool {
        satisfy::satisfies(self.sema.tcx, ty, iface, &self.env).is_ok()
    }

    /// A C22 conversion of `ty` to `iface` at `site` uses `ty` as `iface`: the one
    /// satisfaction routine records what the satisfaction relies on (SPEC 4.4).
    fn satisfy_at(&mut self, ty: Ty, iface: Ty, site: Span) {
        let _ = satisfy::satisfy(self.sema, ty, iface, &self.env, site);
    }

    /// EN0401: a value of one class where another's is expected (A:894).
    fn report_other_class(&mut self, e: &hir::Expr, target: Ty) {
        let value = self.snippet(e.span);
        let Some(p) = self.own_class(target) else {
            return;
        };
        let other = self.holder_name(target, p);
        let iface = self.bound_iface_text(p);
        let mut diag = Diagnostic::new(
            Code::EN0401,
            format!("`{value}` may hold another class than `{other}`"),
            e.span,
            "each interface value stands for a class of its own",
        );
        let from = match self.sema.tcx.kind(self.shallow(e.ty)) {
            TyKind::Ref(inner) => self.shallow(inner),
            _ => self.shallow(e.ty),
        };
        let help = match self.own_class(from) {
            Some(q) => self.one_type_help(p, q, &iface),
            None => None,
        };
        diag = diag.with_help(Help::text(help.unwrap_or_else(|| {
            format!("use one type for both, a type parameter `T extends {iface}`")
        })));
        self.sema.emit(diag);
    }

    /// The name of what holds a value of class `p` (`t` is `p` itself): the
    /// parameter of that type, or the value an opaque parameter was made for.
    fn holder_name(&self, t: Ty, p: ParamId) -> String {
        let tcx = &*self.sema.tcx;
        let named = self.params.iter().find_map(|&local| {
            let decl = &self.locals[local];
            let ty = self.shallow(decl.ty);
            let inner = match tcx.kind(ty) {
                TyKind::Ref(inner) => self.shallow(inner),
                _ => ty,
            };
            (inner == t).then_some(decl.name).flatten()
        });
        match named {
            Some(name) => name.as_str().to_owned(),
            None => self.snippet(tcx.param(p).span),
        }
    }

    /// The interface implicit parameter `p` stands for, as written: `Eq`.
    fn bound_iface_text(&self, p: ParamId) -> String {
        let tcx = &*self.sema.tcx;
        let param = tcx.param(p);
        let adt = match param.implicit {
            Some(Implicit::Interface(adt)) => Some(adt),
            _ => param.bounds.first().map(|&b| tcx.bound(b).adt()),
        };
        match adt {
            Some(adt) => {
                let args = param
                    .bounds
                    .iter()
                    .map(|&b| tcx.bound(b))
                    .find(|b| b.adt() == adt)
                    .map_or_else(|| tcx.empty_list(), |b| b.args());
                tcx.ty_string(tcx.intern_ty(TyKind::Adt(adt, args)))
            }
            None => tcx.param(p).name.as_str().to_owned(),
        }
    }

    /// `help: use one type for both: same<T extends Eq>(a: &T, b: &T)`, when `p` and
    /// `q` are both implicit parameters of this function's signature.
    fn one_type_help(&self, p: ParamId, q: ParamId, iface: &str) -> Option<String> {
        let hir::BodyOwner::Fn(def) = self.owner else {
            return None;
        };
        if !self.arrow_stack.is_empty() {
            return None;
        }
        let tcx = &*self.sema.tcx;
        let sig = tcx.sig_opt(def)?;
        let own = &tcx.generics(sig.generics).params;
        if !own.contains(&p) || !own.contains(&q) {
            return None;
        }
        let name = tcx.def(def).name()?;
        let (pt, qt) = (tcx.mk_param(p), tcx.mk_param(q));
        let params: Vec<String> = sig
            .params
            .iter()
            .map(|param| {
                let mark = match param.mark {
                    hir::Mark::None => "",
                    hir::Mark::Let => "let ",
                    hir::Mark::Const => "const ",
                };
                let ty = match tcx.kind(param.ty) {
                    _ if param.ty == pt || param.ty == qt => "T".to_owned(),
                    TyKind::Ref(inner) if inner == pt || inner == qt => "&T".to_owned(),
                    _ => tcx.ty_string(param.ty),
                };
                format!("{mark}{}: {ty}", param.name)
            })
            .collect();
        let written: Vec<String> = own
            .iter()
            .filter(|&&o| tcx.param(o).implicit.is_none())
            .map(|&o| tcx.param(o).name.as_str().to_owned())
            .collect();
        let mut generics = written;
        generics.push(format!("T extends {iface}"));
        Some(format!(
            "use one type for both: {name}<{}>({})",
            generics.join(", "),
            params.join(", ")
        ))
    }

    /// EN0401: a `&string` never becomes an `&I`, since it may be a part of a string
    /// (S:631, A:894), with `help: take <T extends Measured>(m: &T)` and `help: or
    /// keep a copy: s.slice(1, 3).toString()`.
    pub(crate) fn report_part_of_string(&mut self, e: &hir::Expr, iface: AdtId) {
        let diag = self.part_of_string(e.span, iface);
        self.sema.emit(diag);
    }

    /// The EN0401 of [`Self::report_part_of_string`] for the `&string` written at
    /// `span`, which a generic call's binding of an implicit `&I` parameter reports
    /// too (S:631: `keep(s.slice(1, 3))`).
    pub(crate) fn part_of_string(&self, span: Span, iface: AdtId) -> Diagnostic {
        let name = self.sema.tcx.adt(iface).name;
        let text = self.snippet(span);
        let param = self
            .arg_context(span)
            .and_then(|c| c.param)
            .map_or_else(|| "m".to_owned(), |p| p.as_str().to_owned());
        let copy = text.trim_start_matches('&').trim();
        Diagnostic::new(
            Code::EN0401,
            format!("a `&string` can't become a `&{name}`, because it may be a part of a string"),
            span,
            "this is a `&string`",
        )
        .with_help(Help::text(format!("take <T extends {name}>({param}: &T)")))
        .with_help(Help::text(format!("or keep a copy: {copy}.toString()")))
    }

    /// EN0401 for an object type where interface `iface` of methods is expected
    /// (S:629): no anonymous object has a method, so the interface, which a
    /// fields-only one becomes with its first method, is no object type any more.
    /// Whether `from` (or the type it refers to) is an object type and `iface` has
    /// a method, so that it reported.
    pub(crate) fn report_object_at_iface(&mut self, span: Span, from: Ty, iface: AdtId) -> bool {
        let tcx = &*self.sema.tcx;
        let from = match tcx.kind(self.shallow(from)) {
            TyKind::Ref(inner) => self.shallow(inner),
            _ => self.shallow(from),
        };
        let has_method = tcx
            .adt(iface)
            .as_interface()
            .is_some_and(|i| !i.methods.is_empty());
        if !matches!(tcx.kind(from), TyKind::Object(_)) || !has_method {
            return false;
        }
        let name = tcx.adt(iface).name;
        let shown = self.ty_str(from);
        self.sema.emit(
            Diagnostic::new(
                Code::EN0401,
                format!("`{name}` now has a method, so it is an interface, not an object type"),
                span,
                format!("this is `{shown}`, which has no methods"),
            )
            .with_help(Help::text("make it a class")),
        );
        true
    }

    /// EN0701: a borrowing class never becomes an interface value (S:631, A:892).
    fn report_borrowing(&mut self, e: &hir::Expr, iface: AdtId, class: Ty) {
        let name = self.sema.tcx.adt(iface).name;
        let class = self.ty_str(class);
        self.sema.emit(
            Diagnostic::new(
                Code::EN0701,
                format!(
                    "{} `{name}` can't hold {} `{class}`, because `{class}` holds a reference",
                    crate::classes::sig::article(name.as_str()),
                    crate::classes::sig::article(&class)
                ),
                e.span,
                format!("`{class}` holds a reference"),
            )
            .note("an interface declares no loans and no stores, so only a value type becomes one"),
        );
    }

    /// EN1006 for an interface value by value, whose class and size are unknown
    /// (T:862, A:894).
    pub(crate) fn report_iface_value(&mut self, e: &hir::Expr) {
        if self.iface_from_type_arg(e) {
            return;
        }
        let shown = self.ty_str(e.ty);
        let text = self.snippet(e.span);
        self.sema.emit(iface_unsupported(
            e.span,
            format!(
                "this is {} `{shown}` by value",
                crate::classes::sig::article(&shown)
            ),
            format!("`{shown}` is an interface, so the size of `{text}` isn't known"),
            Some(format!(
                "`&{shown}` to refer to one, `Box<{shown}>` to own one"
            )),
        ));
    }

    /// Whether `e` is a call that binds one of its callee's own type parameters to
    /// an interface type, which the generic call reports as EN1006 at its argument
    /// (`iface_type_arg`), so its by-value result reports nothing more.
    fn iface_from_type_arg(&self, e: &hir::Expr) -> bool {
        let ExprKind::Call {
            callee: hir::Callee::Fn(f) | hir::Callee::Super(f),
            ..
        } = &e.kind
        else {
            return false;
        };
        let tcx = &*self.sema.tcx;
        let Some(sig) = tcx.sig_opt(f.def) else {
            return false;
        };
        let own = tcx.generics(sig.generics).params.len();
        let args = tcx.list(f.args);
        args[args.len().saturating_sub(own)..]
            .iter()
            .any(|&a| tcx.is_interface_ty(self.resolve(a)))
    }

    /// The note of EN1006 for `member` of interface `adt` (A:894).
    pub(crate) fn member_reason(&self, adt: AdtId, member: Symbol) -> String {
        let tcx = &*self.sema.tcx;
        let need = class_need(tcx, adt)
            .filter(|&(m, _)| m == member)
            .map_or(ClassNeed::SelfByValue, |(_, need)| need);
        need_note(tcx, adt, member, need)
    }

    /// The member of interface `adt` that needs the class (A:894).
    pub(crate) fn needs_class(&self, adt: AdtId) -> Option<Symbol> {
        class_need(self.sema.tcx, adt).map(|(member, _)| member)
    }

    // ---------------------------------------------------------------------------
    // For generic calls (4A).

    /// An argument `arg` at a by-value parameter of interface `iface` that is a
    /// ternary, a `??` or a `match` of expression arms: typed branch by branch, each
    /// with its own type, and EN1006 at it when the branches may hold different
    /// classes (VI-03-branches); `None` for any other argument, which the caller types
    /// as usual. `callee` names the function for the help.
    pub(crate) fn by_value_iface_arg(
        &mut self,
        arg: &ast::Expr,
        iface: AdtId,
        callee: Option<Symbol>,
    ) -> Option<hir::Expr> {
        let inner = strip_parens(arg);
        let branchy = match &inner.kind {
            ast::ExprKind::Ternary(..) | ast::ExprKind::Coalesce(..) => true,
            ast::ExprKind::Match { arms, .. } => arms
                .iter()
                .all(|arm| !matches!(arm.body, ast::ArmBody::Block(_))),
            _ => false,
        };
        if !branchy {
            return None;
        }
        let mut leaves = Vec::new();
        let mut typed = self.iface_branches(inner, &mut leaves);
        let mut classes: Vec<(Ty, Span)> = Vec::new();
        for (t, span) in leaves {
            let t = self.resolve(t);
            if self.is_error(t) || self.sema.tcx.kind(t) == TyKind::Never {
                continue;
            }
            if !classes.iter().any(|&(c, _)| c == t) {
                classes.push((t, span));
            }
        }
        match classes.as_slice() {
            [] => {}
            [(one, _)] => typed.ty = *one,
            [first, second, ..] => {
                let iface_name = self.sema.tcx.adt(iface).name;
                let (a, b) = (self.class_text(*first), self.class_text(*second));
                let call = callee.map_or_else(|| "the function".to_owned(), |c| c.to_string());
                self.sema.emit(iface_unsupported(
                    inner.span,
                    "its branches may hold different classes",
                    format!("this `{iface_name}` may be {a} or {b}, so its class isn't known"),
                    Some(format!("call {call} in each branch")),
                ));
                typed.ty = self.error_ty();
            }
        }
        Some(typed)
    }

    /// `e`, a branch of a by-value interface argument: a nested ternary, `??` or
    /// `match` branch by branch, any other expression with no expected type; each
    /// leaf's type and span is pushed to `leaves`.
    fn iface_branches(&mut self, e: &ast::Expr, leaves: &mut Vec<(Ty, Span)>) -> hir::Expr {
        let e = strip_parens(e);
        match &e.kind {
            ast::ExprKind::Ternary(c, a, b) => {
                let cond = self.check_cond(c);
                let (when_true, when_false) = self.cond_facts(&cond);
                self.flow = when_true;
                let then_ = self.iface_branches(a, leaves);
                let after_then = std::mem::replace(&mut self.flow, when_false);
                let else_ = self.iface_branches(b, leaves);
                let after_else = std::mem::take(&mut self.flow);
                self.join(vec![after_then, after_else]);
                let ty = then_.ty;
                self.mk_expr(
                    ty,
                    e.span,
                    ExprKind::Ternary(Box::new(cond), Box::new(then_), Box::new(else_)),
                )
            }
            ast::ExprKind::Coalesce(a, b) => {
                let left = self.check_expr(a, Expect::None);
                let payload = match self.sema.tcx.kind(self.shallow(left.ty)) {
                    TyKind::Nullable(inner) => inner,
                    _ => left.ty,
                };
                leaves.push((payload, left.span));
                let right = self.iface_branches(b, leaves);
                self.mk_expr(
                    payload,
                    e.span,
                    ExprKind::Coalesce(Box::new(left), Box::new(right)),
                )
            }
            ast::ExprKind::Match { subject, arms }
                if arms
                    .iter()
                    .all(|arm| !matches!(arm.body, ast::ArmBody::Block(_))) =>
            {
                // Typed as a statement, so no arm is unified with another; each
                // expression arm then counts as a branch.
                let mut typed = self.check_match(subject, arms, e.span, Expect::None, true);
                if let ExprKind::Match { arms, .. } = &typed.kind {
                    for arm in arms {
                        if let hir::ArmBody::Expr(value) = &arm.body {
                            leaves.push((value.ty, value.span));
                        }
                    }
                }
                if let Some(&(first, _)) = leaves.last() {
                    typed.ty = first;
                }
                typed
            }
            _ => {
                let typed = self.check_expr(e, Expect::None);
                leaves.push((typed.ty, typed.span));
                typed
            }
        }
    }

    /// A branch's class as EN1006's note names it: `` a `Dog` ``, or `` the class of
    /// `s` `` for an interface parameter or a two-word value.
    fn class_text(&self, (t, span): (Ty, Span)) -> String {
        if self.own_class(t).is_some() || self.sema.tcx.is_interface_ty(t) {
            format!("the class of `{}`", self.snippet(span))
        } else {
            crate::classes::sig::a_ty(&self.ty_str(t))
        }
    }

    /// EN1006 for a type parameter of `callee` bound to the interface `t` (S:560,
    /// A:894, S2-10-swap): with each `&*b` argument over a `Box<I>`, `` note:
    /// `Speaker` is an interface, so the size of `*a` isn't known ``, at the first such
    /// argument, and the call rewritten with `&b` as the help (`swap the boxes:
    /// mem.swap(&a, &b)` for `mem.swap`); else at `primary`.
    pub(crate) fn iface_type_arg(
        &self,
        callee: DefId,
        call: Span,
        args: &[ast::Expr],
        t: Ty,
        primary: Span,
    ) -> Diagnostic {
        let shown = self.ty_str(t);
        let unboxed: Vec<&ast::Expr> = args
            .iter()
            .filter(|a| match &strip_parens(a).kind {
                ast::ExprKind::Borrow(inner) => {
                    matches!(strip_parens(inner).kind, ast::ExprKind::Deref(_))
                }
                _ => false,
            })
            .collect();
        let Some(first) = unboxed.first() else {
            return iface_unsupported(
                primary,
                format!("this makes a type parameter the interface `{shown}`"),
                format!("`{shown}` is an interface, so no type parameter can stand for it"),
                Some(format!(
                    "`&{shown}` to refer to one, `Box<{shown}>` to own one"
                )),
            );
        };
        let place = match &strip_parens(first).kind {
            ast::ExprKind::Borrow(inner) => self.snippet(strip_parens(inner).span),
            _ => self.snippet(first.span),
        };
        // The call with each `&*b` written `&b`.
        let mut text = self.snippet(call);
        let base = call.lo.0;
        for a in unboxed.iter().rev() {
            if let ast::ExprKind::Borrow(inner) = &strip_parens(a).kind
                && let ast::ExprKind::Deref(boxed) = &strip_parens(inner).kind
            {
                let lo = (inner.span.lo.0 - base) as usize;
                let hi = (boxed.span.lo.0 - base) as usize;
                if lo <= hi && hi <= text.len() {
                    text.replace_range(lo..hi, "");
                }
            }
        }
        let is_swap = self
            .sema
            .tcx
            .def(callee)
            .path
            .to_string()
            .ends_with("mem::swap");
        let help = match is_swap {
            true => format!("swap the boxes: {text}"),
            false => text,
        };
        iface_unsupported(
            first.span,
            format!(
                "`{place}` is {} `{shown}` by value",
                crate::classes::sig::article(&shown)
            ),
            format!("`{shown}` is an interface, so the size of `{place}` isn't known"),
            Some(help),
        )
    }
}

/// Where a C22 conversion's class sits.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Behind {
    Value,
    Ref,
    Boxed,
}
