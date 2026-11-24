//! The view and string facts (plan d.9; A:892, SPEC 4.3 S:606, 4.4 S:631, 4.10
//! S:766; owner 4E).
//!
//! Once every body is typed, each type parameter of each declaration gets two
//! facts, stored with `Tcx::set_facts` in the order of its own generics list:
//!
//! - `views_ok`, whether it may stand for a view `Slice<U>`: its signature and every
//!   body that sees it (a class's parameter: all the class's bodies; nested arrows
//!   count as part of their body) use it only directly behind `&` (`&T`, `&T |
//!   null`), never by value, as an element, field, payload, local, parameter or
//!   result, behind `*`, in a cast, in `sizeOf`, `alignOf` or `offsetOf`, in an
//!   intrinsic's type arguments (a pointer method), in a C22 conversion of `T`, `&T`
//!   or `Box<T>`, nor as the type argument of a parameter or class that lacks it;
//! - `strings_ok`, whether it may stand for `string`: no body converts its `&T` or
//!   `&T | null` to an interface reference (C22), and it is the type argument of no
//!   parameter or class that lacks it.
//!
//! Both start true and are lost at such a use, then along the calls and instances
//! that pass a parameter on, to the greatest fixed point (iterating the passed-on
//! edges until nothing changes, which is the fixed point A:892 computes per SCC).
//! A user declaration with no body, an abstract method or a `declare function`,
//! lacks both; an interface member lacks `views_ok` and has `strings_ok`; a `T`
//! bounded by a class lacks `views_ok`. Library bodies are not typed at M2, so a
//! library declaration's facts come from its signature and fields alone (plan
//! choice: the library's bodyless members are signature stubs, A:2014).
//!
//! Then every binding of a type parameter to a view or to `string` is checked: the
//! uses typing recorded in [`ViewUses`] (4A) and those the finished bodies show,
//! each call's and `new`'s type arguments. A view bound to a `T` without
//! `views_ok` is EN0401 `` `T` can't stand for the view `Slice<u8>` `` at the use,
//! with a label at the use in the body that lost the fact, or a note when the
//! declaration has no body, and `` help: add `show<T>(x: &Slice<T>)` ``; `string`
//! bound to a `T` without `strings_ok` is EN0401 `` a `&string` can't become a
//! `&Measured`, because it may be a part of a string ``, labelled at the conversion
//! (its statement), with `` help: add `show(x: &string)` ``.
//!
//! Last, the string clause of satisfaction (SPEC 4.4, A:899): the one satisfaction
//! routine (`classes/satisfy.rs`) recorded every member a satisfaction relied on,
//! own, inherited or `extend`, at an `implements` entry, a C22 conversion, an
//! argument to a non-null `&I` or by-value `I` parameter or a bound met by a type
//! argument, and once these facts are known it calls [`check_implementations`] over
//! that set. A member that has lost `strings_ok` for a type parameter the interface
//! member keeps it for is EN0401 at the conversion or call in its body that lost
//! it, with `` `Keeper` is used as a `Sizer` here `` at the site and `` note:
//! `Sizer.size` lets `T` stand for `string` ``, once per member and interface.

use std::collections::{BTreeMap, BTreeSet};

use enrang_base::Span;
use enrang_diag::{Code, Diagnostic, Help};
use enrang_hir::{
    Adjust, ArmBody, ArmValue, ArrayPart, ArrowBodyKind, Block, Body, BodyOwner, Bound, Callee,
    DefId, DefKind, ExpectArg, Expr, ExprKind, ForSource, FormKind, Implicit, OptMember, ParamId,
    Stmt, StmtKind, Tcx, TplPart, Ty, TyKind, TyParamFacts,
};

use crate::classes::satisfy::Satisfaction;
use crate::cx::Sema;
use crate::passes::positions;

/// The type arguments each call and class instance bound, collected while bodies are
/// typed (4A), in typing order.
#[derive(Clone, Debug, Default)]
pub(crate) struct ViewUses {
    pub uses: Vec<ViewUse>,
    /// The views and `string`s written as a type argument of a class, enum or
    /// interface (`Keeper<string>`, `Result<Slice<u8>>`), which `positions.rs`
    /// finds and leaves to the facts (S:606).
    pub written: Vec<WrittenArg>,
    /// Each `new` with written type arguments, by its span, to the span of its
    /// written type: a use there is reported at `Keeper<string>` (T:1048).
    pub new_types: BTreeMap<Span, Span>,
}

/// A view or `string` written as the type argument `arg` for `param` at `span`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct WrittenArg {
    pub span: Span,
    pub param: ParamId,
    pub arg: Ty,
}

/// One binding of a callee's type parameter (plan d.9: "(call span, callee def,
/// param, arg ty)"): where EN0401 points when `arg` is a view or `string` that
/// `param` cannot stand for (G13, G19).
#[allow(dead_code)] // `caller` and `callee` are for the recheck of stored code (A:574).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ViewUse {
    /// The body the call or instance is in.
    pub caller: BodyOwner,
    /// The call, or the written instance type.
    pub span: Span,
    /// The function, method or class whose parameter is bound.
    pub callee: DefId,
    pub param: ParamId,
    pub arg: Ty,
}

/// Why a parameter lost a fact, for the label or note of EN0401.
#[derive(Copy, Clone, Debug)]
enum Why {
    /// Its declaration has no body to keep it.
    NoBody,
    /// A library function's or method's own type parameter: its body is a
    /// placeholder at M2, so no use of it is known (A:892, plan f.1).
    Library,
    /// Its signature or fields use it by value.
    Signature,
    /// It has a class bound, which refuses a view itself (S:764): binding one is
    /// EN0419 at the call, so no view report is added.
    ClassBound,
    /// A local holds it by value.
    Local,
    /// A use that needs a value type: a cast, `*T`, a size form, an intrinsic.
    Value,
    /// A C22 conversion of `T`, `&T` or `Box<T>`.
    Convert,
    /// It is passed on to `callee`'s parameter, which lacks the fact.
    PassedOn(DefId),
}

#[derive(Copy, Clone, Debug)]
struct Loss {
    span: Span,
    why: Why,
}

/// A parameter passed on as the type argument of another one.
#[derive(Copy, Clone, Debug)]
struct Dep {
    from: ParamId,
    to: ParamId,
    span: Span,
    callee: DefId,
}

/// The facts being computed.
#[derive(Default)]
pub(crate) struct Facts {
    views: BTreeMap<ParamId, bool>,
    strings: BTreeMap<ParamId, bool>,
    views_loss: BTreeMap<ParamId, Loss>,
    strings_loss: BTreeMap<ParamId, Loss>,
    deps: Vec<Dep>,
    /// Each declaration's own parameters, in order.
    owners: Vec<(DefId, Vec<ParamId>)>,
    /// The bindings to a view or `string` the bodies show.
    uses: Vec<ViewUse>,
}

impl Facts {
    fn lose_views(&mut self, p: ParamId, span: Span, why: Why) {
        if let Some(v) = self.views.get_mut(&p)
            && *v
        {
            *v = false;
            self.views_loss.insert(p, Loss { span, why });
        }
    }

    fn lose_strings(&mut self, p: ParamId, span: Span, why: Why) {
        if let Some(s) = self.strings.get_mut(&p)
            && *s
        {
            *s = false;
            self.strings_loss.insert(p, Loss { span, why });
        }
    }

    fn has(&self, p: ParamId) -> bool {
        self.views.contains_key(&p)
    }

    /// Every occurrence of a parameter in `t` that is not directly behind `&` loses
    /// `views_ok`; a parameter standing as a class's type argument is passed on.
    fn scan(&mut self, tcx: &Tcx, t: Ty, span: Span, why: Why) {
        self.occurs(tcx, t, false, span, why);
    }

    fn occurs(&mut self, tcx: &Tcx, t: Ty, behind_ref: bool, span: Span, why: Why) {
        match tcx.kind(t) {
            TyKind::Param(p) => {
                if !behind_ref {
                    self.lose_views(p, span, why);
                }
            }
            TyKind::Ref(inner) => self.occurs(tcx, inner, true, span, why),
            TyKind::Adt(adt, args) => {
                let params = tcx.generics(tcx.adt(adt).generics).params.clone();
                let args = tcx.list(args);
                for (i, &a) in args.iter().enumerate() {
                    match (tcx.kind(a), params.get(i)) {
                        (TyKind::Param(p), Some(&q)) if self.has(p) => self.deps.push(Dep {
                            from: p,
                            to: q,
                            span,
                            callee: tcx.adt(adt).def,
                        }),
                        _ => self.occurs(tcx, a, false, span, why),
                    }
                }
            }
            _ => {
                for c in tcx.children(t) {
                    self.occurs(tcx, c, false, span, why);
                }
            }
        }
    }

    /// `args` bound to `params` of `callee` at `span`.
    /// A view or `string` is a use only for the parameters in `checked`: a call's
    /// own ones, or a construction's class parameters; the class parameters a
    /// call's receiver binds were checked where the instance was written or built.
    #[allow(clippy::too_many_arguments)]
    fn bind(
        &mut self,
        tcx: &Tcx,
        caller: BodyOwner,
        callee: DefId,
        params: &[ParamId],
        checked: &[ParamId],
        args: &[Ty],
        span: Span,
    ) {
        for (&q, &a) in params.iter().zip(args) {
            match tcx.kind(a) {
                TyKind::Param(p) if self.has(p) => {
                    if let Some(Implicit::Interface(_)) = tcx.param(q).implicit {
                        // A by-value `T` passed as a by-value interface: C22.
                        self.lose_views(p, span, Why::Convert);
                    } else {
                        self.deps.push(Dep {
                            from: p,
                            to: q,
                            span,
                            callee,
                        });
                    }
                }
                TyKind::Slice(_) | TyKind::Str => {
                    if checked.contains(&q) {
                        self.uses.push(ViewUse {
                            caller,
                            span,
                            callee: tcx.param(q).owner,
                            param: q,
                            arg: a,
                        });
                    }
                }
                _ => self.scan(tcx, a, span, Why::Value),
            }
        }
    }
}

/// Computes the facts, sets them in `Tcx`, and reports the uses they forbid.
pub(crate) fn compute_and_check(sema: &mut Sema) {
    let mut facts = Facts::default();
    declare(sema.tcx, &mut facts);
    signatures(sema.tcx, &mut facts);
    let mut bodies: Vec<std::sync::Arc<Body>> = Vec::new();
    if let Some(b) = &sema.statements {
        bodies.push(b.clone());
    }
    bodies.extend(sema.bodies.values().cloned());
    // A class's parameters lose their facts in its field initialisers too (A:892).
    bodies.extend(sema.field_init_bodies.values().cloned());
    for b in &bodies {
        scan_body(sema.tcx, &mut facts, b);
    }
    // The greatest fixed point along the passed-on edges.
    loop {
        let mut changed = false;
        for i in 0..facts.deps.len() {
            let d = facts.deps[i];
            let loss = Loss {
                span: d.span,
                why: Why::PassedOn(d.callee),
            };
            if !facts.views.get(&d.to).copied().unwrap_or(true)
                && facts.views.get(&d.from).copied().unwrap_or(false)
            {
                facts.views.insert(d.from, false);
                facts.views_loss.insert(d.from, loss);
                changed = true;
            }
            if !facts.strings.get(&d.to).copied().unwrap_or(true)
                && facts.strings.get(&d.from).copied().unwrap_or(false)
            {
                facts.strings.insert(d.from, false);
                facts.strings_loss.insert(d.from, loss);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    for (def, params) in &facts.owners {
        let views_ok = params.iter().map(|p| facts.views[p]).collect();
        let strings_ok = params.iter().map(|p| facts.strings[p]).collect();
        sema.tcx.set_facts(
            *def,
            TyParamFacts {
                views_ok,
                strings_ok,
            },
        );
    }
    check_uses(sema, &facts);
    crate::classes::satisfy::check_recorded(sema, &facts);
}

/// The library functions and methods whose own type parameters are used only
/// behind `&` and may stand for a view: none at M2 (`mem.swap<T>(&T, &T)` moves
/// its `T`s by value).
const LIBRARY_VIEWS: &[&str] = &[];

/// Every declaration with type parameters of its own, with the facts it starts
/// with.
fn declare(tcx: &Tcx, facts: &mut Facts) {
    let extends: BTreeMap<DefId, enrang_hir::GenericsId> =
        tcx.extends().iter().map(|e| (e.def, e.generics)).collect();
    for (def, data) in tcx.defs() {
        let generics = match data.kind {
            k if k.has_sig() => tcx.sig_opt(def).map(|s| s.generics),
            DefKind::Adt(adt) | DefKind::StrUnion(adt) => Some(tcx.adt(adt).generics),
            DefKind::Extend => extends.get(&def).copied(),
            _ => None,
        };
        let Some(generics) = generics else {
            continue;
        };
        let params = tcx.generics(generics).params.clone();
        if params.is_empty() {
            continue;
        }
        let library = tcx.module(data.module).library;
        let (views, strings) = if data.kind.has_sig() {
            let iface_member = data
                .parent
                .and_then(|p| tcx.adt_of(p))
                .is_some_and(|a| tcx.adt(a).is_interface());
            if iface_member {
                (false, true)
            } else if library {
                // Bodies arrive at M4: a library function stands for a value type
                // unless this table says otherwise (A:892), keeping the strings
                // fact of its signature.
                (
                    LIBRARY_VIEWS.contains(&data.name().map_or("", |n| n.as_str())),
                    true,
                )
            } else if data.flags.has_body {
                (true, true)
            } else {
                (false, false)
            }
        } else {
            (true, true)
        };
        for &p in &params {
            facts.views.insert(p, true);
            facts.strings.insert(p, true);
            let span = data.name_span;
            if !views {
                let why = match library && data.kind.has_sig() {
                    true => Why::Library,
                    false => Why::NoBody,
                };
                facts.lose_views(p, span, why);
            }
            if !strings {
                facts.lose_strings(p, span, Why::NoBody);
            }
            let class_bound = tcx
                .param(p)
                .bounds
                .iter()
                .any(|&b| matches!(tcx.bound(b), Bound::Class { .. }));
            if class_bound {
                facts.lose_views(p, tcx.param(p).span, Why::ClassBound);
            }
        }
        facts.owners.push((def, params));
    }
}

/// The by-value uses in every signature, field and `extend` target.
fn signatures(tcx: &Tcx, facts: &mut Facts) {
    for (def, data) in tcx.defs() {
        let span = data.name_span;
        if data.kind.has_sig()
            && let Some(sig) = tcx.sig_opt(def)
        {
            for p in &sig.params {
                facts.scan(tcx, p.ty, span, Why::Signature);
            }
            facts.scan(tcx, sig.ret, span, Why::Signature);
        }
        if let DefKind::Adt(adt) = data.kind {
            for t in tcx.adt_field_tys(adt, tcx.identity_args(tcx.adt(adt).generics)) {
                facts.scan(tcx, t, span, Why::Signature);
            }
        }
    }
    for e in tcx.extends() {
        facts.scan(tcx, e.ty, tcx.def(e.def).name_span, Why::Signature);
    }
}

/// The uses of one body: expressions first, then its locals, so that a label
/// names the cast or conversion before the local that holds its result.
fn scan_body(tcx: &Tcx, facts: &mut Facts, b: &Body) {
    let caller = b.owner;
    walk(b, &mut |e, stmt| {
        expr_uses(tcx, facts, caller, e, stmt);
    });
    for (_, local) in b.locals.iter_enumerated() {
        facts.scan(tcx, local.ty, local.span, Why::Local);
    }
}

/// The uses of one expression; `stmt` is the innermost statement around it.
fn expr_uses(tcx: &Tcx, facts: &mut Facts, caller: BodyOwner, e: &Expr, stmt: Option<Span>) {
    match &e.kind {
        ExprKind::Cast(..) => facts.scan(tcx, e.ty, e.span, Why::Value),
        ExprKind::Call { callee, .. } => callee_uses(tcx, facts, caller, callee, e.span),
        ExprKind::OptionalChain(chain) => {
            if let OptMember::Call { callee, .. } = &chain.member {
                callee_uses(tcx, facts, caller, callee, e.span);
            }
        }
        ExprKind::New { ctor, args, .. } => {
            if let Some(sig) = tcx.sig_opt(*ctor) {
                let params = tcx.all_params(sig.generics);
                let args = tcx.list(*args);
                let owner = tcx.def(*ctor).parent.unwrap_or(*ctor);
                facts.bind(tcx, caller, owner, &params, &params, &args, e.span);
            }
        }
        ExprKind::NewNamed { adt, args, .. } | ExprKind::VariantLit { adt, args, .. } => {
            let params = tcx.generics(tcx.adt(*adt).generics).params.clone();
            let args = tcx.list(*args);
            facts.bind(
                tcx,
                caller,
                tcx.adt(*adt).def,
                &params,
                &params,
                &args,
                e.span,
            );
        }
        _ => {}
    }
    // C22: `&T`, `&T | null`, `T` or `Box<T>` converted to an interface.
    let converts = e
        .adjust
        .iter()
        .any(|a| matches!(a, Adjust::RefToInterface | Adjust::BoxToInterface));
    if converts {
        let at = stmt.unwrap_or(e.span);
        let param = match tcx.kind(e.ty) {
            TyKind::Param(p) => Some(p),
            TyKind::Ref(inner) | TyKind::Boxed(inner) => match tcx.kind(inner) {
                TyKind::Param(p) => Some(p),
                _ => None,
            },
            TyKind::Nullable(inner) => match tcx.kind(inner) {
                TyKind::Ref(r) => match tcx.kind(r) {
                    TyKind::Param(p) => Some(p),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        };
        if let Some(p) = param {
            facts.lose_views(p, at, Why::Convert);
            if e.adjust.contains(&Adjust::RefToInterface) {
                facts.lose_strings(p, at, Why::Convert);
            }
        }
    }
}

fn callee_uses(tcx: &Tcx, facts: &mut Facts, caller: BodyOwner, callee: &Callee, span: Span) {
    match callee {
        Callee::Fn(f) | Callee::Super(f) => {
            if let Some(sig) = tcx.sig_opt(f.def) {
                let params = tcx.all_params(sig.generics);
                let own = tcx.generics(sig.generics).params.clone();
                let args = tcx.list(f.args);
                facts.bind(tcx, caller, f.def, &params, &own, &args, span);
            }
        }
        Callee::SuperCtor { adt, args, .. } => {
            let params = tcx.generics(tcx.adt(*adt).generics).params.clone();
            let args = tcx.list(*args);
            facts.bind(tcx, caller, tcx.adt(*adt).def, &params, &[], &args, span);
        }
        Callee::Intrinsic(_, args) => {
            for &a in tcx.list(*args).iter() {
                if tcx.has_params(a) {
                    lose_all_views(tcx, facts, a, span);
                }
            }
        }
        Callee::Form(FormKind::SizeOf(t) | FormKind::AlignOf(t) | FormKind::OffsetOf(t, _)) => {
            lose_all_views(tcx, facts, *t, span);
        }
        _ => {}
    }
}

/// Every parameter in `t`, behind `&` or not, loses `views_ok`.
fn lose_all_views(tcx: &Tcx, facts: &mut Facts, t: Ty, span: Span) {
    let mut found = Vec::new();
    tcx.any_ty(t, &mut |tcx, inner| {
        if let TyKind::Param(p) = tcx.kind(inner) {
            found.push(p);
        }
        false
    });
    for p in found {
        facts.lose_views(p, span, Why::Value);
    }
}

// ---------------------------------------------------------------------------------
// The checks.

/// EN0401 for every binding of a view or `string` to a parameter without the fact.
fn check_uses(sema: &mut Sema, facts: &Facts) {
    let mut seen: BTreeSet<(Span, ParamId)> = BTreeSet::new();
    let uses: Vec<ViewUse> = sema.views.uses.iter().chain(&facts.uses).cloned().collect();
    for u in uses {
        if !seen.insert((u.span, u.param)) {
            continue;
        }
        let at = sema.views.new_types.get(&u.span).copied().unwrap_or(u.span);
        match sema.tcx.kind(u.arg) {
            TyKind::Slice(_) if !facts.views.get(&u.param).copied().unwrap_or(true) => {
                report_view(sema, facts, at, u.param, u.arg);
            }
            // An implicit `X extends I` of an `&I` parameter: C22 rejects the
            // `&string` at the argument already, one report per mistake (A:1270).
            // A by-value `I` parameter keeps this report, which is its only one.
            TyKind::Str if behind_ref_only(&sema.tcx, u.param) => {}
            TyKind::Str if !facts.strings.get(&u.param).copied().unwrap_or(true) => {
                report_string(sema, facts, at, u.param);
            }
            _ => {}
        }
    }
    // The type arguments written in types: a view by value is S:606's EN0401.
    let written = std::mem::take(&mut sema.views.written);
    for w in written {
        if !seen.insert((w.span, w.param)) {
            continue;
        }
        match sema.tcx.kind(w.arg) {
            TyKind::Slice(_) if !facts.views.get(&w.param).copied().unwrap_or(true) => {
                positions::report_view(sema, w.arg, w.span);
            }
            TyKind::Str if !facts.strings.get(&w.param).copied().unwrap_or(true) => {
                report_string(sema, facts, w.span, w.param);
            }
            _ => {}
        }
    }
}

/// A declaration's name as messages give it: `Dumper.dump` for a member.
fn qualified(tcx: &Tcx, def: DefId) -> String {
    let data = tcx.def(def);
    let name = data.name().map_or("", |n| n.as_str());
    match data.parent.and_then(|p| tcx.def(p).name()) {
        Some(parent) if data.kind.has_sig() => format!("{parent}.{name}"),
        _ => name.to_owned(),
    }
}

/// `show<T>(x: &Slice<T>)`, or with `to_str`, `show(x: &string)`: `def`'s signature
/// with `q` replaced, for the help that adds such an overload.
fn overload_help(tcx: &Tcx, def: DefId, q: ParamId, to_str: bool) -> Option<String> {
    let data = tcx.def(def);
    let sig = tcx.sig_opt(def)?;
    let name = data.name()?;
    let replacement = if to_str {
        tcx.common().str
    } else {
        tcx.mk_slice(tcx.mk_param(q))
    };
    let own: Vec<String> = tcx
        .generics(sig.generics)
        .params
        .iter()
        .filter(|&&p| tcx.param(p).implicit.is_none() && !(to_str && p == q))
        .map(|&p| tcx.param(p).name.as_str().to_owned())
        .collect();
    let generics = if own.is_empty() {
        String::new()
    } else {
        format!("<{}>", own.join(", "))
    };
    // Each parameter as written, its default or `?` kept, so the overload added
    // takes the call that failed (S:766).
    let params: Vec<String> = sig
        .params
        .iter()
        .map(|p| {
            let ty = tcx.subst(p.ty, &[q], &[replacement]);
            let written = match p.span.is_dummy() {
                true => "",
                false => tcx.map().text(p.span),
            };
            match (p.has_default, written.split_once('=')) {
                (true, Some((_, default))) => {
                    format!("{}: {} = {}", p.name, tcx.ty_string(ty), default.trim())
                }
                (true, None) if written.contains("?:") => {
                    let inner = match tcx.kind(ty) {
                        TyKind::Nullable(inner) => inner,
                        _ => ty,
                    };
                    format!("{}?: {}", p.name, tcx.ty_string(inner))
                }
                _ => format!("{}: {}", p.name, tcx.ty_string(ty)),
            }
        })
        .collect();
    Some(format!("add `{name}{generics}({})`", params.join(", ")))
}

/// EN0401: a view bound to a parameter without `views_ok`.
fn report_view(sema: &mut Sema, facts: &Facts, span: Span, param: ParamId, arg: Ty) {
    let tcx = &*sema.tcx;
    let name = tcx.param(param).name;
    let owner = tcx.param(param).owner;
    let view = tcx.ty_string(arg);
    let mut diag = Diagnostic::new(
        Code::EN0401,
        format!("`{name}` can't stand for the view `{view}`"),
        span,
        format!("this binds `{name}` to `{view}`"),
    );
    match facts.views_loss.get(&param) {
        Some(Loss {
            why: Why::ClassBound,
            ..
        }) => return,
        Some(Loss {
            why: Why::NoBody, ..
        }) => {
            diag = diag.note(format!(
                "`{}` has no body, so its `{name}` may be used by value",
                qualified(tcx, owner)
            ));
        }
        Some(Loss {
            why: Why::Library, ..
        }) => {
            diag = diag.note(format!(
                "`{}` is the library's, whose body may use `{name}` by value",
                qualified(tcx, owner)
            ));
        }
        Some(&Loss { span, why }) => {
            let label = match why {
                Why::PassedOn(callee) => format!(
                    "this passes `{name}` on to `{}`, which needs a value type",
                    qualified(tcx, callee)
                ),
                Why::Convert => {
                    format!("this converts `{name}` to an interface, which needs a value type")
                }
                Why::Signature => format!("`{}` uses `{name}` by value", qualified(tcx, owner)),
                Why::Local | Why::Value | Why::NoBody | Why::ClassBound | Why::Library => {
                    format!("this needs `{name}` to be a value type")
                }
            };
            diag = diag.with_secondary(span, label);
        }
        None => {}
    }
    // No overload can be added to the library.
    let library = tcx.module(tcx.def(owner).module).library;
    if !library && let Some(help) = overload_help(tcx, owner, param, false) {
        diag = diag.with_help(Help::text(help));
    }
    sema.emit(diag);
}

/// The interface a conversion of `q`'s `&T` reaches: its first interface bound.
fn iface_name(tcx: &Tcx, q: ParamId) -> String {
    tcx.param(q)
        .bounds
        .iter()
        .find_map(|&b| match tcx.bound(b) {
            Bound::Iface { adt, args } => {
                Some(tcx.ty_string(tcx.intern_ty(TyKind::Adt(*adt, *args))))
            }
            Bound::Class { .. } => None,
        })
        .unwrap_or_else(|| "interface".to_owned())
}

/// The interface the loss of `q`'s `strings_ok` converts to, following passed-on
/// edges to the conversion.
fn converted_to(tcx: &Tcx, facts: &Facts, q: ParamId) -> String {
    let mut at = q;
    let mut seen = BTreeSet::new();
    while seen.insert(at) {
        let next = facts
            .deps
            .iter()
            .find(|d| d.from == at && !facts.strings.get(&d.to).copied().unwrap_or(true));
        match (facts.strings_loss.get(&at), next) {
            (
                Some(Loss {
                    why: Why::PassedOn(_),
                    ..
                }),
                Some(d),
            ) => at = d.to,
            _ => break,
        }
    }
    iface_name(tcx, at)
}

/// Whether `p` is the implicit `X extends I` of `&I` parameters only, never of a
/// by-value `I` one.
fn behind_ref_only(tcx: &Tcx, p: ParamId) -> bool {
    let param = tcx.param(p);
    if !matches!(param.implicit, Some(Implicit::Interface(_))) {
        return false;
    }
    let Some(sig) = tcx.sig_opt(param.owner) else {
        return false;
    };
    let x = tcx.mk_param(p);
    let by_ref = sig.params.iter().any(|ps| ps.ty == tcx.mk_ref(x));
    by_ref && sig.params.iter().all(|ps| ps.ty != x)
}

/// EN0401: `string` bound to a parameter without `strings_ok`.
fn report_string(sema: &mut Sema, facts: &Facts, span: Span, param: ParamId) {
    let tcx = &*sema.tcx;
    let name = tcx.param(param).name;
    let owner = tcx.param(param).owner;
    let iface = converted_to(tcx, facts, param);
    let mut diag = Diagnostic::new(
        Code::EN0401,
        format!("a `&string` can't become a `&{iface}`, because it may be a part of a string"),
        span,
        format!("this binds `{name}` to `string`"),
    );
    match facts.strings_loss.get(&param) {
        Some(Loss {
            why: Why::NoBody, ..
        }) => {
            diag = diag.note(format!(
                "`{}` has no body, so its `&{name}` may become an interface reference",
                qualified(tcx, owner)
            ));
        }
        Some(&Loss { span, why }) => {
            let label = match why {
                Why::PassedOn(callee) => format!(
                    "this passes `{name}` on to `{}`, which converts it",
                    qualified(tcx, callee)
                ),
                _ => format!("here a `&{name}` becomes a `&{iface}`"),
            };
            diag = diag.with_secondary(span, label);
        }
        None => {}
    }
    if let Some(help) = overload_help(tcx, owner, param, true) {
        diag = diag.with_help(Help::text(help));
    }
    sema.emit(diag);
}

/// The string clause of satisfaction (SPEC 4.4, A:899), called by the one
/// satisfaction routine (`satisfy::check_recorded`) over the members it recorded,
/// one entry per member found and interface member: EN0401 for a member that lost
/// `strings_ok` for a type parameter the interface member keeps it for, at the
/// conversion or call in its body that lost it, labelled at the satisfaction site,
/// with a note naming the interface member; once per entry, for its first such
/// type parameter. Entries that share that type parameter, one member found used
/// as members of several interfaces, share its conversion, where `DiagCtx` keeps
/// one diagnostic, so they are one diagnostic with each entry's site and note.
pub(crate) fn check_implementations(sema: &mut Sema, facts: &Facts, set: &[Satisfaction]) {
    let mut found: Vec<(Loss, ParamId, Vec<Satisfaction>)> = Vec::new();
    {
        let tcx = &*sema.tcx;
        for sat in set {
            let (Some(sig), Some(msig)) = (tcx.sig_opt(sat.found), tcx.sig_opt(sat.member)) else {
                continue;
            };
            let own = &tcx.generics(sig.generics).params;
            let mown = &tcx.generics(msig.generics).params;
            let broken = own.iter().zip(mown).find_map(|(&p, &q)| {
                let keeps = facts.strings.get(&q).copied().unwrap_or(false);
                let lost = !facts.strings.get(&p).copied().unwrap_or(true);
                match (keeps && lost, facts.strings_loss.get(&p)) {
                    (true, Some(&loss)) => Some((loss, p)),
                    _ => None,
                }
            });
            if let Some((loss, p)) = broken {
                match found.iter_mut().find(|(_, q, _)| *q == p) {
                    Some((_, _, sats)) => sats.push(sat.clone()),
                    None => found.push((loss, p, vec![sat.clone()])),
                }
            }
        }
    }
    for (loss, p, sats) in found {
        let tcx = &*sema.tcx;
        let name = tcx.param(p).name;
        let iface = converted_to(tcx, facts, p);
        let sat = &sats[0];
        let label = match loss.why {
            Why::PassedOn(callee) => format!(
                "this passes `{name}` on to `{}`, which converts it",
                qualified(tcx, callee)
            ),
            Why::NoBody => format!(
                "`{}` has no body, so its `&{name}` may become an interface reference",
                qualified(tcx, sat.found)
            ),
            _ => format!("here a `&{name}` becomes a `&{iface}`"),
        };
        let mut diag = Diagnostic::new(
            Code::EN0401,
            format!("a `&string` can't become a `&{iface}`, because it may be a part of a string"),
            loss.span,
            label,
        );
        for sat in &sats {
            if sat.site.is_dummy() {
                continue;
            }
            let class = match tcx.kind(sat.ty) {
                TyKind::Adt(adt, _) => tcx.adt(adt).name.as_str().to_owned(),
                _ => tcx.ty_string(sat.ty),
            };
            diag = diag.with_secondary(
                sat.site,
                format!("`{class}` is used as a `{}` here", tcx.ty_string(sat.iface)),
            );
        }
        for sat in &sats {
            diag = diag.note(format!(
                "`{}` lets `{name}` stand for `string`",
                qualified(tcx, sat.member)
            ));
        }
        sema.emit(diag);
    }
}

// ---------------------------------------------------------------------------------
// The walk, with the innermost statement around each expression.

fn walk(b: &Body, f: &mut dyn FnMut(&Expr, Option<Span>)) {
    for (_, d) in &b.param_defaults {
        walk_expr(d, None, f);
    }
    walk_block(&b.root, f);
    for arrow in &b.arrows {
        match &arrow.body {
            ArrowBodyKind::Expr(e) => walk_expr(e, None, f),
            ArrowBodyKind::Block(block) => walk_block(block, f),
        }
    }
}

fn walk_block(b: &Block, f: &mut dyn FnMut(&Expr, Option<Span>)) {
    for s in &b.stmts {
        walk_stmt(s, f);
    }
}

fn walk_stmt(s: &Stmt, f: &mut dyn FnMut(&Expr, Option<Span>)) {
    let at = Some(s.span);
    match &s.kind {
        StmtKind::Let { init, .. } => {
            if let Some(e) = init {
                walk_expr(e, at, f);
            }
        }
        StmtKind::Destructure { init, .. } => walk_expr(init, at, f),
        StmtKind::If { cond, then_, else_ } => {
            walk_expr(cond, at, f);
            walk_block(then_, f);
            if let Some(b) = else_ {
                walk_block(b, f);
            }
        }
        StmtKind::While { cond, body, .. } | StmtKind::DoWhile { body, cond, .. } => {
            walk_expr(cond, at, f);
            walk_block(body, f);
        }
        StmtKind::For {
            init,
            cond,
            step,
            body,
            ..
        } => {
            if let Some(s) = init {
                walk_stmt(s, f);
            }
            if let Some(c) = cond {
                walk_expr(c, at, f);
            }
            if let Some(s) = step {
                walk_stmt(s, f);
            }
            walk_block(body, f);
        }
        StmtKind::ForOf { source, body, .. } => {
            match source {
                ForSource::Path { place } => walk_expr(place, at, f),
                ForSource::Once { value, .. } => walk_expr(value, at, f),
                ForSource::Range { lo, hi } => {
                    walk_expr(lo, at, f);
                    walk_expr(hi, at, f);
                }
            }
            walk_block(body, f);
        }
        StmtKind::Return(e) => {
            if let Some(e) = e {
                walk_expr(e, at, f);
            }
        }
        StmtKind::Break(_) | StmtKind::Continue(_) => {}
        StmtKind::Block(b) | StmtKind::Unsafe(b) => walk_block(b, f),
        StmtKind::Expr(e) => walk_expr(e, at, f),
        StmtKind::Expect(x) => {
            walk_expr(&x.actual, at, f);
            for arg in &x.args {
                match arg {
                    ExpectArg::Expr(e) | ExpectArg::Arm(ArmValue::Cond(e)) => walk_expr(e, at, f),
                    ExpectArg::Arm(_) => {}
                }
            }
        }
    }
}

fn walk_expr(e: &Expr, at: Option<Span>, f: &mut dyn FnMut(&Expr, Option<Span>)) {
    f(e, at);
    match &e.kind {
        ExprKind::Field(b, _)
        | ExprKind::Deref(b)
        | ExprKind::NarrowedPayload(b, _, _)
        | ExprKind::Repeat(b, _)
        | ExprKind::Unary(_, b)
        | ExprKind::Cast(b, _)
        | ExprKind::Borrow(b)
        | ExprKind::AddrOf(b)
        | ExprKind::Try(b, _)
        | ExprKind::NonNull(b)
        | ExprKind::VoidOp(b)
        | ExprKind::IncDec { target: b, .. } => walk_expr(b, at, f),
        ExprKind::Destructure { pat, value } => {
            pat.places().into_iter().for_each(|p| walk_expr(p, at, f));
            walk_expr(value, at, f);
        }
        ExprKind::Index(a, b)
        | ExprKind::Binary(_, a, b)
        | ExprKind::Logical(_, a, b)
        | ExprKind::Coalesce(a, b)
        | ExprKind::Assign {
            target: a,
            value: b,
            ..
        } => {
            walk_expr(a, at, f);
            walk_expr(b, at, f);
        }
        ExprKind::Ternary(a, b, c) => {
            walk_expr(a, at, f);
            walk_expr(b, at, f);
            walk_expr(c, at, f);
        }
        ExprKind::Template(parts) => {
            for part in parts {
                if let TplPart::Hole(h) = part {
                    walk_expr(h, at, f);
                }
            }
        }
        ExprKind::ArrayLit(items)
        | ExprKind::TupleLit(items)
        | ExprKind::ObjectLit { fields: items, .. }
        | ExprKind::VariantLit { fields: items, .. }
        | ExprKind::New { values: items, .. } => items.iter().for_each(|c| walk_expr(c, at, f)),
        ExprKind::ArrayBuild { parts, .. } => {
            for part in parts {
                match part {
                    ArrayPart::Item(i) | ArrayPart::Spread(i, _) => walk_expr(i, at, f),
                }
            }
        }
        ExprKind::NewNamed { fields, .. } => fields.iter().for_each(|(_, i)| walk_expr(i, at, f)),
        ExprKind::Call {
            callee,
            receiver,
            args,
        } => {
            if let Callee::FnPtr(p) = callee {
                walk_expr(p, at, f);
            }
            if let Some(r) = receiver {
                walk_expr(r, at, f);
            }
            args.iter().for_each(|c| walk_expr(c, at, f));
        }
        ExprKind::OptionalChain(chain) => {
            walk_expr(&chain.base, at, f);
            if let OptMember::Call { callee, args } = &chain.member {
                if let Callee::FnPtr(p) = callee {
                    walk_expr(p, at, f);
                }
                args.iter().for_each(|c| walk_expr(c, at, f));
            }
        }
        ExprKind::Match { subject, arms } => {
            walk_expr(subject, at, f);
            for arm in arms {
                for value in &arm.values {
                    if let ArmValue::Cond(c) = value {
                        walk_expr(c, at, f);
                    }
                }
                if let Some(g) = &arm.guard {
                    walk_expr(g, at, f);
                }
                match &arm.body {
                    ArmBody::Expr(b) => walk_expr(b, at, f),
                    ArmBody::Block(b) => walk_block(b, f),
                    ArmBody::Return(Some(b)) => walk_expr(b, at, f),
                    ArmBody::Return(None) | ArmBody::Break(_) | ArmBody::Continue(_) => {}
                }
            }
        }
        ExprKind::Asm(asm) => {
            asm.ins.iter().for_each(|(_, v)| walk_expr(v, at, f));
            asm.outs
                .iter()
                .filter_map(|(_, v)| v.as_ref())
                .for_each(|c| walk_expr(c, at, f));
        }
        ExprKind::Local(_)
        | ExprKind::Static(_)
        | ExprKind::Const(_)
        | ExprKind::Arrow(_)
        | ExprKind::Never
        | ExprKind::NullLit => {}
    }
}
