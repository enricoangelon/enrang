//! Overloads (plan d.9; SPEC 4.14 S:829; A:888; owner 4A).
//!
//! A candidate matches a call when it takes that many arguments and every argument
//! fits its parameter as it is or through a chain of d.7, never a numeric
//! conversion: each candidate's call is typed in a probe, from its arguments alone,
//! and a number literal must keep its default type (`int`, `f64`), so with
//! overloads for `int` and `i64`, `describe(5)` picks `int`; only when no candidate
//! matches so does a literal take its parameter's type (plan choice: with `g(x: i64)`
//! and `g(s: &string)`, `g(1)` runs the first). An argument that fails by itself,
//! typed with no expected type, reports its own error instead of EN0451. Among the
//! matches, in order: (1) a non-generic overload beats a generic one (generic: with
//! type parameters written; D5's implicit ones do not count, plan choice); (2) of
//! the same kind, one whose arguments need no chain beats one that needs one; (3)
//! between generic ones still tied, the more specific wins, `F` over `G` when every
//! parameter type of `F` passes to `G`'s with `G`'s type parameters bound by `F`'s
//! types, and not the reverse (`&Slice<T>` beats `&T`). No step reads `views_ok`.
//! No match, or a tie after (3), is EN0451, with a note per candidate.
//!
//! The declaration check (EN0450), over each set of functions, methods or
//! constructors of one name in one scope of user code, each overload against the
//! ones before it in the source: overloads with the same parameter types (only the
//! result differing, or nothing) and overloads that one call could match through
//! a default parameter are EN0450 at the later one's name (a constructor's
//! `constructor` keyword), with the earlier one as the secondary. It also runs the
//! written-type bound check of declarations (`generic::check_decl_types`).

use std::collections::BTreeMap;

use enrang_base::{Span, Symbol};
use enrang_diag::{Code, Diagnostic};
use enrang_hir::{DefId, DefKind, ExprKind, ItemPath, ModulePath, ParamId, Receiver, Ty, TyKind};

use crate::cx::Sema;
use crate::typeck::call::CallSite;
use crate::typeck::generic::{self, number_literal};
use crate::typeck::infer::VarKind;
use crate::typeck::{FnCtxt, Site};

/// One matching candidate, for the ranking.
#[derive(Copy, Clone, Debug)]
struct Match {
    def: DefId,
    generic: bool,
    chain: bool,
}

impl FnCtxt<'_, '_> {
    /// The overload of `cands` that `call` runs (S:829); `None` after EN0451.
    pub(crate) fn select_overload(&mut self, cands: &[DefId], call: &CallSite) -> Option<DefId> {
        let span = call.expr.span;
        let mut errors = Vec::new();
        let mut matches = self.matching(cands, call, true, &mut errors);
        if matches.is_empty() {
            matches = self.matching(cands, call, false, &mut errors);
        }
        if matches.is_empty() {
            if !self.args_fail_alone(call, &errors) {
                self.no_overload(cands, span, call.at);
            }
            return None;
        }
        if matches.iter().any(|m| !m.generic) {
            matches.retain(|m| !m.generic);
        }
        if matches.iter().any(|m| !m.chain) {
            matches.retain(|m| !m.chain);
        }
        if let [one] = matches.as_slice() {
            return Some(one.def);
        }
        if matches.iter().all(|m| m.generic) {
            let defs: Vec<DefId> = matches.iter().map(|m| m.def).collect();
            let n = call.args.len();
            for &f in &defs {
                let wins = defs.iter().all(|&g| {
                    g == f
                        || (self.more_specific(f, g, n, call) && !self.more_specific(g, f, n, call))
                });
                if wins {
                    return Some(f);
                }
            }
        }
        let tied: Vec<DefId> = matches.iter().map(|m| m.def).collect();
        // Under `T extends A & B` a member both bounds declare with one signature,
        // generic or not, is one member (S:762): equal up to the names of their own
        // type parameters, the first stands for all.
        if call
            .at
            .is_some_and(|at| matches!(self.sema.tcx.kind(self.shallow(at)), TyKind::Param(_)))
            && self.one_signature(&tied)
        {
            return Some(tied[0]);
        }
        self.tied_overloads(&tied, span, call.at);
        None
    }

    /// Whether every candidate of `defs` has the first's signature: equal type
    /// parameters with equal bounds, parameter types and result (S:615).
    fn one_signature(&self, defs: &[DefId]) -> bool {
        use crate::classes::sig::{same_bounds, same_params, same_ret, view};
        let tcx = &*self.sema.tcx;
        let Some(first) = defs.first().and_then(|&d| view(tcx, d, &[], None)) else {
            return false;
        };
        defs[1..].iter().all(|&d| {
            view(tcx, d, &[], None).is_some_and(|v| {
                same_params(tcx, &first, &v)
                    && same_ret(tcx, &first, &v)
                    && same_bounds(tcx, &first, &v)
            })
        })
    }

    /// The candidates `call` matches, each typed in a probe from the arguments alone;
    /// with `defaults`, a number literal must keep its default type (S:829), else it
    /// may take its parameter's (plan choice: only when no candidate matches with
    /// the defaults, so adding an overload never breaks a call that one matched).
    /// `errors` gets the errors each candidate typed reported, as code and span.
    fn matching(
        &mut self,
        cands: &[DefId],
        call: &CallSite,
        defaults: bool,
        errors: &mut Vec<Vec<(Code, Span)>>,
    ) -> Vec<Match> {
        let span = call.expr.span;
        let mut matches = Vec::new();
        errors.clear();
        for &def in cands {
            let Some(sig) = self.sema.tcx.sig_opt(def) else {
                continue;
            };
            let required = sig.required_params();
            if call.args.len() < required || call.args.len() > sig.params.len() {
                continue;
            }
            let p = self.probe();
            let target = self.call_target(def, call);
            let typed = self.type_args(&target, call.args, None, span);
            let mut ok = !self.probe_failed();
            if ok && defaults {
                ok = call
                    .args
                    .iter()
                    .zip(&typed.args)
                    .all(|(arg, e)| self.keeps_default(arg, e.ty));
            }
            let chain = typed.chain;
            errors.push(
                self.sema
                    .dcx
                    .take()
                    .iter()
                    .filter(|d| d.severity.fails())
                    .map(|d| (d.code, d.primary.span))
                    .collect(),
            );
            self.rollback(p);
            if ok {
                matches.push(Match {
                    def,
                    generic: self.written_generic(def),
                    chain,
                });
            }
        }
        matches
    }

    /// Whether some non-arrow argument of `call` is rejected by itself, typed with no
    /// expected type (`` `e` has no member `value` ``): then every candidate failed
    /// for it, its own errors are reported, and EN0451 is not. An argument that is
    /// `Error` alone counts only when every candidate's probe (`errors`) reported an
    /// error inside it too, so one that needs an expected type (a bare overloaded
    /// name, `null`, `[]`) never hides the EN0451 that another argument causes. An
    /// argument whose type survives an error inside it (`k(&x.left)?`) counts too,
    /// by the errors that typing it alone reports and that every candidate's probe
    /// reported as well.
    fn args_fail_alone(&mut self, call: &CallSite, errors: &[Vec<(Code, Span)>]) -> bool {
        let p = self.probe();
        let mut broken = false;
        for arg in call.args.iter().filter(|a| !generic::is_arrow(a)) {
            let e = self.check_expr(arg, crate::typeck::Expect::None);
            if self.is_error(e.ty) {
                let inside = |(_, at): &(Code, Span)| arg.span.lo <= at.lo && at.hi <= arg.span.hi;
                broken |= errors.iter().all(|errs| errs.iter().any(inside));
            }
        }
        if broken {
            self.commit(p);
            return true;
        }
        let alone = self.sema.dcx.take();
        self.rollback(p);
        if errors.is_empty() {
            return false;
        }
        let own: Vec<Diagnostic> = alone
            .into_iter()
            .filter(|d| {
                d.severity.fails() && errors.iter().all(|e| e.contains(&(d.code, d.primary.span)))
            })
            .collect();
        let broken = !own.is_empty();
        for diag in own {
            self.sema.emit(diag);
        }
        broken
    }

    /// Whether a number literal `arg`, typed `t`, kept its default type (S:829).
    fn keeps_default(&self, arg: &enrang_syntax::ast::Expr, t: Ty) -> bool {
        let Some(kind) = number_literal(arg) else {
            return true;
        };
        let t = self.resolve(t);
        if self.var_kind(t).is_some() {
            return true;
        }
        let common = self.sema.tcx.common();
        match kind {
            VarKind::Int => t == common.i32 || self.sema.tcx.references_error(t),
            _ => t == common.f64 || self.sema.tcx.references_error(t),
        }
    }

    /// Whether `def` has type parameters written on itself.
    fn written_generic(&self, def: DefId) -> bool {
        let tcx = &*self.sema.tcx;
        tcx.sig_opt(def).is_some_and(|sig| {
            tcx.generics(sig.generics)
                .params
                .iter()
                .any(|&p| tcx.param(p).implicit.is_none())
        })
    }

    /// Whether `f` is more specific than `g` over the first `n` parameters: each of
    /// `f`'s parameter types, its own type parameters as they stand, passes to
    /// `g`'s with `g`'s own type parameters fresh variables (S:829).
    fn more_specific(&mut self, f: DefId, g: DefId, n: usize, call: &CallSite) -> bool {
        let p = self.probe();
        let fs = self.rigid_params(f, call);
        let target = self.call_target(g, call);
        let tcx = &*self.sema.tcx;
        let gs: Vec<Ty> = tcx
            .sig_opt(g)
            .map(|s| {
                s.params
                    .iter()
                    .map(|q| tcx.subst(q.ty, &target.params, &target.args))
                    .collect()
            })
            .unwrap_or_default();
        for (&from, &to) in fs.iter().zip(&gs).take(n) {
            let value = self.mk_expr(from, Span::DUMMY, ExprKind::Never);
            let _ = self.coerce(value, to, Site::Arg);
        }
        let ok = !self.probe_failed();
        self.rollback(p);
        ok
    }

    /// `f`'s parameter types at `call`'s owner arguments, its own type parameters
    /// left as they are.
    fn rigid_params(&self, f: DefId, call: &CallSite) -> Vec<Ty> {
        let tcx = &*self.sema.tcx;
        let Some(sig) = tcx.sig_opt(f) else {
            return Vec::new();
        };
        let parent = tcx
            .generics(sig.generics)
            .parent
            .map(|p| tcx.all_params(p))
            .unwrap_or_default();
        let owner: Option<Vec<Ty>> = call
            .methods
            .iter()
            .find(|m| m.def == f)
            .map(|m| tcx.list(m.args).to_vec())
            .or_else(|| (!call.owner_args.is_empty()).then(|| call.owner_args.clone()));
        let (params, args): (Vec<ParamId>, Vec<Ty>) = match owner {
            Some(args) if args.len() == parent.len() => (parent, args),
            _ => (Vec::new(), Vec::new()),
        };
        sig.params
            .iter()
            .map(|q| tcx.subst(q.ty, &params, &args))
            .collect()
    }

    /// EN0451: no overload matches; `at`, for a method, the receiver's type, which
    /// an interface member's `Self` is shown as.
    fn no_overload(&mut self, cands: &[DefId], span: Span, at: Option<Ty>) {
        self.mark_call_reported();
        let what = self.overload_noun(cands);
        let mut diag = Diagnostic::new(
            Code::EN0451,
            format!("no {what} matches these arguments"),
            span,
            "no overload takes these arguments",
        );
        for &c in cands {
            diag = diag.note(format!("candidate: `{}`", self.signature_string(c, at)));
        }
        self.sema.emit(diag);
    }

    /// EN0451: two or more overloads still tie; `at` as for `no_overload`.
    fn tied_overloads(&mut self, tied: &[DefId], span: Span, at: Option<Ty>) {
        self.mark_call_reported();
        let what = self.overload_noun(tied);
        let mut diag = Diagnostic::new(
            Code::EN0451,
            format!("more than one {what} matches"),
            span,
            "these arguments match more than one overload equally",
        );
        for &c in tied {
            diag = diag.note(format!("candidate: `{}`", self.signature_string(c, at)));
        }
        self.sema.emit(diag);
    }

    /// `overload of `f`` or, for constructors, `constructor of `User``.
    fn overload_noun(&self, cands: &[DefId]) -> String {
        let Some(&first) = cands.first() else {
            return "overload".to_owned();
        };
        let name = self.callee_name(first);
        match self.sema.tcx.def(first).kind {
            DefKind::Ctor => format!("constructor of `{name}`"),
            _ => format!("overload of `{name}`"),
        }
    }

    /// A candidate as a note prints it: `f<T>(a: &T, b: i64): void`, a
    /// constructor as `User(name: string)`, an interface member's `Self` as `at`,
    /// the receiver's type (`compare(other: &T): int` on a `T extends Ord`).
    fn signature_string(&self, def: DefId, at: Option<Ty>) -> String {
        let at = at.map(|t| crate::typeck::infer::display_in(self.sema.tcx, &self.infer, t));
        signature_string(self.sema, def, at)
    }
}

/// [`FnCtxt::signature_string`].
fn signature_string(sema: &Sema, def: DefId, self_ty: Option<Ty>) -> String {
    let tcx = &*sema.tcx;
    let data = tcx.def(def);
    let Some(sig) = tcx.sig_opt(def) else {
        return String::new();
    };
    // An interface member's `Self` shown as the receiver's type.
    let self_param = data
        .parent
        .and_then(|p| tcx.adt_of(p))
        .and_then(|a| tcx.adt(a).as_interface())
        .map(|i| i.self_param);
    let at_self = |t: Ty| match (self_param, self_ty) {
        (Some(p), Some(s)) => tcx.subst(t, &[p], &[s]),
        _ => t,
    };
    let name = match data.kind {
        DefKind::Ctor => data
            .parent
            .and_then(|p| tcx.def(p).name())
            .map_or_else(String::new, |n| n.as_str().to_owned()),
        _ => data
            .name()
            .map_or_else(String::new, |n| n.as_str().to_owned()),
    };
    let written: Vec<String> = tcx
        .generics(sig.generics)
        .params
        .iter()
        .filter(|&&p| tcx.param(p).implicit.is_none())
        .map(|&p| {
            // With its bounds, which tell two candidates apart (S:615).
            let def = tcx.param(p);
            let bounds: Vec<String> = def
                .bounds
                .iter()
                .map(|&b| {
                    let bound = tcx.bound(b);
                    tcx.ty_string(tcx.mk_adt(bound.adt(), &tcx.list(bound.args())))
                })
                .collect();
            match bounds.is_empty() {
                true => def.name.as_str().to_owned(),
                false => format!("{} extends {}", def.name, bounds.join(" & ")),
            }
        })
        .collect();
    let generics = if written.is_empty() {
        String::new()
    } else {
        format!("<{}>", written.join(", "))
    };
    let params: Vec<String> = sig
        .params
        .iter()
        .map(|p| {
            let ty = at_self(p.ty);
            let shown = match tcx.kind(ty) {
                TyKind::Ref(inner) => match tcx.kind(inner) {
                    TyKind::Param(x) => match tcx.param(x).implicit {
                        Some(enrang_hir::Implicit::Interface(adt)) => {
                            format!("&{}", tcx.ty_string(tcx.mk_adt(adt, &[])))
                        }
                        _ => tcx.ty_string(ty),
                    },
                    _ => tcx.ty_string(ty),
                },
                _ => tcx.ty_string(ty),
            };
            let opt = if p.has_default { "?" } else { "" };
            format!("{}{opt}: {shown}", p.name)
        })
        .collect();
    match data.kind {
        DefKind::Ctor => format!("{name}({})", params.join(", ")),
        _ => format!(
            "{name}{generics}({}): {}",
            params.join(", "),
            tcx.ty_string(at_self(sig.ret))
        ),
    }
}

/// EN0450 over every overload set of user code, then the written-type bound
/// check of declarations.
pub(crate) fn check_decls(sema: &mut Sema) {
    let tcx = &*sema.tcx;
    let mut groups: BTreeMap<(ModulePath, Vec<Symbol>), Vec<DefId>> = BTreeMap::new();
    for (def, data) in tcx.defs() {
        if tcx.module(data.module).library
            || !data.kind.has_sig()
            || data.kind == DefKind::Dtor
            || tcx.sig_opt(def).is_none()
        {
            continue;
        }
        let ItemPath {
            module, segments, ..
        } = data.path.clone();
        groups.entry((module, segments)).or_default().push(def);
    }
    let mut reports = Vec::new();
    for mut defs in groups.into_values().filter(|d| d.len() > 1) {
        defs.sort_by_key(|&d| (tcx.def(d).name_span, tcx.def(d).span));
        for (j, &b) in defs.iter().enumerate() {
            if let Some((a, reason)) = defs[..j]
                .iter()
                .find_map(|&a| indistinguishable(sema, a, b).map(|r| (a, r)))
            {
                reports.push((a, b, reason));
            }
        }
    }
    for (a, b, reason) in reports {
        let tcx = &*sema.tcx;
        let what = match tcx.def(b).kind {
            DefKind::Ctor => {
                let class = tcx.def(b).parent.and_then(|p| tcx.def(p).name());
                format!("constructors of `{}`", class.map_or("", |n| n.as_str()))
            }
            _ => format!(
                "overloads of `{}`",
                tcx.def(b).name().map_or("", |n| n.as_str())
            ),
        };
        let at = decl_name_span(tcx, b);
        let other = decl_name_span(tcx, a);
        let mut diag = Diagnostic::new(
            Code::EN0450,
            format!("a call can't tell these {what} apart"),
            at,
            "this overload",
        )
        .note(reason);
        if !other.is_dummy() {
            diag = diag.with_secondary(other, "and this one");
        }
        sema.emit(diag);
    }
    generic::check_decl_types(sema);
}

/// Where a declaration's name is written: its name, or a constructor's
/// `constructor` keyword.
pub(crate) fn decl_name_span(tcx: &enrang_hir::Tcx, def: DefId) -> Span {
    let data = tcx.def(def);
    if data.kind != DefKind::Ctor || data.span.is_dummy() {
        return data.name_span;
    }
    let text = tcx.map().text(data.span);
    match text.find("constructor") {
        Some(at) => {
            let lo = data.span.lo + at as u32;
            Span {
                lo,
                hi: lo + "constructor".len() as u32,
            }
        }
        None => data.name_span,
    }
}

/// Why one call could not tell overloads `a` and `b` apart, if it could not.
fn indistinguishable(sema: &Sema, a: DefId, b: DefId) -> Option<String> {
    let tcx = &*sema.tcx;
    let (sa, sb) = (tcx.sig_opt(a)?, tcx.sig_opt(b)?);
    let is_static = |r: Option<Receiver>| r == Some(Receiver::Static);
    if is_static(sa.receiver) != is_static(sb.receiver) {
        return None;
    }
    let own_a = tcx.generics(sa.generics).params.clone();
    let own_b = tcx.generics(sb.generics).params.clone();
    let (from, to): (Vec<ParamId>, Vec<Ty>) = if own_a.len() == own_b.len() {
        (own_b, own_a.iter().map(|&p| tcx.mk_param(p)).collect())
    } else {
        (Vec::new(), Vec::new())
    };
    let pa: Vec<Ty> = sa.params.iter().map(|p| p.ty).collect();
    let pb: Vec<Ty> = sb
        .params
        .iter()
        .map(|p| tcx.subst(p.ty, &from, &to))
        .collect();
    let same = |x: &[Ty], y: &[Ty]| {
        x.len() == y.len() && x.iter().zip(y).all(|(&s, &t)| tcx.same_ignoring_rows(s, t))
    };
    if same(&pa, &pb) {
        let ra = sa.ret;
        let rb = tcx.subst(sb.ret, &from, &to);
        return Some(if tcx.same_ignoring_rows(ra, rb) {
            "they take the same parameters".to_owned()
        } else {
            "they differ only in their return type".to_owned()
        });
    }
    let lo = sa.required_params().max(sb.required_params());
    let hi = pa.len().min(pb.len());
    (lo..=hi).find(|&k| same(&pa[..k], &pb[..k])).map(|k| {
        let args = match k {
            0 => "no arguments".to_owned(),
            1 => "1 argument".to_owned(),
            n => format!("{n} arguments"),
        };
        format!("a call with {args} matches both, through a default parameter")
    })
}
