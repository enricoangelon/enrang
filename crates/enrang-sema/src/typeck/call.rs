//! Calls (plan d.9's `call.rs`; SPEC 4.14; A:898; owner 3B).
//!
//! The callee forms: a function name (`Res::Fns`, overloads included); a method
//! found by `member` on a receiver (`recv.m()`, `recv?.m()`); a `static` method
//! through a type path (`Counter.make()`, `Stack<i64>.empty()`,
//! `i64[].withCapacity(8)`); a function through a namespace (`u.helper()`); an `fn`
//! or closure value (`Callee::FnPtr`, `Callee::Closure`), which a nullable one is
//! only where a fact makes it non-null, else EN0428 (S:827); a form (`Res::Form`,
//! 4A's `check_form`, `Err` to 4C's `check_err`; `console.log` through the form's
//! name; `mem.forget` and `cpu.has` through their namespaces, with EN0908 for an
//! unknown feature); `super(...)` and `super.m()` (plan c.5, `Callee::SuperCtor` and
//! `Callee::Super`). Anything else called is EN0428, with the `new` fix-it only for
//! a class or an alias of one; an `fn` field called through `?.` is EN0428 too, a
//! value that may be `null` (plan doc gap G38); `x.destructor()` is EN0606. A
//! callee or receiver whose type is a variable a later assignment decided is called
//! at that type. A method called through a value is checked for being `static`
//! before its visibility, so a misuse gets one diagnostic.
//!
//! One non-generic candidate with no explicit type arguments is checked here:
//! the argument count against the parameters, counting defaults and `?` (EN0423),
//! then each argument at its parameter's type, the owner's parameters replaced by
//! the receiver's arguments and `Self` by the receiver's class, as a coercion site
//! (`Site::Arg`). Overload sets, generic callees and explicit type arguments go to
//! 4A's seams, `select_overload` and `check_generic_call`. A receiver's narrowed
//! type is committed only after the arguments are checked (A:898): a fact an
//! argument kills leaves the receiver nullable, which the coercion to the type
//! the lookup used reports. Before the first arrow argument, the prescan of the
//! call's arrows kills the facts their bodies change (A:900, 4B). Each argument is
//! offered to 4B's `record_ref` as a `CallArg`, and each hidden argument of a local
//! function as a `HiddenArg` under the call's expression id (A:898). An optional
//! call's `OptChain` holds no receiver: MIR passes the payload as `call_receiver`
//! would (plan doc gap G37).

use enrang_base::{Span, Symbol};
use enrang_diag::{Code, Diagnostic, Edit, Help};
use enrang_hir::{
    self as hir, Adjust, Callee, DefId, DefKind, ExprKind, FnRef, FormKind, FormName, FoundMethod,
    Implicit, IntrinsicKind, IntrinsicName, LocalKind, MemberKind, OptChain, OptMember, Receiver,
    RecordKind, Res, Ty, TyKind, Vis,
};
use enrang_syntax::ast::{self, Ident};
use enrang_target::Feature;

use crate::resolve::{scope, toplevel};
use crate::typeck::member::Member;
use crate::typeck::narrow::Prescan;
use crate::typeck::path::{PathBase, TypeBase};
use crate::typeck::{Expect, FnCtxt, Site};

/// One call: its AST, its typed receiver, explicit type arguments and arguments.
///
/// `receiver`, for a method, is the receiver as the call passes it to the first
/// candidate: a reference, auto-borrowed or already one, or for a `move` method the
/// place itself (`call_receiver`); for `super.m()` it is `this`, upcast.
pub(crate) struct CallSite<'e> {
    pub expr: &'e ast::Expr,
    pub receiver: Option<hir::Expr>,
    pub type_args: &'e [ast::TypeExpr],
    pub args: &'e [ast::Expr],
    /// For a method call: the methods the lookup found, each with its owner's
    /// arguments at the receiver, which 4A reads for the one it runs; empty
    /// otherwise.
    pub methods: Vec<FoundMethod>,
    /// For a `static` call through a written type: that type's arguments.
    pub owner_args: Vec<Ty>,
    /// For a method call: the type the member was found at (`Member.at`), which
    /// gives an interface method its `Self` and a bounded `T` its `BoundMember`.
    pub at: Option<Ty>,
    /// `recv?.m(args)` on a nullable receiver: the call is an `OptionalChain` whose
    /// base is `receiver`.
    pub optional: bool,
}

impl CallSite<'_> {
    /// The callee's AST.
    fn callee(&self) -> Option<&ast::Expr> {
        match &self.expr.kind {
            ast::ExprKind::Call { callee, .. } => Some(callee),
            _ => None,
        }
    }
}

/// One parameter as a call sees it: its type at this call, and whether a call may
/// leave it out (a default or `?`).
#[derive(Copy, Clone, Debug)]
struct ParamAt {
    ty: Ty,
    optional: bool,
}

impl FnCtxt<'_, '_> {
    /// A call expression.
    pub(crate) fn check_call(&mut self, e: &ast::Expr, ex: Expect) -> hir::Expr {
        let ast::ExprKind::Call {
            callee,
            type_args,
            args,
        } = &e.kind
        else {
            return self.error_expr(e.span);
        };
        let site = CallSite {
            expr: e,
            receiver: None,
            type_args,
            args,
            methods: Vec::new(),
            owner_args: Vec::new(),
            at: None,
            optional: false,
        };
        match &callee.kind {
            ast::ExprKind::Ident(name) => self.call_name(*name, callee.span, site, ex),
            ast::ExprKind::Super => self.call_super_ctor(callee.span, site),
            ast::ExprKind::Member {
                base,
                name,
                optional,
            } => self.call_member(base, *name, *optional, site, ex),
            ast::ExprKind::TypeMember { ty, name } => {
                let base = ty.span;
                let ty = self.lower_body_type(ty, false);
                let path = PathBase::Type(TypeBase { ty, infer: None });
                self.static_call(path, base, *name, site, ex)
            }
            _ => {
                let f = self.check_expr(callee, Expect::None);
                self.call_value(f, site)
            }
        }
    }

    /// `name(args)`: a local holding an `fn` or closure value, a function or an
    /// overload set, a form, a top-level variable; anything else is EN0428.
    fn call_name(&mut self, name: Symbol, span: Span, site: CallSite, ex: Expect) -> hir::Expr {
        if let Some(local) = self.scopes.lookup(name) {
            let ty = self.locals[local].ty;
            let f = self.mk_expr(ty, span, ExprKind::Local(local));
            return self.call_value(f, site);
        }
        let ident = Ident { name, span };
        match scope::lookup_value(self.sema, self.at, ident) {
            Res::Form(FormName::Err) => self.check_err(site.expr, ex),
            Res::Form(form) => self.check_form(form, site.expr, ex),
            Res::Fns(cands) => {
                for &def in &cands {
                    toplevel::check_use(self.sema, self.at, def, span);
                }
                self.call_fns(&cands, &[], ident, site, ex)
            }
            Res::Def(def) => match self.sema.tcx.def(def).kind {
                DefKind::Const | DefKind::Static => {
                    let f = self.check_path(site.callee().expect("a call"), Expect::None);
                    self.call_value(f, site)
                }
                DefKind::Adt(_) | DefKind::TypeAlias | DefKind::StrUnion(_) => {
                    let mut diag = Diagnostic::new(
                        Code::EN0428,
                        format!("`{name}` is not callable"),
                        span,
                        "a type, not a function",
                    );
                    // Only a class is made with `new` (EN0221 for the rest); one
                    // with no constructor in its chain by naming its fields (S:580),
                    // where arguments would be EN0449.
                    match self.names_class(def) {
                        Some(true) => {
                            diag = diag.with_help(Help::machine(
                                format!("create one with `new {name}(...)`"),
                                vec![Edit::insert(span.lo, "new ")],
                            ));
                        }
                        Some(false) => {
                            diag = diag.with_help(Help::text(format!(
                                "create one by naming its fields: `new {name} {{ ... }}`"
                            )));
                        }
                        None => {}
                    }
                    self.sema.emit(diag);
                    self.untyped_call(&site)
                }
                _ => {
                    self.not_callable(span, "not a function");
                    self.untyped_call(&site)
                }
            },
            Res::TopVar(_) | Res::Local(_) => {
                let f = self.check_path(site.callee().expect("a call"), Expect::None);
                self.call_value(f, site)
            }
            Res::PrimType(_) | Res::TyParam(_) | Res::SelfTy => {
                self.not_callable(span, "a type, not a function");
                self.untyped_call(&site)
            }
            Res::Namespace(_) => {
                self.not_a_value(ident, "a namespace");
                self.untyped_call(&site)
            }
            Res::Err => {
                self.unresolved_value(ident);
                self.untyped_call(&site)
            }
        }
    }

    /// Whether type definition `def` names a class: a class, or an alias of one.
    fn names_class(&self, def: DefId) -> Option<bool> {
        let tcx = &*self.sema.tcx;
        let adt = match tcx.def(def).kind {
            DefKind::Adt(adt) => Some(adt),
            DefKind::TypeAlias => tcx.alias(def).and_then(|a| match tcx.kind(a.ty) {
                TyKind::Adt(adt, _) => Some(adt),
                _ => None,
            }),
            _ => None,
        }?;
        tcx.adt(adt).as_class()?;
        // Whether a class of its chain declares a constructor.
        let mut cur = Some(adt);
        let mut steps = 0;
        while let Some(class) = cur {
            let class_def = tcx.adt(class).as_class()?;
            if !class_def.ctors.is_empty() {
                return Some(true);
            }
            steps += 1;
            if steps > tcx.adts().count() {
                break;
            }
            cur = class_def.base.and_then(|b| match tcx.kind(b) {
                TyKind::Adt(b, _) => Some(b),
                _ => None,
            });
        }
        Some(false)
    }

    /// A call of a function or of one of an overload set; `owner_args` are the
    /// arguments of a static method's owner.
    fn call_fns(
        &mut self,
        cands: &[DefId],
        owner_args: &[Ty],
        name: Ident,
        site: CallSite,
        ex: Expect,
    ) -> hir::Expr {
        let site = CallSite {
            owner_args: owner_args.to_vec(),
            ..site
        };
        let [def] = cands else {
            return self.dispatch(cands, site, ex);
        };
        if !site.type_args.is_empty() || self.is_generic(*def) {
            return self.dispatch(cands, site, ex);
        }
        let (params, ret) = self.sig_at(*def, owner_args, None);
        let args = self.check_args(&params, &site, name.name.as_str(), Some(*def));
        let fn_args = self.fn_ref_args(*def, owner_args);
        let callee = self.callee_of(*def, fn_args);
        let call = self.mk_expr(
            ret,
            site.expr.span,
            ExprKind::Call {
                callee,
                receiver: None,
                args,
            },
        );
        self.record_hidden_args(*def, &call);
        call
    }

    /// Records, for 4B, each hidden argument a call of local function `f` passes
    /// (A:898): the top-level variable's local in this body, under the call's own
    /// expression id and span, since the HIR `Call` lists no hidden argument. A
    /// variable this body has no local for yet is passed by no path a fact holds on.
    pub(crate) fn record_hidden_args(&mut self, f: DefId, call: &hir::Expr) {
        if self.sema.tcx.def(f).kind != DefKind::LocalFn {
            return;
        }
        let vars = toplevel::hidden_args(self.sema, f).to_vec();
        for var in vars {
            let local = self.locals.iter_enumerated().find(|(_, decl)| {
                matches!(decl.kind, LocalKind::TopVar(v) | LocalKind::Hidden(v) if v == var)
            });
            let Some((local, decl)) = local else {
                continue;
            };
            let passed = hir::Expr::new(call.id, decl.ty, call.span, ExprKind::Local(local));
            self.record_ref(&passed, RecordKind::HiddenArg);
        }
    }

    /// The seams of 4A: an overload set picks its overload, which, like a single
    /// generic callee or one given type arguments, `check_generic_call` types.
    fn dispatch(&mut self, cands: &[DefId], site: CallSite, ex: Expect) -> hir::Expr {
        let chosen = match cands {
            [one] => Some(*one),
            many => self.select_overload(many, &site),
        };
        match chosen {
            Some(f) => self.check_generic_call(f, &site, ex),
            None => self.error_expr(site.expr.span),
        }
    }

    /// Whether `def` has type parameters of its own (written, or D5's implicit
    /// ones), which a call infers (4A).
    fn is_generic(&self, def: DefId) -> bool {
        let tcx = &*self.sema.tcx;
        tcx.sig_opt(def)
            .is_some_and(|sig| !tcx.generics(sig.generics).params.is_empty())
    }

    /// `def`'s parameters and result at a call: its owner's parameters (a class's,
    /// an interface's, an `extend` block's) replaced by `owner_args`, and an
    /// interface's `Self` by `self_ty`.
    fn sig_at(&self, def: DefId, owner_args: &[Ty], self_ty: Option<Ty>) -> (Vec<ParamAt>, Ty) {
        let tcx = &*self.sema.tcx;
        let Some(sig) = tcx.sig_opt(def) else {
            return (Vec::new(), tcx.common().error);
        };
        let owner = match tcx.generics(sig.generics).parent {
            Some(parent) => tcx.all_params(parent),
            None => Vec::new(),
        };
        let n = owner.len().min(owner_args.len());
        let mut params = owner[..n].to_vec();
        let mut args = owner_args[..n].to_vec();
        if let Some(self_ty) = self_ty
            && let Some(parent) = tcx.def(def).parent
            && let Some(adt) = tcx.adt_of(parent)
            && let Some(iface) = tcx.adt(adt).as_interface()
        {
            params.push(iface.self_param);
            args.push(self_ty);
        }
        let at = sig
            .params
            .iter()
            .map(|p| ParamAt {
                ty: tcx.subst(p.ty, &params, &args),
                optional: p.has_default,
            })
            .collect();
        (at, tcx.subst(sig.ret, &params, &args))
    }

    /// The arguments of a call against `params`: EN0423 when their number is outside
    /// what the callee takes; each argument at its parameter's type as a coercion
    /// site, one past the parameters with no expected type. `name` is the callee as
    /// messages name it, `decl` its declaration.
    fn check_args(
        &mut self,
        params: &[ParamAt],
        site: &CallSite,
        name: &str,
        decl: Option<DefId>,
    ) -> Vec<hir::Expr> {
        let required = params.iter().filter(|p| !p.optional).count();
        let given = site.args.len();
        if given < required || given > params.len() {
            self.arity_error(name, required, params.len(), given, site.expr.span, decl);
        }
        let mut prescanned = false;
        site.args
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                if !prescanned && crate::typeck::narrow::holds_arrow(arg) {
                    prescanned = true;
                    self.prescan_kill(Prescan::Arrows(site.args));
                }
                let typed = match params.get(i) {
                    Some(p) => self.check_expr(arg, Expect::Coerce(p.ty, Site::Arg)),
                    None => self.check_expr(arg, Expect::None),
                };
                // 4B keeps the record when the argument reaches a narrowed path.
                self.record_ref(&typed, RecordKind::CallArg);
                typed
            })
            .collect()
    }

    /// EN0423: `name` takes `lo` to `hi` arguments, but `given` were given.
    pub(crate) fn arity_error(
        &mut self,
        name: &str,
        lo: usize,
        hi: usize,
        given: usize,
        span: Span,
        decl: Option<DefId>,
    ) {
        self.mark_call_reported();
        let count = |n: usize| match n {
            0 => "no arguments".to_owned(),
            1 => "1 argument".to_owned(),
            n => format!("{n} arguments"),
        };
        let takes = match lo == hi {
            true => count(lo),
            false => format!("{lo} to {hi} arguments"),
        };
        let gave = match given {
            0 => "none were given".to_owned(),
            1 => "1 was given".to_owned(),
            n => format!("{n} were given"),
        };
        let label = match given < lo {
            true => "too few arguments",
            false => "too many arguments",
        };
        let mut diag = Diagnostic::new(
            Code::EN0423,
            format!("`{name}` takes {takes}, but {gave}"),
            span,
            label,
        );
        if let Some(def) = decl {
            let tcx = &*self.sema.tcx;
            let data = tcx.def(def);
            if !tcx.module(data.module).library && !data.name_span.is_dummy() {
                diag = diag.with_secondary(data.name_span, format!("`{name}` is declared here"));
            }
        }
        self.sema.emit(diag);
    }

    /// How a call reaches `def`: a host call, an intrinsic whose payload the call
    /// decides, a foreign function, or the function itself.
    pub(crate) fn callee_of(&self, def: DefId, args: hir::TyList) -> Callee {
        let tcx = &*self.sema.tcx;
        let data = tcx.def(def);
        if let Some(id) = data.attrs.host_call {
            return Callee::HostCall(id);
        }
        if let Some(name) = data.attrs.intrinsic
            && let Some(kind) = intrinsic_kind(name, tcx.list(args).first().copied())
        {
            return Callee::Intrinsic(kind, args);
        }
        if data.kind == DefKind::DeclareFn && data.attrs.intrinsic.is_none() {
            return Callee::Foreign(def);
        }
        Callee::Fn(FnRef { def, args })
    }

    /// EN0428 at `span`: the callee is no function.
    fn not_callable(&mut self, span: Span, label: &str) {
        let written = self.source(span);
        self.sema.emit(Diagnostic::new(
            Code::EN0428,
            format!("`{written}` is not callable"),
            span,
            label,
        ));
    }

    /// The arguments of a call that typing rejected, each with no expected type, so
    /// the errors inside them still show; the call is `Error`.
    pub(crate) fn untyped_call(&mut self, site: &CallSite) -> hir::Expr {
        self.mark_call_reported();
        let mut prescanned = false;
        for arg in site.args {
            if !prescanned && crate::typeck::narrow::holds_arrow(arg) {
                prescanned = true;
                self.prescan_kill(Prescan::Arrows(site.args));
            }
            let _ = self.check_expr(arg, Expect::None);
        }
        self.error_expr(site.expr.span)
    }

    // ---------------------------------------------------------------------------
    // Values called.

    /// A call through a value: an `fn` value (`Callee::FnPtr`) or a closure
    /// (`Callee::Closure` for a local); a nullable one only where its facts make it
    /// non-null, else EN0428 (S:827, T:916); anything else EN0428.
    fn call_value(&mut self, f: hir::Expr, site: CallSite) -> hir::Expr {
        let callee_span = site.callee().map_or(f.span, |c| c.span);
        let written = self.source(callee_span);
        let f = self.narrowed(f);
        // A local whose type a later assignment decided is called at that type.
        let fty = self.resolve(f.ty);
        let tcx = &*self.sema.tcx;
        match tcx.kind(fty) {
            TyKind::FnPtr(_, sig) | TyKind::Closure(sig) => {
                let closure = matches!(tcx.kind(fty), TyKind::Closure(_));
                let sig = tcx.fn_sig(sig);
                let params: Vec<ParamAt> = sig
                    .params
                    .iter()
                    .map(|&(ty, _)| ParamAt {
                        ty,
                        optional: false,
                    })
                    .collect();
                let ret = sig.ret;
                let args = self.check_args(&params, &site, &written, None);
                let callee = match (closure, local_of(&f)) {
                    (true, Some(local)) => Callee::Closure(local),
                    _ => Callee::FnPtr(Box::new(f)),
                };
                self.mk_expr(
                    ret,
                    site.expr.span,
                    ExprKind::Call {
                        callee,
                        receiver: None,
                        args,
                    },
                )
            }
            TyKind::Nullable(inner)
                if matches!(tcx.kind(inner), TyKind::FnPtr(..) | TyKind::Closure(_)) =>
            {
                self.sema.emit(
                    Diagnostic::new(
                        Code::EN0428,
                        format!("`{written}` may be `null`, so it can't be called"),
                        callee_span,
                        "this may be `null`",
                    )
                    .with_help(Help::text(format!(
                        "check it first: `if ({written} != null) {{ {written}(...); }}`"
                    ))),
                );
                self.untyped_call(&site)
            }
            TyKind::Error => self.untyped_call(&site),
            _ => {
                let shown = self.ty_str(fty);
                self.not_callable(callee_span, &format!("its type is `{shown}`"));
                self.untyped_call(&site)
            }
        }
    }

    // ---------------------------------------------------------------------------
    // Members called.

    /// `base.name(args)` or `base?.name(args)`.
    fn call_member(
        &mut self,
        base: &ast::Expr,
        name: Ident,
        optional: bool,
        site: CallSite,
        ex: Expect,
    ) -> hir::Expr {
        if name.name.as_str() == "destructor" {
            if !matches!(base.kind, ast::ExprKind::Super) && self.path_base(base).is_none() {
                let _ = self.check_operand(base, optional);
            }
            self.destructor_named(site.expr.span, base.span);
            return self.untyped_call(&site);
        }
        if matches!(base.kind, ast::ExprKind::Super) {
            return self.call_super_method(base.span, name, site, ex);
        }
        if !optional && let Some(path) = self.path_base(base) {
            return self.static_call(path, base.span, name, site, ex);
        }
        let raw = self.check_operand(base, optional);
        if !optional
            && name.name.as_str() == "toString"
            && let Some(form) = self.to_string_form(&raw, name, site.args, site.expr)
        {
            return form;
        }
        self.call_method(raw, name, optional, site, ex)
    }

    /// A method called on a typed receiver `raw`.
    fn call_method(
        &mut self,
        raw: hir::Expr,
        name: Ident,
        optional: bool,
        site: CallSite,
        ex: Expect,
    ) -> hir::Expr {
        let narrowed = self.narrowed(raw);
        let member = self.lookup_with(narrowed.clone(), name, optional, true);
        let nullable_base = matches!(
            self.sema.tcx.kind(self.shallow(member.receiver.ty)),
            TyKind::Nullable(_)
        );
        let field = match (&member.object_field, member.found.as_ref().map(|f| &f.kind)) {
            (Some((field, ty)), _) => Some((*field, *ty)),
            (None, Some(MemberKind::Field { adt, field })) => {
                let args = member.found.as_ref().map(|f| f.args);
                let args = args.unwrap_or_else(|| self.sema.tcx.empty_list());
                Some((*field, self.sema.tcx.field_ty(*adt, None, *field, args)))
            }
            _ => None,
        };
        if let Some((field, ty)) = field {
            let span = site.callee().map_or(name.span, |c| c.span);
            if optional && nullable_base {
                // An `fn` held in a field is called on a value known not to be
                // `null` (plan choice; S:750 covers methods only).
                return self.optional_fn_field(span, &member, name, site);
            }
            let f = self.field_expr(member, field, ty, optional, span);
            return self.call_value(f, site);
        }
        let Some(found) = member.found.clone() else {
            return self.untyped_call(&site);
        };
        let MemberKind::Methods(methods) = found.kind else {
            return self.untyped_call(&site);
        };
        let instance: Vec<FoundMethod> = methods
            .iter()
            .copied()
            .filter(|m| self.receiver_kind(m.def) != Some(Receiver::Static))
            .collect();
        if instance.is_empty() {
            let shown = self.sema.tcx.ty_string(member.at);
            self.sema.emit(
                Diagnostic::new(
                    Code::EN0303,
                    format!("`{shown}` has no member `{}`", name.name),
                    name.span,
                    "a `static` method, not a member of each value",
                )
                .note(format!(
                    "`{}` is `static`: call it through the type, `{shown}.{}()`",
                    name.name, name.name
                )),
            );
            return self.untyped_call(&site);
        }
        let optional_base = optional && nullable_base;
        if let [method] = instance.as_slice() {
            self.check_dispatched_two_word(member.at, method.def, site.args);
        }
        let [method] = instance.as_slice() else {
            return self.dispatch_method(&instance, &member, &narrowed, optional_base, site, ex);
        };
        if !site.type_args.is_empty() || self.is_generic(method.def) {
            return self.dispatch_method(&instance, &member, &narrowed, optional_base, site, ex);
        }
        let owner_args = self.sema.tcx.list(method.args).to_vec();
        let (params, ret) = self.sig_at(method.def, &owner_args, Some(member.at));
        let args = self.check_args(&params, &site, name.name.as_str(), Some(method.def));
        self.check_call_bounds(method.def, &owner_args, site.expr);
        self.commit_receiver(&narrowed);
        let callee = match self.sema.tcx.kind(member.at) {
            TyKind::Param(param) => Callee::BoundMember {
                param,
                member: name.name,
                found: method.def,
                args: method.args,
            },
            // A member the compiler synthesises (D12) is its glue form.
            _ if member.synthesised => Callee::Form(match name.name.as_str() {
                "equals" => FormKind::Equals,
                _ => FormKind::Clone,
            }),
            _ => {
                let fn_args = self.fn_ref_args(method.def, &owner_args);
                self.callee_of(method.def, fn_args)
            }
        };
        if optional && nullable_base {
            let tcx = &*self.sema.tcx;
            let (ty, void_result) = match tcx.kind(ret) {
                TyKind::Void => (ret, true),
                TyKind::Nullable(_) | TyKind::Error => (ret, false),
                _ => (tcx.mk_nullable(ret), false),
            };
            return self.mk_expr(
                ty,
                site.expr.span,
                ExprKind::OptionalChain(Box::new(OptChain {
                    base: member.receiver,
                    member: OptMember::Call { callee, args },
                    void_result,
                })),
            );
        }
        let receiver = self.call_receiver(&member, &narrowed, method.def);
        self.mk_expr(
            ret,
            site.expr.span,
            ExprKind::Call {
                callee,
                receiver,
                args,
            },
        )
    }

    /// EN1006 at each argument of a call whose callee is chosen when the program
    /// runs, through a class's method table or an interface's table, for an `&I`
    /// parameter of an interface no table can serve: the call needs its two-word
    /// form, which no single copy of the method provides (S:631, A:894).
    fn check_dispatched_two_word(&mut self, at: Ty, def: DefId, args: &[ast::Expr]) {
        let tcx = &*self.sema.tcx;
        let at = self.shallow(at);
        let runtime = match tcx.kind(at) {
            TyKind::Adt(adt, _) => match &tcx.adt(adt).kind {
                hir::AdtKind::Interface(_) => true,
                hir::AdtKind::Class(class) => {
                    class.modifier != hir::ClassModifier::Final
                        && tcx.def(def).vis != Vis::Private
                        && self.receiver_kind(def) != Some(Receiver::Static)
                }
                hir::AdtKind::Enum(_) => false,
            },
            // An `&I` parameter's value: one copy serves every class through the
            // interface's table (D5).
            TyKind::Param(q) => matches!(tcx.param(q).implicit, Some(Implicit::Interface(_))),
            _ => false,
        };
        if !runtime {
            return;
        }
        let Some(sig) = tcx.sig_opt(def).cloned() else {
            return;
        };
        let method = tcx
            .def(def)
            .name()
            .map_or_else(String::new, |n| n.to_string());
        for (param, arg) in sig.params.iter().zip(args) {
            let tcx = &*self.sema.tcx;
            let inner = match tcx.kind(param.ty) {
                TyKind::Nullable(n) => n,
                _ => param.ty,
            };
            let TyKind::Ref(r) = tcx.kind(inner) else {
                continue;
            };
            let adt = match tcx.kind(r) {
                TyKind::Param(q) => match tcx.param(q).implicit {
                    Some(Implicit::Interface(adt)) => adt,
                    _ => continue,
                },
                TyKind::Adt(adt, _) if tcx.adt(adt).is_interface() => adt,
                _ => continue,
            };
            let Some(member) = self.needs_class(adt) else {
                continue;
            };
            let iface = self.sema.tcx.adt(adt).name;
            let note = self.member_reason(adt, member);
            self.sema.emit(crate::typeck::iface::iface_unsupported(
                arg.span,
                format!(
                    "`{method}` is chosen when the program runs, so `{}` needs the two-word form of `&{iface}`",
                    param.name
                ),
                note,
                None,
            ));
        }
    }

    /// EN0428 for `o?.f(args)` where `f` is a field holding an `fn` or closure
    /// value: the field is read only on an `o` that is not `null`, so the call
    /// asks for that first.
    fn optional_fn_field(
        &mut self,
        span: Span,
        member: &Member,
        name: Ident,
        site: CallSite,
    ) -> hir::Expr {
        let written = self.source(span);
        let base = self.source(member.receiver.span);
        self.sema.emit(
            Diagnostic::new(
                Code::EN0428,
                format!("`{written}` may be `null`, so it can't be called"),
                span,
                "this may be `null`",
            )
            .with_help(Help::text(format!(
                "check it first: `if ({base} != null) {{ {base}.{}(...); }}`",
                name.name
            ))),
        );
        self.untyped_call(&site)
    }

    /// An overloaded or generic method: 4A's seams, with the receiver as a call
    /// passes it to the first candidate (`call_receiver`), or for `recv?.m()` on a
    /// nullable receiver the nullable base itself (`optional`), and the methods
    /// found with their owners' arguments.
    fn dispatch_method(
        &mut self,
        methods: &[FoundMethod],
        member: &Member,
        narrowed: &hir::Expr,
        optional: bool,
        site: CallSite,
        ex: Expect,
    ) -> hir::Expr {
        let defs: Vec<DefId> = methods.iter().map(|m| m.def).collect();
        // The upcast to an inherited method's class waits for the candidate 4A
        // runs (`finish_call`, `upcast_inherited`).
        let receiver = match optional {
            true => member.receiver.clone(),
            false => self
                .borrowed_receiver(member, narrowed, defs[0])
                .map(|r| *r)
                .unwrap_or_else(|| member.receiver.clone()),
        };
        let site = CallSite {
            receiver: Some(receiver),
            methods: methods.to_vec(),
            at: Some(member.at),
            optional,
            ..site
        };
        let call = self.dispatch(&defs, site, ex);
        // As on the one-candidate path: an argument that killed a fact the
        // receiver was typed through is reported (O6, S:743).
        if !optional {
            self.commit_receiver(narrowed);
        }
        call
    }

    /// Commits the receiver's narrowed type after the arguments (A:898): when an
    /// argument killed a fact the receiver was typed through, that is EN0401 with a
    /// note naming the argument (4B's `recheck_receiver`).
    fn commit_receiver(&mut self, narrowed: &hir::Expr) {
        self.recheck_receiver(narrowed);
    }

    /// A method's receiver kind.
    fn receiver_kind(&self, def: DefId) -> Option<Receiver> {
        self.sema.tcx.sig_opt(def).and_then(|s| s.receiver)
    }

    /// The receiver a call passes to method `def`: [`Self::borrowed_receiver`],
    /// then C21's `Upcast` when `def` is inherited (`upcast_inherited`).
    fn call_receiver(
        &mut self,
        member: &Member,
        narrowed: &hir::Expr,
        def: DefId,
    ) -> Option<Box<hir::Expr>> {
        let mut recv = self.borrowed_receiver(member, narrowed, def)?;
        self.upcast_inherited(&mut recv, member.at, def);
        Some(recv)
    }

    /// The receiver a call passes to method `def` before any upcast: none for a
    /// `static` method; for a `move` method the place the lookup reached; for any
    /// other, a reference: the receiver itself when it already is one, else the
    /// place auto-borrowed (`AutoBorrow`, after its `BoxDeref`s); then C18
    /// (`ArrayToSlice`, `FixedToSlice`) for a member of `Slice<T>` found from an
    /// array.
    fn borrowed_receiver(
        &mut self,
        member: &Member,
        narrowed: &hir::Expr,
        def: DefId,
    ) -> Option<Box<hir::Expr>> {
        let via_slice = member.found.as_ref().and_then(|f| f.via_slice);
        let mut recv = match self.receiver_kind(def) {
            None | Some(Receiver::Static) => return None,
            Some(Receiver::Move) => member.receiver.clone(),
            Some(Receiver::Ref(_)) => {
                let through_ref = matches!(
                    self.sema.tcx.kind(self.shallow(narrowed.ty)),
                    TyKind::Ref(_)
                ) && member.receiver.adjust.is_empty();
                match through_ref {
                    true => narrowed.clone(),
                    false => {
                        let mut recv = member.receiver.clone();
                        recv.adjust.push(Adjust::AutoBorrow);
                        recv
                    }
                }
            }
        };
        if let Some(adjust) = via_slice {
            recv.adjust.push(adjust);
        }
        Some(Box::new(recv))
    }

    /// C21 on an inherited method's receiver (A:2.4, A:4): when `def`, called with a
    /// reference receiver, is declared in a proper base of the class `at` the member
    /// was found at, `Upcast` to that base after the receiver's `AutoBorrow` or
    /// `Reborrow`, so MIR building reads it from the adjusts and the receiver
    /// reaches the call through a `Convert` that keeps its loans. Once: `super.m()`
    /// already upcasts `this`. A receiver of a type parameter calls a
    /// `BoundMember`, which mono resolves, and an interface's member is no class's.
    pub(crate) fn upcast_inherited(&self, recv: &mut hir::Expr, at: Ty, def: DefId) {
        if !matches!(self.receiver_kind(def), Some(Receiver::Ref(_)))
            || recv.adjust.contains(&Adjust::Upcast)
        {
            return;
        }
        let tcx = &*self.sema.tcx;
        let TyKind::Adt(class, args) = tcx.kind(self.shallow(at)) else {
            return;
        };
        let declaring = tcx.def(def).parent.and_then(|p| tcx.adt_of(p));
        let Some(declaring) = declaring.filter(|&d| d != class) else {
            return;
        };
        if tcx.adt(declaring).as_class().is_none() {
            return;
        }
        let mut base = tcx.base_of(class, args);
        let mut seen = vec![class];
        while let Some((c, cargs)) = base {
            if seen.contains(&c) {
                return;
            }
            if c == declaring {
                recv.adjust.push(Adjust::Upcast);
                return;
            }
            seen.push(c);
            base = tcx.base_of(c, cargs);
        }
    }

    // ---------------------------------------------------------------------------
    // Paths called.

    /// `base.name(args)` with `base` a type, namespace or form.
    fn static_call(
        &mut self,
        path: PathBase,
        base: Span,
        name: Ident,
        site: CallSite,
        ex: Expect,
    ) -> hir::Expr {
        match path {
            PathBase::Form(FormName::Console) => self.check_form(FormName::Console, site.expr, ex),
            PathBase::Form(_) => {
                let written = self.source(base);
                self.sema.emit(Diagnostic::new(
                    Code::EN0303,
                    format!("`{written}` has no member `{}`", name.name),
                    name.span,
                    "no such member",
                ));
                self.untyped_call(&site)
            }
            PathBase::Namespace(index) => self.ns_call(index, base, name, site, ex),
            PathBase::Type(tb) => self.type_call(tb, base, name, site, ex),
        }
    }

    /// `ns.name(args)`: a function the namespace shows, an `fn` value, or the forms
    /// `mem.forget` and `cpu.has`.
    fn ns_call(
        &mut self,
        index: usize,
        base: Span,
        name: Ident,
        site: CallSite,
        ex: Expect,
    ) -> hir::Expr {
        let module = self.sema.program.modules[index].path;
        match (module.as_str(), name.name.as_str()) {
            ("core/mem", "forget") => return self.mem_forget(site),
            ("core/cpu", "has") => return self.cpu_has(site),
            _ => {}
        }
        match scope::public_member(self.sema, index, name.name) {
            Some(Res::Fns(defs)) => self.call_fns(&defs, &[], name, site, ex),
            Some(Res::Def(def)) => match self.sema.tcx.def(def).kind {
                DefKind::Const | DefKind::Static => {
                    let f = self.check_operand(site.callee().expect("a call"), false);
                    self.call_value(f, site)
                }
                _ => {
                    let span = site.callee().map_or(name.span, |c| c.span);
                    self.not_callable(span, "not a function");
                    self.untyped_call(&site)
                }
            },
            Some(Res::Namespace(_)) => {
                self.not_a_value(name, "a namespace");
                self.untyped_call(&site)
            }
            Some(_) => self.untyped_call(&site),
            None => {
                self.ns_missing(index, base, name);
                self.untyped_call(&site)
            }
        }
    }

    /// `T.name(args)`: a `static` method; a case or a constant is EN0428.
    fn type_call(
        &mut self,
        tb: TypeBase,
        base: Span,
        name: Ident,
        site: CallSite,
        ex: Expect,
    ) -> hir::Expr {
        let ty = tb.ty;
        if tb.infer.is_none() && self.sema.tcx.references_error(ty) {
            return self.untyped_call(&site);
        }
        let callee_span = site.callee().map_or(name.span, |c| c.span);
        // The case named, if any, and whether it has fields.
        let case = match (tb.infer, self.sema.tcx.kind(ty)) {
            (Some(adt), _) | (None, TyKind::Adt(adt, _)) => {
                self.sema.tcx.adt(adt).as_enum().and_then(|e| {
                    e.variant_named(name.name)
                        .map(|(_, v)| !v.fields.is_empty())
                })
            }
            _ => None,
        };
        if let Some(has_fields) = case {
            let written = self.source(callee_span);
            self.sema.emit(
                Diagnostic::new(
                    Code::EN0428,
                    format!("`{written}` is not callable"),
                    callee_span,
                    "an enum case, not a function",
                )
                .with_help(Help::text(if has_fields {
                    format!(
                        "a case is written `{written}`, or with its fields, `{written} {{ ... }}`"
                    )
                } else {
                    format!("a case is written `{written}`")
                })),
            );
            return self.untyped_call(&site);
        }
        if self.prim_const(ty, name.name).is_some() {
            self.not_callable(callee_span, "a constant, not a function");
            return self.untyped_call(&site);
        }
        let Some(statics) = self.static_methods(ty, name, base) else {
            return self.untyped_call(&site);
        };
        let defs: Vec<DefId> = statics.iter().map(|m| m.def).collect();
        if tb.infer.is_some() {
            return self.dispatch(&defs, site, ex);
        }
        let owner_args = self.sema.tcx.list(statics[0].args).to_vec();
        self.call_fns(&defs, &owner_args, name, site, ex)
    }

    /// `mem.forget(x)` (SPEC 6): one argument of any type, by move.
    fn mem_forget(&mut self, site: CallSite) -> hir::Expr {
        if site.args.len() != 1 {
            self.arity_error("mem.forget", 1, 1, site.args.len(), site.expr.span, None);
        }
        let args = site
            .args
            .iter()
            .map(|a| self.check_expr(a, Expect::None))
            .collect();
        let void = self.sema.tcx.common().void;
        self.mk_expr(
            void,
            site.expr.span,
            ExprKind::Call {
                callee: Callee::Form(FormKind::MemForget),
                receiver: None,
                args,
            },
        )
    }

    /// `cpu.has("f")` (SPEC 6, S:1574): one string literal naming a feature, else
    /// EN0908.
    fn cpu_has(&mut self, site: CallSite) -> hir::Expr {
        if site.args.len() != 1 {
            self.arity_error("cpu.has", 1, 1, site.args.len(), site.expr.span, None);
            return self.untyped_call(&site);
        }
        let arg = &site.args[0];
        let feature = match &arg.kind {
            ast::ExprKind::Str(s) => Feature::from_name(s.as_str()),
            _ => None,
        };
        let typed = self.check_expr(arg, Expect::None);
        let Some(feature) = feature else {
            // A literal that names no feature, or no literal at all (which names
            // nothing the compiler can check).
            let head = match &arg.kind {
                ast::ExprKind::Str(s) => format!("unknown feature name `{}`", s.as_str()),
                _ => "a feature name must be a string literal".to_owned(),
            };
            self.sema.emit(Diagnostic::new(
                Code::EN0908,
                head,
                arg.span,
                "a feature name, written as a string literal",
            ));
            return self.error_expr(site.expr.span);
        };
        let bool_ty = self.sema.tcx.common().bool;
        self.mk_expr(
            bool_ty,
            site.expr.span,
            ExprKind::Call {
                callee: Callee::Form(FormKind::CpuHas(feature)),
                receiver: None,
                args: vec![typed],
            },
        )
    }

    // ---------------------------------------------------------------------------
    // `super`.

    /// The class whose body this is, with `this`, and the class's base: EN0219 where
    /// there is no receiver or no base.
    fn super_target(&mut self, span: Span, what: &str) -> Option<(hir::Expr, Ty)> {
        let this = self.scopes.lookup(enrang_base::intern("this"));
        let class = self.at.class;
        let (Some(this), Some(class)) = (this, class) else {
            self.sema.emit(Diagnostic::new(
                Code::EN0219,
                format!("`{what}` outside a method"),
                span,
                "there is no object here",
            ));
            return None;
        };
        let tcx = &*self.sema.tcx;
        let Some(base) = tcx.adt(class).as_class().and_then(|c| c.base) else {
            // An `extends` that names no class was reported at the class.
            if self.sema.base_unknown(class) {
                return None;
            }
            let tcx = &*self.sema.tcx;
            let name = tcx.adt(class).name;
            self.sema.emit(Diagnostic::new(
                Code::EN0219,
                format!("`{what}` in `{name}`, which extends no class"),
                span,
                "there is no base class here",
            ));
            return None;
        };
        let ty = self.locals[this].ty;
        let this = self.mk_expr(ty, span, ExprKind::Local(this));
        Some((this, base))
    }

    /// `super(args)` in a constructor: the base's constructor (`Callee::SuperCtor`,
    /// `ctor: None` for a base chain with none), which 4A's `check_super_ctor`
    /// finds and checks.
    fn call_super_ctor(&mut self, span: Span, site: CallSite) -> hir::Expr {
        let in_ctor = match self.owner {
            hir::BodyOwner::Fn(def) => self.sema.tcx.def(def).kind == DefKind::Ctor,
            _ => false,
        };
        if !in_ctor {
            self.sema.emit(Diagnostic::new(
                Code::EN0219,
                "`super(...)` outside a constructor",
                span,
                "only a constructor calls its base's",
            ));
            return self.untyped_call(&site);
        }
        let Some((_, base)) = self.super_target(span, "super") else {
            return self.untyped_call(&site);
        };
        let TyKind::Adt(adt, base_args) = self.sema.tcx.kind(base) else {
            return self.untyped_call(&site);
        };
        self.check_super_ctor(adt, base_args, site)
    }

    /// `super.name(args)`: the base's method, called directly (`Callee::Super`),
    /// with `this` upcast to the base (C21).
    fn call_super_method(
        &mut self,
        span: Span,
        name: Ident,
        site: CallSite,
        ex: Expect,
    ) -> hir::Expr {
        let Some((this, base)) = self.super_target(span, "super") else {
            return self.untyped_call(&site);
        };
        let found = self.sema.tcx.member(base, name.name, self.at.module);
        let found = found.map(|f| self.check_visible(f, name));
        let methods: Vec<FoundMethod> = match found.map(|f| f.kind) {
            Some(MemberKind::Methods(methods)) => methods
                .into_iter()
                .filter(|m| self.receiver_kind(m.def) != Some(Receiver::Static))
                .collect(),
            _ => Vec::new(),
        };
        let Some(&method) = methods.first() else {
            let shown = self.sema.tcx.ty_string(base);
            self.sema.emit(Diagnostic::new(
                Code::EN0303,
                format!("`{shown}` has no method `{}`", name.name),
                name.span,
                "no such method in the base class",
            ));
            return self.untyped_call(&site);
        };
        // The receiver is a recorded reference, as every other method call's is,
        // so a base body that writes `this` kills the facts on it (S:742).
        self.record_ref(&this, RecordKind::Receiver);
        let mut receiver = this;
        receiver.adjust.push(Adjust::Upcast);
        if methods.len() > 1 || !site.type_args.is_empty() || self.is_generic(method.def) {
            let defs: Vec<DefId> = methods.iter().map(|m| m.def).collect();
            let site = CallSite {
                receiver: Some(receiver),
                methods: methods.clone(),
                at: Some(base),
                ..site
            };
            return self.dispatch(&defs, site, ex);
        }
        let owner_args = self.sema.tcx.list(method.args).to_vec();
        let (params, ret) = self.sig_at(method.def, &owner_args, None);
        let args = self.check_args(&params, &site, name.name.as_str(), Some(method.def));
        self.check_call_bounds(method.def, &owner_args, site.expr);
        let fn_args = self.fn_ref_args(method.def, &owner_args);
        self.mk_expr(
            ret,
            site.expr.span,
            ExprKind::Call {
                callee: Callee::Super(FnRef {
                    def: method.def,
                    args: fn_args,
                }),
                receiver: Some(Box::new(receiver)),
                args,
            },
        )
    }
}

/// The local a callee value is, narrowed or not.
fn local_of(e: &hir::Expr) -> Option<hir::LocalId> {
    match &e.kind {
        ExprKind::Local(local) => Some(*local),
        ExprKind::NarrowedPayload(inner, _, _) => local_of(inner),
        _ => None,
    }
}

/// The intrinsic kind `@intrinsic(name)` makes at a call whose first type argument
/// is `first`: the payload-free kinds, and the kinds whose payload is that type;
/// `None` for the kinds whose payload no declaration's name decides (plan doc gap
/// G13), which stay calls of their definition.
fn intrinsic_kind(name: IntrinsicName, first: Option<Ty>) -> Option<IntrinsicKind> {
    use IntrinsicName as N;
    Some(match name {
        N::VolatileRead => IntrinsicKind::VolatileRead,
        N::VolatileWrite => IntrinsicKind::VolatileWrite,
        N::ReadUnaligned => IntrinsicKind::ReadUnaligned,
        N::WriteUnaligned => IntrinsicKind::WriteUnaligned,
        N::MemCopy => IntrinsicKind::MemCopy,
        N::MemCopyOverlap => IntrinsicKind::MemCopyOverlap,
        N::MemSet => IntrinsicKind::MemSet,
        N::AtomicLoad => IntrinsicKind::AtomicLoad,
        N::AtomicStore => IntrinsicKind::AtomicStore,
        N::AtomicExchange => IntrinsicKind::AtomicExchange,
        N::AtomicFence => IntrinsicKind::AtomicFence,
        N::AtomicCompareExchange => IntrinsicKind::AtomicCompareExchange,
        N::AtomicFetchAdd => IntrinsicKind::AtomicFetchAdd,
        N::MulWideU32 => IntrinsicKind::MulWideU32,
        N::DivWideU32 => IntrinsicKind::DivWideU32,
        N::ToBitsCanon => IntrinsicKind::ToBitsCanon,
        N::FromBits => IntrinsicKind::FromBits,
        N::SizeOf => IntrinsicKind::SizeOf(first?),
        N::AlignOf => IntrinsicKind::AlignOf(first?),
        N::AllocArray => IntrinsicKind::AllocArray(first?),
        N::SliceFromRaw => IntrinsicKind::SliceFromRaw(first?),
        N::AtomicAlu | N::AtomicIncDecTest | N::AtomicBitTest | N::CpuHas | N::OffsetOf => {
            return None;
        }
    })
}
