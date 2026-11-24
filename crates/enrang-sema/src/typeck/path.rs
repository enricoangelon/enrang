//! Names in expressions (plan c.5, d.3, d.8; owner 3B): `Res` to HIR.
//!
//! A local is `Local`; a constant or `unsafe let` is `Static`; a function name is
//! `Const(FnAddr)` of its `fn` type, which C11 converts at an `fn` site (4C), and an
//! overload set picks the overload whose `fn` type is expected, EN0410 when none
//! is (S:734); a top-level variable a local function sees is its hidden argument,
//! a `LocalKind::Hidden` local of the type the statements gave the variable (N13),
//! and `args` in the statements a `LocalKind::TopVar` local of type `string[]`.
//! `this` where no receiver exists is EN0219, and so is `super` anywhere but
//! `super(...)` and `super.m()` (plan choice). A type, namespace or form in value
//! position is EN0301 (plan choice). A name in no scope is EN0301 with "did you
//! mean" over the locals in scope and the names `suggest.rs` lists (G06), or its
//! SPEC 16 code; a local function with hidden arguments named outside the
//! statements and other local functions is EN0313 (`toplevel::check_use`).
//!
//! A path through a type, a namespace or a form (`Color.Red`, `i64.MAX`,
//! `Stack<i64>.empty`, `E<i64>.V`, `u.helper`, `d.serial.Port.open`) is found by
//! [`FnCtxt::path_base`] and typed by [`FnCtxt::static_member`]: an enum case is a
//! `VariantLit` (its arguments from the expected type, else inferred, when the path
//! writes none), a primitive constant (`MIN`, `MAX` of the integers, from the target
//! for `isize` and `usize`; `PI`, `E`, `INFINITY`, `NAN` of the floats) a `Const`
//! (built into sema, plan doc gap G7), a `static` method an `fn` value; anything
//! else is EN0303. A namespace's member is its `public` item: a `private` one is
//! EN0311, a missing one EN0301 with "did you mean" over its `public` names (plan
//! d.3).

use enrang_base::{Span, Symbol};
use enrang_diag::{Code, Diagnostic, Edit, Help, did_you_mean};
use enrang_hir::{
    self as hir, AdtId, ConstValue, DefId, DefKind, ExprKind, FloatTy, FnPtrSig, FnRef, FormName,
    FoundMethod, LocalId, LocalKind, MemberKind, PrimTy, Receiver, Res, TopVar, Ty, TyKind, Vis,
};
use enrang_syntax::ast::{self, Ident};

use crate::load::graph;
use crate::resolve::suggest::{NameKind, unresolved_with};
use crate::resolve::{scope, toplevel};
use crate::typeck::infer::VarKind;
use crate::typeck::{Expect, FnCtxt};

/// What the base of a member path names, when it is no value.
#[derive(Copy, Clone, Debug)]
pub(crate) enum PathBase {
    /// A type: written, or an ADT whose arguments the path leaves to inference.
    Type(TypeBase),
    /// A namespace: a user folder, `import * as`, or a child module, by load index.
    Namespace(usize),
    /// A compiler form (`console`).
    Form(FormName),
}

/// A type named before `.`.
#[derive(Copy, Clone, Debug)]
pub(crate) struct TypeBase {
    pub ty: Ty,
    /// The ADT, when the path wrote no arguments for its parameters: `ty` then holds
    /// its identity arguments, which the use infers.
    pub infer: Option<AdtId>,
}

impl FnCtxt<'_, '_> {
    /// `Ident`, `This`, `TypeMember`, or `Super` out of a call.
    pub(crate) fn check_path(&mut self, e: &ast::Expr, ex: Expect) -> hir::Expr {
        match &e.kind {
            ast::ExprKind::Ident(name) => self.check_name(*name, e.span, ex),
            ast::ExprKind::This => {
                let this = self.check_this(e.span);
                self.this_moved(this, ex)
            }
            ast::ExprKind::Super => {
                self.super_outside_call(e.span);
                self.error_expr(e.span)
            }
            ast::ExprKind::TypeMember { ty: written, name } => {
                let ty = self.lower_body_type(written, false);
                let path = PathBase::Type(TypeBase { ty, infer: None });
                self.static_member_at(path, e.span, *name, e.span, ex)
            }
            _ => self.error_expr(e.span),
        }
    }

    /// A type written in a body outside an annotation, lowered and position-checked
    /// (a static path's type, or with `form` a size form's): `Error` once rejected,
    /// so nothing reports the same mistake again.
    pub(crate) fn lower_body_type(&mut self, written: &ast::TypeExpr, form: bool) -> Ty {
        let ty = self.lower_ty(written);
        if !self.sema.tcx.module(self.at.module).library
            && crate::passes::positions::rejects_body_type(self.sema, ty, written, form)
        {
            return self.error_ty();
        }
        ty
    }

    /// `this`: the receiver local; EN0219 where there is none.
    fn check_this(&mut self, span: Span) -> hir::Expr {
        if let Some(local) = self.scopes.lookup(enrang_base::intern("this")) {
            let ty = self.locals[local].ty;
            return self.mk_expr(ty, span, ExprKind::Local(local));
        }
        let fn_owner = match self.owner {
            hir::BodyOwner::Fn(def) => Some(def),
            _ => None,
        };
        // A class-level body that is no function is a field initialiser, where
        // `this` is EN0610 at M3 (plan e, EN0219's row).
        if self.at.class.is_some() && fn_owner.is_none() {
            self.this_spans.push(span);
            return self.error_expr(span);
        }
        let is_static = fn_owner.is_some_and(|def| {
            self.sema
                .tcx
                .sig_opt(def)
                .is_some_and(|s| s.receiver == Some(Receiver::Static))
        });
        let label = match is_static {
            true => "a `static` method has no `this`",
            false => "there is no object here",
        };
        self.sema.emit(Diagnostic::new(
            Code::EN0219,
            "`this` outside a method",
            span,
            label,
        ));
        self.error_expr(span)
    }

    /// N7 (S:588): at an expected type `C`, a non-Copy `this` of type `&C` is a
    /// move of the object, `*this`; whether the method may move it (a `move`
    /// method, else EN0603) is phase 3's.
    fn this_moved(&mut self, this: hir::Expr, ex: Expect) -> hir::Expr {
        let Some(want) = ex.ty() else {
            return this;
        };
        let want = self.shallow(want);
        let tcx = &*self.sema.tcx;
        let TyKind::Ref(object) = tcx.kind(self.shallow(this.ty)) else {
            return this;
        };
        let object = self.shallow(object);
        if object != want
            || !matches!(tcx.kind(object), TyKind::Adt(..))
            || tcx.is_copy(object, &self.env)
        {
            return this;
        }
        let span = this.span;
        self.mk_expr(object, span, ExprKind::Deref(Box::new(this)))
    }

    /// A name read as a value.
    fn check_name(&mut self, name: Symbol, span: Span, ex: Expect) -> hir::Expr {
        if let Some(local) = self.scopes.lookup(name) {
            let ty = self.locals[local].ty;
            return self.mk_expr(ty, span, ExprKind::Local(local));
        }
        let ident = Ident { name, span };
        match scope::lookup_value(self.sema, self.at, ident) {
            Res::Def(def) => self.def_value(def, ident, ex),
            Res::Fns(defs) => {
                for &def in &defs {
                    toplevel::check_use(self.sema, self.at, def, span);
                }
                self.fns_value(&defs, &[], ident, ex)
            }
            Res::TopVar(var) => self.top_var_expr(var, span),
            Res::PrimType(_) | Res::TyParam(_) | Res::SelfTy => {
                self.not_a_value(ident, "a type");
                self.error_expr(span)
            }
            Res::Namespace(_) => {
                self.not_a_value(ident, "a namespace");
                self.error_expr(span)
            }
            Res::Form(_) => {
                self.not_a_value(ident, "a compiler form");
                self.error_expr(span)
            }
            Res::Local(local) => {
                let ty = self.locals[local].ty;
                self.mk_expr(ty, span, ExprKind::Local(local))
            }
            Res::Err => {
                self.unresolved_value(ident);
                self.error_expr(span)
            }
        }
    }

    /// EN0301 (or a SPEC 16 code) for a name in no scope, with "did you mean" over
    /// the locals in scope first (G06).
    pub(crate) fn unresolved_value(&mut self, ident: Ident) {
        let locals: Vec<(Symbol, Span)> = self
            .scopes
            .visible()
            .into_iter()
            .map(|(name, local)| (name, self.locals[local].span))
            .filter(|(_, span)| !span.is_dummy())
            .collect();
        unresolved_with(self.sema, self.at, ident, NameKind::Value, &locals);
    }

    /// EN0301 for a type, namespace or form where a value is read (plan choice).
    pub(crate) fn not_a_value(&mut self, ident: Ident, what: &str) {
        self.sema.emit(Diagnostic::new(
            Code::EN0301,
            format!("`{}` is {what}, not a value", ident.name),
            ident.span,
            "used as a value here",
        ));
    }

    /// The value a definition names: a constant or `unsafe let` is `Static`, a
    /// function an `fn` value; a type is EN0301.
    fn def_value(&mut self, def: DefId, ident: Ident, ex: Expect) -> hir::Expr {
        let error = self.error_ty();
        match self.sema.tcx.def(def).kind {
            DefKind::Const | DefKind::Static => {
                let ty = crate::typeck::const_ty(self.sema, def).unwrap_or(error);
                self.mk_expr(ty, ident.span, ExprKind::Static(def))
            }
            DefKind::Fn | DefKind::LocalFn | DefKind::DeclareFn | DefKind::Method => {
                self.fns_value(&[def], &[], ident, ex)
            }
            DefKind::Adt(_) | DefKind::TypeAlias | DefKind::StrUnion(_) => {
                self.not_a_value(ident, "a type");
                self.error_expr(ident.span)
            }
            _ => self.error_expr(ident.span),
        }
    }

    /// A function named as a value: `Const(FnAddr)` of its `fn` type (C11 converts it
    /// at its site, 4C). Of an overload set, the overload whose `fn` type the context
    /// expects; with none expected, EN0410 (S:734). `owner_args` are the arguments of
    /// a static method's class.
    pub(crate) fn fns_value(
        &mut self,
        defs: &[DefId],
        owner_args: &[Ty],
        ident: Ident,
        ex: Expect,
    ) -> hir::Expr {
        let chosen = match defs {
            [] => return self.error_expr(ident.span),
            [one] => *one,
            many => {
                let expected = ex.ty().map(|t| match self.sema.tcx.kind(t) {
                    TyKind::Nullable(inner) => inner,
                    _ => t,
                });
                let fits: Vec<DefId> = many
                    .iter()
                    .copied()
                    .filter(|&d| {
                        expected.is_some_and(|t| {
                            let mine = self.fn_ptr_ty(d, owner_args);
                            self.same_fn_shape(mine, t)
                        })
                    })
                    .collect();
                match fits.as_slice() {
                    [one] => *one,
                    // An expected `fn` type that no overload fits is a mismatch, not
                    // a choice left open (S:829).
                    [] if expected.is_some_and(|t| {
                        matches!(self.sema.tcx.kind(self.shallow(t)), TyKind::FnPtr(..))
                    }) =>
                    {
                        let want = self.ty_str(expected.expect("an expected type"));
                        let mut diag = Diagnostic::new(
                            Code::EN0401,
                            format!(
                                "mismatched types: no overload of `{}` is `{want}`",
                                ident.name
                            ),
                            ident.span,
                            format!("`{}` has {} overloads", ident.name, many.len()),
                        );
                        for &d in many.iter() {
                            let ty = self.fn_ptr_ty(d, owner_args);
                            let names: Vec<Symbol> = self
                                .sema
                                .tcx
                                .sig_opt(d)
                                .map(|sig| sig.params.iter().map(|p| p.name).collect())
                                .unwrap_or_default();
                            let shown = self.sema.tcx.fn_ty_string(ty, Some(&names));
                            diag = diag.note(format!("one overload is `{shown}`"));
                        }
                        self.sema.emit(diag);
                        return self.error_expr(ident.span);
                    }
                    _ => {
                        let first = self.fn_ptr_ty(many[0], owner_args);
                        let names: Vec<Symbol> = self
                            .sema
                            .tcx
                            .sig_opt(many[0])
                            .map(|sig| sig.params.iter().map(|p| p.name).collect())
                            .unwrap_or_default();
                        let written = self.sema.tcx.fn_ty_string(first, Some(&names));
                        self.sema.emit(
                            Diagnostic::new(
                                Code::EN0410,
                                format!("cannot infer which overload of `{}` is meant", ident.name),
                                ident.span,
                                format!("`{}` has {} overloads", ident.name, many.len()),
                            )
                            .with_help(Help::text(format!(
                                "give it an expected type: `const {}: {written} = {};`",
                                self.init_name
                                    .filter(|n| *n != ident.name)
                                    .map_or_else(|| "f".to_owned(), |n| n.to_string()),
                                ident.name
                            ))),
                        );
                        return self.error_expr(ident.span);
                    }
                }
            }
        };
        let ty = self.fn_ptr_ty(chosen, owner_args);
        let args = self.fn_ref_args(chosen, owner_args);
        self.mk_expr(
            ty,
            ident.span,
            ExprKind::Const(ConstValue::FnAddr(FnRef { def: chosen, args })),
        )
    }

    /// The `fn` type of function `def`, its owner's parameters replaced by
    /// `owner_args`.
    pub(crate) fn fn_ptr_ty(&self, def: DefId, owner_args: &[Ty]) -> Ty {
        let tcx = &*self.sema.tcx;
        let Some(sig) = tcx.sig_opt(def) else {
            return tcx.common().error;
        };
        let owner = match tcx.generics(sig.generics).parent {
            Some(parent) => tcx.all_params(parent),
            None => Vec::new(),
        };
        let n = owner.len().min(owner_args.len());
        let subst = |t: Ty| tcx.subst(t, &owner[..n], &owner_args[..n]);
        let ptr = FnPtrSig {
            unsafety: sig.unsafety,
            params: sig.params.iter().map(|p| (subst(p.ty), p.mark)).collect(),
            ret: subst(sig.ret),
            ret_readonly: sig.ret_readonly,
        };
        tcx.mk_fn_ptr(sig.abi, ptr)
    }

    /// The type arguments of a reference to function `def`: its owner's
    /// `owner_args`, then its own parameters as they stand.
    pub(crate) fn fn_ref_args(&self, def: DefId, owner_args: &[Ty]) -> hir::TyList {
        let tcx = &*self.sema.tcx;
        let Some(sig) = tcx.sig_opt(def) else {
            return tcx.empty_list();
        };
        let mut args: Vec<Ty> = owner_args.to_vec();
        args.extend(
            tcx.generics(sig.generics)
                .params
                .iter()
                .map(|&p| tcx.mk_param(p)),
        );
        tcx.intern_list(&args)
    }

    /// Whether `fn` type `mine` fits the expected `fn` or closure type `t`: the same
    /// parameter and result types, rows ignored.
    fn same_fn_shape(&self, mine: Ty, t: Ty) -> bool {
        let tcx = &*self.sema.tcx;
        let (TyKind::FnPtr(_, a), TyKind::FnPtr(_, b) | TyKind::Closure(b)) =
            (tcx.kind(mine), tcx.kind(t))
        else {
            return false;
        };
        let (a, b) = (tcx.fn_sig(a), tcx.fn_sig(b));
        a.params.len() == b.params.len()
            && a.params
                .iter()
                .zip(b.params.iter())
                .all(|(x, y)| tcx.same_ignoring_rows(x.0, y.0))
            && tcx.same_ignoring_rows(a.ret, b.ret)
    }

    /// A top-level variable seen below the locals: `args` in the statements, or a
    /// local function's hidden argument (N13), one local per variable and body.
    fn top_var_expr(&mut self, var: TopVar, span: Span) -> hir::Expr {
        let kind = match self.at.statements {
            true => LocalKind::TopVar(var),
            false => LocalKind::Hidden(var),
        };
        let local = self.top_var_local(var, kind);
        let ty = self.locals[local].ty;
        self.mk_expr(ty, span, ExprKind::Local(local))
    }

    /// The local of top-level variable `var` in this body, declared on first use
    /// outside every block scope, with the type and mutability the statements gave
    /// it; `args` is `string[]`.
    pub(crate) fn top_var_local(&mut self, var: TopVar, kind: LocalKind) -> LocalId {
        if let Some((local, _)) = self
            .locals
            .iter_enumerated()
            .find(|(_, decl)| decl.kind == kind)
        {
            return local;
        }
        let def = self.sema.res.toplevel.vars.get(var.0 as usize).cloned();
        let name = def.as_ref().map(|d| d.name);
        let decl_span = def.as_ref().map_or(Span::DUMMY, |d| d.span);
        let statements = self.sema.statements.clone();
        let from_statements = statements.as_ref().and_then(|body| {
            body.locals
                .iter()
                .find(|decl| {
                    decl.kind == LocalKind::TopVar(var)
                        || (!decl_span.is_dummy() && decl.span == decl_span && decl.name == name)
                })
                .map(|decl| (decl.ty, decl.mutable))
        });
        let (ty, mutable) = match from_statements {
            Some(found) => found,
            None if var.0 == 0 => {
                let tcx = &*self.sema.tcx;
                (tcx.mk_array(tcx.common().str), false)
            }
            None => (self.error_ty(), false),
        };
        self.locals.push(hir::LocalDecl {
            name,
            ty,
            mutable,
            kind,
            span: decl_span,
        })
    }

    // ---------------------------------------------------------------------------
    // Paths through types, namespaces and forms.

    /// What `e`, the base of a member path, names when it is no value: a type, a
    /// namespace or a form. `None` for a value, a local, or a name in no scope.
    /// Reports nothing but what lowering a named type reports.
    pub(crate) fn path_base(&mut self, e: &ast::Expr) -> Option<PathBase> {
        match &e.kind {
            ast::ExprKind::Ident(name) => {
                if self.scopes.lookup(*name).is_some() {
                    return None;
                }
                let ident = Ident {
                    name: *name,
                    span: e.span,
                };
                match scope::lookup_value(self.sema, self.at, ident) {
                    Res::Def(def) => self.type_base(def, &[ident], e),
                    Res::PrimType(prim) => Some(PathBase::Type(TypeBase {
                        ty: self.prim_ty(prim),
                        infer: None,
                    })),
                    Res::Namespace(m) => Some(PathBase::Namespace(self.sema.res.index(m))),
                    Res::Form(form) => Some(PathBase::Form(form)),
                    _ => None,
                }
            }
            ast::ExprKind::Member {
                base,
                name,
                optional: false,
            } => {
                let PathBase::Namespace(index) = self.path_base(base)? else {
                    return None;
                };
                match scope::public_member(self.sema, index, name.name)? {
                    Res::Def(def) => {
                        let path = path_idents(e)?;
                        self.type_base(def, &path, e)
                    }
                    Res::Namespace(m) => Some(PathBase::Namespace(self.sema.res.index(m))),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The type definition `def`, written `path` at `e`, as a path base: a generic
    /// ADT with no arguments written is left to inference; anything else is lowered
    /// as the type `path` names (lang classes to their kinds, aliases expanded).
    fn type_base(&mut self, def: DefId, path: &[Ident], e: &ast::Expr) -> Option<PathBase> {
        match self.sema.tcx.def(def).kind {
            DefKind::Adt(adt) => {
                let generics = self.sema.tcx.adt(adt).generics;
                if !self.sema.tcx.generics(generics).params.is_empty() {
                    let ty = self.sema.tcx.adt_identity(adt);
                    return Some(PathBase::Type(TypeBase {
                        ty,
                        infer: Some(adt),
                    }));
                }
            }
            DefKind::TypeAlias | DefKind::StrUnion(_) => {}
            _ => return None,
        }
        let written = ast::TypeExpr {
            id: e.id,
            span: e.span,
            kind: ast::TypeExprKind::Named {
                path: path.to_vec(),
                args: Vec::new(),
            },
        };
        let ty = self.lower_ty(&written);
        Some(PathBase::Type(TypeBase { ty, infer: None }))
    }

    /// The type a primitive name spells.
    fn prim_ty(&self, prim: PrimTy) -> Ty {
        let common = self.sema.tcx.common();
        match prim {
            PrimTy::Bool => common.bool,
            PrimTy::Int(int) => common.int(int),
            PrimTy::Float(float) => common.float(float),
            PrimTy::Void => common.void,
            PrimTy::Never => common.never,
            PrimTy::Str => common.str,
        }
    }

    /// `base.name` read as a value, `base` a type, namespace or form.
    pub(crate) fn static_member(
        &mut self,
        path: PathBase,
        base: &ast::Expr,
        name: Ident,
        span: Span,
        ex: Expect,
    ) -> hir::Expr {
        self.static_member_at(path, base.span, name, span, ex)
    }

    /// [`Self::static_member`] with the base's span.
    fn static_member_at(
        &mut self,
        path: PathBase,
        base: Span,
        name: Ident,
        span: Span,
        ex: Expect,
    ) -> hir::Expr {
        match path {
            PathBase::Form(_) => {
                let ident = Ident {
                    name: enrang_base::intern(&format!("{}.{}", self.source(base), name.name)),
                    span,
                };
                self.not_a_value(ident, "a compiler form");
                self.error_expr(span)
            }
            PathBase::Namespace(index) => self.ns_value(index, base, name, span, ex),
            PathBase::Type(tb) => self.type_value(tb, base, name, span, ex),
        }
    }

    /// A namespace's member read as a value.
    fn ns_value(
        &mut self,
        index: usize,
        base: Span,
        name: Ident,
        span: Span,
        ex: Expect,
    ) -> hir::Expr {
        let ident = Ident {
            name: name.name,
            span: name.span,
        };
        match scope::public_member(self.sema, index, name.name) {
            Some(Res::Def(def)) => {
                let value = self.def_value(def, ident, ex);
                self.respan(value, span)
            }
            Some(Res::Fns(defs)) => {
                let value = self.fns_value(&defs, &[], ident, ex);
                self.respan(value, span)
            }
            Some(Res::Namespace(_)) => {
                self.not_a_value(ident, "a namespace");
                self.error_expr(span)
            }
            Some(_) => self.error_expr(span),
            None => {
                self.ns_missing(index, base, name);
                self.error_expr(span)
            }
        }
    }

    /// `e` with its span widened to `span`, the whole path.
    fn respan(&mut self, mut e: hir::Expr, span: Span) -> hir::Expr {
        e.span = span;
        e
    }

    /// `name` is no `public` member of the namespace at load index `index`, written
    /// at `base`: EN0311 for a `private` item, as importing it would be (S:801);
    /// otherwise EN0301 with "did you mean" over the namespace's `public` names
    /// (plan d.3, choice of wording, as `suggest::unresolved_member` words a type's).
    pub(crate) fn ns_missing(&mut self, index: usize, base: Span, name: Ident) {
        let module = &self.sema.program.modules[index];
        let declared = self.sema.res.scopes[index]
            .names
            .get(&name.name)
            .is_some_and(|defs| !defs.is_empty());
        if !module.folder && declared {
            let shown = graph::file_name(self.sema, index);
            self.sema.err(
                Code::EN0311,
                format!("`{}` is private to `{shown}`", name.name),
                name.span,
                "a private item",
            );
            return;
        }
        let prefix = self.source(base);
        let mut diag = Diagnostic::new(
            Code::EN0301,
            format!("cannot find `{}` in `{prefix}`", name.name),
            name.span,
            "not found",
        );
        let names = self.ns_names(index);
        let names: Vec<&str> = names.iter().map(|n| n.as_str()).collect();
        if let Some(found) = did_you_mean(name.name.as_str(), &names) {
            diag = diag.with_help(Help::machine(
                format!("did you mean `{found}`?"),
                vec![Edit::replace(name.span, found)],
            ));
        }
        self.sema.emit(diag);
    }

    /// What the namespace at load index `index` shows: its `public` items, what it
    /// re-exports and its child modules.
    fn ns_names(&self, index: usize) -> Vec<Symbol> {
        let sema = &*self.sema;
        let mut out: Vec<Symbol> = Vec::new();
        for (name, defs) in &sema.res.scopes[index].names {
            if defs.iter().any(|&d| {
                sema.tcx.def(d).vis == Vis::Public && sema.tcx.def(d).kind != DefKind::LocalFn
            }) {
                out.push(*name);
            }
        }
        for name in sema.res.imports[index].keys() {
            if scope::reexports(sema, index, *name) {
                out.push(*name);
            }
        }
        let parent = &sema.program.modules[index];
        let prefix = format!("{}/", parent.path);
        for m in &sema.program.modules {
            if m.library == parent.library
                && let Some(rest) = m.path.as_str().strip_prefix(&prefix)
                && !rest.contains('/')
            {
                out.push(enrang_base::intern(rest));
            }
        }
        out.sort_by_key(|n| n.as_str());
        out.dedup();
        out
    }

    /// A type's member read as a value: a case, a primitive constant or a `static`
    /// method; anything else EN0303.
    fn type_value(
        &mut self,
        tb: TypeBase,
        base: Span,
        name: Ident,
        span: Span,
        ex: Expect,
    ) -> hir::Expr {
        let ty = tb.ty;
        if self.sema.tcx.references_error(ty) && tb.infer.is_none() {
            return self.error_expr(span);
        }
        if let Some(value) = self.case_value(tb, base, name, span, ex) {
            return value;
        }
        if let Some(value) = self.prim_const(ty, name.name) {
            return self.mk_expr(ty, span, ExprKind::Const(value));
        }
        let Some(statics) = self.static_methods(ty, name, base) else {
            return self.error_expr(span);
        };
        let owner_args = match tb.infer {
            Some(_) => self.owner_args_of(tb, ex),
            None => self.sema.tcx.list(statics[0].args).to_vec(),
        };
        let defs: Vec<DefId> = statics.iter().map(|m| m.def).collect();
        let value = self.fns_value(&defs, &owner_args, name, ex);
        self.respan(value, span)
    }

    /// The `static` methods named `name` of type `ty` written at `base`; EN0303
    /// when it has none (a missing member, an instance member, a field).
    pub(crate) fn static_methods(
        &mut self,
        ty: Ty,
        name: Ident,
        base: Span,
    ) -> Option<Vec<FoundMethod>> {
        let found = self.sema.tcx.member(ty, name.name, self.at.module);
        let statics: Vec<FoundMethod> = match &found {
            Some(found) => match &found.kind {
                MemberKind::Methods(methods) => methods
                    .iter()
                    .copied()
                    .filter(|m| {
                        self.sema
                            .tcx
                            .sig_opt(m.def)
                            .is_some_and(|s| s.receiver == Some(Receiver::Static))
                    })
                    .collect(),
                MemberKind::Field { .. } => Vec::new(),
            },
            None => Vec::new(),
        };
        // Static or not is decided first, so a misuse gets one diagnostic: an
        // instance member named through the type is EN0303 whatever its
        // visibility, and only a `static` one found is checked for it (EN0308).
        if let (Some(found), Some(&first)) = (&found, statics.first()) {
            let only = hir::MemberRef {
                kind: MemberKind::Methods(statics.clone()),
                via_slice: found.via_slice,
                owner: first.owner,
                args: first.args,
            };
            return match self.check_visible(only, name).kind {
                MemberKind::Methods(seen) => Some(seen),
                MemberKind::Field { .. } => Some(statics),
            };
        }
        let shown = self.source(base);
        let tcx = &*self.sema.tcx;
        let mut diag = match found {
            Some(_) => Diagnostic::new(
                Code::EN0303,
                format!("`{shown}` has no static member `{}`", name.name),
                name.span,
                "a member of each value, not of the type",
            ),
            None => Diagnostic::new(
                Code::EN0303,
                format!("`{shown}` has no member `{}`", name.name),
                name.span,
                "no such member",
            ),
        };
        let mut names: Vec<Symbol> = Vec::new();
        if let TyKind::Adt(adt, _) = tcx.kind(ty)
            && let Some(e) = tcx.adt(adt).as_enum()
        {
            names.extend(e.variants.iter().map(|v| v.name));
        }
        names.extend(
            self.prim_const_names(ty)
                .iter()
                .map(|n| enrang_base::intern(n)),
        );
        names.extend(self.member_names(ty).into_iter().filter(|&n| {
            match self.sema.tcx.member(ty, n, self.at.module).map(|f| f.kind) {
                Some(MemberKind::Methods(ms)) => ms.iter().any(|m| {
                    self.sema
                        .tcx
                        .sig_opt(m.def)
                        .is_some_and(|s| s.receiver == Some(Receiver::Static))
                }),
                _ => false,
            }
        }));
        let names: Vec<&str> = names.iter().map(|n| n.as_str()).collect();
        if let Some(found) = did_you_mean(name.name.as_str(), &names) {
            diag = diag.with_help(Help::machine(
                format!("did you mean `{found}`?"),
                vec![Edit::replace(name.span, found)],
            ));
        }
        self.sema.emit(diag);
        None
    }

    /// The arguments of a type base's ADT: written, else those the expected type
    /// gives the same ADT, else fresh variables.
    pub(crate) fn owner_args_of(&mut self, tb: TypeBase, ex: Expect) -> Vec<Ty> {
        let tcx = &*self.sema.tcx;
        let Some(adt) = tb.infer else {
            return match tcx.kind(tb.ty) {
                TyKind::Adt(_, args) => tcx.list(args).to_vec(),
                _ => tcx
                    .lang_class_of(tb.ty)
                    .map(|(_, args)| tcx.list(args).to_vec())
                    .unwrap_or_default(),
            };
        };
        if let Some(t) = ex.ty() {
            let t = match tcx.kind(t) {
                TyKind::Nullable(inner) => inner,
                _ => t,
            };
            if let TyKind::Adt(a, args) = tcx.kind(t)
                && a == adt
            {
                return tcx.list(args).to_vec();
            }
        }
        let count = tcx.generics(tcx.adt(adt).generics).params.len();
        (0..count)
            .map(|_| {
                let var = self.infer.fresh(VarKind::Any);
                self.sema.tcx.intern_ty(TyKind::Infer(var))
            })
            .collect()
    }

    /// `E.V` read as a value, when `tb` is an enum with a case `name`: a
    /// `VariantLit`; a case with a field that has no default is EN0433, as
    /// `new Team()` is (S:582).
    fn case_value(
        &mut self,
        tb: TypeBase,
        base: Span,
        name: Ident,
        span: Span,
        ex: Expect,
    ) -> Option<hir::Expr> {
        let tcx = &*self.sema.tcx;
        let adt = match (tb.infer, tcx.kind(tb.ty)) {
            (Some(adt), _) | (None, TyKind::Adt(adt, _)) => adt,
            _ => return None,
        };
        let e = tcx.adt(adt).as_enum()?;
        let (variant, def) = e.variant_named(name.name)?;
        let unset = def.fields.iter().find(|f| !f.has_default).map(|f| f.name);
        if let Some(field) = unset {
            let written = format!("{}.{}", self.source(base), name.name);
            self.sema.emit(
                Diagnostic::new(
                    Code::EN0433,
                    format!("`{written}` leaves `{field}` unset"),
                    span,
                    format!("`{field}` has no default"),
                )
                .with_help(Help::text(format!("use `{written} {{ {field}: ... }}`"))),
            );
            return Some(self.error_expr(span));
        }
        let args = self.owner_args_of(tb, ex);
        let tcx = &*self.sema.tcx;
        let ty = tcx.mk_adt(adt, &args);
        let args = tcx.intern_list(&args);
        Some(self.mk_expr(
            ty,
            span,
            ExprKind::VariantLit {
                adt,
                variant,
                args,
                fields: Vec::new(),
                eval: Vec::new(),
            },
        ))
    }

    /// The names of the built-in constants of a primitive type (plan doc gap G7).
    fn prim_const_names(&self, ty: Ty) -> &'static [&'static str] {
        match self.sema.tcx.kind(ty) {
            TyKind::Int(_) => &["MIN", "MAX"],
            TyKind::Float(_) => &["PI", "E", "INFINITY", "NAN"],
            _ => &[],
        }
    }

    /// A built-in constant of a primitive type (plan doc gap G7): `MIN` and `MAX` of
    /// each integer, `isize` and `usize` at the target's pointer width; `PI`, `E`,
    /// `INFINITY` and `NAN` of each float, at its width.
    pub(crate) fn prim_const(&self, ty: Ty, name: Symbol) -> Option<ConstValue> {
        let tcx = &*self.sema.tcx;
        match tcx.kind(ty) {
            TyKind::Int(int) => {
                let width = int.bits(u32::from(tcx.target().layout.ptr_bytes) * 8);
                let all = match width {
                    128 => u128::MAX,
                    w => (1u128 << w) - 1,
                };
                let (min, max) = match int.is_signed() {
                    true => (1u128 << (width - 1), (1u128 << (width - 1)) - 1),
                    false => (0, all),
                };
                match name.as_str() {
                    "MIN" => Some(ConstValue::Int(min, ty)),
                    "MAX" => Some(ConstValue::Int(max, ty)),
                    _ => None,
                }
            }
            TyKind::Float(float) => {
                let value = match name.as_str() {
                    "PI" => std::f64::consts::PI,
                    "E" => std::f64::consts::E,
                    "INFINITY" => f64::INFINITY,
                    "NAN" => f64::NAN,
                    _ => return None,
                };
                let bits = match float {
                    FloatTy::F64 => value.to_bits(),
                    FloatTy::F32 => u64::from((value as f32).to_bits()),
                };
                Some(ConstValue::Float(bits, ty))
            }
            _ => None,
        }
    }
}

/// The identifiers of a path of `Ident` and non-optional `Member` steps.
fn path_idents(e: &ast::Expr) -> Option<Vec<Ident>> {
    match &e.kind {
        ast::ExprKind::Ident(name) => Some(vec![Ident {
            name: *name,
            span: e.span,
        }]),
        ast::ExprKind::Member {
            base,
            name,
            optional: false,
        } => {
            let mut path = path_idents(base)?;
            path.push(*name);
            Some(path)
        }
        _ => None,
    }
}
