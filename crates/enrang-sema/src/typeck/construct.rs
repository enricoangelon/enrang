//! Construction (plan c.5, d.16; SPEC 4.3 S:579-600; owner 4A).
//!
//! `new C(args)` runs a constructor: the nearest class of `C`'s chain that
//! declares one, since a subclass with none reuses its base's (S:587), its
//! overloads ranked as any call's and its arguments typed as a generic call's, `C`'s
//! own type arguments inferred from them and from the expected type when none are
//! written (`new Box(new Dog("Fido"))`). With no constructor in the chain, `new C()`
//! is the named form with every field at its default, EN0433 `` `new Team()` leaves
//! `owner` unset `` for a field with none, and arguments are EN0449. `new` of what
//! is no class is EN0221, of an abstract class EN0445.
//!
//! The named form, `new C { ... }` or an object literal where a class is expected,
//! is EN0447 for a chain with a constructor; it lists base and own fields together
//! (S:587), each visible where the literal is written (EN0308), unknown ones
//! EN0434, and the fields it leaves out take their defaults, written or their
//! type's (numbers `0`, `bool` `false`, `string` `""`, arrays `[]`, `T | null`
//! `null`, raw pointers address 0; plan choice: a fixed array, tuple or object type
//! when its parts have one), a field with neither being EN0433 `` missing field
//! `owner` ``, every such field in one diagnostic. A case literal `Shape.Circle {
//! radius: 2.5 }` does the same over its case's fields, the left-out ones filled
//! with their type's default value; `Ok { value: v }` and `Err { error: e }` name
//! `Result`'s cases bare. An object literal at an object type is that type's value:
//! a field the type lacks is EN0434 (`` `greet` doesn't use the field `age`, so it
//! would be thrown away `` for an argument), an optional field left out is `null`
//! (S:600). With no expected class or object type, an object literal has an
//! anonymous object type of its fields' own types (S:600). `super(args)` finds its
//! constructor the same way, EN0449 when the base chain has none.

use enrang_base::{Span, Symbol};
use enrang_diag::{Code, Diagnostic, Help, did_you_mean};
use enrang_hir::{
    self as hir, AdtId, Callee, ClassModifier, ConstValue, DefId, DefKind, ExprKind, FieldIdx,
    LangItem, MemberKind, MemberRef, Res, Shape, Ty, TyKind,
};
use enrang_syntax::ast::{self, Ident};

use crate::resolve::scope;
use crate::typeck::call::CallSite;
use crate::typeck::generic::{Target, args_span};
use crate::typeck::infer::VarKind;
use crate::typeck::{Expect, FnCtxt, Site};

impl FnCtxt<'_, '_> {
    /// `New`, `ObjectLit` or `CaseLit`.
    pub(crate) fn check_new(&mut self, e: &ast::Expr, ex: Expect) -> hir::Expr {
        let value = match &e.kind {
            ast::ExprKind::New { ty, init } => self.new_expr(e, ty, init, ex),
            ast::ExprKind::ObjectLit(fields) => self.object_lit(e, fields, ex),
            ast::ExprKind::CaseLit { path, args, fields } => {
                self.case_lit(e, path, args, fields, ex)
            }
            _ => self.error_expr(e.span),
        };
        // A named form's field values move into the new value (4B).
        self.moved_into(&value);
        value
    }

    // ---------------------------------------------------------------------------
    // `new`.

    /// `new C(args)` or `new C { ... }`.
    fn new_expr(
        &mut self,
        e: &ast::Expr,
        ty: &ast::TypeExpr,
        init: &ast::NewInit,
        ex: Expect,
    ) -> hir::Expr {
        let Some((adt, given)) = self.new_target(ty) else {
            self.untyped_init(init);
            return self.error_expr(e.span);
        };
        let name = self.sema.tcx.adt(adt).name;
        // An abstract class is reported alone: no field or argument of an object
        // that can never exist is checked against it, only the values typed.
        if self.is_abstract(adt) {
            self.sema.emit(Diagnostic::new(
                Code::EN0445,
                format!("`{name}` is abstract, so it can't be created"),
                ty.span,
                "an abstract class",
            ));
            self.untyped_init(init);
            return self.error_expr(e.span);
        }
        let class_args = match given {
            Some(args) => args,
            None => self.instance_vars(adt, &format!("new {name}"), e.span),
        };
        match init {
            ast::NewInit::Args(args) => self.new_with_args(e, ty.span, adt, &class_args, args, ex),
            ast::NewInit::Fields(fields) => self.named_form(e, adt, &class_args, fields, ex),
        }
    }

    /// The class `new` names, with its written type arguments (`None` for a generic
    /// class written without them, which the construction infers); EN0221 for what
    /// is no class.
    fn new_target(&mut self, ty: &ast::TypeExpr) -> Option<(AdtId, Option<Vec<Ty>>)> {
        if let ast::TypeExprKind::Named { path, args } = &ty.kind
            && args.is_empty()
            && let Res::Def(def) = scope::lookup_type(self.sema, self.at, path)
            && let DefKind::Adt(adt) = self.sema.tcx.def(def).kind
            && !self
                .sema
                .tcx
                .generics(self.sema.tcx.adt(adt).generics)
                .params
                .is_empty()
        {
            return self.class_or_not(adt, None, ty.span);
        }
        let t = self.lower_ty_unchecked(ty);
        let tcx = &*self.sema.tcx;
        match tcx.kind(t) {
            TyKind::Error => None,
            TyKind::Adt(adt, args) => {
                let args = tcx.list(args).to_vec();
                self.class_or_not(adt, Some(args), ty.span)
            }
            TyKind::Str | TyKind::Slice(_) | TyKind::Array(_) | TyKind::Boxed(_) => {
                match tcx.lang_class_of(t) {
                    Some((adt, args)) => {
                        let args = tcx.list(args).to_vec();
                        self.class_or_not(adt, Some(args), ty.span)
                    }
                    None => None,
                }
            }
            TyKind::Param(p) => {
                let name = tcx.param(p).name;
                self.not_a_class(format!("`{name}` is a type parameter"), ty.span);
                None
            }
            _ => {
                let shown = tcx.ty_string(t);
                self.sema.emit(Diagnostic::new(
                    Code::EN0221,
                    format!("`new` needs a class, not `{shown}`"),
                    ty.span,
                    "not a class",
                ));
                None
            }
        }
    }

    /// `adt` when it is a class; EN0221 for an enum or interface.
    fn class_or_not(
        &mut self,
        adt: AdtId,
        args: Option<Vec<Ty>>,
        span: Span,
    ) -> Option<(AdtId, Option<Vec<Ty>>)> {
        let def = self.sema.tcx.adt(adt);
        let name = def.name;
        match &def.kind {
            hir::AdtKind::Class(_) => Some((adt, args)),
            hir::AdtKind::Enum(_) => {
                self.not_a_class(format!("`{name}` is an enum"), span);
                None
            }
            hir::AdtKind::Interface(_) => {
                self.not_a_class(format!("`{name}` is an interface"), span);
                None
            }
        }
    }

    /// EN0221 at `span`.
    fn not_a_class(&mut self, what: String, span: Span) {
        self.sema.emit(Diagnostic::new(
            Code::EN0221,
            format!("`new` needs a class, and {what}"),
            span,
            "not a class",
        ));
    }

    /// The values of a rejected `new`, typed for the errors inside them.
    fn untyped_init(&mut self, init: &ast::NewInit) {
        match init {
            ast::NewInit::Args(args) => {
                for a in args {
                    let _ = self.check_expr(a, Expect::None);
                }
            }
            ast::NewInit::Fields(fields) => {
                for f in fields {
                    let _ = self.field_value(f, Expect::None);
                }
            }
        }
    }

    /// Fresh variables for the parameters of class or enum `adt`, named in
    /// EN0410 as `` `T` in `what(...)` ``; `Result`'s error type defaults instead.
    fn instance_vars(&mut self, adt: AdtId, what: &str, span: Span) -> Vec<Ty> {
        let tcx = &*self.sema.tcx;
        let def = tcx.adt(adt).def;
        let params = tcx.generics(tcx.adt(adt).generics).params.clone();
        params
            .into_iter()
            .map(|p| {
                if self.defaults_to_failure(def, p) {
                    let var = self.infer.fresh(VarKind::Any);
                    return self.sema.tcx.intern_ty(TyKind::Infer(var));
                }
                let name = self.sema.tcx.param(p).name;
                self.new_var(VarKind::Any, span, format!("`{name}` in `{what}(...)`"))
            })
            .collect()
    }

    /// Whether class `adt` is `abstract`.
    fn is_abstract(&self, adt: AdtId) -> bool {
        self.sema
            .tcx
            .adt(adt)
            .as_class()
            .is_some_and(|c| c.modifier == ClassModifier::Abstract)
    }

    /// The constructors `new` of class `adt` at `args` runs: those of the nearest
    /// class of its chain that declares any, with that class's arguments.
    fn ctor_level(&self, adt: AdtId, args: &[Ty]) -> Option<(AdtId, Vec<Ty>, Vec<DefId>)> {
        let tcx = &*self.sema.tcx;
        let mut cur = Some((adt, tcx.intern_list(args)));
        let mut steps = 0;
        while let Some((class, class_args)) = cur {
            let ctors = tcx
                .adt(class)
                .as_class()
                .map(|c| c.ctors.clone())
                .unwrap_or_default();
            if !ctors.is_empty() {
                return Some((class, tcx.list(class_args).to_vec(), ctors));
            }
            steps += 1;
            if steps > tcx.adts().count() {
                return None;
            }
            cur = tcx.base_of(class, class_args);
        }
        None
    }

    /// `new C(args)`.
    fn new_with_args(
        &mut self,
        e: &ast::Expr,
        name_span: Span,
        adt: AdtId,
        class_args: &[Ty],
        args: &[ast::Expr],
        ex: Expect,
    ) -> hir::Expr {
        let name = self.sema.tcx.adt(adt).name;
        let Some((_, level_args, ctors)) = self.ctor_level(adt, class_args) else {
            if let Some(span) = args_span(args) {
                self.no_ctor(adt, span);
                for a in args {
                    let _ = self.check_expr(a, Expect::None);
                }
                return self.all_defaults(e, adt, class_args, ex, false);
            }
            return self.all_defaults(e, adt, class_args, ex, true);
        };
        let site = CallSite {
            expr: e,
            receiver: None,
            type_args: &[],
            args,
            methods: Vec::new(),
            owner_args: level_args.clone(),
            at: None,
            optional: false,
        };
        let chosen = match ctors.as_slice() {
            [one] => Some(*one),
            many => self.select_overload(many, &site),
        };
        let Some(ctor) = chosen else {
            return self.error_expr(e.span);
        };
        self.check_ctor_visible(ctor, name_span);
        let mut target =
            self.make_target(ctor, Some(&level_args), None, &[], name.as_str(), e.span);
        target.result = self.class_ty(adt, class_args);
        let typed = self.infer_call(&target, args, ex, e.span);
        self.check_call_type_args(&target, args, e.span);
        self.check_instance(adt, class_args, e.span);
        let mut all = class_args.to_vec();
        all.extend_from_slice(&target.args[level_args.len()..target.scope_len]);
        let inst = self.sema.tcx.intern_list(&all);
        self.mk_expr(
            target.result,
            e.span,
            ExprKind::New {
                ctor,
                args: inst,
                values: typed.args,
            },
        )
    }

    /// EN0449 at the arguments `span` of class `adt`'s construction; nothing when
    /// the class's base chain is unknown, whose constructor may be the missing one
    /// (EN0302 was reported at its `extends`).
    fn no_ctor(&mut self, adt: AdtId, span: Span) {
        if self.sema.base_unknown(adt) {
            return;
        }
        let name = self.sema.tcx.adt(adt).name;
        self.sema.emit(Diagnostic::new(
            Code::EN0449,
            format!("`{name}` has no constructor, so it takes no arguments"),
            span,
            "no constructor takes these",
        ));
    }

    /// `new C()` of a chain with no constructor: every field at its default
    /// (S:582); `report` for EN0433 on a field with none.
    fn all_defaults(
        &mut self,
        e: &ast::Expr,
        adt: AdtId,
        class_args: &[Ty],
        ex: Expect,
        report: bool,
    ) -> hir::Expr {
        let ty = self.class_ty(adt, class_args);
        self.hint_instance(ty, ex);
        let args = self.sema.tcx.intern_list(class_args);
        let fields = self.class_fields(adt, args);
        let mut default_from = Vec::new();
        let mut missing = Vec::new();
        for (idx, name, field_ty, has_default) in fields {
            if has_default || self.type_has_default(field_ty) {
                default_from.push(idx);
            } else {
                missing.push(name);
            }
        }
        if report && !missing.is_empty() {
            let written = self.snippet(e.span);
            let class = self.sema.tcx.adt(adt).name;
            let fill: Vec<String> = missing.iter().map(|n| format!("{n}: ...")).collect();
            self.sema.emit(
                Diagnostic::new(
                    Code::EN0433,
                    format!("`{written}` leaves {} unset", name_list(&missing)),
                    e.span,
                    plural(
                        missing.len(),
                        "this field has no default",
                        "these fields have no default",
                    ),
                )
                .with_help(Help::text(format!(
                    "use `new {class} {{ {} }}`",
                    fill.join(", ")
                ))),
            );
        }
        self.check_instance(adt, class_args, e.span);
        self.mk_expr(
            ty,
            e.span,
            ExprKind::NewNamed {
                adt,
                args,
                fields: Vec::new(),
                default_from,
            },
        )
    }

    /// Every field of class `adt` at `args`, flattened: index, name, type, and
    /// whether it has a written default.
    fn class_fields(&self, adt: AdtId, args: hir::TyList) -> Vec<(FieldIdx, Symbol, Ty, bool)> {
        let tcx = &*self.sema.tcx;
        let Some(class) = tcx.adt(adt).as_class() else {
            return Vec::new();
        };
        class
            .fields
            .iter()
            .enumerate()
            .map(|(i, f)| {
                let idx = FieldIdx(i as u32);
                (
                    idx,
                    f.name,
                    tcx.field_ty(adt, None, idx, args),
                    f.has_default,
                )
            })
            .collect()
    }

    /// Unifies an instance's type with the expected type, or its payload, as a hint.
    fn hint_instance(&mut self, ty: Ty, ex: Expect) {
        let Some(hint) = ex.ty() else {
            return;
        };
        let hint = self.shallow(hint);
        if !self.unify(ty, hint)
            && let TyKind::Nullable(payload) = self.sema.tcx.kind(hint)
        {
            let _ = self.unify(ty, payload);
        }
    }

    /// The bounds of class or enum `adt`'s parameters at `args`, the instance a
    /// construction makes.
    fn check_instance(&mut self, adt: AdtId, args: &[Ty], span: Span) {
        let tcx = &*self.sema.tcx;
        let data = tcx.adt(adt);
        let params = tcx.all_params(data.generics);
        if params.is_empty() || params.len() != args.len() {
            return;
        }
        let target = Target {
            def: data.def,
            params,
            args: args.to_vec(),
            scope_len: args.len(),
            check_from: 0,
            result: tcx.common().void,
            name: data.name.as_str().to_owned(),
            explicit: Vec::new(),
        };
        self.check_call_type_args(&target, &[], span);
    }

    // ---------------------------------------------------------------------------
    // Named forms.

    /// `new C { ... }`, or an object literal where class `adt` is expected.
    fn named_form(
        &mut self,
        e: &ast::Expr,
        adt: AdtId,
        class_args: &[Ty],
        fields: &[ast::FieldInit],
        ex: Expect,
    ) -> hir::Expr {
        let name = self.sema.tcx.adt(adt).name;
        let args = self.sema.tcx.intern_list(class_args);
        let all = self.class_fields(adt, args);
        if self.ctor_level(adt, class_args).is_some() {
            self.sema.emit(Diagnostic::new(
                Code::EN0447,
                format!("`{name}` has a constructor: write `new {name}(...)`"),
                e.span,
                "naming the fields skips the constructor",
            ));
            for f in fields {
                let expect = match all.iter().find(|x| x.1 == f.name.name) {
                    Some(&(_, _, t, _)) => Expect::Coerce(t, Site::Field),
                    None => Expect::None,
                };
                let _ = self.field_value(f, expect);
            }
            return self.error_expr(e.span);
        }
        let ty = self.class_ty(adt, class_args);
        self.hint_instance(ty, ex);
        let mut given: Vec<(FieldIdx, hir::Expr)> = Vec::new();
        for f in fields {
            let Some(&(idx, _, field_ty, _)) = all.iter().rev().find(|x| x.1 == f.name.name) else {
                self.unknown_field(
                    format!("`{name}` has no field `{}`", f.name.name),
                    f.name.span,
                    name,
                );
                let _ = self.field_value(f, Expect::None);
                continue;
            };
            let found = MemberRef {
                kind: MemberKind::Field { adt, field: idx },
                via_slice: None,
                owner: self.sema.tcx.adt(adt).def,
                args,
            };
            let _ = self.check_visible(found, f.name);
            let value = self.field_value(f, Expect::Coerce(field_ty, Site::Field));
            given.push((idx, value));
        }
        let mut default_from = Vec::new();
        let mut missing = Vec::new();
        for &(idx, field_name, field_ty, has_default) in &all {
            if given.iter().any(|(i, _)| *i == idx) {
                continue;
            }
            if has_default || self.type_has_default(field_ty) {
                default_from.push(idx);
            } else {
                missing.push(field_name);
            }
        }
        self.missing_fields(&missing, e.span);
        if !matches!(e.kind, ast::ExprKind::New { .. }) && self.is_abstract(adt) {
            self.sema.emit(Diagnostic::new(
                Code::EN0445,
                format!("`{name}` is abstract, so it can't be created"),
                e.span,
                "an abstract class",
            ));
            return self.error_expr(e.span);
        }
        self.check_instance(adt, class_args, e.span);
        self.mk_expr(
            ty,
            e.span,
            ExprKind::NewNamed {
                adt,
                args,
                fields: given,
                default_from,
            },
        )
    }

    /// EN0434 for a field `what` names, at `span`.
    fn unknown_field(&mut self, what: String, span: Span, owner: Symbol) {
        self.sema.emit(Diagnostic::new(
            Code::EN0434,
            what,
            span,
            format!("not a field of `{owner}`"),
        ));
    }

    /// EN0433 for the fields `missing` names, at the literal `span`.
    fn missing_fields(&mut self, missing: &[Symbol], span: Span) {
        if missing.is_empty() {
            return;
        }
        let word = plural(missing.len(), "field", "fields");
        self.sema.emit(Diagnostic::new(
            Code::EN0433,
            format!("missing {word} {}", name_list(missing)),
            span,
            "every field without a default must be set",
        ));
    }

    /// A field's value, the shorthand `{ name }` reading the name.
    fn field_value(&mut self, f: &ast::FieldInit, ex: Expect) -> hir::Expr {
        match &f.value {
            Some(v) => self.check_expr(v, ex),
            None => {
                let read = ast::Expr {
                    id: ast::NodeId(u32::MAX),
                    span: f.name.span,
                    kind: ast::ExprKind::Ident(f.name.name),
                };
                self.check_expr(&read, ex)
            }
        }
    }

    // ---------------------------------------------------------------------------
    // Object literals.

    /// `{ f: v }`: a class's named form, an object type's value, or an anonymous
    /// object.
    fn object_lit(&mut self, e: &ast::Expr, fields: &[ast::FieldInit], ex: Expect) -> hir::Expr {
        let expected = ex.ty().map(|t| {
            let t = self.shallow(t);
            match self.sema.tcx.kind(t) {
                TyKind::Nullable(inner) => self.shallow(inner),
                _ => t,
            }
        });
        let tcx = &*self.sema.tcx;
        match expected.map(|t| tcx.kind(t)) {
            Some(TyKind::Adt(adt, args)) if tcx.adt(adt).is_class() => {
                let args = tcx.list(args).to_vec();
                self.named_form(e, adt, &args, fields, ex)
            }
            Some(TyKind::Object(shape)) => self.shaped_object(e, shape, fields),
            _ => self.anonymous_object(e, fields),
        }
    }

    /// An object literal at object type `shape` (S:600-601).
    fn shaped_object(
        &mut self,
        e: &ast::Expr,
        shape: hir::ShapeId,
        fields: &[ast::FieldInit],
    ) -> hir::Expr {
        let tcx = &*self.sema.tcx;
        let sh = (*tcx.shape(shape)).clone();
        let shape_ty = tcx.intern_ty(TyKind::Object(shape));
        let shown = tcx.ty_string(shape_ty);
        let mut values: Vec<Option<hir::Expr>> = vec![None; sh.fields.len()];
        let mut eval = Vec::new();
        for f in fields {
            match sh.position(f.name.name) {
                Some(i) if values[i].is_none() => {
                    let field_ty = sh.fields[i].1;
                    values[i] = Some(self.field_value(f, Expect::Coerce(field_ty, Site::Field)));
                    eval.push(i as u32);
                }
                Some(_) => {
                    let _ = self.field_value(f, Expect::None);
                }
                None => {
                    let message = match self.literal_arg_of(e.span) {
                        Some(callee) => format!(
                            "`{callee}` doesn't use the field `{}`, so it would be thrown away",
                            f.name.name
                        ),
                        None => format!("`{shown}` has no field `{}`", f.name.name),
                    };
                    self.sema.emit(Diagnostic::new(
                        Code::EN0434,
                        message,
                        f.name.span,
                        format!("not a field of `{shown}`"),
                    ));
                    let _ = self.field_value(f, Expect::None);
                }
            }
        }
        let mut missing = Vec::new();
        let mut out = Vec::with_capacity(values.len());
        for (i, value) in values.into_iter().enumerate() {
            let (field_name, field_ty) = sh.fields[i];
            match value {
                Some(v) => out.push(v),
                None if sh.is_optional(field_name) => {
                    out.push(self.mk_expr(field_ty, e.span, ExprKind::NullLit));
                }
                None => {
                    missing.push(field_name);
                    out.push(self.error_expr(e.span));
                }
            }
        }
        self.missing_fields(&missing, e.span);
        let kind = ExprKind::ObjectLit {
            shape,
            fields: out,
            eval,
        };
        self.mk_expr(shape_ty, e.span, kind)
    }

    /// EN0433 for a value of an object type that lacks optional fields of the object
    /// type it meets, directly or behind `&` (S:600): `` missing `subtitle` ``, help
    /// `` add `subtitle: null` ``; only a literal written at that type may leave them
    /// out. `false`, reporting nothing, for any other mismatch. `coerce`'s failure
    /// path asks this before its mismatch (plan d.16).
    pub(crate) fn report_missing_optional(&mut self, e: &hir::Expr, from: Ty, target: Ty) -> bool {
        let tcx = &*self.sema.tcx;
        let (from_v, target_v) = match (tcx.kind(from), tcx.kind(target)) {
            (TyKind::Ref(f), TyKind::Ref(t)) => (self.shallow(f), self.shallow(t)),
            _ => (from, target),
        };
        let (TyKind::Object(have), TyKind::Object(want)) = (tcx.kind(from_v), tcx.kind(target_v))
        else {
            return false;
        };
        let (have, want) = ((*tcx.shape(have)).clone(), (*tcx.shape(want)).clone());
        let mut probe = self.infer.clone();
        let fits = have.fields.iter().all(|&(name, t)| {
            want.position(name).is_some_and(|i| {
                crate::typeck::infer::unify_in(tcx, &mut probe, t, want.fields[i].1)
            })
        });
        let missing: Vec<Symbol> = want
            .fields
            .iter()
            .map(|&(name, _)| name)
            .filter(|&name| have.position(name).is_none())
            .collect();
        if !fits || missing.is_empty() || !missing.iter().all(|&n| want.is_optional(n)) {
            return false;
        }
        let fill: Vec<String> = missing.iter().map(|n| format!("{n}: null")).collect();
        let shown = self.ty_str(target_v);
        self.sema.emit(
            Diagnostic::new(
                Code::EN0433,
                format!("missing {}", name_list(&missing)),
                e.span,
                format!("`{shown}` needs every field it names, optional ones included"),
            )
            .with_help(Help::text(format!("add `{}`", fill.join(", ")))),
        );
        true
    }

    /// The callee whose argument the literal at `span` is, directly or behind `&`.
    fn literal_arg_of(&self, span: Span) -> Option<Symbol> {
        let frame = self.calls.last()?;
        let callee = frame.callee?;
        let inner = self.snippet(span);
        frame
            .args
            .iter()
            .any(|&a| {
                a.lo <= span.lo && span.hi <= a.hi && {
                    let outer = self.snippet(a);
                    outer
                        .trim_start_matches(|c: char| c == '&' || c == '(' || c.is_whitespace())
                        .trim_end_matches(|c: char| c == ')' || c.is_whitespace())
                        == inner
                }
            })
            .then_some(callee)
    }

    /// An object literal with no expected class or object type (S:600).
    fn anonymous_object(&mut self, e: &ast::Expr, fields: &[ast::FieldInit]) -> hir::Expr {
        let mut named: Vec<(Symbol, hir::Expr)> = Vec::new();
        for f in fields {
            let value = self.field_value(f, Expect::None);
            if named.iter().all(|(n, _)| *n != f.name.name) {
                named.push((f.name.name, value));
            }
        }
        let shape = Shape::new(named.iter().map(|(n, v)| (*n, v.ty)).collect());
        let order: Vec<Symbol> = shape.fields.iter().map(|(n, _)| *n).collect();
        let tcx = &*self.sema.tcx;
        let id = tcx.intern_shape(shape);
        let ty = tcx.intern_ty(TyKind::Object(id));
        // The values evaluate as written (O6), each at its shape position.
        let eval = (named.iter())
            .filter_map(|(n, _)| order.iter().position(|m| m == n).map(|i| i as u32))
            .collect();
        let mut values = Vec::with_capacity(order.len());
        for name in order {
            if let Some(i) = named.iter().position(|(n, _)| *n == name) {
                values.push(named.swap_remove(i).1);
            }
        }
        self.mk_expr(
            ty,
            e.span,
            ExprKind::ObjectLit {
                shape: id,
                fields: values,
                eval,
            },
        )
    }

    // ---------------------------------------------------------------------------
    // Case literals.

    /// `E.V { ... }`, `E<T>.V { ... }`, or `Ok { ... }` and `Err { ... }` bare.
    fn case_lit(
        &mut self,
        e: &ast::Expr,
        path: &[Ident],
        args: &[ast::TypeExpr],
        fields: &[ast::FieldInit],
        ex: Expect,
    ) -> hir::Expr {
        let Some((case, enum_path)) = path.split_last() else {
            return self.error_expr(e.span);
        };
        let Some((adt, given)) = self.case_enum(enum_path, args, *case) else {
            for f in fields {
                let _ = self.field_value(f, Expect::None);
            }
            return self.error_expr(e.span);
        };
        let tcx = &*self.sema.tcx;
        let enum_name = tcx.adt(adt).name;
        let Some((variant, vdef)) = tcx
            .adt(adt)
            .as_enum()
            .and_then(|en| en.variant_named(case.name))
            .map(|(i, v)| (i, v.clone()))
        else {
            let names: Vec<String> = tcx
                .adt(adt)
                .as_enum()
                .map(|en| {
                    en.variants
                        .iter()
                        .map(|v| v.name.as_str().to_owned())
                        .collect()
                })
                .unwrap_or_default();
            let refs: Vec<&str> = names.iter().map(String::as_str).collect();
            let mut diag = Diagnostic::new(
                Code::EN0303,
                format!("`{enum_name}` has no case `{}`", case.name),
                case.span,
                "no such case",
            );
            if let Some(similar) = did_you_mean(case.name.as_str(), &refs) {
                diag = diag.with_help(Help::text(format!("did you mean `{enum_name}.{similar}`?")));
            }
            self.sema.emit(diag);
            for f in fields {
                let _ = self.field_value(f, Expect::None);
            }
            return self.error_expr(e.span);
        };
        let enum_args = match given {
            Some(args) => args,
            None => self.instance_vars(adt, &format!("{enum_name}.{}", case.name), e.span),
        };
        let ty = self.sema.tcx.mk_adt(adt, &enum_args);
        self.hint_instance(ty, ex);
        let args_list = self.sema.tcx.intern_list(&enum_args);
        let written = format!("{enum_name}.{}", case.name);
        let mut values: Vec<Option<hir::Expr>> = vec![None; vdef.fields.len()];
        let mut eval = Vec::new();
        for f in fields {
            match vdef.fields.iter().position(|x| x.name == f.name.name) {
                Some(i) if values[i].is_none() => {
                    let field_ty =
                        self.sema
                            .tcx
                            .field_ty(adt, Some(variant), FieldIdx(i as u32), args_list);
                    values[i] = Some(self.field_value(f, Expect::Coerce(field_ty, Site::Field)));
                    eval.push(i as u32);
                }
                Some(_) => {
                    let _ = self.field_value(f, Expect::None);
                }
                None => {
                    self.sema.emit(Diagnostic::new(
                        Code::EN0434,
                        format!("`{written}` has no field `{}`", f.name.name),
                        f.name.span,
                        format!("not a field of `{written}`"),
                    ));
                    let _ = self.field_value(f, Expect::None);
                }
            }
        }
        let mut missing = Vec::new();
        let mut out = Vec::with_capacity(values.len());
        for (i, value) in values.into_iter().enumerate() {
            match value {
                Some(v) => out.push(v),
                None => {
                    let field_ty =
                        self.sema
                            .tcx
                            .field_ty(adt, Some(variant), FieldIdx(i as u32), args_list);
                    match self.default_value(field_ty, e.span) {
                        Some(d) => out.push(d),
                        None => {
                            missing.push(vdef.fields[i].name);
                            out.push(self.error_expr(e.span));
                        }
                    }
                }
            }
        }
        self.missing_fields(&missing, e.span);
        self.check_instance(adt, &enum_args, e.span);
        self.mk_expr(
            ty,
            e.span,
            ExprKind::VariantLit {
                adt,
                variant,
                args: args_list,
                fields: out,
                eval,
            },
        )
    }

    /// The enum a case literal names, with its written arguments (`None` for a
    /// generic enum written without them); EN0303 when it names none.
    fn case_enum(
        &mut self,
        enum_path: &[Ident],
        args: &[ast::TypeExpr],
        case: Ident,
    ) -> Option<(AdtId, Option<Vec<Ty>>)> {
        if enum_path.is_empty() {
            if matches!(case.name.as_str(), "Ok" | "Err")
                && let Some(result) = self.sema.tcx.lang_adt(LangItem::Result)
            {
                return Some((result, None));
            }
            self.sema.emit(Diagnostic::new(
                Code::EN0303,
                format!("`{}` is not a case of an enum", case.name),
                case.span,
                "cases are written with their enum, `E.V { ... }`",
            ));
            return None;
        }
        if args.is_empty()
            && let Res::Def(def) = scope::lookup_type(self.sema, self.at, enum_path)
            && let DefKind::Adt(adt) = self.sema.tcx.def(def).kind
            && self.sema.tcx.adt(adt).is_enum()
            && !self
                .sema
                .tcx
                .generics(self.sema.tcx.adt(adt).generics)
                .params
                .is_empty()
        {
            return Some((adt, None));
        }
        let first = enum_path[0].span;
        let last = args
            .last()
            .map_or(enum_path[enum_path.len() - 1].span, |a| a.span);
        let written = ast::TypeExpr {
            id: ast::NodeId(u32::MAX),
            span: first.to(last),
            kind: ast::TypeExprKind::Named {
                path: enum_path.to_vec(),
                args: args.to_vec(),
            },
        };
        let t = self.lower_ty_unchecked(&written);
        let tcx = &*self.sema.tcx;
        match tcx.kind(t) {
            TyKind::Error => None,
            TyKind::Adt(adt, list) if tcx.adt(adt).is_enum() => {
                Some((adt, Some(tcx.list(list).to_vec())))
            }
            _ => {
                let shown = tcx.ty_string(t);
                self.sema.emit(Diagnostic::new(
                    Code::EN0303,
                    format!("`{shown}` has no case `{}`", case.name),
                    case.span,
                    format!("`{shown}` is not an enum"),
                ));
                None
            }
        }
    }

    // ---------------------------------------------------------------------------
    // Defaults.

    /// Whether a field of type `t` with no initialiser starts at its type's
    /// default: the one table EN0448 reads too (`classes::sig::has_type_default`).
    pub(crate) fn type_has_default(&self, t: Ty) -> bool {
        let t = self.resolve(t);
        crate::classes::sig::has_type_default(self.sema.tcx, t)
    }

    /// The default value of type `t`, for a case literal's left-out field; `None`
    /// for a type with none.
    fn default_value(&mut self, t: Ty, span: Span) -> Option<hir::Expr> {
        let tcx = &*self.sema.tcx;
        let t = self.resolve(t);
        let kind = match tcx.kind(t) {
            TyKind::Int(_) => ExprKind::Const(ConstValue::Int(0, t)),
            TyKind::Float(_) => ExprKind::Const(ConstValue::Float(0, t)),
            TyKind::Bool => ExprKind::Const(ConstValue::Bool(false)),
            TyKind::Void => ExprKind::Const(ConstValue::Void),
            TyKind::Str => ExprKind::Const(ConstValue::Str(tcx.intern_str(""))),
            TyKind::Array(_) => ExprKind::ArrayLit(Vec::new()),
            TyKind::Nullable(_) => ExprKind::NullLit,
            TyKind::Raw(_) => {
                let usize_ty = tcx.common().usize;
                let zero = self.mk_expr(
                    usize_ty,
                    span,
                    ExprKind::Const(ConstValue::Int(0, usize_ty)),
                );
                ExprKind::Cast(Box::new(zero), hir::CastKind::UsizeToRaw)
            }
            TyKind::Fixed(e, n) => {
                let elem = self.default_value(e, span)?;
                ExprKind::Repeat(Box::new(elem), n)
            }
            TyKind::Tuple(parts) => {
                let parts = tcx.list(parts).to_vec();
                let mut values = Vec::with_capacity(parts.len());
                for p in parts {
                    values.push(self.default_value(p, span)?);
                }
                ExprKind::TupleLit(values)
            }
            TyKind::Object(shape) => {
                let fields = tcx.shape(shape).fields.clone();
                let mut values = Vec::with_capacity(fields.len());
                for (_, f) in fields {
                    values.push(self.default_value(f, span)?);
                }
                ExprKind::ObjectLit {
                    shape,
                    fields: values,
                    eval: Vec::new(),
                }
            }
            TyKind::Error => return Some(self.error_expr(span)),
            _ => return None,
        };
        Some(self.mk_expr(t, span, kind))
    }

    // ---------------------------------------------------------------------------
    // `super(...)`.

    /// `super(args)` in a constructor of a class whose base is `adt` at
    /// `base_args`: the nearest constructor of the base chain, EN0449 with
    /// arguments when it has none (S:587, T:987).
    pub(crate) fn check_super_ctor(
        &mut self,
        adt: AdtId,
        base_args: hir::TyList,
        site: CallSite,
    ) -> hir::Expr {
        let span = site.expr.span;
        let void = self.sema.tcx.common().void;
        let args_v = self.sema.tcx.list(base_args).to_vec();
        let Some((_, level_args, ctors)) = self.ctor_level(adt, &args_v) else {
            if let Some(at) = args_span(site.args) {
                self.no_ctor(adt, at);
            }
            let args = site
                .args
                .iter()
                .map(|a| self.check_expr(a, Expect::None))
                .collect();
            return self.mk_expr(
                void,
                span,
                ExprKind::Call {
                    callee: Callee::SuperCtor {
                        adt,
                        args: base_args,
                        ctor: None,
                    },
                    receiver: None,
                    args,
                },
            );
        };
        let site = CallSite {
            owner_args: level_args.clone(),
            ..site
        };
        let chosen = match ctors.as_slice() {
            [one] => Some(*one),
            many => self.select_overload(many, &site),
        };
        let Some(ctor) = chosen else {
            return self.error_expr(span);
        };
        let callee_span = match &site.expr.kind {
            ast::ExprKind::Call { callee, .. } => callee.span,
            _ => span,
        };
        self.check_ctor_visible(ctor, callee_span);
        let mut target = self.make_target(ctor, Some(&level_args), None, &[], "super", span);
        target.result = void;
        let typed = self.infer_call(&target, site.args, Expect::None, span);
        self.check_call_type_args(&target, site.args, span);
        self.mk_expr(
            void,
            span,
            ExprKind::Call {
                callee: Callee::SuperCtor {
                    adt,
                    args: base_args,
                    ctor: Some(ctor),
                },
                receiver: None,
                args: typed.args,
            },
        )
    }
}

/// `` `a` ``, `` `a` and `b` ``, `` `a`, `b` and `c` ``.
fn name_list(names: &[Symbol]) -> String {
    let quoted: Vec<String> = names.iter().map(|n| format!("`{n}`")).collect();
    match quoted.as_slice() {
        [] => String::new(),
        [one] => one.clone(),
        [init @ .., last] => format!("{} and {last}", init.join(", ")),
    }
}

/// `one` for a count of 1, else `many`.
fn plural(n: usize, one: &str, many: &str) -> String {
    if n == 1 {
        one.to_owned()
    } else {
        many.to_owned()
    }
}
