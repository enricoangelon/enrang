//! Compiler forms (SPEC 6's table, S:1177-1191; plan d.17; owner 4A), each typed
//! into a `Callee::Form`: `console.log` and `console.error` (variadic, any values,
//! `void`; any other member of `console` is EN0303, and `console` called itself
//! EN0428), `panic(m)` (`m` a `&string` or a template, `never`), `assert(c, m?)`
//! (`c` a condition, `void`), `unreachable()` (`never`), `dispose(x)` (any value by
//! move, `void`), `writeTo(f, t)` (`f` a `&Formatter`, `t` as `panic`'s `m`,
//! `void`), `sizeOf<T>()`, `alignOf<T>()` and `offsetOf<T>("f")` (`usize`; a field
//! `T` lacks is EN0303), and `x.toString()` (any value with no `toString` member of
//! its own, `string`). A wrong number of arguments is EN0423. `Err` is 4C's;
//! `mem.forget` and `cpu.has` (EN0908) are typed with the calls through their
//! namespaces. The implicit shared borrow of a printed value is the form's own,
//! as a template hole's is: no `Adjust` is recorded (plan choice).

use enrang_base::Span;
use enrang_diag::{Code, Diagnostic, Help, did_you_mean};
use enrang_hir::{
    self as hir, Callee, ExprKind, FieldIdx, FormKind, FormName, LangItem, RecordKind, Ty, TyKind,
};
use enrang_syntax::ast::{self, Ident};

use crate::typeck::generic::strip_parens;
use crate::typeck::{Expect, FnCtxt, Site};

impl FnCtxt<'_, '_> {
    /// A call of the form `f` (or a size form, `e` a `SizeForm`).
    pub(crate) fn check_form(&mut self, f: FormName, e: &ast::Expr, ex: Expect) -> hir::Expr {
        match f {
            FormName::Err => return self.check_err(e, ex),
            FormName::SizeOf | FormName::AlignOf | FormName::OffsetOf => {
                return self.size_form(e);
            }
            _ => {}
        }
        let ast::ExprKind::Call { callee, args, .. } = &e.kind else {
            return self.error_expr(e.span);
        };
        let common = *self.sema.tcx.common();
        let (kind, ty, typed) = match f {
            FormName::Console => {
                let Some(kind) = self.console_member(callee) else {
                    return self.untyped_form(args, e.span);
                };
                let typed = args
                    .iter()
                    .map(|a| {
                        let arg = self.check_expr(a, Expect::None);
                        self.iface_rvalue(arg)
                    })
                    .collect();
                (kind, common.void, typed)
            }
            FormName::Panic => {
                self.form_arity("panic", 1, 1, args, e.span);
                let typed = args.iter().map(|a| self.message_arg(a)).collect();
                (FormKind::Panic, common.never, typed)
            }
            FormName::Assert => {
                self.form_arity("assert", 1, 2, args, e.span);
                let typed = args
                    .iter()
                    .enumerate()
                    .map(|(i, a)| match i {
                        0 => self.check_cond(a),
                        _ => self.message_arg(a),
                    })
                    .collect();
                (FormKind::Assert, common.void, typed)
            }
            FormName::Unreachable => {
                self.form_arity("unreachable", 0, 0, args, e.span);
                let typed = args
                    .iter()
                    .map(|a| self.check_expr(a, Expect::None))
                    .collect();
                (FormKind::Unreachable, common.never, typed)
            }
            FormName::Dispose => {
                self.form_arity("dispose", 1, 1, args, e.span);
                let typed = args
                    .iter()
                    .map(|a| self.check_expr(a, Expect::None))
                    .collect();
                (FormKind::Dispose, common.void, typed)
            }
            FormName::WriteTo => {
                self.form_arity("writeTo", 2, 2, args, e.span);
                let formatter = self.formatter_ref();
                let typed = args
                    .iter()
                    .enumerate()
                    .map(|(i, a)| match (i, formatter) {
                        (0, Some(f)) => self.check_expr(a, Expect::Coerce(f, Site::Arg)),
                        (0, None) => self.check_expr(a, Expect::None),
                        _ => self.message_arg(a),
                    })
                    .collect();
                (FormKind::WriteTo, common.void, typed)
            }
            FormName::Err | FormName::SizeOf | FormName::AlignOf | FormName::OffsetOf => {
                return self.error_expr(e.span);
            }
        };
        let typed: Vec<hir::Expr> = typed;
        for arg in &typed {
            self.record_ref(arg, RecordKind::CallArg);
        }
        self.mk_expr(
            ty,
            e.span,
            ExprKind::Call {
                callee: Callee::Form(kind),
                receiver: None,
                args: typed,
            },
        )
    }

    /// `console.log` or `console.error`; another member is EN0303, `console`
    /// called itself EN0428.
    fn console_member(&mut self, callee: &ast::Expr) -> Option<FormKind> {
        let ast::ExprKind::Member { name, .. } = &strip_parens(callee).kind else {
            self.sema.emit(Diagnostic::new(
                Code::EN0428,
                "`console` is not callable",
                callee.span,
                "a compiler form, called as `console.log(...)` or `console.error(...)`",
            ));
            return None;
        };
        match name.name.as_str() {
            "log" => Some(FormKind::ConsoleLog),
            "error" => Some(FormKind::ConsoleError),
            other => {
                let mut diag = Diagnostic::new(
                    Code::EN0303,
                    format!("`console` has no member `{other}`"),
                    name.span,
                    "no such member",
                );
                if let Some(similar) = did_you_mean(other, &["log", "error"]) {
                    diag = diag.with_help(Help::text(format!("did you mean `{similar}`?")));
                }
                self.sema.emit(diag);
                None
            }
        }
    }

    /// The arguments of a form typing rejected, each with no expected type.
    fn untyped_form(&mut self, args: &[ast::Expr], span: Span) -> hir::Expr {
        for a in args {
            let _ = self.check_expr(a, Expect::None);
        }
        self.error_expr(span)
    }

    /// EN0423 when a form is given a number of arguments outside `lo..=hi`.
    fn form_arity(&mut self, name: &str, lo: usize, hi: usize, args: &[ast::Expr], span: Span) {
        if args.len() < lo || args.len() > hi {
            self.arity_error(name, lo, hi, args.len(), span, None);
        }
    }

    /// A message: a template as it is, anything else at `&string` (C13 for a
    /// literal).
    fn message_arg(&mut self, a: &ast::Expr) -> hir::Expr {
        if matches!(strip_parens(a).kind, ast::ExprKind::Template(_)) {
            return self.check_expr(a, Expect::None);
        }
        let str_ref = self.sema.tcx.mk_ref(self.sema.tcx.common().str);
        self.check_expr(a, Expect::Coerce(str_ref, Site::Arg))
    }

    /// `&Formatter`, once the library declares it.
    fn formatter_ref(&self) -> Option<Ty> {
        let tcx = &*self.sema.tcx;
        let adt = tcx.lang_adt(LangItem::Formatter)?;
        Some(tcx.mk_ref(tcx.mk_adt(adt, &[])))
    }

    /// `sizeOf<T>()`, `alignOf<T>()` or `offsetOf<T>("f")`: a `usize`.
    fn size_form(&mut self, e: &ast::Expr) -> hir::Expr {
        let ast::ExprKind::SizeForm(form) = &e.kind else {
            return self.error_expr(e.span);
        };
        let sized = |me: &mut Self, t: &ast::TypeExpr| me.lower_body_type(t, true);
        let kind = match form {
            ast::SizeForm::SizeOf(t) => FormKind::SizeOf(sized(self, t)),
            ast::SizeForm::AlignOf(t) => FormKind::AlignOf(sized(self, t)),
            ast::SizeForm::OffsetOf(t, field) => {
                let ty = sized(self, t);
                if self.sema.tcx.references_error(ty) {
                    return self.error_expr(e.span);
                }
                let Some(index) = self.field_index(ty, field.value) else {
                    let shown = self.ty_str(ty);
                    self.sema.emit(Diagnostic::new(
                        Code::EN0303,
                        format!("`{shown}` has no field `{}`", field.value),
                        field.span,
                        "no such field",
                    ));
                    return self.error_expr(e.span);
                };
                FormKind::OffsetOf(ty, index)
            }
        };
        let usize_ty = self.sema.tcx.common().usize;
        // A rejected type (EN1006, EN0401, EN0701) leaves no size to compute.
        if let FormKind::SizeOf(t) | FormKind::AlignOf(t) = kind
            && self.sema.tcx.references_error(t)
        {
            return self.error_expr(e.span);
        }
        self.mk_expr(
            usize_ty,
            e.span,
            ExprKind::Call {
                callee: Callee::Form(kind),
                receiver: None,
                args: Vec::new(),
            },
        )
    }

    /// The index of field `name` in `ty`: a class's flattened one, or an object
    /// type's place in its shape.
    fn field_index(&self, ty: Ty, name: enrang_base::Symbol) -> Option<FieldIdx> {
        let tcx = &*self.sema.tcx;
        match tcx.kind(ty) {
            TyKind::Adt(adt, _) => tcx
                .adt(adt)
                .as_class()
                .and_then(|c| c.field_named(name))
                .map(|(i, _)| i),
            TyKind::Object(shape) => tcx.shape(shape).position(name).map(|i| FieldIdx(i as u32)),
            _ => None,
        }
    }

    /// `x.toString()` (S:1182): a `string` from any value whose type has no
    /// `toString` member of its own, nor, as member lookup goes on through `Box`
    /// (S:607), any type a `Box` holds; `None` leaves the call to member lookup.
    pub(crate) fn to_string_form(
        &mut self,
        raw: &hir::Expr,
        name: Ident,
        args: &[ast::Expr],
        call: &ast::Expr,
    ) -> Option<hir::Expr> {
        let tcx = &*self.sema.tcx;
        let mut t = self.shallow(raw.ty);
        if let TyKind::Ref(inner) = tcx.kind(t) {
            t = self.shallow(inner);
        }
        loop {
            if tcx
                .member_in(t, name.name, self.at.module, &self.env)
                .is_some()
            {
                return None;
            }
            match tcx.kind(t) {
                TyKind::Boxed(inner) => t = self.shallow(inner),
                _ => break,
            }
        }
        if !args.is_empty() {
            self.arity_error("toString", 0, 0, args.len(), call.span, None);
            for a in args {
                let _ = self.check_expr(a, Expect::None);
            }
        }
        let value = self.narrowed(raw.clone());
        self.record_ref(&value, RecordKind::CallArg);
        let str_ty = self.sema.tcx.common().str;
        Some(self.mk_expr(
            str_ty,
            call.span,
            ExprKind::Call {
                callee: Callee::Form(FormKind::ToString),
                receiver: None,
                args: vec![value],
            },
        ))
    }
}
