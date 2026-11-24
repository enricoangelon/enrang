//! Expressions (plan c.5, d.5; owner 3A): `check_expr` synthesises each expression's
//! type and, at a coercion site, passes it to `coerce`, the only place that pushes
//! `Adjust`s (A:888). It dispatches to the seams of the other stages: names
//! (`check_path`, `this` and `super` included), calls (`check_call`, inside a
//! [`CallFrame`] that a coercion at an argument names), construction (`check_new`),
//! compiler forms (`check_form`, `sizeOf` and its kin), `?` (`check_try`), arrows
//! (`check_arrow`) and members (`lookup_member`), and to the operator, literal and
//! cast rules of `ops.rs`, `literal.rs` and `cast.rs`.
//!
//! Here: a field read from what `lookup_member` finds (`p?.f` has type `&F | null`,
//! S:750), and fields of an anonymous object type by name; a member access on an
//! unknown type is EN0410 at once (S:733); arrays from the expected type (a tuple, a
//! fixed array, `T[N]` behind `&` at `&Slice<T>`, else a growable array whose
//! elements unify, `[1, "a"]` EN0401 with a tuple help; `[]` with no expected type is
//! `?[]`, S:733, S:735); spreads (A:890, S:803-823: one `&` peeled, `AutoBorrow` or
//! `Reborrow` then `ArrayToSlice` or `FixedToSlice`, the element type unified, never
//! coerced, `Clone` checked after inference, EN0438, EN0410, EN0401 with the `.map`
//! help); repeat literals; `match` with arm values typed against the subject
//! (EN0502, EN0504), `match (true)` with conditions as `ArmValue::Cond`, and arm
//! results that coerce to an expected type or else unify (EN0432); ternaries
//! (EN0432), a string literal among `&string` results taking its descriptor (C13);
//! indexing (EN0405) and tuple indices (EN0452), one `&` stripped as a `Deref` node
//! as a member's base is; `null` at an expected
//! nullable (EN0410 with none); templates; `&`, `*`, `void`, `!`; assignments
//! (EN0422 for a value into a reference variable, S:656, S:775) and `++`/`--`;
//! `asm` operands.
//!
//! A one-segment arm value that names a local is EN0504, one in no scope EN0301;
//! under `match (true)` a path is a condition.
//!
//! A `match` arm value that typing rejects stays as `ArmValue::Const(Void)`, which
//! fits no column, so exhaustiveness skips that `match` (2D's handover). While
//! typing, a number literal in an arm value is an `ArmValue::Cond` holding the
//! literal, and a range one holding a `TupleLit` of its ends; the resolver turns them
//! into `Const` and `Range` once the literals have their final types.

use enrang_base::{Span, intern};
use enrang_diag::{Code, Diagnostic, Edit, Help};
use enrang_hir::{
    self as hir, Adjust, AdtKind, ArmBody, ArmValue, ArrayPart, ConstValue, ExprKind, Fact,
    FieldIdx, FormName, LangItem, LoopId, RecordKind, Res, SpreadKind, StmtKind, TplPart, Ty,
    TyKind, VariantIdx,
};
use enrang_syntax::ast;

use crate::consteval;
use crate::resolve::scope;
use crate::typeck::infer::VarKind;
use crate::typeck::{CallFrame, Expect, FnCtxt, NumNeed, Site};

impl FnCtxt<'_, '_> {
    /// Types `e` against `ex`, with the use `ex` gives its value (`value_use`), or
    /// the enclosing one when the caller set `inherit_use`.
    pub(crate) fn check_expr(&mut self, e: &ast::Expr, ex: Expect) -> hir::Expr {
        let saved = self.value_use;
        if !std::mem::take(&mut self.inherit_use) {
            self.value_use = self.use_of(ex);
        }
        let typed = self.check_expr_kind(e, ex);
        self.value_use = saved;
        typed
    }

    /// [`Self::check_expr`] once `value_use` is set.
    fn check_expr_kind(&mut self, e: &ast::Expr, ex: Expect) -> hir::Expr {
        let typed = match &e.kind {
            ast::ExprKind::Paren(inner) => {
                // Parentheses change no use of the value.
                self.inherit_use = true;
                return self.check_expr(inner, ex);
            }
            ast::ExprKind::Ident(_)
            | ast::ExprKind::This
            | ast::ExprKind::Super
            | ast::ExprKind::TypeMember { .. } => {
                let path = self.check_path(e, ex);
                self.narrow_read(path, ex)
            }
            ast::ExprKind::Call { callee, args, .. } => {
                let frame = call_frame(callee, args);
                self.calls.push(frame);
                let call = self.check_call(e, ex);
                self.calls.pop();
                call
            }
            ast::ExprKind::New { ty, init } => {
                let args: &[ast::Expr] = match init {
                    ast::NewInit::Args(args) => args,
                    ast::NewInit::Fields(_) => &[],
                };
                self.calls.push(CallFrame {
                    callee: type_name(ty),
                    callee_span: Span::DUMMY,
                    args: args.iter().map(|a| a.span).collect(),
                    reported: false,
                });
                let new = self.check_new(e, ex);
                self.calls.pop();
                new
            }
            ast::ExprKind::CaseLit { .. } | ast::ExprKind::ObjectLit(_) => self.check_new(e, ex),
            ast::ExprKind::Try(_) => self.check_try(e),
            ast::ExprKind::Arrow(arrow) => {
                // An arrow's `return` ends the arrow's body, not the enclosing one.
                let (reachable, loops) = (self.reachable, std::mem::take(&mut self.loops));
                let flow = self.enter_arrow(arrow);
                let typed = self.check_arrow(arrow, ex.ty());
                self.exit_arrow(flow, &typed);
                (self.reachable, self.loops) = (reachable, loops);
                typed
            }
            ast::ExprKind::Member { .. } => {
                let member = self.check_member_expr(e, ex);
                self.narrow_read(member, ex)
            }
            ast::ExprKind::Int { .. }
            | ast::ExprKind::Float(_)
            | ast::ExprKind::Str(_)
            | ast::ExprKind::RawTemplate(_)
            | ast::ExprKind::Bool(_) => self.check_literal(e, ex),
            ast::ExprKind::Template(parts) => self.check_template(parts, e.span),
            ast::ExprKind::Null => self.check_null(e.span, ex),
            ast::ExprKind::Array(elems) => {
                let lit = self.check_array(elems, e.span, ex);
                self.moved_into(&lit);
                lit
            }
            ast::ExprKind::Repeat(value, count) => self.check_repeat(value, count, e.span, ex),
            ast::ExprKind::Match { subject, arms } => {
                self.check_match(subject, arms, e.span, ex, false)
            }
            ast::ExprKind::SizeForm(form) => {
                let name = match form {
                    ast::SizeForm::SizeOf(_) => FormName::SizeOf,
                    ast::SizeForm::AlignOf(_) => FormName::AlignOf,
                    ast::SizeForm::OffsetOf(..) => FormName::OffsetOf,
                };
                self.check_form(name, e, ex)
            }
            ast::ExprKind::Asm(asm) => self.check_asm(asm, e.span),
            ast::ExprKind::Unary(op, operand) => self.check_unary(*op, operand, e.span, ex),
            ast::ExprKind::Borrow(inner) => self.check_borrow(inner, e.span, ex),
            ast::ExprKind::Deref(inner) => {
                // `*r` is a narrowing path (S:1007): a fact on it types a read.
                let deref = self.check_deref(inner, e.span);
                self.narrow_read(deref, ex)
            }
            ast::ExprKind::VoidOp(inner) => {
                let value = self.check_expr(inner, Expect::None);
                let void = self.sema.tcx.common().void;
                self.mk_expr(void, e.span, ExprKind::VoidOp(Box::new(value)))
            }
            ast::ExprKind::Binary(op, a, b) => self.check_binary(*op, a, b, e.span, ex),
            ast::ExprKind::Logical(op, a, b) => self.check_logical(*op, a, b, e.span),
            ast::ExprKind::Coalesce(a, b) => self.check_coalesce(a, b, e.span, ex),
            ast::ExprKind::Ternary(c, a, b) => self.check_ternary(c, a, b, e.span, ex),
            ast::ExprKind::Cast(operand, ty) => self.check_cast(operand, ty, e.span),
            ast::ExprKind::Assign { op, target, value } => {
                self.check_assign(*op, target, value, e.span)
            }
            ast::ExprKind::IncDec {
                target,
                inc,
                prefix,
            } => self.check_incdec(target, *inc, *prefix, e.span),
            ast::ExprKind::Index(base, index) => self.check_index(base, index, e.span),
            ast::ExprKind::NonNull(inner) => self.check_non_null(inner, e.span),
            ast::ExprKind::Error => self.error_expr(e.span),
        };
        match ex {
            Expect::Coerce(to, site) => self.coerce(typed, to, site),
            Expect::None | Expect::Has(_) => typed,
        }
    }

    /// EN0410 at once for an operand whose type is still an unknown `Any` variable
    /// (S:733, S:813), the variable then bound to `Error`; whether it was one.
    fn unknown_operand(&mut self, e: &hir::Expr) -> bool {
        let t = self.shallow(e.ty);
        let t = match self.sema.tcx.kind(t) {
            TyKind::Ref(inner) => self.shallow(inner),
            _ => t,
        };
        if self.var_kind(t) != Some(VarKind::Any) {
            return false;
        }
        let what = format!("`{}`", self.snippet(e.span));
        self.report_uninferred(e.span, &what);
        let error = self.error_ty();
        self.unify(t, error);
        true
    }

    /// A template literal: any value in a hole (S:1180); a `string`.
    fn check_template(&mut self, parts: &[ast::TplPart], span: Span) -> hir::Expr {
        let parts = parts
            .iter()
            .map(|part| match part {
                ast::TplPart::Str(text) => TplPart::Text(self.sema.tcx.intern_str(text.as_str())),
                ast::TplPart::Expr(e) => {
                    let hole = self.check_expr(e, Expect::None);
                    TplPart::Hole(self.iface_rvalue(hole))
                }
            })
            .collect();
        let str_ty = self.sema.tcx.common().str;
        self.mk_expr(str_ty, span, ExprKind::Template(parts))
    }

    /// `null`, typed at the expected nullable (D11); with no expected type EN0410
    /// (S:734); at a coercion site of a type that is never `null`, EN0401.
    fn check_null(&mut self, span: Span, ex: Expect) -> hir::Expr {
        let Some(t) = ex.ty() else {
            self.report_uninferred(span, "`null`");
            return self.error_expr(span);
        };
        let t = self.shallow(t);
        if self.is_error(t) {
            return self.error_expr(span);
        }
        if matches!(self.sema.tcx.kind(t), TyKind::Nullable(_)) {
            return self.mk_expr(t, span, ExprKind::NullLit);
        }
        if self.var_kind(t).is_some() {
            self.report_uninferred(span, "`null`");
            return self.error_expr(span);
        }
        match ex {
            Expect::Coerce(..) => {
                let shown = self.ty_str(t);
                self.sema.emit(Diagnostic::new(
                    Code::EN0401,
                    format!("mismatched types: expected `{shown}`, found `null`"),
                    span,
                    format!("`{shown}` is never `null`"),
                ));
                self.error_expr(span)
            }
            _ => {
                let nullable = self.sema.tcx.mk_nullable(t);
                self.mk_expr(nullable, span, ExprKind::NullLit)
            }
        }
    }

    /// A bracket literal (S:735, S:803-823).
    pub(crate) fn check_array(
        &mut self,
        elems: &[ast::ArrayElem],
        span: Span,
        ex: Expect,
    ) -> hir::Expr {
        let expected = ex.ty().map(|t| {
            let t = self.shallow(t);
            match self.sema.tcx.kind(t) {
                TyKind::Nullable(inner) => self.shallow(inner),
                _ => t,
            }
        });
        let spread = elems
            .iter()
            .any(|e| matches!(e, ast::ArrayElem::Spread { .. }));
        let kind = expected.map(|t| self.sema.tcx.kind(t));
        match kind {
            Some(TyKind::Tuple(parts)) if !spread => {
                let parts = self.sema.tcx.list(parts);
                if parts.len() == elems.len() {
                    let items: Vec<hir::Expr> = elems
                        .iter()
                        .zip(parts.iter())
                        .map(|(e, &part)| match e {
                            ast::ArrayElem::Item(e) => {
                                self.check_expr(e, Expect::Coerce(part, Site::Element))
                            }
                            ast::ArrayElem::Spread { expr, .. } => self.error_expr(expr.span),
                        })
                        .collect();
                    let ty = expected.unwrap_or_else(|| self.error_ty());
                    return self.mk_expr(ty, span, ExprKind::TupleLit(items));
                }
                let items: Vec<hir::Expr> = elems
                    .iter()
                    .map(|e| match e {
                        ast::ArrayElem::Item(e) => self.check_expr(e, Expect::None),
                        ast::ArrayElem::Spread { expr, .. } => self.error_expr(expr.span),
                    })
                    .collect();
                let tys: Vec<Ty> = items.iter().map(|i| i.ty).collect();
                let ty = self.sema.tcx.mk_tuple(&tys);
                self.mk_expr(ty, span, ExprKind::TupleLit(items))
            }
            Some(TyKind::Fixed(elem, _)) if !spread => {
                let items: Vec<hir::Expr> = elems
                    .iter()
                    .filter_map(|e| match e {
                        ast::ArrayElem::Item(e) => {
                            Some(self.check_expr(e, Expect::Coerce(elem, Site::Element)))
                        }
                        ast::ArrayElem::Spread { .. } => None,
                    })
                    .collect();
                let ty = self.sema.tcx.mk_fixed(elem, items.len() as u64);
                self.mk_expr(ty, span, ExprKind::ArrayLit(items))
            }
            Some(TyKind::Array(elem)) => self.array_of(elems, elem, true, span),
            Some(TyKind::Fixed(elem, _)) => self.array_of(elems, elem, false, span),
            // An annotation already reported (it lowered to `Error`): the elements
            // are typed against `Error`, with no EN0410 after that report.
            Some(TyKind::Error) => {
                let error = self.error_ty();
                self.array_of(elems, error, true, span)
            }
            _ => self.inferred_array(elems, span),
        }
    }

    /// A growable array of `elem` (or, `coerce_items` false, one whose expected
    /// fixed type a spread can't meet: elements still typed as `elem`).
    fn array_of(
        &mut self,
        elems: &[ast::ArrayElem],
        elem: Ty,
        coerce_items: bool,
        span: Span,
    ) -> hir::Expr {
        let mut parts = Vec::new();
        let mut spread = false;
        for e in elems {
            match e {
                ast::ArrayElem::Item(e) => {
                    let expect = if coerce_items {
                        Expect::Coerce(elem, Site::Element)
                    } else {
                        Expect::Has(elem)
                    };
                    parts.push(ArrayPart::Item(self.check_expr(e, expect)));
                }
                ast::ArrayElem::Spread { dots, expr } => {
                    spread = true;
                    if let Some(part) = self.check_spread(*dots, expr, elem) {
                        parts.push(part);
                    }
                }
            }
        }
        self.build_array(parts, elem, spread, span)
    }

    /// The array `parts` make: `ArrayLit` with no spread, else `ArrayBuild`.
    fn build_array(
        &mut self,
        parts: Vec<ArrayPart>,
        elem: Ty,
        spread: bool,
        span: Span,
    ) -> hir::Expr {
        let ty = self.sema.tcx.mk_array(elem);
        if spread {
            return self.mk_expr(ty, span, ExprKind::ArrayBuild { elem, parts });
        }
        let items = parts
            .into_iter()
            .map(|p| match p {
                ArrayPart::Item(e) | ArrayPart::Spread(e, _) => e,
            })
            .collect();
        self.mk_expr(ty, span, ExprKind::ArrayLit(items))
    }

    /// A bracket literal with no expected type: its elements unify (`[1, "a"]` is
    /// EN0401 with a tuple help, S:735); `[]` is an array of a variable a later use
    /// may decide (S:733).
    fn inferred_array(&mut self, elems: &[ast::ArrayElem], span: Span) -> hir::Expr {
        let elem = self.new_var(VarKind::Any, span, format!("`{}`", self.snippet(span)));
        let mut parts = Vec::new();
        let mut spread = false;
        let mut first: Option<Ty> = None;
        let mut broken = false;
        for e in elems {
            match e {
                ast::ArrayElem::Item(item) => {
                    let hint = first.map_or(Expect::None, Expect::Has);
                    let value = self.check_expr(item, hint);
                    let t = self.shallow(value.ty);
                    broken |= self.is_error(t);
                    if !self.is_error(t) && self.sema.tcx.kind(t) != TyKind::Never {
                        if self.unify(elem, t) {
                            first.get_or_insert(t);
                        } else {
                            self.report_mixed_elements(&value, elem, span, elems);
                        }
                    }
                    parts.push(ArrayPart::Item(value));
                }
                ast::ArrayElem::Spread { dots, expr } => {
                    spread = true;
                    if let Some(part) = self.check_spread(*dots, expr, elem) {
                        parts.push(part);
                    }
                }
            }
        }
        // An element already reported, and nothing else to decide the type: the
        // array is of `Error`, with no EN0410 after that report.
        if broken && first.is_none() {
            let error = self.error_ty();
            let _ = self.unify(elem, error);
        }
        self.build_array(parts, elem, spread, span)
    }

    /// EN0401 for an element of another type than the first, with the help to
    /// annotate a tuple (S:735).
    fn report_mixed_elements(
        &mut self,
        value: &hir::Expr,
        elem: Ty,
        span: Span,
        elems: &[ast::ArrayElem],
    ) {
        let (se, sv) = (self.ty_str(elem), self.ty_str(value.ty));
        let mut diag = Diagnostic::new(
            Code::EN0401,
            format!("mismatched types: expected `{se}`, found `{sv}`"),
            value.span,
            format!("this is `{sv}`"),
        )
        .with_secondary(span, format!("the elements of this array are `{se}`"));
        let plain = elems.iter().all(|e| matches!(e, ast::ArrayElem::Item(_)));
        if plain {
            diag = diag.with_help(Help::text(
                "for values of different types, annotate a tuple type, as in `const x: [int, string] = [1, \"a\"];`",
            ));
        }
        self.sema.emit(diag);
    }

    /// One spread operand, unified with the literal's element type `elem` (A:890);
    /// a rejected one binds `elem` to `Error`, so nothing else reports on it.
    fn check_spread(&mut self, dots: Span, expr: &ast::Expr, elem: Ty) -> Option<ArrayPart> {
        let part = self.spread_part(dots, expr, elem);
        if part.is_none() {
            let error = self.error_ty();
            if self.var_kind(elem) == Some(VarKind::Any) {
                self.unify(elem, error);
            }
        }
        part
    }

    fn spread_part(&mut self, dots: Span, expr: &ast::Expr, elem: Ty) -> Option<ArrayPart> {
        let span = dots.to(expr.span);
        let mut value = self.check_expr(expr, Expect::None);
        if self.is_error(value.ty) {
            return None;
        }
        if self.unknown_operand(&value) {
            return None;
        }
        let t = self.shallow(value.ty);
        let (reference, inner) = match self.sema.tcx.kind(t) {
            TyKind::Ref(inner) => (true, self.shallow(inner)),
            _ => (false, t),
        };
        let (kind, source_elem) = match self.sema.tcx.kind(inner) {
            TyKind::Array(e) => (SpreadKind::Array, e),
            TyKind::Fixed(e, n) => (SpreadKind::Fixed(n), e),
            TyKind::Slice(e) => (SpreadKind::Slice, e),
            TyKind::Infer(_) if self.var_kind(inner) == Some(VarKind::Any) => {
                self.unknown_operand(&value);
                return None;
            }
            _ => {
                self.report_not_spreadable(span, expr, inner);
                return None;
            }
        };
        value.adjust.push(if reference {
            Adjust::Reborrow
        } else {
            Adjust::AutoBorrow
        });
        match kind {
            SpreadKind::Array => value.adjust.push(Adjust::ArrayToSlice),
            SpreadKind::Fixed(_) => value.adjust.push(Adjust::FixedToSlice),
            SpreadKind::Slice => {}
        }
        if !self.unify(source_elem, elem) {
            self.report_spread_mismatch(span, expr, source_elem, elem);
            return None;
        }
        self.deferred.push(super::Deferred::SpreadClone {
            span,
            elem: source_elem,
        });
        Some(ArrayPart::Spread(value, kind))
    }

    /// EN0438 `` `...` needs an array, found `T` ``, with `...*b` for a box.
    fn report_not_spreadable(&mut self, span: Span, expr: &ast::Expr, t: Ty) {
        let shown = self.ty_str(t);
        let mut diag = Diagnostic::new(
            Code::EN0438,
            format!("`...` needs an array, found `{shown}`"),
            span,
            format!("this is `{shown}`"),
        );
        if let TyKind::Boxed(inner) = self.sema.tcx.kind(t)
            && matches!(
                self.sema.tcx.kind(self.shallow(inner)),
                TyKind::Array(_) | TyKind::Fixed(..)
            )
        {
            let text = self.snippet(expr.span);
            diag = diag.with_help(Help::machine(
                format!("spread the array in the box: `...*{text}`"),
                vec![Edit::insert(expr.span.lo, "*")],
            ));
        }
        self.sema.emit(diag);
    }

    /// EN0401 for a spread whose elements are not the literal's (S:817-818).
    fn report_spread_mismatch(&mut self, span: Span, expr: &ast::Expr, from: Ty, elem: Ty) {
        let (sf, se) = (self.ty_str(from), self.ty_str(elem));
        let from_array = self.sema.tcx.mk_array(from);
        let elem_array = self.sema.tcx.mk_array(elem);
        let (sfa, sea) = (self.ty_str(from_array), self.ty_str(elem_array));
        let mut diag = Diagnostic::new(
            Code::EN0401,
            format!("mismatched types: expected `{sea}`, found `{sfa}`"),
            span,
            format!("the elements of `{}` are `{sf}`", self.snippet(expr.span)),
        );
        let resolved = self.resolve(elem);
        if let TyKind::Nullable(payload) = self.sema.tcx.kind(resolved)
            && self.can_unify(payload, from)
        {
            diag = diag
                .note("a spread keeps its elements' type; nothing wraps them in `| null`")
                .with_help(Help::text(format!(
                    "spread a converted copy: `...{}.map((x): {se} => x)`",
                    self.snippet(expr.span)
                )));
        }
        self.sema.emit(diag);
    }

    /// EN0438 when a spread's element type is not `Clone` once inference is done
    /// (S:815, G22).
    pub(crate) fn check_spread_clone(&mut self, span: Span, elem: Ty) {
        let elem = self.resolve(elem);
        let tcx = &*self.sema.tcx;
        if tcx.references_error(elem) || tcx.is_clone(elem, &self.env) {
            return;
        }
        let operand = self.snippet(span);
        let operand = operand.trim_start_matches("...").trim().to_owned();
        let shown = tcx.ty_string(elem);
        let label = format!("each element of `{operand}` would be cloned here");
        let ts = "JS spread copies references to the same objects. In Enrang a value has one owner, so `...` copies the elements too.";
        let diag = match tcx.kind(elem) {
            TyKind::Param(p) => {
                let param = tcx.param(p);
                let mut diag = Diagnostic::new(
                    Code::EN0438,
                    format!("`...` clones each element, and `{shown}` has no `Clone` bound"),
                    span,
                    label,
                );
                let user = param.implicit.is_none() && !param.span.is_dummy();
                if user {
                    diag = diag.with_secondary(param.span, format!("`{shown}` is declared here"));
                }
                diag = diag.from_typescript(ts);
                if user && param.bounds.is_empty() {
                    diag = diag.with_help(Help::machine(
                        "require `Clone`",
                        vec![Edit::insert(param.span.hi, " extends Clone")],
                    ));
                } else if user {
                    diag = diag.with_help(Help::text(format!("add `Clone` to `{shown}`'s bounds")));
                }
                diag
            }
            _ => Diagnostic::new(
                Code::EN0438,
                format!("`...` clones each element, and `{shown}` is not `Clone`"),
                span,
                label,
            )
            .from_typescript(ts),
        };
        self.sema.emit(diag);
    }

    /// `[e; n]`: a `T[n]`, `n` a constant (4F's `eval_len`).
    fn check_repeat(
        &mut self,
        value: &ast::Expr,
        count: &ast::Expr,
        span: Span,
        ex: Expect,
    ) -> hir::Expr {
        let elem_expect = ex
            .ty()
            .map(|t| self.shallow(t))
            .and_then(|t| match self.sema.tcx.kind(t) {
                TyKind::Fixed(elem, _) | TyKind::Array(elem) => {
                    Some(Expect::Coerce(elem, Site::Element))
                }
                _ => None,
            })
            .unwrap_or(Expect::None);
        let item = self.check_expr(value, elem_expect);
        let elem = match elem_expect {
            Expect::Coerce(t, _) => t,
            _ => item.ty,
        };
        let saved = self.shadow_names(consteval::idents_of(count));
        let n = consteval::eval_len(self.sema, self.at, count);
        self.sema.consts.shadowing = saved;
        let Some(n) = n else {
            return self.error_expr(span);
        };
        let ty = self.sema.tcx.mk_fixed(elem, n);
        self.mk_expr(ty, span, ExprKind::Repeat(Box::new(item), n))
    }

    /// `c ? a : b`: with an expected type each branch coerces (EN0401); without,
    /// they unify (EN0432, S:1136).
    fn check_ternary(
        &mut self,
        c: &ast::Expr,
        a: &ast::Expr,
        b: &ast::Expr,
        span: Span,
        ex: Expect,
    ) -> hir::Expr {
        let cond = self.check_cond(c);
        let (when_true, when_false) = self.cond_facts(&cond);
        let branch = match ex {
            Expect::Coerce(t, _) => Expect::Coerce(t, Site::Branch),
            other => other,
        };
        self.flow = when_true;
        let mut then_ = self.check_expr(a, branch);
        let after_then = std::mem::replace(&mut self.flow, when_false);
        let mut else_ = self.check_expr(b, branch);
        let after_else = std::mem::take(&mut self.flow);
        self.join(vec![after_then, after_else]);
        let ty = match branch {
            Expect::Coerce(t, _) => t,
            _ => self.unify_results(&mut [&mut then_, &mut else_]),
        };
        self.mk_expr(
            ty,
            span,
            ExprKind::Ternary(Box::new(cond), Box::new(then_), Box::new(else_)),
        )
    }

    /// The common type of branch or arm results with no expected type: `never` ones
    /// skipped; a string literal among results of type `&string` (or `&string |
    /// null`) takes its static descriptor (C13, S:962), so `c ? name : "none"` is a
    /// `&string`; EN0432 at the first that differs.
    fn unify_results(&mut self, results: &mut [&mut hir::Expr]) -> Ty {
        let never = self.sema.tcx.common().never;
        let target = self.str_ref_result(results);
        let mut tys = Vec::with_capacity(results.len());
        for r in results.iter_mut() {
            let mut t = self.shallow(r.ty);
            if let Some(target) = target {
                let (e, descriptor) = self.str_literal_at((**r).clone(), target);
                **r = e;
                if descriptor {
                    t = target;
                }
            }
            tys.push(t);
        }
        let mut common: Option<Ty> = None;
        for (r, t) in results.iter().zip(tys) {
            if self.is_error(t) {
                return self.error_ty();
            }
            if self.sema.tcx.kind(t) == TyKind::Never {
                continue;
            }
            match common {
                None => common = Some(t),
                Some(c) => {
                    if !self.unify(c, t) {
                        let (sa, sb) = (self.ty_str(c), self.ty_str(t));
                        self.sema.emit(
                            Diagnostic::new(
                                Code::EN0432,
                                format!("the branches have different types: `{sa}` and `{sb}`"),
                                r.span,
                                format!("this is `{sb}`"),
                            )
                            .with_help(Help::text(
                                "annotate the expected type, or make every branch give one type",
                            )),
                        );
                        return self.error_ty();
                    }
                }
            }
        }
        common.map_or(never, |c| self.shallow(c))
    }

    /// The type a string literal among `results` takes: the first result's of
    /// type `&string` or `&string | null`, when some result is a string literal.
    fn str_ref_result(&self, results: &[&mut hir::Expr]) -> Option<Ty> {
        let literal = |e: &hir::Expr| {
            matches!(e.kind, ExprKind::Const(ConstValue::Str(_))) && e.adjust.is_empty()
        };
        if !results.iter().any(|r| literal(r)) {
            return None;
        }
        let tcx = &*self.sema.tcx;
        let str_ref = tcx.mk_ref(tcx.common().str);
        let nullable = tcx.mk_nullable(str_ref);
        results
            .iter()
            .map(|r| self.resolve(r.ty))
            .find(|&t| t == str_ref || t == nullable)
    }

    /// `a[i]` (S:720, S:602).
    fn check_index(&mut self, base: &ast::Expr, index: &ast::Expr, span: Span) -> hir::Expr {
        let base = self.check_expr(base, Expect::None);
        if self.is_error(base.ty) || self.unknown_operand(&base) {
            let _ = self.check_expr(index, Expect::None);
            return self.error_expr(span);
        }
        let t = self.shallow(base.ty);
        let inner = match self.sema.tcx.kind(t) {
            TyKind::Ref(inner) => self.shallow(inner),
            _ => t,
        };
        // One `&` is stripped as a `Deref` node, as a member's base is (plan d.8).
        let base = match self.sema.tcx.kind(t) {
            TyKind::Ref(_) if !matches!(self.sema.tcx.kind(inner), TyKind::Error) => {
                let span = base.span;
                self.mk_expr(inner, span, ExprKind::Deref(Box::new(base)))
            }
            _ => base,
        };
        match self.sema.tcx.kind(inner) {
            TyKind::Array(elem) | TyKind::Fixed(elem, _) | TyKind::Slice(elem) => {
                let idx = self.check_expr(index, Expect::None);
                let it = self.shallow(idx.ty);
                if self.var_kind(it) == Some(VarKind::Int) {
                    self.note_index(it);
                    // A later use may make it a float: checked at the end (EN0405).
                    self.defer_num_use(idx.span, it, NumNeed::Index);
                } else if !self.is_error(it) && !matches!(self.sema.tcx.kind(it), TyKind::Int(_)) {
                    let shown = self.ty_str(it);
                    self.sema.emit(Diagnostic::new(
                        Code::EN0405,
                        format!("an index must be an integer, found `{shown}`"),
                        idx.span,
                        format!("this is `{shown}`"),
                    ));
                    return self.error_expr(span);
                }
                self.mk_expr(elem, span, ExprKind::Index(Box::new(base), Box::new(idx)))
            }
            TyKind::Tuple(parts) => {
                let parts = self.sema.tcx.list(parts);
                let ast::ExprKind::Int { value, .. } = strip_parens(index).kind else {
                    self.sema.emit(Diagnostic::new(
                        Code::EN0452,
                        "a tuple index must be a constant",
                        index.span,
                        "the parts of a tuple may differ in type",
                    ));
                    return self.error_expr(span);
                };
                match usize::try_from(value).ok().filter(|&i| i < parts.len()) {
                    Some(i) => {
                        let ty = parts[i];
                        self.mk_expr(
                            ty,
                            span,
                            ExprKind::Field(Box::new(base), FieldIdx(i as u32)),
                        )
                    }
                    None => {
                        let shown = self.ty_str(inner);
                        let count = parts.len();
                        let noun = if count == 1 { "element" } else { "elements" };
                        self.sema.emit(Diagnostic::new(
                            Code::EN0452,
                            format!("`{shown}` has no element {value}"),
                            index.span,
                            format!("it has {count} {noun}"),
                        ));
                        self.error_expr(span)
                    }
                }
            }
            _ => {
                let _ = self.check_expr(index, Expect::None);
                let shown = self.ty_str(inner);
                self.sema.emit(Diagnostic::new(
                    Code::EN0420,
                    format!("`{shown}` can't be indexed"),
                    base.span,
                    format!("this is `{shown}`"),
                ));
                self.error_expr(span)
            }
        }
    }

    /// `&e` (S:684, S:735): a bracket literal at `&Slice<T>` or `&T[N]` is a `T[N]`
    /// that C18 then converts; `&r` with `r: &T` is `r` itself.
    fn check_borrow(&mut self, inner: &ast::Expr, span: Span, ex: Expect) -> hir::Expr {
        let expected = ex.ty().map(|t| {
            let t = self.shallow(t);
            match self.sema.tcx.kind(t) {
                TyKind::Nullable(payload) => self.shallow(payload),
                _ => t,
            }
        });
        let pointee = expected.and_then(|t| match self.sema.tcx.kind(t) {
            TyKind::Ref(p) => Some(self.shallow(p)),
            _ => None,
        });
        let literal = strip_parens(inner);
        if let (ast::ExprKind::Array(elems), Some(p)) = (&literal.kind, pointee)
            && elems.iter().all(|e| matches!(e, ast::ArrayElem::Item(_)))
        {
            let fixed = match self.sema.tcx.kind(p) {
                TyKind::Slice(elem) => Some(self.sema.tcx.mk_fixed(elem, elems.len() as u64)),
                TyKind::Fixed(..) => Some(p),
                _ => None,
            };
            if let Some(fixed) = fixed {
                let value = self.check_expr(literal, Expect::Has(fixed));
                let ty = self.sema.tcx.mk_ref(value.ty);
                return self.mk_expr(ty, span, ExprKind::Borrow(Box::new(value)));
            }
        }
        let hint = pointee.map_or(Expect::None, Expect::Has);
        let value = self.check_expr(inner, hint);
        // A by-value interface temporary, as `&b.unbox()` borrows, has no known
        // size either (EN1006, T:862 F7).
        let value = self.iface_rvalue(value);
        if self.is_error(value.ty) {
            return self.error_expr(span);
        }
        let shallow = self.shallow(value.ty);
        if matches!(self.sema.tcx.kind(shallow), TyKind::Ref(_)) {
            return value;
        }
        // `&r` with `r: &T | null` would be `&(&T | null)`, which R2 forbids
        // however it is reached, written or inferred (S:849, EN0702).
        if let TyKind::Nullable(payload) = self.sema.tcx.kind(shallow)
            && matches!(self.sema.tcx.kind(self.shallow(payload)), TyKind::Ref(_))
        {
            let shown = self.ty_str(shallow);
            self.sema.emit(Diagnostic::new(
                Code::EN0702,
                "a reference can't point to a reference",
                span,
                format!("this points to `{shown}`"),
            ));
            return self.error_expr(span);
        }
        let ty = self.sema.tcx.mk_ref(value.ty);
        self.mk_expr(ty, span, ExprKind::Borrow(Box::new(value)))
    }

    /// `*e` on a reference, a raw pointer or a `Box`.
    fn check_deref(&mut self, inner: &ast::Expr, span: Span) -> hir::Expr {
        let value = self.check_expr(inner, Expect::None);
        if self.is_error(value.ty) || self.unknown_operand(&value) {
            return self.error_expr(span);
        }
        let t = self.shallow(value.ty);
        match self.sema.tcx.kind(t) {
            TyKind::Ref(p) | TyKind::Raw(p) | TyKind::Boxed(p) => {
                self.mk_expr(p, span, ExprKind::Deref(Box::new(value)))
            }
            _ => {
                let shown = self.ty_str(t);
                self.sema.emit(Diagnostic::new(
                    Code::EN0420,
                    format!("`*` needs a reference, a raw pointer or a `Box`, found `{shown}`"),
                    span,
                    format!("this is `{shown}`"),
                ));
                self.error_expr(span)
            }
        }
    }

    /// `e!`: the payload of a `T | null`.
    fn check_non_null(&mut self, inner: &ast::Expr, span: Span) -> hir::Expr {
        let value = self.check_place(inner, Expect::None);
        if self.is_error(value.ty) || self.unknown_operand(&value) {
            return self.error_expr(span);
        }
        let t = self.shallow(value.ty);
        let payload = match self.sema.tcx.kind(t) {
            TyKind::Nullable(p) => Some(self.shallow(p)),
            TyKind::Ref(r) => match self.sema.tcx.kind(self.shallow(r)) {
                TyKind::Nullable(p) => Some(self.sema.tcx.mk_ref(p)),
                _ => None,
            },
            _ => None,
        };
        match payload {
            Some(p) => self.mk_expr(p, span, ExprKind::NonNull(Box::new(value))),
            None => {
                let shown = self.ty_str(t);
                self.sema.emit(Diagnostic::new(
                    Code::EN0420,
                    format!("`!` needs a `T | null`, found `{shown}`"),
                    span,
                    format!("this is `{shown}`, which is never `null`"),
                ));
                self.error_expr(span)
            }
        }
    }

    /// An assignment; a compound one keeps its operator's rules and is no coercion
    /// site (S:656); a value into a reference variable is EN0422 (S:775).
    fn check_assign(
        &mut self,
        op: ast::AssignOp,
        target_ast: &ast::Expr,
        value_ast: &ast::Expr,
        span: Span,
    ) -> hir::Expr {
        if op == ast::AssignOp::Assign
            && matches!(
                strip_parens(target_ast).kind,
                ast::ExprKind::Array(_) | ast::ExprKind::ObjectLit(_)
            )
        {
            return self.check_destructure_assign(strip_parens(target_ast), value_ast, span);
        }
        // `=` stores into the place at its declared type; a compound assignment
        // reads and writes the narrowed payload (4B).
        let target = match op {
            ast::AssignOp::Assign => self.check_place(target_ast, Expect::None),
            _ => self.check_expr(target_ast, Expect::None),
        };
        if self.is_error(target.ty) {
            let _ = self.check_expr(value_ast, Expect::None);
            return self.error_expr(span);
        }
        let tt = self.shallow(target.ty);
        let ref_local = matches!(target.kind, ExprKind::Local(_))
            && matches!(self.sema.tcx.kind(tt), TyKind::Ref(_));
        // A nullable reference variable is one too for `=` (S:656): it takes a
        // reference, a string literal or `null`, and a value is EN0422.
        let nullable_ref_local = matches!(target.kind, ExprKind::Local(_))
            && matches!(self.sema.tcx.kind(tt), TyKind::Nullable(inner)
                if matches!(self.sema.tcx.kind(self.shallow(inner)), TyKind::Ref(_)));
        let binop = compound_op(op);
        let value = match binop {
            Some(binop) => {
                if ref_local {
                    let value = self.check_expr(value_ast, Expect::None);
                    self.report_ref_assign(&target, &value, op, span);
                    return self.error_expr(span);
                }
                let value = self.check_expr(value_ast, Expect::Has(self.operand_ty(tt)));
                let value = self.read_narrowed(value);
                if !self.check_compound(binop, &target, &value, span) {
                    return self.error_expr(span);
                }
                value
            }
            None if ref_local || nullable_ref_local => {
                let value = self.check_expr(value_ast, Expect::Has(tt));
                let vt = self.shallow(value.ty);
                let repoints = self.is_error(vt)
                    || matches!(
                        self.sema.tcx.kind(vt),
                        TyKind::Ref(_) | TyKind::Nullable(_) | TyKind::Never
                    )
                    || matches!(value.kind, ExprKind::Const(ConstValue::Str(_)));
                if !repoints {
                    self.report_ref_assign(&target, &value, op, span);
                    return self.error_expr(span);
                }
                self.coerce(value, tt, Site::Assign)
            }
            None => self.check_expr(value_ast, Expect::Coerce(tt, Site::Assign)),
        };
        // O6: the right side, which `=` copies or moves (a compound assignment's is
        // an operand, only read), then the place's narrowed use, then the store
        // (A:898).
        if binop.is_none() {
            self.record_ref(&value, RecordKind::Copy);
        }
        if binop.is_none() || self.sema.tcx.is_copy(self.resolve(tt), &self.env) {
            self.recheck_place(&target, value.span);
        }
        self.kill_write(&target);
        self.mk_expr(
            tt,
            span,
            ExprKind::Assign {
                op: binop,
                target: Box::new(target),
                value: Box::new(value),
            },
        )
    }

    /// EN0422 `` `r` is a reference: write through it with `*r` ``, with fix-its to
    /// `*r` and, for a plain assignment, to `&` (S:656, S:775).
    fn report_ref_assign(
        &mut self,
        target: &hir::Expr,
        value: &hir::Expr,
        op: ast::AssignOp,
        span: Span,
    ) {
        let name = self.snippet(target.span);
        let nullable = matches!(
            self.sema.tcx.kind(self.shallow(target.ty)),
            TyKind::Nullable(_)
        );
        let through = match nullable {
            true => format!("write through it once it is not `null`: `*{name}`"),
            false => format!("write through it: `*{name}`"),
        };
        let mut diag = Diagnostic::new(
            Code::EN0422,
            format!("`{name}` is a reference: write through it with `*{name}`"),
            span,
            format!("`{name}` is `{}`", self.ty_str(target.ty)),
        )
        .with_help(Help::suggest(
            through,
            vec![Edit::insert(target.span.lo, "*")],
        ));
        if op == ast::AssignOp::Assign {
            let text = self.snippet(value.span);
            diag = diag.with_help(Help::suggest(
                format!("or point it at another place: `&{text}`"),
                vec![Edit::insert(value.span.lo, "&")],
            ));
        }
        self.sema.emit(diag);
    }

    /// The operator rules of a compound assignment `t op= v`: `+=` appends a string;
    /// arithmetic and bitwise operators need one numeric type, shifts integers.
    fn check_compound(
        &mut self,
        op: ast::BinOp,
        target: &hir::Expr,
        value: &hir::Expr,
        span: Span,
    ) -> bool {
        let (tt, tv) = (self.operand_ty(target.ty), self.operand_ty(value.ty));
        if self.is_error(tt) || self.is_error(tv) {
            return true;
        }
        let tcx = &*self.sema.tcx;
        if op == ast::BinOp::Add && tcx.kind(tt) == TyKind::Str && tcx.kind(tv) == TyKind::Str {
            return true;
        }
        if op == ast::BinOp::Add && (tcx.kind(tt) == TyKind::Str || tcx.kind(tv) == TyKind::Str) {
            // `+=` appends to a string (S:1191): the other operand is the bad one,
            // as binary `+` reports it.
            let (bad, bad_ty) = match tcx.kind(tt) == TyKind::Str {
                true => (value, tv),
                false => (target, tt),
            };
            let shown = self.ty_str(bad_ty);
            self.sema.emit(Diagnostic::new(
                Code::EN0420,
                format!(
                    "`+=` needs two numbers or two strings, found `{}` and `{}`",
                    self.ty_str(tt),
                    self.ty_str(tv)
                ),
                bad.span,
                format!("this is `{shown}`"),
            ));
            return false;
        }
        let numeric = |me: &Self, t: Ty| {
            matches!(me.sema.tcx.kind(t), TyKind::Int(_) | TyKind::Float(_))
                || matches!(me.var_kind(t), Some(VarKind::Int | VarKind::Float))
        };
        let integer = |me: &Self, t: Ty| {
            matches!(me.sema.tcx.kind(t), TyKind::Int(_)) || me.var_kind(t) == Some(VarKind::Int)
        };
        let bitwise = matches!(
            op,
            ast::BinOp::BitAnd
                | ast::BinOp::BitOr
                | ast::BinOp::BitXor
                | ast::BinOp::Shl
                | ast::BinOp::Shr
        );
        for (e, t) in [(target, tt), (value, tv)] {
            let ok = if bitwise {
                integer(self, t)
            } else {
                numeric(self, t)
            };
            if !ok {
                let shown = self.ty_str(t);
                let (code, message) = if bitwise {
                    (
                        Code::EN0403,
                        format!("`{}=` needs integers, found `{shown}`", op.as_str()),
                    )
                } else {
                    (
                        Code::EN0420,
                        format!("`{}=` needs numbers, found `{shown}`", op.as_str()),
                    )
                };
                self.sema.emit(Diagnostic::new(
                    code,
                    message,
                    e.span,
                    format!("this is `{shown}`"),
                ));
                return false;
            }
        }
        if bitwise {
            // A variable a later use may make a float: checked at the end (EN0403).
            self.defer_num_use(target.span, tt, NumNeed::Integer(op.as_str()));
            if matches!(op, ast::BinOp::Shl | ast::BinOp::Shr) {
                self.defer_num_use(value.span, tv, NumNeed::Integer(op.as_str()));
            }
        }
        if matches!(op, ast::BinOp::Shl | ast::BinOp::Shr) {
            return true;
        }
        if self.unify(tt, tv) {
            // `x /= 2` truncates as `x / 2` does (EN0430, S:688), when the target's
            // type came from the `int` default.
            let ty = self.shallow(tt);
            if op == ast::BinOp::Div && self.var_kind(ty) == Some(VarKind::Int) {
                self.int_divisions.push(super::ops::IntDivision {
                    span,
                    ty,
                    literals: None,
                    literal_operands: false,
                    values: None,
                });
            }
            return true;
        }
        let (st, sv) = (self.ty_str(tt), self.ty_str(tv));
        let display_t = super::infer::display_in(self.sema.tcx, &self.infer, tt);
        let display_v = super::infer::display_in(self.sema.tcx, &self.infer, tv);
        let mut diag = Diagnostic::new(
            Code::EN0402,
            match op {
                ast::BinOp::Add => format!("cannot add `{sv}` to `{st}`"),
                ast::BinOp::Sub => format!("cannot subtract `{sv}` from `{st}`"),
                ast::BinOp::Mul => format!("cannot multiply `{st}` by `{sv}`"),
                ast::BinOp::Div => format!("cannot divide `{st}` by `{sv}`"),
                ast::BinOp::Rem => format!("cannot take the remainder of `{st}` divided by `{sv}`"),
                other => format!("cannot apply `{}` to `{st}` and `{sv}`", other.as_str()),
            },
            span,
            format!("`{st}` and `{sv}` are different types"),
        );
        if super::ops::widens(self.sema.tcx, display_v, display_t) {
            let text = self.snippet(value.span);
            diag = diag.with_help(Help::machine(
                format!("convert it, which never fails: `({text} as {st})`"),
                vec![
                    Edit::insert(value.span.lo, "("),
                    Edit::insert(value.span.hi, format!(" as {st})")),
                ],
            ));
        }
        self.sema.emit(diag);
        false
    }

    /// `x++`, `--x`: a number; on a reference variable EN0422.
    fn check_incdec(
        &mut self,
        target: &ast::Expr,
        inc: bool,
        prefix: bool,
        span: Span,
    ) -> hir::Expr {
        let place = self.check_expr(target, Expect::None);
        if self.is_error(place.ty) {
            return self.error_expr(span);
        }
        let t = self.shallow(place.ty);
        let op = if inc { "++" } else { "--" };
        if matches!(place.kind, ExprKind::Local(_))
            && matches!(self.sema.tcx.kind(t), TyKind::Ref(_))
        {
            let name = self.snippet(place.span);
            self.sema.emit(
                Diagnostic::new(
                    Code::EN0422,
                    format!("`{name}` is a reference: write through it with `*{name}`"),
                    span,
                    format!("`{name}` is `{}`", self.ty_str(t)),
                )
                .with_help(Help::machine(
                    format!("write through it: `(*{name}){op}`"),
                    vec![Edit::replace(place.span, format!("(*{name})"))],
                )),
            );
            return self.error_expr(span);
        }
        let numeric = matches!(self.sema.tcx.kind(t), TyKind::Int(_) | TyKind::Float(_))
            || matches!(self.var_kind(t), Some(VarKind::Int | VarKind::Float));
        if !numeric {
            let shown = self.ty_str(t);
            self.sema.emit(Diagnostic::new(
                Code::EN0420,
                format!("`{op}` needs a number, found `{shown}`"),
                span,
                format!("this is `{shown}`"),
            ));
            return self.error_expr(span);
        }
        self.kill_write(&place);
        self.mk_expr(
            t,
            span,
            ExprKind::IncDec {
                target: Box::new(place),
                inc,
                prefix,
            },
        )
    }

    /// `asm(...)`: operands typed, nothing else (A:1253; EN0801 is 4E's).
    fn check_asm(&mut self, asm: &ast::AsmExpr, span: Span) -> hir::Expr {
        let template = match &strip_parens(&asm.template).kind {
            ast::ExprKind::Str(s) | ast::ExprKind::RawTemplate(s) => *s,
            ast::ExprKind::Template(parts) => {
                let text: String = parts
                    .iter()
                    .filter_map(|p| match p {
                        ast::TplPart::Str(s) => Some(s.as_str().to_owned()),
                        ast::TplPart::Expr(_) => None,
                    })
                    .collect();
                intern(&text)
            }
            _ => intern(""),
        };
        let mut ins = Vec::new();
        let mut outs = Vec::new();
        let mut clobbers = Vec::new();
        for option in asm.options.iter().flatten() {
            match &option.kind {
                ast::AsmOptionKind::In(bindings) => {
                    for b in bindings {
                        let value = match &b.value {
                            Some(v) => self.check_expr(v, Expect::None),
                            None => self.reg_local(b.reg),
                        };
                        ins.push((b.reg.name, value));
                    }
                }
                ast::AsmOptionKind::Out(bindings) => {
                    for b in bindings {
                        let value = match &b.value {
                            Some(v) => Some(self.check_expr(v, Expect::None)),
                            None => Some(self.reg_local(b.reg)),
                        };
                        outs.push((b.reg.name, value));
                    }
                }
                ast::AsmOptionKind::Clobbers(names) => {
                    clobbers.extend(names.iter().map(|n| n.value));
                }
            }
        }
        let void = self.sema.tcx.common().void;
        self.mk_expr(
            void,
            span,
            ExprKind::Asm(Box::new(hir::HirAsm {
                template,
                ins,
                outs,
                clobbers,
                span,
            })),
        )
    }

    /// The local a register shorthand `{ edx }` names.
    fn reg_local(&mut self, reg: ast::Ident) -> hir::Expr {
        match self.scopes.lookup(reg.name) {
            Some(local) => {
                let ty = self.locals[local].ty;
                self.mk_expr(ty, reg.span, ExprKind::Local(local))
            }
            None => self.error_expr(reg.span),
        }
    }

    /// A `match` (S:1132-1136, plan d.5): the subject typed with no expected type;
    /// arm values against it; arm results coerced to an expected type, else unified
    /// (EN0432), or, for a `match` statement, left as they are.
    pub(crate) fn check_match(
        &mut self,
        subject: &ast::Expr,
        arms: &[ast::MatchArm],
        span: Span,
        ex: Expect,
        statement: bool,
    ) -> hir::Expr {
        let conditions = matches!(strip_parens(subject).kind, ast::ExprKind::Bool(true));
        let subject_e = self.check_expr(subject, Expect::None);
        let level = MatchLevel::of(self, subject_e.ty);
        let result = match ex {
            Expect::Coerce(t, _) => Expect::Coerce(t, Site::Branch),
            other => other,
        };
        let reachable_before = self.reachable;
        let mut all_diverge = !arms.is_empty();
        let mut out = Vec::new();
        // Each arm's result, when the `match` gives a value: its expression, or a
        // `void` marker for a block that ends.
        let mut markers: Vec<Option<hir::Expr>> = Vec::new();
        let mut expr_results: Vec<bool> = Vec::new();
        // Each arm starts from `entry`; the states that reach the end join (4B).
        let mut entry = self.flow.clone();
        let mut exits = Vec::new();
        for arm in arms {
            self.flow = entry.clone();
            let mut values = Vec::new();
            let mut value_spans = Vec::new();
            for v in &arm.values {
                value_spans.push(arm_value_span(v));
                let value = self.arm_value(v, &subject_e, &level, conditions);
                values.push(value);
            }
            // One case narrows the subject in the arm and its guard (S:1133); one
            // condition under `match (true)`, and the guard, give their facts.
            match values.as_slice() {
                [ArmValue::Case(c)] => {
                    let _ = self.enter_arm(&subject_e, Fact::Case(*c));
                }
                [ArmValue::Cond(c)] => (self.flow, _) = self.cond_facts(c),
                _ => {}
            }
            let guard = arm.guard.as_ref().map(|g| self.check_cond(g));
            // A later arm runs only after this arm's values and guard were
            // evaluated and failed, so the kills they made reach it (S:742).
            let evaluated = self.flow.clone();
            if let Some(g) = &guard {
                (self.flow, _) = self.cond_facts(g);
            }
            self.reachable = true;
            let mut marker = None;
            let mut expr_result = false;
            let body = match &arm.body {
                ast::ArmBody::Expr(e) => {
                    let expect = if statement { Expect::None } else { result };
                    let value = self.check_expr(e, expect);
                    if self.sema.tcx.kind(self.shallow(value.ty)) == TyKind::Never {
                        self.reachable = false;
                    }
                    expr_result = !statement;
                    ArmBody::Expr(value)
                }
                ast::ArmBody::Block(b) => {
                    let block = self.check_block(b);
                    if !statement && self.reachable {
                        let void = self.sema.tcx.common().void;
                        let m = self.mk_expr(void, b.span, ExprKind::Never);
                        marker = Some(match result {
                            Expect::Coerce(t, site) => self.coerce(m, t, site),
                            _ => m,
                        });
                    }
                    ArmBody::Block(block)
                }
                ast::ArmBody::Return(e) => {
                    let kind = self.check_return(e.as_ref(), arm.span);
                    self.reachable = false;
                    match kind {
                        StmtKind::Return(value) => ArmBody::Return(value),
                        _ => ArmBody::Return(None),
                    }
                }
                ast::ArmBody::Break(label) => {
                    let id = self.jump_target(label.as_ref());
                    self.broken.insert(id);
                    self.record_jump(id, true);
                    self.reachable = false;
                    ArmBody::Break(id)
                }
                ast::ArmBody::Continue(label) => {
                    let id = self.jump_target(label.as_ref());
                    self.continued.insert(id);
                    self.record_jump(id, false);
                    self.reachable = false;
                    ArmBody::Continue(id)
                }
            };
            all_diverge &= !self.reachable;
            markers.push(marker);
            expr_results.push(expr_result);
            if self.reachable {
                exits.push(self.flow.clone());
            }
            entry = self.intersect(vec![entry, evaluated]);
            // After an unguarded `null` arm the subject is not `null` (S:1135).
            if arm.guard.is_none() && values.iter().any(|v| matches!(v, ArmValue::Null)) {
                self.flow = entry;
                self.null_arm(&subject_e);
                entry = self.flow.clone();
            }
            out.push(hir::Arm {
                values,
                guard,
                body,
                span: arm.span,
                value_spans,
            });
        }
        match exits.is_empty() {
            true => self.flow = entry,
            false => self.join(exits),
        }
        self.reachable = reachable_before && !all_diverge;
        let never = self.sema.tcx.common().never;
        let ty = if statement {
            if all_diverge {
                never
            } else {
                self.sema.tcx.common().void
            }
        } else {
            match result {
                Expect::Coerce(t, _) if !all_diverge => t,
                _ if all_diverge => never,
                _ => {
                    let mut refs: Vec<&mut hir::Expr> = Vec::new();
                    for ((arm, marker), &is_result) in
                        out.iter_mut().zip(markers.iter_mut()).zip(&expr_results)
                    {
                        if let Some(m) = marker {
                            refs.push(m);
                        } else if is_result && let ArmBody::Expr(v) = &mut arm.body {
                            refs.push(v);
                        }
                    }
                    self.unify_results(&mut refs)
                }
            }
        };
        self.mk_expr(
            ty,
            span,
            ExprKind::Match {
                subject: Box::new(subject_e),
                arms: out,
            },
        )
    }

    /// The loop a `break` or `continue` leaves: the labelled one, or the innermost
    /// (phase 1 reported a jump outside any loop or to an unknown label).
    pub(crate) fn jump_target(&self, label: Option<&ast::Ident>) -> LoopId {
        match label {
            Some(l) => self.scopes.label(l.name),
            None => self.loops.last().copied(),
        }
        .unwrap_or(LoopId(0))
    }

    /// A `toMatchPattern` argument, an arm value against `actual` (plan d.17).
    pub(crate) fn expect_arm(&mut self, v: &ast::ArmValue, actual: &hir::Expr) -> ArmValue {
        let level = MatchLevel::of(self, actual.ty);
        self.arm_value(v, actual, &level, false)
    }

    /// One arm value against the subject (S:1132-1133).
    fn arm_value(
        &mut self,
        v: &ast::ArmValue,
        subject: &hir::Expr,
        level: &MatchLevel,
        conditions: bool,
    ) -> ArmValue {
        let rejected = ArmValue::Const(ConstValue::Void);
        if level.error {
            return rejected;
        }
        match v {
            ast::ArmValue::Value(e) if conditions => ArmValue::Cond(self.check_cond(e)),
            ast::ArmValue::Case(path) if conditions => match path_expr(path) {
                Some(e) => ArmValue::Cond(self.check_cond(&e)),
                None => rejected,
            },
            ast::ArmValue::Value(e) => self.literal_arm(e, level).unwrap_or(rejected),
            ast::ArmValue::Null(span) => {
                if level.nullable {
                    ArmValue::Null
                } else {
                    self.report_arm_mismatch("`null`", *span, level);
                    rejected
                }
            }
            ast::ArmValue::Ok(span) | ast::ArmValue::Err(span) => {
                let is_ok = matches!(v, ast::ArmValue::Ok(_));
                match level.adt {
                    Some(adt) if self.sema.tcx.is_lang_adt(adt, LangItem::Result) => {
                        ArmValue::Case(VariantIdx(if is_ok { 0 } else { 1 }))
                    }
                    _ => {
                        let word = if is_ok { "`Ok`" } else { "`Err`" };
                        self.report_arm_mismatch(word, *span, level);
                        rejected
                    }
                }
            }
            ast::ArmValue::Case(path) => self.case_arm(path, subject, level).unwrap_or(rejected),
            ast::ArmValue::Range(a, b) => self.range_arm(a, b, level).unwrap_or(rejected),
        }
    }

    /// A literal arm value: a number (kept as a `Cond` until its type settles), a
    /// string (a case of a string-literal union), or a boolean.
    fn literal_arm(&mut self, e: &ast::Expr, level: &MatchLevel) -> Option<ArmValue> {
        let e = strip_parens(e);
        let base = level.base;
        let tcx = &*self.sema.tcx;
        match &e.kind {
            ast::ExprKind::Int { .. } | ast::ExprKind::Float(_) | ast::ExprKind::Unary(..) => {
                let numeric = matches!(tcx.kind(base), TyKind::Int(_) | TyKind::Float(_))
                    || matches!(self.var_kind(base), Some(VarKind::Int | VarKind::Float));
                let literal = match &e.kind {
                    ast::ExprKind::Unary(ast::UnOp::Neg, inner) => {
                        self.negative_literal(inner, e.span, Expect::Has(base))
                    }
                    ast::ExprKind::Unary(..) => None,
                    _ => Some(self.check_literal(e, Expect::Has(base))),
                };
                let Some(literal) = literal else {
                    self.report_not_arm_value(e.span, level);
                    return None;
                };
                if !numeric || !self.unify(literal.ty, base) {
                    let text = format!("`{}`", self.snippet(e.span));
                    self.report_arm_mismatch(&text, e.span, level);
                    return None;
                }
                self.arm_literals.insert(literal.id);
                Some(ArmValue::Cond(literal))
            }
            ast::ExprKind::Str(text) | ast::ExprKind::RawTemplate(text) => {
                if let Some(adt) = self.str_union_of(base) {
                    return match self.union_case(adt, *text) {
                        Some(variant) => Some(ArmValue::Case(variant)),
                        None => {
                            self.report_not_in_union(*text, e.span, adt);
                            None
                        }
                    };
                }
                if tcx.kind(base) != TyKind::Str {
                    let shown = format!("`{}`", self.snippet(e.span));
                    self.report_arm_mismatch(&shown, e.span, level);
                    return None;
                }
                let id = tcx.intern_str(text.as_str());
                Some(ArmValue::Const(ConstValue::Str(id)))
            }
            ast::ExprKind::Bool(b) => {
                if tcx.kind(base) != TyKind::Bool {
                    let shown = format!("`{b}`");
                    self.report_arm_mismatch(&shown, e.span, level);
                    return None;
                }
                Some(ArmValue::Const(ConstValue::Bool(*b)))
            }
            _ => {
                self.report_not_arm_value(e.span, level);
                None
            }
        }
    }

    /// A range arm value `a..b` over numbers (half-open).
    fn range_arm(&mut self, a: &ast::Expr, b: &ast::Expr, level: &MatchLevel) -> Option<ArmValue> {
        let lo = self.literal_arm(a, level)?;
        let hi = self.literal_arm(b, level)?;
        let (ArmValue::Cond(lo), ArmValue::Cond(hi)) = (lo, hi) else {
            self.report_not_arm_value(a.span.to(b.span), level);
            return None;
        };
        self.arm_literals.remove(&lo.id);
        self.arm_literals.remove(&hi.id);
        let span = a.span.to(b.span);
        let ty = lo.ty;
        let pair = self.mk_expr(ty, span, ExprKind::TupleLit(vec![lo, hi]));
        self.arm_ranges.insert(pair.id);
        Some(ArmValue::Cond(pair))
    }

    /// A path arm value: a qualified case of the subject's enum, or a constant; a
    /// bare case name is EN0502 (S:492, S:1133); a local, or anything else that is
    /// no constant, EN0504; a name in no scope EN0301.
    fn case_arm(
        &mut self,
        path: &[ast::Ident],
        subject: &hir::Expr,
        level: &MatchLevel,
    ) -> Option<ArmValue> {
        let _ = subject;
        let span = path.first()?.span.to(path.last()?.span);
        let tcx = &*self.sema.tcx;
        if let [name] = path {
            if let Some(adt) = level.adt
                && let AdtKind::Enum(e) = &tcx.adt(adt).kind
                && let Some((variant, _)) = e.variant_named(name.name)
            {
                let enum_name = tcx.adt(adt).name;
                self.sema.emit(
                    Diagnostic::new(
                        Code::EN0502,
                        format!(
                            "`{}` is a case of `{enum_name}`: write `{enum_name}.{}`",
                            name.name, name.name
                        ),
                        name.span,
                        "a case is always written with its enum's name",
                    )
                    .with_help(Help::machine(
                        format!("write `{enum_name}.{}`", name.name),
                        vec![Edit::insert(name.span.lo, format!("{enum_name}."))],
                    )),
                );
                return Some(ArmValue::Case(variant));
            }
            if self.scopes.lookup(name.name).is_some() {
                // A local is no arm value (S:1132): only `match (true)` tests one.
                self.report_not_arm_value(span, level);
                return None;
            }
            let res = scope::lookup_value(self.sema, self.at, *name);
            return match res {
                Res::Def(def) if self.sema.tcx.def(def).kind == hir::DefKind::Const => {
                    let ty = crate::typeck::const_ty(self.sema, def);
                    let value = self
                        .sema
                        .tcx
                        .const_value(def)
                        .and_then(|tree| tree.as_scalar());
                    if let Some(ty) = ty
                        && !self.is_error(level.base)
                        && !self.can_unify(ty, level.base)
                    {
                        let text = format!("`{}`", name.name);
                        self.report_arm_mismatch(&text, span, level);
                        return None;
                    }
                    value.map(ArmValue::Const)
                }
                Res::Err => {
                    self.unresolved_value(*name);
                    None
                }
                _ => {
                    self.report_not_arm_value(span, level);
                    None
                }
            };
        }
        let (last, ty_path) = path.split_last()?;
        let res = scope::lookup_type(self.sema, self.at, ty_path);
        let adt = match res {
            Res::Def(def) => self.sema.tcx.adt_of(def),
            _ => None,
        };
        let Some(adt) = adt else {
            if !matches!(res, Res::Err) {
                self.report_not_arm_value(span, level);
            }
            return None;
        };
        let tcx = &*self.sema.tcx;
        let AdtKind::Enum(e) = &tcx.adt(adt).kind else {
            self.report_not_arm_value(span, level);
            return None;
        };
        let Some((variant, _)) = e.variant_named(last.name) else {
            let name = tcx.adt(adt).name;
            self.sema.emit(Diagnostic::new(
                Code::EN0303,
                format!("`{name}` has no member `{}`", last.name),
                last.span,
                format!("not a case of `{name}`"),
            ));
            return None;
        };
        if level.adt != Some(adt) {
            let text = format!("`{}`", self.snippet(span));
            self.report_arm_mismatch(&text, span, level);
            return None;
        }
        Some(ArmValue::Case(variant))
    }

    /// EN0504 `` `Shape.Circle` can't match a `Color` ``.
    fn report_arm_mismatch(&mut self, what: &str, span: Span, level: &MatchLevel) {
        let shown = self.ty_str(level.shown);
        self.sema.emit(Diagnostic::new(
            Code::EN0504,
            format!("{what} can't match {}", crate::classes::sig::a_ty(&shown)),
            span,
            format!("the subject is `{shown}`"),
        ));
    }

    /// EN0504 for an arm value that is no literal, case, constant, `null`, `Ok`,
    /// `Err` or range (S:1132).
    fn report_not_arm_value(&mut self, span: Span, level: &MatchLevel) {
        let text = self.snippet(span);
        let shown = self.ty_str(level.shown);
        self.sema.emit(
            Diagnostic::new(
                Code::EN0504,
                format!("`{text}` can't match {}", crate::classes::sig::a_ty(&shown)),
                span,
                "an arm value is a literal, a case, a constant, `null`, `Ok`, `Err` or a range",
            )
            .with_help(Help::text(
                "to test conditions, write `match (true)` with a condition in each arm",
            )),
        );
    }
}

/// The expression a path of identifiers spells, `a` or `a.b.c`: an arm value under
/// `match (true)`, which the parser leaves as a path (plan c.5).
fn path_expr(path: &[ast::Ident]) -> Option<ast::Expr> {
    let (first, rest) = path.split_first()?;
    let id = ast::NodeId(u32::MAX);
    let mut e = ast::Expr {
        id,
        span: first.span,
        kind: ast::ExprKind::Ident(first.name),
    };
    for name in rest {
        let span = e.span.to(name.span);
        e = ast::Expr {
            id,
            span,
            kind: ast::ExprKind::Member {
                base: Box::new(e),
                name: *name,
                optional: false,
            },
        };
    }
    Some(e)
}

/// What a `match` subject's arm values are checked against: the type under its
/// references, boxes and `| null` layers.
pub(crate) struct MatchLevel {
    /// The innermost type.
    base: Ty,
    /// The subject's type as messages show it (references and boxes looked through).
    shown: Ty,
    nullable: bool,
    /// The enum (or `Result`, or string-literal union) of `base`.
    adt: Option<hir::AdtId>,
    error: bool,
}

impl MatchLevel {
    fn of(fcx: &FnCtxt<'_, '_>, t: Ty) -> MatchLevel {
        let tcx = &*fcx.sema.tcx;
        let peel = |mut t: Ty| loop {
            t = fcx.shallow(t);
            match tcx.kind(t) {
                TyKind::Ref(inner) | TyKind::Boxed(inner) => t = inner,
                _ => return t,
            }
        };
        let shown = peel(t);
        let mut base = shown;
        let mut nullable = false;
        while let TyKind::Nullable(inner) = tcx.kind(base) {
            nullable = true;
            base = peel(inner);
        }
        let adt = match tcx.kind(base) {
            TyKind::Adt(adt, _) if tcx.adt(adt).is_enum() => Some(adt),
            _ => None,
        };
        MatchLevel {
            base,
            shown,
            nullable,
            adt,
            error: fcx.is_error(t),
        }
    }
}

/// The span of an arm value, for `Arm.value_spans` (D7).
fn arm_value_span(v: &ast::ArmValue) -> Span {
    match v {
        ast::ArmValue::Value(e) => e.span,
        ast::ArmValue::Null(s) | ast::ArmValue::Ok(s) | ast::ArmValue::Err(s) => *s,
        ast::ArmValue::Case(path) => match (path.first(), path.last()) {
            (Some(a), Some(b)) => a.span.to(b.span),
            _ => Span::DUMMY,
        },
        ast::ArmValue::Range(a, b) => a.span.to(b.span),
    }
}

/// `e` under its parentheses.
pub(crate) fn strip_parens(mut e: &ast::Expr) -> &ast::Expr {
    while let ast::ExprKind::Paren(inner) = &e.kind {
        e = inner;
    }
    e
}

/// The frame of a call: the callee's name, and the callee's span when it is a
/// plain name (which a coercion's message may resolve to a parameter).
fn call_frame(callee: &ast::Expr, args: &[ast::Expr]) -> CallFrame {
    let (name, span) = match &strip_parens(callee).kind {
        ast::ExprKind::Ident(name) => (Some(*name), callee.span),
        ast::ExprKind::Member { name, .. } => (Some(name.name), Span::DUMMY),
        ast::ExprKind::TypeMember { name, .. } => (Some(name.name), Span::DUMMY),
        ast::ExprKind::Super => (Some(intern("super")), Span::DUMMY),
        _ => (None, Span::DUMMY),
    };
    CallFrame {
        callee: name,
        callee_span: span,
        args: args.iter().map(|a| a.span).collect(),
        reported: false,
    }
}

/// The last name of a written named type (`Box` for `Box<i64>`).
fn type_name(t: &ast::TypeExpr) -> Option<enrang_base::Symbol> {
    match &t.kind {
        ast::TypeExprKind::Named { path, .. } => path.last().map(|i| i.name),
        _ => None,
    }
}

/// The operator of a compound assignment, as a `BinOp`.
fn compound_op(op: ast::AssignOp) -> Option<ast::BinOp> {
    Some(match op {
        ast::AssignOp::Assign => return None,
        ast::AssignOp::Add => ast::BinOp::Add,
        ast::AssignOp::Sub => ast::BinOp::Sub,
        ast::AssignOp::Mul => ast::BinOp::Mul,
        ast::AssignOp::Div => ast::BinOp::Div,
        ast::AssignOp::Rem => ast::BinOp::Rem,
        ast::AssignOp::BitAnd => ast::BinOp::BitAnd,
        ast::AssignOp::BitOr => ast::BinOp::BitOr,
        ast::AssignOp::BitXor => ast::BinOp::BitXor,
        ast::AssignOp::Shl => ast::BinOp::Shl,
        ast::AssignOp::Shr => ast::BinOp::Shr,
    })
}
