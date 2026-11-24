//! Operators (plan d.6; SPEC 4.6-4.8; owner 3A).
//!
//! Operators see through one reference: an operand of type `&T` acts as a `T` when
//! `T` is Copy or `string` (S:684), and `==` compares through a reference on either
//! side, never by address. Binary arithmetic needs identical types after inference
//! (EN0402 `` cannot subtract `int` from `isize` ``, with an `as` fix-it that widens
//! the narrower operand, which never fails on any target, S:688); `+` on two strings
//! builds a new `string`; integer `/` of two literal operands (literals, or
//! arithmetic of literals), whatever their integer type, or of two operands whose
//! type came from the `int` default, is warning EN0430 with `7.0 / 2.0` (S:688:
//! `const q: i64 = 7 / 2;` warns too), unless both are literals that divide
//! exactly, which truncates nothing (plan choice, so `10 / 2` is quiet); bitwise
//! operators need integers of
//! one type and shifts integers of any two (EN0403); `a & b == c` reads as
//! `a & (b == c)` and is EN0420 with a parenthesise fix-it (S:508). Comparisons
//! follow S:692-701: `p == null` for a nullable `p`; numerics of one type, `bool`,
//! `string` and payload-free enums natively; two integer types by value; an integer
//! and a float never (EN0402); a class or payload enum through `Eq` (EN0421);
//! `T | null == T` EN0401 with a narrowing help; `<` on numerics only, `string`
//! EN0420 with a `.compare` fix-it. In a comparison an unresolved variable takes the
//! other operand's type (S:726), and a string literal on the left takes a
//! string-literal union on the right as `d == "left"` does. `!` needs `bool`
//! (EN0203, plan choice), `-` a signed number (EN0420) and `~` an integer (EN0403);
//! an operand still an `Int` variable, which a later use may make a float or an
//! unsigned integer (S:726), is checked for these and for indexing once it has its
//! final type (`Deferred::NumUse`), so the outcome never depends on statement order.
//! `&&` and `||` take conditions (EN0203, plan choice), and `a ?? b` a nullable `a`
//! (EN0420) and a `b` of its payload's type or of its own (S:752), a string literal
//! taking its static descriptor where the payload is `&string` (C13, S:827).

use enrang_base::{Span, intern};
use enrang_diag::{Code, Diagnostic, Edit, Help};
use enrang_hir::{self as hir, AdtKind, ExprKind, IntTy, LangItem, Ty, TyKind};
use enrang_syntax::ast::{self, BinOp, LogOp, UnOp};

use crate::typeck::infer::VarKind;
use crate::typeck::{Deferred, Expect, FnCtxt, NumNeed};

/// What a numeric operand is.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Num {
    Int(IntTy),
    Float,
    IntVar,
    FloatVar,
}

impl FnCtxt<'_, '_> {
    /// `t` as an operator sees it: `&T` as `T` when `T` is Copy or `string`. A
    /// number still being inferred is Copy whatever type it becomes, so `x * x`
    /// with `x: &int` from `[1, 2, 3].map(x => x * x)` reads through too.
    pub(crate) fn operand_ty(&self, t: Ty) -> Ty {
        let t = self.shallow(t);
        match self.sema.tcx.kind(t) {
            TyKind::Ref(inner) => {
                let inner = self.shallow(inner);
                let number_var =
                    matches!(self.var_kind(inner), Some(VarKind::Int | VarKind::Float));
                let tcx = &*self.sema.tcx;
                if number_var || tcx.kind(inner) == TyKind::Str || tcx.is_copy(inner, &self.env) {
                    inner
                } else {
                    t
                }
            }
            _ => t,
        }
    }

    fn num(&self, t: Ty) -> Option<Num> {
        match self.sema.tcx.kind(t) {
            TyKind::Int(int) => Some(Num::Int(int)),
            TyKind::Float(_) => Some(Num::Float),
            TyKind::Infer(_) => match self.var_kind(t) {
                Some(VarKind::Int) => Some(Num::IntVar),
                Some(VarKind::Float) => Some(Num::FloatVar),
                _ => None,
            },
            _ => None,
        }
    }

    fn is_int(&self, t: Ty) -> bool {
        matches!(self.num(t), Some(Num::Int(_) | Num::IntVar))
    }

    fn is_str(&self, t: Ty) -> bool {
        self.sema.tcx.kind(t) == TyKind::Str
    }

    /// Whether `t` is `Error` or an `Any` variable an earlier error left behind.
    fn absorbs(&self, t: Ty) -> bool {
        self.is_error(t)
    }

    pub(crate) fn check_unary(
        &mut self,
        op: UnOp,
        operand: &ast::Expr,
        span: Span,
        ex: Expect,
    ) -> hir::Expr {
        let common = *self.sema.tcx.common();
        match op {
            UnOp::Not => {
                let value = self.check_cond(operand);
                self.mk_expr(common.bool, span, ExprKind::Unary(op, Box::new(value)))
            }
            UnOp::Neg => {
                if let Some(literal) = self.negative_literal(operand, span, ex) {
                    return literal;
                }
                let hint = self.numeric_hint(ex);
                let value = self.check_value(operand, hint);
                let t = self.operand_ty(value.ty);
                if self.absorbs(t) {
                    return self.mk_expr(t, span, ExprKind::Unary(op, Box::new(value)));
                }
                let ok = match self.num(t) {
                    Some(Num::Int(int)) => int.is_signed(),
                    Some(Num::IntVar) => {
                        // A later use may make it unsigned: checked at the end.
                        self.defer_num_use(span, t, NumNeed::Signed);
                        true
                    }
                    Some(_) => true,
                    None => false,
                };
                if !ok {
                    let shown = self.ty_str(t);
                    let what = if self.num(t).is_some() {
                        "a signed number"
                    } else {
                        "a number"
                    };
                    self.sema.emit(Diagnostic::new(
                        Code::EN0420,
                        format!("`-` needs {what}, found `{shown}`"),
                        span,
                        format!("this is `{shown}`"),
                    ));
                    let error = self.error_ty();
                    return self.mk_expr(error, span, ExprKind::Unary(op, Box::new(value)));
                }
                self.mk_expr(t, span, ExprKind::Unary(op, Box::new(value)))
            }
            UnOp::BitNot => {
                let hint = self.numeric_hint(ex);
                let value = self.check_expr(operand, hint);
                let t = self.operand_ty(value.ty);
                if !self.absorbs(t) && !self.is_int(t) {
                    self.report_needs_int("~", &value, t);
                    let error = self.error_ty();
                    return self.mk_expr(error, span, ExprKind::Unary(op, Box::new(value)));
                }
                self.defer_num_use(value.span, t, NumNeed::Integer("~"));
                self.mk_expr(t, span, ExprKind::Unary(op, Box::new(value)))
            }
        }
    }

    /// The expectation passed to a numeric operator's operands: the expected type
    /// when it is numeric, so `const x: i64 = 1 + 2;` types both literals `i64`.
    fn numeric_hint(&self, ex: Expect) -> Expect {
        match ex.ty() {
            Some(t) => {
                let t = self.shallow(t);
                if self.num(t).is_some() {
                    Expect::Has(t)
                } else {
                    Expect::None
                }
            }
            None => Expect::None,
        }
    }

    /// EN0403 `` `&` needs integers, found `f64` `` at the operand.
    fn report_needs_int(&mut self, op: &str, operand: &hir::Expr, t: Ty) {
        let shown = self.ty_str(t);
        self.sema.emit(Diagnostic::new(
            Code::EN0403,
            format!("`{op}` needs integers, found `{shown}`"),
            operand.span,
            format!("this is `{shown}`"),
        ));
    }

    /// Defers the check that the operand at `span`, of type `t`, is what `need`
    /// asks, when `t` is still an `Int` variable, which a later use may make a float
    /// or an unsigned integer (S:726): [`Self::check_num_use`] runs after defaults.
    pub(crate) fn defer_num_use(&mut self, span: Span, t: Ty, need: NumNeed) {
        if self.var_kind(t) == Some(VarKind::Int) {
            self.deferred.push(Deferred::NumUse { span, ty: t, need });
        }
    }

    /// The deferred check of [`Self::defer_num_use`], on the operand's final type:
    /// EN0403 for a float at a bitwise or shift operator, EN0405 for a float index,
    /// EN0420 for `-` of an unsigned integer.
    pub(crate) fn check_num_use(&mut self, span: Span, ty: Ty, need: NumNeed) {
        let t = self.resolve(ty);
        let tcx = &*self.sema.tcx;
        let shown = tcx.ty_string(t);
        let (code, message) = match (need, tcx.kind(t)) {
            (NumNeed::Integer(op), TyKind::Float(_)) => (
                Code::EN0403,
                format!("`{op}` needs integers, found `{shown}`"),
            ),
            (NumNeed::Index, TyKind::Float(_)) => (
                Code::EN0405,
                format!("an index must be an integer, found `{shown}`"),
            ),
            (NumNeed::Signed, TyKind::Int(int)) if !int.is_signed() => (
                Code::EN0420,
                format!("`-` needs a signed number, found `{shown}`"),
            ),
            _ => return,
        };
        self.sema.emit(Diagnostic::new(
            code,
            message,
            span,
            format!("this is `{shown}`"),
        ));
    }

    pub(crate) fn check_binary(
        &mut self,
        op: BinOp,
        a: &ast::Expr,
        b: &ast::Expr,
        span: Span,
        ex: Expect,
    ) -> hir::Expr {
        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                self.check_arith(op, a, b, span, ex)
            }
            BinOp::Shl | BinOp::Shr => self.check_shift(op, a, b, span, ex),
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => self.check_bitwise(op, a, b, span, ex),
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => self.check_ordering(op, a, b, span),
            BinOp::Eq | BinOp::Ne => self.check_equality(op, a, b, span),
        }
    }

    fn binary(&mut self, op: BinOp, a: hir::Expr, b: hir::Expr, ty: Ty, span: Span) -> hir::Expr {
        self.mk_expr(ty, span, ExprKind::Binary(op, Box::new(a), Box::new(b)))
    }

    /// The two operands of a numeric operator: the right one hinted with the left
    /// one's type, so `x + 1` types the literal as `x`.
    fn operands(&mut self, a: &ast::Expr, b: &ast::Expr, ex: Expect) -> (hir::Expr, hir::Expr) {
        let hint = self.numeric_hint(ex);
        let a = self.check_value(a, hint);
        let a = self.read_narrowed(a);
        let ta = self.operand_ty(a.ty);
        let hint_b = if self.num(ta).is_some() || self.is_str(ta) {
            Expect::Has(ta)
        } else {
            hint
        };
        let b = self.check_value(b, hint_b);
        let b = self.read_narrowed(b);
        (a, b)
    }

    fn check_arith(
        &mut self,
        op: BinOp,
        a_ast: &ast::Expr,
        b_ast: &ast::Expr,
        span: Span,
        ex: Expect,
    ) -> hir::Expr {
        let (a, b) = self.operands(a_ast, b_ast, ex);
        let (ta, tb) = (self.operand_ty(a.ty), self.operand_ty(b.ty));
        if self.absorbs(ta) || self.absorbs(tb) {
            let error = self.error_ty();
            return self.binary(op, a, b, error, span);
        }
        if op == BinOp::Add && self.is_str(ta) && self.is_str(tb) {
            let str_ty = self.sema.tcx.common().str;
            return self.binary(op, a, b, str_ty, span);
        }
        let (na, nb) = (self.num(ta), self.num(tb));
        if na.is_none() || nb.is_none() {
            self.report_not_numbers(op, (&a, a_ast, ta), (&b, b_ast, tb), na.is_none(), span);
            let error = self.error_ty();
            return self.binary(op, a, b, error, span);
        }
        if !self.unify(ta, tb) {
            self.report_mixed(op, a_ast, b_ast, ta, tb, span);
            let error = self.error_ty();
            return self.binary(op, a, b, error, span);
        }
        let ty = self.shallow(ta);
        let (fa, fb) = (fold_int(a_ast), fold_int(b_ast));
        let exact = match (fa, fb) {
            (Some(x), Some(y)) => y == 0 || x.checked_rem(y) == Some(0),
            _ => false,
        };
        let literal_operands = fa.is_some() && fb.is_some();
        let int_var = self.var_kind(ty) == Some(VarKind::Int);
        let int_ty = int_var || matches!(self.sema.tcx.kind(ty), TyKind::Int(_));
        if op == BinOp::Div && !exact && int_ty && (int_var || literal_operands) {
            let literals = matches!(a_ast.kind, ast::ExprKind::Int { .. })
                && matches!(b_ast.kind, ast::ExprKind::Int { .. });
            self.int_divisions.push(IntDivision {
                span,
                ty,
                literals: literals.then_some((a_ast.span, b_ast.span)),
                literal_operands,
                values: fa.zip(fb),
            });
        }
        self.binary(op, a, b, ty, span)
    }

    /// EN0420 for arithmetic with an operand that is not a number, labelled at that
    /// operand (SPEC 13.1: the label describes the span it marks). A nullable
    /// number gets a `??` default and, when it is a path, a narrowing help (S:739);
    /// a string and a number under `+` get a template, TypeScript's habit of
    /// joining them being refused.
    fn report_not_numbers(
        &mut self,
        op: BinOp,
        a: (&hir::Expr, &ast::Expr, Ty),
        b: (&hir::Expr, &ast::Expr, Ty),
        a_bad: bool,
        span: Span,
    ) {
        let (ta, tb) = (a.2, b.2);
        let ((bad, bad_ast, bad_ty), (_, other_ast, other_ty)) =
            if a_bad { (a, b) } else { (b, a) };
        let shown = self.ty_str(bad_ty);
        let joins_text = op == BinOp::Add && (self.is_str(ta) || self.is_str(tb));
        let message = if joins_text {
            format!(
                "`+` needs two numbers or two strings, found `{}` and `{}`",
                self.ty_str(ta),
                self.ty_str(tb)
            )
        } else {
            format!("`{}` needs numbers, found `{shown}`", op.as_str())
        };
        let mut diag = Diagnostic::new(
            Code::EN0420,
            message,
            bad_ast.span,
            format!("this is `{shown}`"),
        );
        let payload = match self.sema.tcx.kind(self.shallow(bad_ty)) {
            TyKind::Nullable(inner) => self.num(self.operand_ty(inner)),
            _ => None,
        };
        if let Some(num) = payload {
            let zero = match num {
                Num::Float | Num::FloatVar => "0.0",
                Num::Int(_) | Num::IntVar => "0",
            };
            let text = self.snippet(bad_ast.span);
            diag = diag.with_help(Help::suggest(
                format!("give it a default for `null`: `({text} ?? {zero})`"),
                vec![
                    Edit::insert(bad_ast.span.lo, "("),
                    Edit::insert(bad_ast.span.hi, format!(" ?? {zero})")),
                ],
            ));
            if self.adjusted_path(bad).is_some() {
                diag = diag.with_help(Help::text(format!(
                    "or narrow it first: `if ({text} != null) {{ ... }}`"
                )));
            }
        } else if joins_text && self.num(other_ty).is_some() {
            let shown_other = self.ty_str(other_ty);
            let (left, right) = if a_bad {
                (bad_ast, other_ast)
            } else {
                (other_ast, bad_ast)
            };
            let template = format!(
                "`{}{}`",
                self.template_part(left),
                self.template_part(right)
            );
            diag = diag
                .with_secondary(other_ast.span, format!("this is `{shown_other}`"))
                .with_help(Help::suggest(
                    "use a template, which formats the number",
                    vec![Edit::replace(span, template)],
                ));
        }
        self.sema.emit(diag);
    }

    /// `e` as a part of a template: a string literal's text in place, when it
    /// holds no escape, backtick or `${`; a template's text without its backticks;
    /// anything else as a hole, `${e}`.
    fn template_part(&self, e: &ast::Expr) -> String {
        let text = self.snippet(e.span);
        let inner = match &e.kind {
            ast::ExprKind::Str(_) | ast::ExprKind::Template(_) if text.len() >= 2 => {
                Some(&text[1..text.len() - 1])
            }
            _ => None,
        };
        match inner {
            Some(inner)
                if matches!(e.kind, ast::ExprKind::Template(_))
                    || !(inner.contains('\\') || inner.contains('`') || inner.contains("${")) =>
            {
                inner.to_owned()
            }
            _ => format!("${{{text}}}"),
        }
    }

    /// EN0402 for two numeric types that differ, with an `as` fix-it on the operand
    /// that widens into the other's type, when one does on every target (S:688).
    fn report_mixed(
        &mut self,
        op: BinOp,
        a: &ast::Expr,
        b: &ast::Expr,
        ta: Ty,
        tb: Ty,
        span: Span,
    ) {
        let (sa, sb) = (self.ty_str(ta), self.ty_str(tb));
        let message = match op {
            BinOp::Add => format!("cannot add `{sb}` to `{sa}`"),
            BinOp::Sub => format!("cannot subtract `{sb}` from `{sa}`"),
            BinOp::Mul => format!("cannot multiply `{sa}` by `{sb}`"),
            BinOp::Div => format!("cannot divide `{sa}` by `{sb}`"),
            BinOp::Rem => format!("cannot take the remainder of `{sa}` divided by `{sb}`"),
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne => {
                format!("cannot compare `{sa}` with `{sb}`")
            }
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
                format!("cannot apply `{}` to `{sa}` and `{sb}`", op.as_str())
            }
        };
        let mut diag = Diagnostic::new(
            Code::EN0402,
            message,
            span,
            format!("`{sa}` and `{sb}` are different types"),
        );
        let display_a = super::infer::display_in(self.sema.tcx, &self.infer, ta);
        let display_b = super::infer::display_in(self.sema.tcx, &self.infer, tb);
        let widen = if widens(self.sema.tcx, display_b, display_a) {
            Some((b, sa.clone()))
        } else if widens(self.sema.tcx, display_a, display_b) {
            Some((a, sb.clone()))
        } else {
            None
        };
        if let Some((operand, to)) = widen {
            let (text, edits) = self.widen_fix(operand, &to);
            diag = diag.with_help(Help::machine(
                format!("convert it, which never fails: `{text}`"),
                edits,
            ));
        }
        self.sema.emit(diag);
    }

    /// The `as` conversion of `operand` to `to`, as the help prints it and as the
    /// edits that write it: `(x as T)`. `as` binds tighter than every binary
    /// operator (SPEC 3.5), so an operand that is not a primary, postfix or prefix
    /// expression is parenthesised first, `((n - 1) as T)`, and one the user already
    /// parenthesised keeps those parentheses, `((xs.length() - 1) as T)`; otherwise
    /// the edit would convert only its last operand.
    fn widen_fix(&self, operand: &ast::Expr, to: &str) -> (String, Vec<Edit>) {
        let span = operand.span;
        let text = self.snippet(span);
        if binds_tighter_than_as(operand) {
            let edits = vec![
                Edit::insert(span.lo, "("),
                Edit::insert(span.hi, format!(" as {to})")),
            ];
            (format!("({text} as {to})"), edits)
        } else {
            let edits = vec![
                Edit::insert(span.lo, "(("),
                Edit::insert(span.hi, format!(") as {to})")),
            ];
            (format!("(({text}) as {to})"), edits)
        }
    }

    fn check_shift(
        &mut self,
        op: BinOp,
        a_ast: &ast::Expr,
        b_ast: &ast::Expr,
        span: Span,
        ex: Expect,
    ) -> hir::Expr {
        let hint = self.numeric_hint(ex);
        let a = self.check_expr(a_ast, hint);
        let b = self.check_expr(b_ast, Expect::None);
        let (ta, tb) = (self.operand_ty(a.ty), self.operand_ty(b.ty));
        if self.absorbs(ta) || self.absorbs(tb) {
            let error = self.error_ty();
            return self.binary(op, a, b, error, span);
        }
        let bad = if !self.is_int(ta) {
            Some((&a, ta))
        } else if !self.is_int(tb) {
            Some((&b, tb))
        } else {
            None
        };
        if let Some((operand, t)) = bad {
            self.report_needs_int(op.as_str(), operand, t);
            let error = self.error_ty();
            return self.binary(op, a, b, error, span);
        }
        self.defer_num_use(a.span, ta, NumNeed::Integer(op.as_str()));
        if !self.same_var(ta, tb) {
            self.defer_num_use(b.span, tb, NumNeed::Integer(op.as_str()));
        }
        let ty = self.shallow(ta);
        self.binary(op, a, b, ty, span)
    }

    /// Whether `a` and `b` are the same unbound variable.
    fn same_var(&self, a: Ty, b: Ty) -> bool {
        let (a, b) = (self.shallow(a), self.shallow(b));
        a == b && matches!(self.sema.tcx.kind(a), TyKind::Infer(_))
    }

    fn check_bitwise(
        &mut self,
        op: BinOp,
        a_ast: &ast::Expr,
        b_ast: &ast::Expr,
        span: Span,
        ex: Expect,
    ) -> hir::Expr {
        if let Some(cmp) = [a_ast, b_ast].into_iter().find(|e| is_comparison(e)) {
            return self.report_precedence(op, a_ast, b_ast, cmp, span);
        }
        let (a, b) = self.operands(a_ast, b_ast, ex);
        let (ta, tb) = (self.operand_ty(a.ty), self.operand_ty(b.ty));
        if self.absorbs(ta) || self.absorbs(tb) {
            let error = self.error_ty();
            return self.binary(op, a, b, error, span);
        }
        let bad = if !self.is_int(ta) {
            Some((&a, ta))
        } else if !self.is_int(tb) {
            Some((&b, tb))
        } else {
            None
        };
        if let Some((operand, t)) = bad {
            self.report_needs_int(op.as_str(), operand, t);
            let error = self.error_ty();
            return self.binary(op, a, b, error, span);
        }
        if !self.unify(ta, tb) {
            self.report_mixed(op, a_ast, b_ast, ta, tb, span);
            let error = self.error_ty();
            return self.binary(op, a, b, error, span);
        }
        // The operands now share one type: one check, at the first.
        self.defer_num_use(a.span, ta, NumNeed::Integer(op.as_str()));
        let ty = self.shallow(ta);
        self.binary(op, a, b, ty, span)
    }

    /// EN0420 for `a & b == c`, which reads as `a & (b == c)` (S:508), with a fix-it
    /// that parenthesises the bitwise operation.
    fn report_precedence(
        &mut self,
        op: BinOp,
        a: &ast::Expr,
        b: &ast::Expr,
        cmp: &ast::Expr,
        span: Span,
    ) -> hir::Expr {
        let ast::ExprKind::Binary(cmp_op, left, right) = &cmp.kind else {
            return self.error_expr(span);
        };
        let (open, close) = if std::ptr::eq(cmp, b) {
            (a.span.lo, left.span.hi)
        } else {
            (right.span.lo, b.span.hi)
        };
        let o = op.as_str();
        let c = cmp_op.as_str();
        self.sema.emit(
            Diagnostic::new(
                Code::EN0420,
                format!("`{o}` binds looser than `{c}`"),
                span,
                format!("this reads as `{o}` of a `bool`"),
            )
            .with_secondary(cmp.span, format!("`{c}` is applied first"))
            .with_help(Help::machine(
                format!("parenthesise the `{o}`"),
                vec![Edit::insert(open, "("), Edit::insert(close, ")")],
            )),
        );
        let _ = self.check_expr(a, Expect::None);
        let _ = self.check_expr(b, Expect::None);
        self.error_expr(span)
    }

    fn check_ordering(
        &mut self,
        op: BinOp,
        a_ast: &ast::Expr,
        b_ast: &ast::Expr,
        span: Span,
    ) -> hir::Expr {
        let bool_ty = self.sema.tcx.common().bool;
        let (a, b) = self.operands(a_ast, b_ast, Expect::None);
        let (ta, tb) = (self.operand_ty(a.ty), self.operand_ty(b.ty));
        if self.absorbs(ta) || self.absorbs(tb) {
            return self.binary(op, a, b, bool_ty, span);
        }
        if self.is_str(ta) && self.is_str(tb) {
            self.report_string_order(op, &a, &b, a_ast, b_ast, span);
            return self.binary(op, a, b, bool_ty, span);
        }
        let (na, nb) = (self.num(ta), self.num(tb));
        if na.is_none() || nb.is_none() {
            let (sa, sb) = (self.ty_str(ta), self.ty_str(tb));
            let message = if sa == sb {
                format!("`{}` can't compare `{sa}`s", op.as_str())
            } else {
                format!("`{}` can't compare `{sa}` with `{sb}`", op.as_str())
            };
            self.sema.emit(Diagnostic::new(
                Code::EN0420,
                message,
                span,
                "only numbers have an order".to_owned(),
            ));
            return self.binary(op, a, b, bool_ty, span);
        }
        self.compare_numbers(op, a_ast, b_ast, ta, tb, span);
        self.binary(op, a, b, bool_ty, span)
    }

    /// Two numeric operands of a comparison: a variable takes the other's type; two
    /// integer types compare by value; an integer and a float never (EN0402).
    fn compare_numbers(
        &mut self,
        op: BinOp,
        a: &ast::Expr,
        b: &ast::Expr,
        ta: Ty,
        tb: Ty,
        span: Span,
    ) {
        if self.unify(ta, tb) {
            return;
        }
        if self.is_int(ta) && self.is_int(tb) {
            return;
        }
        self.report_mixed(op, a, b, ta, tb, span);
    }

    /// EN0420 `` `<` can't compare `string`s ``, with a `.compare` fix-it (S:701).
    fn report_string_order(
        &mut self,
        op: BinOp,
        a: &hir::Expr,
        b: &hir::Expr,
        a_ast: &ast::Expr,
        b_ast: &ast::Expr,
        span: Span,
    ) {
        let left = self.snippet(a_ast.span);
        let right = self.snippet(b_ast.span);
        let b_is_ref = matches!(self.sema.tcx.kind(self.shallow(b.ty)), TyKind::Ref(_))
            || matches!(b.kind, ExprKind::Const(hir::ConstValue::Str(_)));
        let right = if b_is_ref { right } else { format!("&{right}") };
        let left = if is_atomic(a_ast) {
            left
        } else {
            format!("({left})")
        };
        let _ = a;
        let o = op.as_str();
        let replacement = format!("{left}.compare({right}) {o} 0");
        self.sema.emit(
            Diagnostic::new(
                Code::EN0420,
                format!("`{o}` can't compare `string`s"),
                span,
                "strings have no operator order".to_owned(),
            )
            .with_help(Help::machine(
                format!("compare them with `.compare`: `{replacement}`"),
                vec![Edit::replace(span, replacement.clone())],
            )),
        );
    }

    fn check_equality(
        &mut self,
        op: BinOp,
        a_ast: &ast::Expr,
        b_ast: &ast::Expr,
        span: Span,
    ) -> hir::Expr {
        let a_null = matches!(a_ast.kind, ast::ExprKind::Null);
        let b_null = matches!(b_ast.kind, ast::ExprKind::Null);
        if a_null || b_null {
            return self.check_null_test(op, a_ast, b_ast, a_null, span);
        }
        if is_str_literal(a_ast) && !is_str_literal(b_ast) {
            // A text on the left takes the right side's type, so `"left" == d` reads
            // as `d == "left"` does at a string-literal union.
            let b = self.check_expr(b_ast, Expect::None);
            let tb = self.peel_ref(self.operand_ty(b.ty));
            let hint = match self.str_union_of(tb) {
                Some(_) => Expect::Has(tb),
                None => Expect::None,
            };
            let a = self.check_expr(a_ast, hint);
            return self.finish_equality(op, a, b, a_ast, b_ast, span);
        }
        let a = self.check_expr(a_ast, Expect::None);
        let ta = self.operand_ty(a.ty);
        let ta = self.peel_ref(ta);
        let hint = if self.absorbs(ta) {
            Expect::None
        } else {
            Expect::Has(ta)
        };
        let b = self.check_expr(b_ast, hint);
        self.finish_equality(op, a, b, a_ast, b_ast, span)
    }

    /// The rest of `a == b` once both operands are typed.
    fn finish_equality(
        &mut self,
        op: BinOp,
        a: hir::Expr,
        b: hir::Expr,
        a_ast: &ast::Expr,
        b_ast: &ast::Expr,
        span: Span,
    ) -> hir::Expr {
        let bool_ty = self.sema.tcx.common().bool;
        let ta = self.peel_ref(self.operand_ty(a.ty));
        let tb = self.operand_ty(b.ty);
        let tb = self.peel_ref(tb);
        if self.absorbs(ta) || self.absorbs(tb) {
            return self.binary(op, a, b, bool_ty, span);
        }
        if let (Some(_), Some(_)) = (self.num(ta), self.num(tb)) {
            self.compare_numbers(op, a_ast, b_ast, ta, tb, span);
            return self.binary(op, a, b, bool_ty, span);
        }
        if self.unify(ta, tb) {
            // A comparison EN0421 refused is `Error`: nothing evaluates or
            // reports the `equals` it would call (one mistake, one diagnostic).
            let ty = match self.check_comparable(ta, span) {
                true => bool_ty,
                false => self.error_ty(),
            };
            return self.binary(op, a, b, ty, span);
        }
        let tcx = &*self.sema.tcx;
        let nullable_vs_plain = |x: Ty, y: Ty, me: &Self| match tcx.kind(x) {
            TyKind::Nullable(inner) => me.clone_can_unify(inner, y),
            _ => false,
        };
        if nullable_vs_plain(ta, tb, self) || nullable_vs_plain(tb, ta, self) {
            let (sa, sb) = (self.ty_str(ta), self.ty_str(tb));
            let (nullable, plain, plain_span, nullable_ast) =
                if matches!(self.sema.tcx.kind(ta), TyKind::Nullable(_)) {
                    (sa, sb, b.span, a_ast)
                } else {
                    (sb, sa, a.span, b_ast)
                };
            let name = self.snippet(nullable_ast.span);
            self.sema.emit(
                Diagnostic::new(
                    Code::EN0401,
                    format!("mismatched types: expected `{nullable}`, found `{plain}`"),
                    plain_span,
                    format!("this is `{plain}`"),
                )
                .with_help(Help::text(format!(
                    "test `{name}` first: `{name} != null && ...` narrows it to its payload"
                ))),
            );
            return self.binary(op, a, b, bool_ty, span);
        }
        let (sa, sb) = (self.ty_str(ta), self.ty_str(tb));
        self.sema.emit(Diagnostic::new(
            Code::EN0401,
            format!("mismatched types: expected `{sa}`, found `{sb}`"),
            b.span,
            format!("this is `{sb}`"),
        ));
        self.binary(op, a, b, bool_ty, span)
    }

    /// Whether `a` would unify with `b`, nothing changed.
    fn clone_can_unify(&self, a: Ty, b: Ty) -> bool {
        let mut infer = self.infer.clone();
        super::infer::unify_in(self.sema.tcx, &mut infer, a, b)
    }

    /// `t` with one reference stripped, as `==` compares through references.
    fn peel_ref(&self, t: Ty) -> Ty {
        match self.sema.tcx.kind(self.shallow(t)) {
            TyKind::Ref(inner) => self.shallow(inner),
            _ => self.shallow(t),
        }
    }

    /// `p == null`: `p` must be nullable (S:692).
    fn check_null_test(
        &mut self,
        op: BinOp,
        a_ast: &ast::Expr,
        b_ast: &ast::Expr,
        null_first: bool,
        span: Span,
    ) -> hir::Expr {
        let bool_ty = self.sema.tcx.common().bool;
        let (value_ast, null_ast) = if null_first {
            (b_ast, a_ast)
        } else {
            (a_ast, b_ast)
        };
        let value = self.check_place(value_ast, Expect::None);
        let t = self.shallow(value.ty);
        let null_ty = if self.absorbs(t) {
            self.error_ty()
        } else if matches!(self.sema.tcx.kind(t), TyKind::Nullable(_)) {
            t
        } else if let TyKind::Ref(inner) = self.sema.tcx.kind(t)
            && matches!(self.sema.tcx.kind(self.shallow(inner)), TyKind::Nullable(_))
        {
            self.shallow(inner)
        } else {
            let shown = self.ty_str(t);
            self.sema.emit(Diagnostic::new(
                Code::EN0401,
                format!("mismatched types: expected `{shown} | null`, found `{shown}`"),
                value.span,
                format!("this is `{shown}`, which is never `null`"),
            ));
            self.error_ty()
        };
        let null = self.mk_expr(null_ty, null_ast.span, ExprKind::NullLit);
        let (a, b) = if null_first {
            (null, value)
        } else {
            (value, null)
        };
        self.binary(op, a, b, bool_ty, span)
    }

    /// `==` on one type: natively for numerics, `bool`, `string`, payload-free enums
    /// and raw pointers; `T | null` when `T` is comparable; otherwise through `Eq`
    /// (EN0421, S:698).
    fn check_comparable(&mut self, t: Ty, span: Span) -> bool {
        let t = self.resolve(t);
        if self.comparable(t) {
            return true;
        }
        let shown = self.ty_str(t);
        // An enum writes no `implements` (S:303): it writes `equals` itself.
        let tcx = &*self.sema.tcx;
        let help = match tcx.kind(t) {
            TyKind::Adt(adt, _) if tcx.adt(adt).as_enum().is_some() => format!(
                "add `public equals(other: &{shown}): bool` to `{shown}`'s methods, or `match` on its case"
            ),
            _ => format!("declare `implements Eq` on `{shown}`, or compare its fields"),
        };
        self.sema.emit(
            Diagnostic::new(
                Code::EN0421,
                format!("`==` needs `{shown}` to implement `Eq`"),
                span,
                format!("`{shown}` has no `equals`"),
            )
            .with_help(Help::text(help)),
        );
        false
    }

    fn comparable(&self, t: Ty) -> bool {
        let tcx = &*self.sema.tcx;
        match tcx.kind(t) {
            TyKind::Bool
            | TyKind::Int(_)
            | TyKind::Float(_)
            | TyKind::Str
            | TyKind::Raw(_)
            | TyKind::Void
            | TyKind::Never
            | TyKind::Error
            | TyKind::Infer(_) => true,
            TyKind::Nullable(inner) | TyKind::Ref(inner) => self.comparable(self.shallow(inner)),
            TyKind::Adt(adt, args) => {
                if let AdtKind::Enum(e) = &tcx.adt(adt).kind
                    && e.is_payload_free()
                {
                    return true;
                }
                if self.implements_eq(adt) {
                    return true;
                }
                let equals = intern("equals");
                tcx.member(t, equals, self.at.module).is_some() || {
                    let _ = args;
                    false
                }
            }
            TyKind::Param(p) => tcx.param_bounded_by(p, &self.env, LangItem::Eq),
            _ => {
                let equals = intern("equals");
                tcx.member(t, equals, self.at.module).is_some()
            }
        }
    }

    /// Whether class `adt` or a base declares `implements Eq`.
    fn implements_eq(&self, adt: hir::AdtId) -> bool {
        let tcx = &*self.sema.tcx;
        let Some(eq) = tcx.lang_adt(LangItem::Eq) else {
            return false;
        };
        let mut current = Some(adt);
        let mut seen = Vec::new();
        while let Some(a) = current {
            if seen.contains(&a) {
                return false;
            }
            seen.push(a);
            let Some(class) = tcx.adt(a).as_class() else {
                return false;
            };
            if class
                .implements
                .iter()
                .any(|&i| matches!(tcx.kind(i), TyKind::Adt(x, _) if x == eq))
            {
                return true;
            }
            current = class.base.and_then(|b| match tcx.kind(b) {
                TyKind::Adt(x, _) => Some(x),
                _ => None,
            });
        }
        false
    }

    /// `a && b`, `a || b`: two conditions; `b` is typed under the facts `a` gives
    /// it (4B's `cond_facts`).
    pub(crate) fn check_logical(
        &mut self,
        op: LogOp,
        a: &ast::Expr,
        b: &ast::Expr,
        span: Span,
    ) -> hir::Expr {
        let bool_ty = self.sema.tcx.common().bool;
        let left = self.check_cond(a);
        let saved = self.flow.clone();
        let (when_true, when_false) = self.cond_facts(&left);
        self.flow = match op {
            LogOp::And => when_true,
            LogOp::Or => when_false,
        };
        let right = self.check_cond(b);
        // A change `b` makes may or may not have run (4B).
        let after = std::mem::take(&mut self.flow);
        self.join(vec![saved, after]);
        self.mk_expr(
            bool_ty,
            span,
            ExprKind::Logical(op, Box::new(left), Box::new(right)),
        )
    }

    /// `a ?? b` (S:752): `a: T | null` and `b: T` give `T`; a `b` of `a`'s own type
    /// gives that type; `b` may be `never`.
    pub(crate) fn check_coalesce(
        &mut self,
        a_ast: &ast::Expr,
        b_ast: &ast::Expr,
        span: Span,
        ex: Expect,
    ) -> hir::Expr {
        let hint = match ex.ty() {
            Some(t) => {
                let t = self.shallow(t);
                Expect::Has(self.sema.tcx.mk_nullable(t))
            }
            None => Expect::None,
        };
        let a = self.check_place(a_ast, hint);
        let ta = self.shallow(a.ty);
        if self.absorbs(ta) {
            let b = self.check_expr(b_ast, Expect::None);
            let error = self.error_ty();
            return self.mk_expr(error, span, ExprKind::Coalesce(Box::new(a), Box::new(b)));
        }
        let payload = match self.sema.tcx.kind(ta) {
            TyKind::Nullable(inner) => Some(self.shallow(inner)),
            _ => None,
        };
        let Some(mut payload) = payload else {
            let shown = self.ty_str(ta);
            self.sema.emit(Diagnostic::new(
                Code::EN0420,
                format!("`??` needs a `T | null` on its left, found `{shown}`"),
                a.span,
                format!("this is `{shown}`, which is never `null`"),
            ));
            let b = self.check_expr(b_ast, Expect::None);
            let error = self.error_ty();
            return self.mk_expr(error, span, ExprKind::Coalesce(Box::new(a), Box::new(b)));
        };
        let mut a = a;
        // C08 on the left (S:666): a `&T | null` whose `T` is Copy reads through
        // where the expected type is a `T` by value (S:750; S:605 and A:932 count a
        // `??` arm that reads one as a copy out), or else where the right operand
        // is one, so `ys.first() ?? 0` and `p?.count ?? 0` are a `T`.
        if let Some(inner) = self.copy_behind_ref(payload)
            && let Some(want) = ex.ty().map(|t| self.shallow(t))
            && !matches!(self.sema.tcx.kind(want), TyKind::Ref(_))
            && !self.absorbs(want)
            && self.can_unify(inner, want)
        {
            a.adjust.push(hir::Adjust::ReadThroughNullable);
            payload = inner;
        }
        let b = self.check_expr(b_ast, Expect::Has(payload));
        // A text where `a` holds a `&string` refers to its static descriptor (C13).
        let (b, descriptor) = self.str_literal_at(b, payload);
        let tb = self.shallow(b.ty);
        let ty = if descriptor || self.absorbs(tb) || self.sema.tcx.kind(tb) == TyKind::Never {
            payload
        } else if self.unify(payload, tb) {
            payload
        } else if self.unify(ta, tb) {
            ta
        } else if let Some(inner) = self.copy_behind_ref(payload)
            && !matches!(self.sema.tcx.kind(tb), TyKind::Ref(_))
            && self.unify(inner, tb)
        {
            a.adjust.push(hir::Adjust::ReadThroughNullable);
            inner
        } else {
            let (sp, sb) = (self.ty_str(payload), self.ty_str(tb));
            self.sema.emit(Diagnostic::new(
                Code::EN0401,
                format!("mismatched types: expected `{sp}`, found `{sb}`"),
                b.span,
                format!("this is `{sb}`"),
            ));
            self.error_ty()
        };
        self.mk_expr(ty, span, ExprKind::Coalesce(Box::new(a), Box::new(b)))
    }

    /// `T` when `t` is `&T` and `T` is Copy, an integer or float variable counting
    /// as its default type, as C08 reads through it.
    fn copy_behind_ref(&self, t: Ty) -> Option<Ty> {
        let TyKind::Ref(inner) = self.sema.tcx.kind(self.shallow(t)) else {
            return None;
        };
        let shown = crate::typeck::infer::display_in(self.sema.tcx, &self.infer, inner);
        let tcx = &*self.sema.tcx;
        (!tcx.has_infer(shown) && tcx.is_copy(shown, &self.env)).then_some(inner)
    }

    /// EN0430 for each integer division of two literal operands (literals, or
    /// arithmetic of literals) whatever its integer type, or of operands whose type
    /// came from the `int` default (S:688).
    pub(crate) fn check_int_divisions(&mut self) {
        for division in std::mem::take(&mut self.int_divisions) {
            if !matches!(
                self.sema.tcx.kind(self.resolve(division.ty)),
                TyKind::Int(_)
            ) {
                continue;
            }
            let defaulted = match self.sema.tcx.kind(division.ty) {
                TyKind::Infer(v) => self.infer.defaulted.contains(&self.infer.root(v)),
                _ => false,
            };
            if !division.literal_operands && !defaulted {
                continue;
            }
            let mut diag = Diagnostic::new(
                Code::EN0430,
                "integer division truncates",
                division.span,
                "both sides are integers, so the result is an integer",
            )
            .from_typescript(
                // The operands' own values where they are known (S:688).
                match division
                    .values
                    .and_then(|(x, y)| Some((x, y, x.checked_div(y)?)))
                {
                    Some((x, y, q)) => format!(
                        "TypeScript would give `{}` for `{}`; here it is `{q}`.",
                        x as f64 / y as f64,
                        self.snippet(division.span),
                    ),
                    None => "TypeScript would give `3.5` for `7 / 2`; here it is `3`.".to_owned(),
                },
            );
            diag = match division.literals {
                Some((a, b)) => {
                    let (ta, tb) = (self.snippet(a), self.snippet(b));
                    diag.with_help(Help::machine(
                        format!("for a fraction, divide floats: `{ta}.0 / {tb}.0`"),
                        vec![Edit::insert(a.hi, ".0"), Edit::insert(b.hi, ".0")],
                    ))
                }
                None => diag.with_help(Help::text(
                    "for a fraction, divide floats, as in `7.0 / 2.0`",
                )),
            };
            self.sema.emit(diag);
        }
    }
}

/// An integer division to check once defaults apply (EN0430): its type, the spans
/// of its operands when both are written literals, and whether both are literals
/// or arithmetic of literals.
#[derive(Clone, Debug)]
pub(crate) struct IntDivision {
    pub span: Span,
    pub ty: Ty,
    pub literals: Option<(Span, Span)>,
    pub literal_operands: bool,
    /// The operands' values, when both are literals or arithmetic of literals.
    pub values: Option<(i128, i128)>,
}

/// The value of an integer expression made of literals and `+ - * / %` alone, when
/// it has one: a division of two such values that leaves no remainder truncates
/// nothing, so EN0430 stays quiet (`10 / 2`, plan choice).
fn fold_int(e: &ast::Expr) -> Option<i128> {
    match &e.kind {
        ast::ExprKind::Int { value, .. } => i128::try_from(*value).ok(),
        ast::ExprKind::Paren(inner) => fold_int(inner),
        ast::ExprKind::Unary(UnOp::Neg, inner) => fold_int(inner)?.checked_neg(),
        ast::ExprKind::Binary(op, a, b) => {
            let (x, y) = (fold_int(a)?, fold_int(b)?);
            match op {
                BinOp::Add => x.checked_add(y),
                BinOp::Sub => x.checked_sub(y),
                BinOp::Mul => x.checked_mul(y),
                BinOp::Div => x.checked_div(y),
                BinOp::Rem => x.checked_rem(y),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Whether `e` is a string literal, parentheses aside.
fn is_str_literal(e: &ast::Expr) -> bool {
    match &e.kind {
        ast::ExprKind::Paren(inner) => is_str_literal(inner),
        ast::ExprKind::Str(_) | ast::ExprKind::RawTemplate(_) => true,
        _ => false,
    }
}

/// Whether `e` is a comparison written without parentheses.
fn is_comparison(e: &ast::Expr) -> bool {
    matches!(
        e.kind,
        ast::ExprKind::Binary(
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge,
            _,
            _
        )
    )
}

/// Whether `e` needs no parentheses before `.`.
pub(crate) fn is_atomic(e: &ast::Expr) -> bool {
    matches!(
        e.kind,
        ast::ExprKind::Ident(_)
            | ast::ExprKind::This
            | ast::ExprKind::Str(_)
            | ast::ExprKind::Paren(_)
            | ast::ExprKind::Member { .. }
            | ast::ExprKind::Call { .. }
            | ast::ExprKind::Index(..)
    )
}

/// Whether `e` stays whole as the operand of `as` written after it: a primary,
/// postfix or prefix expression, or a cast (SPEC 3.5, levels 1-3). A binary,
/// logical, `??`, ternary or assignment operand would lose all but its last part
/// (`n - 1 as i64` is `n - (1 as i64)`), and a `match`, object literal, arrow or
/// `asm` is parenthesised to be safe.
fn binds_tighter_than_as(e: &ast::Expr) -> bool {
    use ast::ExprKind as K;
    match &e.kind {
        K::Int { .. }
        | K::Float(_)
        | K::Str(_)
        | K::Template(_)
        | K::RawTemplate(_)
        | K::Bool(_)
        | K::Null
        | K::Paren(_)
        | K::Ident(_)
        | K::This
        | K::Super
        | K::Array(_)
        | K::Repeat(..)
        | K::TypeMember { .. }
        | K::New { .. }
        | K::CaseLit { .. }
        | K::SizeForm(_)
        | K::Unary(..)
        | K::Borrow(_)
        | K::Deref(_)
        | K::VoidOp(_)
        | K::Cast(..)
        | K::IncDec { .. }
        | K::Member { .. }
        | K::Index(..)
        | K::Call { .. }
        | K::Try(_)
        | K::NonNull(_) => true,
        K::Binary(..)
        | K::Logical(..)
        | K::Coalesce(..)
        | K::Ternary(..)
        | K::Assign { .. }
        | K::Match { .. }
        | K::ObjectLit(_)
        | K::Asm(_)
        | K::Arrow(_)
        | K::Error => false,
    }
}

/// Whether every value of `from` is a value of `to`, on every target: an integer
/// into a wider one (`isize`/`usize` counted as 32 bits when widened into and 64
/// when widened from), an integer into a float, `f32` into `f64`.
pub(crate) fn widens(tcx: &hir::Tcx, from: Ty, to: Ty) -> bool {
    match (tcx.kind(from), tcx.kind(to)) {
        (TyKind::Int(a), TyKind::Int(b)) => {
            let from_bits = match a {
                IntTy::Isize | IntTy::Usize => 64,
                other => other.bits(64),
            };
            let to_bits = match b {
                IntTy::Isize | IntTy::Usize => 32,
                other => other.bits(64),
            };
            match (a.is_signed(), b.is_signed()) {
                (false, false) | (true, true) => from_bits <= to_bits,
                (false, true) => from_bits < to_bits,
                (true, false) => false,
            }
        }
        (TyKind::Int(_), TyKind::Float(_)) => true,
        (TyKind::Float(a), TyKind::Float(b)) => a == hir::FloatTy::F32 && b == hir::FloatTy::F64,
        _ => false,
    }
}
