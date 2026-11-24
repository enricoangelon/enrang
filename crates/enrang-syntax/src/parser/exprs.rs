//! SPEC 3.4 expressions by Pratt parsing over SPEC 3.5's levels: arrows, assignment,
//! the ternary, `??`, the binary levels, `as`, prefix and postfix operators, type
//! arguments by speculation, literals, named-form literals, `match`, `sizeOf`,
//! `alignOf`, `offsetOf` and `asm`, and array spread, the one consumer of `...`.
//!
//! Disambiguation (SPEC 3.4): a `<` with no space before it, after a path or a
//! member, starts type arguments only if they parse and are followed by `(`, `.` or
//! a same-line `{`; a path or `TypeMember` followed by `{` on the same line starts a
//! named-form literal; `(...) =>` and `x =>` start arrows, and `(...): T =>` only
//! where `(` starts an expression, and in a ternary's first branch only if a `:`
//! follows the arrow's body.

use enrang_base::{BytePos, Span, intern};
use enrang_diag::{Code, Diagnostic, Edit, Help};

use super::{Guess, Parser, Scope, hints, is_named};
use crate::ast::{
    ArmBody, ArmValue, ArrayElem, ArrowBody, ArrowFn, ArrowParam, AsmExpr, AsmOption,
    AsmOptionKind, AssignOp, BinOp, Expr, ExprKind, FieldInit, Ident, LogOp, MatchArm, NewInit,
    RegBinding, RetType, SizeForm, StrLit, TplPart, TypeExpr, TypeExprKind, UnOp,
};
use crate::token::{Keyword, Punct, Reserved, Token, TokenKind};

/// A binary operator of SPEC 3.5 levels 4 to 13, and the TypeScript operators
/// that recover as something else: `**` as a call of `pow` (EN1022), and
/// `instanceof`, dropped with its type (EN0211).
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(super) enum Op {
    Bin(BinOp),
    Log(LogOp),
    Pow,
    InstanceOf,
}

/// The outcome of one postfix step: the longer expression, or the same one when no
/// postfix operator follows.
enum Step {
    Next(Expr),
    Stop(Expr),
}

/// What ended a template hole that did not end where it should.
enum HoleEnd {
    Middle(enrang_base::Symbol),
    Tail(enrang_base::Symbol),
}

impl Parser<'_> {
    /// `Expr = ArrowFn | Assign`.
    pub(super) fn parse_expr(&mut self) -> Expr {
        self.parse_expr_in(false)
    }

    /// `parse_expr` for the first branch of a ternary when `ternary_then`, where an
    /// annotated arrow must be followed by the `:` of the ternary and `x : T =>` is
    /// no arrow. The flag goes on along the branch's right edge, to an arrow's body,
    /// an assignment's value and a nested ternary's second branch, which end at that
    /// `:` too, as TypeScript's parser carries it: `c ? (a) => b : d => e` is a
    /// choice between two arrows (SPEC 3.4).
    fn parse_expr_in(&mut self, ternary_then: bool) -> Expr {
        if !self.enter() {
            return self.error_expr();
        }
        let expr = match self.try_arrow(ternary_then) {
            Some(arrow) => arrow,
            None => self.parse_assign_in(ternary_then),
        };
        self.leave();
        expr
    }

    /// An arrow function, if one starts here.
    pub(super) fn try_arrow(&mut self, ternary_then: bool) -> Option<Expr> {
        let lo = self.lo();
        match self.peek().kind {
            TokenKind::Ident(_) if self.nth_is(1, Punct::FatArrow) => {
                let name = self.ident_or_error();
                self.bump();
                let param = ArrowParam {
                    is_let: false,
                    name,
                    ty: None,
                };
                Some(self.finish_arrow_in(lo, vec![param], None, ternary_then))
            }
            // `x: T => ...`, never in a ternary's first branch, where `c ? x : y => z`
            // is `c ? x : (y => z)`.
            TokenKind::Ident(_) if !ternary_then && self.nth_is(1, Punct::Colon) => {
                let (name, ty) = self.speculate_as(Guess::BareArrow, |p| {
                    let name = p.ident()?;
                    p.bump();
                    let ty = p.parse_type();
                    p.at(Punct::FatArrow).then_some((name, ty))
                })?;
                self.bare_return_type(&name, &ty);
                self.bump();
                let param = ArrowParam {
                    is_let: false,
                    name,
                    ty: None,
                };
                let ret = RetType {
                    readonly: false,
                    ty,
                };
                Some(self.finish_arrow(lo, vec![param], Some(ret)))
            }
            TokenKind::Punct(Punct::LParen) => {
                let close = self.matching_close(self.pos)?;
                if !self.tokens[close].is(Punct::RParen) {
                    return None;
                }
                let after = *self.tokens.get(close + 1)?;
                if after.is(Punct::FatArrow) {
                    let (params, ret) = self.parse_arrow_head();
                    return Some(self.finish_arrow_in(lo, params, ret, ternary_then));
                }
                if !after.is(Punct::Colon) {
                    return None;
                }
                if ternary_then {
                    self.speculate_as(Guess::TernaryArrow, |p| {
                        let (params, ret) = p.parse_arrow_head();
                        let arrow = p.finish_arrow_in(lo, params, ret, true);
                        p.at(Punct::Colon).then_some(arrow)
                    })
                } else {
                    let (params, ret) =
                        self.speculate_as(Guess::ArrowHead, |p| Some(p.parse_arrow_head()))?;
                    Some(self.finish_arrow(lo, params, ret))
                }
            }
            _ => None,
        }
    }

    /// EN0224: `x: T =>`, a return type after a bare parameter, with SPEC 3.4's
    /// two helps, one for each thing `T` may have meant.
    fn bare_return_type(&mut self, name: &Ident, ty: &TypeExpr) {
        let colon = Span {
            lo: name.span.hi,
            hi: ty.span.hi,
        };
        let colon = self
            .op_between(name.span.hi, ty.span.lo, ":")
            .map_or(colon, |at| at.to(ty.span));
        let ty_text = self.text(ty.span);
        let name_text = name.name.as_str();
        self.emit(
            Diagnostic::new(
                Code::EN0224,
                "a return type needs the arrow's parameters in parentheses",
                colon,
                "a type after a bare parameter",
            )
            .with_help(Help::suggest(
                format!(
                    "if `{ty_text}` is the parameter's type: `({name_text}: {ty_text}) => ...`"
                ),
                vec![
                    Edit::insert(name.span.lo, "("),
                    Edit::insert(ty.span.hi, ")"),
                ],
            ))
            .with_help(Help::suggest(
                format!("if `{ty_text}` is the return type: `({name_text}): {ty_text} => ...`"),
                vec![
                    Edit::insert(name.span.lo, "("),
                    Edit::insert(name.span.hi, ")"),
                ],
            )),
        );
    }

    /// `"(" ArrowParam % "," ")" [ ":" RetType ] "=>"`, from the `(`.
    fn parse_arrow_head(&mut self) -> (Vec<ArrowParam>, Option<RetType>) {
        self.bump();
        let params = self.comma_list(Punct::RParen, |p| {
            if p.at(Punct::DotDotDot) {
                hints::spread_outside_array(p);
            }
            let is_let = p.eat_kw(Keyword::Let);
            let name = p.ident()?;
            let ty = p.eat(Punct::Colon).then(|| p.parse_type());
            Some(ArrowParam { is_let, name, ty })
        });
        let ret = self.eat(Punct::Colon).then(|| self.parse_ret_type());
        self.expect(Punct::FatArrow);
        (params, ret)
    }

    /// The body after `=>`: a `{` there always starts a block (SPEC 3.4).
    pub(super) fn finish_arrow(
        &mut self,
        lo: BytePos,
        params: Vec<ArrowParam>,
        ret: Option<RetType>,
    ) -> Expr {
        self.finish_arrow_in(lo, params, ret, false)
    }

    /// `finish_arrow` in the first branch of a ternary when `ternary_then`.
    fn finish_arrow_in(
        &mut self,
        lo: BytePos,
        params: Vec<ArrowParam>,
        ret: Option<RetType>,
        ternary_then: bool,
    ) -> Expr {
        // `break` and `continue` in the body cannot reach a loop outside it.
        let head = self.span_from(lo);
        let body = self.within(Scope::Arrow(head), |p| {
            if p.at(Punct::LBrace) {
                ArrowBody::Block(p.parse_block())
            } else {
                ArrowBody::Expr(Box::new(p.parse_expr_in(ternary_then)))
            }
        });
        let span = self.span_from(lo);
        let arrow = ArrowFn {
            params,
            ret,
            body,
            span,
        };
        self.mk_expr(ExprKind::Arrow(arrow), span)
    }

    /// `Assign = Ternary [ AssignOp Expr ]`, right-associative.
    fn parse_assign(&mut self) -> Expr {
        self.parse_assign_in(false)
    }

    /// `parse_assign` in the first branch of a ternary when `ternary_then`.
    fn parse_assign_in(&mut self, ternary_then: bool) -> Expr {
        let lo = self.lo();
        let target = self.parse_ternary_in(ternary_then);
        let op = match self.peek().kind {
            TokenKind::Punct(punct) => AssignOp::from_punct(punct),
            _ => None,
        };
        let Some(op) = op else {
            return target;
        };
        self.bump();
        if op == AssignOp::Assign {
            self.spread_in_pattern(&target);
        }
        self.check_target(&target, op == AssignOp::Assign, "assign to");
        let value = self.parse_expr_in(ternary_then);
        let span = self.span_from(lo);
        self.mk_expr(
            ExprKind::Assign {
                op,
                target: Box::new(target),
                value: Box::new(value),
            },
            span,
        )
    }

    /// EN1013 at each spread of an array literal on the left of `=`, which is a
    /// pattern there, not a literal (SPEC 3.4).
    fn spread_in_pattern(&mut self, target: &Expr) {
        match &target.kind {
            ExprKind::Array(elems) => {
                for elem in elems {
                    match elem {
                        ArrayElem::Spread { dots, .. } => hints::report_spread(self, *dots),
                        ArrayElem::Item(item) => self.spread_in_pattern(item),
                    }
                }
            }
            ExprKind::ObjectLit(fields) => {
                for value in fields.iter().filter_map(|field| field.value.as_ref()) {
                    self.spread_in_pattern(value);
                }
            }
            ExprKind::Paren(inner) => self.spread_in_pattern(inner),
            _ => {}
        }
    }

    /// EN0114 unless `target` is a place: a name, a field, an element, a
    /// dereference or a `!` assertion, in parentheses or not; after `=` (when
    /// `pattern`) also a tuple or object pattern of places. An array holding a
    /// spread has EN1013 instead (SPEC 3.4), and a default inside a pattern is
    /// EN1010.
    pub(super) fn check_target(&mut self, target: &Expr, pattern: bool, verb: &str) {
        match &target.kind {
            ExprKind::Ident(_)
            | ExprKind::Index(..)
            | ExprKind::Deref(_)
            | ExprKind::NonNull(_)
            | ExprKind::Error
            | ExprKind::Member {
                optional: false, ..
            } => {}
            ExprKind::Paren(inner) => self.check_target(inner, pattern, verb),
            ExprKind::Array(elems) if pattern => {
                if elems
                    .iter()
                    .any(|elem| matches!(elem, ArrayElem::Spread { .. }))
                {
                    return;
                }
                for elem in elems {
                    if let ArrayElem::Item(part) = elem {
                        self.check_pattern_part(part);
                    }
                }
            }
            ExprKind::ObjectLit(fields) if pattern => {
                for value in fields.iter().filter_map(|field| field.value.as_ref()) {
                    self.check_pattern_part(value);
                }
            }
            // `x ||= y` read as `x || <error> = y` after its EN0100 is no second
            // mistake.
            ExprKind::Binary(_, left, right)
            | ExprKind::Logical(_, left, right)
            | ExprKind::Coalesce(left, right)
                if [left, right]
                    .iter()
                    .any(|operand| matches!(operand.kind, ExprKind::Error)) => {}
            kind => {
                let what = match kind {
                    ExprKind::Call { .. } => "a call's result",
                    ExprKind::Int { .. }
                    | ExprKind::Float(_)
                    | ExprKind::Str(_)
                    | ExprKind::Template(_)
                    | ExprKind::RawTemplate(_)
                    | ExprKind::Bool(_)
                    | ExprKind::Null => "a literal",
                    ExprKind::This => "`this`",
                    ExprKind::Member { optional: true, .. } => "an optional member access",
                    ExprKind::Assign { .. } => "an assignment",
                    _ => "this expression",
                };
                self.emit(Diagnostic::new(
                    Code::EN0114,
                    format!("cannot {verb} {what}"),
                    target.span,
                    "not a variable, field, element or dereference",
                ));
            }
        }
    }

    /// A part of a pattern on the left of `=`: a place, a nested pattern, or
    /// `a = 1`, a default (EN1010).
    fn check_pattern_part(&mut self, part: &Expr) {
        if let ExprKind::Assign {
            op: AssignOp::Assign,
            target,
            value,
        } = &part.kind
        {
            let eq = self
                .op_between(target.span.hi, value.span.lo, "=")
                .unwrap_or(part.span);
            hints::report_deferred(self, Code::EN1010, eq, "a default in a pattern");
            self.check_target(target, true, "assign to");
            return;
        }
        self.check_target(part, true, "assign to");
    }

    /// EN0105 when `expr`, through parentheses, is an assignment used as `what`:
    /// a condition, or an operand of `&&`, `||` or `!`. A plain `=` gets a fix-it
    /// to `==`.
    pub(super) fn check_assignment(&mut self, expr: &Expr, what: &str) {
        let mut inner = expr;
        while let ExprKind::Paren(e) = &inner.kind {
            inner = e;
        }
        let ExprKind::Assign { op, target, value } = &inner.kind else {
            return;
        };
        let mut diag = Diagnostic::new(
            Code::EN0105,
            format!("assignment used as {what}"),
            inner.span,
            "this assigns; it does not compare",
        );
        if *op == AssignOp::Assign
            && let Some(eq) = self.op_between(target.span.hi, value.span.lo, "=")
        {
            diag = diag.with_help(Help::machine(
                "compare with `==`",
                vec![Edit::replace(eq, "==")],
            ));
        }
        self.emit(diag);
    }

    /// Whether the current `?`, which has no space before it, starts a ternary
    /// anyway: the next token has a space before it, starts an operand and is no
    /// binary operator, and a `:` follows before the expression ends (EN0103).
    fn spaceless_ternary(&self) -> bool {
        let next = self.nth(1);
        if !next.space_before || !hints::can_start_operand(next) || hints::is_binary_operator(next)
        {
            return false;
        }
        let mut depth = 0usize;
        let end = (self.pos + 257).min(self.tokens.len());
        for index in self.pos + 1..end {
            match self.tokens[index].kind {
                TokenKind::Punct(Punct::LParen | Punct::LBracket | Punct::LBrace) => depth += 1,
                TokenKind::Punct(Punct::RParen | Punct::RBracket | Punct::RBrace) => {
                    if depth == 0 {
                        return false;
                    }
                    depth -= 1;
                }
                TokenKind::Punct(Punct::Semi | Punct::Comma) if depth == 0 => return false,
                TokenKind::Punct(Punct::Colon) if depth == 0 => return true,
                TokenKind::Eof => return false,
                _ => {}
            }
        }
        false
    }

    /// Whether the current `?` or `!`, which has a space before it, is postfix
    /// anyway: nothing after it can start an operand (EN0103).
    fn spaced_postfix(&self) -> bool {
        !hints::can_start_operand(self.nth(1))
    }

    /// `Ternary = Coalesce [ "?" Expr ":" Expr ]`. A ternary `?` has a space or a
    /// line break before it; one with none is postfix (SPEC 2), unless only a
    /// ternary can follow it, which is EN0103 with a fix-it adding the space.
    fn parse_ternary(&mut self) -> Expr {
        self.parse_ternary_in(false)
    }

    /// `parse_ternary` in the first branch of another ternary when `ternary_then`.
    fn parse_ternary_in(&mut self, ternary_then: bool) -> Expr {
        let lo = self.lo();
        let cond = self.parse_coalesce();
        let token = self.peek();
        if !token.is(Punct::Question) {
            return cond;
        }
        if !token.space_before {
            if !self.spaceless_ternary() {
                return cond;
            }
            self.emit(
                Diagnostic::new(
                    Code::EN0103,
                    "a ternary `?` needs a space before it",
                    token.span,
                    "this `?` starts a choice",
                )
                .note("with no space before it, `?` passes an error or `null` up, as in `f()?`")
                .with_help(Help::machine(
                    "add a space before `?`",
                    vec![Edit::insert(token.span.lo, " ")],
                )),
            );
        }
        self.check_assignment(&cond, "a condition");
        self.bump();
        let then = self.parse_expr_in(true);
        let other = if self.eat(Punct::Colon) {
            self.parse_expr_in(ternary_then)
        } else {
            let span = self.peek().span;
            self.unexpected(span, "expected `:` to finish the choice", "expected `:`");
            self.error_expr()
        };
        let span = self.span_from(lo);
        self.mk_expr(
            ExprKind::Ternary(Box::new(cond), Box::new(then), Box::new(other)),
            span,
        )
    }

    /// `Coalesce = LogOr [ "??" Coalesce ]`, right-associative.
    fn parse_coalesce(&mut self) -> Expr {
        let lo = self.lo();
        let lhs = self.parse_binary(LogOp::Or.precedence());
        if !self.at(Punct::QuestionQuestion) || !self.enter() {
            return lhs;
        }
        let qq = self.bump();
        let rhs = self.parse_coalesce();
        self.leave();
        self.check_coalesce(qq.span, &lhs, &rhs);
        let span = self.span_from(lo);
        self.mk_expr(ExprKind::Coalesce(Box::new(lhs), Box::new(rhs)), span)
    }

    /// EN0106 when an operand of `??` is an unparenthesised `&&` or `||`.
    fn check_coalesce(&mut self, qq: Span, lhs: &Expr, rhs: &Expr) {
        let logical: Vec<(LogOp, Span)> = [lhs, rhs]
            .into_iter()
            .filter_map(|operand| match operand.kind {
                ExprKind::Logical(op, ..) => Some((op, operand.span)),
                _ => None,
            })
            .collect();
        let Some(&(op, _)) = logical.first() else {
            return;
        };
        let op = op.as_str();
        let edits = logical
            .iter()
            .flat_map(|&(_, span)| [Edit::insert(span.lo, "("), Edit::insert(span.hi, ")")])
            .collect();
        self.emit(
            Diagnostic::new(
                Code::EN0106,
                format!("`??` and `{op}` cannot mix without parentheses"),
                qq,
                format!("this `??` mixes with `{op}`"),
            )
            .with_help(Help::suggest(format!("parenthesise the `{op}`"), edits)),
        );
    }

    /// EN0107 when `lhs` is an unparenthesised comparison of the same level as
    /// `op`, at `token`: `a < b < c` and `a == b != c` do not associate. A
    /// comparison with an `Error` operand is what recovery read after an EN0100, as
    /// `<i64>value` is, so it is no second mistake.
    fn check_chain(&mut self, token: Token, op: BinOp, lhs: &Expr) {
        let ExprKind::Binary(first, left, middle) = &lhs.kind else {
            return;
        };
        if first.precedence() != op.precedence() {
            return;
        }
        if [left, middle]
            .iter()
            .any(|operand| matches!(operand.kind, ExprKind::Error))
        {
            return;
        }
        let middle_text = self.text(middle.span).to_owned();
        self.emit(
            Diagnostic::new(
                Code::EN0107,
                "comparisons cannot be chained",
                token.span,
                "this compares the result of the comparison before it",
            )
            .note(format!(
                "`{}` is a `bool`, which is not compared with `{}`",
                self.text(lhs.span),
                op.as_str()
            ))
            .with_help(Help::suggest(
                "compare each pair, joined by `&&`",
                vec![Edit::insert(middle.span.hi, format!(" && {middle_text}"))],
            )),
        );
    }

    /// Levels 3 to `max` of SPEC 3.5, left-associative. Levels 7 and 8 do not
    /// associate; a chain of them parses left to right, and is EN0107. `**` is a
    /// TypeScript operator at level 3, right-associative (EN1022).
    fn parse_binary(&mut self, max: u8) -> Expr {
        let lo = self.lo();
        let mut lhs = self.parse_cast();
        let mut links = 0;
        while let Some((prec, op)) = self.binary_op() {
            if prec > max || !self.enter_link() {
                break;
            }
            links += 1;
            let token = self.bump();
            if op == Op::InstanceOf {
                hints::instanceof(self, token);
                continue;
            }
            let rhs = if op == Op::Pow {
                self.parse_binary(prec)
            } else {
                self.parse_binary(prec - 1)
            };
            hints::binary_found(self, token, &lhs, &rhs);
            let kind = match op {
                Op::Bin(op) => {
                    if op.is_comparison() {
                        self.check_chain(token, op, &lhs);
                    }
                    ExprKind::Binary(op, Box::new(lhs), Box::new(rhs))
                }
                Op::Log(op) => {
                    let what = format!("an operand of `{}`", op.as_str());
                    self.check_assignment(&lhs, &what);
                    self.check_assignment(&rhs, &what);
                    ExprKind::Logical(op, Box::new(lhs), Box::new(rhs))
                }
                Op::Pow | Op::InstanceOf => {
                    let name = Ident {
                        name: intern("pow"),
                        span: token.span,
                    };
                    let member_span = lhs.span.to(token.span);
                    let callee = self.mk_expr(
                        ExprKind::Member {
                            base: Box::new(lhs),
                            name,
                            optional: false,
                        },
                        member_span,
                    );
                    ExprKind::Call {
                        callee: Box::new(callee),
                        type_args: Vec::new(),
                        args: vec![rhs],
                    }
                }
            };
            let span = self.span_from(lo);
            lhs = self.mk_expr(kind, span);
        }
        self.links -= links;
        lhs
    }

    /// The binary operator the current token spells, with its level.
    fn binary_op(&mut self) -> Option<(u8, Op)> {
        let token = self.peek();
        if let TokenKind::Punct(punct) = token.kind {
            if let Some(op) = LogOp::from_punct(punct) {
                return Some((op.precedence(), Op::Log(op)));
            }
            if let Some(op) = BinOp::from_punct(punct) {
                return Some((op.precedence(), Op::Bin(op)));
            }
        }
        hints::binary_habit(token)
    }

    /// `Cast = Unary { "as" PrefixType }`.
    fn parse_cast(&mut self) -> Expr {
        let lo = self.lo();
        let mut expr = self.parse_unary();
        let mut links = 0;
        while self.at_kw(Keyword::As) && self.enter_link() {
            links += 1;
            let keyword = self.bump();
            if self.at_kw(Keyword::Const) {
                let word = self.bump();
                hints::report_deferred(
                    self,
                    Code::EN1039,
                    keyword.span.to(word.span),
                    "`as const`",
                );
                continue;
            }
            let ty = self.parse_cast_type();
            let span = self.span_from(lo);
            expr = self.mk_expr(ExprKind::Cast(Box::new(expr), ty), span);
        }
        self.links -= links;
        expr
    }

    /// `Unary = ("!" | "-" | "~" | "*" | "&" | "++" | "--" | "void") Unary | Postfix`;
    /// `**` and `&&` here are two operators each (SPEC 2).
    pub(super) fn parse_unary(&mut self) -> Expr {
        if !self.enter() {
            return self.error_expr();
        }
        let expr = self.parse_unary_inner();
        self.leave();
        expr
    }

    fn parse_unary_inner(&mut self) -> Expr {
        let lo = self.lo();
        if matches!(
            self.peek().kind,
            TokenKind::Punct(Punct::StarStar | Punct::AmpAmp)
        ) {
            self.split_current();
        }
        let token = self.peek();
        let kind = match token.kind {
            TokenKind::Punct(Punct::DotDotDot) => {
                hints::spread_outside_array(self);
                return self.parse_unary();
            }
            TokenKind::Punct(
                punct @ (Punct::Bang
                | Punct::Minus
                | Punct::Tilde
                | Punct::Star
                | Punct::Amp
                | Punct::PlusPlus
                | Punct::MinusMinus),
            ) => {
                self.bump();
                let operand = Box::new(self.parse_unary());
                match punct {
                    Punct::Bang => self.check_assignment(&operand, "an operand of `!`"),
                    Punct::PlusPlus => self.check_target(&operand, false, "increment"),
                    Punct::MinusMinus => self.check_target(&operand, false, "decrement"),
                    _ => {}
                }
                match punct {
                    Punct::Bang => ExprKind::Unary(UnOp::Not, operand),
                    Punct::Minus => ExprKind::Unary(UnOp::Neg, operand),
                    Punct::Tilde => ExprKind::Unary(UnOp::BitNot, operand),
                    Punct::Star => ExprKind::Deref(operand),
                    Punct::Amp => ExprKind::Borrow(operand),
                    _ => ExprKind::IncDec {
                        target: operand,
                        inc: punct == Punct::PlusPlus,
                        prefix: true,
                    },
                }
            }
            TokenKind::Keyword(Keyword::Void) => {
                self.bump();
                ExprKind::VoidOp(Box::new(self.parse_unary()))
            }
            _ => return self.parse_postfix(),
        };
        let span = self.span_from(lo);
        self.mk_expr(kind, span)
    }

    /// `Postfix = Primary { "." MemberName | "?." MemberName | "[" Expr "]" |
    /// CallArgs | "?" | "!" | "++" | "--" }`, with `TypeMember` and named-form
    /// literals.
    fn parse_postfix(&mut self) -> Expr {
        let lo = self.lo();
        let mut expr = self.parse_primary();
        let mut links = 0;
        loop {
            match self.postfix_step(lo, expr) {
                Step::Next(next) => {
                    expr = next;
                    links += 1;
                }
                Step::Stop(last) => {
                    expr = last;
                    break;
                }
            }
        }
        self.links -= links;
        expr
    }

    /// One postfix operation on `expr`, or `expr` back when none follows. Each one
    /// taken is a chain link, which `parse_postfix` gives back.
    fn postfix_step(&mut self, lo: BytePos, expr: Expr) -> Step {
        let token = self.peek();
        let starts = match token.kind {
            TokenKind::Punct(Punct::Dot | Punct::QuestionDot | Punct::LBracket | Punct::LParen) => {
                true
            }
            // As in TypeScript, a postfix `++` or `--` is on its operand's line; one
            // on the next line starts the next statement, after a missing `;`.
            TokenKind::Punct(Punct::PlusPlus | Punct::MinusMinus) => {
                !self.line_break_before(self.pos)
            }
            // Postfix `?` and `!` have no space before them, a ternary `?` has one
            // (SPEC 2); a spacing only the other reading fits is EN0103.
            TokenKind::Punct(Punct::Question) if token.space_before => self.spaced_postfix(),
            TokenKind::Punct(Punct::Question) => !self.spaceless_ternary(),
            TokenKind::Punct(Punct::Bang) => !token.space_before || self.spaced_postfix(),
            TokenKind::Punct(Punct::Lt) => {
                !token.space_before
                    && (path_of(&expr).is_some() || matches!(expr.kind, ExprKind::Member { .. }))
            }
            TokenKind::Punct(Punct::LBrace) => {
                !self.line_break_before(self.pos) && names_a_case(&expr)
            }
            _ => false,
        };
        if !starts || !self.enter_link() {
            return Step::Stop(expr);
        }
        let step = self.postfix_op(lo, expr, token);
        if matches!(step, Step::Stop(_)) {
            self.links -= 1;
        }
        step
    }

    fn postfix_op(&mut self, lo: BytePos, expr: Expr, token: Token) -> Step {
        let kind = match token.kind {
            TokenKind::Punct(Punct::Dot | Punct::QuestionDot) => {
                self.bump();
                let name = self.member_name().unwrap_or_else(|| self.error_ident());
                ExprKind::Member {
                    base: Box::new(expr),
                    name,
                    optional: token.is(Punct::QuestionDot),
                }
            }
            TokenKind::Punct(Punct::LBracket) => {
                if self.nth_is(1, Punct::RBracket)
                    && let Some(path) = path_of(&expr)
                {
                    // `TypeMember = NamedType "[" "]" "." MemberName`: `i64[].withCapacity`.
                    self.bump();
                    self.bump();
                    let named = self.mk_ty(
                        TypeExprKind::Named {
                            path,
                            args: Vec::new(),
                        },
                        expr.span,
                    );
                    let span = self.span_from(lo);
                    let array = self.mk_ty(TypeExprKind::Array(Box::new(named)), span);
                    return Step::Next(self.type_member(lo, array));
                }
                self.bump();
                let index = self.parse_expr();
                self.expect(Punct::RBracket);
                ExprKind::Index(Box::new(expr), Box::new(index))
            }
            TokenKind::Punct(Punct::LParen) => {
                let args = self.parse_call_args();
                ExprKind::Call {
                    callee: Box::new(expr),
                    type_args: Vec::new(),
                    args,
                }
            }
            TokenKind::Punct(Punct::Lt) => {
                let is_path = path_of(&expr).is_some();
                let kind = if is_path {
                    Guess::PathTypeArgs
                } else {
                    Guess::MemberTypeArgs
                };
                return match self.speculate_as(kind, |p| p.type_args_after(is_path)) {
                    Some(args) => Step::Next(self.after_type_args(lo, expr, args)),
                    None => Step::Stop(expr),
                };
            }
            TokenKind::Punct(punct @ (Punct::Question | Punct::Bang)) => {
                if token.space_before {
                    self.spaced_postfix_found(token, punct);
                }
                self.bump();
                if punct == Punct::Question {
                    ExprKind::Try(Box::new(expr))
                } else {
                    ExprKind::NonNull(Box::new(expr))
                }
            }
            TokenKind::Punct(Punct::PlusPlus | Punct::MinusMinus) => {
                let verb = if token.is(Punct::PlusPlus) {
                    "increment"
                } else {
                    "decrement"
                };
                self.check_target(&expr, false, verb);
                self.bump();
                ExprKind::IncDec {
                    target: Box::new(expr),
                    inc: token.is(Punct::PlusPlus),
                    prefix: false,
                }
            }
            TokenKind::Punct(Punct::LBrace) => {
                let (path, args) = case_head(expr);
                self.bump();
                let fields = self.comma_list(Punct::RBrace, |p| p.parse_field_init());
                ExprKind::CaseLit { path, args, fields }
            }
            _ => return Step::Stop(expr),
        };
        let span = self.span_from(lo);
        Step::Next(self.mk_expr(kind, span))
    }

    /// EN0103 at a postfix `?` or `!` with a space before it, the current token,
    /// with a fix-it that removes the space.
    fn spaced_postfix_found(&mut self, token: Token, punct: Punct) {
        let gap = self.gap_before_current();
        let (mark, label, note) = if punct == Punct::Question {
            (
                "?",
                "this `?` passes an error or `null` up",
                Some("with a space before it, `?` starts a choice, `a ? b : c`"),
            )
        } else {
            ("!", "this `!` asserts that the value is not `null`", None)
        };
        let mut diag = Diagnostic::new(
            Code::EN0103,
            format!("a postfix `{mark}` takes no space before it"),
            token.span,
            label,
        );
        if let Some(note) = note {
            diag = diag.note(note);
        }
        self.emit(diag.with_help(Help::machine(
            format!("remove the space before `{mark}`"),
            vec![Edit::delete(gap)],
        )));
    }

    /// Type arguments after a path or member, from the `<`, and whether what follows
    /// lets them be arguments: `(`, or after a path `.`, `[` `]` `.`, or a `{` on the
    /// same line.
    fn type_args_after(&mut self, is_path: bool) -> Option<Vec<TypeExpr>> {
        let args = self.parse_type_args();
        let next = self.peek();
        let member = next.is(Punct::Dot)
            || (next.is(Punct::LBracket)
                && self.nth_is(1, Punct::RBracket)
                && self.nth_is(2, Punct::Dot));
        let literal = next.is(Punct::LBrace) && !self.line_break_before(self.pos);
        let fits = next.is(Punct::LParen) || (is_path && (member || literal));
        fits.then_some(args)
    }

    /// What type arguments attach to (SPEC 3.4): a call, a `TypeMember`, or the head
    /// of a named-form literal. Never a member access: `x.wrap<u8>()` is a call of
    /// `x.wrap`.
    fn after_type_args(&mut self, lo: BytePos, expr: Expr, args: Vec<TypeExpr>) -> Expr {
        if self.at(Punct::LParen) {
            let call_args = self.parse_call_args();
            let span = self.span_from(lo);
            return self.mk_expr(
                ExprKind::Call {
                    callee: Box::new(expr),
                    type_args: args,
                    args: call_args,
                },
                span,
            );
        }
        let path = path_of(&expr).unwrap_or_default();
        if self.at(Punct::LBrace) {
            self.bump();
            let fields = self.comma_list(Punct::RBrace, |p| p.parse_field_init());
            let span = self.span_from(lo);
            return self.mk_expr(ExprKind::CaseLit { path, args, fields }, span);
        }
        let span = self.span_from(lo);
        let mut ty = self.mk_ty(TypeExprKind::Named { path, args }, span);
        if self.at(Punct::LBracket) {
            self.bump();
            self.bump();
            let span = self.span_from(lo);
            ty = self.mk_ty(TypeExprKind::Array(Box::new(ty)), span);
        }
        self.type_member(lo, ty)
    }

    /// `"." MemberName` after the type of a `TypeMember`.
    fn type_member(&mut self, lo: BytePos, ty: TypeExpr) -> Expr {
        let name = if self.expect(Punct::Dot) {
            self.member_name().unwrap_or_else(|| self.error_ident())
        } else {
            self.error_ident()
        };
        let span = self.span_from(lo);
        self.mk_expr(ExprKind::TypeMember { ty, name }, span)
    }

    /// `"(" Expr % "," ")"`, from the `(`.
    pub(super) fn parse_call_args(&mut self) -> Vec<Expr> {
        self.bump();
        self.comma_list(Punct::RParen, |p| Some(p.parse_expr()))
    }

    /// `Primary` (SPEC 3.4).
    pub(super) fn parse_primary(&mut self) -> Expr {
        let lo = self.lo();
        let token = self.peek();
        let kind = match token.kind {
            TokenKind::Int { value, text } => {
                self.bump();
                ExprKind::Int { value, text }
            }
            TokenKind::Float(text) => {
                self.bump();
                ExprKind::Float(text)
            }
            TokenKind::Str(value) => {
                self.bump();
                ExprKind::Str(value)
            }
            TokenKind::NoSubTemplate(text) => {
                self.bump();
                ExprKind::Template(vec![TplPart::Str(text)])
            }
            TokenKind::TemplateHead(_) => return self.parse_template(),
            TokenKind::RawTemplate(text) => {
                self.bump();
                ExprKind::RawTemplate(text)
            }
            TokenKind::Keyword(Keyword::True) => {
                self.bump();
                ExprKind::Bool(true)
            }
            TokenKind::Keyword(Keyword::False) => {
                self.bump();
                ExprKind::Bool(false)
            }
            TokenKind::Keyword(Keyword::Null) => {
                self.bump();
                ExprKind::Null
            }
            TokenKind::Keyword(Keyword::This) => {
                self.bump();
                ExprKind::This
            }
            TokenKind::Keyword(Keyword::Super) => {
                self.bump();
                if !self.at(Punct::LParen) && !self.at(Punct::Dot) {
                    self.expected("`(` or `.` after `super`");
                }
                ExprKind::Super
            }
            TokenKind::Ident(name)
                if ["sizeOf", "alignOf", "offsetOf"].contains(&name.as_str())
                    && self.nth_is(1, Punct::Lt)
                    && !self.nth(1).space_before =>
            {
                return self.parse_size_form();
            }
            TokenKind::Ident(name)
                if name.as_str() == "require" && self.nth_is(1, Punct::LParen) =>
            {
                return hints::require_call(self);
            }
            TokenKind::Ident(name) => {
                self.bump();
                ExprKind::Ident(name)
            }
            TokenKind::Punct(Punct::LParen) => {
                self.bump();
                let inner = self.parse_expr();
                self.expect(Punct::RParen);
                ExprKind::Paren(Box::new(inner))
            }
            TokenKind::Punct(Punct::LBracket) => return self.parse_array(),
            TokenKind::Punct(Punct::LBrace) => {
                self.bump();
                ExprKind::ObjectLit(self.comma_list(Punct::RBrace, |p| p.parse_field_init()))
            }
            TokenKind::Keyword(Keyword::New) => return self.parse_new(),
            TokenKind::Keyword(Keyword::Match) => return self.parse_match(),
            TokenKind::Keyword(Keyword::Asm) => return self.parse_asm(),
            _ => {
                if let Some(expr) = hints::expr_start(self) {
                    return expr;
                }
                self.expected("an expression");
                return self.error_expr();
            }
        };
        let span = self.span_from(lo);
        self.mk_expr(kind, span)
    }

    /// `TemplateLit` with holes: the text pieces and the holes, alternating, from
    /// the first piece to the last, empty pieces included.
    fn parse_template(&mut self) -> Expr {
        let lo = self.lo();
        let TokenKind::TemplateHead(head) = self.bump().kind else {
            return self.error_expr();
        };
        let mut parts = vec![TplPart::Str(head)];
        loop {
            let hole = self.parse_expr();
            parts.push(TplPart::Expr(hole));
            let end = match self.peek().kind {
                TokenKind::TemplateMiddle(text) => {
                    self.bump();
                    Some(HoleEnd::Middle(text))
                }
                TokenKind::TemplateTail(text) => {
                    self.bump();
                    Some(HoleEnd::Tail(text))
                }
                _ => {
                    self.expected("`}` to close the hole");
                    self.skip_to_hole_end()
                }
            };
            match end {
                Some(HoleEnd::Middle(text)) => parts.push(TplPart::Str(text)),
                Some(HoleEnd::Tail(text)) => {
                    parts.push(TplPart::Str(text));
                    break;
                }
                None => break,
            }
        }
        let span = self.span_from(lo);
        self.mk_expr(ExprKind::Template(parts), span)
    }

    /// Skips to the end of the current hole, past templates nested in it, and
    /// consumes it. The lexer closes every template, so only a broken stream ends
    /// the file first.
    fn skip_to_hole_end(&mut self) -> Option<HoleEnd> {
        let mut nested = 0usize;
        loop {
            match self.bump().kind {
                TokenKind::Eof => return None,
                TokenKind::TemplateHead(_) => nested += 1,
                TokenKind::TemplateMiddle(text) if nested == 0 => {
                    return Some(HoleEnd::Middle(text));
                }
                TokenKind::TemplateTail(text) if nested == 0 => return Some(HoleEnd::Tail(text)),
                TokenKind::TemplateTail(_) => nested -= 1,
                _ => {}
            }
        }
    }

    /// `SizeForm = ("sizeOf" | "alignOf") "<" Type ">" "(" ")" | "offsetOf" "<" Type
    /// ">" "(" StringLit [ "," ] ")"`.
    fn parse_size_form(&mut self) -> Expr {
        let lo = self.lo();
        let name = self.bump();
        let mut args = self.parse_type_args();
        if args.len() != 1 {
            let span = self.span_from(lo);
            self.unexpected(
                span,
                "expected one type between `<` and `>`",
                "one type here",
            );
        }
        let ty = if args.is_empty() {
            self.error_ty()
        } else {
            args.swap_remove(0)
        };
        self.expect(Punct::LParen);
        let form = if is_named(name, "offsetOf") {
            let field = self.parse_str_lit().unwrap_or(StrLit {
                value: intern(""),
                span: self.here(),
            });
            self.eat(Punct::Comma);
            SizeForm::OffsetOf(ty, field)
        } else if is_named(name, "alignOf") {
            SizeForm::AlignOf(ty)
        } else {
            SizeForm::SizeOf(ty)
        };
        self.expect(Punct::RParen);
        let span = self.span_from(lo);
        self.mk_expr(ExprKind::SizeForm(form), span)
    }

    /// `ArrayLit` or `RepeatLit`. The token after `[` picks the path with no
    /// backtracking: after `...` the literal is a list of elements, so
    /// `[...a; 3]` is EN0100 at `;` (SPEC 3.4).
    fn parse_array(&mut self) -> Expr {
        let lo = self.lo();
        self.bump();
        let kind = if self.at(Punct::DotDotDot) || self.at(Punct::RBracket) {
            ExprKind::Array(self.comma_list(Punct::RBracket, |p| Some(p.parse_array_elem())))
        } else {
            let first = self.parse_expr();
            if self.eat(Punct::Semi) {
                let count = self.parse_expr();
                self.expect(Punct::RBracket);
                ExprKind::Repeat(Box::new(first), Box::new(count))
            } else {
                let mut elems = vec![ArrayElem::Item(first)];
                if self.eat(Punct::Comma) {
                    elems.extend(self.comma_list(Punct::RBracket, |p| Some(p.parse_array_elem())));
                } else if !self.eat(Punct::RBracket) {
                    self.expected("`,`, `;` or `]`");
                    super::recover::skip_until(self, &[Punct::Comma, Punct::RBracket]);
                    if self.eat(Punct::Comma) {
                        elems.extend(
                            self.comma_list(Punct::RBracket, |p| Some(p.parse_array_elem())),
                        );
                    } else {
                        self.eat(Punct::RBracket);
                    }
                }
                ExprKind::Array(elems)
            }
        };
        let span = self.span_from(lo);
        self.mk_expr(kind, span)
    }

    /// `ArrayElem = Expr | "..." Expr`: the only place `...` is consumed.
    fn parse_array_elem(&mut self) -> ArrayElem {
        if self.at(Punct::DotDotDot) {
            let dots = self.bump().span;
            let expr = self.parse_expr();
            ArrayElem::Spread { dots, expr }
        } else {
            ArrayElem::Item(self.parse_expr())
        }
    }

    /// `FieldInit = MemberName [ ":" Expr ]`, in an object literal, a named-form
    /// literal or `new`.
    pub(super) fn parse_field_init(&mut self) -> Option<FieldInit> {
        if self.at(Punct::DotDotDot) {
            hints::spread_outside_array(self);
        }
        let lo = self.lo();
        let name = self.member_name()?;
        let value = self.eat(Punct::Colon).then(|| self.parse_expr());
        let span = self.span_from(lo);
        Some(FieldInit { name, value, span })
    }

    /// `NewExpr = "new" NamedType ( "(" Expr % "," ")" | "{" FieldInit % "," "}" )`,
    /// the `{` on the same line.
    fn parse_new(&mut self) -> Expr {
        let lo = self.lo();
        self.bump();
        if self.at_kw(Keyword::Class) {
            let class = self.peek().span;
            hints::report_deferred(self, Code::EN1037, class, "an anonymous class");
            hints::skip_class(self);
            if self.at(Punct::LParen) {
                self.parse_call_args();
            }
            let span = self.span_from(lo);
            return self.mk_expr(ExprKind::Error, span);
        }
        let ty = self.parse_named_type(false);
        let init = if self.at(Punct::LParen) {
            NewInit::Args(self.parse_call_args())
        } else if self.at(Punct::LBrace) && !self.line_break_before(self.pos) {
            self.bump();
            NewInit::Fields(self.comma_list(Punct::RBrace, |p| p.parse_field_init()))
        } else {
            self.expected("`(` or `{`");
            NewInit::Args(Vec::new())
        };
        let span = self.span_from(lo);
        self.mk_expr(ExprKind::New { ty, init }, span)
    }

    /// `MatchExpr = "match" "(" Expr ")" "{" MatchArm % "," "}"`.
    pub(super) fn parse_match(&mut self) -> Expr {
        let lo = self.lo();
        self.bump();
        let subject = if self.expect(Punct::LParen) {
            let subject = self.parse_expr();
            self.expect(Punct::RParen);
            subject
        } else {
            self.error_expr()
        };
        let arms = if self.expect(Punct::LBrace) {
            self.comma_list(Punct::RBrace, |p| Some(p.parse_arm()))
        } else {
            Vec::new()
        };
        let span = self.span_from(lo);
        self.mk_expr(
            ExprKind::Match {
                subject: Box::new(subject),
                arms,
            },
            span,
        )
    }

    /// `MatchArm = ( "default" | ArmValue { "," ArmValue } ) [ "if" Expr ] "=>" ...`.
    fn parse_arm(&mut self) -> MatchArm {
        let lo = self.lo();
        let mut values = Vec::new();
        let case = self.peek();
        let is_case = case.kind == TokenKind::Reserved(Reserved::Case);
        if is_case {
            self.bump();
            hints::report_case(self, case.span);
        }
        if !self.eat_kw(Keyword::Default) {
            values.push(self.parse_arm_value());
            while self.eat(Punct::Comma) {
                values.push(self.parse_arm_value());
            }
        }
        // The arm's `=>` follows the guard, so `if c => x` is no arrow `c => x`.
        let guard = self.eat_kw(Keyword::If).then(|| self.parse_assign());
        if !(is_case && self.eat(Punct::Colon)) {
            self.expect(Punct::FatArrow);
        }
        let body = self.parse_arm_body();
        let span = self.span_from(lo);
        MatchArm {
            values,
            guard,
            body,
            span,
        }
    }

    /// `ArmValue = Literal | "-" IntLit | "null" | NamedPath | "Ok" | "Err" | Expr
    /// ".." Expr | Expr`. A path of identifiers is always `Case`: only names tell a
    /// case from a constant, so sema decides. An arm value is no arrow and no
    /// assignment, so `x =>` is the arm of `x`.
    pub(super) fn parse_arm_value(&mut self) -> ArmValue {
        let token = self.peek();
        if self.arm_value_ends(1) {
            if token.is_keyword(Keyword::Null) {
                self.bump();
                return ArmValue::Null(token.span);
            }
            if is_named(token, "Ok") {
                self.bump();
                return ArmValue::Ok(token.span);
            }
            if is_named(token, "Err") {
                self.bump();
                return ArmValue::Err(token.span);
            }
        }
        if let Some(len) = self.path_len()
            && self.arm_value_ends(len)
        {
            let mut path = Vec::with_capacity(len / 2 + 1);
            path.push(self.ident_or_error());
            while path.len() * 2 - 1 < len {
                self.bump();
                path.push(self.ident_or_error());
            }
            return ArmValue::Case(path);
        }
        let value = self.parse_ternary();
        if self.eat(Punct::DotDot) {
            let end = self.parse_ternary();
            ArmValue::Range(value, end)
        } else {
            ArmValue::Value(value)
        }
    }

    /// The tokens of `Ident { "." Ident }` from the current token, if one is here.
    fn path_len(&self) -> Option<usize> {
        if !matches!(self.peek().kind, TokenKind::Ident(_)) {
            return None;
        }
        let mut len = 1;
        while self.nth_is(len, Punct::Dot) && matches!(self.nth(len + 1).kind, TokenKind::Ident(_))
        {
            len += 2;
        }
        Some(len)
    }

    /// Whether the token `n` ahead ends an arm value, or a matcher's argument.
    fn arm_value_ends(&self, n: usize) -> bool {
        let token = self.nth(n);
        token.is(Punct::Comma)
            || token.is(Punct::FatArrow)
            || token.is(Punct::RParen)
            || token.is_keyword(Keyword::If)
            || token.kind == TokenKind::Eof
    }

    /// `Expr | Block | "return" [ Expr ] | "break" [ Ident ] | "continue" [ Ident ]`.
    fn parse_arm_body(&mut self) -> ArmBody {
        match self.peek().kind {
            TokenKind::Punct(Punct::LBrace) => ArmBody::Block(self.parse_block()),
            TokenKind::Keyword(Keyword::Return) => {
                self.bump();
                let ends = self.at(Punct::Comma) || self.at(Punct::RBrace) || self.at_eof();
                ArmBody::Return((!ends).then(|| self.parse_expr()))
            }
            TokenKind::Keyword(Keyword::Break) => {
                let keyword = self.bump();
                let label = self.optional_label();
                self.check_jump(keyword, label);
                ArmBody::Break(label)
            }
            TokenKind::Keyword(Keyword::Continue) => {
                let keyword = self.bump();
                let label = self.optional_label();
                self.check_jump(keyword, label);
                ArmBody::Continue(label)
            }
            _ => ArmBody::Expr(self.parse_expr()),
        }
    }

    /// The label after `break` or `continue`, if one is written. A name on a later
    /// line that goes on as an expression is the next statement, after a missing
    /// `;`: `continue` then `console.log(i)` (EN0101).
    pub(super) fn optional_label(&mut self) -> Option<Ident> {
        if !matches!(self.peek().kind, TokenKind::Ident(_)) {
            return None;
        }
        let after = self.nth(1);
        let ends = after.is(Punct::Semi)
            || after.is(Punct::RBrace)
            || after.is(Punct::Comma)
            || after.kind == TokenKind::Eof
            || self.line_break_before(self.pos + 1);
        if self.line_break_before(self.pos) && !ends {
            return None;
        }
        self.ident()
    }

    /// `AsmExpr = "asm" "(" ( TemplateLit | StringLit ) [ "," AsmOptions ] [ "," ]
    /// ")"`.
    fn parse_asm(&mut self) -> Expr {
        let lo = self.lo();
        self.bump();
        if !self.expect(Punct::LParen) {
            return self.error_expr();
        }
        let template = match self.peek().kind {
            TokenKind::Str(_) | TokenKind::NoSubTemplate(_) | TokenKind::TemplateHead(_) => {
                self.parse_primary()
            }
            _ => {
                self.expected("an assembly template");
                self.error_expr()
            }
        };
        let mut options = None;
        if self.eat(Punct::Comma) && self.at(Punct::LBrace) {
            options = Some(self.parse_asm_options());
            self.eat(Punct::Comma);
        }
        self.expect(Punct::RParen);
        let span = self.span_from(lo);
        self.mk_expr(
            ExprKind::Asm(AsmExpr {
                template: Box::new(template),
                options,
            }),
            span,
        )
    }

    /// `AsmOptions = "{" AsmOption % "," "}"`, each key at most once.
    fn parse_asm_options(&mut self) -> Vec<AsmOption> {
        self.bump();
        let mut seen: Vec<&'static str> = Vec::new();
        self.comma_list(Punct::RBrace, |p| {
            let lo = p.lo();
            let key = p.peek();
            let Some(name) = ["in", "out", "clobbers"]
                .into_iter()
                .find(|name| is_named(key, name))
            else {
                p.expected("`in`, `out` or `clobbers`");
                return None;
            };
            if seen.contains(&name) {
                p.unexpected(
                    key.span,
                    format!("`{name}` is given twice in these options"),
                    "each key appears at most once",
                );
            }
            seen.push(name);
            p.bump();
            p.expect(Punct::Colon);
            let kind = match name {
                "clobbers" => {
                    let names = if p.expect(Punct::LBracket) {
                        p.comma_list(Punct::RBracket, |p| p.parse_str_lit())
                    } else {
                        Vec::new()
                    };
                    AsmOptionKind::Clobbers(names)
                }
                "in" => AsmOptionKind::In(p.parse_reg_map()),
                _ => AsmOptionKind::Out(p.parse_reg_map()),
            };
            let span = p.span_from(lo);
            Some(AsmOption { kind, span })
        })
    }

    /// `RegMap = "{" ( RegName [ ":" Expr ] ) % "," "}"`.
    fn parse_reg_map(&mut self) -> Vec<RegBinding> {
        if !self.expect(Punct::LBrace) {
            return Vec::new();
        }
        self.comma_list(Punct::RBrace, |p| {
            let reg = p.ident()?;
            let value = p.eat(Punct::Colon).then(|| p.parse_expr());
            Some(RegBinding { reg, value })
        })
    }
}

/// The identifiers of a path: an identifier, or plain member accesses on one, each
/// named by an identifier (SPEC 3.4 `NamedPath`, 3.2 `NamedType`). A member may be
/// named by a keyword or reserved word, `a.type`, which no path holds; the lexer
/// never makes an identifier with such a spelling, so the spelling tells.
pub(super) fn path_of(expr: &Expr) -> Option<Vec<Ident>> {
    match &expr.kind {
        ExprKind::Ident(name) => Some(vec![Ident {
            name: *name,
            span: expr.span,
        }]),
        ExprKind::Member {
            base,
            name,
            optional: false,
        } if Keyword::from_name(name.name.as_str()).is_none()
            && Reserved::from_name(name.name.as_str()).is_none() =>
        {
            let mut path = path_of(base)?;
            path.push(*name);
            Some(path)
        }
        _ => None,
    }
}

/// Whether a `{` after `expr` starts a named-form literal: after a path, or after a
/// `TypeMember` whose type has no `[]`.
fn names_a_case(expr: &Expr) -> bool {
    path_of(expr).is_some()
        || matches!(
            &expr.kind,
            ExprKind::TypeMember { ty, .. } if matches!(ty.kind, TypeExprKind::Named { .. })
        )
}

/// The path and type arguments of a named-form literal's head, `Shape.Circle` or
/// `E<i64>.V`, for an `expr` that `names_a_case`.
fn case_head(expr: Expr) -> (Vec<Ident>, Vec<TypeExpr>) {
    if let Some(path) = path_of(&expr) {
        return (path, Vec::new());
    }
    match expr.kind {
        ExprKind::TypeMember { ty, name } => match ty.kind {
            TypeExprKind::Named { mut path, args } => {
                path.push(name);
                (path, args)
            }
            _ => (vec![name], Vec::new()),
        },
        _ => (Vec::new(), Vec::new()),
    }
}
