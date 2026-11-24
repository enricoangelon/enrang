//! Printing expressions: number spellings, string quotes by the Quotes rule, templates
//! as written, paren nodes, arrow parameters, lists and rows, operator breaking,
//! method chains and `match` arms (SPEC 12.5).

use std::path::PathBuf;
use std::sync::Arc;

use enrang_base::{BytePos, FileId, FileOrigin, SourceFile, Span, Symbol};
use enrang_diag::DiagCtx;

use crate::ast::*;
use crate::token::{Punct, TokenKind};

use super::comments::SeqEl;
use super::doc::{
    Doc, GroupId, break_parent, concat, conditional, fill, group, group_with, hardline, indent,
    indent_if_break, join, line, nil, text, verbatim,
};
use super::{ListItem, ListOpts, Printer, pos};

/// Where an expression stands, for the operator rule (SPEC 12.5 Operators).
#[derive(Copy, Clone, Eq, PartialEq)]
pub(crate) enum Ctx {
    Plain,
    /// The right side of `=`, already on a line of its own when it breaks: an
    /// operator chain is not indented again.
    Rhs,
    /// The condition of `if`, `while` or `do`, whose parentheses break with it: an
    /// operator chain puts one operand per line with them.
    Cond,
}

/// One postfix step of a member chain.
enum Link<'e> {
    Member(&'e Ident, bool),
    Index(&'e Expr),
    Call(&'e [TypeExpr], &'e [Expr], Span),
    Try,
    NonNull,
}

impl Link<'_> {
    fn is_member(&self) -> bool {
        matches!(self, Link::Member(..))
    }

    fn is_call(&self) -> bool {
        matches!(self, Link::Call(..))
    }
}

/// An argument of a call-like list whose items differ in kind.
pub(crate) enum Arg<'e> {
    Expr(&'e Expr),
    Str(&'e StrLit),
    Raw(&'e StrLit),
    Arrow(&'e ArrowFn),
    Arm(&'e ArmValue),
    /// The options of `asm`, after its template.
    Asm(&'e [AsmOption], Span),
}

impl Arg<'_> {
    pub(crate) fn span(&self) -> Span {
        match self {
            Arg::Expr(expr) => expr.span,
            Arg::Str(lit) | Arg::Raw(lit) => lit.span,
            Arg::Arrow(arrow) => arrow.span,
            Arg::Arm(value) => arm_span(value),
            Arg::Asm(options, _) => match (options.first(), options.last()) {
                (Some(first), Some(last)) => first.span.to(last.span),
                _ => Span::DUMMY,
            },
        }
    }
}

impl Printer<'_> {
    pub(super) fn expr(&mut self, expr: &Expr) -> Doc {
        self.expr_ctx(expr, Ctx::Plain)
    }

    pub(super) fn expr_ctx(&mut self, expr: &Expr, ctx: Ctx) -> Doc {
        let after = std::mem::take(&mut self.after_amp_lt);
        let lead = if self.has_place(expr.span) {
            self.leading(pos(expr.span.lo))
        } else {
            nil()
        };
        let doc = self.expr_kind(expr, ctx, after);
        concat(vec![lead, doc])
    }

    fn expr_kind(&mut self, expr: &Expr, ctx: Ctx, after: bool) -> Doc {
        match &expr.kind {
            ExprKind::Int { text: spelling, .. } => text(spelling.as_str()),
            ExprKind::Float(spelling) => text(spelling.as_str()),
            ExprKind::Str(value) => self.string(expr.span, *value, after),
            ExprKind::Template(parts) => self.template(expr.span, parts),
            ExprKind::RawTemplate(raw) => {
                if self.has_place(expr.span) {
                    self.skip_until(pos(expr.span.hi));
                }
                verbatim(format!("raw`{}`", raw.as_str()))
            }
            ExprKind::Bool(value) => text(if *value { "true" } else { "false" }),
            ExprKind::Null => text("null"),
            ExprKind::This => text("this"),
            ExprKind::Super => text("super"),
            ExprKind::Ident(name) => text(name.as_str()),
            ExprKind::Error => self.error_text(expr.span),
            ExprKind::Paren(inner) => {
                let inner = self.expr(inner);
                concat(vec![text("("), inner, text(")")])
            }
            ExprKind::Array(elems) => self.array(elems, expr.span),
            ExprKind::Repeat(value, count) => {
                let value = self.expr(value);
                let count = self.expr(count);
                concat(vec![text("["), value, text("; "), count, text("]")])
            }
            ExprKind::TypeMember { ty, name } => {
                // `a<>.b`: a named type with an empty argument list keeps `<>`, or
                // it would read back as a member access.
                let empty = matches!(&ty.kind, TypeExprKind::Named { args, .. } if args.is_empty());
                let ty = self.ty(ty);
                let empty = if empty { text("<>") } else { nil() };
                concat(vec![ty, empty, text("."), self.ident(name)])
            }
            ExprKind::New { ty, init } => {
                let ty = self.ty(ty);
                let close = self.close_of(expr.span);
                let init = match init {
                    NewInit::Args(args) => self.args(args, close),
                    NewInit::Fields(fields) => {
                        let fields = self.fields(fields, close).doc;
                        concat(vec![text(" "), fields])
                    }
                };
                concat(vec![text("new "), ty, init])
            }
            ExprKind::CaseLit { path, args, fields } => {
                let path = self.case_path(path, args);
                let fields = self.fields(fields, self.close_of(expr.span)).doc;
                concat(vec![path, text(" "), fields])
            }
            ExprKind::ObjectLit(fields) => self.fields(fields, self.close_of(expr.span)).doc,
            ExprKind::Match { subject, arms } => self.match_expr(subject, arms),
            ExprKind::SizeForm(form) => self.size_form(form, expr.span),
            ExprKind::Asm(asm) => self.asm(asm, expr.span),
            ExprKind::Unary(op, operand) => {
                let space = *op == UnOp::Neg && starts_with_minus(operand);
                let operand = self.expr(operand);
                let op = if space {
                    format!("{} ", op.as_str())
                } else {
                    op.as_str().to_owned()
                };
                concat(vec![text(op), operand])
            }
            ExprKind::Borrow(operand) => {
                self.after_amp_lt = true;
                let operand = self.expr(operand);
                concat(vec![text("&"), operand])
            }
            ExprKind::Deref(operand) => concat(vec![text("*"), self.expr(operand)]),
            ExprKind::VoidOp(operand) => concat(vec![text("void "), self.expr(operand)]),
            ExprKind::Binary(..) | ExprKind::Logical(..) | ExprKind::Coalesce(..) => {
                self.operators(expr, ctx, after)
            }
            ExprKind::Ternary(cond, yes, no) => {
                self.after_amp_lt = after;
                let cond_doc = self.expr(cond);
                let before_yes = self.before_punct(cond.span, Punct::Question);
                let yes_doc = self.expr(yes);
                let before_no = self.before_punct(yes.span, Punct::Colon);
                let no_doc = self.expr(no);
                group(concat(vec![
                    cond_doc,
                    before_yes.0,
                    indent(concat(vec![
                        line(),
                        before_yes.1,
                        text("? "),
                        yes_doc,
                        before_no.0,
                        line(),
                        before_no.1,
                        text(": "),
                        no_doc,
                    ])),
                ]))
            }
            ExprKind::Cast(operand, ty) => {
                self.after_amp_lt = after;
                let operand = self.expr(operand);
                let ty = self.ty(ty);
                concat(vec![operand, text(" as "), ty])
            }
            ExprKind::Assign { op, target, value } => {
                self.after_amp_lt = after;
                let target = self.expr(target);
                self.rhs(target, op.as_str(), value)
            }
            ExprKind::IncDec {
                target,
                inc,
                prefix,
            } => {
                let op = text(if *inc { "++" } else { "--" });
                if *prefix {
                    concat(vec![op, self.expr(target)])
                } else {
                    self.after_amp_lt = after;
                    concat(vec![self.expr(target), op])
                }
            }
            ExprKind::Member { .. }
            | ExprKind::Index(..)
            | ExprKind::Call { .. }
            | ExprKind::Try(_)
            | ExprKind::NonNull(_) => self.postfix(expr, after),
            ExprKind::Arrow(arrow) => self.arrow(arrow).0,
        }
    }

    pub(super) fn ident(&mut self, ident: &Ident) -> Doc {
        let lead = if self.has_place(ident.span) {
            self.leading(pos(ident.span.lo))
        } else {
            nil()
        };
        concat(vec![lead, text(ident.name.as_str())])
    }

    /// The position of the closing bracket of an expression that ends with one.
    pub(super) fn close_of(&self, span: Span) -> Option<u32> {
        self.has_place(span).then(|| pos(span.hi).saturating_sub(1))
    }

    /// `x = value`, `const x = value` (SPEC 12.5 Right-hand sides): a value with a
    /// list of its own keeps `= callee(` on the first line unless that alone does not
    /// fit; any other value breaks after the operator first. A value other than an
    /// operator chain or a ternary that cannot be flat, as a member of a
    /// parenthesised `match` cannot, breaks after `=` only when its first line does not
    /// fit, as a list does.
    pub(super) fn rhs(&mut self, lhs: Doc, op: &str, value: &Expr) -> Doc {
        let op = text(format!(" {op}"));
        let listed = has_list(value);
        let chain = level(value).is_some() || matches!(value.kind, ExprKind::Ternary(..));
        let ctx = if listed { Ctx::Plain } else { Ctx::Rhs };
        // `const x = // c`: the comment trails the `=`, and the value goes on the
        // next line, as a value that breaks after `=` does.
        if self.has_place(value.span)
            && let Some(trailing) = self.code_comment(pos(value.span.lo))
        {
            let value = self.expr_ctx(value, ctx);
            return concat(vec![
                lhs,
                op,
                trailing,
                indent(concat(vec![hardline(), value])),
            ]);
        }
        let value = self.expr_ctx(value, ctx);
        if listed || (value.breaks() && !chain) {
            let id = self.group_id();
            concat(vec![
                lhs,
                op,
                group_with(id, false, indent(line())),
                indent_if_break(id, value),
            ])
        } else {
            concat(vec![lhs, op, group(indent(concat(vec![line(), value])))])
        }
    }

    // -----------------------------------------------------------------------------
    // Literals.

    /// A string literal by the Quotes rule: from its spelling when it has one, else
    /// from its value.
    pub(super) fn string(&mut self, span: Span, value: Symbol, after: bool) -> Doc {
        let spelling = self.span_text(span);
        let written = is_string_spelling(spelling);
        let quote = |forced: Option<char>| {
            if written {
                requote(spelling, forced)
            } else {
                quote_value(value.as_str(), forced)
            }
        };
        let mut out = quote(None);
        if after && out.starts_with('\'') && lexes_as_lifetime(&out) {
            out = quote(Some('"'));
        }
        text(out)
    }

    pub(super) fn str_lit(&mut self, lit: &StrLit) -> Doc {
        let lead = if self.has_place(lit.span) {
            self.leading(pos(lit.span.lo))
        } else {
            nil()
        };
        concat(vec![lead, self.string(lit.span, lit.value, false)])
    }

    /// A `raw` template held as a `StrLit`: as written, or from its text.
    pub(super) fn raw_lit(&mut self, lit: &StrLit) -> Doc {
        if self.has_place(lit.span) {
            let lead = self.leading(pos(lit.span.lo));
            return concat(vec![lead, self.as_written(lit.span)]);
        }
        verbatim(format!("raw`{}`", lit.value.as_str()))
    }

    /// A template: its text as written, holes included, or rebuilt from its parts.
    fn template(&mut self, span: Span, parts: &[TplPart]) -> Doc {
        if self.has_place(span) {
            return self.as_written(span);
        }
        text(self.template_text(parts))
    }

    /// A template rebuilt from its parts, each hole laid out on its own.
    fn template_text(&mut self, parts: &[TplPart]) -> String {
        let mut out = String::from("`");
        for part in parts {
            match part {
                TplPart::Str(piece) => escape_template(piece.as_str(), &mut out),
                TplPart::Expr(expr) => {
                    let doc = self.expr(expr);
                    out.push_str("${");
                    out.push_str(&super::doc::layout(&doc, usize::MAX / 4));
                    out.push('}');
                }
            }
        }
        out.push('`');
        out
    }

    // -----------------------------------------------------------------------------
    // Lists.

    /// The arguments of a call: a list whose last block-bodied arrow or object
    /// literal hugs the call's line, or a sole multi-line template as written.
    pub(super) fn args(&mut self, args: &[Expr], close: Option<u32>) -> Doc {
        if let [only] = args
            && self.is_multiline_template(only)
        {
            let doc = self.expr(only);
            if let Some(close) = close {
                let dangling = self.dangling(close);
                return concat(vec![text("("), doc, concat(dangling), text(")")]);
            }
            return concat(vec![text("("), doc, text(")")]);
        }
        let args: Vec<Arg<'_>> = args.iter().map(Arg::Expr).collect();
        self.arg_list(&args, close)
    }

    /// A call-like argument list of mixed items.
    pub(super) fn arg_list(&mut self, args: &[Arg<'_>], close: Option<u32>) -> Doc {
        let opts = ListOpts {
            hug: true,
            ..ListOpts::new("(", ")")
        }
        .close_at(close);
        self.list(args, Arg::span, |p, arg| p.arg_item(arg), opts)
            .doc
    }

    fn arg_item(&mut self, arg: &Arg<'_>) -> ListItem {
        match arg {
            Arg::Expr(expr) => match &expr.kind {
                ExprKind::Arrow(arrow) => {
                    let (doc, hug) = self.arrow(arrow);
                    ListItem { doc, hug }
                }
                ExprKind::ObjectLit(fields) => {
                    let listed = self.fields(fields, self.close_of(expr.span));
                    ListItem {
                        doc: listed.doc,
                        hug: Some(listed.id),
                    }
                }
                _ => ListItem::plain(self.expr(expr)),
            },
            Arg::Str(lit) => ListItem::plain(self.str_lit(lit)),
            Arg::Raw(lit) => ListItem::plain(self.raw_lit(lit)),
            Arg::Arrow(arrow) => {
                let (doc, hug) = self.arrow(arrow);
                ListItem { doc, hug }
            }
            Arg::Arm(value) => ListItem::plain(self.arm_value(value)),
            Arg::Asm(options, after) => {
                let (doc, id) = self.asm_options(options, *after);
                ListItem { doc, hug: Some(id) }
            }
        }
    }

    pub(super) fn type_args(&mut self, args: &[TypeExpr]) -> Doc {
        if args.is_empty() {
            return nil();
        }
        let close = args
            .last()
            .and_then(|last| self.closer_after(pos(last.span.hi), Punct::Gt));
        let opts = ListOpts::new("<", ">").close_at(close);
        self.list(args, |ty| ty.span, |p, ty| ListItem::plain(p.ty(ty)), opts)
            .doc
    }

    /// An object literal, or the fields of a named-form literal.
    pub(super) fn fields(&mut self, fields: &[FieldInit], close: Option<u32>) -> super::Listed {
        let opts = ListOpts::braces().close_at(close);
        self.list(
            fields,
            |field| field.span,
            |p, field| {
                let name = p.ident(&field.name);
                let doc = match &field.value {
                    Some(value) => concat(vec![name, text(": "), p.expr(value)]),
                    None => name,
                };
                ListItem::plain(doc)
            },
            opts,
        )
    }

    /// An array literal: a list, one element per line when every element is a row
    /// (SPEC 12.5 Rows).
    fn array(&mut self, elems: &[ArrayElem], span: Span) -> Doc {
        let rows = is_rows(elems);
        let opts = ListOpts {
            force: rows,
            fill: !rows,
            ..ListOpts::new("[", "]")
        }
        .close_at(self.close_of(span));
        self.list(
            elems,
            |elem| match elem {
                ArrayElem::Item(expr) => expr.span,
                ArrayElem::Spread { dots, expr } => dots.to(expr.span),
            },
            |p, elem| match elem {
                ArrayElem::Item(expr) => ListItem::plain(p.expr(expr)),
                ArrayElem::Spread { expr, .. } => {
                    ListItem::plain(concat(vec![text("..."), p.expr(expr)]))
                }
            },
            opts,
        )
        .doc
    }

    // -----------------------------------------------------------------------------
    // Operators.

    /// A chain of one operator level, broken at that level, one operand per line,
    /// each line ending with its operator (SPEC 12.5 Operators).
    fn operators(&mut self, expr: &Expr, ctx: Ctx, after: bool) -> Doc {
        let (first, rest) = flatten_operators(expr);
        self.after_amp_lt = after;
        let first = self.expr(first);
        let mut tail = Vec::with_capacity(rest.len() * 3);
        for (op, operand) in rest {
            tail.push(text(format!(" {op}")));
            tail.push(line());
            self.after_amp_lt = op == "&" || op == "<";
            tail.push(self.expr(operand));
        }
        self.after_amp_lt = false;
        match ctx {
            Ctx::Cond => concat(vec![first, concat(tail)]),
            Ctx::Rhs => group(concat(vec![first, concat(tail)])),
            Ctx::Plain => group(concat(vec![first, indent(concat(tail))])),
        }
    }

    // -----------------------------------------------------------------------------
    // Postfix chains.

    /// Member access, indexing, calls and postfix `?` and `!`: a chain of 2 or more
    /// calls that does not fit puts each call on its own line (SPEC 12.5 Method
    /// chains).
    fn postfix(&mut self, expr: &Expr, after: bool) -> Doc {
        let (primary, links) = flatten_postfix(expr);
        let head_len = head_len(&links);
        let groups = chain_groups(&links[head_len..]);
        let calls = links[head_len..]
            .iter()
            .filter(|link| link.is_call())
            .count();
        // A member access right after a postfix `?` takes a space on the same line,
        // since `?.` and `??` are single tokens (SPEC 2): `x? .f`.
        let spaced =
            |at: usize| at > 0 && matches!(links[at - 1], Link::Try) && links[at].is_member();
        self.after_amp_lt = after;
        let mut head = vec![self.expr(primary)];
        for (at, link) in links[..head_len].iter().enumerate() {
            if spaced(at) {
                head.push(text(" "));
            }
            head.push(self.link(link));
        }
        if calls < 2 {
            for (at, link) in links.iter().enumerate().skip(head_len) {
                if spaced(at) {
                    head.push(text(" "));
                }
                head.push(self.link(link));
            }
            return concat(head);
        }
        let forced = calls > 2
            && links[head_len..].iter().any(|link| match link {
                Link::Call(_, args, _) => !args.iter().all(|arg| self.is_simple(arg)),
                _ => false,
            });
        // Each chunk, and whether it starts with a member access after a `?`, which
        // needs the space on one line but not at the start of a line of its own.
        let mut printed = Vec::with_capacity(groups.len());
        let mut at = head_len;
        for chunk in groups {
            let lead = spaced(at);
            let mut parts = Vec::with_capacity(chunk.len());
            for (offset, link) in chunk.iter().enumerate() {
                if offset > 0 && spaced(at + offset) {
                    parts.push(text(" "));
                }
                parts.push(self.link(link));
            }
            at += chunk.len();
            printed.push((lead, concat(parts)));
        }
        let head = concat(head);
        let mut broken = Vec::with_capacity(printed.len() * 2);
        for (_, part) in &printed {
            broken.push(hardline());
            broken.push(part.clone());
        }
        // The links' group holds hard lines, so it is laid out broken, and each
        // group inside a link is measured against the width on its own line.
        let expanded = concat(vec![head.clone(), indent(group(concat(broken)))]);
        if forced {
            return group(expanded);
        }
        let flat: Vec<Doc> = printed
            .into_iter()
            .map(|(lead, part)| {
                if lead {
                    concat(vec![text(" "), part])
                } else {
                    part
                }
            })
            .collect();
        let one_line = concat(vec![head, concat(flat)]);
        let parent = if one_line.breaks() {
            break_parent()
        } else {
            nil()
        };
        concat(vec![parent, conditional(one_line, vec![expanded])])
    }

    /// `lo..hi`, a range of a `for...of` source or an arm, with a space before `..`
    /// when `lo` ends with a postfix `?`, which `..` would join into `?.` (SPEC 2).
    pub(super) fn range(&mut self, lo: &Expr, hi: &Expr) -> Doc {
        let dots = if ends_with_try(lo) { " .." } else { ".." };
        let lo = self.expr(lo);
        let hi = self.expr(hi);
        concat(vec![lo, text(dots), hi])
    }

    fn link(&mut self, link: &Link<'_>) -> Doc {
        match link {
            Link::Member(name, optional) => {
                let lead = if self.has_place(name.span) {
                    self.leading(pos(name.span.lo))
                } else {
                    nil()
                };
                let dot = if *optional { "?." } else { "." };
                concat(vec![lead, text(dot), text(name.name.as_str())])
            }
            Link::Index(index) => {
                let index = self.expr(index);
                concat(vec![text("["), index, text("]")])
            }
            Link::Call(type_args, args, span) => {
                let close = self.close_of(*span);
                let type_args = self.type_args(type_args);
                let args = self.args(args, close);
                concat(vec![type_args, args])
            }
            Link::Try => text("?"),
            Link::NonNull => text("!"),
        }
    }

    /// SPEC 12.5 Method chains: "Simple arguments are literals, names, `this`,
    /// one-line templates, member accesses, unary operators, arrays and class or
    /// object literals of simple items, and calls with simple arguments".
    fn is_simple(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Int { .. }
            | ExprKind::Float(_)
            | ExprKind::Str(_)
            | ExprKind::Bool(_)
            | ExprKind::Null
            | ExprKind::Ident(_)
            | ExprKind::This
            | ExprKind::Super
            | ExprKind::TypeMember { .. }
            | ExprKind::SizeForm(_) => true,
            ExprKind::Template(_) | ExprKind::RawTemplate(_) => !self.is_multiline_template(expr),
            ExprKind::Member { base, .. } => self.is_simple(base),
            ExprKind::Index(base, index) => self.is_simple(base) && self.is_simple(index),
            ExprKind::Unary(_, operand)
            | ExprKind::Borrow(operand)
            | ExprKind::Deref(operand)
            | ExprKind::Try(operand)
            | ExprKind::NonNull(operand)
            | ExprKind::Paren(operand) => self.is_simple(operand),
            ExprKind::Array(elems) => elems.iter().all(|elem| match elem {
                ArrayElem::Item(expr) => self.is_simple(expr),
                ArrayElem::Spread { .. } => false,
            }),
            ExprKind::ObjectLit(fields)
            | ExprKind::CaseLit { fields, .. }
            | ExprKind::New {
                init: NewInit::Fields(fields),
                ..
            } => fields.iter().all(|field| {
                field
                    .value
                    .as_ref()
                    .is_none_or(|value| self.is_simple(value))
            }),
            ExprKind::New {
                init: NewInit::Args(args),
                ..
            } => args.iter().all(|arg| self.is_simple(arg)),
            ExprKind::Call { callee, args, .. } => {
                self.is_simple(callee) && args.iter().all(|arg| self.is_simple(arg))
            }
            _ => false,
        }
    }

    pub(super) fn is_multiline_template(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Template(_) if self.has_place(expr.span) => {
                self.span_text(expr.span).contains('\n')
            }
            // Rebuilt from its parts, a template spans lines when a hole prints over
            // several, as a `match` or a block body does; a printer with no source
            // lays it out with nothing of this print's state.
            ExprKind::Template(parts) => Printer::bare().template_text(parts).contains('\n'),
            ExprKind::RawTemplate(raw) => raw.as_str().contains('\n'),
            _ => false,
        }
    }

    // -----------------------------------------------------------------------------
    // Arrows.

    /// An arrow, and the group of its block body: a single untyped parameter with no
    /// `let` and no return type is bare (SPEC 12.5 Arrow parameters).
    pub(super) fn arrow(&mut self, arrow: &ArrowFn) -> (Doc, Option<GroupId>) {
        let params = match arrow.params.as_slice() {
            [only] if arrow.ret.is_none() && !only.is_let && only.ty.is_none() => {
                self.ident(&only.name)
            }
            params => {
                let close = match params.last() {
                    Some(last) => {
                        let end = last.ty.as_ref().map_or(last.name.span, |ty| ty.span);
                        self.closer_after(pos(end.hi), Punct::RParen)
                    }
                    None if self.has_place(arrow.span) => self
                        .find_punct(pos(arrow.span.lo), Punct::RParen)
                        .map(|at| pos(self.tokens[at].span.lo)),
                    None => None,
                };
                let opts = ListOpts::params().close_at(close);
                self.list_then(
                    params,
                    |param| match &param.ty {
                        Some(ty) => param.name.span.to(ty.span),
                        None => param.name.span,
                    },
                    |p, param| {
                        let mark = if param.is_let { text("let ") } else { nil() };
                        let name = p.ident(&param.name);
                        let ty = match &param.ty {
                            Some(ty) => concat(vec![text(": "), p.ty(ty)]),
                            None => nil(),
                        };
                        ListItem::plain(concat(vec![mark, name, ty]))
                    },
                    opts,
                    |p| match &arrow.ret {
                        Some(ret) => concat(vec![text(": "), p.ret_type(ret)]),
                        None => nil(),
                    },
                )
                .doc
            }
        };
        match &arrow.body {
            ArrowBody::Expr(body) => {
                let head = concat(vec![params, text(" =>")]);
                let doc = self.then_node(head, " ", pos(body.span.lo), |p| p.expr(body));
                (doc, None)
            }
            ArrowBody::Block(block) => {
                let (body, id) = self.body(block);
                (concat(vec![params, text(" => "), body]), Some(id))
            }
        }
    }

    // -----------------------------------------------------------------------------
    // Forms.

    /// `Shape.Circle`, or `E<i64>.V` with the type arguments before the last name.
    fn case_path(&mut self, path: &[Ident], args: &[TypeExpr]) -> Doc {
        let (head, last) = match path {
            [head @ .., last] if !args.is_empty() && !head.is_empty() => (head, Some(last)),
            _ => (path, None),
        };
        let names: Vec<Doc> = head.iter().map(|name| self.ident(name)).collect();
        let Some(last) = last else {
            // A one-name path keeps its arguments after the name, `Point<i64> {`,
            // which SPEC 3.4 reads back as the same literal (a `{` may follow them).
            let names = join(&text("."), names);
            if args.is_empty() {
                return names;
            }
            let args = self.type_args(args);
            return concat(vec![names, args]);
        };
        let args = self.type_args(args);
        let last = self.ident(last);
        concat(vec![join(&text("."), names), args, text("."), last])
    }

    /// The comments between the end of `after` and the next `punct`, an operator
    /// that starts a line when its expression breaks: a trailing comment of the line
    /// `after` ends, then the others, each on a line of its own before the operator.
    fn before_punct(&mut self, after: Span, punct: Punct) -> (Doc, Doc) {
        if !self.has_place(after) {
            return (nil(), nil());
        }
        let found = self.take_trailing(pos(after.hi), false);
        let trailing = self.trailing_doc(&found);
        let Some(at) = self.find_punct(pos(after.hi), punct) else {
            return (trailing, nil());
        };
        let lo = pos(self.tokens[at].span.lo);
        (trailing, self.leading(lo))
    }

    /// `match (subject) {`, one arm per line, each ending with `,` (SPEC 12.5
    /// `match`).
    fn match_expr(&mut self, subject: &Expr, arms: &[MatchArm]) -> Doc {
        let subject_doc = self.expr(subject);
        let (open, close) = self.braces_after(pos(subject.span.hi));
        let els: Vec<SeqEl<&MatchArm>> = arms.iter().map(|arm| SeqEl::row(arm.span, arm)).collect();
        let seq = self.seq(open, close, &els, true, |p, arm| {
            let arm = p.arm(arm);
            concat(vec![arm, text(",")])
        });
        let (body, _) = self.braces(seq, false);
        concat(vec![text("match ("), subject_doc, text(") "), body])
    }

    fn arm(&mut self, arm: &MatchArm) -> Doc {
        let values = if arm.values.is_empty() {
            text("default")
        } else {
            self.arm_values(&arm.values)
        };
        let guard = match &arm.guard {
            Some(guard) => concat(vec![text(" if "), self.expr(guard)]),
            None => nil(),
        };
        let head = concat(vec![values, guard, text(" =>")]);
        match &arm.body {
            ArmBody::Expr(expr) => self.then_node(head, " ", pos(expr.span.lo), |p| p.expr(expr)),
            ArmBody::Block(block) => concat(vec![head, text(" "), self.body(block).0]),
            ArmBody::Return(value) => match value {
                Some(value) => {
                    let head = concat(vec![head, text(" return")]);
                    self.then_node(head, " ", pos(value.span.lo), |p| p.expr(value))
                }
                None => concat(vec![head, text(" return")]),
            },
            ArmBody::Break(label) => {
                concat(vec![head, text(" "), self.jump("break", label.as_ref())])
            }
            ArmBody::Continue(label) => {
                concat(vec![head, text(" "), self.jump("continue", label.as_ref())])
            }
        }
    }

    /// An arm's values, as a list with no brackets (SPEC 12.5 Width, Lists): on one
    /// line when they fit, else filled when every value is 10 characters or shorter,
    /// else one per line, each later line indented 2 more. A comment after a value's
    /// `,` stays on its line and breaks them.
    fn arm_values(&mut self, values: &[ArmValue]) -> Doc {
        let count = values.len();
        let mut docs = Vec::with_capacity(count);
        let mut commented = false;
        let mut short = true;
        for (at, value) in values.iter().enumerate() {
            let doc = self.arm_value(value);
            short &= doc.flat_width().is_some_and(|width| width <= 10);
            let last = at + 1 == count;
            let trail = match arm_value_span(value) {
                Some(span) if !last && self.has_place(span) => {
                    let found = self.take_trailing(pos(span.hi), true);
                    self.trailing_doc(&found)
                }
                _ => nil(),
            };
            commented |= !trail.is_nil();
            let comma = if last { nil() } else { text(",") };
            docs.push(concat(vec![doc, comma, trail]));
        }
        let short = short && !commented;
        let mut parts = Vec::with_capacity(count * 2);
        for (at, doc) in docs.into_iter().enumerate() {
            if at > 0 {
                parts.push(line());
            }
            parts.push(doc);
        }
        if short {
            group(indent(fill(parts)))
        } else {
            group(indent(concat(parts)))
        }
    }

    pub(super) fn jump(&mut self, word: &str, label: Option<&Ident>) -> Doc {
        match label {
            Some(label) => concat(vec![text(format!("{word} ")), self.ident(label)]),
            None => text(word),
        }
    }

    pub(super) fn arm_value(&mut self, value: &ArmValue) -> Doc {
        match value {
            ArmValue::Value(expr) => self.expr(expr),
            ArmValue::Null(span) => self.word_at(*span, "null"),
            ArmValue::Ok(span) => self.word_at(*span, "Ok"),
            ArmValue::Err(span) => self.word_at(*span, "Err"),
            ArmValue::Case(path) => {
                let names: Vec<Doc> = path.iter().map(|name| self.ident(name)).collect();
                join(&text("."), names)
            }
            ArmValue::Range(lo, hi) => self.range(lo, hi),
        }
    }

    /// A keyword with a span of its own, after the comments before it.
    fn word_at(&mut self, span: Span, word: &str) -> Doc {
        let lead = if self.has_place(span) {
            self.leading(pos(span.lo))
        } else {
            nil()
        };
        concat(vec![lead, text(word)])
    }

    fn size_form(&mut self, form: &SizeForm, span: Span) -> Doc {
        let (name, ty, field) = match form {
            SizeForm::SizeOf(ty) => ("sizeOf", ty, None),
            SizeForm::AlignOf(ty) => ("alignOf", ty, None),
            SizeForm::OffsetOf(ty, field) => ("offsetOf", ty, Some(field)),
        };
        let ty = self.ty(ty);
        let args = match field {
            Some(field) => self.arg_list(&[Arg::Str(field)], self.close_of(span)),
            None => text("()"),
        };
        concat(vec![text(name), text("<"), ty, text(">"), args])
    }

    fn asm(&mut self, asm: &AsmExpr, span: Span) -> Doc {
        let close = self.close_of(span);
        let args = match &asm.options {
            None => self.args(std::slice::from_ref(&*asm.template), close),
            Some(options) => {
                let args = [
                    Arg::Expr(&asm.template),
                    Arg::Asm(options, asm.template.span),
                ];
                self.arg_list(&args, close)
            }
        };
        concat(vec![text("asm"), args])
    }

    /// `{ in: { eax: x }, out: { ... }, clobbers: ["memory"] }`, and its group.
    /// `after` is the template, which the options follow.
    fn asm_options(&mut self, options: &[AsmOption], after: Span) -> (Doc, GroupId) {
        let close = match options.last() {
            Some(last) => self.closer_after(pos(last.span.hi), Punct::RBrace),
            None => self.braces_after(pos(after.hi)).1,
        };
        let listed = self.list(
            options,
            |option| option.span,
            |p, option| {
                let close = p.close_of(option.span);
                let doc = match &option.kind {
                    AsmOptionKind::In(regs) => concat(vec![text("in: "), p.reg_map(regs, close)]),
                    AsmOptionKind::Out(regs) => concat(vec![text("out: "), p.reg_map(regs, close)]),
                    AsmOptionKind::Clobbers(names) => {
                        let opts = ListOpts::new("[", "]").close_at(close);
                        let list = p
                            .list(
                                names,
                                |name| name.span,
                                |p, name| ListItem::plain(p.str_lit(name)),
                                opts,
                            )
                            .doc;
                        concat(vec![text("clobbers: "), list])
                    }
                };
                ListItem::plain(doc)
            },
            ListOpts::braces().close_at(close),
        );
        (listed.doc, listed.id)
    }

    /// `{ eax: x, ebx }`, whose `}` is at `close`.
    fn reg_map(&mut self, regs: &[RegBinding], close: Option<u32>) -> Doc {
        let opts = ListOpts::braces().close_at(close);
        self.list(
            regs,
            |reg| match &reg.value {
                Some(value) => reg.reg.span.to(value.span),
                None => reg.reg.span,
            },
            |p, reg| {
                let name = p.ident(&reg.reg);
                let doc = match &reg.value {
                    Some(value) => concat(vec![name, text(": "), p.expr(value)]),
                    None => name,
                };
                ListItem::plain(doc)
            },
            opts,
        )
        .doc
    }
}

/// The span of an arm value, for the comments around it.
pub(crate) fn arm_span(value: &ArmValue) -> Span {
    match value {
        ArmValue::Value(expr) => expr.span,
        ArmValue::Null(span) | ArmValue::Ok(span) | ArmValue::Err(span) => *span,
        ArmValue::Case(path) => match (path.first(), path.last()) {
            (Some(first), Some(last)) => first.span.to(last.span),
            _ => Span::DUMMY,
        },
        ArmValue::Range(lo, hi) => lo.span.to(hi.span),
    }
}

/// SPEC 12.5 Right-hand sides: a call, class literal or array has a list of its own;
/// so does any form whose first line ends in a bracket or a template's first line.
fn has_list(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Call { .. }
        | ExprKind::New { .. }
        | ExprKind::Array(_)
        | ExprKind::Repeat(..)
        | ExprKind::ObjectLit(_)
        | ExprKind::CaseLit { .. }
        | ExprKind::Match { .. }
        | ExprKind::Arrow(_)
        | ExprKind::Template(_)
        | ExprKind::RawTemplate(_)
        | ExprKind::Asm(_)
        | ExprKind::SizeForm(_) => true,
        ExprKind::Borrow(operand)
        | ExprKind::Deref(operand)
        | ExprKind::Unary(_, operand)
        | ExprKind::VoidOp(operand)
        | ExprKind::Try(operand)
        | ExprKind::NonNull(operand)
        | ExprKind::Cast(operand, _) => has_list(operand),
        _ => false,
    }
}

/// Whether an operand printed after a unary `-` starts with `-`, which would make
/// `--`.
fn starts_with_minus(expr: &Expr) -> bool {
    matches!(
        expr.kind,
        ExprKind::Unary(UnOp::Neg, _)
            | ExprKind::IncDec {
                prefix: true,
                inc: false,
                ..
            }
    )
}

/// The operator level of a binary, logical or `??` node.
fn level(expr: &Expr) -> Option<u8> {
    match &expr.kind {
        ExprKind::Binary(op, ..) => Some(op.precedence()),
        ExprKind::Logical(op, ..) => Some(op.precedence()),
        ExprKind::Coalesce(..) => Some(COALESCE_PRECEDENCE),
        _ => None,
    }
}

/// The operands of the chain of `expr`'s level, and the operator before each after
/// the first. Left-associative levels nest to the left, `??` to the right.
fn flatten_operators(expr: &Expr) -> (&Expr, Vec<(&'static str, &Expr)>) {
    let top = level(expr);
    if top == Some(COALESCE_PRECEDENCE) {
        let mut rest = Vec::new();
        let mut first = None;
        let mut cur = expr;
        while let ExprKind::Coalesce(lhs, rhs) = &cur.kind {
            if first.is_none() {
                first = Some(&**lhs);
            } else {
                rest.push(("??", &**lhs));
            }
            cur = rhs;
        }
        rest.push(("??", cur));
        return (first.unwrap_or(expr), rest);
    }
    let mut rest = Vec::new();
    let mut cur = expr;
    loop {
        let (op, lhs, rhs) = match &cur.kind {
            ExprKind::Binary(op, lhs, rhs) if Some(op.precedence()) == top => {
                (op.as_str(), lhs, rhs)
            }
            ExprKind::Logical(op, lhs, rhs) if Some(op.precedence()) == top => {
                (op.as_str(), lhs, rhs)
            }
            _ => break,
        };
        rest.push((op, &**rhs));
        cur = lhs;
    }
    rest.reverse();
    (cur, rest)
}

/// The primary of a postfix chain and its links, in source order.
fn flatten_postfix(expr: &Expr) -> (&Expr, Vec<Link<'_>>) {
    let mut links = Vec::new();
    let mut cur = expr;
    loop {
        cur = match &cur.kind {
            ExprKind::Member {
                base,
                name,
                optional,
            } => {
                links.push(Link::Member(name, *optional));
                base
            }
            ExprKind::Index(base, index) => {
                links.push(Link::Index(index));
                base
            }
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => {
                links.push(Link::Call(type_args, args, cur.span));
                callee
            }
            ExprKind::Try(base) => {
                links.push(Link::Try);
                base
            }
            ExprKind::NonNull(base) => {
                links.push(Link::NonNull);
                base
            }
            _ => break,
        };
    }
    links.reverse();
    (cur, links)
}

/// Whether the last token of `expr` is a postfix `?`.
fn ends_with_try(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Try(_) => true,
        ExprKind::Binary(_, _, right)
        | ExprKind::Logical(_, _, right)
        | ExprKind::Coalesce(_, right)
        | ExprKind::Ternary(_, _, right)
        | ExprKind::Unary(_, right)
        | ExprKind::Borrow(right)
        | ExprKind::Deref(right)
        | ExprKind::VoidOp(right) => ends_with_try(right),
        ExprKind::IncDec {
            target,
            prefix: true,
            ..
        } => ends_with_try(target),
        ExprKind::Assign { value, .. } => ends_with_try(value),
        ExprKind::Arrow(ArrowFn {
            body: ArrowBody::Expr(body),
            ..
        }) => ends_with_try(body),
        _ => false,
    }
}

/// How many links stay with the primary on the first line: calls, indexes and
/// postfix operators right after it, then member accesses up to the last one before
/// a call (`this.items`, `os.fs`), with the indexes and postfix `?` and `!` between
/// them (`this.items!`, `this.groups[0]`).
fn head_len(links: &[Link<'_>]) -> usize {
    let first = links
        .iter()
        .position(|link| link.is_member())
        .unwrap_or(links.len());
    let call = links[first..]
        .iter()
        .position(|link| link.is_call())
        .map_or(links.len(), |at| first + at);
    links[first..call]
        .iter()
        .rposition(|link| link.is_member())
        .map_or(first, |at| first + at)
}

/// The links after the head, cut before each member access that follows a call.
fn chain_groups<'l, 'e>(links: &'l [Link<'e>]) -> Vec<&'l [Link<'e>]> {
    let mut groups = Vec::new();
    let mut start = 0;
    let mut seen_call = false;
    for (at, link) in links.iter().enumerate() {
        if link.is_member() && seen_call {
            groups.push(&links[start..at]);
            start = at;
            seen_call = false;
        }
        seen_call |= link.is_call();
    }
    if start < links.len() {
        groups.push(&links[start..]);
    }
    groups
}

/// SPEC 12.5 Rows: 2 or more elements, every one an array literal of 2 or more
/// elements, or every one a class or object literal of 2 or more fields.
fn is_rows(elems: &[ArrayElem]) -> bool {
    if elems.len() < 2 {
        return false;
    }
    let exprs: Vec<&Expr> = elems
        .iter()
        .filter_map(|elem| match elem {
            ArrayElem::Item(expr) => Some(expr),
            ArrayElem::Spread { .. } => None,
        })
        .collect();
    if exprs.len() != elems.len() {
        return false;
    }
    let arrays = exprs
        .iter()
        .all(|expr| matches!(&expr.kind, ExprKind::Array(inner) if inner.len() >= 2));
    let records = exprs.iter().all(|expr| match &expr.kind {
        ExprKind::ObjectLit(fields)
        | ExprKind::CaseLit { fields, .. }
        | ExprKind::New {
            init: NewInit::Fields(fields),
            ..
        } => fields.len() >= 2,
        _ => false,
    });
    arrays || records
}

/// Whether `spelling` is a whole string literal: a quote, then text, then the same
/// quote.
fn is_string_spelling(spelling: &str) -> bool {
    let mut chars = spelling.chars();
    match (chars.next(), chars.next_back()) {
        (Some(first), Some(last)) => first == last && (first == '"' || first == '\''),
        _ => false,
    }
}

/// SPEC 12.5 Quotes, from a literal's spelling: double quotes unless the text holds
/// more `"` than `'`, the escapes of the other quote dropped, the chosen quote
/// escaped wherever the text holds it, and every other escape kept, as Prettier
/// does. `forced` picks the quote.
fn requote(spelling: &str, forced: Option<char>) -> String {
    let content = &spelling[1..spelling.len() - 1];
    let doubles = content.matches('"').count();
    let singles = content.matches('\'').count();
    let quote = forced.unwrap_or(if doubles > singles { '\'' } else { '"' });
    let other = if quote == '"' { '\'' } else { '"' };
    let mut out = String::with_capacity(spelling.len() + 2);
    out.push(quote);
    let mut chars = content.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some(next) if next == other => out.push(next),
                Some(next) => {
                    out.push('\\');
                    out.push(next);
                }
                None => out.push('\\'),
            }
        } else if c == quote {
            out.push('\\');
            out.push(c);
        } else {
            out.push(c);
        }
    }
    out.push(quote);
    out
}

/// A string literal written from its value, for a tree with no source: the quote by
/// the same count, and an escape for the quote, `\`, and control characters.
fn quote_value(value: &str, forced: Option<char>) -> String {
    let doubles = value.matches('"').count();
    let singles = value.matches('\'').count();
    let quote = forced.unwrap_or(if doubles > singles { '\'' } else { '"' });
    let mut out = String::with_capacity(value.len() + 2);
    out.push(quote);
    for c in value.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            c if c == quote => {
                out.push('\\');
                out.push(c);
            }
            c if c.is_control() => out.push_str(&format!("\\u{{{:X}}}", c as u32)),
            c => out.push(c),
        }
    }
    out.push(quote);
    out
}

/// Template text from its value: `` ` ``, `\` and a `$` before `{` escaped, and line
/// breaks and control characters written as escapes, so the template stays on one
/// line.
fn escape_template(value: &str, out: &mut String) {
    let mut chars = value.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '`' => out.push_str("\\`"),
            '\\' => out.push_str("\\\\"),
            '$' if chars.peek() == Some(&'{') => out.push_str("\\$"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            c if c.is_control() => out.push_str(&format!("\\u{{{:X}}}", c as u32)),
            c => out.push(c),
        }
    }
}

/// Whether `quoted`, a single-quoted string, would lex as a lifetime right after
/// `&` (SPEC 2), which the lexer itself answers.
fn lexes_as_lifetime(quoted: &str) -> bool {
    let file = SourceFile {
        id: FileId(0),
        path: PathBuf::new(),
        text: Arc::from(format!("&{quoted}")),
        start: BytePos(1),
        line_starts: vec![0],
        origin: FileOrigin::User,
    };
    let tokens = crate::lexer::lex(&file, &mut DiagCtx::new());
    matches!(
        tokens.get(1).map(|token| token.kind),
        Some(TokenKind::Lifetime(_))
    )
}

/// The span of an arm value, from its first token to its last.
fn arm_value_span(value: &ArmValue) -> Option<Span> {
    match value {
        ArmValue::Value(expr) => Some(expr.span),
        ArmValue::Null(span) | ArmValue::Ok(span) | ArmValue::Err(span) => Some(*span),
        ArmValue::Case(path) => Some(path.first()?.span.to(path.last()?.span)),
        ArmValue::Range(lo, hi) => Some(lo.span.to(hi.span)),
    }
}
