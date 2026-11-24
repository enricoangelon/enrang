//! Printing blocks by the Bodies rule, `if` and `else`, loops, declarations with the
//! Right-hand sides rule, and statement `match` with no `;` (SPEC 12.5).

use crate::ast::*;

use super::comments::SeqEl;
use super::doc::{
    Doc, GroupId, break_parent, concat, group_with, hardline, if_break, indent, line, nil,
    softline, text,
};
use super::exprs::{Arg, Ctx};
use super::{ListItem, ListOpts, Printer, pos};

impl Printer<'_> {
    pub(super) fn stmt(&mut self, stmt: &Stmt) -> Doc {
        match &stmt.kind {
            StmtKind::VarDecl(decl) => concat(vec![self.var_decl(decl), text(";")]),
            StmtKind::If(if_stmt) => self.if_stmt(if_stmt, false),
            StmtKind::While(w) => {
                let (cond, cond_id) = self.condition(&w.cond);
                let body = self.body(&w.body);
                let body = after_condition(cond_id, body);
                concat(vec![text("while "), cond, text(" "), body])
            }
            StmtKind::DoWhile(w) => {
                let body = self.body(&w.body).0;
                let (cond, _) = self.condition(&w.cond);
                concat(vec![text("do "), body, text(" while "), cond, text(";")])
            }
            StmtKind::For(f) => self.for_stmt(f),
            StmtKind::ForOf(f) => {
                let word = if f.mutable {
                    "for (let "
                } else {
                    "for (const "
                };
                let binding = self.binding(&f.binding);
                let of = if f.in_keyword.is_some() {
                    " in "
                } else {
                    " of "
                };
                let source = match &f.source {
                    ForOfSource::Expr(expr) => self.expr(expr),
                    ForOfSource::Range(lo, hi) => self.range(lo, hi),
                };
                let body = self.body(&f.body).0;
                concat(vec![
                    text(word),
                    binding,
                    text(of),
                    source,
                    text(") "),
                    body,
                ])
            }
            StmtKind::Return(value) => match value {
                Some(value) => {
                    let ret =
                        self.then_node(text("return"), " ", pos(value.span.lo), |p| p.expr(value));
                    concat(vec![ret, text(";")])
                }
                None => text("return;"),
            },
            StmtKind::Break(label) => concat(vec![self.jump("break", label.as_ref()), text(";")]),
            StmtKind::Continue(label) => {
                concat(vec![self.jump("continue", label.as_ref()), text(";")])
            }
            StmtKind::Block(block) => self.body(block).0,
            StmtKind::Unsafe(block) => concat(vec![text("unsafe "), self.body(block).0]),
            StmtKind::Labeled(label, inner) => {
                let label = self.ident(label);
                let inner = self.stmt(inner);
                concat(vec![label, text(": "), inner])
            }
            StmtKind::Expr(expr) => {
                let semi = if matches!(expr.kind, ExprKind::Match { .. }) {
                    nil()
                } else {
                    text(";")
                };
                concat(vec![self.expr(expr), semi])
            }
            StmtKind::LocalFn { decorators, decl } => {
                let decorators = self.decorators(decorators);
                concat(vec![decorators, self.function_decl(decl)])
            }
            StmtKind::Expect(expect) => self.expect(expect),
            StmtKind::Assert { cond, message } => concat(vec![
                self.assert_call(cond, message.as_ref(), stmt.span),
                text(";"),
            ]),
        }
    }

    /// A block in a body position (SPEC 12.5 Bodies): on one line when it holds one
    /// statement that holds no block of its own and the line fits, else one statement
    /// per line. Returns the id of its group.
    pub(super) fn body(&mut self, block: &Block) -> (Doc, GroupId) {
        let one_line = match block.stmts.as_slice() {
            [only] => !holds_block(only),
            _ => false,
        };
        self.block(block, one_line)
    }

    fn block(&mut self, block: &Block, one_line: bool) -> (Doc, GroupId) {
        let (open, close) = if self.has_place(block.span) {
            (
                Some(pos(block.span.lo) + 1),
                Some(pos(block.span.hi).saturating_sub(1)),
            )
        } else {
            (None, None)
        };
        // A comment before the `{` stays before it when it is a block comment on the
        // brace's line; any other goes inside, since `{` never goes on a line by
        // itself (SPEC 12.5 Signatures).
        let lead = if self.has_place(block.span) && self.inline_before(pos(block.span.lo)) {
            self.leading(pos(block.span.lo))
        } else {
            nil()
        };
        let els: Vec<SeqEl<&Stmt>> = block
            .stmts
            .iter()
            .map(|stmt| SeqEl::new(stmt.span, stmt))
            .collect();
        let seq = self.seq(open, close, &els, false, |p, stmt| p.stmt(stmt));
        let (doc, id) = self.braces(seq, one_line);
        (concat(vec![lead, doc]), id)
    }

    /// `if`: with an `else`, every branch splits, and `else` goes on the `}` line
    /// unless a comment follows the `}`.
    fn if_stmt(&mut self, if_stmt: &IfStmt, in_chain: bool) -> Doc {
        let split = in_chain || if_stmt.else_branch.is_some();
        let (cond, cond_id) = self.condition(&if_stmt.cond);
        let then = if split {
            self.block(&if_stmt.then_block, false).0
        } else {
            let body = self.body(&if_stmt.then_block);
            after_condition(cond_id, body)
        };
        let head = concat(vec![text("if "), cond, text(" "), then]);
        let Some(branch) = &if_stmt.else_branch else {
            return head;
        };
        let else_at = match branch {
            ElseBranch::If(nested) => nested.span,
            ElseBranch::Block(block) => block.span,
        };
        let mut between = Vec::new();
        if self.has_place(else_at) {
            let trailing = self.take_trailing(pos(if_stmt.then_block.span.hi), false);
            between.push(self.trailing_doc(&trailing));
            for comment in self.take_before(pos(else_at.lo)) {
                between.push(hardline());
                between.push(self.comment_doc(&comment));
            }
        }
        let branch = match branch {
            ElseBranch::If(nested) => self.if_stmt(nested, true),
            ElseBranch::Block(block) => self.block(block, false).0,
        };
        let joint = if between.iter().all(Doc::is_nil) {
            text(" else ")
        } else {
            concat(vec![
                concat(between),
                break_parent(),
                hardline(),
                text("else "),
            ])
        };
        concat(vec![head, joint, branch])
    }

    /// `(cond)` of `if`, `while` and `do`, and the id of its group: when it breaks,
    /// `(`, the operands one per line, then `)` (SPEC 12.5 Operators).
    fn condition(&mut self, cond: &Expr) -> (Doc, GroupId) {
        let cond = self.expr_ctx(cond, Ctx::Cond);
        let id = self.group_id();
        let doc = group_with(
            id,
            false,
            concat(vec![
                text("("),
                indent(concat(vec![softline(), cond])),
                softline(),
                text(")"),
            ]),
        );
        (doc, id)
    }

    /// `for (init; cond; step)`: a header that does not fit breaks as a condition
    /// does, `for (`, its three parts one per line, then `) {` (SPEC 12.5
    /// Operators), and its body splits.
    fn for_stmt(&mut self, f: &ForStmt) -> Doc {
        let mut parts = vec![softline()];
        match &f.init {
            Some(ForInit::VarDecl(decl)) => parts.push(self.var_decl(decl)),
            Some(ForInit::Expr(expr)) => parts.push(self.expr(expr)),
            None => {}
        }
        parts.push(text(";"));
        if let Some(cond) = &f.cond {
            parts.push(line());
            parts.push(self.expr(cond));
        }
        parts.push(text(";"));
        if let Some(step) = &f.step {
            parts.push(line());
            parts.push(self.expr(step));
        }
        let id = self.group_id();
        let head = group_with(
            id,
            false,
            concat(vec![
                text("("),
                indent(concat(parts)),
                softline(),
                text(")"),
            ]),
        );
        let body = self.body(&f.body);
        let body = after_condition(id, body);
        concat(vec![text("for "), head, text(" "), body])
    }

    /// `const x: T = value`, with no `;`.
    fn var_decl(&mut self, decl: &VarDecl) -> Doc {
        let word = text(if decl.mutable { "let " } else { "const " });
        let binding = self.binding(&decl.binding);
        let ty = match &decl.ty {
            Some(ty) => concat(vec![text(": "), self.ty(ty)]),
            None => nil(),
        };
        let lhs = concat(vec![word, binding, ty]);
        match &decl.init {
            Some(init) => self.rhs(lhs, "=", init),
            None => lhs,
        }
    }

    pub(super) fn binding(&mut self, binding: &Binding) -> Doc {
        match binding {
            Binding::Name(name) => self.ident(name),
            Binding::Object { fields, span } => {
                let opts = ListOpts::braces().close_at(self.close_of(*span));
                self.list(
                    fields,
                    |(name, inner)| match inner {
                        Some(inner) => name.span.to(binding_span(inner)),
                        None => name.span,
                    },
                    |p, (name, inner)| {
                        let name = p.ident(name);
                        let doc = match inner {
                            Some(inner) => concat(vec![name, text(": "), p.binding(inner)]),
                            None => name,
                        };
                        ListItem::plain(doc)
                    },
                    opts,
                )
                .doc
            }
            Binding::Tuple { elems, span } => {
                let opts = ListOpts::new("[", "]").close_at(self.close_of(*span));
                self.list(
                    elems,
                    binding_span,
                    |p, elem| ListItem::plain(p.binding(elem)),
                    opts,
                )
                .doc
            }
        }
    }

    /// `expect(actual)[.not].matcher(args);`.
    fn expect(&mut self, expect: &ExpectStmt) -> Doc {
        let close = self.closer_after(pos(expect.actual.span.hi), crate::token::Punct::RParen);
        let actual = self.arg_list(&[Arg::Expr(&expect.actual)], close);
        let not = if expect.negated { text(".not") } else { nil() };
        let matcher = self.ident(&expect.matcher);
        let args: Vec<Arg<'_>> = expect
            .args
            .iter()
            .map(|arg| match arg {
                MatcherArg::Expr(expr) => Arg::Expr(expr),
                MatcherArg::Arm(value) => Arg::Arm(value),
            })
            .collect();
        let close = self.has_place(expect.span).then(|| {
            let end = pos(expect.span.hi);
            if self.slice(end.saturating_sub(1), end) == ";" {
                end.saturating_sub(2)
            } else {
                end.saturating_sub(1)
            }
        });
        let args = self.arg_list(&args, close);
        concat(vec![
            text("expect"),
            actual,
            not,
            text("."),
            matcher,
            args,
            text(";"),
        ])
    }

    /// `assert(cond, "message")`, with no `;`.
    pub(super) fn assert_call(
        &mut self,
        cond: &Expr,
        message: Option<&StrLit>,
        span: enrang_base::Span,
    ) -> Doc {
        let mut args = vec![Arg::Expr(cond)];
        if let Some(message) = message {
            args.push(Arg::Str(message));
        }
        let last = args.last().map_or(span, Arg::span);
        let close = self.closer_after(pos(last.hi), crate::token::Punct::RParen);
        concat(vec![text("assert"), self.arg_list(&args, close)])
    }
}

/// The body after a condition or a parameter list, group `cond`: one statement per
/// line when that group broke, so that a broken condition ends with `) {` and broken
/// parameters with `): Ret {` on a line of their own (SPEC 12.5 Operators,
/// Signatures), else by the Bodies rule.
pub(super) fn after_condition(cond: GroupId, (body, id): (Doc, GroupId)) -> Doc {
    match body.with_broken(id) {
        Some(broken) => if_break(Some(cond), broken, body),
        None => body,
    }
}

/// SPEC 12.5 Bodies: whether a statement holds a block of its own, so its body cannot
/// go on one line: any statement with a block, and a `match` or a block-bodied arrow
/// anywhere in an expression.
pub(super) fn holds_block(stmt: &Stmt) -> bool {
    match &stmt.kind {
        StmtKind::VarDecl(decl) => decl.init.as_ref().is_some_and(expr_holds_block),
        StmtKind::Return(value) => value.as_ref().is_some_and(expr_holds_block),
        StmtKind::Expr(expr) => expr_holds_block(expr),
        StmtKind::Break(_) | StmtKind::Continue(_) => false,
        StmtKind::Expect(expect) => {
            expr_holds_block(&expect.actual)
                || expect.args.iter().any(|arg| match arg {
                    MatcherArg::Expr(expr) => expr_holds_block(expr),
                    MatcherArg::Arm(_) => false,
                })
        }
        StmtKind::Assert { cond, .. } => expr_holds_block(cond),
        StmtKind::If(_)
        | StmtKind::While(_)
        | StmtKind::DoWhile(_)
        | StmtKind::For(_)
        | StmtKind::ForOf(_)
        | StmtKind::Block(_)
        | StmtKind::Unsafe(_)
        | StmtKind::Labeled(..)
        | StmtKind::LocalFn { .. } => true,
    }
}

pub(super) fn expr_holds_block(expr: &Expr) -> bool {
    let any = |exprs: &[Expr]| exprs.iter().any(expr_holds_block);
    let fields = |fields: &[FieldInit]| {
        fields
            .iter()
            .any(|field| field.value.as_ref().is_some_and(expr_holds_block))
    };
    match &expr.kind {
        ExprKind::Match { .. } => true,
        ExprKind::Arrow(arrow) => match &arrow.body {
            ArrowBody::Block(_) => true,
            ArrowBody::Expr(body) => expr_holds_block(body),
        },
        ExprKind::Int { .. }
        | ExprKind::Float(_)
        | ExprKind::Str(_)
        | ExprKind::RawTemplate(_)
        | ExprKind::Bool(_)
        | ExprKind::Null
        | ExprKind::Ident(_)
        | ExprKind::This
        | ExprKind::Super
        | ExprKind::TypeMember { .. }
        | ExprKind::SizeForm(_)
        | ExprKind::Error => false,
        ExprKind::Template(parts) => parts.iter().any(|part| match part {
            TplPart::Expr(expr) => expr_holds_block(expr),
            TplPart::Str(_) => false,
        }),
        ExprKind::Paren(inner)
        | ExprKind::Unary(_, inner)
        | ExprKind::Borrow(inner)
        | ExprKind::Deref(inner)
        | ExprKind::VoidOp(inner)
        | ExprKind::Cast(inner, _)
        | ExprKind::Try(inner)
        | ExprKind::NonNull(inner)
        | ExprKind::Member { base: inner, .. }
        | ExprKind::IncDec { target: inner, .. } => expr_holds_block(inner),
        ExprKind::Array(elems) => elems.iter().any(|elem| match elem {
            ArrayElem::Item(expr) | ArrayElem::Spread { expr, .. } => expr_holds_block(expr),
        }),
        ExprKind::Repeat(a, b)
        | ExprKind::Binary(_, a, b)
        | ExprKind::Logical(_, a, b)
        | ExprKind::Coalesce(a, b)
        | ExprKind::Index(a, b)
        | ExprKind::Assign {
            target: a,
            value: b,
            ..
        } => expr_holds_block(a) || expr_holds_block(b),
        ExprKind::Ternary(a, b, c) => {
            expr_holds_block(a) || expr_holds_block(b) || expr_holds_block(c)
        }
        ExprKind::New { init, .. } => match init {
            NewInit::Args(args) => any(args),
            NewInit::Fields(list) => fields(list),
        },
        ExprKind::CaseLit { fields: list, .. } | ExprKind::ObjectLit(list) => fields(list),
        ExprKind::Asm(asm) => {
            expr_holds_block(&asm.template)
                || asm
                    .options
                    .iter()
                    .flatten()
                    .any(|option| match &option.kind {
                        AsmOptionKind::In(regs) | AsmOptionKind::Out(regs) => regs
                            .iter()
                            .any(|reg| reg.value.as_ref().is_some_and(expr_holds_block)),
                        AsmOptionKind::Clobbers(_) => false,
                    })
        }
        ExprKind::Call { callee, args, .. } => expr_holds_block(callee) || any(args),
    }
}

pub(super) fn binding_span(binding: &Binding) -> enrang_base::Span {
    match binding {
        Binding::Name(name) => name.span,
        Binding::Object { span, .. } | Binding::Tuple { span, .. } => *span,
    }
}
