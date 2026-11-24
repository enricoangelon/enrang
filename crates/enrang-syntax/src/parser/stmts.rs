//! SPEC 3.3 statements: blocks, `let` and `const` with destructuring, `if` and the
//! loops, `for...of` and its range source, labels, `break` and `continue`,
//! `return`, `unsafe` blocks, `expect` statements (SPEC 3.6) and expression
//! statements, with the statement-`match` rule: a statement that starts with
//! `match` ends at its `}` and an optional `;`.

use enrang_base::{BytePos, Span};
use enrang_diag::{Code, Diagnostic, Edit, Help, did_you_mean};

use super::{Parser, Scope, hints, is_named, recover};
use crate::ast::{
    Binding, Block, ElseBranch, ExpectStmt, Expr, ForInit, ForOfSource, ForOfStmt, ForStmt, Ident,
    IfStmt, MatcherArg, Stmt, StmtKind, VarDecl, WhileStmt,
};
use crate::token::{Contextual, Keyword, Punct, Reserved, Token, TokenKind};

/// The span of a binding: its name, or its whole pattern.
fn binding_span(binding: &Binding) -> Span {
    match binding {
        Binding::Name(name) => name.span,
        Binding::Object { span, .. } | Binding::Tuple { span, .. } => *span,
    }
}

impl Parser<'_> {
    /// `Block = "{" { Stmt } "}"`; the span covers both braces.
    pub(super) fn parse_block(&mut self) -> Block {
        let lo = self.lo();
        if !self.expect(Punct::LBrace) {
            return Block {
                stmts: Vec::new(),
                span: self.span_from(lo),
            };
        }
        let mut stmts = Vec::new();
        while !self.at(Punct::RBrace) && !self.at_eof() {
            let before = self.pos;
            if let Some(stmt) = self.parse_stmt() {
                stmts.push(stmt);
            }
            if self.pos == before {
                self.expected("a statement");
                self.bump();
            }
        }
        // The EN0102 pass gave every `{` its `}`.
        self.expect(Punct::RBrace);
        Block {
            stmts,
            span: self.span_from(lo),
        }
    }

    /// One statement, or `None` when there was none to keep.
    pub(super) fn parse_stmt(&mut self) -> Option<Stmt> {
        if !self.enter() {
            recover::skip_stmt(self);
            return None;
        }
        let stmt = self.parse_stmt_inner();
        self.leave();
        stmt
    }

    fn parse_stmt_inner(&mut self) -> Option<Stmt> {
        let lo = self.lo();
        let token = self.peek();
        let kind = match token.kind {
            TokenKind::Punct(Punct::LBrace) => {
                let object = self.object_field_at(self.pos + 1);
                let block = self.parse_block();
                if object {
                    // `{ name: "Ada", age: 36 };` had its EN0100 inside; its `;`
                    // goes with it.
                    self.eat(Punct::Semi);
                }
                StmtKind::Block(block)
            }
            TokenKind::Keyword(Keyword::Let | Keyword::Const) => {
                let decl = self.parse_var_decl();
                recover::expect_semi(self);
                StmtKind::VarDecl(decl)
            }
            TokenKind::Keyword(Keyword::If) => StmtKind::If(self.parse_if()),
            TokenKind::Keyword(Keyword::While) => {
                let label = self.next_label.take();
                let keyword = self.bump();
                let cond = self.parse_condition();
                let body = self.within(Scope::Loop(label), |p| p.parse_body(keyword));
                StmtKind::While(WhileStmt {
                    cond,
                    body,
                    span: self.span_from(lo),
                })
            }
            TokenKind::Keyword(Keyword::Do) => {
                let label = self.next_label.take();
                let keyword = self.bump();
                let body = self.within(Scope::Loop(label), |p| p.parse_body(keyword));
                self.expect_kw(Keyword::While);
                let cond = self.parse_condition();
                let span = self.span_from(lo);
                recover::expect_semi(self);
                StmtKind::DoWhile(WhileStmt { cond, body, span })
            }
            TokenKind::Keyword(Keyword::For) => self.parse_for()?,
            TokenKind::Keyword(Keyword::Return) => {
                self.bump();
                let ends = self.at(Punct::Semi) || self.at(Punct::RBrace) || self.at_eof();
                let value = (!ends).then(|| self.parse_expr());
                recover::expect_semi(self);
                StmtKind::Return(value)
            }
            TokenKind::Keyword(Keyword::Break) => {
                let keyword = self.bump();
                let label = self.optional_label();
                self.check_jump(keyword, label);
                recover::expect_semi(self);
                StmtKind::Break(label)
            }
            TokenKind::Keyword(Keyword::Continue) => {
                let keyword = self.bump();
                let label = self.optional_label();
                self.check_jump(keyword, label);
                recover::expect_semi(self);
                StmtKind::Continue(label)
            }
            TokenKind::Keyword(Keyword::Unsafe) if self.nth_is(1, Punct::LBrace) => {
                self.bump();
                StmtKind::Unsafe(self.parse_block())
            }
            TokenKind::Keyword(Keyword::Match) => {
                let subject = self.parse_match();
                let span = self.span_from(lo);
                self.eat(Punct::Semi);
                return Some(self.mk_stmt(StmtKind::Expr(subject), span));
            }
            TokenKind::Ident(_) if self.nth_is(1, Punct::Colon) => return self.parse_labeled(),
            TokenKind::Ident(_) if self.at_word(Contextual::Expect) && self.expect_ahead() => {
                StmtKind::Expect(self.parse_expect_stmt())
            }
            _ => {
                if let Some(stmt) = hints::stmt_start(self) {
                    return stmt;
                }
                let before = self.pos;
                let expr = self.parse_expr();
                if self.pos == before {
                    // Nothing here starts a statement; the caller reports the token.
                    return None;
                }
                recover::expect_semi(self);
                StmtKind::Expr(expr)
            }
        };
        let span = self.span_from(lo);
        Some(self.mk_stmt(kind, span))
    }

    /// `"(" Expr ")"`, the condition of `if`, `while` and `do`.
    fn parse_condition(&mut self) -> Expr {
        if !self.expect(Punct::LParen) {
            return self.error_expr();
        }
        let cond = self.parse_expr();
        self.check_assignment(&cond, "a condition");
        self.expect(Punct::RParen);
        cond
    }

    /// The braced body of `if`, `else`, `while`, `do` and `for`, after `keyword`.
    /// Anything else is EN0104, and one statement taken as the body.
    fn parse_body(&mut self, keyword: Token) -> Block {
        if self.at(Punct::LBrace) {
            return self.parse_block();
        }
        if self.at(Punct::RBrace) || self.at(Punct::Semi) || self.at_eof() {
            self.expected("`{`");
            self.eat(Punct::Semi);
            return Block {
                stmts: Vec::new(),
                span: self.here(),
            };
        }
        let head_end = self.prev_hi();
        let stmts: Vec<Stmt> = self.parse_stmt().into_iter().collect();
        let span = match (stmts.first(), stmts.last()) {
            (Some(first), Some(last)) => first.span.to(last.span),
            _ => self.here(),
        };
        if !stmts.is_empty() {
            self.braces_required(keyword, head_end, span);
        }
        Block { stmts, span }
    }

    /// EN0104 at `body`, the one statement after `keyword` with no braces (SPEC
    /// 3.3). The fix-it wraps the statement and the lines after it indented under
    /// the keyword, and the first of those lines gets a second label.
    fn braces_required(&mut self, keyword: Token, head_end: BytePos, body: Span) {
        let word = self.text(keyword.span).to_owned();
        let indent = self.indent_of(keyword.span.lo).to_owned();
        let width = indent.chars().count();
        let start = self.file.start.0;
        let text: &str = &self.file.text;
        let offset = |pos: BytePos| pos.0.saturating_sub(start) as usize;
        let at = |offset: usize| BytePos(start + offset as u32);
        // The end of the body's last line, and of each line after it indented under
        // the keyword, past blank lines.
        let body_line_end = text[offset(body.hi)..]
            .find('\n')
            .map_or(text.len(), |nl| offset(body.hi) + nl);
        let mut end = offset(body.hi) + text[offset(body.hi)..body_line_end].trim_end().len();
        let mut first_extra = None;
        let mut line_start = body_line_end + 1;
        while line_start < text.len() {
            let line_end = text[line_start..]
                .find('\n')
                .map_or(text.len(), |nl| line_start + nl);
            let line = text[line_start..line_end].trim_end();
            let content = line.trim_start_matches([' ', '\t']);
            if !content.is_empty() {
                let leading = &line[..line.len() - content.len()];
                if leading.chars().count() <= width {
                    break;
                }
                let content_lo = line_start + leading.len();
                first_extra.get_or_insert(Span {
                    lo: at(content_lo),
                    hi: at(line_start + line.len()),
                });
                end = line_start + line.len();
            }
            line_start = line_end + 1;
        }
        let same_line = !self
            .text(Span {
                lo: head_end,
                hi: body.lo,
            })
            .contains('\n');
        let close = format!("\n{indent}}}");
        let mut edits = Vec::new();
        if same_line {
            edits.push(Edit::insert(body.lo, "{ "));
            if first_extra.is_none() {
                edits.push(Edit::insert(body.hi, " }"));
            } else {
                edits.push(Edit::insert(at(end), close));
            }
        } else {
            edits.push(Edit::insert(head_end, " {"));
            edits.push(Edit::insert(at(end), close));
        }
        let mut diag = Diagnostic::new(
            Code::EN0104,
            format!("`{word}` needs braces around its body"),
            body,
            "this statement is not in braces",
        );
        let help = match first_extra {
            Some(extra) => {
                diag = diag
                    .with_secondary(extra, format!("indented as if it were inside the `{word}`"));
                Help::suggest(
                    format!("put the lines indented under the `{word}` in braces"),
                    edits,
                )
            }
            None => Help::machine("add braces around the body", edits),
        };
        self.emit(diag.with_help(help));
    }

    /// `IfStmt = "if" "(" Expr ")" Block [ "else" ( IfStmt | Block ) ]`.
    fn parse_if(&mut self) -> IfStmt {
        let lo = self.lo();
        let keyword = self.bump();
        let cond = self.parse_condition();
        let then_block = self.parse_body(keyword);
        let else_word = self.peek();
        let else_branch = if self.eat_kw(Keyword::Else) {
            if self.at_kw(Keyword::If) && self.enter() {
                let nested = self.parse_if();
                self.leave();
                Some(ElseBranch::If(Box::new(nested)))
            } else {
                Some(ElseBranch::Block(self.parse_body(else_word)))
            }
        } else {
            None
        };
        IfStmt {
            cond,
            then_block,
            else_branch,
            span: self.span_from(lo),
        }
    }

    /// `VarDecl` without its `;`: `("let" | "const") Binding [ ":" Type ] [ "=" Expr ]`.
    pub(super) fn parse_var_decl(&mut self) -> VarDecl {
        let lo = self.lo();
        let mutable = self.bump().is_keyword(Keyword::Let);
        let binding = self.parse_binding();
        self.finish_var_decl(lo, mutable, binding)
    }

    pub(super) fn finish_var_decl(
        &mut self,
        lo: BytePos,
        mutable: bool,
        binding: Binding,
    ) -> VarDecl {
        let ty = self.eat(Punct::Colon).then(|| self.parse_type());
        let init = if self.eat(Punct::Eq) {
            // `let y = undefined;`: EN0206's fix-it also gives `y` a nullable type.
            if ty.is_none()
                && let Binding::Name(name) = &binding
                && self.peek().kind == TokenKind::Reserved(Reserved::Undefined)
            {
                let next = self.nth(1);
                if next.is(Punct::Semi)
                    || next.is(Punct::RBrace)
                    || next.kind == TokenKind::Eof
                    || self.line_break_before(self.pos + 1)
                {
                    self.undefined_init = Some((self.lo(), name.span.hi));
                }
            }
            let init = self.parse_expr();
            self.undefined_init = None;
            Some(init)
        } else {
            None
        };
        if init.is_none() {
            if !mutable {
                self.const_without_value(&binding);
            } else if !matches!(binding, Binding::Name(_)) {
                self.expected("`=` after a destructuring pattern");
            }
        }
        VarDecl {
            mutable,
            binding,
            ty,
            init,
            span: self.span_from(lo),
        }
    }

    /// EN0116 at `binding`, a `const` that is given no value. A name that recovery
    /// put where none could be read, after its EN0100, is no second mistake.
    pub(super) fn const_without_value(&mut self, binding: &Binding) {
        let label = match binding {
            Binding::Name(name) if name.name.as_str().is_empty() => return,
            Binding::Name(name) => format!("`{}` is never given a value", name.name),
            _ => "this pattern is never given a value".to_owned(),
        };
        self.emit(
            Diagnostic::new(
                Code::EN0116,
                "a `const` needs a value",
                binding_span(binding),
                label,
            )
            .with_help(Help::text("give it a value, or use `let`")),
        );
    }

    /// `Binding = Ident | ObjPattern | TuplePattern`, nesting.
    pub(super) fn parse_binding(&mut self) -> Binding {
        let lo = self.lo();
        if !self.enter() {
            return Binding::Tuple {
                elems: Vec::new(),
                span: self.here(),
            };
        }
        let token = self.peek();
        let binding = match token.kind {
            TokenKind::Ident(_) => Binding::Name(self.ident_or_error()),
            // `const type = 1;`, a name TypeScript allows: EN0100, and the word is
            // still the name when what follows ends a binding, so the rest of the
            // declaration parses as written.
            TokenKind::Keyword(_) | TokenKind::Reserved(_) if self.binding_ends(1) => {
                self.expected("a name or a pattern");
                self.bump();
                Binding::Name(Ident {
                    name: super::word(token).unwrap_or_else(|| enrang_base::intern("")),
                    span: token.span,
                })
            }
            TokenKind::Punct(Punct::LBrace) => {
                self.bump();
                let fields = self.comma_list(Punct::RBrace, |p| {
                    if p.at(Punct::DotDotDot) {
                        hints::spread_outside_array(p);
                    }
                    let name = p.member_name()?;
                    let sub = p.eat(Punct::Colon).then(|| p.parse_binding());
                    p.pattern_default();
                    Some((name, sub))
                });
                Binding::Object {
                    fields,
                    span: self.span_from(lo),
                }
            }
            TokenKind::Punct(Punct::LBracket) => {
                self.bump();
                let elems = self.comma_list(Punct::RBracket, |p| {
                    if p.at(Punct::DotDotDot) {
                        hints::spread_outside_array(p);
                    }
                    let elem = p.parse_binding();
                    p.pattern_default();
                    Some(elem)
                });
                Binding::Tuple {
                    elems,
                    span: self.span_from(lo),
                }
            }
            _ => {
                self.expected("a name or a pattern");
                Binding::Name(self.error_ident())
            }
        };
        self.leave();
        binding
    }

    /// Whether the token `n` ahead can follow a binding: `=`, `:`, `?`, a closer, a
    /// separator, or the `of` or `in` of a loop.
    fn binding_ends(&self, n: usize) -> bool {
        let token = self.nth(n);
        [
            Punct::Eq,
            Punct::Colon,
            Punct::Question,
            Punct::Semi,
            Punct::Comma,
            Punct::RParen,
            Punct::RBracket,
            Punct::RBrace,
        ]
        .into_iter()
        .any(|p| token.is(p))
            || is_named(token, "of")
            || is_named(token, "in")
    }

    /// A `= default` inside a pattern, parsed and dropped.
    fn pattern_default(&mut self) {
        if !self.at(Punct::Eq) {
            return;
        }
        let eq = self.bump().span;
        hints::report_deferred(self, Code::EN1010, eq, "a default in a pattern");
        self.parse_expr();
    }

    /// `ForStmt` or `ForOfStmt`, told apart by the contextual `of` after the binding.
    /// TypeScript's `in` there is kept as a `ForOf` with `in_keyword`, for sema's
    /// EN1015 (SPEC 16). TypeScript's `for await` is EN1001, and the loop goes on as
    /// the `for` it would be without `await`. A head with no `(` is one EN0100, and
    /// the statement is skipped, so none of it is read again as other statements
    /// (ARCHITECTURE 4).
    fn parse_for(&mut self) -> Option<StmtKind> {
        let label = self.next_label.take();
        let lo = self.lo();
        let for_word = self.bump();
        if self.peek().kind == TokenKind::Reserved(Reserved::Await) {
            let span = self.bump().span;
            hints::report_deferred(self, Code::EN1001, span, "waits for each promise");
        }
        if !self.expect(Punct::LParen) {
            recover::skip_stmt(self);
            return None;
        }
        let var = self.peek().kind == TokenKind::Reserved(Reserved::Var);
        if var {
            hints::report_var(self);
        }
        let init = if var || self.at_kw(Keyword::Let) || self.at_kw(Keyword::Const) {
            let decl_lo = self.lo();
            let mutable = var || self.bump().is_keyword(Keyword::Let);
            if var {
                self.bump();
            }
            let binding = self.parse_binding();
            if self.at_word(Contextual::Of) || self.at_word(Contextual::In) {
                let keyword = self.bump();
                let in_keyword = is_named(keyword, "in").then_some(keyword.span);
                let source = self.parse_for_source();
                self.expect(Punct::RParen);
                let body = self.within(Scope::Loop(label), |p| p.parse_body(for_word));
                return Some(StmtKind::ForOf(ForOfStmt {
                    mutable,
                    binding,
                    in_keyword,
                    source,
                    body,
                    span: self.span_from(lo),
                }));
            }
            let decl = self.finish_var_decl(decl_lo, mutable, binding);
            self.expect(Punct::Semi);
            Some(ForInit::VarDecl(decl))
        } else if self.eat(Punct::Semi) {
            None
        } else {
            let expr = self.parse_expr();
            if self.at_word(Contextual::Of) || self.at_word(Contextual::In) {
                // `for (x of xs)`: the loop's variable is declared, so the rest of
                // the head is skipped after one EN0100.
                self.for_without_binding(&expr);
                recover::skip_until(self, &[Punct::RParen]);
                self.expect(Punct::RParen);
                let body = self.within(Scope::Loop(label), |p| p.parse_body(for_word));
                return Some(StmtKind::For(ForStmt {
                    init: Some(ForInit::Expr(expr)),
                    cond: None,
                    step: None,
                    body,
                    span: self.span_from(lo),
                }));
            }
            self.expect(Punct::Semi);
            Some(ForInit::Expr(expr))
        };
        let cond = (!self.at(Punct::Semi)).then(|| self.parse_expr());
        if let Some(cond) = &cond {
            self.check_assignment(cond, "a condition");
        }
        self.expect(Punct::Semi);
        let step = (!self.at(Punct::RParen)).then(|| self.parse_expr());
        self.expect(Punct::RParen);
        let body = self.within(Scope::Loop(label), |p| p.parse_body(for_word));
        Some(StmtKind::For(ForStmt {
            init,
            cond,
            step,
            body,
            span: self.span_from(lo),
        }))
    }

    /// EN0100 at the `of` or `in` of `for (x of xs)`, whose variable `init` has no
    /// `const` or `let`: the fix-it declares it `const`.
    fn for_without_binding(&mut self, init: &Expr) {
        let token = self.peek();
        let word = self.text(token.span).to_owned();
        let mut diag = Diagnostic::new(
            Code::EN0100,
            format!("expected `;`, found `{word}`"),
            token.span,
            format!("a `for...{word}` loop declares its variable"),
        );
        if let crate::ast::ExprKind::Ident(_) = init.kind {
            diag = diag.with_help(Help::suggest(
                "declare it with `const`",
                vec![Edit::insert(init.span.lo, "const ")],
            ));
        }
        self.emit(diag);
    }

    /// `ForSource = Expr ".." Expr | Expr`. `...` after a complete expression is
    /// EN0100 with a fix-it to `..`, and recovers as the range (SPEC 3.4).
    fn parse_for_source(&mut self) -> ForOfSource {
        let start = self.parse_expr();
        if self.eat(Punct::DotDot) {
            return ForOfSource::Range(start, self.parse_expr());
        }
        if self.at(Punct::DotDotDot) {
            let span = self.peek().span;
            self.emit(
                Diagnostic::new(
                    Code::EN0100,
                    "expected `..` or `)`, found `...`",
                    span,
                    "a range is written with `..`",
                )
                .with_help(Help::machine(
                    "write the range with `..`",
                    vec![Edit::replace(span, "..")],
                )),
            );
            self.bump();
            return ForOfSource::Range(start, self.parse_expr());
        }
        ForOfSource::Expr(start)
    }

    /// `break` or `continue` at `keyword`, with its `label`: EN0111 outside a loop
    /// or across an arrow's body, EN0112 for a label no enclosing loop has (SPEC
    /// 3.3).
    pub(super) fn check_jump(&mut self, keyword: Token, label: Option<Ident>) {
        let word = self.text(keyword.span).to_owned();
        let mut arrow = None;
        let mut visible: Vec<&'static str> = Vec::new();
        let mut found = false;
        for scope in self.scopes.iter().rev() {
            match scope {
                Scope::Loop(own) => {
                    let matches = match label {
                        None => true,
                        Some(label) => own.is_some_and(|own| own.name == label.name),
                    };
                    if matches {
                        found = true;
                        break;
                    }
                    if arrow.is_none()
                        && let Some(own) = own
                    {
                        visible.push(own.name.as_str());
                    }
                }
                Scope::Arrow(head) => {
                    arrow.get_or_insert(*head);
                }
                Scope::Block(own) => {
                    if label.is_some_and(|label| label.name == own.name) {
                        found = true;
                        break;
                    }
                }
                Scope::Function => break,
            }
        }
        let diag = match (found, arrow, label) {
            (true, None, _) => return,
            (true, Some(head), _) => Diagnostic::new(
                Code::EN0111,
                format!("`{word}` cannot leave an arrow's body"),
                keyword.span,
                "the loop is outside the arrow",
            )
            .with_secondary(head, "this arrow's body is a function of its own")
            .with_help(Help::text(
                "return from the arrow, and act on its result in the loop",
            )),
            (false, _, Some(label)) => {
                let name = label.name.as_str();
                let mut diag = Diagnostic::new(
                    Code::EN0112,
                    format!("no enclosing loop is labelled `{name}`"),
                    label.span,
                    "unknown label",
                );
                if let Some(near) = did_you_mean(name, &visible) {
                    diag = diag.with_help(Help::suggest(
                        format!("did you mean `{near}`?"),
                        vec![Edit::replace(label.span, near)],
                    ));
                }
                diag
            }
            (false, _, None) => Diagnostic::new(
                Code::EN0111,
                format!("`{word}` outside a loop"),
                keyword.span,
                "no loop encloses it",
            ),
        };
        self.emit(diag);
    }

    /// `LabeledStmt = Ident ":" ( WhileStmt | DoStmt | ForStmt | ForOfStmt )`. A
    /// label on a block is EN1038, and a label already in scope EN0113.
    fn parse_labeled(&mut self) -> Option<Stmt> {
        let lo = self.lo();
        let object = self.object_field_at(self.pos);
        let open = self.tokens[self.pos.saturating_sub(1)].span;
        let label = self.ident_or_error();
        let colon = self.bump();
        if self.at(Punct::LBrace) {
            hints::report_deferred(
                self,
                Code::EN1038,
                label.span.to(colon.span),
                "a label on a block",
            );
            let block = self.within(Scope::Block(label), |p| p.parse_block());
            let span = self.span_from(lo);
            return Some(self.mk_stmt(StmtKind::Block(block), span));
        }
        let is_loop = [Keyword::While, Keyword::Do, Keyword::For]
            .into_iter()
            .any(|k| self.at_kw(k));
        if object {
            // `{ name: "Ada" }` where a statement starts, or after the `=>` of an
            // arrow or an arm: an object literal read as a block (SPEC 3.4). The
            // rest of the block goes with this one EN0100.
            self.emit(
                Diagnostic::new(
                    Code::EN0100,
                    "this `{` starts a block, not an object literal",
                    colon.span,
                    "a block holds statements, not fields",
                )
                .with_secondary(open, "a block starts here")
                .with_help(Help::text(
                    "an object literal here goes in parentheses: `({ ... })`",
                )),
            );
            recover::skip_until(self, &[]);
            return None;
        }
        if !is_loop {
            let span = self.peek().span;
            self.unexpected(
                span,
                format!(
                    "expected a loop after the label `{}`, found {}",
                    label.name,
                    self.describe(self.peek())
                ),
                "a label goes before a loop",
            );
            recover::skip_stmt(self);
            return None;
        }
        let outer = self
            .scopes
            .iter()
            .rev()
            .take_while(|scope| matches!(scope, Scope::Loop(_)))
            .find_map(|scope| match scope {
                Scope::Loop(Some(outer)) if outer.name == label.name => Some(outer.span),
                _ => None,
            });
        if let Some(outer) = outer {
            self.emit(
                Diagnostic::new(
                    Code::EN0113,
                    format!("the label `{}` is already in use", label.name),
                    label.span,
                    "this label",
                )
                .with_secondary(outer, "an enclosing loop has it")
                .with_help(Help::text("rename one of the two loops' labels")),
            );
        }
        self.next_label = Some(label);
        let body = self.parse_stmt();
        self.next_label = None;
        let span = self.span_from(lo);
        Some(self.mk_stmt(StmtKind::Labeled(label, Box::new(body?)), span))
    }

    /// Whether the token at `index` is the first field of an object literal that a
    /// block took in: an identifier and `:` right after a `{`, with no loop or `{`
    /// after the `:`, which would make the identifier a label.
    fn object_field_at(&self, index: usize) -> bool {
        let at = |i: usize| self.tokens.get(i).copied();
        index > 0
            && self.tokens[index - 1].is(Punct::LBrace)
            && at(index).is_some_and(|t| matches!(t.kind, TokenKind::Ident(_)))
            && at(index + 1).is_some_and(|t| t.is(Punct::Colon))
            && at(index + 2).is_some_and(|t| {
                !t.is(Punct::LBrace)
                    && ![Keyword::While, Keyword::Do, Keyword::For]
                        .into_iter()
                        .any(|k| t.is_keyword(k))
            })
    }

    /// Whether `expect ( ... ) [ . not ] . Ident (` starts here, which is always an
    /// `ExpectStmt` (SPEC 3.6).
    fn expect_ahead(&self) -> bool {
        if !self.nth_is(1, Punct::LParen) {
            return false;
        }
        let Some(close) = self.matching_close(self.pos + 1) else {
            return false;
        };
        if !self.tokens[close].is(Punct::RParen) {
            return false;
        }
        let at = |i: usize| self.tokens.get(i).copied();
        let mut next = close + 1;
        if !at(next).is_some_and(|t| t.is(Punct::Dot)) {
            return false;
        }
        next += 1;
        if at(next).is_some_and(|t| is_named(t, "not"))
            && at(next + 1).is_some_and(|t| t.is(Punct::Dot))
        {
            next += 2;
        }
        at(next).is_some_and(|t| matches!(t.kind, TokenKind::Ident(_)))
            && at(next + 1).is_some_and(|t| t.is(Punct::LParen))
    }

    /// `ExpectStmt = "expect" "(" Expr [ "," ] ")" [ "." "not" ] "." Ident
    /// "(" MatcherArg % "," ")" ";"`. `toMatchPattern` takes arm values, every
    /// other matcher expressions.
    fn parse_expect_stmt(&mut self) -> ExpectStmt {
        let lo = self.lo();
        self.bump();
        self.bump();
        let actual = self.parse_expr();
        self.eat(Punct::Comma);
        if !self.at(Punct::RParen) {
            self.expected("`)`");
            recover::skip_until(self, &[Punct::RParen]);
        }
        self.expect(Punct::RParen);
        self.expect(Punct::Dot);
        let negated = self.at_word(Contextual::Not) && self.nth_is(1, Punct::Dot);
        if negated {
            self.bump();
            self.bump();
        }
        let matcher = self.ident_or_error();
        let pattern = matcher.name.as_str() == "toMatchPattern";
        let args = if self.expect(Punct::LParen) {
            self.comma_list(Punct::RParen, |p| {
                Some(if pattern {
                    MatcherArg::Arm(p.parse_arm_value())
                } else {
                    MatcherArg::Expr(p.parse_expr())
                })
            })
        } else {
            Vec::new()
        };
        let span = self.span_from(lo);
        recover::expect_semi(self);
        ExpectStmt {
            actual,
            negated,
            matcher,
            args,
            span,
        }
    }
}
