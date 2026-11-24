//! The parser (SPEC 3, ARCHITECTURE 4 "Lexer and parser"): hand-written recursive
//! descent, with Pratt parsing for the operators of SPEC 3.5.
//!
//! - `items`: SPEC 3.1 and 3.6, the file's order of imports, statements and items.
//! - `types`: SPEC 3.2.
//! - `stmts`: SPEC 3.3.
//! - `exprs`: SPEC 3.4 and 3.5, the `<` speculation and `split_token`.
//! - `recover`: the skips after an error, the missing `;` fold (EN0101), and the
//!   pass before the parse that closes every bracket left open (EN0102).
//! - `hints`: the TypeScript habits and deferred features, EN02xx and EN10xx.
//!
//! A mistake with a code of its own gets it: the TypeScript habits and deferred
//! features of `hints`, the folded missing `;` and the unclosed `{` of `recover`, and
//! the structural checks (EN0103 to EN0116, EN0214, EN0226 to EN0229) where the
//! parser builds the node they inspect. Anything else the grammar does not allow is
//! EN0100, `expected X, found Y`. The parser always terminates: every loop either
//! consumes a token or stops, nesting deeper than [`MAX_DEPTH`] or chaining more
//! than [`MAX_LINKS`] operators is an error instead of a deeper stack, and a speculation that fails leaves the token stream, the node
//! ids, the missing `;` sites and the diagnostics as they were.
//!
//! It also terminates in time. A failed speculation's tokens are parsed again the
//! other way, and every speculation nested in them would be tried again, so each
//! level of nesting would double the work: `a ? (x): T => ` written thirty times, or
//! `x<T[` thirty times, would take hours. So each failure is remembered by its kind
//! and first token, and never tried twice; from the same token the same guess sees
//! the same tokens and fails the same way. Only [`MAX_DEPTH`] can tell two tries
//! apart, the second being shallower: within it, and within [`MAX_LINKS`], the memo
//! changes no tree and no diagnostic, and past them the outcome stays
//! deterministic.

mod exprs;
mod hints;
mod items;
mod recover;
mod stmts;
mod types;

use std::collections::BTreeSet;

use enrang_base::{BytePos, FileOrigin, SourceFile, Span, Symbol, intern};
use enrang_diag::{Code, DiagCtx, Diagnostic, Edit, Help};

use crate::ParseMode;
use crate::ast::{
    Block, Expr, ExprKind, File, Ident, NodeIdGen, Stmt, StmtKind, TypeExpr, TypeExprKind,
};
use crate::token::{Contextual, Keyword, Punct, Token, TokenKind};

/// How deep expressions, types, statements and patterns may nest. Deeper input is
/// EN0100: the parser and every walk over its tree recurse, and a stack overflow is
/// no diagnostic. Real code stays far below it.
pub(crate) const MAX_DEPTH: u32 = 256;

/// How many links the chains of binary operators, casts and postfix operations
/// around a node may have between them: `a + b + c` and `x.f().g()` are flat to
/// read, but each link nests the tree one level deeper on its left. The parser
/// takes a chain in a loop, so only the walks over the tree pay for its length,
/// and this bounds their depth with [`MAX_DEPTH`]. A longer chain is EN0100.
pub(crate) const MAX_LINKS: u32 = 1024;

/// Where a source sits in its module, which says where its test items may go.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) enum Placement {
    /// A module's own file: a test item in it is EN1112.
    Module,
    /// A `*.test.en` part, the only place for test items: a lifecycle hook at its
    /// top level is EN1105.
    TestPart,
    /// No file at all, as standard input: nothing says which of the two it is, so it
    /// takes what either takes, and neither rule applies.
    Unknown,
}

impl Placement {
    /// The placement of a file, by its name.
    pub(crate) fn of(file: &SourceFile) -> Placement {
        if file.path.to_string_lossy().ends_with(".test.en") {
            Placement::TestPart
        } else {
            Placement::Module
        }
    }
}

pub(crate) fn parse_file(
    file: &SourceFile,
    ids: &mut NodeIdGen,
    _mode: ParseMode,
    placement: Placement,
    dcx: &mut DiagCtx,
) -> File {
    let mut tokens = crate::lexer::lex(file, dcx);
    recover::close_unclosed(file, &mut tokens, dcx);
    let mut parser = Parser::new(file, tokens, ids, placement, dcx);
    let tree = parser.parse_file();
    recover::flush_missing_semis(&mut parser);
    tree
}

pub(crate) struct Parser<'a> {
    file: &'a SourceFile,
    /// Ends with one `Eof`, which the cursor never moves past.
    tokens: Vec<Token>,
    pos: usize,
    ids: &'a mut NodeIdGen,
    dcx: &'a mut DiagCtx,
    /// Open speculations. While one is open, diagnostics wait in `held`, and reach
    /// `dcx` only if the outermost succeeds.
    speculating: u32,
    held: Vec<Diagnostic>,
    /// EN0100s emitted so far, held ones included. A speculation fails when it adds
    /// one: its tokens were not what it guessed.
    fatal: u32,
    /// Each `split_token` made while speculating: where, and the token it replaced.
    splits: Vec<(usize, Token)>,
    /// The speculations that failed, each by its kind and the start of its first
    /// token, which are never tried again.
    failed: BTreeSet<(Guess, BytePos)>,
    /// The nesting level, see `MAX_DEPTH`.
    depth: u32,
    /// The chain links around the current token, see `MAX_LINKS`.
    links: u32,
    /// Every opener, `(`, `[` or `{`, by where its token starts, in source order,
    /// with its closer (see `matching_close`): where that token starts, and how
    /// many tokens before it start there too, as the zero-width closers of EN0102
    /// may. `split_current` never touches a bracket and keeps every token's start
    /// and that order, so the table stays true as the token list changes.
    brackets: Vec<(BytePos, Option<(BytePos, u32)>)>,
    /// Where the file sits in its module, which says where test items may go
    /// (EN1112, EN1105).
    placement: Placement,
    /// The file belongs to a library module, which may name a function with any
    /// `MemberName` (SPEC 3.1).
    library: bool,
    /// Where a `;` is missing, each a zero-width span at the end of its statement:
    /// one EN0101 reports them all when the parse ends (SPEC 2).
    missing_semis: Vec<Span>,
    /// The loops and function bodies around the current token, innermost last, for
    /// `break` and `continue` (EN0111 to EN0113).
    scopes: Vec<Scope>,
    /// The label of the loop statement about to be parsed.
    next_label: Option<Ident>,
    /// The function whose parameters are being parsed, for EN0205's generic.
    sig: Option<Sig>,
    /// Where the type of the parameter being parsed starts.
    param_ty: Option<BytePos>,
    /// An `undefined` that is the whole value of an unannotated binding: where it
    /// starts and where EN0206's fix-it writes the binding's type.
    undefined_init: Option<(BytePos, BytePos)>,
    /// The right side of a `type` alias is being parsed (EN0216's wording).
    in_alias: bool,
}

/// What `break` and `continue` see around them.
#[derive(Clone, Debug)]
pub(crate) enum Scope {
    /// A loop, with its label.
    Loop(Option<Ident>),
    /// The body of an arrow, whose head is at the span: a jump cannot leave it.
    Arrow(Span),
    /// The body of a function, method or constructor.
    Function,
    /// A labelled block, after its EN1038: `break` with its label leaves it, and
    /// nothing else sees it.
    Block(Ident),
}

/// The function whose parameters are being parsed: the end of its name, and the
/// start of the `>` of its type parameters with what EN0205's fix-it writes before
/// it to add `T`: `T` in `<>`, `, T` after a parameter, ` T` after a trailing `,`.
#[derive(Copy, Clone, Debug)]
pub(crate) struct Sig {
    name_hi: BytePos,
    angle: Option<(BytePos, &'static str)>,
}

/// What a speculation guesses, from its first token.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub(crate) enum Guess {
    /// `<` after a path: type arguments followed by `(`, `.`, `[` `]` `.` or a
    /// same-line `{`.
    PathTypeArgs,
    /// `<` after a member access: type arguments followed by `(`.
    MemberTypeArgs,
    /// `<` after the name of a type after `as`: type arguments, whatever follows.
    CastTypeArgs,
    /// `(` followed after its `)` by `:`: an annotated arrow's head.
    ArrowHead,
    /// The same in a ternary's first branch: the whole arrow, followed by `:`.
    TernaryArrow,
    /// `x: T =>`, a bare parameter with a return type (EN0224).
    BareArrow,
    /// `<T>(x) =>`, a generic arrow (EN1036).
    GenericArrow,
}

/// What a failed speculation restores.
#[derive(Copy, Clone)]
struct Checkpoint {
    pos: usize,
    ids: u32,
    held: usize,
    fatal: u32,
    splits: usize,
    missing_semis: usize,
}

impl<'a> Parser<'a> {
    fn new(
        file: &'a SourceFile,
        mut tokens: Vec<Token>,
        ids: &'a mut NodeIdGen,
        placement: Placement,
        dcx: &'a mut DiagCtx,
    ) -> Parser<'a> {
        if tokens.last().is_none_or(|t| t.kind != TokenKind::Eof) {
            tokens.push(Token::eof(file.end(), false));
        }
        let brackets = bracket_table(&tokens);
        Parser {
            file,
            tokens,
            pos: 0,
            ids,
            dcx,
            speculating: 0,
            held: Vec::new(),
            fatal: 0,
            splits: Vec::new(),
            failed: BTreeSet::new(),
            depth: 0,
            links: 0,
            brackets,
            placement,
            library: file.origin == FileOrigin::Library,
            missing_semis: Vec::new(),
            scopes: Vec::new(),
            next_label: None,
            sig: None,
            param_ty: None,
            undefined_init: None,
            in_alias: false,
        }
    }

    // -----------------------------------------------------------------------------
    // The cursor.

    fn peek(&self) -> Token {
        self.tokens[self.pos]
    }

    /// The token `n` places ahead, or the `Eof` past the end.
    fn nth(&self, n: usize) -> Token {
        let last = self.tokens.len() - 1;
        self.tokens[(self.pos + n).min(last)]
    }

    fn at(&self, p: Punct) -> bool {
        self.peek().is(p)
    }

    fn nth_is(&self, n: usize, p: Punct) -> bool {
        self.nth(n).is(p)
    }

    fn at_kw(&self, k: Keyword) -> bool {
        self.peek().is_keyword(k)
    }

    fn nth_kw(&self, n: usize, k: Keyword) -> bool {
        self.nth(n).is_keyword(k)
    }

    /// Whether the current token is the identifier `w`, a contextual keyword.
    fn at_word(&self, w: Contextual) -> bool {
        is_named(self.peek(), w.as_str())
    }

    fn at_eof(&self) -> bool {
        self.peek().kind == TokenKind::Eof
    }

    fn bump(&mut self) -> Token {
        let token = self.peek();
        if token.kind != TokenKind::Eof {
            self.pos += 1;
        }
        token
    }

    fn eat(&mut self, p: Punct) -> bool {
        let found = self.at(p);
        if found {
            self.bump();
        }
        found
    }

    fn eat_kw(&mut self, k: Keyword) -> bool {
        let found = self.at_kw(k);
        if found {
            self.bump();
        }
        found
    }

    /// Consumes `p`, or reports EN0100 and consumes nothing.
    fn expect(&mut self, p: Punct) -> bool {
        if self.eat(p) {
            return true;
        }
        self.expected(&format!("`{}`", p.as_str()));
        false
    }

    fn expect_kw(&mut self, k: Keyword) -> bool {
        if self.eat_kw(k) {
            return true;
        }
        self.expected(&format!("`{}`", k.as_str()));
        false
    }

    /// The start of the current token.
    fn lo(&self) -> BytePos {
        self.peek().span.lo
    }

    /// The end of the last token consumed, or the start of the file.
    fn prev_hi(&self) -> BytePos {
        match self.pos {
            0 => self.file.start,
            pos => self.tokens[pos - 1].span.hi,
        }
    }

    /// From `lo` to the end of the last token consumed; empty when nothing was.
    fn span_from(&self, lo: BytePos) -> Span {
        Span {
            lo,
            hi: self.prev_hi().max(lo),
        }
    }

    /// A zero-width span at the current token.
    fn here(&self) -> Span {
        let lo = self.lo();
        Span { lo, hi: lo }
    }

    /// Whether a line break lies between token `index` and the one before it. The
    /// start of the file counts as one.
    fn line_break_before(&self, index: usize) -> bool {
        if index == 0 || index >= self.tokens.len() {
            return true;
        }
        let lo = self.tokens[index - 1].span.hi;
        let hi = self.tokens[index].span.lo;
        self.text(Span { lo, hi }).contains('\n')
    }

    /// The source under `span`, or nothing when it lies outside this file.
    fn text(&self, span: Span) -> &'a str {
        let start = self.file.start.0;
        let (Some(lo), Some(hi)) = (span.lo.0.checked_sub(start), span.hi.0.checked_sub(start))
        else {
            return "";
        };
        self.file.text.get(lo as usize..hi as usize).unwrap_or("")
    }

    /// The source from the start of the line holding `pos` up to `pos`.
    fn line_before(&self, pos: BytePos) -> &'a str {
        let start = self.file.start.0;
        let offset = pos.0.saturating_sub(start) as usize;
        let text: &'a str = &self.file.text;
        let Some(before) = text.get(..offset) else {
            return "";
        };
        let line_start = before.rfind('\n').map_or(0, |at| at + 1);
        &before[line_start..]
    }

    /// The white space that starts the line holding `pos`.
    fn indent_of(&self, pos: BytePos) -> &'a str {
        let line = self.line_before(pos);
        let rest = self.text(Span {
            lo: BytePos(pos.0 - line.len() as u32),
            hi: self.file.end(),
        });
        let width = rest.len() - rest.trim_start_matches([' ', '\t']).len();
        &rest[..width]
    }

    /// The span of the operator `op` in the gap from `lo` to `hi`, past white space
    /// and comments, or `None` when it is not there.
    fn op_between(&self, lo: BytePos, hi: BytePos, op: &str) -> Option<Span> {
        let gap = self.text(Span { lo, hi });
        let mut at = 0;
        loop {
            let rest = &gap[at..];
            let trimmed = rest.trim_start();
            at += rest.len() - trimmed.len();
            if let Some(comment) = trimmed.strip_prefix("//") {
                at += 2 + comment.find('\n').unwrap_or(comment.len());
            } else if let Some(comment) = trimmed.strip_prefix("/*") {
                at += 2 + comment.find("*/").map_or(comment.len(), |end| end + 2);
            } else if trimmed.starts_with(op) {
                let lo = lo + at as u32;
                return Some(Span {
                    lo,
                    hi: lo + op.len() as u32,
                });
            } else {
                return None;
            }
        }
    }

    /// The span from the end of the token before the current one to the current
    /// one: the white space before it.
    fn gap_before_current(&self) -> Span {
        Span {
            lo: self.prev_hi(),
            hi: self.lo(),
        }
    }

    /// The span of `span` and the spaces and tabs after it on its line: what
    /// deleting a word removes.
    fn with_trailing_space(&self, span: Span) -> Span {
        let rest = self.text(Span {
            lo: span.hi,
            hi: self.file.end(),
        });
        let spaces = rest.len() - rest.trim_start_matches([' ', '\t']).len();
        Span {
            lo: span.lo,
            hi: span.hi + spaces as u32,
        }
    }

    /// The index of the closer that matches the opener at `open`, counting `(`, `[`
    /// and `{` alike, or `None` when the file ends first. Arrow heads and
    /// `expect(...)` look for their `)` here. The answer comes from
    /// [`Parser::brackets`], so a line of many unclosed `(`, whose closers all wait
    /// at its end, is not scanned once for each.
    fn matching_close(&self, open: usize) -> Option<usize> {
        let opener = self.tokens.get(open)?;
        if !matches!(
            opener.kind,
            TokenKind::Punct(Punct::LParen | Punct::LBracket | Punct::LBrace)
        ) {
            return None;
        }
        let at = self
            .brackets
            .binary_search_by_key(&opener.span.lo, |&(lo, _)| lo)
            .ok()?;
        let (lo, nth) = self.brackets[at].1?;
        Some(self.tokens.partition_point(|token| token.span.lo < lo) + nth as usize)
    }

    /// `split_token` (SPEC 2): replaces the current token by its two halves.
    fn split_current(&mut self) -> bool {
        let token = self.peek();
        let Some((head, tail)) = token.split() else {
            return false;
        };
        if self.speculating > 0 {
            self.splits.push((self.pos, token));
        }
        self.tokens[self.pos] = head;
        self.tokens.insert(self.pos + 1, tail);
        true
    }

    /// Consumes the `>` that closes type parameters or arguments, splitting `>>`,
    /// `>>>`, `>=` and `>>=` after their first `>` (SPEC 2).
    fn eat_closing_angle(&mut self) -> bool {
        if matches!(
            self.peek().kind,
            TokenKind::Punct(Punct::Shr | Punct::Shr3 | Punct::Ge | Punct::ShrEq)
        ) {
            self.split_current();
        }
        self.eat(Punct::Gt)
    }

    // -----------------------------------------------------------------------------
    // Speculation.

    fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            pos: self.pos,
            ids: self.ids.count(),
            held: self.held.len(),
            fatal: self.fatal,
            splits: self.splits.len(),
            missing_semis: self.missing_semis.len(),
        }
    }

    fn rewind(&mut self, cp: Checkpoint) {
        while self.splits.len() > cp.splits {
            let (index, token) = self.splits.pop().expect("a split to undo");
            self.tokens.remove(index + 1);
            self.tokens[index] = token;
        }
        self.pos = cp.pos;
        self.ids.rewind(cp.ids);
        self.held.truncate(cp.held);
        self.fatal = cp.fatal;
        self.missing_semis.truncate(cp.missing_semis);
    }

    /// `speculate` for a guess of kind `kind` from the current token, unless the
    /// same guess failed here before.
    fn speculate_as<T>(
        &mut self,
        kind: Guess,
        guess: impl FnOnce(&mut Self) -> Option<T>,
    ) -> Option<T> {
        let key = (kind, self.lo());
        if self.failed.contains(&key) {
            return None;
        }
        let result = self.speculate(guess);
        if result.is_none() {
            self.failed.insert(key);
        }
        result
    }

    /// Runs `guess` with diagnostics held back. It succeeds when it returns `Some`
    /// and reported no EN0100; then its diagnostics stand. Otherwise everything it
    /// did is undone.
    fn speculate<T>(&mut self, guess: impl FnOnce(&mut Self) -> Option<T>) -> Option<T> {
        let cp = self.checkpoint();
        self.speculating += 1;
        let result = guess(self);
        self.speculating -= 1;
        match result {
            Some(value) if self.fatal == cp.fatal => {
                if self.speculating == 0 {
                    for diag in std::mem::take(&mut self.held) {
                        self.dcx.emit(diag);
                    }
                    self.splits.clear();
                }
                Some(value)
            }
            _ => {
                self.rewind(cp);
                None
            }
        }
    }

    // -----------------------------------------------------------------------------
    // Scopes of `break` and `continue`.

    /// Runs `body` inside `scope`.
    fn within<T>(&mut self, scope: Scope, body: impl FnOnce(&mut Self) -> T) -> T {
        self.scopes.push(scope);
        let result = body(self);
        self.scopes.pop();
        result
    }

    /// The block of a function, method, constructor or destructor: `break` and
    /// `continue` inside it cannot reach a loop outside it.
    fn parse_fn_body(&mut self) -> Block {
        self.within(Scope::Function, |p| p.parse_block())
    }

    // -----------------------------------------------------------------------------
    // Diagnostics.

    fn emit(&mut self, diag: Diagnostic) {
        if diag.code == Code::EN0100 {
            self.fatal += 1;
        }
        if self.speculating > 0 {
            self.held.push(diag);
        } else {
            self.dcx.emit(diag);
        }
    }

    /// EN0100 at the current token: `expected {what}, found {token}`.
    fn expected(&mut self, what: &str) {
        let token = self.peek();
        let found = self.describe(token);
        self.emit(Diagnostic::new(
            Code::EN0100,
            format!("expected {what}, found {found}"),
            token.span,
            format!("expected {what}"),
        ));
    }

    /// EN0100 at `span` with words of its own.
    fn unexpected(&mut self, span: Span, message: impl Into<String>, label: impl Into<String>) {
        self.emit(Diagnostic::new(Code::EN0100, message, span, label));
    }

    /// How a message names a token.
    fn describe(&self, token: Token) -> String {
        match token.kind {
            TokenKind::Eof => "end of file".to_owned(),
            TokenKind::Str(_) => "a string".to_owned(),
            TokenKind::NoSubTemplate(_) | TokenKind::TemplateHead(_) => "a template".to_owned(),
            TokenKind::RawTemplate(_) => "a `raw` template".to_owned(),
            TokenKind::TemplateMiddle(_) | TokenKind::TemplateTail(_) => "`}`".to_owned(),
            TokenKind::Lifetime(name) => format!("the lifetime `'{name}`"),
            TokenKind::Int { text, .. } => format!("`{text}`"),
            TokenKind::Float(text) | TokenKind::Ident(text) => format!("`{text}`"),
            TokenKind::Keyword(k) => format!("`{}`", k.as_str()),
            TokenKind::Reserved(r) => format!("`{}`", r.as_str()),
            TokenKind::Punct(p) => format!("`{}`", p.as_str()),
        }
    }

    /// Enters one nesting level, or reports EN0100 once the limit is reached.
    fn enter(&mut self) -> bool {
        if self.depth >= MAX_DEPTH {
            let span = self.peek().span;
            self.unexpected(
                span,
                "this is nested too deeply",
                format!("more than {MAX_DEPTH} levels deep here"),
            );
            return false;
        }
        self.depth += 1;
        true
    }

    fn leave(&mut self) {
        self.depth -= 1;
    }

    /// Takes one more link of an operator or postfix chain, or reports EN0100 once
    /// the chains around the token have [`MAX_LINKS`]. The chain gives its links
    /// back when it ends.
    fn enter_link(&mut self) -> bool {
        if self.links >= MAX_LINKS {
            let span = self.peek().span;
            self.unexpected(
                span,
                "this expression has too many operators in a row",
                format!("more than {MAX_LINKS} operators in one expression here"),
            );
            return false;
        }
        self.links += 1;
        true
    }

    // -----------------------------------------------------------------------------
    // Nodes.

    fn mk_expr(&mut self, kind: ExprKind, span: Span) -> Expr {
        Expr {
            id: self.ids.next_id(),
            span,
            kind,
        }
    }

    fn mk_ty(&mut self, kind: TypeExprKind, span: Span) -> TypeExpr {
        TypeExpr {
            id: self.ids.next_id(),
            span,
            kind,
        }
    }

    fn mk_stmt(&mut self, kind: StmtKind, span: Span) -> Stmt {
        Stmt {
            id: self.ids.next_id(),
            kind,
            span,
        }
    }

    /// An `Error` expression at the current token, consuming nothing.
    fn error_expr(&mut self) -> Expr {
        let span = self.here();
        self.mk_expr(ExprKind::Error, span)
    }

    fn error_ty(&mut self) -> TypeExpr {
        let span = self.here();
        self.mk_ty(TypeExprKind::Error, span)
    }

    /// `Elem % ","` and its `close`, after the opener: a trailing comma is allowed.
    /// After a bad element the list skips to the next `,` or to `close`.
    fn comma_list<T>(&mut self, close: Punct, elem: impl FnMut(&mut Self) -> Option<T>) -> Vec<T> {
        self.separated_list(close, None, elem)
    }

    /// `comma_list` where `wrong`, written in place of a `,`, is EN0100 with a
    /// fix-it, after which the list goes on.
    fn separated_list<T>(
        &mut self,
        close: Punct,
        wrong: Option<Punct>,
        mut elem: impl FnMut(&mut Self) -> Option<T>,
    ) -> Vec<T> {
        let mut items = Vec::new();
        loop {
            if self.eat(close) {
                break;
            }
            if self.at_eof() {
                self.expected(&format!("`{}`", close.as_str()));
                break;
            }
            if let Some(item) = elem(self) {
                items.push(item);
            }
            if self.eat(Punct::Comma) {
                continue;
            }
            if self.eat(close) {
                break;
            }
            if let Some(wrong) = wrong
                && self.at(wrong)
            {
                self.wrong_separator(wrong, Punct::Comma);
                self.bump();
                continue;
            }
            self.expected(&format!("`,` or `{}`", close.as_str()));
            recover::skip_until(self, &[Punct::Comma, close]);
            if self.eat(Punct::Comma) {
                continue;
            }
            self.eat(close);
            break;
        }
        items
    }

    /// EN0100 at the current token, `found`, which should be `want`, with the
    /// machine fix-it that replaces it.
    fn wrong_separator(&mut self, found: Punct, want: Punct) {
        let span = self.peek().span;
        let (found, want) = (found.as_str(), want.as_str());
        self.emit(
            Diagnostic::new(
                Code::EN0100,
                format!("expected `{want}`, found `{found}`"),
                span,
                format!("expected `{want}`"),
            )
            .with_help(Help::machine(
                format!("replace `{found}` with `{want}`"),
                vec![Edit::replace(span, want)],
            )),
        );
    }

    /// The name a node gets when its own was missing, after an EN0100.
    fn error_ident(&self) -> Ident {
        Ident {
            name: intern(""),
            span: self.here(),
        }
    }

    /// An identifier, or EN0100.
    fn ident(&mut self) -> Option<Ident> {
        let token = self.peek();
        match token.kind {
            TokenKind::Ident(name) => {
                self.bump();
                Some(Ident {
                    name,
                    span: token.span,
                })
            }
            _ => {
                self.expected("an identifier");
                None
            }
        }
    }

    fn ident_or_error(&mut self) -> Ident {
        self.ident().unwrap_or_else(|| self.error_ident())
    }

    /// `MemberName = Ident | Keyword | Reserved`, or EN0100.
    fn member_name(&mut self) -> Option<Ident> {
        let token = self.peek();
        match word(token) {
            Some(name) => {
                self.bump();
                Some(Ident {
                    name,
                    span: token.span,
                })
            }
            None => {
                self.expected("a name");
                None
            }
        }
    }
}

/// [`Parser::brackets`] for `tokens`, in one pass with a stack of the openers.
fn bracket_table(tokens: &[Token]) -> Vec<(BytePos, Option<(BytePos, u32)>)> {
    let mut table: Vec<(BytePos, Option<(BytePos, u32)>)> = Vec::new();
    let mut open: Vec<usize> = Vec::new();
    let mut run = 0;
    for (index, token) in tokens.iter().enumerate() {
        if index > 0 && tokens[index - 1].span.lo != token.span.lo {
            run = index;
        }
        match token.kind {
            TokenKind::Punct(Punct::LParen | Punct::LBracket | Punct::LBrace) => {
                table.push((token.span.lo, None));
                open.push(table.len() - 1);
            }
            TokenKind::Punct(Punct::RParen | Punct::RBracket | Punct::RBrace) => {
                if let Some(at) = open.pop() {
                    table[at].1 = Some((token.span.lo, (index - run) as u32));
                }
            }
            TokenKind::Eof => break,
            _ => {}
        }
    }
    table
}

/// The spelling of a word token: an identifier, a keyword or a reserved word, each
/// of which may name a member.
fn word(token: Token) -> Option<Symbol> {
    match token.kind {
        TokenKind::Ident(name) => Some(name),
        TokenKind::Keyword(k) => Some(intern(k.as_str())),
        TokenKind::Reserved(r) => Some(intern(r.as_str())),
        _ => None,
    }
}

/// Whether `token` is the identifier `name`.
fn is_named(token: Token, name: &str) -> bool {
    matches!(token.kind, TokenKind::Ident(symbol) if symbol.as_str() == name)
}
