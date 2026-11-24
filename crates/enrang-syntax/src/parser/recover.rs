//! Recovery (ARCHITECTURE 4): a missing `;` is assumed where it belongs and every
//! repeat folds into one EN0101 for the file; an unclosed `{` is closed where SPEC
//! 2's indentation comparison says, as its EN0102 fix-it does, before the parse
//! starts; a bad statement skips to `;` or `}`, a bad item to the next item keyword
//! at brace depth 0, and a bad list element to the next `,` or the list's closer.
//! Every skip keeps brackets balanced, and none crosses a closer it did not see
//! open, so an error inside a body never swallows the rest of the file.
//!
//! - [`close_unclosed`], before the parse: EN0102 (SPEC 2, G02). For each `{` still
//!   open at the end of the file, the first `}` whose line is indented unlike its
//!   `{`'s line gives the place, and a zero-width `}` token goes where the fix-it
//!   inserts one; with no such `}`, it goes at the end of the file. An unclosed `(`
//!   or `[` gets EN0102 too, closed before the first later line indented no deeper
//!   than its own, outside anything opened after it.
//! - [`expect_semi`] and [`flush_missing_semis`]: EN0101. A `;` is missing when
//!   the next token is on a later line, is `}` or is the end of the file; the parse
//!   goes on as if it were there, and after the parse one diagnostic at the first
//!   site counts the others and carries every insertion (SPEC 2, G01).

use std::collections::BTreeSet;

use enrang_base::{BytePos, SourceFile, Span};
use enrang_diag::{Code, DiagCtx, Diagnostic, Edit, Help};

use super::Parser;
use crate::token::{Keyword, Punct, Reserved, Token, TokenKind};

/// How many unclosed `{` are placed by the indentation comparison, each costing a
/// pass over the tokens; any left after that close at the end of the file.
const MISMATCH_ROUNDS: usize = 64;

/// How many tokens the search for the closing place of unclosed `(` and `[` may
/// look at in all, so a file of them stays linear; past it they close at the end.
const PAREN_BUDGET: usize = 200_000;

/// Whether `token` is a closer this pass inserted: the lexer makes no zero-width
/// punctuator.
pub(super) fn is_synthetic(token: Token) -> bool {
    token.span.is_empty()
        && matches!(
            token.kind,
            TokenKind::Punct(Punct::RBrace | Punct::RParen | Punct::RBracket)
        )
}

/// The lines of a file, for the indentation comparison.
struct Lines<'a> {
    file: &'a SourceFile,
}

impl Lines<'_> {
    /// The 0-based line holding `pos`.
    fn line(&self, pos: BytePos) -> usize {
        let offset = pos.0.saturating_sub(self.file.start.0);
        self.file
            .line_starts
            .partition_point(|&start| start <= offset)
            .saturating_sub(1)
    }

    /// Where `line` starts.
    fn start(&self, line: usize) -> BytePos {
        let offset = self.file.line_starts.get(line).copied().unwrap_or(0);
        self.file.start + offset
    }

    /// The spaces and tabs that start `line`.
    fn indent(&self, line: usize) -> &str {
        let offset = self.file.line_starts.get(line).copied().unwrap_or(0) as usize;
        let rest = self.file.text.get(offset..).unwrap_or("");
        let width = rest.len() - rest.trim_start_matches([' ', '\t']).len();
        &rest[..width]
    }

    /// The width of `line`'s indentation, a tab counting as one column (SPEC 13.1).
    fn width(&self, line: usize) -> usize {
        self.indent(line).chars().count()
    }

    /// The spelling of a punctuator token, also of one this pass inserted.
    fn text_of_kind(&self, token: Token) -> &'static str {
        match token.kind {
            TokenKind::Punct(punct) => punct.as_str(),
            _ => "",
        }
    }

    /// The source of `token`.
    fn text(&self, token: Token) -> &str {
        let lo = token.span.lo.0.saturating_sub(self.file.start.0) as usize;
        let hi = token.span.hi.0.saturating_sub(self.file.start.0) as usize;
        self.file.text.get(lo..hi).unwrap_or("")
    }
}

/// EN0102 before the parse: every `(`, `[` and `{` still open at the end of the
/// file is reported, and a zero-width closer is inserted where its fix-it puts one,
/// so the parse sees every bracket closed (SPEC 2, G02).
pub(super) fn close_unclosed(file: &SourceFile, tokens: &mut Vec<Token>, dcx: &mut DiagCtx) {
    let lines = Lines { file };
    // Braces first: a `(` left open inside a block then closes before its `}`.
    close_braces(&lines, tokens, dcx);
    close_parens(&lines, tokens, dcx);
}

/// The index of the `Eof` token, or the length when there is none.
fn eof_index(tokens: &[Token]) -> usize {
    match tokens.last() {
        Some(token) if token.kind == TokenKind::Eof => tokens.len() - 1,
        _ => tokens.len(),
    }
}

/// A zero-width `closer` to insert at `index`, right after the token before it.
fn synthetic(tokens: &[Token], file: &SourceFile, index: usize, closer: Punct) -> Token {
    let at = match index {
        0 => file.start,
        index => tokens[index - 1].span.hi,
    };
    Token {
        kind: TokenKind::Punct(closer),
        span: Span { lo: at, hi: at },
        space_before: false,
    }
}

/// The unclosed `(` and `[`. Each closes before the first later line, outside the
/// brackets opened after it, that is indented no deeper than its own line, or
/// before a closer of something that encloses it, or at the end of the file; when
/// the token there is a `;` ending the statement, the closer goes before it.
fn close_parens(lines: &Lines, tokens: &mut Vec<Token>, dcx: &mut DiagCtx) {
    let mut stack: Vec<usize> = Vec::new();
    for (index, token) in tokens.iter().enumerate() {
        match token.kind {
            TokenKind::Punct(Punct::LParen | Punct::LBracket) => stack.push(index),
            TokenKind::Punct(closer @ (Punct::RParen | Punct::RBracket)) => {
                let opener = if closer == Punct::RParen {
                    Punct::LParen
                } else {
                    Punct::LBracket
                };
                if let Some(at) = stack.iter().rposition(|&open| tokens[open].is(opener)) {
                    stack.truncate(at);
                }
            }
            _ => {}
        }
    }
    if stack.is_empty() {
        return;
    }
    let eof = eof_index(tokens);
    // An unclosed opener inside another gets its closer of its own, so it opens
    // nothing the outer one's search must wait for.
    let unclosed: BTreeSet<usize> = stack.iter().copied().collect();
    let mut budget = PAREN_BUDGET;
    let mut inserts: Vec<(usize, usize, Token)> = Vec::new();
    for &open in &stack {
        let opener = tokens[open];
        let closer = if opener.is(Punct::LParen) {
            Punct::RParen
        } else {
            Punct::RBracket
        };
        let own_line = lines.line(opener.span.lo);
        let own_width = lines.width(own_line);
        let mut depth = 0usize;
        let mut at = eof;
        let mut index = open + 1;
        while index < eof {
            if budget == 0 {
                at = eof;
                break;
            }
            budget -= 1;
            let token = tokens[index];
            let line = lines.line(token.span.lo);
            let starts_line = line != lines.line(tokens[index - 1].span.lo);
            if depth == 0 && starts_line && line > own_line && lines.width(line) <= own_width {
                at = index;
                break;
            }
            match token.kind {
                TokenKind::Punct(Punct::LParen | Punct::LBracket | Punct::LBrace)
                    if !unclosed.contains(&index) =>
                {
                    depth += 1;
                }
                TokenKind::Punct(Punct::RParen | Punct::RBracket | Punct::RBrace) => {
                    if depth == 0 {
                        at = index;
                        break;
                    }
                    depth -= 1;
                }
                _ => {}
            }
            index += 1;
        }
        if at > open + 1 && tokens[at - 1].is(Punct::Semi) {
            at -= 1;
        }
        let token = synthetic(tokens, lines.file, at, closer);
        inserts.push((at, open, token));
    }
    // At one place an inner opener's closer comes first.
    inserts.sort_by_key(|&(at, open, _)| (at, std::cmp::Reverse(open)));
    report_parens(lines, tokens, &inserts, dcx);
    let mut merged = Vec::with_capacity(tokens.len() + inserts.len());
    let mut pending = inserts.into_iter().peekable();
    for (index, token) in tokens.iter().enumerate() {
        while let Some(&(at, _, closer)) = pending.peek() {
            if at != index {
                break;
            }
            merged.push(closer);
            pending.next();
        }
        merged.push(*token);
    }
    merged.extend(pending.map(|(_, _, closer)| closer));
    *tokens = merged;
}

/// EN0102 for the unclosed `(` and `[` of `inserts`, `(index, opener, closer)`
/// sorted by index, inner openers first: one diagnostic per place, at the
/// outermost opener, the others its secondary labels, and one fix-it with every
/// closer in order. A place right after a closer that the `{` pass inserted gets
/// no fix-it: that `}` has to be written first, and its own EN0102 says so.
fn report_parens(
    lines: &Lines,
    tokens: &[Token],
    inserts: &[(usize, usize, Token)],
    dcx: &mut DiagCtx,
) {
    for group in inserts.chunk_by(|a, b| a.0 == b.0) {
        let (at, _, closer) = group[0];
        let closers: String = group
            .iter()
            .map(|&(_, _, token)| lines.text_of_kind(token))
            .collect();
        let (_, outer, _) = group[group.len() - 1];
        let opener = tokens[outer];
        let open = lines.text(opener);
        let close = lines.text_of_kind(group[group.len() - 1].2);
        let mut diag = Diagnostic::new(
            Code::EN0102,
            format!("the file ended with `{open}` still open"),
            opener.span,
            format!("this `{open}` has no matching `{close}`"),
        );
        for &(_, inner, token) in group.iter().rev().skip(1) {
            diag = diag.with_secondary(
                tokens[inner].span,
                format!(
                    "this `{}` has no matching `{}` either",
                    lines.text(tokens[inner]),
                    lines.text_of_kind(token)
                ),
            );
        }
        let message = format!("add the missing `{closers}`");
        let help = if at > 0 && is_synthetic(tokens[at - 1]) {
            Help::text(message)
        } else {
            Help::suggest(message, vec![Edit::insert(closer.span.lo, closers)])
        };
        dcx.emit(diag.with_help(help));
    }
}

/// The `{` still open at the end of the file, outermost first.
fn open_braces(tokens: &[Token]) -> Vec<usize> {
    let mut stack = Vec::new();
    for (index, token) in tokens.iter().enumerate() {
        if token.is(Punct::LBrace) {
            stack.push(index);
        } else if token.is(Punct::RBrace) {
            stack.pop();
        }
    }
    stack
}

/// A `}` that closes a `{` on a line indented differently from its own: the
/// first such `}`, its `{`, and the innermost `{` still open around it whose line
/// is indented as the `}`'s line is.
struct Mismatch {
    open: usize,
    close: usize,
    lines_up_with: Option<usize>,
}

fn first_mismatch(lines: &Lines, tokens: &[Token]) -> Option<Mismatch> {
    let mut stack: Vec<usize> = Vec::new();
    for (index, token) in tokens.iter().enumerate() {
        if token.is(Punct::LBrace) {
            stack.push(index);
            continue;
        }
        if !token.is(Punct::RBrace) {
            continue;
        }
        let Some(open) = stack.pop() else {
            continue;
        };
        if is_synthetic(*token) {
            continue;
        }
        let width = lines.width(lines.line(token.span.lo));
        if width == lines.width(lines.line(tokens[open].span.lo)) {
            continue;
        }
        let lines_up_with = stack
            .iter()
            .rev()
            .copied()
            .find(|&outer| lines.width(lines.line(tokens[outer].span.lo)) == width);
        return Some(Mismatch {
            open,
            close: index,
            lines_up_with,
        });
    }
    None
}

/// The first word on the line of the `{` at `index`, before it: what a message
/// calls the block by, as `if` and `function` in G02. A `{` with no word before it
/// on its line has none.
fn first_word(lines: &Lines, tokens: &[Token], index: usize) -> Option<String> {
    line_word(lines, tokens, index)
        .filter(|&(at, _)| at < index)
        .map(|(_, word)| word)
}

/// The first word on the line holding token `index`, with its index.
fn line_word(lines: &Lines, tokens: &[Token], index: usize) -> Option<(usize, String)> {
    let line = lines.line(tokens[index].span.lo);
    let first = line_head(lines, tokens, index);
    tokens[first..]
        .iter()
        .take_while(|token| lines.line(token.span.lo) == line && token.kind != TokenKind::Eof)
        .position(|token| {
            matches!(
                token.kind,
                TokenKind::Ident(_) | TokenKind::Keyword(_) | TokenKind::Reserved(_)
            )
        })
        .map(|at| (first + at, lines.text(tokens[first + at]).to_owned()))
}

/// What the help of EN0102 calls the block of the `{` at `index`: of the words on
/// its line before it and after any brace there, the last that starts a block,
/// `if` in `} else if (x) {` and `function` in `public function f(): void {`;
/// with none, the first that is no visibility or modifier, as a method's name. The
/// "lines up with" label keeps [`first_word`]: it says where the `}` stands.
fn block_word(lines: &Lines, tokens: &[Token], index: usize) -> Option<String> {
    let line = lines.line(tokens[index].span.lo);
    let mut first = index;
    while first > 0
        && lines.line(tokens[first - 1].span.lo) == line
        && !tokens[first - 1].is(Punct::LBrace)
        && !tokens[first - 1].is(Punct::RBrace)
    {
        first -= 1;
    }
    let words: Vec<Token> = tokens[first..index]
        .iter()
        .copied()
        .filter(|token| {
            matches!(
                token.kind,
                TokenKind::Ident(_) | TokenKind::Keyword(_) | TokenKind::Reserved(_)
            )
        })
        .collect();
    let starts_block = |token: &Token| match token.kind {
        TokenKind::Keyword(k) => matches!(
            k,
            Keyword::If
                | Keyword::Else
                | Keyword::While
                | Keyword::For
                | Keyword::Do
                | Keyword::Function
                | Keyword::Class
                | Keyword::Enum
                | Keyword::Interface
                | Keyword::Match
                | Keyword::Constructor
                | Keyword::Destructor
                | Keyword::Unsafe
        ),
        TokenKind::Reserved(r) => matches!(
            r,
            Reserved::Switch
                | Reserved::Try
                | Reserved::Catch
                | Reserved::Finally
                | Reserved::Namespace
        ),
        _ => lines.text(*token) == "extend",
    };
    let modifier = |token: &Token| match token.kind {
        TokenKind::Keyword(k) => matches!(
            k,
            Keyword::Public
                | Keyword::Private
                | Keyword::Protected
                | Keyword::Static
                | Keyword::Abstract
                | Keyword::Override
                | Keyword::Final
                | Keyword::Readonly
                | Keyword::Declare
                | Keyword::Let
                | Keyword::Const
                | Keyword::Move
        ),
        TokenKind::Reserved(r) => matches!(r, Reserved::Export | Reserved::Async),
        _ => false,
    };
    words
        .iter()
        .rev()
        .find(|token| starts_block(token))
        .or_else(|| words.iter().find(|token| !modifier(token)))
        .map(|token| lines.text(*token).to_owned())
}

/// `` `word` block `` or, with no word, `block`.
fn block_name(word: Option<&str>) -> String {
    match word {
        Some(word) => format!("`{word}` block"),
        None => "block".to_owned(),
    }
}

/// The index of the first token on the line holding token `index`.
fn line_head(lines: &Lines, tokens: &[Token], index: usize) -> usize {
    let line = lines.line(tokens[index].span.lo);
    let mut first = index;
    while first > 0 && lines.line(tokens[first - 1].span.lo) == line {
        first -= 1;
    }
    first
}

/// The unclosed `{`: SPEC 2's indentation comparison, one EN0102 per `{`.
fn close_braces(lines: &Lines, tokens: &mut Vec<Token>, dcx: &mut DiagCtx) {
    for round in 0.. {
        let open = open_braces(tokens);
        if open.is_empty() {
            return;
        }
        let mismatch = if round < MISMATCH_ROUNDS {
            first_mismatch(lines, tokens)
        } else {
            None
        };
        let Some(mismatch) = mismatch else {
            close_at_end(lines, tokens, &open, dcx);
            return;
        };
        let opener = tokens[mismatch.open];
        let closer = tokens[mismatch.close];
        let close_line = lines.line(closer.span.lo);
        let label = match mismatch.lines_up_with {
            Some(outer) => {
                let what = match first_word(lines, tokens, outer) {
                    Some(word) => format!("`{word}`"),
                    None => "the `{`".to_owned(),
                };
                format!(
                    "this `}}` lines up with {what} on line {}, so it probably closes that instead",
                    lines.line(tokens[outer].span.lo) + 1
                )
            }
            None => "this `}` does not line up with its `{`".to_owned(),
        };
        let indent = lines.indent(lines.line(opener.span.lo)).to_owned();
        dcx.emit(
            Diagnostic::new(
                Code::EN0102,
                "the file ended with `{` still open",
                opener.span,
                "this block has no matching `}`",
            )
            .with_secondary(closer.span, label)
            .with_help(Help::machine(
                format!(
                    "close the {} before line {}",
                    block_name(block_word(lines, tokens, mismatch.open).as_deref()),
                    close_line + 1
                ),
                vec![Edit::insert(
                    lines.start(close_line),
                    format!("{indent}}}\n"),
                )],
            )),
        );
        let at = line_head(lines, tokens, mismatch.close);
        let token = synthetic(tokens, lines.file, at, Punct::RBrace);
        tokens.insert(at, token);
    }
}

/// Closes every `{` of `open` at the end of the file, innermost first.
fn close_at_end(lines: &Lines, tokens: &mut Vec<Token>, open: &[usize], dcx: &mut DiagCtx) {
    let file = lines.file;
    let newline = if file.text.is_empty() || file.text.ends_with('\n') {
        ""
    } else {
        "\n"
    };
    let mut closers = Vec::with_capacity(open.len());
    for &index in open.iter().rev() {
        let opener = tokens[index];
        let line = lines.line(opener.span.lo);
        let indent = lines.indent(line);
        // The search for the word stops at the brace before, so many braces on
        // one line cost one pass over it.
        let block = block_name(block_word(lines, tokens, index).as_deref());
        dcx.emit(
            Diagnostic::new(
                Code::EN0102,
                "the file ended with `{` still open",
                opener.span,
                "this block has no matching `}`",
            )
            .with_help(Help::machine(
                format!("close the {block} at the end of the file"),
                vec![Edit::insert(file.end(), format!("{newline}{indent}}}\n"))],
            )),
        );
        closers.push(index);
    }
    let at = eof_index(tokens);
    let token = synthetic(tokens, file, at, Punct::RBrace);
    let inserted = closers.iter().map(|_| token);
    tokens.splice(at..at, inserted);
}

/// The `;` that ends a statement. When the next token is on a later line, is `}`
/// or is the end of the file, the `;` is taken as missing (EN0101) and nothing is
/// skipped; otherwise it is EN0100 and the statement skips to its end. After a
/// closer that EN0102 inserted, or the end of a template that the lexer closed at
/// the end of the file (EN0004), nothing is said: the place has its diagnostic.
pub(super) fn expect_semi(p: &mut Parser) {
    if p.eat(Punct::Semi) {
        return;
    }
    let token = p.peek();
    let ends_line =
        token.is(Punct::RBrace) || token.kind == TokenKind::Eof || p.line_break_before(p.pos);
    if ends_line {
        if p.pos > 0 {
            let last = p.tokens[p.pos - 1];
            let closed_tail =
                last.span.is_empty() && matches!(last.kind, TokenKind::TemplateTail(_));
            if is_synthetic(last) || closed_tail {
                return;
            }
        }
        let at = p.prev_hi();
        p.missing_semis.push(Span { lo: at, hi: at });
    } else {
        p.expected("`;`");
        skip_stmt(p);
    }
}

/// EN0101 after the parse: one diagnostic at the first site, whose note counts the
/// others and whose fix-it inserts every `;` (SPEC 2, G01).
pub(super) fn flush_missing_semis(p: &mut Parser) {
    let mut sites = std::mem::take(&mut p.missing_semis);
    sites.sort();
    sites.dedup();
    let Some(&first) = sites.first() else {
        return;
    };
    let more = sites.len() - 1;
    let mut diag = Diagnostic::new(
        Code::EN0101,
        "missing `;` after this statement",
        first,
        "expected `;` here",
    );
    if more == 1 {
        diag = diag.note("1 more statement in this file is missing `;`");
    } else if more > 1 {
        diag = diag.note(format!(
            "{more} more statements in this file are missing `;`"
        ));
    }
    let message = if more == 0 {
        "add the semicolon"
    } else {
        "add the semicolons"
    };
    let edits = sites
        .iter()
        .map(|site| Edit::insert(site.lo, ";"))
        .collect();
    p.emit(
        diag.from_typescript("Enrang has no automatic semicolon insertion.")
            .with_help(Help::machine(message, edits)),
    );
}

/// Whether `token`, first on its line, may start the next statement or member:
/// a word or a decorator. A line that starts with an operator or a `.` goes on
/// with the statement before it.
fn starts_line_stmt(token: Token) -> bool {
    matches!(
        token.kind,
        TokenKind::Ident(_)
            | TokenKind::Keyword(_)
            | TokenKind::Reserved(_)
            | TokenKind::Punct(Punct::At)
    ) && !token.is_keyword(Keyword::As)
}

/// Skips a bad statement or class member: to just past a `;` at depth 0, or past a
/// `}` that closes a `{` the skip opened and a `;` right after it, or to a `}` at
/// depth 0, which belongs to the enclosing body, or to the end of the file. A stray
/// `)` or `]` is consumed.
/// Where the `;` is missing, as in a file written without any, the statement also
/// ends at depth 0 before a line that starts another (ARCHITECTURE 4: a missing `;`
/// is assumed at the next line start).
pub(super) fn skip_stmt(p: &mut Parser) {
    let mut depth = 0usize;
    let start = p.pos;
    loop {
        let token = p.peek();
        if depth == 0 && p.pos > start && p.line_break_before(p.pos) && starts_line_stmt(token) {
            return;
        }
        match token.kind {
            TokenKind::Eof => return,
            TokenKind::Punct(Punct::Semi) if depth == 0 => {
                p.bump();
                return;
            }
            TokenKind::Punct(Punct::RBrace) if depth == 0 => return,
            TokenKind::Punct(Punct::LParen | Punct::LBracket | Punct::LBrace) => {
                depth += 1;
                p.bump();
            }
            TokenKind::Punct(Punct::RBrace) => {
                depth -= 1;
                p.bump();
                if depth == 0 {
                    // `const v = E[].V { x: 1 };` ends at its `;`, not at the `}`.
                    if !p.line_break_before(p.pos) {
                        p.eat(Punct::Semi);
                    }
                    return;
                }
            }
            TokenKind::Punct(Punct::RParen | Punct::RBracket) => {
                depth = depth.saturating_sub(1);
                p.bump();
            }
            _ => {
                p.bump();
            }
        }
    }
}

/// Skips a statement that ends on its line: to just past a `;` at depth 0, or to
/// the first token at depth 0 on a later line, or to a closer at depth 0 it did not
/// open, or to the end of the file. An `import` of a form Enrang lacks is skipped
/// this way, braces and all.
pub(super) fn skip_line(p: &mut Parser) {
    let mut depth = 0usize;
    let start = p.pos;
    loop {
        let token = p.peek();
        if depth == 0 && p.pos > start && p.line_break_before(p.pos) {
            return;
        }
        match token.kind {
            TokenKind::Eof => return,
            TokenKind::Punct(Punct::Semi) if depth == 0 => {
                p.bump();
                return;
            }
            TokenKind::Punct(Punct::LParen | Punct::LBracket | Punct::LBrace) => {
                depth += 1;
                p.bump();
            }
            TokenKind::Punct(Punct::RParen | Punct::RBracket | Punct::RBrace) => {
                if depth == 0 {
                    return;
                }
                depth -= 1;
                p.bump();
            }
            _ => {
                p.bump();
            }
        }
    }
}

/// Skips a balanced group from the opener at the cursor through its closer, or to
/// the end of the file.
pub(super) fn skip_group(p: &mut Parser) {
    let mut depth = 0usize;
    loop {
        let token = p.bump();
        match token.kind {
            TokenKind::Eof => return,
            TokenKind::Punct(Punct::LParen | Punct::LBracket | Punct::LBrace) => depth += 1,
            TokenKind::Punct(Punct::RParen | Punct::RBracket | Punct::RBrace) => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return;
                }
            }
            _ if depth == 0 => return,
            _ => {}
        }
    }
}

/// Skips a bad item: at least one token, then to the next item keyword or
/// decorator at depth 0, or past a `;` at depth 0, or past a `}` that closes a `{`
/// the skip opened.
pub(super) fn skip_to_item(p: &mut Parser) {
    let mut depth = 0usize;
    let mut first = true;
    loop {
        let token = p.peek();
        if !first && depth == 0 && starts_item_keyword(p) {
            return;
        }
        first = false;
        match token.kind {
            TokenKind::Eof => return,
            TokenKind::Punct(Punct::Semi) if depth == 0 => {
                p.bump();
                return;
            }
            TokenKind::Punct(Punct::LParen | Punct::LBracket | Punct::LBrace) => {
                depth += 1;
                p.bump();
            }
            TokenKind::Punct(Punct::RBrace) if depth == 1 => {
                p.bump();
                return;
            }
            TokenKind::Punct(Punct::RParen | Punct::RBracket | Punct::RBrace) => {
                depth = depth.saturating_sub(1);
                p.bump();
            }
            _ => {
                p.bump();
            }
        }
    }
}

/// A token that starts a declaration at the top level.
fn starts_item_keyword(p: &Parser) -> bool {
    let token = p.peek();
    match token.kind {
        TokenKind::Keyword(k) => matches!(
            k,
            Keyword::Public
                | Keyword::Private
                | Keyword::Protected
                | Keyword::Class
                | Keyword::Enum
                | Keyword::Interface
                | Keyword::Type
                | Keyword::Function
                | Keyword::Declare
                | Keyword::Abstract
                | Keyword::Final
                | Keyword::Import
        ),
        TokenKind::Reserved(Reserved::Export) => true,
        TokenKind::Punct(Punct::At) => true,
        _ => false,
    }
}

/// Skips the rest of a bad list element: to one of `stops` at depth 0, which it
/// leaves for the caller, or to a closer at depth 0 the list did not open, or to the
/// end of the file. A `;` does not stop it: `[...a; 3]` is one mistake. Every
/// opener has its closer by now, as EN0102 inserted the missing ones.
pub(super) fn skip_until(p: &mut Parser, stops: &[Punct]) {
    let mut depth = 0usize;
    loop {
        let token = p.peek();
        match token.kind {
            TokenKind::Eof => return,
            TokenKind::Punct(punct) if depth == 0 && stops.contains(&punct) => return,
            TokenKind::Punct(Punct::LParen | Punct::LBracket | Punct::LBrace) => {
                depth += 1;
                p.bump();
            }
            TokenKind::Punct(Punct::RParen | Punct::RBracket | Punct::RBrace) => {
                if depth == 0 {
                    return;
                }
                depth -= 1;
                p.bump();
            }
            _ => {
                p.bump();
            }
        }
    }
}
