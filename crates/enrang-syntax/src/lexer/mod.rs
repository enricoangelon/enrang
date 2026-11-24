//! The lexer (SPEC 2, ARCHITECTURE 4 "Lexer and parser"): maximal munch over the
//! `Punct` table, `...` before `..` before the `.5` check of EN0006, keywords and
//! reserved words by `Keyword::from_name` and `Reserved::from_name`, contextual words
//! as identifiers, template nesting by a stack of open holes, `raw` templates, and
//! the `Lifetime` rule.
//!
//! It reports EN0002 to EN0008 and goes on, so lexing always reaches the end of the
//! file and the parser sees every token. What it does with each mistake:
//!
//! - EN0002, an unterminated block comment: the comment runs to the end of the file.
//! - EN0003, a bad escape: the literal goes on; an unknown escape keeps the character
//!   after the `\`, a malformed `\x` or `\u` gives U+FFFD.
//! - EN0004, an unterminated string or template: a string ends before the line break
//!   (strings never span lines), a template at the end of the file. A template whose
//!   hole is still open at the end of the file gets a zero-width `TemplateTail` there,
//!   so the parser sees every template closed.
//! - EN0005, EN0006 and EN0007: the literal keeps its value, `.5` and `5.` read as
//!   `0.5` and `5.0`, and a suffix is part of the token's span but not of its text.
//! - EN0008, a character that starts no token: it is skipped, and counts as space
//!   before the next token. A U+FFFD that `decode_source` put where the bytes were not
//!   UTF-8 is skipped with no EN0008, since the driver reported EN0001 at its span
//!   before lexing; a U+FFFD typed in a valid file is EN0008.
//!
//! The gaps between token spans hold white space, comments, a leading BOM and the
//! skipped characters, nothing else. So for a file with no lexical error a gap is pure
//! trivia, which is where `enrang fmt` finds the comments.

mod literals;
mod xid;

use enrang_base::{BytePos, SourceFile, Span, intern};
use enrang_diag::{Code, DiagCtx, Diagnostic, Edit, Help};

use crate::token::{Contextual, Keyword, Punct, Reserved, Token, TokenKind};

use xid::{is_ident_continue, is_ident_start};

/// The byte order mark: skipped at the start of a file, EN0008 anywhere else outside a
/// literal or comment (SPEC 2).
const BOM: char = '\u{FEFF}';

pub(crate) fn lex(file: &SourceFile, dcx: &mut DiagCtx) -> Vec<Token> {
    let mut lexer = Lexer {
        text: &file.text,
        start: file.start,
        pos: 0,
        last_end: 0,
        dcx,
        tokens: Vec::with_capacity(file.text.len() / 4 + 1),
        holes: Vec::new(),
    };
    lexer.run();
    lexer.tokens
}

struct Lexer<'a> {
    text: &'a str,
    start: BytePos,
    /// The offset of the next character to read.
    pos: usize,
    /// Where the last token ended, or the leading BOM: `space_before` is whether
    /// anything lies between it and the next token.
    last_end: usize,
    dcx: &'a mut DiagCtx,
    tokens: Vec<Token>,
    /// The templates whose `${` hole is open, innermost last.
    holes: Vec<Hole>,
}

#[derive(Copy, Clone, Debug)]
struct Hole {
    /// The offset of the template's opening backtick, where EN0004 points.
    backtick: usize,
    /// The `{` opened inside the hole and not yet closed. A `}` closes the hole only
    /// when this is zero (SPEC 2: "the tokeniser tracks brace depth inside `${ }`").
    depth: u32,
}

/// What an EN0004 left open.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum Open {
    /// A string that met a line break, or the end of the file.
    String {
        line_end: bool,
    },
    Template,
    Raw,
}

impl<'a> Lexer<'a> {
    fn run(&mut self) {
        if self.text.starts_with(BOM) {
            self.pos = BOM.len_utf8();
            self.last_end = self.pos;
        }
        loop {
            self.skip_trivia();
            let Some(c) = self.peek() else { break };
            let lo = self.pos;
            if let Some(kind) = self.token(c) {
                self.push(kind, lo);
            }
        }
        let end = self.text.len();
        while let Some(hole) = self.holes.pop() {
            self.unterminated(hole.backtick, Open::Template);
            self.push(TokenKind::TemplateTail(intern("")), end);
        }
        self.push(TokenKind::Eof, end);
    }

    /// Adds the token from `lo` to the current position.
    fn push(&mut self, kind: TokenKind, lo: usize) {
        let token = Token {
            kind,
            span: self.span(lo, self.pos),
            space_before: lo > self.last_end,
        };
        self.tokens.push(token);
        self.last_end = self.pos;
    }

    /// Skips `Whitespace`, `LineComment` and `BlockComment`. A line comment stops
    /// before its `\n`; a block comment ends at the first `*/`, since comments do not
    /// nest.
    fn skip_trivia(&mut self) {
        let bytes = self.text.as_bytes();
        while let Some(&b) = bytes.get(self.pos) {
            match (b, bytes.get(self.pos + 1)) {
                (b' ' | b'\t' | b'\r' | b'\n', _) => self.pos += 1,
                (b'/', Some(b'/')) => {
                    self.pos = self.text[self.pos..]
                        .find('\n')
                        .map_or(self.text.len(), |len| self.pos + len);
                }
                (b'/', Some(b'*')) => {
                    let lo = self.pos;
                    match self.text[lo + 2..].find("*/") {
                        Some(len) => self.pos = lo + 2 + len + 2,
                        None => {
                            self.pos = self.text.len();
                            self.unterminated_comment(lo);
                        }
                    }
                }
                _ => return,
            }
        }
    }

    /// The token starting with `c`, or `None` after skipping a character that starts
    /// none.
    fn token(&mut self, c: char) -> Option<TokenKind> {
        let kind = match c {
            '0'..='9' => self.number(),
            '"' => self.string(),
            '\'' if self.at_lifetime() => self.lifetime(),
            '\'' => self.string(),
            '`' => self.template(),
            '}' if self.holes.last().is_some_and(|hole| hole.depth == 0) => {
                self.template_continue()
            }
            _ if is_ident_start(c) => self.word(),
            _ => return self.punct_or_skip(c),
        };
        Some(kind)
    }

    /// The longest punctuator here (SPEC 2: maximal munch), or `.5` for EN0006, which
    /// is tried after `...` and `..`.
    fn punct_or_skip(&mut self, c: char) -> Option<TokenKind> {
        let rest = &self.text[self.pos..];
        let longest = Punct::ALL
            .iter()
            .copied()
            .filter(|p| rest.starts_with(p.as_str()))
            .max_by_key(|p| p.as_str().len());
        let Some(punct) = longest else {
            self.skip_unexpected(c);
            return None;
        };
        if punct == Punct::Dot && rest.as_bytes().get(1).is_some_and(u8::is_ascii_digit) {
            return Some(self.dot_float());
        }
        self.pos += punct.as_str().len();
        if let Some(hole) = self.holes.last_mut() {
            match punct {
                Punct::LBrace => hole.depth += 1,
                Punct::RBrace => hole.depth = hole.depth.saturating_sub(1),
                _ => {}
            }
        }
        Some(TokenKind::Punct(punct))
    }

    /// An identifier, keyword or reserved word, or a `raw` template when `raw` is
    /// followed by a backtick with no space between (SPEC 2 `RawTemplate`).
    fn word(&mut self) -> TokenKind {
        let lo = self.pos;
        self.pos = self.ident_end(lo);
        let word = &self.text[lo..self.pos];
        if word == Contextual::Raw.as_str() && self.byte(self.pos) == Some(b'`') {
            return self.raw_template();
        }
        if let Some(keyword) = Keyword::from_name(word) {
            TokenKind::Keyword(keyword)
        } else if let Some(reserved) = Reserved::from_name(word) {
            TokenKind::Reserved(reserved)
        } else {
            TokenKind::Ident(intern(word))
        }
    }

    /// SPEC 2: `'` followed by identifier characters and then any character other than
    /// `'` is a `Lifetime` when the previous token is `&` or `<`, or is `,` directly
    /// after another `Lifetime`. Everywhere else `'` starts a string.
    fn at_lifetime(&self) -> bool {
        let name = self.pos + 1;
        let name_end = self.ident_end(name);
        if name_end == name || self.byte(name_end) == Some(b'\'') {
            return false;
        }
        match self.tokens.as_slice() {
            [.., last] if last.is(Punct::Amp) || last.is(Punct::Lt) => true,
            [.., before, last] => {
                last.is(Punct::Comma) && matches!(before.kind, TokenKind::Lifetime(_))
            }
            _ => false,
        }
    }

    /// The `Lifetime` at a `'` that `at_lifetime` accepted. When the words after the
    /// name close with a `'` on the same line, as in `&'a b'`, the token takes them in:
    /// what was meant is the string `"a b"`, which the parser's EN1005 says to write
    /// (SPEC 2). Only words and spaces or tabs qualify, and the closing `'` must not
    /// start another lifetime, so `<'a, 'b>` and `&'a T, y: &'b U` stay lifetimes.
    fn lifetime(&mut self) -> TokenKind {
        let name_lo = self.pos + 1;
        let name_hi = self.ident_end(name_lo);
        let name = intern(&self.text[name_lo..name_hi]);
        self.pos = name_hi;
        let rest = &self.text[name_hi..];
        let words = rest
            .find(|c: char| !(is_ident_continue(c) || c == ' ' || c == '\t'))
            .unwrap_or(rest.len());
        let closing = name_hi + words;
        let closes = self.byte(closing) == Some(b'\'')
            && !self.char_at(closing + 1).is_some_and(is_ident_continue);
        if closes {
            self.pos = closing + 1;
        }
        TokenKind::Lifetime(name)
    }

    /// Skips a character that starts no token, with EN0008. A U+FFFD where the driver
    /// already reported EN0001 stands for bytes that were not UTF-8, and is skipped
    /// with nothing more to say; one typed in a valid file is EN0008 like any other.
    fn skip_unexpected(&mut self, c: char) {
        let lo = self.pos;
        self.pos += c.len_utf8();
        let span = self.span(lo, self.pos);
        if c == char::REPLACEMENT_CHARACTER && self.dcx.reported(Code::EN0001, span) {
            return;
        }
        let diag = unexpected_character(c, span, self.peek());
        self.dcx.emit(diag);
    }

    /// EN0002 at the `/*` at `lo`.
    fn unterminated_comment(&mut self, lo: usize) {
        let span = self.span(lo, lo + 2);
        self.dcx.emit(
            Diagnostic::new(
                Code::EN0002,
                "unterminated block comment",
                span,
                "this comment has no closing `*/`",
            )
            .with_help(Help::text("close it with `*/`")),
        );
    }

    /// EN0004 at the opening quote or backtick at `at`.
    fn unterminated(&mut self, at: usize, open: Open) {
        let span = self.span(at, at + 1);
        let (message, label) = match open {
            Open::String { .. } => {
                let quote = &self.text[at..at + 1];
                let label = format!("this string has no closing `{quote}`");
                ("unterminated string", label)
            }
            Open::Template => (
                "unterminated template",
                "this template has no closing backtick".to_owned(),
            ),
            Open::Raw => (
                "unterminated raw template",
                "this raw template has no closing backtick".to_owned(),
            ),
        };
        let mut diag = Diagnostic::new(Code::EN0004, message, span, label);
        if open == (Open::String { line_end: true }) {
            diag = diag.note("a string ends on the line it starts; a template may span lines");
        }
        self.dcx.emit(diag);
    }

    fn span(&self, lo: usize, hi: usize) -> Span {
        Span {
            lo: self.start + offset(lo),
            hi: self.start + offset(hi),
        }
    }

    fn peek(&self) -> Option<char> {
        self.text[self.pos..].chars().next()
    }

    fn byte(&self, at: usize) -> Option<u8> {
        self.text.as_bytes().get(at).copied()
    }

    /// The character at `at`, or `None` at the end or inside a character.
    fn char_at(&self, at: usize) -> Option<char> {
        self.text.get(at..).and_then(|rest| rest.chars().next())
    }

    /// The end of the identifier starting at `at`, or `at` when none starts there.
    fn ident_end(&self, at: usize) -> usize {
        let rest = &self.text[at..];
        let mut chars = rest.char_indices();
        if !chars.next().is_some_and(|(_, c)| is_ident_start(c)) {
            return at;
        }
        chars
            .find(|&(_, c)| !is_ident_continue(c))
            .map_or(self.text.len(), |(len, _)| at + len)
    }

    /// Advances past every character that `class` accepts.
    fn eat_while(&mut self, class: fn(char) -> bool) {
        while let Some(c) = self.peek().filter(|&c| class(c)) {
            self.pos += c.len_utf8();
        }
    }
}

/// A file-relative offset as a `BytePos` distance. `SourceMap::add` refuses text that
/// does not fit, so this never saturates for a file of a map.
fn offset(at: usize) -> u32 {
    u32::try_from(at).unwrap_or(u32::MAX)
}

/// EN0008 for `c`, which starts no token, with `next` the character after it.
fn unexpected_character(c: char, span: Span, next: Option<char>) -> Diagnostic {
    let shown = if c.is_ascii_graphic() {
        format!("`{c}`")
    } else {
        format!("U+{:04X}", u32::from(c))
    };
    let message = format!("unexpected character {shown}");
    if c == BOM {
        Diagnostic::new(
            Code::EN0008,
            message,
            span,
            "a byte order mark may only start the file",
        )
        .with_help(Help::machine("remove it", vec![Edit::delete(span)]))
    } else if c.is_whitespace() {
        Diagnostic::new(
            Code::EN0008,
            message,
            span,
            "white space is a space, a tab or a line break",
        )
        .with_help(Help::machine(
            "replace it with a space",
            vec![Edit::replace(span, " ")],
        ))
    } else if c == '\\' {
        Diagnostic::new(
            Code::EN0008,
            message,
            span,
            "`\\` starts an escape only inside a string or template",
        )
    } else if c == '#' && next.is_some_and(is_ident_start) {
        Diagnostic::new(Code::EN0008, message, span, "no token starts with `#`")
            .from_typescript("a private member is declared `private`, not with `#`.")
    } else {
        Diagnostic::new(
            Code::EN0008,
            message,
            span,
            "no token starts with this character",
        )
    }
}
