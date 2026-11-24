//! Numbers, strings and templates (SPEC 2 `IntLit`, `FloatLit`, `StringLit`,
//! `TemplateLit`, `RawTemplate`), with EN0003 to EN0007.

use enrang_base::{Symbol, intern};
use enrang_diag::{Code, Diagnostic, Edit, Help};

use super::xid::{is_ident_continue, is_ident_start};
use super::{Hole, Lexer, Open};
use crate::token::TokenKind;

/// The primitive numeric types (SPEC 4.2), which a suffix such as `1u8` names.
const NUMERIC_TYPES: [&str; 13] = [
    "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "isize", "usize", "f32", "f64", "int",
];

/// The escapes of SPEC 2, for EN0003's note.
const ESCAPES: &str = "\\n \\r \\t \\0 \\\\ \\\" \\' \\` \\$ \\xHH and \\u{H}";

/// A literal's value as it is decoded. A run of `\x` escapes is kept as bytes until
/// something else follows, because together they must form UTF-8 (SPEC 2).
#[derive(Default)]
struct Cooked {
    text: String,
    /// Each pending byte, with the offsets of the escape that wrote it.
    bytes: Vec<(u8, usize, usize)>,
}

impl<'a> Lexer<'a> {
    /// `IntLit` or `FloatLit`, at a digit. A suffix (EN0007) is part of the token's
    /// span and not of its text.
    pub(super) fn number(&mut self) -> TokenKind {
        let lo = self.pos;
        if let Some(kind) = self.radix_literal(lo) {
            return kind;
        }
        let value = self.digits(10);
        let int_end = self.pos;
        let mut float = false;
        if self.byte(self.pos) == Some(b'.') && self.byte(self.pos + 1).is_some_and(is_digit) {
            self.pos += 1;
            self.digits(10);
            float = true;
        }
        float |= self.exponent();
        if float {
            let text = intern(&self.text[lo..self.pos]);
            self.suffix(lo);
            return TokenKind::Float(text);
        }
        // `5.` never takes the dot of `5..`, `5...` or `5.foo` (SPEC 2), so only a dot
        // that nothing continues makes the malformed `5.`.
        if self.byte(self.pos) == Some(b'.') && !self.dot_continues(self.pos + 1) {
            self.pos += 1;
            return self.malformed_float(lo, false);
        }
        self.leading_zero(lo, int_end);
        let text = intern(&self.text[lo..int_end]);
        self.suffix(lo);
        TokenKind::Int { value, text }
    }

    /// `HexLit`, `OctLit` or `BinLit`: `0x`, `0o` or `0b` and a digit of that radix.
    /// An upper-case `0X`, `0O` or `0B` lexes the same way, with EN0007: by the
    /// grammar it is `0` with a suffix.
    fn radix_literal(&mut self, lo: usize) -> Option<TokenKind> {
        if self.byte(lo) != Some(b'0') {
            return None;
        }
        let marker = self.byte(lo + 1)?;
        let radix = match marker.to_ascii_lowercase() {
            b'x' => 16,
            b'o' => 8,
            b'b' => 2,
            _ => return None,
        };
        if !char::from(self.byte(lo + 2)?).is_digit(radix) {
            return None;
        }
        self.pos = lo + 2;
        let value = self.digits(radix);
        let text = intern(&self.text[lo..self.pos]);
        if marker.is_ascii_uppercase() {
            let prefix = self.span(lo + 1, lo + 2);
            let lower = char::from(marker.to_ascii_lowercase()).to_string();
            let written = &self.text[lo..lo + 2];
            self.dcx.emit(
                Diagnostic::new(
                    Code::EN0007,
                    format!("numeric literal with the upper-case prefix `{written}`"),
                    prefix,
                    "a prefix is written in lower case",
                )
                .with_help(Help::machine(
                    format!("write `0{lower}`"),
                    vec![Edit::replace(prefix, lower)],
                )),
            );
        }
        self.suffix(lo);
        Some(TokenKind::Int { value, text })
    }

    /// Digits of `radix` and `_` separators. The value saturates at `u128::MAX`,
    /// which no integer type holds, so sema rejects it with the rest.
    fn digits(&mut self, radix: u32) -> u128 {
        let mut value = 0u128;
        while let Some(b) = self.byte(self.pos) {
            if b != b'_' {
                let Some(digit) = char::from(b).to_digit(radix) else {
                    break;
                };
                value = value
                    .saturating_mul(u128::from(radix))
                    .saturating_add(u128::from(digit));
            }
            self.pos += 1;
        }
        value
    }

    /// `Exponent = ("e" | "E") [ "+" | "-" ] Digit { Digit }`, consumed only when
    /// complete; otherwise the `e` is a suffix.
    fn exponent(&mut self) -> bool {
        if !matches!(self.byte(self.pos), Some(b'e' | b'E')) {
            return false;
        }
        let mut at = self.pos + 1;
        if matches!(self.byte(at), Some(b'+' | b'-')) {
            at += 1;
        }
        if !self.byte(at).is_some_and(is_digit) {
            return false;
        }
        self.pos = at;
        while self.byte(self.pos).is_some_and(is_digit) {
            self.pos += 1;
        }
        true
    }

    /// Whether the character at `at`, after an integer's `.`, keeps the dot out of the
    /// number: another `.`, a digit or an identifier (`5..n`, `5.foo`).
    fn dot_continues(&self, at: usize) -> bool {
        self.char_at(at)
            .is_some_and(|c| c == '.' || c.is_ascii_digit() || is_ident_start(c))
    }

    /// `.5`, at a `.` followed by a digit that `...` and `..` did not take: EN0006.
    pub(super) fn dot_float(&mut self) -> TokenKind {
        let lo = self.pos;
        self.pos += 1;
        self.digits(10);
        self.exponent();
        self.malformed_float(lo, true)
    }

    /// EN0006 for the float from `lo` to here, which lacks the digit before its `.`
    /// (`.5`) or after it (`5.`). It reads as `0.5` or `5.0`.
    fn malformed_float(&mut self, lo: usize, digit_before: bool) -> TokenKind {
        let span = self.span(lo, self.pos);
        let written = &self.text[lo..self.pos];
        let (fixed, edit, label) = if digit_before {
            let fixed = format!("0{written}");
            (fixed, Edit::insert(span.lo, "0"), "no digit before the `.`")
        } else {
            let fixed = format!("{written}0");
            (fixed, Edit::insert(span.hi, "0"), "no digit after the `.`")
        };
        self.dcx.emit(
            Diagnostic::new(
                Code::EN0006,
                format!("malformed float literal `{written}`"),
                span,
                label,
            )
            .with_help(Help::suggest(format!("write `{fixed}`"), vec![edit])),
        );
        let text = intern(&fixed);
        self.suffix(lo);
        TokenKind::Float(text)
    }

    /// EN0005 for a `DecLit` from `lo` to `end` whose first digit is `0` and that has
    /// another digit: TS legacy octal. `0_1` counts.
    fn leading_zero(&mut self, lo: usize, end: usize) {
        let written = &self.text[lo..end];
        if !written.starts_with('0') || !written.bytes().skip(1).any(|b| b.is_ascii_digit()) {
            return;
        }
        let rest = written.trim_start_matches(['0', '_']);
        let decimal = if rest.is_empty() { "0" } else { rest };
        let octal = written.bytes().all(|b| matches!(b, b'0'..=b'7' | b'_'));
        let help = if octal {
            format!("write `0o{decimal}` for octal, or `{decimal}` for decimal")
        } else {
            format!("write `{decimal}`")
        };
        self.dcx.emit(
            Diagnostic::new(
                Code::EN0005,
                format!("leading zero in the integer literal `{written}`"),
                self.span(lo, end),
                "a leading zero and another digit",
            )
            .from_typescript(
                "a leading `0` once made a number octal, so Enrang takes no such zero.",
            )
            .with_help(Help::text(help)),
        );
    }

    /// EN0007 for identifier characters right after the literal that started at
    /// `literal_lo`, which become part of its token.
    fn suffix(&mut self, literal_lo: usize) {
        let lo = self.pos;
        self.eat_while(is_ident_continue);
        if self.pos == lo {
            return;
        }
        let suffix = &self.text[lo..self.pos];
        let literal = &self.text[literal_lo..lo];
        let mut diag = Diagnostic::new(
            Code::EN0007,
            format!("numeric literal with the suffix `{suffix}`"),
            self.span(lo, self.pos),
            "a number literal takes no suffix",
        );
        diag = if NUMERIC_TYPES.contains(&suffix) {
            let cast = format!("{literal} as {suffix}");
            diag.with_help(Help::suggest(
                format!("write `{cast}`, or give the binding a type"),
                vec![Edit::replace(self.span(literal_lo, self.pos), cast)],
            ))
        } else {
            diag.with_help(Help::text(
                "remove it: a literal takes its type from `as` or an annotation",
            ))
        };
        self.dcx.emit(diag);
    }

    /// `StringLit`, at its opening quote. A string ends at its line: a line break or
    /// the end of the file first is EN0004, and the literal ends there.
    pub(super) fn string(&mut self) -> TokenKind {
        let lo = self.pos;
        let quote = char::from(self.text.as_bytes()[lo]);
        self.pos += 1;
        let mut cooked = Cooked::default();
        loop {
            let Some(c) = self.peek() else {
                self.unterminated(lo, Open::String { line_end: false });
                break;
            };
            if c == quote {
                self.pos += 1;
                break;
            }
            if c == '\n' || (c == '\r' && self.byte(self.pos + 1) == Some(b'\n')) {
                self.unterminated(lo, Open::String { line_end: true });
                break;
            }
            if c == '\\' {
                self.escape(&mut cooked);
            } else {
                self.pos += c.len_utf8();
                self.cook(&mut cooked, c);
            }
        }
        self.flush(&mut cooked);
        TokenKind::Str(intern(&cooked.text))
    }

    /// A template, at its opening backtick: `NoSubTemplate`, or `TemplateHead` with
    /// its hole now open.
    pub(super) fn template(&mut self) -> TokenKind {
        let backtick = self.pos;
        self.pos += 1;
        let (text, hole) = self.template_piece(backtick);
        if hole {
            self.holes.push(Hole { backtick, depth: 0 });
            TokenKind::TemplateHead(text)
        } else {
            TokenKind::NoSubTemplate(text)
        }
    }

    /// The `}` that closes the innermost hole, and the template text after it:
    /// `TemplateMiddle` up to the next `${`, or `TemplateTail` to the backtick.
    pub(super) fn template_continue(&mut self) -> TokenKind {
        let backtick = self.holes.pop().map_or(self.pos, |hole| hole.backtick);
        self.pos += 1;
        let (text, hole) = self.template_piece(backtick);
        if hole {
            self.holes.push(Hole { backtick, depth: 0 });
            TokenKind::TemplateMiddle(text)
        } else {
            TokenKind::TemplateTail(text)
        }
    }

    /// Template text up to and past a `${` (`true`) or the closing backtick
    /// (`false`). At the end of the file it is EN0004 at `backtick`.
    fn template_piece(&mut self, backtick: usize) -> (Symbol, bool) {
        let mut cooked = Cooked::default();
        let hole = loop {
            let Some(c) = self.peek() else {
                self.unterminated(backtick, Open::Template);
                break false;
            };
            match c {
                '`' => {
                    self.pos += 1;
                    break false;
                }
                '$' if self.byte(self.pos + 1) == Some(b'{') => {
                    self.pos += 2;
                    break true;
                }
                '\\' => self.escape(&mut cooked),
                _ => {
                    self.pos += c.len_utf8();
                    self.cook(&mut cooked, c);
                }
            }
        };
        self.flush(&mut cooked);
        (intern(&cooked.text), hole)
    }

    /// `RawTemplate`, at the backtick right after `raw`: the text exactly as written,
    /// with no escapes and no holes.
    pub(super) fn raw_template(&mut self) -> TokenKind {
        let source = self.text;
        let backtick = self.pos;
        let body = backtick + 1;
        let text = match source[body..].find('`') {
            Some(len) => {
                self.pos = body + len + 1;
                &source[body..body + len]
            }
            None => {
                self.pos = source.len();
                self.unterminated(backtick, Open::Raw);
                &source[body..]
            }
        };
        TokenKind::RawTemplate(intern(text))
    }

    /// `Escape`, at its `\`. An unknown escape is EN0003 and keeps the character after
    /// the `\`. A `\` at the end of the file leaves the literal unterminated.
    fn escape(&mut self, cooked: &mut Cooked) {
        let lo = self.pos;
        self.pos += 1;
        let Some(c) = self.peek() else { return };
        self.pos += c.len_utf8();
        let simple = match c {
            'n' => Some('\n'),
            'r' => Some('\r'),
            't' => Some('\t'),
            '0' => Some('\0'),
            '\\' | '"' | '\'' | '`' | '$' => Some(c),
            _ => None,
        };
        if let Some(value) = simple {
            self.cook(cooked, value);
            return;
        }
        match c {
            'x' => self.hex_escape(cooked, lo),
            'u' => self.unicode_escape(cooked, lo),
            _ => {
                self.cook(cooked, c);
                if c == '\r' && self.byte(self.pos) == Some(b'\n') {
                    self.pos += 1;
                    self.cook(cooked, '\n');
                }
                let shown = if c.is_ascii_graphic() {
                    format!("`\\{c}`")
                } else {
                    format!("`\\` before U+{:04X}", u32::from(c))
                };
                let diag = Diagnostic::new(
                    Code::EN0003,
                    format!("unknown escape sequence {shown}"),
                    self.span(lo, self.pos),
                    "not an escape Enrang knows",
                )
                .note(format!("the escapes are {ESCAPES}"))
                .with_help(Help::text("write `\\\\` for a backslash"));
                self.dcx.emit(diag);
            }
        }
    }

    /// `\x` and two hex digits, after the `x`. The byte joins the current run.
    fn hex_escape(&mut self, cooked: &mut Cooked, lo: usize) {
        let mut byte = 0u8;
        let mut count = 0;
        while count < 2 {
            let Some(digit) = self.byte(self.pos).and_then(|b| char::from(b).to_digit(16)) else {
                break;
            };
            byte = byte * 16 + digit as u8;
            count += 1;
            self.pos += 1;
        }
        if count == 2 {
            cooked.bytes.push((byte, lo, self.pos));
            return;
        }
        self.bad_escape(
            cooked,
            lo,
            "`\\x` needs two hex digits",
            "`\\x` and two hex digits",
        );
    }

    /// `\u{` and one to six hex digits naming a Unicode scalar value, then `}`, after
    /// the `u`. TypeScript's four-digit form is EN0003 too: see `ts_unicode_escape`.
    fn unicode_escape(&mut self, cooked: &mut Cooked, lo: usize) {
        if self.byte(self.pos) != Some(b'{') {
            self.ts_unicode_escape(cooked, lo);
            return;
        }
        self.pos += 1;
        let digits = self.hex_run(self.pos, usize::MAX);
        self.pos += digits.len();
        let closed = self.byte(self.pos) == Some(b'}');
        if closed {
            self.pos += 1;
        }
        let problem = if !closed {
            "unclosed `\\u{` escape"
        } else if digits.is_empty() || digits.len() > 6 {
            "`\\u{...}` takes one to six hex digits"
        } else if let Some(value) = scalar(digits) {
            self.cook(cooked, value);
            return;
        } else {
            "this `\\u{...}` is not a Unicode scalar value"
        };
        self.bad_escape(
            cooked,
            lo,
            problem,
            "`\\u{` and one to six hex digits, then `}`",
        );
    }

    /// TypeScript's `\uXXXX`, after the `u`: EN0003 with a fix-it to the braced form,
    /// recovered as the character. A UTF-16 surrogate pair, `😀`, names one
    /// character: one EN0003 spans both escapes, and its fix-it writes `\u{1F600}`. A
    /// lone surrogate names none, so it has no fix-it and reads as U+FFFD.
    fn ts_unicode_escape(&mut self, cooked: &mut Cooked, lo: usize) {
        let digits = self.hex_run(self.pos, 4);
        if digits.len() < 4 {
            self.bad_escape(
                cooked,
                lo,
                "`\\u` takes its digits in braces",
                "`\\u{` and one to six hex digits, then `}`",
            );
            return;
        }
        self.pos += 4;
        let unit = hex_value(digits);
        let (value, fixed, label) = if let Some(value) = char::from_u32(unit) {
            let fixed = format!("\\u{{{digits}}}");
            (value, fixed, "the four-digit form of TypeScript")
        } else if let Some(value) = self.surrogate_pair(unit) {
            self.pos += 6;
            let fixed = format!("\\u{{{:X}}}", u32::from(value));
            (
                value,
                fixed,
                "a UTF-16 surrogate pair, as TypeScript writes one",
            )
        } else {
            self.dcx.emit(
                Diagnostic::new(
                    Code::EN0003,
                    "`\\u` takes its digits in braces",
                    self.span(lo, self.pos),
                    "a lone surrogate, which is not a Unicode scalar value",
                )
                .note("a string holds Unicode scalar values, and D800 to DFFF are none"),
            );
            self.cook(cooked, char::REPLACEMENT_CHARACTER);
            return;
        };
        let span = self.span(lo, self.pos);
        self.dcx.emit(
            Diagnostic::new(
                Code::EN0003,
                "`\\u` takes its digits in braces",
                span,
                label,
            )
            .with_help(Help::suggest(
                format!("write `{fixed}`"),
                vec![Edit::replace(span, fixed)],
            )),
        );
        self.cook(cooked, value);
    }

    /// The character of the UTF-16 surrogate pair whose high half is `high`, when a
    /// four-digit `\u` escape of its low half follows at the current position.
    fn surrogate_pair(&self, high: u32) -> Option<char> {
        if !(0xD800..=0xDBFF).contains(&high) || !self.text[self.pos..].starts_with("\\u") {
            return None;
        }
        let digits = self.hex_run(self.pos + 2, 4);
        let low = hex_value(digits);
        if digits.len() < 4 || !(0xDC00..=0xDFFF).contains(&low) {
            return None;
        }
        char::from_u32(0x10000 + ((high - 0xD800) << 10) + (low - 0xDC00))
    }

    /// The hex digits at `at`, at most `max` of them.
    fn hex_run(&self, at: usize, max: usize) -> &'a str {
        let text = self.text;
        let rest = &text[at..];
        let len = rest
            .bytes()
            .take(max)
            .take_while(u8::is_ascii_hexdigit)
            .count();
        &rest[..len]
    }

    /// EN0003 for the malformed escape from `lo` to here, which reads as U+FFFD.
    fn bad_escape(&mut self, cooked: &mut Cooked, lo: usize, message: &str, form: &str) {
        let diag = Diagnostic::new(
            Code::EN0003,
            message,
            self.span(lo, self.pos),
            format!("the escape is {form}"),
        );
        self.dcx.emit(diag);
        self.cook(cooked, char::REPLACEMENT_CHARACTER);
    }

    /// Adds a character to the value, after the pending `\x` bytes.
    fn cook(&mut self, cooked: &mut Cooked, c: char) {
        self.flush(cooked);
        cooked.text.push(c);
    }

    /// Decodes the pending run of `\x` bytes. Each maximal sequence that is not UTF-8
    /// is EN0003 at its escapes and reads as U+FFFD.
    fn flush(&mut self, cooked: &mut Cooked) {
        if cooked.bytes.is_empty() {
            return;
        }
        let run = std::mem::take(&mut cooked.bytes);
        let raw: Vec<u8> = run.iter().map(|&(byte, _, _)| byte).collect();
        let mut at = 0;
        for chunk in raw.utf8_chunks() {
            cooked.text.push_str(chunk.valid());
            at += chunk.valid().len();
            let bad = chunk.invalid().len();
            if bad == 0 {
                continue;
            }
            let span = self.span(run[at].1, run[at + bad - 1].2);
            self.dcx.emit(
                Diagnostic::new(
                    Code::EN0003,
                    "these `\\x` escapes are not UTF-8",
                    span,
                    "a `\\x` above 7F must be part of a UTF-8 sequence",
                )
                .with_help(Help::text("write the character itself, or `\\u{...}`")),
            );
            cooked.text.push(char::REPLACEMENT_CHARACTER);
            at += bad;
        }
    }
}

fn is_digit(b: u8) -> bool {
    b.is_ascii_digit()
}

/// The scalar value written in hex `digits`, which are at most six.
fn scalar(digits: &str) -> Option<char> {
    char::from_u32(hex_value(digits))
}

/// The number written in hex `digits`, which are at most six, all hex.
fn hex_value(digits: &str) -> u32 {
    digits
        .chars()
        .filter_map(|digit| digit.to_digit(16))
        .fold(0, |value, digit| value * 16 + digit)
}
