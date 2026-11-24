//! Generated inputs for the lexer, seeded by `ENRANG_SEED` and sized by
//! `ENRANG_SCALE`: random byte strings and random token soups never panic, lex the
//! same way twice, give tokens that tile the text, and pass TESTING 11's independent
//! check, "Token re-print": each token written again from its kind and value alone,
//! with escapes of its own choosing, lexes back to the same kinds and values. Every
//! `ts` block of SPEC lexes with no lexical error.

use std::fmt::Write as _;

use enrang_diag::Code;
use enrang_syntax::{Keyword, Punct, Reserved, Token, TokenKind, decode_source};
use enrang_testkit::{Harness, Rng, Xoshiro256, catch_panic, rng_for, scaled, seed, shrink};

use crate::lexer::Lexed;
use crate::support::doc;

fn pick<'a, T>(rng: &mut Xoshiro256, items: &'a [T]) -> &'a T {
    &items[rng.below(items.len() as u64) as usize]
}

/// Bytes that start or end tokens, comments and literals, drawn half the time.
const INTERESTING: &[u8] = b" \n\r\t\"'`${}()[]/*\\.0123456789xobeE_+-<>&,?!=#@;:aZr";

fn random_bytes(rng: &mut Xoshiro256) -> Vec<u8> {
    let len = if rng.below(10) == 0 {
        rng.below(400)
    } else {
        rng.below(48)
    };
    let mut bytes = Vec::new();
    if rng.below(16) == 0 {
        bytes.extend_from_slice("\u{FEFF}".as_bytes());
    }
    for _ in 0..len {
        let byte = if rng.below(2) == 0 {
            *pick(rng, INTERESTING)
        } else {
            rng.below(256) as u8
        };
        bytes.push(byte);
    }
    bytes
}

/// Pieces of tokens, whole tokens, and the characters that break them.
const FRAGMENTS: &[&str] = &[
    "a",
    "x1",
    "$",
    "_",
    "é",
    "日本",
    "raw",
    "raw`",
    "raw`x`",
    "0",
    "017",
    "0x1F",
    "0X1F",
    "0b2",
    "0o",
    "1.5",
    "5.",
    ".5",
    "1e",
    "1e+5",
    "1u8",
    "1_000",
    "\"a\"",
    "'b'",
    "\"",
    "'",
    "`",
    "\"\\q\"",
    "\"\\x\"",
    "\"\\xC3\"",
    "\"\\u{1F600}\"",
    "\"\\u{\"",
    "'\\u00e9'",
    "\\",
    "`a`",
    "`a${",
    "${",
    "}",
    "{",
    "`${x}`",
    "'a",
    "&'a",
    "<'a, 'b>",
    "&'a b'",
    "//",
    "/*",
    "*/",
    "/* x */",
    "// x\n",
    "#",
    "\u{A0}",
    "\u{FEFF}",
    "\u{FFFD}",
    "\u{301}",
    "🦀",
    "\u{0}",
    "\u{7F}",
    "\u{2028}",
    "\r\n",
    "\r",
];

const SEPARATORS: &[&str] = &["", "", "", " ", " ", "\n", "\t"];

fn soup(rng: &mut Xoshiro256, words: &[&'static str]) -> String {
    let mut text = String::new();
    if rng.below(16) == 0 {
        text.push('\u{FEFF}');
    }
    for _ in 0..rng.below(40) {
        text.push_str(pick(rng, words));
        text.push_str(pick(rng, SEPARATORS));
    }
    text
}

/// Every fragment a soup draws from: `FRAGMENTS`, the punctuators and the words.
fn soup_words() -> Vec<&'static str> {
    let mut words = FRAGMENTS.to_vec();
    words.extend(Punct::ALL.iter().map(|p| p.as_str()));
    words.extend(Keyword::ALL.iter().map(|k| k.as_str()));
    words.extend(Reserved::ALL.iter().map(|r| r.as_str()));
    words
}

/// Lexes `text` twice and checks every invariant of the result.
fn check(text: &str) -> Result<(), String> {
    check_decoded(text, &[])
}

/// Decodes `bytes` as the driver does, reports EN0001 at each invalid sequence, lexes
/// the text twice and checks every invariant of the result.
fn check_bytes(bytes: &[u8]) -> Result<(), String> {
    let decoded = decode_source(bytes);
    check_decoded(&decoded.text, &decoded.invalid)
}

/// `check` for `text` with U+FFFD standing for bad bytes at each offset of `invalid`.
fn check_decoded(text: &str, invalid: &[u32]) -> Result<(), String> {
    let mut first = None;
    if let Some(message) = catch_panic(|| first = Some(Lexed::with_invalid(text, invalid))) {
        return Err(format!("the lexer panicked: {message}"));
    }
    let lexed = first.expect("set when the lexer returns");
    let again = Lexed::with_invalid(text, invalid);
    if again.tokens != lexed.tokens || again.diags != lexed.diags {
        return Err("two runs differ".to_owned());
    }
    tiles(&lexed)?;
    let start = lexed.file.start;
    for diag in &lexed.diags {
        let span = diag.primary.span;
        let inside = span.lo >= start && span.hi <= lexed.file.end();
        if !inside || span.lo > span.hi {
            return Err(format!("{} has a span outside the file", diag.code));
        }
        let _ = lexed.text(span);
        let lexical = (1..=8).any(|n| diag.code.name() == format!("EN000{n}"));
        if !lexical {
            return Err(format!("the lexer reported {}", diag.code));
        }
        let at = span.lo.0 - start.0;
        if diag.code == Code::EN0001 && !invalid.contains(&at) {
            return Err(format!("EN0001 at {at}, where the bytes were UTF-8"));
        }
        if diag.code == Code::EN0008 && invalid.contains(&at) {
            return Err(format!("EN0008 at {at}, which EN0001 already reported"));
        }
    }
    reprinted(&lexed)
}

/// TESTING 11's "Token re-print": every token written again from its kind and value,
/// never from the source, lexes back to the same kinds and values, with no bad
/// escape. Tokens are written one space apart; a string is written in double quotes
/// with an escape for each character that has one of SPEC 2, `\x` for the other
/// ASCII controls and `\u{...}` beyond ASCII, so the escapes the second lex decodes
/// are not those the source spelled.
fn reprinted(lexed: &Lexed) -> Result<(), String> {
    let mut text = String::new();
    for token in &lexed.tokens {
        text.push_str(&reprint(token));
        text.push(' ');
    }
    let again = Lexed::new(&text);
    if kinds(&again) != kinds(lexed) {
        return Err(format!(
            "the re-print {text:?} lexes as {:?}, not {:?}",
            kinds(&again),
            kinds(lexed)
        ));
    }
    if let Some(diag) = again.diags.iter().find(|d| d.code == Code::EN0003) {
        return Err(format!("the re-print {text:?} has {}", diag.message));
    }
    Ok(())
}

/// The kind of each token, its value included.
fn kinds(lexed: &Lexed) -> Vec<TokenKind> {
    lexed.tokens.iter().map(|token| token.kind).collect()
}

/// One token written from its kind and value. A template tail of no width is the one
/// the lexer adds where a hole is still open at the end of the file, so it is written
/// as nothing, and the second lex adds it again.
fn reprint(token: &Token) -> String {
    match token.kind {
        TokenKind::Punct(punct) => punct.as_str().to_owned(),
        TokenKind::Keyword(word) => word.as_str().to_owned(),
        TokenKind::Reserved(word) => word.as_str().to_owned(),
        TokenKind::Ident(name) => name.to_string(),
        TokenKind::Lifetime(name) => format!("'{name}"),
        TokenKind::Int { text, .. } | TokenKind::Float(text) => text.to_string(),
        TokenKind::Str(value) => format!("\"{}\"", escaped(value.as_str(), '"')),
        TokenKind::NoSubTemplate(value) => format!("`{}`", escaped(value.as_str(), '`')),
        TokenKind::TemplateHead(value) => format!("`{}${{", escaped(value.as_str(), '`')),
        TokenKind::TemplateMiddle(value) => format!("}}{}${{", escaped(value.as_str(), '`')),
        TokenKind::TemplateTail(_) if token.span.is_empty() => String::new(),
        TokenKind::TemplateTail(value) => format!("}}{}`", escaped(value.as_str(), '`')),
        TokenKind::RawTemplate(value) => format!("raw`{value}`"),
        TokenKind::Eof => String::new(),
    }
}

/// `value` as the inside of a literal that `quote` closes.
fn escaped(value: &str, quote: char) -> String {
    let mut out = String::new();
    for c in value.chars() {
        match c {
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            '\\' => out.push_str("\\\\"),
            '$' if quote == '`' => out.push_str("\\$"),
            _ if c == quote => {
                out.push('\\');
                out.push(c);
            }
            _ if c.is_ascii_control() => {
                let _ = write!(out, "\\x{:02X}", u32::from(c));
            }
            _ if !c.is_ascii() => {
                let _ = write!(out, "\\u{{{:x}}}", u32::from(c));
            }
            _ => out.push(c),
        }
    }
    out
}

/// The tokens tile the text: spans in order and in bounds, on character boundaries,
/// each with the text its kind says, with only trivia or reported characters between
/// them; and `space_before` says whether anything lies between.
fn tiles(lexed: &Lexed) -> Result<(), String> {
    let text = &*lexed.file.text;
    let base = lexed.file.start.0 as usize;
    let mut prev = if text.starts_with('\u{FEFF}') { 3 } else { 0 };
    let count = lexed.tokens.len();
    for (index, token) in lexed.tokens.iter().enumerate() {
        let lo = (token.span.lo.0 as usize).wrapping_sub(base);
        let hi = (token.span.hi.0 as usize).wrapping_sub(base);
        if lo > hi || hi > text.len() || lo < prev {
            return Err(format!("token {index} at {lo}..{hi} after {prev}"));
        }
        if !text.is_char_boundary(lo) || !text.is_char_boundary(hi) {
            return Err(format!("token {index} at {lo}..{hi} splits a character"));
        }
        if token.space_before != (lo > prev) {
            return Err(format!(
                "token {index} has space_before {}",
                token.space_before
            ));
        }
        gap(lexed, prev, lo)?;
        let last = index + 1 == count;
        if (token.kind == TokenKind::Eof) != last {
            return Err(format!("token {index} of {count} is {:?}", token.kind));
        }
        let at_end = lo == hi && hi == text.len();
        let source = &text[lo..hi];
        if source.is_empty() && !at_end {
            return Err(format!("token {index} is empty before the end"));
        }
        spelled(token.kind, source, at_end)
            .map_err(|why| format!("token {index} {:?} at {source:?}: {why}", token.kind))?;
        prev = hi;
    }
    if prev != text.len() {
        return Err(format!("the tokens end at {prev} of {}", text.len()));
    }
    Ok(())
}

/// The gap from `lo` to `hi` holds white space, comments, and characters each
/// reported where they stand (EN0008, or the driver's EN0001 for a U+FFFD that stands
/// for bad bytes); an unterminated comment has its EN0002.
fn gap(lexed: &Lexed, lo: usize, hi: usize) -> Result<(), String> {
    let text = &*lexed.file.text;
    let reported = |at: usize, len: usize, codes: &[Code]| {
        lexed.diags.iter().any(|diag| {
            let lo = diag.primary.span.lo.0 as usize - lexed.file.start.0 as usize;
            let hi = diag.primary.span.hi.0 as usize - lexed.file.start.0 as usize;
            codes.contains(&diag.code) && (lo, hi) == (at, at + len)
        })
    };
    let mut at = lo;
    while at < hi {
        let rest = &text[at..hi];
        if rest.starts_with([' ', '\t', '\r', '\n']) {
            at += 1;
        } else if rest.starts_with("//") {
            at += rest.find('\n').unwrap_or(rest.len());
        } else if let Some(body) = rest.strip_prefix("/*") {
            match body.find("*/") {
                Some(len) => at += len + 4,
                None if reported(at, 2, &[Code::EN0002]) => at = hi,
                None => return Err(format!("an open comment at {at} has no EN0002")),
            }
        } else {
            let c = rest.chars().next().expect("not empty");
            if !reported(at, c.len_utf8(), &[Code::EN0008, Code::EN0001]) {
                return Err(format!("{c:?} at {at} lies between tokens unreported"));
            }
            at += c.len_utf8();
        }
    }
    Ok(())
}

/// Whether `source`, the text under a token, is spelled as its kind says.
fn spelled(kind: TokenKind, source: &str, at_end: bool) -> Result<(), &'static str> {
    let ok = match kind {
        TokenKind::Punct(punct) => source == punct.as_str(),
        TokenKind::Keyword(word) => source == word.as_str(),
        TokenKind::Reserved(word) => source == word.as_str(),
        TokenKind::Ident(name) => source == name.as_str(),
        TokenKind::Int { value, text } => {
            let digits: String = text.as_str().chars().filter(|&c| c != '_').collect();
            let (radix, body) = match digits.get(..2) {
                Some("0x" | "0X") => (16, &digits[2..]),
                Some("0o" | "0O") => (8, &digits[2..]),
                Some("0b" | "0B") => (2, &digits[2..]),
                _ => (10, &digits[..]),
            };
            let expected = u128::from_str_radix(body, radix).unwrap_or(u128::MAX);
            source.starts_with(text.as_str()) && value == expected
        }
        TokenKind::Float(text) => {
            let plain: String = text.as_str().chars().filter(|&c| c != '_').collect();
            plain.parse::<f64>().is_ok()
                && source.starts_with(|c: char| c == '.' || c.is_ascii_digit())
        }
        TokenKind::Str(_) => source.starts_with(['"', '\'']),
        TokenKind::NoSubTemplate(_) => source.starts_with('`'),
        TokenKind::TemplateHead(_) => source.starts_with('`') && source.ends_with("${"),
        TokenKind::TemplateMiddle(_) => source.starts_with('}') && source.ends_with("${"),
        TokenKind::TemplateTail(_) => at_end || source.starts_with('}'),
        TokenKind::RawTemplate(_) => source.starts_with("raw`"),
        TokenKind::Lifetime(name) => {
            let written = format!("'{name}");
            source == written || (source.starts_with(&written) && source.ends_with('\''))
        }
        TokenKind::Eof => at_end,
    };
    if ok { Ok(()) } else { Err("misspelled") }
}

/// The text of every fenced `ts` block of `doc`.
fn ts_blocks(doc: &str) -> Vec<String> {
    let mut blocks = Vec::new();
    let mut current: Option<String> = None;
    for line in doc.lines() {
        match &mut current {
            None if line.trim_start() == "```ts" => current = Some(String::new()),
            None => {}
            Some(_) if line.trim_start() == "```" => blocks.extend(current.take()),
            Some(block) => {
                block.push_str(line);
                block.push('\n');
            }
        }
    }
    blocks
}

pub fn register(h: &mut Harness) {
    h.case("lexer properties/random bytes tile their text", || {
        let mut rng = rng_for("lexer-bytes");
        for _ in 0..scaled(10_000) {
            let bytes = random_bytes(&mut rng);
            if check_bytes(&bytes).is_err() {
                let small = shrink(bytes, |b| check_bytes(b).is_err());
                let why = check_bytes(&small).expect_err("still fails");
                return Err(format!("ENRANG_SEED={:#x}: {small:?}: {why}", seed()));
            }
        }
        Ok(())
    });
    h.case("lexer properties/token soups tile their text", || {
        let mut rng = rng_for("lexer-soups");
        let words = soup_words();
        for _ in 0..scaled(10_000) {
            let text = soup(&mut rng, &words);
            if check(&text).is_err() {
                let small = shrink(text, |t| check(t).is_err());
                let why = check(&small).expect_err("still fails");
                return Err(format!("ENRANG_SEED={:#x}: {small:?}: {why}", seed()));
            }
        }
        Ok(())
    });
    h.case("lexer properties/SPEC's ts blocks lex clean", || {
        let blocks = ts_blocks(doc("SPEC.md"));
        assert!(blocks.len() > 50, "{} blocks", blocks.len());
        for block in blocks {
            check(&block).map_err(|why| format!("{block}\n{why}"))?;
            let lexed = Lexed::new(&block);
            if let Some(diag) = lexed.diags.first() {
                let at = lexed.text(diag.primary.span);
                return Err(format!(
                    "{block}\n{}: {} at {at:?}",
                    diag.code, diag.message
                ));
            }
        }
        Ok::<(), String>(())
    });
}
