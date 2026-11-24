//! The lexer against SPEC 2: token rows, the classification of words, literal
//! values and spellings, `space_before`, lifetimes, the examples SPEC 2 and TESTING 18
//! state, and each lexical code firing at its span beside a near-miss that does not.

use std::collections::BTreeSet;

use enrang_base::{SourceFile, Span};
use enrang_diag::{
    Applicability, Code, DiagCtx, Diagnostic, Entry, EntryKind, Milestone, Owner, Phase,
    apply_fixes,
};
use enrang_syntax::{
    Contextual, Keyword, Punct, Reserved, Token, TokenKind, decode_source, lex, report_invalid_utf8,
};
use enrang_testkit::Harness;

use crate::support::{backticked, doc, section, source};

/// A file and what the lexer made of it.
pub struct Lexed {
    pub file: SourceFile,
    pub tokens: Vec<Token>,
    pub diags: Vec<Diagnostic>,
}

impl Lexed {
    pub fn new(text: &str) -> Lexed {
        Lexed::with_invalid(text, &[])
    }

    /// What the driver gets for a file whose bytes `decode_source` turned into
    /// `text`, with U+FFFD at each offset of `invalid`: EN0001 there, then the tokens.
    pub fn with_invalid(text: &str, invalid: &[u32]) -> Lexed {
        let file = source("lex.en", text);
        let mut dcx = DiagCtx::new();
        report_invalid_utf8(&file, invalid, &mut dcx);
        let tokens = lex(&file, &mut dcx);
        Lexed {
            file,
            tokens,
            diags: dcx.take(),
        }
    }

    /// The source under `span`.
    pub fn text(&self, span: Span) -> &str {
        let lo = (span.lo.0 - self.file.start.0) as usize;
        let hi = (span.hi.0 - self.file.start.0) as usize;
        &self.file.text[lo..hi]
    }

    /// Every token but the final `Eof`, as `show` writes it, space-separated.
    fn shown(&self) -> String {
        let (eof, tokens) = self.tokens.split_last().expect("an end-of-file token");
        assert_eq!(eof.kind, TokenKind::Eof);
        tokens.iter().map(show).collect::<Vec<_>>().join(" ")
    }

    /// Each diagnostic as its code and the source under its primary span.
    fn found(&self) -> Vec<String> {
        self.diags
            .iter()
            .map(|diag| format!("{} {}", diag.code, self.text(diag.primary.span)))
            .collect()
    }

    /// The text with every edit of every help applied.
    fn fixed(&self) -> String {
        let edits: Vec<_> = self
            .diags
            .iter()
            .flat_map(|diag| &diag.helps)
            .flat_map(|help| help.edits.iter().cloned())
            .collect();
        apply_fixes(&self.file.text, self.file.start, &edits).expect("the edits apply")
    }
}

/// A token in a row: punctuators and identifiers as written, keywords `kw:` and
/// reserved words `rw:`, literals with their kind and value.
fn show(token: &Token) -> String {
    match token.kind {
        TokenKind::Int { value, text } => format!("int:{text}={value}"),
        TokenKind::Float(text) => format!("float:{text}"),
        TokenKind::Str(value) => format!("str:{:?}", value.as_str()),
        TokenKind::NoSubTemplate(value) => format!("tpl:{:?}", value.as_str()),
        TokenKind::TemplateHead(value) => format!("head:{:?}", value.as_str()),
        TokenKind::TemplateMiddle(value) => format!("mid:{:?}", value.as_str()),
        TokenKind::TemplateTail(value) => format!("tail:{:?}", value.as_str()),
        TokenKind::RawTemplate(value) => format!("raw:{:?}", value.as_str()),
        TokenKind::Lifetime(name) => format!("'{name}"),
        TokenKind::Ident(name) => name.to_string(),
        TokenKind::Keyword(word) => format!("kw:{}", word.as_str()),
        TokenKind::Reserved(word) => format!("rw:{}", word.as_str()),
        TokenKind::Punct(punct) => punct.as_str().to_owned(),
        TokenKind::Eof => "eof".to_owned(),
    }
}

/// `(name, input, tokens, diagnostics)`: the input lexes to exactly these tokens and
/// these diagnostics, each as its code and the source under its primary span.
type Row = (
    &'static str,
    &'static str,
    &'static str,
    &'static [&'static str],
);

const NUMBERS: &[Row] = &[
    ("zero", "0", "int:0=0", &[]),
    ("decimal", "42", "int:42=42", &[]),
    ("separators", "1_000_000", "int:1_000_000=1000000", &[]),
    ("loose separators", "1__0_", "int:1__0_=10", &[]),
    ("hex keeps its case", "0xFF_ff", "int:0xFF_ff=65535", &[]),
    ("octal", "0o17", "int:0o17=15", &[]),
    ("binary", "0b1010_1010", "int:0b1010_1010=170", &[]),
    (
        "hex above u128 saturates",
        "0x1_0000_0000_0000_0000_0000_0000_0000_0000",
        "int:0x1_0000_0000_0000_0000_0000_0000_0000_0000=340282366920938463463374607431768211455",
        &[],
    ),
    (
        "decimal above u128 saturates",
        "340282366920938463463374607431768211456",
        "int:340282366920938463463374607431768211456=340282366920938463463374607431768211455",
        &[],
    ),
    ("float", "3.14", "float:3.14", &[]),
    ("float separators", "1_000.000_1", "float:1_000.000_1", &[]),
    ("exponent", "1e10", "float:1e10", &[]),
    (
        "signed exponent",
        "1E+5 6.02e-23",
        "float:1E+5 float:6.02e-23",
        &[],
    ),
    ("zero float", "0.5 0e0", "float:0.5 float:0e0", &[]),
    ("a method on an integer", "5.foo", "int:5=5 . foo", &[]),
    ("an integer range", "5..n", "int:5=5 .. n", &[]),
    ("an e after a dot is a name", "5.e3", "int:5=5 . e3", &[]),
    ("a float then a member", "1.5.max", "float:1.5 . max", &[]),
    ("minus is an operator", "-1", "- int:1=1", &[]),
    (
        "hex has no fraction",
        "0x1.5",
        "int:0x1=1 float:0.5",
        &["EN0006 .5"],
    ),
    ("an incomplete exponent", "1e+", "int:1=1 +", &["EN0007 e"]),
    (
        "exponents have no separators",
        "1e1_0",
        "float:1e1",
        &["EN0007 _0"],
    ),
];

const STRINGS: &[Row] = &[
    ("empty", r#""""#, r#"str:"""#, &[]),
    ("single quotes", r"'it\'s'", r#"str:"it's""#, &[]),
    ("the other quote", r#"'"' "'""#, r#"str:"\"" str:"'""#, &[]),
    (
        "every simple escape",
        r#""\n\r\t\0\\\"\'\`\$""#,
        r#"str:"\n\r\t\0\\\"'`$""#,
        &[],
    ),
    ("ascii bytes", r#""\x41\x7e""#, r#"str:"A~""#, &[]),
    ("bytes forming UTF-8", r#""\xC3\xA9""#, r#"str:"é""#, &[]),
    (
        "braced scalars",
        r#""\u{1F600}\u{0}\u{10FFFF}""#,
        r#"str:"😀\0\u{10ffff}""#,
        &[],
    ),
    ("Unicode text", "\"é日本\"", "str:\"é日本\"", &[]),
    ("a bare CR is text", "\"a\rb\"", r#"str:"a\rb""#, &[]),
    (
        "a BOM inside is text",
        "\"\u{FEFF}\"",
        r#"str:"\u{feff}""#,
        &[],
    ),
    (
        "a FFFD inside is text",
        "\"\u{FFFD}\"",
        "str:\"\u{FFFD}\"",
        &[],
    ),
    (
        "comment marks inside",
        r#""// /* */""#,
        r#"str:"// /* */""#,
        &[],
    ),
];

const TEMPLATES: &[Row] = &[
    ("no holes", "`abc`", r#"tpl:"abc""#, &[]),
    ("one hole", "`a${x}b`", r#"head:"a" x tail:"b""#, &[]),
    (
        "two holes",
        "`a${x}b${y}c`",
        r#"head:"a" x mid:"b" y tail:"c""#,
        &[],
    ),
    (
        "braces in a hole",
        "`${ {} }`",
        r#"head:"" { } tail:"""#,
        &[],
    ),
    (
        "an object in a hole",
        "`${ f({ a: { b: 1 } }) }!`",
        r#"head:"" f ( { a : { b : int:1=1 } } ) tail:"!""#,
        &[],
    ),
    (
        "nested templates",
        "`a${`b${c}`}d`",
        r#"head:"a" head:"b" c tail:"" tail:"d""#,
        &[],
    ),
    ("dollars", r"`$x \${y} $`", r#"tpl:"$x ${y} $""#, &[]),
    ("lines", "`one\ntwo`", r#"tpl:"one\ntwo""#, &[]),
    ("escapes", r"`\u{41}\x42\``", r#"tpl:"AB`""#, &[]),
    ("raw", r"raw`a\n${x}`", r#"raw:"a\\n${x}""#, &[]),
    ("raw then space", "raw `x`", r#"raw tpl:"x""#, &[]),
    ("raw alone", "raw", "raw", &[]),
    ("raw as a member", "x.raw`y`", r#"x . raw:"y""#, &[]),
    ("a closing brace outside", "`a` }", r#"tpl:"a" }"#, &[]),
];

const LIFETIMES: &[Row] = &[
    ("after &", "&'a T", "& 'a T", &[]),
    ("after <", "<'a>", "< 'a >", &[]),
    ("a list", "<'a, 'b>", "< 'a , 'b >", &[]),
    ("a string", "'a'", r#"str:"a""#, &[]),
    ("a string after &", "&'a'", r#"& str:"a""#, &[]),
    (
        "a string argument",
        "f(x, 'a b')",
        r#"f ( x , str:"a b" )"#,
        &[],
    ),
    ("a comma after a name", "a, 'b'", r#"a , str:"b""#, &[]),
    (
        "a signature",
        "f<'a>(x: &'a string)",
        "f < 'a > ( x : & 'a string )",
        &[],
    ),
    (
        "a later empty string",
        "const x: Foo<'a> = f('');",
        r#"kw:const x : Foo < 'a > = f ( str:"" ) ;"#,
        &[],
    ),
    ("a keyword name", "&'static T", "& 'static T", &[]),
    ("space after &", "& 'a T", "& 'a T", &[]),
    ("words read as a string", "&'a b';", "& 'a ;", &[]),
    ("a tab among the words", "&'a\tb';", "& 'a ;", &[]),
    (
        "a digit after the closing quote",
        "&'a b'2'",
        r#"& 'a b str:"2""#,
        &[],
    ),
    ("a string after <=", "x <= 'a b'", r#"x <= str:"a b""#, &[]),
    ("a string after ==", "x == 'a b'", r#"x == str:"a b""#, &[]),
    ("a string after &&", "x && 'a b'", r#"x && str:"a b""#, &[]),
    (
        "a comma ends the words",
        "f(&'a, ' ')",
        r#"f ( & 'a , str:" " )"#,
        &[],
    ),
];

const PUNCTUATION: &[Row] = &[
    (">>>=", ">>>=", ">>> =", &[]),
    ("**=", "**=", "** =", &[]),
    ("??=", "??=", "?? =", &[]),
    ("&&= and ||=", "&&= ||=", "&& = || =", &[]),
    ("optional chaining", "a?.b", "a ?. b", &[]),
    ("?. before a digit", "a?.5:1", "a ?. int:5=5 : int:1=1", &[]),
    ("null assertion", "x! = y", "x ! = y", &[]),
    ("not equal", "x!=y", "x != y", &[]),
    ("arrow", "a=>b", "a => b", &[]),
    ("arrow then =", "=>=", "=> =", &[]),
    ("strict forms", "=== !== <<= >>=", "=== !== <<= >>=", &[]),
    ("four dots", "....", "... .", &[]),
    ("five dots", ".....", "... ..", &[]),
    ("a division", "a/b", "a / b", &[]),
    ("a decorator", "@d", "@ d", &[]),
];

const COMMENTS: &[Row] = &[
    ("line", "a // c\nb", "a b", &[]),
    ("line at the end", "a // c", "a", &[]),
    ("block", "a /* c */ b", "a b", &[]),
    ("block over lines", "a /* c\n d */ b", "a b", &[]),
    ("no nesting", "a /* /* */ b */", "a b * /", &[]),
    ("touching", "a/**/b", "a b", &[]),
    (
        "anchors are comments",
        "x; //~ EN0101\n//! note",
        "x ;",
        &[],
    ),
    ("only a comment", "// only", "", &[]),
    ("CRLF", "a\r\nb\r\n", "a b", &[]),
    ("a bare CR is space", "a\rb", "a b", &[]),
];

/// One firing input per code beside near-misses that must lex clean.
const ERRORS: &[Row] = &[
    (
        "a FFFD typed outside a literal",
        "a\u{FFFD}b",
        "a b",
        &["EN0008 \u{FFFD}"],
    ),
    ("unterminated comment", "a /* b", "a", &["EN0002 /*"]),
    ("unknown escape", r#""\q""#, r#"str:"q""#, &[r"EN0003 \q"]),
    ("TS backspace", r#""\b""#, r#"str:"b""#, &[r"EN0003 \b"]),
    (
        "short \\x",
        r#""\x4""#,
        "str:\"\u{FFFD}\"",
        &[r"EN0003 \x4"],
    ),
    (
        "half a UTF-8 sequence",
        r#""\xC3""#,
        "str:\"\u{FFFD}\"",
        &[r"EN0003 \xC3"],
    ),
    (
        "a bad byte after a good sequence",
        r#""\xC3\xA9\xFF!""#,
        "str:\"é\u{FFFD}!\"",
        &[r"EN0003 \xFF"],
    ),
    (
        "a sequence cut by a character",
        r#""\xE2\x82z""#,
        "str:\"\u{FFFD}z\"",
        &[r"EN0003 \xE2\x82"],
    ),
    (
        "TS four-digit form",
        r#""\u00e9""#,
        r#"str:"é""#,
        &[r"EN0003 \u00e9"],
    ),
    (
        "TS four-digit form takes four",
        r#""\u0041B""#,
        r#"str:"AB""#,
        &[r"EN0003 \u0041"],
    ),
    (
        "TS surrogate pair",
        r#""\uD83D\uDE00!""#,
        r#"str:"😀!""#,
        &[r"EN0003 \uD83D\uDE00"],
    ),
    (
        "TS surrogate pair in lower case",
        r#""\ud83d\ude00""#,
        r#"str:"😀""#,
        &[r"EN0003 \ud83d\ude00"],
    ),
    (
        "the first surrogate pair",
        r#""\uD800\uDC00""#,
        "str:\"\u{10000}\"",
        &[r"EN0003 \uD800\uDC00"],
    ),
    (
        "the last surrogate pair",
        r#""\uDBFF\uDFFF""#,
        r#"str:"\u{10ffff}""#,
        &[r"EN0003 \uDBFF\uDFFF"],
    ),
    (
        "a lone high surrogate",
        r#""\uD800x""#,
        "str:\"\u{FFFD}x\"",
        &[r"EN0003 \uD800"],
    ),
    (
        "surrogates in the wrong order",
        r#""\uDE00\uD83D""#,
        "str:\"\u{FFFD}\u{FFFD}\"",
        &[r"EN0003 \uDE00", r"EN0003 \uD83D"],
    ),
    (
        "a high surrogate before a braced low one",
        r#""\uD83D\u{DE00}""#,
        "str:\"\u{FFFD}\u{FFFD}\"",
        &[r"EN0003 \uD83D", r"EN0003 \u{DE00}"],
    ),
    (
        "two high surrogates",
        r#""\uD83D\uD83D""#,
        "str:\"\u{FFFD}\u{FFFD}\"",
        &[r"EN0003 \uD83D", r"EN0003 \uD83D"],
    ),
    (
        "short TS form",
        r#""\u0e""#,
        "str:\"\u{FFFD}0e\"",
        &[r"EN0003 \u"],
    ),
    (
        "empty braces",
        r#""\u{}""#,
        "str:\"\u{FFFD}\"",
        &[r"EN0003 \u{}"],
    ),
    (
        "seven digits",
        r#""\u{1234567}""#,
        "str:\"\u{FFFD}\"",
        &[r"EN0003 \u{1234567}"],
    ),
    (
        "seven digits naming a scalar",
        r#""\u{0000041}""#,
        "str:\"\u{FFFD}\"",
        &[r"EN0003 \u{0000041}"],
    ),
    (
        "a surrogate",
        r#""\u{D800}""#,
        "str:\"\u{FFFD}\"",
        &[r"EN0003 \u{D800}"],
    ),
    (
        "past 10FFFF",
        r#""\u{110000}""#,
        "str:\"\u{FFFD}\"",
        &[r"EN0003 \u{110000}"],
    ),
    (
        "unclosed braces",
        r#""\u{41""#,
        "str:\"\u{FFFD}\"",
        &[r"EN0003 \u{41"],
    ),
    (
        "a backslash before a line break",
        "\"a\\\nb\"",
        r#"str:"a\nb""#,
        &["EN0003 \\\n"],
    ),
    (
        "a backslash before a CRLF",
        "\"a\\\r\nb\"",
        r#"str:"a\r\nb""#,
        &["EN0003 \\\r\n"],
    ),
    (
        "a string at the end",
        "\"abc",
        r#"str:"abc""#,
        &["EN0004 \""],
    ),
    (
        "a string at a line end",
        "\"abc\nx",
        r#"str:"abc" x"#,
        &["EN0004 \""],
    ),
    (
        "a string at a CRLF",
        "'abc\r\nx",
        r#"str:"abc" x"#,
        &["EN0004 '"],
    ),
    (
        "a backslash at the end",
        "\"abc\\",
        r#"str:"abc""#,
        &["EN0004 \""],
    ),
    (
        "a template at the end",
        "`abc",
        r#"tpl:"abc""#,
        &["EN0004 `"],
    ),
    (
        "an open hole at the end",
        "`a${x",
        r#"head:"a" x tail:"""#,
        &["EN0004 `"],
    ),
    (
        "a template in an open hole",
        "`a${`b",
        r#"head:"a" tpl:"b" tail:"""#,
        &["EN0004 `", "EN0004 `"],
    ),
    (
        "a raw template at the end",
        "raw`abc",
        r#"raw:"abc""#,
        &["EN0004 `"],
    ),
    ("legacy octal", "017", "int:017=17", &["EN0005 017"]),
    (
        "zero, separator, digit",
        "0_1",
        "int:0_1=1",
        &["EN0005 0_1"],
    ),
    ("two zeros", "00", "int:00=0", &["EN0005 00"]),
    (
        "a leading zero and a suffix",
        "01u8",
        "int:01=1",
        &["EN0005 01", "EN0007 u8"],
    ),
    ("not octal", "09", "int:09=9", &["EN0005 09"]),
    ("no digit before the dot", ".5", "float:0.5", &["EN0006 .5"]),
    (
        "no digit after the dot",
        "5.;",
        "float:5.0 ;",
        &["EN0006 5."],
    ),
    ("5. at the end", "x = 5.", "x = float:5.0", &["EN0006 5."]),
    (
        "an exponent after .5",
        ".5e3",
        "float:0.5e3",
        &["EN0006 .5e3"],
    ),
    ("a type suffix", "1u8", "int:1=1", &["EN0007 u8"]),
    ("BigInt", "1n", "int:1=1", &["EN0007 n"]),
    ("a hex suffix", "0xFFu8", "int:0xFF=255", &["EN0007 u8"]),
    ("a float suffix", "1.5f32", "float:1.5", &["EN0007 f32"]),
    ("a separator suffix", "1_u8", "int:1_=1", &["EN0007 u8"]),
    ("an upper-case prefix", "0X1F", "int:0X1F=31", &["EN0007 X"]),
    (
        "a digit past the radix",
        "0b102",
        "int:0b10=2",
        &["EN0007 2"],
    ),
    ("a prefix with no digit", "0x", "int:0=0", &["EN0007 x"]),
    (
        "a suffix after .5",
        ".5f",
        "float:0.5",
        &["EN0006 .5", "EN0007 f"],
    ),
    ("a hash", "a # b", "a b", &["EN0008 #"]),
    ("a TS private name", "this.#x", "kw:this . x", &["EN0008 #"]),
    ("a backslash", "a \\ b", "a b", &["EN0008 \\"]),
    ("a no-break space", "a\u{A0}b", "a b", &["EN0008 \u{A0}"]),
    ("a BOM later", "a\u{FEFF}b", "a b", &["EN0008 \u{FEFF}"]),
    ("an emoji", "x = \u{1F980};", "x = ;", &["EN0008 \u{1F980}"]),
    (
        "a combining mark first",
        "\u{301}x",
        "x",
        &["EN0008 \u{301}"],
    ),
    ("a control character", "a\u{0}b", "a b", &["EN0008 \u{0}"]),
    ("a form feed", "a\u{C}b", "a b", &["EN0008 \u{C}"]),
];

/// For each lexical code, inputs that come close and must lex with no diagnostic.
const NEAR_MISSES: &[(Code, &[&str])] = &[
    (
        Code::EN0001,
        &[
            "\"\u{FFFD}\"",
            "// \u{FFFD}",
            "`\u{FFFD}`",
            "/* \u{FFFD} */",
        ],
    ),
    (
        Code::EN0002,
        &["/* closed */ x", "/**/", "/* a /* b */", "a */"],
    ),
    (
        Code::EN0003,
        &[
            r#""\n""#,
            r#""\u{41}""#,
            r#""\x7F""#,
            r"raw`\q`",
            r#""\\q""#,
        ],
    ),
    (
        Code::EN0004,
        &["\"abc\"", "'abc'", "`a\nb`", "raw`a\nb`", "`${`a`}`", "''"],
    ),
    (Code::EN0005, &["0", "0o17", "0.5", "0e5", "01.5", "10"]),
    (
        Code::EN0006,
        &["0.5", "5..n", "5...", "5.foo", "a.b", "0..n"],
    ),
    (
        Code::EN0007,
        &["1 as u8", "0xFF", "1e5", "0b10", "x1", "1.5"],
    ),
    (
        Code::EN0008,
        &[
            "\"#\"",
            "// #",
            "a.b",
            "\u{FEFF}x",
            "é日本",
            "x\u{301}",
            "$_",
        ],
    ),
];

/// `(name, input, space_before of each token, Eof included)`.
const SPACING: &[(&str, &str, &[bool])] = &[
    ("postfix ?", "a?b", &[false, false, false, false]),
    ("ternary ?", "a ?b", &[false, true, false, false]),
    (
        "a ? on the next line",
        "a\n? b",
        &[false, true, true, false],
    ),
    ("a comment counts", "a/**/?", &[false, true, false]),
    ("propagation", "f()?", &[false, false, false, false, false]),
    (
        "a spaced propagation",
        "f() ?",
        &[false, false, false, true, false],
    ),
    ("type arguments", "a<b>(c)", &[false; 8]),
    (
        "a comparison",
        "a < b > (c)",
        &[false, true, true, true, true, false, false, false],
    ),
    ("a leading space", " a", &[true, false]),
    ("a leading BOM", "\u{FEFF}a", &[false, false]),
    ("a BOM then a space", "\u{FEFF} a", &[true, false]),
    ("trailing space", "a ", &[false, true]),
    ("a skipped character", "a#?", &[false, true, false]),
    ("a hole", "`a${ x }b`", &[false, true, true, false]),
];

fn register_rows(h: &mut Harness, group: &str, rows: &'static [Row]) {
    for &(name, input, tokens, diags) in rows {
        h.case(format!("lexer/{group}: {name}"), move || {
            let lexed = Lexed::new(input);
            assert_eq!(lexed.shown(), tokens, "{input:?}");
            assert_eq!(lexed.found(), diags, "{input:?}");
        });
    }
}

pub fn register(h: &mut Harness) {
    register_rows(h, "numbers", NUMBERS);
    register_rows(h, "strings", STRINGS);
    register_rows(h, "templates", TEMPLATES);
    register_rows(h, "lifetimes", LIFETIMES);
    register_rows(h, "punctuation", PUNCTUATION);
    register_rows(h, "comments", COMMENTS);
    register_rows(h, "errors", ERRORS);
    register_near_misses(h);
    register_spacing(h);
    register_words(h);
    register_docs(h);
    register_shapes(h);
}

fn register_near_misses(h: &mut Harness) {
    for &(code, inputs) in NEAR_MISSES {
        h.case(format!("lexer/{code} near-misses lex clean"), move || {
            for input in inputs {
                let lexed = Lexed::new(input);
                assert_eq!(lexed.found(), Vec::<String>::new(), "{input:?}");
            }
        });
    }
    h.case("lexer/each lexical code fires and has near-misses", || {
        let lexical: BTreeSet<Code> = (1..=8)
            .map(|n| Code::from_name(&format!("EN000{n}")).expect("a lexical code"))
            .collect();
        // EN0001 comes from `report_invalid_utf8`, before lexing; every other
        // lexical code comes from `lex`.
        let mut fired: BTreeSet<Code> = ERRORS
            .iter()
            .flat_map(|&(_, input, _, _)| Lexed::new(input).diags)
            .map(|diag| diag.code)
            .collect();
        assert!(!fired.contains(&Code::EN0001), "lex reports no EN0001");
        let decoded = decode_source(b"x\xFF");
        let bad = Lexed::with_invalid(&decoded.text, &decoded.invalid);
        fired.extend(bad.diags.iter().map(|diag| diag.code));
        assert_eq!(fired, lexical);
        let missed: BTreeSet<Code> = NEAR_MISSES.iter().map(|&(code, _)| code).collect();
        assert_eq!(missed, lexical);
        for code in lexical {
            assert_eq!(code.phase(), Phase::Syntax, "{code}");
            assert_eq!(code.owner(), Owner::Syntax, "{code}");
            assert_eq!(code.since(), Milestone::M1, "{code}");
        }
    });
}

fn register_spacing(h: &mut Harness) {
    for &(name, input, spaces) in SPACING {
        h.case(format!("lexer/space before: {name}"), move || {
            let lexed = Lexed::new(input);
            let found: Vec<bool> = lexed.tokens.iter().map(|t| t.space_before).collect();
            assert_eq!(found, spaces, "{input:?}: {}", lexed.shown());
        });
    }
}

fn register_words(h: &mut Harness) {
    h.case("lexer/keywords lex as keywords", || {
        for &word in Keyword::ALL {
            let lexed = Lexed::new(word.as_str());
            assert_eq!(lexed.tokens[0].kind, TokenKind::Keyword(word));
            assert!(lexed.diags.is_empty());
        }
    });
    h.case("lexer/reserved words lex as reserved words", || {
        for &word in Reserved::ALL {
            let lexed = Lexed::new(word.as_str());
            assert_eq!(lexed.tokens[0].kind, TokenKind::Reserved(word));
            assert!(lexed.diags.is_empty());
        }
    });
    h.case("lexer/contextual words lex as identifiers", || {
        for &word in Contextual::ALL {
            let lexed = Lexed::new(word.as_str());
            let TokenKind::Ident(name) = lexed.tokens[0].kind else {
                panic!("{word:?} lexed as {:?}", lexed.tokens[0].kind);
            };
            assert_eq!(name.as_str(), word.as_str());
        }
    });
    h.case("lexer/a word is a whole identifier", || {
        let lexed = Lexed::new("iffy ifs $if if_ ifé typeofx a$b");
        assert_eq!(lexed.shown(), "iffy ifs $if if_ ifé typeofx a$b");
    });
    h.case("lexer/every punctuator lexes alone", || {
        for &punct in Punct::ALL {
            let lexed = Lexed::new(punct.as_str());
            assert_eq!(lexed.tokens.len(), 2, "{punct:?}");
            assert_eq!(lexed.tokens[0].kind, TokenKind::Punct(punct));
        }
    });
    h.case("lexer/identifier characters are XID's", || {
        let lexed = Lexed::new("é 日本 x\u{301} _1 $ Ω ⅳ \u{1D465} a\u{B7}b");
        assert_eq!(lexed.shown(), "é 日本 x\u{301} _1 $ Ω ⅳ \u{1D465} a\u{B7}b");
        assert!(lexed.diags.is_empty());
        // A digit of another script continues a name and starts none.
        let lexed = Lexed::new("x\u{661} \u{661}");
        assert_eq!(lexed.shown(), "x\u{661}");
        assert_eq!(lexed.found(), ["EN0008 \u{661}"]);
    });
}

/// The tokens of the source under each token's span, `Eof` left out.
fn texts(lexed: &Lexed) -> Vec<String> {
    let (_, tokens) = lexed.tokens.split_last().expect("an end-of-file token");
    tokens
        .iter()
        .map(|token| lexed.text(token.span).to_owned())
        .collect()
}

/// The exact tokens of each input of TESTING 18's lexer row.
const DOT_FIXTURES: &[(&str, &[&str], &[&str])] = &[
    ("0..n", &["0", "..", "n"], &[]),
    ("[...a]", &["[", "...", "a", "]"], &[]),
    ("[....5]", &["[", "...", ".5", "]"], &["EN0006 .5"]),
    ("a...b", &["a", "...", "b"], &[]),
    ("5...", &["5", "..."], &[]),
];

fn register_docs(h: &mut Harness) {
    h.case("lexer/TESTING 18's lexer fixtures", || {
        let testing = doc("TESTING.md");
        let row = testing
            .lines()
            .find(|line| line.starts_with("| Lexer:"))
            .expect("TESTING 18 has a lexer row");
        let first_cell = row.split(" | ").next().expect("a cell");
        let inputs = backticked(first_cell);
        let covered: Vec<&str> = DOT_FIXTURES.iter().map(|&(input, _, _)| input).collect();
        assert_eq!(inputs, covered);
        for &(input, tokens, diags) in DOT_FIXTURES {
            let lexed = Lexed::new(input);
            assert_eq!(texts(&lexed), tokens, "{input}");
            assert_eq!(lexed.found(), diags, "{input}");
        }
        let fixture = Lexed::new("[....5]");
        assert!(fixture.tokens[1].is(Punct::DotDotDot));
        assert!(matches!(fixture.tokens[2].kind, TokenKind::Float(_)));
    });
    h.case("lexer/SPEC 2's examples of dots", || {
        let grammar = section(doc("SPEC.md"), "## 2. Lexical grammar");
        let rule = grammar
            .lines()
            .find(|line| line.starts_with("- `...` is tried before `..`"))
            .expect("the rule on dots");
        let after = rule.split_once("So ").expect("examples after `So`").1;
        let examples = after.split_once(". ").map_or(after, |(first, _)| first);
        let examples = examples.split("; ");
        let mut seen = 0;
        for example in examples {
            let quoted = backticked(example);
            let Some((input, listed)) = quoted.split_first() else {
                continue;
            };
            let lexed = Lexed::new(input);
            let found = texts(&lexed);
            assert_eq!(&found[..listed.len()], listed, "{example}");
            let fires = lexed.diags.iter().any(|d| d.code == Code::EN0006);
            assert_eq!(fires, example.contains("EN0006"), "{example}");
            seen += 1;
        }
        assert_eq!(seen, 4);
    });
    h.case("lexer/each EN1013 form of TESTING 18 has its `...`", || {
        let testing = doc("TESTING.md");
        let row = testing
            .lines()
            .find(|line| line.starts_with("| Deferred forms:"))
            .expect("TESTING 18 lists the EN1013 forms");
        let forms = backticked(row.split(" | ").next().expect("a cell"));
        assert_eq!(forms.len(), 12);
        for form in &forms {
            let lexed = Lexed::new(form);
            assert!(lexed.diags.is_empty(), "{form}: {:?}", lexed.found());
            let spreads: Vec<&Token> = lexed
                .tokens
                .iter()
                .filter(|t| t.is(Punct::DotDotDot))
                .collect();
            assert_eq!(spreads.len(), form.matches("...").count(), "{form}");
            for spread in spreads {
                assert_eq!(lexed.text(spread.span), "...");
            }
        }
    });
    h.case("lexer/the spread forms the parser rejects", || {
        let rows: &[(&str, &str)] = &[
            ("[...a; 3]", "[ ... a ; int:3=3 ]"),
            ("[...0..n]", "[ ... int:0=0 .. n ]"),
            ("for (const i of a...b)", "kw:for ( kw:const i of a ... b )"),
            (
                "i64[].withCapacity(8)",
                "i64 [ ] . withCapacity ( int:8=8 )",
            ),
            ("x[...", "x [ ..."),
        ];
        for &(input, tokens) in rows {
            let lexed = Lexed::new(input);
            assert_eq!(lexed.shown(), tokens, "{input}");
            assert!(lexed.diags.is_empty(), "{input}");
        }
    });
}

fn register_shapes(h: &mut Harness) {
    h.case("lexer/fix-its give the Enrang form", || {
        let rows: &[(&str, &str)] = &[
            (".5", "0.5"),
            ("x = 5.;", "x = 5.0;"),
            ("1u8", "1 as u8"),
            ("1.5f64", "1.5 as f64"),
            ("0X1F", "0x1F"),
            ("1int", "1 as int"),
            (r#""\u00e9""#, r#""\u{00e9}""#),
            (r#""\u0041B""#, r#""\u{0041}B""#),
            (r#""\uD83D\uDE00""#, r#""\u{1F600}""#),
            (r#"x = '\ud83e\udd80';"#, r#"x = '\u{1F980}';"#),
            ("a\u{A0}b", "a b"),
            ("a\u{2028}b", "a b"),
            ("a\u{FEFF}b", "ab"),
        ];
        for &(input, fixed) in rows {
            let lexed = Lexed::new(input);
            assert_eq!(lexed.diags.len(), 1, "{input:?}");
            assert_eq!(lexed.fixed(), fixed, "{input:?}");
            assert!(Lexed::new(fixed).diags.is_empty(), "{fixed:?}");
        }
    });
    h.case("lexer/messages, labels and helps follow SPEC 13.1", || {
        let inputs = ERRORS.iter().map(|&(_, input, _, _)| input);
        for input in inputs {
            for diag in Lexed::new(input).diags {
                let mut texts = vec![diag.message.as_str(), diag.primary.text.as_str()];
                texts.extend(diag.helps.iter().map(|help| help.message.as_str()));
                for text in texts {
                    let first = text.chars().next().expect("not empty");
                    assert!(!first.is_ascii_uppercase(), "{text}");
                    assert!(!text.ends_with('.'), "{text}");
                }
            }
        }
    });
    h.case("lexer/each lexical label says what is wrong", || {
        // `(input, the label of its one diagnostic)`.
        let rows: &[(&str, &str)] = &[
            ("a /* b", "this comment has no closing `*/`"),
            (r#""\q""#, "not an escape Enrang knows"),
            (r#""\x4""#, "the escape is `\\x` and two hex digits"),
            (
                r#""\u{}""#,
                "the escape is `\\u{` and one to six hex digits, then `}`",
            ),
            (
                r#""\xC3""#,
                "a `\\x` above 7F must be part of a UTF-8 sequence",
            ),
            (r#""\u00e9""#, "the four-digit form of TypeScript"),
            (
                r#""\uD83D\uDE00""#,
                "a UTF-16 surrogate pair, as TypeScript writes one",
            ),
            (
                r#""\uD800""#,
                "a lone surrogate, which is not a Unicode scalar value",
            ),
            ("\"abc", "this string has no closing `\"`"),
            ("'abc", "this string has no closing `'`"),
            ("`abc", "this template has no closing backtick"),
            ("raw`abc", "this raw template has no closing backtick"),
            ("017", "a leading zero and another digit"),
            (".5", "no digit before the `.`"),
            ("5.;", "no digit after the `.`"),
            ("1u8", "a number literal takes no suffix"),
            ("0X1", "a prefix is written in lower case"),
            ("a\u{A0}b", "white space is a space, a tab or a line break"),
            ("a\u{FEFF}b", "a byte order mark may only start the file"),
            (
                "a \\ b",
                "`\\` starts an escape only inside a string or template",
            ),
            ("#x", "no token starts with `#`"),
            ("a # b", "no token starts with this character"),
            ("\u{FFFD}", "no token starts with this character"),
        ];
        for &(input, label) in rows {
            let lexed = Lexed::new(input);
            assert_eq!(lexed.diags.len(), 1, "{input:?}");
            assert_eq!(lexed.diags[0].primary.text, label, "{input:?}");
        }
    });
    h.case("lexer/EN0005 offers octal only for octal digits", || {
        let help = |input: &str| Lexed::new(input).diags[0].helps[0].message.clone();
        assert_eq!(help("017"), "write `0o17` for octal, or `17` for decimal");
        assert_eq!(help("09"), "write `9`");
        assert_eq!(help("00"), "write `0o0` for octal, or `0` for decimal");
        assert_eq!(help("0_1"), "write `0o1` for octal, or `1` for decimal");
        assert_eq!(help("0_9"), "write `9`");
    });
    h.case("lexer/how far each lexical fix-it can be trusted", || {
        use Applicability::{MachineApplicable, MaybeIncorrect};
        // `(input, its one code, then each help's applicability and edit count)`.
        let rows: &[(&str, Code, &[(Applicability, usize)])] = &[
            ("017", Code::EN0005, &[(MaybeIncorrect, 0)]),
            (".5", Code::EN0006, &[(MaybeIncorrect, 1)]),
            ("5.;", Code::EN0006, &[(MaybeIncorrect, 1)]),
            ("1u8", Code::EN0007, &[(MaybeIncorrect, 1)]),
            ("1n", Code::EN0007, &[(MaybeIncorrect, 0)]),
            ("0X1F", Code::EN0007, &[(MachineApplicable, 1)]),
            (r#""\u00e9""#, Code::EN0003, &[(MaybeIncorrect, 1)]),
            (r#""\uD83D\uDE00""#, Code::EN0003, &[(MaybeIncorrect, 1)]),
            (r#""\uD800""#, Code::EN0003, &[]),
            (r#""\q""#, Code::EN0003, &[(MaybeIncorrect, 0)]),
            ("a\u{A0}b", Code::EN0008, &[(MachineApplicable, 1)]),
            ("a\u{FEFF}b", Code::EN0008, &[(MachineApplicable, 1)]),
            ("a # b", Code::EN0008, &[]),
        ];
        for &(input, code, helps) in rows {
            let lexed = Lexed::new(input);
            assert_eq!(lexed.diags.len(), 1, "{input:?}");
            assert_eq!(lexed.diags[0].code, code, "{input:?}");
            let found: Vec<(Applicability, usize)> = lexed.diags[0]
                .helps
                .iter()
                .map(|help| (help.applicability, help.edits.len()))
                .collect();
            assert_eq!(found, helps, "{input:?}");
        }
    });
    h.case(
        "lexer/`#` before a name says how TypeScript differs",
        || {
            let entries = |input: &str| Lexed::new(input).diags[0].entries.clone();
            let from_typescript = Entry {
                kind: EntryKind::FromTypeScript,
                text: "a private member is declared `private`, not with `#`.".to_owned(),
            };
            assert_eq!(entries("this.#x"), [from_typescript.clone()]);
            assert_eq!(entries("#_y"), [from_typescript]);
            assert_eq!(entries("a # b"), []);
            assert_eq!(entries("#1"), []);
        },
    );
    h.case("lexer/EN0004 at a line end says strings end there", || {
        let lexed = Lexed::new("\"abc\nx");
        assert_eq!(lexed.diags[0].message, "unterminated string");
        assert_eq!(lexed.diags[0].entries.len(), 1);
        let at_end = Lexed::new("\"abc");
        assert!(at_end.diags[0].entries.is_empty());
    });
    h.case(
        "lexer/an open hole closes with an empty tail at the end",
        || {
            let lexed = Lexed::new("`a${x");
            let tail = lexed.tokens[2];
            assert_eq!(tail.kind, TokenKind::TemplateTail(enrang_base::intern("")));
            assert!(tail.span.is_empty());
            assert_eq!(tail.span.lo, lexed.file.end());
        },
    );
    h.case(
        "lexer/a lifetime takes in the string it was meant as",
        || {
            let lexed = Lexed::new("&'a b';");
            let lifetime = lexed.tokens[1];
            assert_eq!(lexed.text(lifetime.span), "'a b'");
            let tab = Lexed::new("&'a\tb';");
            assert_eq!(tab.text(tab.tokens[1].span), "'a\tb'");
            let plain = Lexed::new("&'a T");
            assert_eq!(plain.text(plain.tokens[1].span), "'a");
        },
    );
    h.case("lexer/a suffix is in its literal's span", || {
        let lexed = Lexed::new("x = 1u8;");
        assert_eq!(lexed.text(lexed.tokens[2].span), "1u8");
        let lexed = Lexed::new("0X1Fu8");
        assert_eq!(lexed.text(lexed.tokens[0].span), "0X1Fu8");
        assert_eq!(lexed.found(), ["EN0007 X", "EN0007 u8"]);
    });
    h.case("lexer/a U+FFFD typed in a valid file is EN0008", || {
        let lexed = Lexed::new("let x = \u{FFFD};");
        assert_eq!(lexed.found(), ["EN0008 \u{FFFD}"]);
        assert_eq!(lexed.diags[0].message, "unexpected character U+FFFD");
        assert_eq!(lexed.shown(), "kw:let x = ;");
    });
    h.case("lexer/bad bytes and a typed U+FFFD in one file", || {
        // `\xFF` is not UTF-8; `\xEF\xBF\xBD` is U+FFFD, written in the source.
        let decoded = decode_source(b"\xFF \xEF\xBF\xBD");
        assert_eq!(decoded.invalid, [0]);
        let lexed = Lexed::with_invalid(&decoded.text, &decoded.invalid);
        assert_eq!(lexed.found(), ["EN0001 \u{FFFD}", "EN0008 \u{FFFD}"]);
        let spans: Vec<(u32, u32)> = lexed
            .diags
            .iter()
            .map(|diag| (diag.primary.span.lo.0, diag.primary.span.hi.0))
            .collect();
        let start = lexed.file.start.0;
        assert_eq!(spans, [(start, start + 3), (start + 4, start + 7)]);
    });
    h.case("lexer/EN0001 once for bytes that are not UTF-8", || {
        let decoded = decode_source(b"let caf\xE9 = 1;");
        let file = source("bad.en", &decoded.text);
        let mut dcx = DiagCtx::new();
        report_invalid_utf8(&file, &decoded.invalid, &mut dcx);
        let tokens = lex(&file, &mut dcx);
        let diags = dcx.take();
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, Code::EN0001);
        assert_eq!(diags[0].primary.text, "these bytes are not UTF-8");
        let kinds: Vec<String> = tokens.iter().map(show).collect();
        assert_eq!(kinds, ["kw:let", "caf", "=", "int:1=1", ";", "eof"]);
    });
    h.case("lexer/the end of the file is the last token", || {
        for text in ["", "a", "a ", "// c", "`a${x", "/* open"] {
            let lexed = Lexed::new(text);
            let last = lexed.tokens.last().expect("a token");
            assert_eq!(last.kind, TokenKind::Eof);
            assert_eq!(last.span.lo, lexed.file.end());
            assert!(last.span.is_empty());
        }
    });
}
