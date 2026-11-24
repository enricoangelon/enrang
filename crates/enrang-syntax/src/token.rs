//! Tokens (SPEC 2, ARCHITECTURE 2.3).
//!
//! A token has no trivia: `enrang fmt` takes comments from the source text between
//! token spans. Each token records whether white space or a comment came before it,
//! which decides postfix `?` and `!` against the ternary (SPEC 2) and whether `<`
//! may start type arguments (SPEC 3.4). Whether a line break came before it is read
//! from the source between the two spans, by the parser, when a rule needs it.

use enrang_base::{BytePos, Span, Symbol};
use enrang_diag::Code;

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    /// White space, a comment, or a character the lexer skipped with EN0008 lies
    /// between the previous token and this one. The first token has it when anything
    /// but a leading BOM comes before it.
    pub space_before: bool,
}

impl Token {
    /// `split_token` (SPEC 2): the two tokens this one splits into, the first one
    /// byte long and the second with no space before it. `None` for a token that
    /// never splits.
    pub fn split(self) -> Option<(Token, Token)> {
        let TokenKind::Punct(punct) = self.kind else {
            return None;
        };
        let (first, second) = punct.split()?;
        let middle = self.span.lo + 1;
        let head = Token {
            kind: TokenKind::Punct(first),
            span: Span {
                lo: self.span.lo,
                hi: middle,
            },
            space_before: self.space_before,
        };
        let tail = Token {
            kind: TokenKind::Punct(second),
            span: Span {
                lo: middle,
                hi: self.span.hi,
            },
            space_before: false,
        };
        Some((head, tail))
    }

    /// Whether this is the punctuator `p`.
    pub fn is(self, p: Punct) -> bool {
        self.kind == TokenKind::Punct(p)
    }

    /// Whether this is the keyword `k`.
    pub fn is_keyword(self, k: Keyword) -> bool {
        self.kind == TokenKind::Keyword(k)
    }

    /// The end-of-file token of a file ending at `end`.
    pub fn eof(end: BytePos, space_before: bool) -> Token {
        Token {
            kind: TokenKind::Eof,
            span: Span { lo: end, hi: end },
            space_before,
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum TokenKind {
    /// `IntLit` (SPEC 2 line `IntLit = DecLit | HexLit | OctLit | BinLit`): the value,
    /// and the spelling `enrang fmt` prints back, underscores and hex case included.
    /// A literal above `u128::MAX` keeps `u128::MAX`, which no integer type holds. A
    /// suffix (EN0007) is in the span and not in the spelling.
    Int {
        value: u128,
        text: Symbol,
    },
    /// `FloatLit`: the spelling, parsed once at its final width (ARCHITECTURE 2.3).
    /// After EN0006 it is the repaired spelling, `0.5` for `.5` and `5.0` for `5.`.
    Float(Symbol),
    /// `StringLit`, either quote: the value, escapes decoded. The quotes and escapes
    /// as written are the source text under the span.
    Str(Symbol),
    /// `TemplateLit` with no `${`: the text between the backticks, escapes decoded.
    NoSubTemplate(Symbol),
    /// `` `text${ ``: the text before the first hole, decoded.
    TemplateHead(Symbol),
    /// `}text${` between two holes. The tokeniser tracks brace depth inside `${ }`,
    /// so templates nest.
    TemplateMiddle(Symbol),
    /// `` }text` `` after the last hole.
    TemplateTail(Symbol),
    /// `RawTemplate = "raw" "`" { any - "`" } "`"`, with no space between `raw` and
    /// the backtick: the text exactly as written.
    RawTemplate(Symbol),
    /// `'a` where SPEC 2 lexes a lifetime, after `&` or `<`, or after `,` directly
    /// after another lifetime. The parser reports it as EN1005. Holds the name
    /// without the quote. When words and spaces after the name close with a `'` on
    /// the same line, as in `&'a b'`, the span takes them in, so the source under it
    /// ends with `'` and is the string EN1005's note says to write as `"a b"`.
    Lifetime(Symbol),
    /// `Ident`, which includes every contextual keyword (`Contextual`).
    Ident(Symbol),
    Keyword(Keyword),
    /// A reserved word, lexed as a keyword so the parser can give its hint.
    Reserved(Reserved),
    Punct(Punct),
    Eof,
}

macro_rules! words {
    ($(#[$meta:meta])* $name:ident { $($variant:ident = $text:literal,)+ }) => {
        $(#[$meta])*
        #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
        pub enum $name {
            $($variant,)+
        }

        impl $name {
            /// Every word, in SPEC 2's order.
            pub const ALL: &'static [$name] = &[$($name::$variant,)+];

            /// The word as it is written.
            pub fn as_str(self) -> &'static str {
                match self {
                    $($name::$variant => $text,)+
                }
            }

            /// The word written `text`, exactly.
            pub fn from_name(text: &str) -> Option<$name> {
                match text {
                    $($text => Some($name::$variant),)+
                    _ => None,
                }
            }
        }
    };
}

words! {
    /// SPEC 2 `Keyword`. `default` outside a `match` arm, as in `export default`, is
    /// EN1009. `MemberName = Ident | Keyword | Reserved` (SPEC 3.1), so every keyword
    /// can name a member.
    Keyword {
        Abstract = "abstract",
        As = "as",
        Asm = "asm",
        Break = "break",
        Class = "class",
        Const = "const",
        Constructor = "constructor",
        Destructor = "destructor",
        Continue = "continue",
        Declare = "declare",
        Default = "default",
        Do = "do",
        Else = "else",
        Enum = "enum",
        False = "false",
        Final = "final",
        Fn = "fn",
        For = "for",
        Function = "function",
        If = "if",
        Implements = "implements",
        Import = "import",
        Interface = "interface",
        Let = "let",
        Match = "match",
        Move = "move",
        Never = "never",
        New = "new",
        Null = "null",
        Override = "override",
        Private = "private",
        Protected = "protected",
        Public = "public",
        Readonly = "readonly",
        Return = "return",
        Static = "static",
        Super = "super",
        This = "this",
        True = "true",
        Type = "type",
        Unsafe = "unsafe",
        Void = "void",
        While = "while",
    }
}

words! {
    /// SPEC 2 `Contextual`: identifiers everywhere except the grammar positions that
    /// name them, so the lexer yields `TokenKind::Ident` and the parser compares.
    Contextual {
        Describe = "describe",
        Test = "test",
        Expect = "expect",
        CompileFails = "compileFails",
        CompileOk = "compileOk",
        Raw = "raw",
        Extends = "extends",
        From = "from",
        Of = "of",
        Not = "not",
        In = "in",
        Out = "out",
        Clobbers = "clobbers",
        Assert = "assert",
        Extend = "extend",
        Where = "where",
    }
}

words! {
    /// SPEC 2 `Reserved`: lexed as keywords, each with a section 13 or 16 hint.
    Reserved {
        Any = "any",
        Await = "await",
        Async = "async",
        Case = "case",
        Catch = "catch",
        Delete = "delete",
        Export = "export",
        Finally = "finally",
        Instanceof = "instanceof",
        Keyof = "keyof",
        Namespace = "namespace",
        Number = "number",
        Switch = "switch",
        Throw = "throw",
        Try = "try",
        Typeof = "typeof",
        Undefined = "undefined",
        Unknown = "unknown",
        Using = "using",
        Var = "var",
        Yield = "yield",
    }
}

impl Reserved {
    /// The code of the word's hint (SPEC 13.2 and 16). `export` is EN0226, with a
    /// fix-it to `public`, except in `export default`, which the parser reports as
    /// EN1009; `case` belongs to `switch` and `finally` to `try`.
    pub fn code(self) -> Code {
        match self {
            Reserved::Any => Code::EN0205,
            Reserved::Await | Reserved::Async => Code::EN1001,
            Reserved::Case | Reserved::Switch => Code::EN0209,
            Reserved::Catch | Reserved::Finally | Reserved::Throw | Reserved::Try => Code::EN0207,
            Reserved::Delete | Reserved::Namespace => Code::EN0222,
            Reserved::Export => Code::EN0226,
            Reserved::Instanceof | Reserved::Typeof => Code::EN0211,
            Reserved::Keyof => Code::EN1023,
            Reserved::Number => Code::EN0225,
            Reserved::Undefined => Code::EN0206,
            Reserved::Unknown => Code::EN0210,
            Reserved::Using => Code::EN0213,
            Reserved::Var => Code::EN0202,
            Reserved::Yield => Code::EN1002,
        }
    }
}

words! {
    /// SPEC 2 `Punct`, in its order: brackets and separators, then the binary
    /// operators, then assignment and increments, then comparisons and the four TS
    /// tokens (`===`, `!==`, `>>>`, `**`) that exist only to get a hint. Maximal munch
    /// picks the longest; `...` is tried before `..`, and both before `.5` (EN0006).
    Punct {
        LParen = "(",
        RParen = ")",
        LBrace = "{",
        RBrace = "}",
        LBracket = "[",
        RBracket = "]",
        Semi = ";",
        Comma = ",",
        Colon = ":",
        Dot = ".",
        DotDot = "..",
        DotDotDot = "...",
        FatArrow = "=>",
        At = "@",
        Question = "?",
        QuestionDot = "?.",
        QuestionQuestion = "??",
        Bang = "!",
        Tilde = "~",
        Plus = "+",
        Minus = "-",
        Star = "*",
        Slash = "/",
        Percent = "%",
        Amp = "&",
        Pipe = "|",
        Caret = "^",
        Shl = "<<",
        Shr = ">>",
        AmpAmp = "&&",
        PipePipe = "||",
        Eq = "=",
        PlusEq = "+=",
        MinusEq = "-=",
        StarEq = "*=",
        SlashEq = "/=",
        PercentEq = "%=",
        AmpEq = "&=",
        PipeEq = "|=",
        CaretEq = "^=",
        ShlEq = "<<=",
        ShrEq = ">>=",
        PlusPlus = "++",
        MinusMinus = "--",
        EqEq = "==",
        BangEq = "!=",
        Lt = "<",
        Le = "<=",
        Gt = ">",
        Ge = ">=",
        EqEqEq = "===",
        BangEqEq = "!==",
        Shr3 = ">>>",
        StarStar = "**",
    }
}

impl Punct {
    /// SPEC 2's `split_token`: closing type arguments splits `>>`, `>>>`, `>=` and
    /// `>>=` after their first `>`, and prefix or type position reads `**` as two `*`
    /// and `&&` as two `&`. Every other token stays whole.
    pub fn split(self) -> Option<(Punct, Punct)> {
        match self {
            Punct::Shr => Some((Punct::Gt, Punct::Gt)),
            Punct::Shr3 => Some((Punct::Gt, Punct::Shr)),
            Punct::Ge => Some((Punct::Gt, Punct::Eq)),
            Punct::ShrEq => Some((Punct::Gt, Punct::Ge)),
            Punct::StarStar => Some((Punct::Star, Punct::Star)),
            Punct::AmpAmp => Some((Punct::Amp, Punct::Amp)),
            _ => None,
        }
    }

    /// The code a TS-only token gets (SPEC 2): `===` and `!==` EN0201, `>>>` EN0208,
    /// and `**` EN1022, though only in binary position, where the parser recovers
    /// with a call to `pow`.
    pub fn habit_code(self) -> Option<Code> {
        match self {
            Punct::EqEqEq | Punct::BangEqEq => Some(Code::EN0201),
            Punct::Shr3 => Some(Code::EN0208),
            Punct::StarStar => Some(Code::EN1022),
            _ => None,
        }
    }
}
