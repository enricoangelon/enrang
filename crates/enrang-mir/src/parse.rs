//! The MIR text form, reading side (ARCHITECTURE 2.5; M3 plan b.6): the lexer, the
//! syntax of types, paths and constants, the top-level pass that reads every
//! declaration, and the body parser.
//!
//! `parse_module` reads in three passes: the top level, with types, paths and
//! constants as syntax and each body as a token range; the declarations, defined in
//! a new `Tcx` through `define_*` (`decls.rs`); then each body, whose places need
//! the types of its locals to read field and case names. Every local, statement,
//! terminator and body gets the span of its text in `module.mir`, so a diagnostic
//! on a fixture points into it.

use std::collections::BTreeMap;
use std::fmt;
use std::path::PathBuf;
use std::sync::Arc;

use enrang_base::{BytePos, FileOrigin, Idx, SourceMap, Span, Symbol, intern};
use enrang_hir::{
    ArrowId, ConstValue, Fact, FactId, FieldIdx, IntrinsicKind, IntrinsicName, LoopId, Mark,
    PathStep, Tcx, Ty, TyKind, VariantIdx,
};

use crate::body::{
    AggregateKind, AsmStmt, Block, Body, BodyNames, BodyOwner, Callee, Capture, ClassOp, ClosureFn,
    ConstKind, Constant, DropOrigin, ForOfLoop, ForeignRef, FormCall, LiteralStatic, LocalDecl,
    LocalKind, LoopSource, MirFact, MirRecord, MovePathKey, MoveStep, Operand, Place, Proj, Rvalue,
    ShimKind, Statement, StatementKind, Terminator, TerminatorKind, UnsafeRegion,
};
use crate::decls::{self, Names, Scope};
use crate::ids::{BlockId, Local, Point, RegionId};
use crate::print::{
    ALU_OPS, BINOPS, CAPTURES, CASTS, CHECKED, CLASS_OPS, CONVS, DEFAULT_MODULE, DEFAULT_TARGET,
    FORMS, HOLDERS, LOCAL_KINDS, LOOP_ROLES, ORIGINS, PERMS, PHASES, REASONS, RECORDS,
    REGION_KINDS, TY_SHIMS, UNOPS, named,
};
use crate::proj::{PlaceTy, canonicalize_projs, variant_named};

/// A text that is no MIR module: the message, and where (1-based line and column
/// in the text).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MirParseError {
    pub message: String,
    pub line: u32,
    pub col: u32,
}

impl fmt::Display for MirParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "module.mir:{}:{}: {}", self.line, self.col, self.message)
    }
}

impl std::error::Error for MirParseError {}

/// An error at a byte offset of the text, made a `MirParseError` once the text's
/// lines are known.
#[derive(Clone, Debug)]
pub(crate) struct Err0 {
    pub message: String,
    pub at: u32,
}

pub(crate) type PResult<T> = Result<T, Err0>;

pub(crate) fn err<T>(at: u32, message: impl Into<String>) -> PResult<T> {
    Err(Err0 {
        message: message.into(),
        at,
    })
}

fn locate(text: &str, e: Err0) -> MirParseError {
    let at = (e.at as usize).min(text.len());
    let before = &text[..at];
    let line = before.matches('\n').count() as u32 + 1;
    let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) as u32 + 1;
    MirParseError {
        message: e.message,
        line,
        col,
    }
}

/// Reads a module: its declarations into a new `Tcx` (target `x86_64-linux` unless
/// a `target "..";` line names another), and its bodies (A:803).
pub fn parse_module(text: &str) -> Result<(Tcx, Vec<Body>), MirParseError> {
    parse_inner(text).map_err(|e| locate(text, e))
}

/// Redefines, in `tcx`, the ADTs that `text` declares under the paths they already
/// have, keeping their ids: a changed field or case order, as a dev-runtime schema
/// change makes one, for `remap_ids` (plan b.10). Spans are `DUMMY`.
pub fn redefine_adts(tcx: &mut Tcx, text: &str) -> Result<(), MirParseError> {
    let mut run = || -> PResult<()> {
        let toks = lex(text)?;
        let mut p = Parser::new(&toks, BytePos(0));
        let top = p.module()?;
        decls::redefine(tcx, &top)
    };
    run().map_err(|e| locate(text, e))
}

fn parse_inner(text: &str) -> PResult<(Tcx, Vec<Body>)> {
    let toks = lex(text)?;
    let mut map = SourceMap::new();
    let file = map.add(
        PathBuf::from("module.mir"),
        Arc::from(text),
        FileOrigin::User,
    );
    let base = map.file(file).start;
    let mut p = Parser::new(&toks, base);
    let top = p.module()?;
    let target = top
        .target
        .clone()
        .unwrap_or_else(|| DEFAULT_TARGET.to_owned());
    let Some(mut tcx) = Tcx::for_target(&target, Arc::new(map)) else {
        return err(0, format!("no target `{target}`"));
    };
    let names = decls::define(&mut tcx, &top, file, base)?;
    let mut bodies = Vec::new();
    for b in &top.bodies {
        let mut bp = BodyParser::new(&toks, base, &mut tcx, &names, b)?;
        bodies.push(bp.body()?);
    }
    Ok((tcx, bodies))
}

// ---------------------------------------------------------------------------------
// The lexer.

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Tok {
    Ident(String),
    Int(u128),
    Float(f64),
    Str(String),
    Punct(&'static str),
    Eof,
}

#[derive(Clone, Debug)]
pub(crate) struct Token {
    pub tok: Tok,
    pub lo: u32,
    pub hi: u32,
    /// A `// ...` comment that follows on the same line: a local's name.
    pub comment: Option<String>,
}

const PUNCTS: [&str; 24] = [
    "::", "->", "=>", "{", "}", "(", ")", "[", "]", "<", ">", ",", ";", ":", "=", "&", "*", ".",
    "|", "@", "!", "#", "-", "?",
];

pub(crate) fn lex(text: &str) -> PResult<Vec<Token>> {
    let bytes = text.as_bytes();
    let scan = |mut k: usize, f: fn(&u8) -> bool| {
        while bytes.get(k).is_some_and(f) {
            k += 1;
        }
        k
    };
    let mut toks: Vec<Token> = Vec::new();
    let (mut i, mut line, mut line_of_last) = (0, 0usize, 0usize);
    while i < bytes.len() {
        let c = bytes[i];
        let lo = i as u32;
        if c.is_ascii_whitespace() {
            line += usize::from(c == b'\n');
            i += 1;
            continue;
        }
        if text[i..].starts_with("//") {
            let end = text[i..].find('\n').map_or(text.len(), |n| i + n);
            let comment = text[i + 2..end].trim().to_owned();
            // `//~ CODE` is a compile-test anchor, never a local's name.
            if let Some(last) = toks.last_mut()
                && line_of_last == line
                && !comment.starts_with('~')
            {
                last.comment = Some(comment);
            }
            i = end;
            continue;
        }
        line_of_last = line;
        let (tok, end) = if c.is_ascii_alphabetic() || c == b'_' {
            let end = scan(i, |b| b.is_ascii_alphanumeric() || *b == b'_');
            (Tok::Ident(text[i..end].to_owned()), end)
        } else if text[i..].starts_with("0x") {
            let end = scan(i + 2, u8::is_ascii_hexdigit);
            let Ok(v) = u128::from_str_radix(&text[i + 2..end], 16) else {
                return err(lo, "a hex number out of range");
            };
            (Tok::Int(v), end)
        } else if c.is_ascii_digit() {
            // After `.` a number is a field (`_1.0.1`), never a fraction.
            let after_dot = matches!(toks.last().map(|t| &t.tok), Some(Tok::Punct(".")));
            let mut end = scan(i, u8::is_ascii_digit);
            let mut float = false;
            if !after_dot {
                if bytes.get(end) == Some(&b'.')
                    && bytes.get(end + 1).is_some_and(u8::is_ascii_digit)
                {
                    (float, end) = (true, scan(end + 1, u8::is_ascii_digit));
                }
                let e = end + 1 + usize::from(matches!(bytes.get(end + 1), Some(b'-' | b'+')));
                if bytes.get(end) == Some(&b'e') && bytes.get(e).is_some_and(u8::is_ascii_digit) {
                    (float, end) = (true, scan(e, u8::is_ascii_digit));
                }
            }
            let tok = match float {
                true => text[i..end].parse().map(Tok::Float).ok(),
                false => text[i..end].parse().map(Tok::Int).ok(),
            };
            match tok {
                Some(tok) => (tok, end),
                None if float => return err(lo, "a malformed number"),
                None => return err(lo, "a number out of range"),
            }
        } else if c == b'"' {
            let (s, end) = string(text, i)?;
            (Tok::Str(s), end)
        } else {
            let Some(p) = PUNCTS.iter().find(|p| text[i..].starts_with(**p)) else {
                let ch = text[i..].chars().next().unwrap_or(' ');
                return err(lo, format!("an unexpected character `{ch}`"));
            };
            (Tok::Punct(p), i + p.len())
        };
        let hi = end as u32;
        toks.push(Token {
            tok,
            lo,
            hi,
            comment: None,
        });
        i = end;
    }
    let end = text.len() as u32;
    toks.push(Token {
        tok: Tok::Eof,
        lo: end,
        hi: end,
        comment: None,
    });
    Ok(toks)
}

/// The string literal opening at byte `i`, unescaped, and the byte after it.
fn string(text: &str, i: usize) -> PResult<(String, usize)> {
    let lo = i as u32;
    let mut s = String::new();
    let mut j = i + 1;
    let mut chars = text[j..].chars();
    loop {
        let Some(ch) = chars.next() else {
            return err(lo, "an unterminated string");
        };
        j += ch.len_utf8();
        if ch == '"' {
            return Ok((s, j));
        }
        if ch != '\\' {
            s.push(ch);
            continue;
        }
        let Some(e) = chars.next() else {
            return err(lo, "an unterminated string");
        };
        j += e.len_utf8();
        s.push(match e {
            'n' => '\n',
            't' => '\t',
            'r' => '\r',
            '0' => '\0',
            '"' | '\\' => e,
            'u' => {
                let rest = &text[j..];
                let close = rest.find('}');
                let hex = close.and_then(|c| rest.get(1..c)).unwrap_or("");
                let Some(ch) = u32::from_str_radix(hex, 16).ok().and_then(char::from_u32) else {
                    return err(lo, "a malformed \\u escape");
                };
                j += close.map_or(0, |c| c + 1);
                chars = text[j..].chars();
                ch
            }
            other => return err(lo, format!("an unknown escape `\\{other}`")),
        });
    }
}

// ---------------------------------------------------------------------------------
// The parser's cursor.

pub(crate) struct Parser<'a> {
    toks: &'a [Token],
    pub pos: usize,
    base: BytePos,
}

impl<'a> Parser<'a> {
    pub fn new(toks: &'a [Token], base: BytePos) -> Parser<'a> {
        Parser { toks, pos: 0, base }
    }

    pub fn peek(&self) -> &Tok {
        &self.toks[self.pos].tok
    }

    pub fn peek_at(&self, n: usize) -> &Tok {
        &self.toks[(self.pos + n).min(self.toks.len() - 1)].tok
    }

    pub fn at(&self) -> u32 {
        self.toks[self.pos].lo
    }

    fn bump(&mut self) -> &'a Token {
        let t = &self.toks[self.pos];
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        t
    }

    pub fn is(&self, p: &str) -> bool {
        matches!(self.peek(), Tok::Punct(q) if *q == p)
    }

    pub fn is_at(&self, n: usize, p: &str) -> bool {
        matches!(self.peek_at(n), Tok::Punct(q) if *q == p)
    }

    pub fn is_kw(&self, kw: &str) -> bool {
        matches!(self.peek(), Tok::Ident(s) if s == kw)
    }

    pub fn eat(&mut self, p: &str) -> bool {
        if self.is(p) {
            self.bump();
            true
        } else {
            false
        }
    }

    pub fn eat_kw(&mut self, kw: &str) -> bool {
        if self.is_kw(kw) {
            self.bump();
            true
        } else {
            false
        }
    }

    /// A name `table` spells, or "no `what` `name`" at `at`.
    pub fn word_in<T: Clone>(&mut self, table: &[(T, &str)], what: &str, at: u32) -> PResult<T> {
        let word = self.ident()?;
        named(table, &word).map_or_else(|| err(at, format!("no {what} `{word}`")), Ok)
    }

    /// Eats `kw` when `p` follows it, and `p`: a keyword-and-paren head.
    pub fn eat_kw_then(&mut self, kw: &str, p: &str) -> bool {
        let ok = self.is_kw(kw) && self.is_at(1, p);
        if ok {
            self.bump();
            self.bump();
        }
        ok
    }

    pub fn expect(&mut self, p: &str) -> PResult<()> {
        if self.eat(p) {
            Ok(())
        } else {
            self.unexpected(&format!("`{p}`"))
        }
    }

    pub fn expect_kw(&mut self, kw: &str) -> PResult<()> {
        if self.eat_kw(kw) {
            Ok(())
        } else {
            self.unexpected(&format!("`{kw}`"))
        }
    }

    pub fn unexpected<T>(&self, wanted: &str) -> PResult<T> {
        let found = match self.peek() {
            Tok::Ident(s) => format!("`{s}`"),
            Tok::Int(n) => format!("`{n}`"),
            Tok::Float(f) => format!("`{f}`"),
            Tok::Str(s) => format!("\"{s}\""),
            Tok::Punct(p) => format!("`{p}`"),
            Tok::Eof => "the end of the text".to_owned(),
        };
        err(self.at(), format!("expected {wanted}, found {found}"))
    }

    pub fn ident(&mut self) -> PResult<String> {
        match self.peek().clone() {
            Tok::Ident(s) => {
                self.bump();
                Ok(s)
            }
            _ => self.unexpected("a name"),
        }
    }

    /// A name, or a number standing as one (a tuple-like case's field `0`).
    pub fn name(&mut self) -> PResult<String> {
        match self.peek().clone() {
            Tok::Int(n) => {
                self.bump();
                Ok(n.to_string())
            }
            _ => self.ident(),
        }
    }

    pub fn int(&mut self) -> PResult<u128> {
        match *self.peek() {
            Tok::Int(n) => {
                self.bump();
                Ok(n)
            }
            _ => self.unexpected("a number"),
        }
    }

    pub fn u32(&mut self) -> PResult<u32> {
        let at = self.at();
        let n = self.int()?;
        u32::try_from(n).or_else(|_| err(at, "a number out of range"))
    }

    pub fn string(&mut self) -> PResult<String> {
        match self.peek().clone() {
            Tok::Str(s) => {
                self.bump();
                Ok(s)
            }
            _ => self.unexpected("a string"),
        }
    }

    /// The span of the tokens from `start` up to the cursor.
    pub fn span_from(&self, start: usize) -> Span {
        let lo = self.toks[start].lo;
        let hi = self.toks[self.pos.saturating_sub(1).max(start)].hi;
        Span {
            lo: self.base + lo,
            hi: self.base + hi.max(lo),
        }
    }

    /// An identifier `<prefix><digits>` (`_3`, `bb2`, `r0`, `l1`, `f0`) as its number.
    pub fn numbered(&mut self, prefix: &str) -> PResult<u32> {
        if let Tok::Ident(s) = self.peek()
            && let Some(rest) = s.strip_prefix(prefix)
            && !rest.is_empty()
            && rest.bytes().all(|b| b.is_ascii_digit())
            && let Ok(n) = rest.parse::<u32>()
        {
            self.bump();
            return Ok(n);
        }
        self.unexpected(&format!("`{prefix}<n>`"))
    }

    pub fn is_numbered(&self, prefix: &str) -> bool {
        matches!(self.peek(), Tok::Ident(s) if s.strip_prefix(prefix).is_some_and(|r| !r.is_empty() && r.bytes().all(|b| b.is_ascii_digit())))
    }

    fn comma_list<T>(
        &mut self,
        close: &str,
        mut item: impl FnMut(&mut Self) -> PResult<T>,
    ) -> PResult<Vec<T>> {
        let mut out = Vec::new();
        while !self.is(close) {
            out.push(item(self)?);
            if !self.eat(",") {
                break;
            }
        }
        self.expect(close)?;
        Ok(out)
    }

    // -----------------------------------------------------------------------------
    // Types.

    pub fn ty(&mut self) -> PResult<TyAst> {
        let mut t = self.ty_unary()?;
        while self.is("|") && matches!(self.peek_at(1), Tok::Ident(s) if s == "null") {
            self.bump();
            self.bump();
            t = TyAst::Nullable(Box::new(t));
        }
        Ok(t)
    }

    fn ty_unary(&mut self) -> PResult<TyAst> {
        if self.eat("&") {
            return Ok(TyAst::Ref(Box::new(self.ty_unary()?)));
        }
        if self.eat("*") {
            return Ok(TyAst::Raw(Box::new(self.ty_unary()?)));
        }
        let mut t = self.ty_atom()?;
        while self.is("[") {
            if self.is_at(1, "]") {
                self.bump();
                self.bump();
                t = TyAst::Array(Box::new(t));
            } else if matches!(self.peek_at(1), Tok::Int(_)) && self.is_at(2, "]") {
                self.bump();
                let n = self.int()?;
                self.bump();
                let n = u64::try_from(n).or_else(|_| err(self.at(), "a length out of range"))?;
                t = TyAst::Fixed(Box::new(t), n);
            } else {
                break;
            }
        }
        Ok(t)
    }

    fn ty_atom(&mut self) -> PResult<TyAst> {
        let at = self.at();
        if self.eat("[") {
            let parts = self.comma_list("]", |p| p.ty())?;
            return Ok(TyAst::Tuple(parts));
        }
        if self.eat("{") {
            let fields = self.comma_list("}", |p| {
                let name = intern(&p.name()?);
                let optional = p.eat("?");
                p.expect(":")?;
                Ok((name, optional, p.ty()?))
            })?;
            return Ok(TyAst::Object(fields));
        }
        if self.is("(") {
            self.bump();
            let params = self.comma_list(")", |p| {
                let mark = p.mark();
                Ok((mark, p.ty()?))
            })?;
            if self.eat("=>") {
                let readonly = self.eat_kw("readonly");
                let ret = self.ty()?;
                return Ok(TyAst::Fn {
                    abi: None,
                    unsafety: false,
                    params,
                    ret: Box::new(ret),
                    readonly,
                    closure: true,
                });
            }
            return match <[_; 1]>::try_from(params) {
                Ok([(Mark::None, t)]) => Ok(t),
                _ => err(at, "expected `=>` after a closure type's parameters"),
            };
        }
        if self.eat("@") {
            self.expect_kw("abi")?;
            self.expect("(")?;
            let abi = self.string()?;
            self.expect(")")?;
            let unsafety = self.eat_kw("unsafe");
            self.expect_kw("fn")?;
            return self.fn_ty(Some(abi), unsafety);
        }
        if self.is_kw("unsafe") && matches!(self.peek_at(1), Tok::Ident(s) if s == "fn") {
            self.bump();
            self.bump();
            return self.fn_ty(None, true);
        }
        if self.is_kw("fn") && self.is_at(1, "(") {
            self.bump();
            return self.fn_ty(None, false);
        }
        if self.is_kw("_") {
            self.bump();
            return Ok(TyAst::Error);
        }
        let name = intern(&self.ident()?);
        let args = if self.eat("<") {
            self.comma_list(">", |p| p.ty())?
        } else {
            Vec::new()
        };
        Ok(TyAst::Named { name, args, at })
    }

    fn fn_ty(&mut self, abi: Option<String>, unsafety: bool) -> PResult<TyAst> {
        self.expect("(")?;
        let params = self.comma_list(")", |p| {
            let mark = p.mark();
            Ok((mark, p.ty()?))
        })?;
        self.expect("=>")?;
        let readonly = self.eat_kw("readonly");
        let ret = self.ty()?;
        Ok(TyAst::Fn {
            abi,
            unsafety,
            params,
            ret: Box::new(ret),
            readonly,
            closure: false,
        })
    }

    pub fn mark(&mut self) -> Mark {
        if self.eat_kw("let") {
            Mark::Let
        } else if self.eat_kw("const") {
            Mark::Const
        } else {
            Mark::None
        }
    }

    /// `[ "extends" ty { "&" ty } ]`.
    fn bounds(&mut self) -> PResult<Vec<TyAst>> {
        let mut bounds = Vec::new();
        if self.eat_kw("extends") {
            bounds.push(self.ty()?);
            while self.eat("&") {
                bounds.push(self.ty()?);
            }
        }
        Ok(bounds)
    }

    // -----------------------------------------------------------------------------
    // Paths.

    pub fn path(&mut self) -> PResult<PathAst> {
        let at = self.at();
        let module = match self.peek() {
            Tok::Str(_) if self.is_at(1, "::") => {
                let m = self.string()?;
                self.bump();
                Some(m)
            }
            _ => None,
        };
        let mut segs = Vec::new();
        loop {
            let name = if self.eat("#") {
                format!("#{}", self.ident()?)
            } else {
                self.ident()?
            };
            let args = if self.eat("<") {
                self.comma_list(">", |p| {
                    let implicit = p.is_kw("implicit")
                        && matches!(p.peek_at(1), Tok::Ident(_) | Tok::Punct("{"));
                    if implicit {
                        p.bump();
                    }
                    let ty = p.ty()?;
                    let bounds = p.bounds()?;
                    Ok(GenArg {
                        ty,
                        bounds,
                        implicit,
                    })
                })?
            } else {
                Vec::new()
            };
            segs.push(SegAst {
                name: intern(&name),
                args,
            });
            if !(self.is("::") && !matches!(self.peek_at(1), Tok::Str(_))) {
                break;
            }
            if !matches!(self.peek_at(1), Tok::Ident(_)) && !self.is_at(1, "#") {
                break;
            }
            self.bump();
        }
        let overload = if self.is("@") && self.is_at(1, "[") {
            self.bump();
            self.bump();
            Some(self.comma_list("]", |p| p.string())?)
        } else {
            None
        };
        Ok(PathAst {
            module,
            segs,
            overload,
            at,
        })
    }

    // -----------------------------------------------------------------------------
    // Constants.

    /// A scalar or a constant tree.
    pub fn const_ast(&mut self) -> PResult<ConstAst> {
        let at = self.at();
        if self.eat("-") {
            return match self.peek().clone() {
                Tok::Int(n) => {
                    self.bump();
                    let n = i128::try_from(n).or_else(|_| err(at, "a number out of range"))?;
                    Ok(ConstAst::Int(-n, at))
                }
                Tok::Float(f) => {
                    self.bump();
                    Ok(ConstAst::Float(-f))
                }
                Tok::Ident(s) if s == "inf" => {
                    self.bump();
                    Ok(ConstAst::Float(f64::NEG_INFINITY))
                }
                _ => self.unexpected("a number"),
            };
        }
        match self.peek().clone() {
            Tok::Int(n) => {
                self.bump();
                let n = i128::try_from(n).or_else(|_| err(at, "a number out of range"))?;
                return Ok(ConstAst::Int(n, at));
            }
            Tok::Float(f) => {
                self.bump();
                return Ok(ConstAst::Float(f));
            }
            Tok::Str(s) => {
                self.bump();
                return Ok(ConstAst::Str(s));
            }
            _ => {}
        }
        if self.eat("[") {
            return Ok(ConstAst::Array(self.comma_list("]", |p| p.const_ast())?));
        }
        let Tok::Ident(word) = self.peek().clone() else {
            return self.unexpected("a constant");
        };
        let simple = match word.as_str() {
            "true" => Some(ConstAst::Bool(true)),
            "false" => Some(ConstAst::Bool(false)),
            "void" => Some(ConstAst::Void),
            "null" => Some(ConstAst::Null),
            "inf" => Some(ConstAst::Float(f64::INFINITY)),
            _ => None,
        };
        if let Some(c) = simple {
            self.bump();
            return Ok(c);
        }
        if self.eat_kw_then("nan", "(") {
            let bits = self.int()?;
            self.expect(")")?;
            return Ok(ConstAst::Nan(bits as u64));
        }
        if self.eat_kw_then("tuple", "(") {
            return Ok(ConstAst::Tuple(self.comma_list(")", |p| p.const_ast())?));
        }
        if self.eat_kw_then("present", "(") {
            let inner = self.const_ast()?;
            self.expect(")")?;
            return Ok(ConstAst::Present(Box::new(inner)));
        }
        if self.eat_kw_then("object", "{") {
            return Ok(ConstAst::Object(self.const_fields()?));
        }
        if self.eat_kw_then("view", "<") {
            let elem = self.ty()?;
            self.expect(">")?;
            self.expect("[")?;
            let items = self.comma_list("]", |p| p.const_ast())?;
            return Ok(ConstAst::View(elem, items));
        }
        match word.as_str() {
            "fn" => {
                self.bump();
                Ok(ConstAst::Fn(self.path()?))
            }
            "static_addr" => {
                self.bump();
                self.expect("(")?;
                let c = ConstAst::Static(self.path()?);
                self.expect(")")?;
                Ok(c)
            }
            "overridden" => {
                self.bump();
                self.expect("(")?;
                let name = self.name()?;
                self.expect(")")?;
                Ok(ConstAst::Overridden(name, at))
            }
            _ => {
                let ty = self.ty()?;
                let case = if self.eat("::") {
                    Some(intern(&self.ident()?))
                } else {
                    None
                };
                self.expect("{")?;
                let fields = self.const_fields()?;
                Ok(ConstAst::Adt {
                    ty,
                    case,
                    fields,
                    at,
                })
            }
        }
    }

    /// `name: tree, ... }`, the opening brace read.
    fn const_fields(&mut self) -> PResult<Vec<(String, ConstAst, u32)>> {
        self.comma_list("}", |p| {
            let at = p.at();
            let name = p.name()?;
            p.expect(":")?;
            Ok((name, p.const_ast()?, at))
        })
    }

    // -----------------------------------------------------------------------------
    // The top level.

    pub fn module(&mut self) -> PResult<TopLevel> {
        let mut top = TopLevel::default();
        if self.eat_kw("target") {
            top.target = Some(self.string()?);
            self.expect(";")?;
        }
        if self.eat_kw("module") {
            top.module = Some(self.string()?);
            self.expect(";")?;
        }
        while *self.peek() != Tok::Eof {
            self.item(&mut top)?;
        }
        Ok(top)
    }

    fn attrs(&mut self) -> PResult<Vec<AttrAst>> {
        let mut out = Vec::new();
        while self.is("@") && matches!(self.peek_at(1), Tok::Ident(_)) {
            let at = self.at();
            self.bump();
            let name = self.ident()?;
            let mut more = Vec::new();
            let arg = if self.eat("(") {
                let s = self.string()?;
                while self.eat(",") {
                    more.push(self.string()?);
                }
                self.expect(")")?;
                Some(s)
            } else {
                None
            };
            out.push(AttrAst {
                name,
                arg,
                more,
                at,
            });
        }
        Ok(out)
    }

    /// The last segment's angle list of a declaration's path, as its own type
    /// parameters (`class Stack<T extends Clone>`), taken off the path.
    fn own_generics(path: &mut PathAst) -> PResult<Vec<GenParam>> {
        let Some(seg) = path.segs.last_mut() else {
            return Ok(Vec::new());
        };
        std::mem::take(&mut seg.args)
            .into_iter()
            .map(|a| match a.ty {
                TyAst::Named { name, args, at } if args.is_empty() && !a.implicit => Ok(GenParam {
                    name,
                    bounds: a.bounds,
                    at,
                    implicit: None,
                }),
                ty if a.implicit && a.bounds.is_empty() => Ok(GenParam {
                    name: intern("_"),
                    bounds: Vec::new(),
                    at: path.at,
                    implicit: Some(ty),
                }),
                _ => err(path.at, "a declaration's own parameters are names"),
            })
            .collect()
    }

    fn item(&mut self, top: &mut TopLevel) -> PResult<()> {
        let start = self.pos;
        let attrs = self.attrs()?;
        if let Some(owner) = self.other_owner()? {
            let body = self.other_body(owner, start)?;
            top.bodies.push(body);
            return Ok(());
        }
        let kind = if self.eat_kw("class") {
            let mut path = self.path()?;
            let generics = Parser::own_generics(&mut path)?;
            let base = if self.eat_kw("extends") {
                Some(self.ty()?)
            } else {
                None
            };
            let wtf = self.eat_kw("writes_through_fields");
            self.expect("{")?;
            let mut fields = Vec::new();
            while !self.eat("}") {
                fields.push(self.field()?);
            }
            DeclKind::Class {
                path,
                generics,
                base,
                wtf,
                fields,
            }
        } else if self.eat_kw("enum") {
            let mut path = self.path()?;
            let generics = Parser::own_generics(&mut path)?;
            self.expect("{")?;
            let cases = self.comma_list("}", |p| {
                let at = p.at();
                let name = intern(&p.ident()?);
                let mut fields = Vec::new();
                if p.eat("{") {
                    fields = p.comma_list("}", |p| {
                        let name = intern(&p.name()?);
                        p.expect(":")?;
                        Ok((name, p.ty()?))
                    })?;
                }
                let value = if p.eat("=") {
                    match p.peek().clone() {
                        Tok::Str(s) => {
                            p.bump();
                            Some(CaseValue::Text(s))
                        }
                        _ => {
                            let neg = p.eat("-");
                            let n = p.int()? as i128;
                            Some(CaseValue::Int(if neg { -n } else { n }))
                        }
                    }
                } else {
                    None
                };
                Ok(CaseAst {
                    name,
                    fields,
                    value,
                    at,
                })
            })?;
            DeclKind::Enum {
                path,
                generics,
                cases,
            }
        } else if self.eat_kw("interface") {
            let mut path = self.path()?;
            let generics = Parser::own_generics(&mut path)?;
            self.expect("{")?;
            self.expect("}")?;
            DeclKind::Iface { path, generics }
        } else if self.is_kw("fn")
            || self.is_kw("static") && !self.is_at(2, ":")
            || self.is_kw("move")
        {
            DeclKind::Fn(self.fn_decl()?)
        } else if self.eat_kw("static") {
            let path = self.path()?;
            self.expect(":")?;
            let ty = self.ty()?;
            self.expect(";")?;
            DeclKind::Static { path, ty }
        } else if self.eat_kw("const") {
            let path = self.path()?;
            self.expect(":")?;
            let ty = self.ty()?;
            self.expect("=")?;
            let value = self.const_ast()?;
            self.expect(";")?;
            DeclKind::Const { path, ty, value }
        } else if self.eat_kw("extend") {
            let mut path = self.path()?;
            let generics = Parser::own_generics(&mut path)?;
            self.expect(":")?;
            let ty = self.ty()?;
            self.expect(";")?;
            DeclKind::Extend { path, generics, ty }
        } else if self.eat_kw("instantiate") {
            self.path()?;
            self.expect(";")?;
            return Ok(());
        } else if self.eat_kw("test") {
            let path = self.path()?;
            if self.eat(";") {
                DeclKind::Test { path }
            } else {
                let owner = OwnerAst::Test(path.clone());
                top.decls.push(DeclAst {
                    attrs,
                    kind: DeclKind::Test { path },
                });
                let body = self.other_body(owner, start)?;
                top.bodies.push(body);
                return Ok(());
            }
        } else {
            return self.unexpected("a declaration or a body");
        };
        if let DeclKind::Fn(f) = &kind
            && f.body.is_some()
        {
            top.bodies.push(BodyAst {
                owner: OwnerAst::Fn(f.path.clone()),
                params: Vec::new(),
                ret: None,
                range: f.body.expect("a body"),
                start,
            });
        }
        top.decls.push(DeclAst { attrs, kind });
        Ok(())
    }

    /// The owner of a body that has no declaration of its own: the statements
    /// body, an arrow of an owner, or a shim.
    fn other_owner(&mut self) -> PResult<Option<OwnerAst>> {
        if self.eat_kw("statements") {
            return Ok(Some(OwnerAst::Statements));
        }
        if self.eat_kw("shim") {
            return Ok(Some(OwnerAst::Shim(self.shim_kind()?)));
        }
        if !self.eat_kw("arrow") {
            return Ok(None);
        }
        self.expect("#")?;
        let arrow = self.u32()?;
        self.expect_kw("of")?;
        let parent = if self.eat_kw("fn") {
            ParentAst::Fn(self.path()?)
        } else if self.eat_kw("const") {
            ParentAst::Const(self.path()?)
        } else if self.eat_kw("test") {
            ParentAst::Test(self.path()?)
        } else {
            self.expect_kw("statements")?;
            ParentAst::Statements
        };
        Ok(Some(OwnerAst::Arrow(parent, arrow)))
    }

    fn shim_kind(&mut self) -> PResult<ShimAst> {
        let word = self.ident()?;
        self.expect("(")?;
        let k = match word.as_str() {
            "fn_as_closure" => ShimAst::Fn(true, self.path()?),
            "string_form" => ShimAst::Fn(false, self.path()?),
            "string_form_env" => {
                let from = self.ty()?;
                self.expect(",")?;
                ShimAst::Env(from, self.ty()?)
            }
            w if TY_SHIMS.iter().any(|s| s.1 == w) => ShimAst::Ty(word, self.ty()?),
            _ => return err(self.at(), format!("no shim `{word}`")),
        };
        self.expect(")")?;
        Ok(k)
    }

    fn field(&mut self) -> PResult<FieldAst> {
        let at = self.at();
        let mut vis = None;
        let mut readonly = false;
        loop {
            if self.eat_kw("private") {
                vis = Some(enrang_hir::Vis::Private);
            } else if self.eat_kw("protected") {
                vis = Some(enrang_hir::Vis::Protected);
            } else if self.is_kw("readonly") && !self.is_at(1, ":") && !self.is_at(1, "?") {
                self.bump();
                readonly = true;
            } else {
                break;
            }
        }
        let name = intern(&self.name()?);
        let optional = self.eat("?");
        self.expect(":")?;
        let mut readonly_refs = Vec::new();
        if self.eat_kw("readonly") {
            readonly_refs.push(Vec::new());
        }
        let ty = self.ty()?;
        if self.eat_kw("readonly_at") {
            self.expect("(")?;
            let more = self.comma_list(")", |p| {
                p.expect("[")?;
                p.comma_list("]", |p| p.u32())
            })?;
            readonly_refs.extend(more);
        }
        let mut has_default = false;
        if self.eat("=") {
            self.expect_kw("default")?;
            has_default = true;
        }
        let is_override = self.eat_kw("override");
        self.expect(";")?;
        Ok(FieldAst {
            name,
            vis,
            readonly,
            optional,
            ty,
            readonly_refs,
            has_default,
            is_override,
            at,
        })
    }

    fn fn_decl(&mut self) -> PResult<FnAst> {
        let receiver = if self.eat_kw("static") {
            Some(enrang_hir::Receiver::Static)
        } else if self.eat_kw("move") {
            Some(enrang_hir::Receiver::Move)
        } else {
            None
        };
        self.expect_kw("fn")?;
        let mut path = self.path()?;
        let generics = Parser::own_generics(&mut path)?;
        self.expect("(")?;
        let params = self.comma_list(")", |p| p.param())?;
        self.expect("->")?;
        let ret_readonly = self.eat_kw("readonly");
        let ret = self.ty()?;
        let mut wheres = Vec::new();
        if self.eat_kw("where") {
            loop {
                let at = self.at();
                let name = intern(&self.ident()?);
                let bounds = self.bounds()?;
                if bounds.is_empty() {
                    return self.unexpected("`extends`");
                }
                wheres.push(GenParam {
                    name,
                    bounds,
                    at,
                    implicit: None,
                });
                if !self.eat(",") {
                    break;
                }
            }
        }
        let contract = self.contract()?;
        let body = if self.eat(";") {
            None
        } else {
            Some(self.skip_body()?)
        };
        Ok(FnAst {
            receiver,
            path,
            generics,
            params,
            ret,
            ret_readonly,
            wheres,
            contract,
            body,
        })
    }

    fn param(&mut self) -> PResult<ParamAst> {
        let start = self.pos;
        let mark = self.mark();
        let local = self.numbered("_")?;
        self.expect(":")?;
        let ty = self.ty()?;
        let has_default = if self.eat("=") {
            self.expect_kw("default")?;
            true
        } else {
            false
        };
        Ok(ParamAst {
            mark,
            local,
            ty,
            has_default,
            span: self.span_from(start),
        })
    }

    fn contract(&mut self) -> PResult<Option<ContractAst>> {
        let mut c = ContractAst::default();
        let mut any = false;
        loop {
            let ints = |p: &mut Self| -> PResult<Vec<u32>> {
                p.expect("(")?;
                p.comma_list(")", |p| p.u32())
            };
            if self.eat_kw("perms") {
                self.expect("(")?;
                c.perms = Some(self.comma_list(")", |p| {
                    let at = p.at();
                    p.word_in(PERMS, "permission", at)
                })?);
            } else if self.eat_kw("sources") {
                c.sources = Some(ints(self)?);
            } else if self.eat_kw("through_fields") {
                c.through_fields = ints(self)?;
            } else if self.eat_kw("through_read") {
                c.through_read = ints(self)?;
            } else if self.eat_kw("moves") {
                c.moves = ints(self)?.into_iter().map(|n| n != 0).collect();
            } else if self.eat_kw("stores") {
                self.expect("(")?;
                c.stores = self.comma_list(")", |p| {
                    let from = p.u32()?;
                    p.expect("->")?;
                    let into = p.u32()?;
                    let mut s = enrang_hir::Store {
                        from,
                        into,
                        fields_only: false,
                        read: false,
                        read_set_only: false,
                    };
                    loop {
                        if p.eat_kw("fields_only") {
                            s.fields_only = true;
                        } else if p.eat_kw("read_set_only") {
                            s.read_set_only = true;
                        } else if p.eat_kw("read") {
                            s.read = true;
                        } else {
                            break;
                        }
                    }
                    Ok(s)
                })?;
            } else if self.eat_kw("result") {
                c.result = Some(if self.eat_kw("none") {
                    ResultAst::None
                } else if self.eat_kw("writable") {
                    ResultAst::Writable
                } else {
                    self.expect_kw("readonly")?;
                    self.expect("(")?;
                    let r = self.reason()?;
                    self.expect(")")?;
                    ResultAst::ReadOnly(r)
                });
            } else {
                break;
            }
            any = true;
        }
        Ok(any.then_some(c))
    }

    fn reason(&mut self) -> PResult<ReasonAst> {
        let at = self.at();
        let word = self.ident()?;
        if let Some(r) = named(REASONS, &word) {
            return Ok(ReasonAst::Simple(r));
        }
        Ok(match word.as_str() {
            "stored" => ReasonAst::Simple(enrang_hir::Reason::StoredSource(self.u32()?)),
            "constant" => ReasonAst::Path(0, self.path()?),
            "static" => ReasonAst::Path(1, self.path()?),
            "readonly_result" => ReasonAst::Path(2, self.path()?),
            "readonly_field" => {
                let path = self.path()?;
                self.expect(".")?;
                ReasonAst::Field(path, self.name()?)
            }
            other => return err(at, format!("no reason `{other}`")),
        })
    }

    /// Skips a balanced `{ ... }`, returning its token range, braces included.
    fn skip_body(&mut self) -> PResult<(usize, usize)> {
        let start = self.pos;
        self.expect("{")?;
        let mut depth = 1;
        while depth > 0 {
            match self.peek() {
                Tok::Punct("{") => depth += 1,
                Tok::Punct("}") => depth -= 1,
                Tok::Eof => return err(self.toks[start].lo, "an unclosed body"),
                _ => {}
            }
            self.bump();
        }
        Ok((start, self.pos))
    }

    /// `( params ) -> ty { ... }` of a body with no declaration of its own.
    fn other_body(&mut self, owner: OwnerAst, start: usize) -> PResult<BodyAst> {
        self.expect("(")?;
        let params = self.comma_list(")", |p| p.param())?;
        self.expect("->")?;
        let ret = self.ty()?;
        let range = self.skip_body()?;
        Ok(BodyAst {
            owner,
            params,
            ret: Some(ret),
            range,
            start,
        })
    }
}

// ---------------------------------------------------------------------------------
// Syntax trees of the top level.

/// A type as written; `decls::resolve_ty` gives it a `Ty`.
#[derive(Clone, Debug)]
pub(crate) enum TyAst {
    Named {
        name: Symbol,
        args: Vec<TyAst>,
        at: u32,
    },
    Ref(Box<TyAst>),
    Raw(Box<TyAst>),
    Nullable(Box<TyAst>),
    Array(Box<TyAst>),
    Fixed(Box<TyAst>, u64),
    Tuple(Vec<TyAst>),
    Object(Vec<(Symbol, bool, TyAst)>),
    Fn {
        abi: Option<String>,
        unsafety: bool,
        params: Vec<(Mark, TyAst)>,
        ret: Box<TyAst>,
        readonly: bool,
        closure: bool,
    },
    Error,
}

#[derive(Clone, Debug)]
pub(crate) struct GenArg {
    pub ty: TyAst,
    pub bounds: Vec<TyAst>,
    /// `implicit I` or `implicit { .. }`: the parameter an interface- or
    /// object-typed parameter makes (D5).
    pub implicit: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct SegAst {
    pub name: Symbol,
    pub args: Vec<GenArg>,
}

#[derive(Clone, Debug)]
pub(crate) struct PathAst {
    pub module: Option<String>,
    pub segs: Vec<SegAst>,
    pub overload: Option<Vec<String>>,
    pub at: u32,
}

#[derive(Clone, Debug)]
pub(crate) enum ConstAst {
    Int(i128, u32),
    Float(f64),
    Nan(u64),
    Bool(bool),
    Void,
    Str(String),
    Fn(PathAst),
    Static(PathAst),
    Overridden(String, u32),
    Array(Vec<ConstAst>),
    Tuple(Vec<ConstAst>),
    Object(Vec<(String, ConstAst, u32)>),
    Adt {
        ty: TyAst,
        case: Option<Symbol>,
        fields: Vec<(String, ConstAst, u32)>,
        at: u32,
    },
    Null,
    Present(Box<ConstAst>),
    View(TyAst, Vec<ConstAst>),
}

#[derive(Clone, Debug)]
pub(crate) struct AttrAst {
    pub name: String,
    pub arg: Option<String>,
    /// The strings after the first: `@requires("cmov", "sse2")`.
    pub more: Vec<String>,
    pub at: u32,
}

#[derive(Clone, Debug)]
pub(crate) struct GenParam {
    pub name: Symbol,
    pub bounds: Vec<TyAst>,
    pub at: u32,
    /// The interface or object type of an implicit parameter, which names it.
    pub implicit: Option<TyAst>,
}

#[derive(Clone, Debug)]
pub(crate) struct FieldAst {
    pub name: Symbol,
    pub vis: Option<enrang_hir::Vis>,
    pub readonly: bool,
    pub optional: bool,
    pub ty: TyAst,
    pub readonly_refs: Vec<Vec<u32>>,
    pub has_default: bool,
    pub is_override: bool,
    pub at: u32,
}

#[derive(Clone, Debug)]
pub(crate) enum CaseValue {
    Int(i128),
    Text(String),
}

#[derive(Clone, Debug)]
pub(crate) struct CaseAst {
    pub name: Symbol,
    pub fields: Vec<(Symbol, TyAst)>,
    pub value: Option<CaseValue>,
    pub at: u32,
}

#[derive(Clone, Debug)]
pub(crate) struct ParamAst {
    pub mark: Mark,
    pub local: u32,
    pub ty: TyAst,
    pub has_default: bool,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub(crate) enum ResultAst {
    None,
    Writable,
    ReadOnly(ReasonAst),
}

#[derive(Clone, Debug)]
pub(crate) enum ReasonAst {
    Simple(enrang_hir::Reason),
    /// 0 `constant`, 1 `static`, 2 `readonly_result`.
    Path(u8, PathAst),
    Field(PathAst, String),
}

#[derive(Clone, Debug, Default)]
pub(crate) struct ContractAst {
    pub perms: Option<Vec<enrang_hir::Perm>>,
    pub sources: Option<Vec<u32>>,
    pub through_fields: Vec<u32>,
    pub through_read: Vec<u32>,
    pub stores: Vec<enrang_hir::Store>,
    pub moves: Vec<bool>,
    pub result: Option<ResultAst>,
}

#[derive(Clone, Debug)]
pub(crate) struct FnAst {
    pub receiver: Option<enrang_hir::Receiver>,
    pub path: PathAst,
    pub generics: Vec<GenParam>,
    pub params: Vec<ParamAst>,
    pub ret: TyAst,
    pub ret_readonly: bool,
    /// `where T extends B`: bounds on the parent's parameters.
    pub wheres: Vec<GenParam>,
    pub contract: Option<ContractAst>,
    pub body: Option<(usize, usize)>,
}

#[derive(Clone, Debug)]
pub(crate) enum DeclKind {
    Class {
        path: PathAst,
        generics: Vec<GenParam>,
        base: Option<TyAst>,
        wtf: bool,
        fields: Vec<FieldAst>,
    },
    Enum {
        path: PathAst,
        generics: Vec<GenParam>,
        cases: Vec<CaseAst>,
    },
    Iface {
        path: PathAst,
        generics: Vec<GenParam>,
    },
    Fn(FnAst),
    Static {
        path: PathAst,
        ty: TyAst,
    },
    Const {
        path: PathAst,
        ty: TyAst,
        value: ConstAst,
    },
    Test {
        path: PathAst,
    },
    Extend {
        path: PathAst,
        generics: Vec<GenParam>,
        ty: TyAst,
    },
}

#[derive(Clone, Debug)]
pub(crate) struct DeclAst {
    pub attrs: Vec<AttrAst>,
    pub kind: DeclKind,
}

#[derive(Clone, Debug)]
pub(crate) enum ParentAst {
    Fn(PathAst),
    Const(PathAst),
    Test(PathAst),
    Statements,
}

#[derive(Clone, Debug)]
pub(crate) enum ShimAst {
    Ty(String, TyAst),
    /// `true`: `fn_as_closure`, `false`: `string_form`.
    Fn(bool, PathAst),
    Env(TyAst, TyAst),
}

#[derive(Clone, Debug)]
pub(crate) enum OwnerAst {
    Fn(PathAst),
    Statements,
    Test(PathAst),
    Arrow(ParentAst, u32),
    Shim(ShimAst),
}

#[derive(Clone, Debug)]
pub(crate) struct BodyAst {
    pub owner: OwnerAst,
    /// Empty for a function, whose declaration gives its parameters.
    pub params: Vec<ParamAst>,
    pub ret: Option<TyAst>,
    /// The `{ ... }` tokens.
    pub range: (usize, usize),
    pub start: usize,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct TopLevel {
    pub target: Option<String>,
    pub module: Option<String>,
    pub decls: Vec<DeclAst>,
    pub bodies: Vec<BodyAst>,
}

impl TopLevel {
    pub fn module_name(&self) -> &str {
        self.module.as_deref().unwrap_or(DEFAULT_MODULE)
    }
}

// ---------------------------------------------------------------------------------
// Bodies.

struct BodyParser<'a, 't> {
    p: Parser<'a>,
    tcx: &'t mut Tcx,
    names: &'t Names,
    scope: Scope,
    body: Body,
    end: usize,
    /// The locals the head declared: a `let` of one only names it.
    declared: u32,
}

impl<'a, 't> BodyParser<'a, 't> {
    fn new(
        toks: &'a [Token],
        base: BytePos,
        tcx: &'t mut Tcx,
        names: &'t Names,
        b: &BodyAst,
    ) -> PResult<BodyParser<'a, 't>> {
        let mut p = Parser::new(toks, base);
        p.pos = b.start;
        let (owner, scope, ret, args) = decls::body_head(tcx, names, b)?;
        p.pos = b.range.1;
        let span = p.span_from(b.start);
        let mut body = Body::new(owner, ret, span);
        for (ty, span) in &args {
            body.locals.push(LocalDecl::new(*ty, LocalKind::Arg, *span));
        }
        body.arg_count = args.len() as u32;
        p.pos = b.range.0 + 1;
        Ok(BodyParser {
            p,
            tcx,
            names,
            scope,
            declared: body.arg_count,
            body,
            end: b.range.1 - 1,
        })
    }

    fn body(&mut self) -> PResult<Body> {
        let mut blocks: BTreeMap<u32, Block> = BTreeMap::new();
        while self.p.pos < self.end {
            if self.p.is_numbered("bb") && self.p.is_at(1, ":") {
                let at = self.p.at();
                let n = self.p.numbered("bb")?;
                self.p.expect(":")?;
                let block = self.block()?;
                if blocks.insert(n, block).is_some() {
                    return err(at, format!("bb{n} is defined twice"));
                }
            } else if blocks.is_empty() {
                self.item()?;
            } else {
                return self.p.unexpected("a block");
            }
        }
        for (i, (&n, _)) in blocks.iter().enumerate() {
            if n as usize != i {
                return err(self.p.at(), format!("bb{i} is missing"));
            }
        }
        self.body.blocks = blocks.into_values().collect();
        let mut body = std::mem::replace(
            &mut self.body,
            Body::new(
                BodyOwner::Statements(enrang_hir::ModuleId(0)),
                self.tcx.common().void,
                Span::DUMMY,
            ),
        );
        canonicalize_projs(&mut body);
        body.names = BodyNames::collect(self.tcx, &body);
        Ok(body)
    }

    fn ty(&mut self) -> PResult<Ty> {
        let t = self.p.ty()?;
        decls::resolve_ty(self.tcx, self.names, &self.scope, &t)
    }

    fn local(&mut self) -> PResult<Local> {
        let at = self.p.at();
        let n = self.p.numbered("_")?;
        if n as usize >= self.body.locals.len() {
            return err(at, format!("_{n} is not declared"));
        }
        Ok(Local(n))
    }

    fn block_id(&mut self) -> PResult<BlockId> {
        Ok(BlockId(self.p.numbered("bb")?))
    }

    fn point(&mut self) -> PResult<Point> {
        let block = self.block_id()?;
        self.p.expect("[")?;
        let index = self.p.u32()?;
        self.p.expect("]")?;
        Ok(Point { block, index })
    }

    fn region(&mut self) -> PResult<RegionId> {
        Ok(RegionId(self.p.numbered("r")?))
    }

    fn fact_id(&mut self) -> PResult<FactId> {
        Ok(FactId(self.p.numbered("f")?))
    }

    /// One item before the blocks: a local, a region, a capture, a drop flag, a
    /// literal, the phase, or a line of `PhaseMeta`.
    fn item(&mut self) -> PResult<()> {
        let start = self.p.pos;
        let at = self.p.at();
        let word = self.p.ident()?;
        match word.as_str() {
            "phase" => {
                self.body.phase = self.p.word_in(PHASES, "phase", at)?;
            }
            "let" => {
                let mutable = self.p.eat_kw("mut");
                let lat = self.p.at();
                let n = self.p.numbered("_")?;
                self.p.expect(":")?;
                let ty = self.ty()?;
                let kind = if self.p.eat("#") {
                    let role = self.p.ident()?;
                    let Some(role) = named(LOOP_ROLES, &role) else {
                        return err(lat, format!("no loop role `#{role}`"));
                    };
                    Some(LocalKind::HiddenLoop(role))
                } else if let Tok::Ident(k) = self.p.peek().clone() {
                    let Some(kind) = named(LOCAL_KINDS, &k) else {
                        return err(self.p.at(), format!("no local kind `{k}`"));
                    };
                    self.p.bump();
                    Some(kind)
                } else {
                    None
                };
                let semi = self.p.pos;
                self.p.expect(";")?;
                let name = self.p.toks[semi].comment.as_deref().map(intern);
                let span = self.p.span_from(start);
                if n == 0 || n <= self.declared {
                    let decl = &mut self.body.locals[Local(n)];
                    // The head's type stands: an implicit parameter (D5) prints as
                    // the interface or object type it stands for, which the
                    // restatement here names (A:562).
                    if decl.ty != ty && self.tcx.ty_string(decl.ty) != self.tcx.ty_string(ty) {
                        return err(
                            lat,
                            format!("_{n} is declared with another type in the head"),
                        );
                    }
                    decl.mutable = mutable;
                    decl.name = name;
                    match kind {
                        None | Some(LocalKind::User | LocalKind::Arg) => {}
                        Some(LocalKind::ClosureEnv) if n > 0 => decl.kind = LocalKind::ClosureEnv,
                        Some(_) => return err(lat, format!("_{n} of the head keeps its kind")),
                    }
                    return Ok(());
                }
                if n as usize != self.body.locals.len() {
                    return err(lat, format!("_{n} is declared out of order"));
                }
                let kind = kind.unwrap_or(LocalKind::User);
                if kind == LocalKind::Arg {
                    if self.body.arg_count as usize + 1 != self.body.locals.len() {
                        return err(lat, "an argument after a local that is not one");
                    }
                    self.body.arg_count += 1;
                }
                self.body.locals.push(LocalDecl {
                    ty,
                    mutable,
                    name,
                    span,
                    kind,
                });
                return Ok(());
            }
            "region" => {
                let r = self.region()?;
                self.p.expect(":")?;
                let kind = self.p.word_in(REGION_KINDS, "region kind", at)?;
                let parent = if self.p.eat_kw("in") {
                    Some(self.region()?)
                } else {
                    None
                };
                if r.index() != self.body.unsafe_regions.len() {
                    return err(at, format!("{r} is declared out of order"));
                }
                self.p.expect(";")?;
                // A region's text is its declaration, not the code it covers, so a
                // parsed region has no span for V05 to compare.
                self.body.unsafe_regions.push(UnsafeRegion {
                    kind,
                    parent,
                    span: Span::DUMMY,
                });
                return Ok(());
            }
            "capture" => {
                let name = intern(&self.p.name()?);
                self.p.expect(":")?;
                let ty = self.ty()?;
                let kind = self.p.word_in(CAPTURES, "capture kind", at)?;
                self.p.expect(";")?;
                let span = self.p.span_from(start);
                self.body.captures.push(Capture {
                    name,
                    ty,
                    kind,
                    span,
                });
                return Ok(());
            }
            "drop_flag" => {
                let flag = self.local()?;
                self.p.expect(":")?;
                let pat = self.p.at();
                let (local, projs) = self.place_raw()?;
                let mut steps = Vec::new();
                let mut it = projs.iter();
                while let Some(p) = it.next() {
                    match (p, it.clone().next()) {
                        (Proj::Field(f), _) => steps.push(MoveStep::Field(*f)),
                        (Proj::Variant(v), Some(Proj::Field(f))) => {
                            steps.push(MoveStep::VariantField(*v, *f));
                            it.next();
                        }
                        _ => return err(pat, "a move path has only fields and case fields"),
                    }
                }
                self.body
                    .drop_flags
                    .push((flag, MovePathKey { local, steps }));
            }
            "literal" => {
                self.p.expect("#")?;
                let k = self.p.u32()?;
                if k as usize != self.body.literals.len() {
                    return err(at, format!("literal#{k} is declared out of order"));
                }
                self.p.expect(":")?;
                let ty = self.ty()?;
                self.p.expect("=")?;
                let c = self.p.const_ast()?;
                let value = decls::const_tree(self.tcx, self.names, &self.scope, &c, ty, None)?;
                self.body.literals.push(LiteralStatic { ty, value });
            }
            "loop" => {
                let id = LoopId(self.p.numbered("l")?);
                self.p.expect(":")?;
                let source = if self.p.eat_kw("path") {
                    LoopSource::Path(self.place()?)
                } else {
                    self.p.expect_kw("once")?;
                    LoopSource::Once(self.local()?)
                };
                self.p.expect_kw("preheader")?;
                let preheader = self.block_id()?;
                self.p.expect_kw("head")?;
                let head = self.block_id()?;
                self.p.expect_kw("bind")?;
                let bind = self.point()?;
                self.p.expect_kw("binding")?;
                let binding = self.local()?;
                self.p.expect(";")?;
                let span = self.p.span_from(start);
                self.body.meta.loops.push(ForOfLoop {
                    id,
                    preheader,
                    head,
                    bind,
                    source,
                    binding,
                    span,
                });
                return Ok(());
            }
            "fact" => {
                let f = self.fact_id()?;
                if f.index() != self.body.meta.facts.len() {
                    return err(at, format!("f{} is declared out of order", f.index()));
                }
                self.p.expect(":")?;
                let root = self.local()?;
                let mut pt = Some(PlaceTy::of(self.body.locals[root].ty));
                let mut steps = Vec::new();
                while self.p.eat(".") {
                    let sat = self.p.at();
                    if self.p.eat("*") {
                        steps.push(PathStep::Deref);
                        pt = pt.and_then(|t| t.project(self.tcx, Proj::Deref));
                    } else if self.p.eat("?") {
                        steps.push(PathStep::Payload);
                        pt = pt
                            .and_then(|t| t.project(self.tcx, Proj::Variant(VariantIdx::PRESENT)))
                            .and_then(|t| t.project(self.tcx, Proj::Field(FieldIdx(0))));
                    } else {
                        let name = self.p.name()?;
                        let f = self.field_of(pt, &name, sat)?;
                        steps.push(PathStep::Field(f));
                        pt = pt.and_then(|t| t.project(self.tcx, Proj::Field(f)));
                    }
                }
                let fact = if self.p.eat_kw("nonnull") {
                    Fact::NonNull
                } else {
                    self.p.expect_kw("case")?;
                    let cat = self.p.at();
                    let name = self.p.name()?;
                    Fact::Case(self.variant_of(pt.map(|t| t.ty), &name, cat)?)
                };
                self.p.expect(";")?;
                let span = self.p.span_from(start);
                self.body.meta.facts.push(MirFact {
                    root,
                    steps,
                    fact,
                    span,
                });
                return Ok(());
            }
            "record" => {
                let fact = self.fact_id()?;
                self.p.expect_kw("at")?;
                let at_point = self.point()?;
                let slot = self.local()?;
                let kind = self.p.word_in(RECORDS, "record kind", at)?;
                self.p.expect(";")?;
                let span = self.p.span_from(start);
                self.body.meta.records.push(MirRecord {
                    fact,
                    at: at_point,
                    slot,
                    kind,
                    span,
                });
                return Ok(());
            }
            "use" => {
                let f = self.fact_id()?;
                self.p.expect_kw("at")?;
                let pt = self.point()?;
                self.body.meta.narrowed_uses.push((f, pt));
            }
            "test" => {
                let f = self.fact_id()?;
                self.p.expect_kw("at")?;
                let bb = self.block_id()?;
                self.body.meta.fact_tests.push((f, bb));
            }
            "assign_value" => {
                let pt = self.point()?;
                self.body.meta.assign_values.push(pt);
            }
            "defaults" => {
                self.body.meta.defaults_count = Some(self.local()?);
            }
            other => return err(at, format!("expected a body item, found `{other}`")),
        }
        self.p.expect(";")
    }

    fn field_of(&self, pt: Option<PlaceTy>, name: &str, at: u32) -> PResult<FieldIdx> {
        if let Ok(n) = name.parse::<u32>() {
            return Ok(FieldIdx(n));
        }
        match pt.and_then(|t| t.field_named(self.tcx, intern(name))) {
            Some(f) => Ok(f),
            None => err(at, format!("no field `{name}` here")),
        }
    }

    fn variant_of(&self, ty: Option<Ty>, name: &str, at: u32) -> PResult<VariantIdx> {
        if let Ok(n) = name.parse::<u32>() {
            return Ok(VariantIdx(n));
        }
        match ty.and_then(|t| variant_named(self.tcx, t, intern(name))) {
            Some(v) => Ok(v),
            None => err(at, format!("no case `{name}` here")),
        }
    }

    // -----------------------------------------------------------------------------
    // Places, operands, rvalues.

    fn place_ty(&self, local: Local, projs: &[Proj]) -> Option<PlaceTy> {
        let mut pt = PlaceTy::of(self.body.locals[local].ty);
        for &p in projs {
            pt = pt.project(self.tcx, p)?;
        }
        Some(pt)
    }

    fn place_raw(&mut self) -> PResult<(Local, Vec<Proj>)> {
        if self.p.eat("*") {
            let (l, mut projs) = self.place_raw()?;
            projs.push(Proj::Deref);
            return Ok((l, projs));
        }
        let (local, mut projs) = if self.p.eat("(") {
            let (l, mut projs) = self.place_raw()?;
            if self.p.eat_kw("as") {
                let at = self.p.at();
                let name = self.p.name()?;
                let ty = self.place_ty(l, &projs).map(|t| t.ty);
                projs.push(Proj::Variant(self.variant_of(ty, &name, at)?));
            }
            self.p.expect(")")?;
            (l, projs)
        } else {
            (self.local()?, Vec::new())
        };
        loop {
            if self.p.is(".") && !matches!(self.p.peek_at(1), Tok::Punct(_)) {
                self.p.bump();
                let at = self.p.at();
                let name = self.p.name()?;
                let pt = self.place_ty(local, &projs);
                projs.push(Proj::Field(self.field_of(pt, &name, at)?));
            } else if self.p.is("[") && self.p.is_at(2, "]") {
                match self.p.peek_at(1).clone() {
                    Tok::Int(n) => {
                        self.p.bump();
                        self.p.bump();
                        self.p.bump();
                        projs.push(Proj::ConstIndex(n as u64));
                    }
                    Tok::Ident(s)
                        if s.starts_with('_')
                            && s[1..].bytes().all(|b| b.is_ascii_digit())
                            && s.len() > 1 =>
                    {
                        self.p.bump();
                        let l = self.local()?;
                        self.p.bump();
                        projs.push(Proj::Index(l));
                    }
                    _ => break,
                }
            } else {
                break;
            }
        }
        Ok((local, projs))
    }

    fn place(&mut self) -> PResult<Place> {
        let (local, projs) = self.place_raw()?;
        Ok(self.body.place(local, &projs))
    }

    fn operand(&mut self) -> PResult<Operand> {
        if self.p.eat_kw("copy") {
            return Ok(Operand::Copy(self.place()?));
        }
        if self.p.eat_kw("move") {
            return Ok(Operand::Move(self.place()?));
        }
        self.p.expect_kw("const")?;
        if self.p.is_kw("static_addr")
            && self.p.is_at(1, "(")
            && matches!(self.p.peek_at(2), Tok::Ident(s) if s == "literal")
        {
            self.p.bump();
            self.p.bump();
            self.p.bump();
            self.p.expect("#")?;
            let k = self.p.u32()?;
            self.p.expect(")")?;
            self.p.expect(":")?;
            let ty = self.ty()?;
            return Ok(Operand::Const(Box::new(Constant {
                kind: ConstKind::LiteralAddr(k),
                ty,
            })));
        }
        let c = self.p.const_ast()?;
        self.p.expect(":")?;
        let ty = self.ty()?;
        let ctor = crate::print::ctor_class(self.tcx, &self.body);
        let value = decls::const_value(self.tcx, self.names, &self.scope, &c, ty, ctor)?;
        Ok(Operand::constant(value, ty))
    }

    fn operands(&mut self, close: &str) -> PResult<Vec<Operand>> {
        let mut out = Vec::new();
        while !self.p.is(close) {
            out.push(self.operand()?);
            if !self.p.eat(",") {
                break;
            }
        }
        self.p.expect(close)?;
        Ok(out)
    }

    /// `name: op, ... }` in the field order of `pt`, every field once.
    fn fields(&mut self, pt: PlaceTy, count: usize, at: u32) -> PResult<Vec<Operand>> {
        let mut got: BTreeMap<u32, Operand> = BTreeMap::new();
        while !self.p.is("}") {
            let fat = self.p.at();
            let name = self.p.name()?;
            let f = self.field_of(Some(pt), &name, fat)?;
            self.p.expect(":")?;
            let op = self.operand()?;
            if got.insert(f.0, op).is_some() {
                return err(fat, format!("field `{name}` is given twice"));
            }
            if !self.p.eat(",") {
                break;
            }
        }
        self.p.expect("}")?;
        if got.len() != count || got.keys().enumerate().any(|(i, &k)| i as u32 != k) {
            return err(
                at,
                format!("{count} fields are needed, {} given", got.len()),
            );
        }
        Ok(got.into_values().collect())
    }

    fn rvalue(&mut self) -> PResult<Rvalue> {
        let at = self.p.at();
        if self.p.is_kw("copy") || self.p.is_kw("move") || self.p.is_kw("const") {
            return Ok(Rvalue::Use(self.operand()?));
        }
        if self.p.eat("&") {
            let place = self.place()?;
            self.p.expect("[")?;
            let mut words = vec![self.p.ident()?];
            while self.p.eat("-") {
                words.push(self.p.ident()?);
            }
            let word = words.join("-");
            let Some(origin) = named(ORIGINS, &word) else {
                return err(at, format!("no borrow origin `{word}`"));
            };
            self.p.expect("]")?;
            return Ok(Rvalue::Ref { place, origin });
        }
        let Tok::Ident(word) = self.p.peek().clone() else {
            return self.p.unexpected("an rvalue");
        };
        if self.p.is_at(1, "(")
            && let Some(rv) = self.paren_rvalue(&word)?
        {
            return Ok(rv);
        }
        if self.p.eat_kw("addr_of") {
            return Ok(Rvalue::AddrOf(self.place()?));
        }
        if self.p.eat_kw("null") {
            return Ok(Rvalue::Aggregate(AggregateKind::Null, Vec::new()));
        }
        if self.p.eat_kw_then("arrow_fn", "#") {
            return Ok(Rvalue::ArrowFn(ArrowId(self.p.u32()?)));
        }
        if self.p.eat_kw_then("fixed", "<") {
            let elem = self.ty()?;
            self.p.expect(">")?;
            self.p.expect("[")?;
            let ops = self.operands("]")?;
            return Ok(Rvalue::Aggregate(AggregateKind::Fixed(elem), ops));
        }
        match word.as_str() {
            "object" if !self.p.is_at(1, "{") || matches!(self.p.peek_at(2), Tok::Ident(_)) => {
                self.p.bump();
                let tat = self.p.at();
                let ty = self.ty()?;
                let TyKind::Object(shape) = self.tcx.kind(ty) else {
                    return err(tat, "`object` needs an object type");
                };
                self.p.expect("{")?;
                let n = self.tcx.shape(shape).fields.len();
                let ops = self.fields(PlaceTy::of(ty), n, at)?;
                return Ok(Rvalue::Aggregate(AggregateKind::Object(shape), ops));
            }
            _ => {}
        }
        let tat = self.p.at();
        let ty = self.ty()?;
        let TyKind::Adt(adt, args) = self.tcx.kind(ty) else {
            return err(tat, "expected an rvalue");
        };
        let variant = if self.p.eat("::") {
            let cat = self.p.at();
            let name = self.p.name()?;
            Some(self.variant_of(Some(ty), &name, cat)?)
        } else {
            None
        };
        self.p.expect("{")?;
        let pt = PlaceTy { ty, variant };
        let count = match (variant, &self.tcx.adt(adt).kind) {
            (None, enrang_hir::AdtKind::Class(c)) => c.fields.len(),
            (Some(v), enrang_hir::AdtKind::Enum(e)) => e.variants[v.index()].fields.len(),
            _ => return err(tat, "an aggregate builds a class or an enum case"),
        };
        let ops = self.fields(pt, count, at)?;
        Ok(Rvalue::Aggregate(
            AggregateKind::Adt { adt, variant, args },
            ops,
        ))
    }

    /// `word(..)`, the cursor on `word`, when it names a form in parentheses.
    fn paren_rvalue(&mut self, w: &str) -> PResult<Option<Rvalue>> {
        use AggregateKind as A;
        let checked = w.strip_prefix("checked_").and_then(|n| named(CHECKED, n));
        let (binary, unary) = (named(BINOPS, w), named(UNOPS, w));
        let forms = [
            "checked_neg",
            "cast",
            "convert",
            "repeat",
            "tuple",
            "present",
            "env",
            "discriminant",
            "len",
            "closure",
            "closure_reborrow",
        ];
        if binary.is_none() && checked.is_none() && unary.is_none() && !forms.contains(&w) {
            return Ok(None);
        }
        self.p.bump();
        self.p.bump();
        let rv = match w {
            _ if binary.is_some() || checked.is_some() => {
                let a = self.operand()?;
                self.p.expect(",")?;
                let b = self.operand()?;
                match (binary, checked) {
                    (Some(op), _) => Rvalue::Binary(op, a, b),
                    (_, op) => Rvalue::Checked(op.expect("a checked operator"), a, b),
                }
            }
            "tuple" => return Ok(Some(Rvalue::Aggregate(A::Tuple, self.operands(")")?))),
            "env" => return Ok(Some(Rvalue::Aggregate(A::ClosureEnv, self.operands(")")?))),
            "checked_neg" => Rvalue::CheckedNeg(self.operand()?),
            "present" => Rvalue::Aggregate(A::Present, vec![self.operand()?]),
            "discriminant" => Rvalue::Discriminant(self.place()?),
            "len" => Rvalue::Len(self.place()?),
            "closure_reborrow" => Rvalue::ClosureReborrow(self.place()?),
            "cast" | "convert" => {
                let kat = self.p.at();
                let k = self.p.ident()?;
                let (cast, conv) = (named(CASTS, &k), named(CONVS, &k));
                match (w, cast, conv) {
                    ("cast", None, _) => return err(kat, format!("no cast `{k}`")),
                    ("convert", _, None) => return err(kat, format!("no conversion `{k}`")),
                    _ => {}
                }
                self.p.expect(",")?;
                let op = self.operand()?;
                match (cast, conv) {
                    (Some(kind), _) if w == "cast" => {
                        self.p.expect(",")?;
                        Rvalue::Cast(kind, op, self.ty()?)
                    }
                    (_, kind) => Rvalue::Convert(kind.expect("a conversion"), op),
                }
            }
            "repeat" => {
                let op = self.operand()?;
                self.p.expect(";")?;
                let n = self.p.int()? as u64;
                Rvalue::Aggregate(A::Repeat(n), vec![op])
            }
            "closure" => {
                let func = if self.p.eat_kw("arrow") {
                    self.p.expect("#")?;
                    ClosureFn::Arrow(ArrowId(self.p.u32()?))
                } else if self.p.eat_kw("fn_value") {
                    ClosureFn::FnValue
                } else {
                    self.p.expect_kw("fn")?;
                    let path = self.p.path()?;
                    ClosureFn::Named(decls::fn_ref(self.tcx, self.names, &self.scope, &path)?)
                };
                self.p.expect(",")?;
                let env = self.place()?;
                Rvalue::ClosureValue { func, env }
            }
            _ => Rvalue::Unary(unary.expect("a unary operator"), self.operand()?),
        };
        self.close(Some(rv))
    }

    // -----------------------------------------------------------------------------
    // Statements and terminators.

    /// Whether the item at the cursor, up to its `;`, is a terminator.
    fn at_terminator(&self) -> bool {
        if ["goto", "switch", "return", "unreachable"]
            .iter()
            .any(|k| self.p.is_kw(k))
        {
            return true;
        }
        let mut depth = 0i32;
        let mut i = self.p.pos;
        loop {
            match &self.p.toks[i].tok {
                Tok::Punct("(" | "[" | "{") => depth += 1,
                Tok::Punct(")" | "]" | "}") => {
                    depth -= 1;
                    if depth < 0 {
                        return false;
                    }
                }
                Tok::Punct(";") if depth == 0 => return false,
                Tok::Punct("->") if depth == 0 => return true,
                Tok::Eof => return false,
                _ => {}
            }
            i += 1;
        }
    }

    fn block(&mut self) -> PResult<Block> {
        self.p.expect("{")?;
        let mut stmts = Vec::new();
        loop {
            let start = self.p.pos;
            if self.at_terminator() {
                let kind = self.terminator()?;
                let region = self.region_suffix()?;
                let span = self.p.span_from(start);
                self.p.expect(";")?;
                self.p.expect("}")?;
                return Ok(Block {
                    stmts,
                    term: Terminator { kind, span, region },
                });
            }
            if self.p.is("}") {
                return self.p.unexpected("a terminator");
            }
            let kind = self.statement()?;
            let region = self.region_suffix()?;
            let span = self.p.span_from(start);
            self.p.expect(";")?;
            stmts.push(Statement { kind, span, region });
        }
    }

    fn region_suffix(&mut self) -> PResult<Option<RegionId>> {
        if self.p.eat("@") {
            Ok(Some(self.region()?))
        } else {
            Ok(None)
        }
    }

    fn statement(&mut self) -> PResult<StatementKind> {
        use StatementKind as S;
        if self.p.eat_kw_then("check_bounds", "(") {
            let index = self.operand()?;
            self.p.expect(",")?;
            let len = self.operand()?;
            return self.close(S::CheckBounds { index, len });
        }
        if self.p.eat_kw_then("check_tag", "(") {
            let place = self.place()?;
            self.p.expect(",")?;
            let vat = self.p.at();
            let name = self.p.name()?;
            let ty = self.body.place_ty(self.tcx, place).map(|t| t.ty);
            let variant = self.variant_of(ty, &name, vat)?;
            return self.close(S::CheckTag { place, variant });
        }
        if self.p.eat_kw_then("check_class", "(") {
            let place = self.place()?;
            self.p.expect(",")?;
            let oat = self.p.at();
            let word = self.p.ident()?;
            let op = match named(CLASS_OPS, &word) {
                Some(op) => op,
                None if word == "move_this" => {
                    self.p.expect("(")?;
                    let name = intern(&self.p.ident()?);
                    self.p.expect(")")?;
                    ClassOp::MoveThis(name)
                }
                None => return err(oat, format!("no class event `{word}`")),
            };
            self.p.expect(",")?;
            let via = match self.p.peek() {
                Tok::Ident(w) => named(HOLDERS, w),
                _ => None,
            };
            let Some(via) = via else {
                return self.p.unexpected("`ref`");
            };
            self.p.bump();
            return self.close(S::CheckClass { place, op, via });
        }
        if self.p.eat_kw_then("set_table", "(") {
            let place = self.place()?;
            self.p.expect(",")?;
            let class = self.ty()?;
            return self.close(S::SetTable { place, class });
        }
        if self.p.eat_kw_then("field_init", "(") {
            let field = self.place()?;
            self.p.expect(",")?;
            let value = self.operand()?;
            return self.close(S::FieldInit { field, value });
        }
        for (word, make) in [
            ("storage_live", S::StorageLive as fn(Local) -> S),
            ("storage_dead", S::StorageDead),
        ] {
            if self.p.eat_kw_then(word, "(") {
                let l = self.local()?;
                return self.close(make(l));
            }
        }
        if self.p.eat_kw_then("drop", "(") {
            let place = self.place()?;
            self.p.expect(")")?;
            if self.p.eat("[") {
                self.p.expect_kw("assign")?;
                self.p.expect("]")?;
                return Ok(S::Drop(place, DropOrigin::Assign));
            }
            return Ok(S::Drop(place, DropOrigin::Scope));
        }
        if self.p.eat_kw_then("drop_glue", "(") {
            let place = self.place()?;
            return self.close(S::DropGlue(place));
        }
        if self.p.eat_kw_then("asm", "(") {
            let template = intern(&self.p.string()?);
            let mut asm = AsmStmt {
                template,
                ins: Vec::new(),
                outs: Vec::new(),
                clobbers: Vec::new(),
            };
            while self.p.eat(",") {
                if self.p.eat_kw("clobber") {
                    asm.clobbers.push(intern(&self.p.string()?));
                    continue;
                }
                let name = intern(&self.p.ident()?);
                if self.p.eat_kw("in") {
                    asm.ins.push((name, self.operand()?));
                } else {
                    self.p.expect_kw("out")?;
                    let place = match self.p.is(",") || self.p.is(")") {
                        true => None,
                        false => Some(self.place()?),
                    };
                    asm.outs.push((name, place));
                }
            }
            return self.close(S::Asm(Box::new(asm)));
        }
        if self.p.eat_kw("nop") {
            return Ok(S::Nop);
        }
        if self.p.is_kw("intrinsic") || self.p.is_kw("host_call") {
            return self.call_statement(None);
        }
        let dest = self.place()?;
        self.p.expect("=")?;
        if (self.p.is_kw("intrinsic") && matches!(self.p.peek_at(1), Tok::Ident(_)))
            || (self.p.is_kw("host_call") && matches!(self.p.peek_at(1), Tok::Str(_)))
        {
            return self.call_statement(Some(dest));
        }
        let value = self.rvalue()?;
        Ok(S::Assign { dest, value })
    }

    /// `)`, then `v`.
    fn close<T>(&mut self, v: T) -> PResult<T> {
        self.p.expect(")")?;
        Ok(v)
    }

    /// `intrinsic Kind<payload>(ops)` or `host_call "name"(ops)`.
    fn call_statement(&mut self, dest: Option<Place>) -> PResult<StatementKind> {
        if self.p.eat_kw("host_call") {
            let name = intern(&self.p.string()?);
            let id = self.tcx.intern_host_call(name);
            self.p.expect("(")?;
            let args = self.operands(")")?;
            return Ok(StatementKind::HostCall { id, args, dest });
        }
        self.p.expect_kw("intrinsic")?;
        let at = self.p.at();
        let word = self.p.ident()?;
        let Some(name) = IntrinsicName::from_name(&word) else {
            return err(at, format!("no intrinsic `{word}`"));
        };
        let kind = self.intrinsic_kind(name, at)?;
        self.p.expect("(")?;
        let args = self.operands(")")?;
        Ok(StatementKind::Intrinsic { kind, args, dest })
    }

    /// A kind of `name`: a payload-free one, or `<payload>` read.
    fn intrinsic_kind(&mut self, name: IntrinsicName, at: u32) -> PResult<IntrinsicKind> {
        use IntrinsicKind as K;
        use IntrinsicName as N;
        if let Some(&k) = PLAIN_INTRINSICS.iter().find(|k| k.name() == name) {
            return Ok(k);
        }
        self.p.expect("<")?;
        let kind = match name {
            N::AtomicAlu => {
                let op = self.p.word_in(ALU_OPS, "atomic operation", at)?;
                K::AtomicAlu(op)
            }
            N::AtomicIncDecTest | N::AtomicBitTest => {
                let b = match self.p.ident()?.as_str() {
                    "true" => true,
                    "false" => false,
                    _ => return err(at, "expected `true` or `false`"),
                };
                match name {
                    N::AtomicIncDecTest => K::AtomicIncDecTest(b),
                    _ => K::AtomicBitTest(b),
                }
            }
            N::CpuHas => {
                let f = self.p.string()?;
                match K::cpu_has_named(&f) {
                    Some(k) => k,
                    None => return err(at, format!("no feature `{f}`")),
                }
            }
            N::OffsetOf => {
                let t = self.ty()?;
                self.p.expect(",")?;
                let fat = self.p.at();
                let fname = self.p.name()?;
                K::OffsetOf(t, self.field_of(Some(PlaceTy::of(t)), &fname, fat)?)
            }
            _ => {
                let make: fn(Ty) -> IntrinsicKind = match name {
                    N::SizeOf => K::SizeOf,
                    N::AlignOf => K::AlignOf,
                    N::AllocArray => K::AllocArray,
                    _ => K::SliceFromRaw,
                };
                make(self.ty()?)
            }
        };
        self.p.expect(">")?;
        Ok(kind)
    }

    fn terminator(&mut self) -> PResult<TerminatorKind> {
        if self.p.eat_kw("goto") {
            return Ok(TerminatorKind::Goto(self.block_id()?));
        }
        if self.p.eat_kw("return") {
            return Ok(TerminatorKind::Return);
        }
        if self.p.eat_kw("unreachable") {
            return Ok(TerminatorKind::Unreachable);
        }
        if self.p.eat_kw("switch") {
            let value = self.operand()?;
            self.p.expect("[")?;
            let mut arms = Vec::new();
            let mut otherwise = None;
            while !self.p.is("]") {
                if self.p.eat_kw("otherwise") {
                    self.p.expect(":")?;
                    otherwise = Some(self.block_id()?);
                } else {
                    let v = self.p.int()?;
                    self.p.expect(":")?;
                    arms.push((v, self.block_id()?));
                }
                if !self.p.eat(",") {
                    break;
                }
            }
            self.p.expect("]")?;
            return Ok(TerminatorKind::Switch {
                value,
                arms,
                otherwise,
            });
        }
        let dest = self.place()?;
        self.p.expect("=")?;
        let callee = self.callee()?;
        self.p.expect("(")?;
        let args = self.operands(")")?;
        self.p.expect("->")?;
        let next = if self.p.eat("!") {
            None
        } else {
            Some(self.block_id()?)
        };
        Ok(TerminatorKind::Call {
            callee,
            args,
            dest,
            next,
        })
    }

    fn callee(&mut self) -> PResult<Callee> {
        if self.p.eat_kw_then("fnptr", "(") {
            let op = self.operand()?;
            return self.close(Callee::FnPtr(op));
        }
        if self.p.is_kw("closure")
            && matches!(self.p.peek_at(1), Tok::Ident(s) if s.starts_with('_'))
        {
            self.p.bump();
            return Ok(Callee::ClosureLocal(self.local()?));
        }
        if self.p.eat_kw("foreign") {
            let path = self.p.path()?;
            let f = decls::fn_ref(self.tcx, self.names, &self.scope, &path)?;
            let abi = self.tcx.sig(f.def).abi;
            return Ok(Callee::Foreign(ForeignRef { def: f.def, abi }));
        }
        if self.p.eat_kw("virtual") {
            let path = self.p.path()?;
            let method = decls::fn_ref(self.tcx, self.names, &self.scope, &path)?;
            self.p.expect("[")?;
            let table = self.operand()?;
            self.p.expect("]")?;
            return Ok(Callee::Virtual { method, table });
        }
        if self.p.eat_kw("form") {
            let fat = self.p.at();
            let word = self.p.ident()?;
            if word == "expect" {
                let negated = self.p.eat_kw("not");
                let matcher = intern(&self.p.ident()?);
                return Ok(Callee::Form(FormCall::Expect { matcher, negated }));
            }
            let Some(form) = named(FORMS, &word) else {
                return err(fat, format!("no form `{word}`"));
            };
            if !self.p.eat("[") {
                return Ok(Callee::Form(form));
            }
            let mut parts = Vec::new();
            while !self.p.is("]") {
                let at = self.p.at();
                match u32::try_from(self.p.int()?) {
                    Ok(n) => parts.push(n),
                    Err(_) => return err(at, "a part count past `u32`".to_owned()),
                }
                if !self.p.eat(",") {
                    break;
                }
            }
            self.p.expect("]")?;
            return Ok(Callee::FormParts { form, parts });
        }
        if self.p.eat_kw("named_fill") {
            let class = self.ty()?;
            self.p.expect_kw("leaving")?;
            self.p.expect("(")?;
            let mut left_out = Vec::new();
            while !self.p.is(")") {
                let fat = self.p.at();
                let name = self.p.name()?;
                left_out.push(self.field_of(Some(PlaceTy::of(class)), &name, fat)?);
                if !self.p.eat(",") {
                    break;
                }
            }
            self.p.expect(")")?;
            return Ok(Callee::NamedFill { class, left_out });
        }
        if self.p.eat_kw("implicit_ctor") {
            return Ok(Callee::ImplicitCtor { class: self.ty()? });
        }
        let path = self.p.path()?;
        Ok(Callee::Fn(decls::fn_ref(
            self.tcx,
            self.names,
            &self.scope,
            &path,
        )?))
    }
}

/// `[IntrinsicKind::A, ..]` of payload-free kind names, out of rustfmt's reach.
macro_rules! kinds {
    ($($k:ident)*) => { [$(IntrinsicKind::$k),*] };
}

/// The intrinsic kinds a call decides nothing for.
const PLAIN_INTRINSICS: [IntrinsicKind; 17] = kinds! { VolatileRead VolatileWrite ReadUnaligned
WriteUnaligned MemCopy MemCopyOverlap MemSet AtomicLoad AtomicStore AtomicExchange AtomicFence
AtomicCompareExchange AtomicFetchAdd MulWideU32 DivWideU32 ToBitsCanon FromBits };

/// The shim of a parsed `shim` head.
pub(crate) fn shim_of(word: &str, t: Ty) -> ShimKind {
    let make = TY_SHIMS
        .iter()
        .find(|s| s.1 == word)
        .map_or(ShimKind::NamedFill as fn(Ty) -> ShimKind, |s| s.0);
    make(t)
}

/// The text of a `ConstValue` an operand of type `ty` may hold, from its syntax.
pub(crate) fn scalar(tcx: &Tcx, c: &ConstAst, ty: Ty) -> Option<ConstValue> {
    Some(match *c {
        ConstAst::Int(n, _) => match tcx.kind(ty) {
            TyKind::Int(int) => {
                let width = int.bits(u32::from(tcx.target().layout.ptr_bytes) * 8);
                let mask = if width == 128 {
                    u128::MAX
                } else {
                    (1u128 << width) - 1
                };
                ConstValue::Int((n as u128) & mask, ty)
            }
            TyKind::Float(_) => return float(tcx, n as f64, ty),
            _ => return None,
        },
        ConstAst::Float(f) => return float(tcx, f, ty),
        ConstAst::Nan(bits) => ConstValue::Float(bits, ty),
        ConstAst::Bool(b) => ConstValue::Bool(b),
        ConstAst::Void => ConstValue::Void,
        ConstAst::Str(ref s) => ConstValue::Str(tcx.intern_str(s)),
        _ => return None,
    })
}

fn float(tcx: &Tcx, f: f64, ty: Ty) -> Option<ConstValue> {
    match tcx.kind(ty) {
        TyKind::Float(enrang_hir::FloatTy::F32) => {
            Some(ConstValue::Float(u64::from((f as f32).to_bits()), ty))
        }
        TyKind::Float(enrang_hir::FloatTy::F64) => Some(ConstValue::Float(f.to_bits(), ty)),
        _ => None,
    }
}
