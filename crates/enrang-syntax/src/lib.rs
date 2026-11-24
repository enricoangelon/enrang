//! Tokens, lexer, syntax tree, parser with recovery, the syntax-level TypeScript
//! and deferred-feature hints, and the tree printer, which is both `enrang fmt` and
//! the parser's oracle (ARCHITECTURE 1, 2.3, 3 and 4).
//!
//! The pipeline of one file: [`decode_source`] turns the bytes read from disk into
//! text and the places of invalid UTF-8 (EN0001), [`lex`] turns the text into
//! [`Token`]s, [`parse_file`] builds an [`ast::File`], and [`print_file`] writes a tree
//! back in the canonical style of SPEC 12.5, with the comments of its source.
//! Everything reports to a [`DiagCtx`]; nothing here reads a clock, the file system
//! or a hash order.
//!
//! `scratchpad/m1/plan.md` of the M1 work maps each SPEC 3 production to its parser
//! function and each syntax code to the module that reports it.

#![forbid(unsafe_code)]

pub mod ast;
mod lexer;
mod parser;
mod printer;
pub mod token;
mod walk;

use enrang_base::SourceFile;
use enrang_diag::{Code, DiagCtx, Diagnostic};

pub use ast::{NodeId, NodeIdGen};
pub use token::{Contextual, Keyword, Punct, Reserved, Token, TokenKind};
pub use walk::{MutVisitor, Walk, erase};

/// Which parts of a module a command loads (ARCHITECTURE 3). The loader decides
/// which files to parse; a file parses the same way in either mode, and a test item
/// outside a `.test.en` file is EN1112 in both.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum ParseMode {
    /// Loads no `.test.en` part, so a module builds byte-identical with or without
    /// its tests.
    Build,
    /// Used by `check` and `test`: loads `.test.en` parts.
    Test,
}

/// The tokens of `file`, ending with one `TokenKind::Eof`. Lexical errors (EN0002 to
/// EN0008) go to `dcx`, and lexing goes on past each. A U+FFFD outside a literal or
/// comment where [`report_invalid_utf8`] already put an EN0001 is skipped quietly, so
/// a file that was not UTF-8 gets one EN0001 for each place; any other U+FFFD there
/// is EN0008, an unexpected character.
pub fn lex(file: &SourceFile, dcx: &mut DiagCtx) -> Vec<Token> {
    lexer::lex(file, dcx)
}

/// The tree of `file`. Every syntax error goes to `dcx` with recovery, so one run
/// reports all of them (SPEC 13.1); the tree is complete even then, with `Error`
/// nodes where nothing could be built.
pub fn parse_file(
    file: &SourceFile,
    ids: &mut NodeIdGen,
    mode: ParseMode,
    dcx: &mut DiagCtx,
) -> ast::File {
    parser::parse_file(file, ids, mode, parser::Placement::of(file), dcx)
}

/// [`parse_file`] for a source that is no file, such as what `enrang fmt` reads
/// from standard input. Its name names no module, so nothing says whether it is a
/// module's own file or its `.test.en` part, and it takes what either takes: a test
/// item is no EN1112, and a lifecycle hook at the top level is the call it is in a
/// module's own file, not EN1105. No layout depends on where a file sits.
pub fn parse_input(
    file: &SourceFile,
    ids: &mut NodeIdGen,
    mode: ParseMode,
    dcx: &mut DiagCtx,
) -> ast::File {
    parser::parse_file(file, ids, mode, parser::Placement::Unknown, dcx)
}

/// `enrang fmt`: `file` in the canonical style of SPEC 12.5, with every comment of
/// `source`, the text it was parsed from.
pub fn print_file(source: &SourceFile, file: &ast::File) -> String {
    printer::print_file(source, file)
}

/// Source bytes as text. Each maximal invalid UTF-8 sequence becomes one U+FFFD, and
/// `invalid` holds the byte offset of each in `text`, ascending.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Decoded {
    pub text: String,
    pub invalid: Vec<u32>,
}

/// SPEC 2: input is UTF-8, and invalid UTF-8 is EN0001. The driver decodes what it
/// reads with this, adds `text` to the source map, and passes `invalid` to
/// [`report_invalid_utf8`].
pub fn decode_source(bytes: &[u8]) -> Decoded {
    let mut text = String::with_capacity(bytes.len());
    let mut invalid = Vec::new();
    for chunk in bytes.utf8_chunks() {
        text.push_str(chunk.valid());
        if !chunk.invalid().is_empty() {
            invalid.push(u32::try_from(text.len()).expect("source fits in u32"));
            text.push(char::REPLACEMENT_CHARACTER);
        }
    }
    Decoded { text, invalid }
}

/// EN0001 at each offset `decode_source` reported, in `file`, which holds its text.
/// Called before [`lex`] or [`parse_file`] with the same `dcx`, it is how the lexer
/// tells a U+FFFD that stands for bad bytes from one typed in the source.
pub fn report_invalid_utf8(file: &SourceFile, invalid: &[u32], dcx: &mut DiagCtx) {
    let width = char::REPLACEMENT_CHARACTER.len_utf8() as u32;
    for &offset in invalid {
        let lo = file.start + offset;
        let span = enrang_base::Span { lo, hi: lo + width };
        dcx.emit(Diagnostic::new(
            Code::EN0001,
            "source is not valid UTF-8",
            span,
            "these bytes are not UTF-8",
        ));
    }
}
