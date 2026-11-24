//! The crate's entry points (ARCHITECTURE 3): what each promises whatever the stage
//! of the lexer, parser and printer behind it, and EN0001's decoding.

use enrang_base::Span;
use enrang_diag::{Code, DiagCtx};
use enrang_syntax::{
    NodeIdGen, ParseMode, TokenKind, decode_source, lex, parse_file, print_file,
    report_invalid_utf8,
};
use enrang_testkit::Harness;

use crate::support::source;

pub fn register(h: &mut Harness) {
    let decode_rows: &[(&str, &[u8], &str, &[u32])] = &[
        ("empty", b"", "", &[]),
        ("valid", "let é = 1;\n".as_bytes(), "let é = 1;\n", &[]),
        ("one bad byte", b"a\xFFb", "a\u{FFFD}b", &[1]),
        ("two bad bytes", b"\xFF\xFE", "\u{FFFD}\u{FFFD}", &[0, 3]),
        ("a cut sequence", b"x\xF0\x9F", "x\u{FFFD}", &[1]),
        ("a cut sequence then text", b"\xE2\x82z", "\u{FFFD}z", &[0]),
        (
            "a surrogate",
            b"\xED\xA0\x80.",
            "\u{FFFD}\u{FFFD}\u{FFFD}.",
            &[0, 3, 6],
        ),
    ];
    for &(name, bytes, text, invalid) in decode_rows {
        h.case(format!("api/decode_source: {name}"), move || {
            let decoded = decode_source(bytes);
            assert_eq!(decoded.text, text);
            assert_eq!(decoded.invalid, invalid);
        });
    }
    h.case("api/EN0001 at each invalid sequence", || {
        let decoded = decode_source(b"ok\xFF\nno\xC0\n");
        let file = source("bad.en", &decoded.text);
        let mut dcx = DiagCtx::new();
        report_invalid_utf8(&file, &decoded.invalid, &mut dcx);
        let diags = dcx.take();
        assert_eq!(diags.len(), 2);
        for (diag, &offset) in diags.iter().zip(&decoded.invalid) {
            assert_eq!(diag.code, Code::EN0001);
            let lo = file.start + offset;
            assert_eq!(diag.primary.span, Span { lo, hi: lo + 3 });
        }
        assert!(dcx.has_errors());
    });
    h.case("api/lexing ends with one end-of-file token", || {
        for text in ["", "const x = 1;\n"] {
            let file = source("a.en", text);
            let tokens = lex(&file, &mut DiagCtx::new());
            let last = tokens.last().expect("a token");
            assert_eq!(last.kind, TokenKind::Eof);
            assert_eq!(
                last.span,
                Span {
                    lo: file.end(),
                    hi: file.end()
                }
            );
            let ends = tokens.iter().filter(|t| t.kind == TokenKind::Eof).count();
            assert_eq!(ends, 1);
        }
    });
    h.case("api/a parsed file spans its source", || {
        for mode in [ParseMode::Build, ParseMode::Test] {
            let file = source("a.en", "");
            let tree = parse_file(&file, &mut NodeIdGen::new(), mode, &mut DiagCtx::new());
            assert_eq!(
                tree.span,
                Span {
                    lo: file.start,
                    hi: file.end()
                }
            );
            assert!(tree.imports.is_empty() && tree.stmts.is_empty() && tree.items.is_empty());
        }
    });
    h.case("api/an empty file prints empty", || {
        let file = source("a.en", "");
        let mut dcx = DiagCtx::new();
        let tree = parse_file(&file, &mut NodeIdGen::new(), ParseMode::Test, &mut dcx);
        assert_eq!(print_file(&file, &tree), "");
        assert!(!dcx.has_errors());
    });
}
