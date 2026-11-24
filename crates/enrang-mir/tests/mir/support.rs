//! Reading the suite's `.mir` fixtures, and comparing bodies but for their spans.

use std::path::PathBuf;

use enrang_base::Span;
use enrang_hir::Tcx;
use enrang_mir::{Body, parse_module, print_module};

/// The fixtures directory of this suite.
pub fn dir(sub: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/mir")
        .join(sub)
}

/// Every `.mir` file of `sub`, sorted, with its text.
pub fn fixtures(sub: &str) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = std::fs::read_dir(dir(sub))
        .expect("a fixtures directory")
        .map(|e| e.expect("an entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "mir"))
        .map(|p| {
            let name = p
                .file_stem()
                .expect("a name")
                .to_string_lossy()
                .into_owned();
            (
                name,
                std::fs::read_to_string(&p).expect("a readable fixture"),
            )
        })
        .collect();
    out.sort();
    out
}

/// Parses `text`, panicking with the error.
pub fn parse(text: &str) -> (Tcx, Vec<Body>) {
    parse_module(text).unwrap_or_else(|e| panic!("{e}\n{text}"))
}

/// `b` with every span `DUMMY`.
pub fn unspanned(b: &Body) -> Body {
    let mut b = b.clone();
    b.span = Span::DUMMY;
    for l in b.locals.iter_mut() {
        l.span = Span::DUMMY;
    }
    for r in b.unsafe_regions.iter_mut() {
        r.span = Span::DUMMY;
    }
    for c in &mut b.captures {
        c.span = Span::DUMMY;
    }
    for block in b.blocks.iter_mut() {
        for s in &mut block.stmts {
            s.span = Span::DUMMY;
        }
        block.term.span = Span::DUMMY;
    }
    for l in &mut b.meta.loops {
        l.span = Span::DUMMY;
    }
    for f in b.meta.facts.iter_mut() {
        f.span = Span::DUMMY;
    }
    for r in &mut b.meta.records {
        r.span = Span::DUMMY;
    }
    b
}

/// Prints the bodies of a parsed module.
pub fn print(tcx: &Tcx, bodies: &[Body]) -> String {
    print_module(tcx, bodies)
}
