//! The explain pages of the codes this crate reports (TESTING 18: a `Compile` code
//! has "an explain page whose examples compile"). The pages live in
//! `crates/enrang-diag/explain/`, which cannot depend on this crate, so they are
//! checked here, through `enrang_diag::explain`: each failing example, parsed as
//! `check` parses a file, fires the page's code and no other, and each fixed example
//! parses with no diagnostic and is already in the canonical style of SPEC 12.5, as
//! every SPEC block is. EN0001's failing example is printed as the text it was meant
//! to be, and its file holds that text in Latin-1, so the test encodes it so.

use std::path::PathBuf;
use std::sync::Arc;

use enrang_base::{FileOrigin, SourceMap};
use enrang_diag::{Code, DiagCtx, FixtureKind, Milestone, Owner, Phase, explain};
use enrang_syntax::{
    NodeIdGen, ParseMode, decode_source, parse_file, print_file, report_invalid_utf8,
};
use enrang_testkit::Harness;

/// The name every example is parsed under: a module, not a `.test.en` part.
const FILE: &str = "page.en";

/// What `check` makes of a file holding `bytes`.
struct Checked {
    codes: Vec<Code>,
    /// Each diagnostic on a line, for a failure message.
    listing: String,
    /// The file as `fmt` prints it, when it parsed with no diagnostic.
    printed: Option<String>,
}

fn check(bytes: &[u8]) -> Checked {
    let decoded = decode_source(bytes);
    let mut map = SourceMap::new();
    let text: Arc<str> = Arc::from(decoded.text.as_str());
    let id = map.add(PathBuf::from(FILE), text, FileOrigin::User);
    let file = map.file(id).clone();
    let mut dcx = DiagCtx::new();
    report_invalid_utf8(&file, &decoded.invalid, &mut dcx);
    let tree = parse_file(&file, &mut NodeIdGen::new(), ParseMode::Test, &mut dcx);
    let diags = dcx.take();
    let listing = diags
        .iter()
        .map(|diag| format!("{}: {}\n", diag.code, diag.message))
        .collect();
    let printed = diags.is_empty().then(|| print_file(&file, &tree));
    Checked {
        codes: diags.iter().map(|diag| diag.code).collect(),
        listing,
        printed,
    }
}

/// A page's section as the file it stands for: its text and one final newline.
fn file_text(section: &str) -> String {
    format!("{section}\n")
}

/// The bytes of the file a failing example stands for.
fn failing_bytes(code: Code, text: &str) -> Vec<u8> {
    if code == Code::EN0001 {
        text.chars()
            .map(|c| u8::try_from(u32::from(c)).expect("the example is Latin-1"))
            .collect()
    } else {
        text.as_bytes().to_vec()
    }
}

/// The codes whose pages hold phase 1 source: this crate reports them.
fn syntax_codes() -> Vec<Code> {
    Code::ALL
        .iter()
        .copied()
        .filter(|code| {
            code.owner() == Owner::Syntax
                && code.phase() == Phase::Syntax
                && code.fixture() == FixtureKind::Compile
        })
        .collect()
}

/// `text`, the failing example of `code`'s page, reports `code` and nothing else.
fn fires(code: Code, text: &str) -> Result<(), String> {
    let checked = check(&failing_bytes(code, text));
    if checked.codes.is_empty() || checked.codes.iter().any(|&found| found != code) {
        return Err(format!(
            "the failing example must report {code} and nothing else:\n{text}{}",
            checked.listing
        ));
    }
    Ok(())
}

/// `text`, a fixed example, parses with no diagnostic and `fmt` leaves it as it is.
fn passes(text: &str) -> Result<(), String> {
    let checked = check(text.as_bytes());
    let Some(printed) = checked.printed else {
        return Err(format!(
            "the fixed example must parse clean:\n{text}{}",
            checked.listing
        ));
    };
    if printed != text {
        return Err(format!(
            "the fixed example is not formatted; `enrang fmt` prints:\n{printed}"
        ));
    }
    Ok(())
}

pub fn register(h: &mut Harness) {
    for code in syntax_codes() {
        if explain(code).is_none() {
            continue;
        }
        let page = explain(code).expect("a page");
        h.case(
            format!("explain/{code}/the failing example fires it"),
            move || fires(code, &file_text(page.failing)),
        );
        h.case(
            format!("explain/{code}/the fixed example passes"),
            move || passes(&file_text(page.fixed)),
        );
    }
    h.case("explain/every phase 1 code due by M1 has a page", || {
        let due: Vec<Code> = syntax_codes()
            .into_iter()
            .filter(|code| code.since() <= Milestone::M1)
            .collect();
        assert_eq!(due.len(), 65);
        for code in due {
            assert!(explain(code).is_some(), "{code} has no page");
        }
    });
    h.case("explain/EN0001's file is not UTF-8", || {
        let page = explain(Code::EN0001).expect("a page");
        let bytes = failing_bytes(Code::EN0001, &file_text(page.failing));
        assert!(std::str::from_utf8(&bytes).is_err());
        assert!(std::str::from_utf8(page.fixed.as_bytes()).is_ok());
    });
    h.case(
        "explain/the check rejects a page that proves nothing",
        || {
            // Each half fails on what it exists to catch: a failing example that reports
            // nothing or another code too, and a fixed example that reports something or
            // is not formatted.
            assert!(fires(Code::EN0201, "const y = a === b;\n").is_ok());
            assert!(fires(Code::EN0201, "const y = a == b;\n").is_err());
            assert!(fires(Code::EN0201, "const y = a === b\nf();\n").is_err());
            assert!(fires(Code::EN0101, "const y = a === b;\n").is_err());
            assert!(passes("const x = 1;\n").is_ok());
            assert!(passes("const x = 1\n").is_err());
            assert!(passes("const  x = 1;\n").is_err());
            assert!(passes("const x = 1;").is_err());
        },
    );
}
