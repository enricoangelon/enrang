//! The header of each severity, and the final `aborting` line.

use enrang_diag::{Code, Diagnostic, Severity};
use enrang_testkit::Harness;

use crate::support::{Src, err, lines, same, warn};

fn summary_rows(h: &mut Harness) {
    let table: [(usize, usize, Option<&str>); 13] = [
        (0, 0, None),
        (0, 1, None),
        (0, 2, None),
        (0, 5, None),
        (1, 0, Some("error: aborting due to 1 previous error")),
        (2, 0, Some("error: aborting due to 2 previous errors")),
        (3, 0, Some("error: aborting due to 3 previous errors")),
        (11, 0, Some("error: aborting due to 11 previous errors")),
        (
            1,
            1,
            Some("error: aborting due to 1 previous error; 1 warning emitted"),
        ),
        (
            1,
            2,
            Some("error: aborting due to 1 previous error; 2 warnings emitted"),
        ),
        (
            2,
            1,
            Some("error: aborting due to 2 previous errors; 1 warning emitted"),
        ),
        (
            2,
            2,
            Some("error: aborting due to 2 previous errors; 2 warnings emitted"),
        ),
        (
            7,
            13,
            Some("error: aborting due to 7 previous errors; 13 warnings emitted"),
        ),
    ];
    for (errors, warnings, expected) in table {
        h.case(
            format!("summary/{errors} errors {warnings} warnings"),
            move || {
                let src = Src::new("a.en", "x\n");
                let span = src.find("x");
                let mut diags: Vec<Diagnostic> = Vec::new();
                diags.extend((0..warnings).map(|_| warn(span, "p")));
                diags.extend((0..errors).map(|_| err(span, "p")));
                let rendered = src.render(&diags);
                match expected {
                    Some(last) => {
                        assert!(
                            rendered.ends_with(&format!("\n\n{last}\n")),
                            "wanted a blank line and `{last}` at the end of:\n{rendered}"
                        );
                        assert_eq!(rendered.matches("aborting").count(), 1);
                    }
                    None => {
                        assert!(!rendered.contains("aborting"), "{rendered}");
                        assert!(
                            rendered.is_empty() || rendered.ends_with("^ p\n"),
                            "{rendered}"
                        );
                    }
                }
                let separators = rendered.matches("\n\n").count();
                let wanted = (errors + warnings).saturating_sub(1) + usize::from(errors > 0);
                assert_eq!(separators, wanted, "blank lines in:\n{rendered}");
            },
        );
    }
}

fn notes(h: &mut Harness) {
    let note = || Diagnostic::bare_note(Code::EN0909, "`q8400` resolves to level `sse2`");
    let error = || Diagnostic::spanless(Code::EN1301, "e");
    let warning = || Diagnostic::spanless(Code::EN0430, "w");
    h.case(
        "summary/a note is one bare line with no abort line",
        move || {
            let src = Src::new("a.en", "x\n");
            same(
                &src.render(&[note()]),
                "note: `q8400` resolves to level `sse2`\n",
            );
        },
    );
    h.case("summary/the abort line does not count a note", move || {
        let src = Src::new("a.en", "x\n");
        same(
            &src.render(&[note(), error()]),
            &lines(&[
                "note: `q8400` resolves to level `sse2`",
                "",
                "error[EN1301]: e",
                "  = explain: run `enrang explain EN1301`",
                "",
                "error: aborting due to 1 previous error",
            ]),
        );
    });
    h.case(
        "summary/the abort line counts warnings beside a note",
        move || {
            let src = Src::new("a.en", "x\n");
            let text = src.render(&[note(), warning(), error()]);
            assert!(
                text.ends_with("error: aborting due to 1 previous error; 1 warning emitted\n"),
                "{text}"
            );
        },
    );
    h.case("summary/a note with a place shows it, and no code", || {
        let src = Src::new("a.en", "abc\n");
        let mut diag = Diagnostic::new(Code::EN0909, "m", src.find("b"), "here");
        diag.severity = Severity::Note;
        same(
            &src.one(diag),
            &lines(&["note: m", " --> a.en:1:2", "  |", "1 | abc", "  |  ^ here"]),
        );
    });
}

fn shapes(h: &mut Harness) {
    h.case("summary/no diagnostics render to nothing", || {
        let src = Src::new("a.en", "x\n");
        assert_eq!(src.render(&[]), "");
    });
    h.case("summary/a warning has no explain line", || {
        let src = Src::new("a.en", "x\n");
        let rendered = src.one(warn(src.find("x"), "p"));
        assert!(!rendered.contains("explain"), "{rendered}");
    });
    h.case(
        "summary/warnings mixed with errors, in the given order",
        || {
            let src = Src::new("a.en", "ab\n");
            let diags = [
                warn(src.find("a"), "first"),
                err(src.find("b"), "second"),
                warn(src.find("b"), "third"),
            ];
            same(
                &src.render(&diags),
                &lines(&[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | ab",
                    "  | ^ first",
                    "",
                    "error[EN0301]: m",
                    " --> a.en:1:2",
                    "  |",
                    "1 | ab",
                    "  |  ^ second",
                    "  |",
                    "  = explain: run `enrang explain EN0301`",
                    "",
                    "warning[EN0430]: m",
                    " --> a.en:1:2",
                    "  |",
                    "1 | ab",
                    "  |  ^ third",
                    "",
                    "error: aborting due to 1 previous error; 2 warnings emitted",
                ]),
            );
        },
    );
    h.case(
        "summary/warnings only: blank lines separate and nothing follows",
        || {
            let src = Src::new("a.en", "ab\n");
            let diags = [warn(src.find("a"), "first"), warn(src.find("b"), "second")];
            same(
                &src.render(&diags),
                &lines(&[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | ab",
                    "  | ^ first",
                    "",
                    "warning[EN0430]: m",
                    " --> a.en:1:2",
                    "  |",
                    "1 | ab",
                    "  |  ^ second",
                ]),
            );
        },
    );
    h.case(
        "summary/a test verdict renders fail and is not counted",
        || {
            let src = Src::new("a.en", "x\n");
            let diag = Diagnostic::new(Code::T0001, "m", src.find("x"), "p");
            assert_eq!(diag.severity, Severity::Fail);
            same(
                &src.one(diag),
                &lines(&[
                    "fail[T0001]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | x",
                    "  | ^ p",
                    "  |",
                    "  = explain: run `enrang explain T0001`",
                ]),
            );
        },
    );
    h.case(
        "summary/a test verdict beside an error counts only the error",
        || {
            let src = Src::new("a.en", "x\n");
            let diags = [
                Diagnostic::new(Code::T0001, "m", src.find("x"), "p"),
                err(src.find("x"), "p"),
            ];
            assert!(
                src.render(&diags)
                    .ends_with("\n\nerror: aborting due to 1 previous error\n")
            );
        },
    );
    h.case(
        "summary/the struct's severity decides, not the registry's",
        || {
            let src = Src::new("a.en", "x\n");
            let mut diag = warn(src.find("x"), "p");
            diag.severity = Severity::Error;
            same(
                &src.one(diag),
                &lines(&[
                    "error[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | x",
                    "  | ^ p",
                    "  |",
                    "  = explain: run `enrang explain EN0430`",
                    "",
                    "error: aborting due to 1 previous error",
                ]),
            );
        },
    );
    h.case("summary/the output ends in exactly one newline", || {
        let src = Src::new("a.en", "x\n");
        for diags in [
            vec![err(src.find("x"), "p")],
            vec![warn(src.find("x"), "p")],
        ] {
            let rendered = src.render(&diags);
            assert!(
                rendered.ends_with('\n') && !rendered.ends_with("\n\n"),
                "{rendered:?}"
            );
        }
    });
    h.case(
        "summary/no line of any output has trailing white space it did not ask for",
        || {
            let src = Src::new("a.en", "x\n\ny\n");
            let diag = err(src.find("y"), "")
                .with_secondary(src.find("x"), "")
                .note("a\n\nb");
            for line in src.one(diag).lines() {
                assert_eq!(line, line.trim_end(), "{line:?}");
            }
        },
    );
}

pub fn register(h: &mut Harness) {
    summary_rows(h);
    notes(h);
    shapes(h);
}
