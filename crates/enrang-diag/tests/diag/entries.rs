//! The `= note`, `= why`, `= rule` and `= from TypeScript` entries, and their
//! separation from the snippet.

use enrang_diag::{Code, Diagnostic, Entry, EntryKind, Help};
use enrang_testkit::Harness;

use crate::support::{Src, lines, numbered_source, render_table, row, same, warn};

const SRC: &str = "abc\n";

fn every_kind(h: &mut Harness) {
    let kinds = [
        (EntryKind::Note, "note"),
        (EntryKind::Why, "why"),
        (EntryKind::Rule, "rule"),
        (EntryKind::FromTypeScript, "from TypeScript"),
    ];
    for (kind, word) in kinds {
        h.case(format!("entries/one/{word}"), move || {
            let src = Src::new("a.en", SRC);
            let diag = warn(src.find("abc"), "p").with_entry(kind, "text");
            same(
                &src.one(diag),
                &lines(&[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | abc",
                    "  | ^^^ p",
                    "  |",
                    &format!("  = {word}: text"),
                ]),
            );
        });
        h.case(format!("entries/continuation/{word}"), move || {
            let src = Src::new("a.en", SRC);
            let diag = warn(src.find("abc"), "p").with_entry(kind, "first\nsecond\n  third");
            let indent = " ".repeat("  = : ".len() + word.len());
            same(
                &src.one(diag),
                &lines(&[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | abc",
                    "  | ^^^ p",
                    "  |",
                    &format!("  = {word}: first"),
                    &format!("{indent}second"),
                    &format!("{indent}  third"),
                ]),
            );
        });
        h.case(
            format!("entries/continuation at width 2/{word}"),
            move || {
                let source = numbered_source(10);
                let src = Src::new("a.en", &source);
                let diag = warn(src.on_line(10, "l10"), "p").with_entry(kind, "first\nsecond");
                let indent = " ".repeat("   = : ".len() + word.len());
                same(
                    &src.one(diag),
                    &lines(&[
                        "warning[EN0430]: m",
                        "  --> a.en:10:1",
                        "   |",
                        "10 | l10",
                        "   | ^^^ p",
                        "   |",
                        &format!("   = {word}: first"),
                        &format!("{indent}second"),
                    ]),
                );
            },
        );
        h.case(format!("entries/spanless/{word}"), move || {
            let src = Src::new("a.en", SRC);
            let diag = Diagnostic::spanless(Code::EN0430, "m").with_entry(kind, "text");
            same(
                &src.one(diag),
                &lines(&["warning[EN0430]: m", &format!("  = {word}: text")]),
            );
        });
        h.case(
            format!("entries/builder and struct literal agree/{word}"),
            move || {
                let src = Src::new("a.en", SRC);
                let built = warn(src.find("abc"), "p").with_entry(kind, "x");
                let mut literal = warn(src.find("abc"), "p");
                literal.entries.push(Entry {
                    kind,
                    text: "x".to_owned(),
                });
                assert_eq!(built, literal);
            },
        );
    }
}

fn shapes(h: &mut Harness) {
    render_table(
        h,
        "entries/shapes",
        vec![
            row(
                "all four, in the order given",
                SRC,
                |s| {
                    vec![
                        warn(s.find("abc"), "p")
                            .from_typescript("t")
                            .rule("r")
                            .why("w")
                            .note("n"),
                    ]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | abc",
                    "  | ^^^ p",
                    "  |",
                    "  = from TypeScript: t",
                    "  = rule: r",
                    "  = why: w",
                    "  = note: n",
                ],
            ),
            row(
                "a kind may repeat",
                SRC,
                |s| {
                    vec![
                        warn(s.find("abc"), "p")
                            .note("one")
                            .note("two")
                            .note("three"),
                    ]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | abc",
                    "  | ^^^ p",
                    "  |",
                    "  = note: one",
                    "  = note: two",
                    "  = note: three",
                ],
            ),
            row(
                "a blank continuation line stays blank",
                SRC,
                |s| vec![warn(s.find("abc"), "p").note("one\n\nthree")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | abc",
                    "  | ^^^ p",
                    "  |",
                    "  = note: one",
                    "",
                    "          three",
                ],
            ),
            row(
                "an empty entry leaves no trailing space",
                SRC,
                |s| vec![warn(s.find("abc"), "p").note("")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | abc",
                    "  | ^^^ p",
                    "  |",
                    "  = note:",
                ],
            ),
            row(
                "a warning with nothing after the snippet has no bare gutter",
                SRC,
                |s| vec![warn(s.find("abc"), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | abc",
                    "  | ^^^ p",
                ],
            ),
            row(
                "an error's explain line follows the bare gutter",
                SRC,
                |s| vec![crate::support::err(s.find("abc"), "p")],
                &[
                    "error[EN0301]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | abc",
                    "  | ^^^ p",
                    "  |",
                    "  = explain: run `enrang explain EN0301`",
                    "",
                    "error: aborting due to 1 previous error",
                ],
            ),
            row(
                "entries come between the bare gutter and the helps",
                SRC,
                |s| {
                    vec![
                        crate::support::err(s.find("abc"), "p")
                            .with_help(Help::text("h"))
                            .note("n"),
                    ]
                },
                &[
                    "error[EN0301]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | abc",
                    "  | ^^^ p",
                    "  |",
                    "  = note: n",
                    "help: h",
                    "  = explain: run `enrang explain EN0301`",
                    "",
                    "error: aborting due to 1 previous error",
                ],
            ),
            row(
                "a bare gutter separates a snippet from a help with no entries",
                SRC,
                |s| vec![warn(s.find("abc"), "p").with_help(Help::text("h"))],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | abc",
                    "  | ^^^ p",
                    "  |",
                    "help: h",
                ],
            ),
            row(
                "a spanless diagnostic has no location, snippet or bare gutter",
                SRC,
                |_| vec![Diagnostic::spanless(Code::EN1301, "m")],
                &[
                    "error[EN1301]: m",
                    "  = explain: run `enrang explain EN1301`",
                    "",
                    "error: aborting due to 1 previous error",
                ],
            ),
        ],
    );
}

pub fn register(h: &mut Harness) {
    every_kind(h);
    shapes(h);
}
