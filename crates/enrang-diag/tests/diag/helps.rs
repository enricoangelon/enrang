//! Help blocks: `help:` lines, suggestion snippets, `+` and `~` marks, inserted and
//! replaced lines and their numbering.

use enrang_base::Span;
use enrang_diag::{Code, Diagnostic, Edit, Help};
use enrang_testkit::Harness;

use crate::support::{Src, lines, render_table, row, same, warn};

/// The source of most rows. Each row shows the part of the output after the common
/// head, which the `with_head` helper adds.
const SRC: &str = "fn main() {\n  let x = 1\n  let y = x;\n}\n";

/// The primary every row of this table shares, on line 3.
fn base(s: &Src) -> Diagnostic {
    warn(s.on_line(3, "y"), "p")
}

const HEAD: [&str; 6] = [
    "warning[EN0430]: m",
    " --> a.en:3:7",
    "  |",
    "3 |   let y = x;",
    "  |       ^ p",
    "  |",
];

type HelpRows = Vec<(&'static str, fn(&Src) -> Vec<Help>, &'static [&'static str])>;

/// Each row is the helps to add and the lines they render to under `HEAD`.
fn code_rows() -> HelpRows {
    vec![
        (
            "no code is one line",
            |_| vec![Help::text("h")],
            &["help: h"],
        ),
        (
            "several helps with no code",
            |_| vec![Help::text("a"), Help::text("or b"), Help::text("or c")],
            &["help: a", "help: or b", "help: or c"],
        ),
        (
            "a deletion ending mid-line keeps the rest of that line",
            |s| {
                let from = s.line_offset(1);
                let to = s.line_offset(2) + 2;
                vec![Help::suggest("h", vec![Edit::delete(s.span(from, to))])]
            },
            &["help: h", "  |", "1 ~ let x = 1"],
        ),
        (
            "a replacement ending in a newline is no insertion",
            |s| {
                let from = s.line_offset(2);
                vec![Help::suggest(
                    "h",
                    vec![Edit::replace(s.span(from, from + 6), "x\n")],
                )]
            },
            &["help: h", "  |", "2 ~ x", "3 ~ x = 1"],
        ),
        (
            "an insertion at the end of a line",
            |s| vec![Help::machine("h", vec![Edit::insert(s.line_end(2), ";")])],
            &["help: h", "  |", "2 |   let x = 1;", "  |            +"],
        ),
        (
            "an insertion at column 1 that adds no line",
            |s| {
                vec![Help::machine(
                    "h",
                    vec![Edit::insert(s.line_start(2), "//")],
                )]
            },
            &["help: h", "  |", "2 | //  let x = 1", "  | ++"],
        ),
        (
            "a replacement of the same width",
            |s| {
                vec![Help::machine(
                    "h",
                    vec![Edit::replace(s.on_line(2, "x"), "z")],
                )]
            },
            &["help: h", "  |", "2 |   let z = 1", "  |       ~"],
        ),
        (
            "a longer replacement marks the new text",
            |s| {
                vec![Help::machine(
                    "h",
                    vec![Edit::replace(s.on_line(2, "x"), "xyz")],
                )]
            },
            &["help: h", "  |", "2 |   let xyz = 1", "  |       ~~~"],
        ),
        (
            "a shorter replacement marks the new text",
            |s| {
                vec![Help::machine(
                    "h",
                    vec![Edit::replace(s.on_line(2, "let"), "l")],
                )]
            },
            &["help: h", "  |", "2 |   l x = 1", "  |   ~"],
        ),
        (
            "an insertion and a replacement, with marks of both kinds",
            |s| {
                vec![Help::suggest(
                    "h",
                    vec![
                        Edit::insert(s.on_line(2, "x").hi, ": i64"),
                        Edit::replace(s.on_line(2, "1"), "two"),
                    ],
                )]
            },
            &[
                "help: h",
                "  |",
                "2 |   let x: i64 = two",
                "  |        +++++   ~~~",
            ],
        ),
        (
            "edits are placed by position, not list order",
            |s| {
                vec![Help::suggest(
                    "h",
                    vec![
                        Edit::replace(s.on_line(2, "1"), "two"),
                        Edit::insert(s.on_line(2, "x").hi, ": i64"),
                    ],
                )]
            },
            &[
                "help: h",
                "  |",
                "2 |   let x: i64 = two",
                "  |        +++++   ~~~",
            ],
        ),
        (
            "a later mark's column counts earlier insertions",
            |s| {
                vec![Help::suggest(
                    "h",
                    vec![
                        Edit::insert(s.line_start(2), "abc"),
                        Edit::replace(s.on_line(2, "1"), "2"),
                    ],
                )]
            },
            &["help: h", "  |", "2 | abc  let x = 2", "  | +++          ~"],
        ),
        (
            "two replacements on a line",
            |s| {
                vec![Help::suggest(
                    "h",
                    vec![
                        Edit::replace(s.on_line(2, "x"), "a"),
                        Edit::replace(s.on_line(2, "1"), "b"),
                    ],
                )]
            },
            &["help: h", "  |", "2 |   let a = b", "  |       ~   ~"],
        ),
        (
            "an insertion right after a replacement",
            |s| {
                vec![Help::suggest(
                    "h",
                    vec![
                        Edit::replace(s.on_line(2, "x"), "ab"),
                        Edit::insert(s.on_line(2, "x").hi, "cd"),
                    ],
                )]
            },
            &["help: h", "  |", "2 |   let abcd = 1", "  |       ~~++"],
        ),
        (
            "an insertion right before a replacement",
            |s| {
                vec![Help::suggest(
                    "h",
                    vec![
                        Edit::replace(s.on_line(2, "x"), "ab"),
                        Edit::insert(s.on_line(2, "x").lo, "cd"),
                    ],
                )]
            },
            &["help: h", "  |", "2 |   let cdab = 1", "  |       ++~~"],
        ),
        (
            "a deletion marks its place once",
            |s| vec![Help::machine("h", vec![Edit::delete(s.on_line(2, " = 1"))])],
            &["help: h", "  |", "2 |   let x", "  |        ~"],
        ),
        (
            "a deletion in the middle of a line",
            |s| vec![Help::machine("h", vec![Edit::delete(s.on_line(2, "let "))])],
            &["help: h", "  |", "2 |   x = 1", "  |   ~"],
        ),
        (
            "an edit that changes nothing has no mark line",
            |s| vec![Help::machine("h", vec![Edit::insert(s.line_end(2), "")])],
            &["help: h", "  |", "2 |   let x = 1"],
        ),
        (
            "a whole line replaced on its own reads as a replacement",
            |s| {
                vec![Help::machine(
                    "h",
                    vec![Edit::replace(s.whole_line(2), "  let x = 2;")],
                )]
            },
            &["help: h", "  |", "2 |   let x = 2;", "  | ~~~~~~~~~~~~"],
        ),
        (
            "whole lines replaced in a multi-line edit show `~` in the gutter",
            |s| {
                vec![Help::machine(
                    "h",
                    vec![
                        Edit::replace(s.whole_line(2), "  let x = 2;"),
                        Edit::replace(s.whole_line(3), "  let y = 3;"),
                    ],
                )]
            },
            &["help: h", "  |", "2 ~   let x = 2;", "3 ~   let y = 3;"],
        ),
        (
            "`~` in the gutter also when only the statement is covered",
            |s| {
                vec![Help::machine(
                    "h",
                    vec![
                        Edit::replace(s.on_line(2, "let x = 1"), "let x = 2;"),
                        Edit::insert(s.line_start(4), "  done();\n"),
                    ],
                )]
            },
            &["help: h", "  |", "2 ~   let x = 2;", "4 +   done();"],
        ),
        (
            "partial edits keep `|` and marks beside a replaced line",
            |s| {
                vec![Help::machine(
                    "h",
                    vec![
                        Edit::replace(s.whole_line(2), "  let x = 2;"),
                        Edit::replace(s.on_line(3, "y"), "w"),
                    ],
                )]
            },
            &[
                "help: h",
                "  |",
                "2 ~   let x = 2;",
                "3 |   let w = x;",
                "  |       ~",
            ],
        ),
        (
            "a whole-line replacement with a second edit on its line stays partial",
            |s| {
                vec![Help::machine(
                    "h",
                    vec![
                        Edit::replace(s.on_line(2, "let x = 1"), "a"),
                        Edit::insert(s.line_end(2), ";"),
                        Edit::replace(s.on_line(3, "y"), "w"),
                    ],
                )]
            },
            &[
                "help: h",
                "  |",
                "2 |   a;",
                "  |   ~+",
                "3 |   let w = x;",
                "  |       ~",
            ],
        ),
        (
            "partial edits on several lines keep their marks",
            |s| {
                vec![Help::machine(
                    "h",
                    vec![
                        Edit::replace(s.on_line(3, "y"), "w"),
                        Edit::replace(s.on_line(2, "x"), "v"),
                    ],
                )]
            },
            &[
                "help: h",
                "  |",
                "2 |   let v = 1",
                "  |       ~",
                "3 |   let w = x;",
                "  |       ~",
            ],
        ),
        (
            "a replacement taking in the terminator is a whole line",
            |s| {
                let lo = s.line_start(2);
                let hi = s.line_start(3);
                vec![Help::machine(
                    "h",
                    vec![
                        Edit::replace(Span { lo, hi }, "  let x = 2;\n"),
                        Edit::insert(s.line_end(3), "//"),
                    ],
                )]
            },
            &[
                "help: h",
                "  |",
                "2 ~   let x = 2;",
                "3 |   let y = x;//",
                "  |             ++",
            ],
        ),
        (
            "an inserted line has `+` in the gutter and no mark line",
            |s| {
                vec![Help::machine(
                    "h",
                    vec![Edit::insert(s.line_start(2), "  new\n")],
                )]
            },
            &["help: h", "  |", "2 +   new"],
        ),
        (
            "an inserted blank line has no trailing space",
            |s| {
                vec![Help::machine(
                    "h",
                    vec![Edit::insert(s.line_start(2), "\n")],
                )]
            },
            &["help: h", "  |", "2 +"],
        ),
        (
            "one edit inserting several lines numbers them all",
            |s| {
                vec![Help::machine(
                    "h",
                    vec![Edit::insert(s.line_start(2), "a\n\nb\n")],
                )]
            },
            &["help: h", "  |", "2 + a", "3 +", "4 + b"],
        ),
        (
            "a line inserted after another takes the next number",
            |s| {
                vec![Help::machine(
                    "h",
                    vec![Edit::insert(s.line_end(2), "\n  new")],
                )]
            },
            &["help: h", "  |", "3 +   new"],
        ),
        (
            "lines inserted after another, several",
            |s| {
                vec![Help::machine(
                    "h",
                    vec![Edit::insert(s.line_end(2), "\na\nb")],
                )]
            },
            &["help: h", "  |", "3 + a", "4 + b"],
        ),
        (
            "a line inserted at the end of the file",
            |s| vec![Help::machine("h", vec![Edit::insert(s.eof().lo, "tail\n")])],
            &["help: h", "  |", "5 + tail"],
        ),
        (
            "numbers ignore the block's other edits",
            |s| {
                vec![Help::machine(
                    "h",
                    vec![
                        Edit::insert(s.line_start(4), "  third\n"),
                        Edit::insert(s.line_start(2), "  first\n"),
                        Edit::insert(s.line_start(3), "  second\n"),
                    ],
                )]
            },
            &[
                "help: h",
                "  |",
                "2 +   first",
                "3 +   second",
                "4 +   third",
            ],
        ),
        (
            "an inserted line goes before changes to the line it precedes",
            |s| {
                vec![Help::machine(
                    "h",
                    vec![
                        Edit::replace(s.on_line(2, "x"), "z"),
                        Edit::insert(s.line_start(2), "  new\n"),
                    ],
                )]
            },
            &[
                "help: h",
                "  |",
                "2 +   new",
                "2 |   let z = 1",
                "  |       ~",
            ],
        ),
        (
            "a line inserted after goes after changes to the line it follows",
            |s| {
                vec![Help::machine(
                    "h",
                    vec![
                        Edit::insert(s.line_end(2), "\n  new"),
                        Edit::replace(s.on_line(2, "x"), "z"),
                    ],
                )]
            },
            &[
                "help: h",
                "  |",
                "2 |   let z = 1",
                "  |       ~",
                "3 +   new",
            ],
        ),
        (
            "replacement text with a line break shows every new line",
            |s| {
                vec![Help::machine(
                    "h",
                    vec![Edit::replace(s.on_line(2, "x"), "a\nb")],
                )]
            },
            &["help: h", "  |", "2 ~   let a", "3 ~ b = 1"],
        ),
        (
            "a span across lines replaced by one line",
            |s| {
                let span = s.on_line(2, "x").to(s.on_line(3, "y"));
                vec![Help::machine("h", vec![Edit::replace(span, "z")])]
            },
            &["help: h", "  |", "2 ~   let z = x;"],
        ),
        (
            "whole lines replaced by more lines",
            |s| {
                let span = Span {
                    lo: s.line_start(2),
                    hi: s.line_end(3),
                };
                vec![Help::machine("h", vec![Edit::replace(span, "a\nb\nc")])]
            },
            &["help: h", "  |", "2 ~ a", "3 ~ b", "4 ~ c"],
        ),
        (
            "a whole line removed, terminator included",
            |s| {
                let span = Span {
                    lo: s.line_start(2),
                    hi: s.line_start(3),
                };
                vec![Help::machine("h", vec![Edit::delete(span)])]
            },
            &["help: h", "  |", "2 ~"],
        ),
        (
            "several whole lines removed",
            |s| {
                let span = Span {
                    lo: s.line_start(2),
                    hi: s.line_start(4),
                };
                vec![Help::machine("h", vec![Edit::delete(span)])]
            },
            &["help: h", "  |", "2 ~"],
        ),
        (
            "a line's text removed, its terminator staying",
            |s| vec![Help::machine("h", vec![Edit::delete(s.whole_line(2))])],
            &["help: h", "  |", "2 |", "  | ~"],
        ),
        (
            "two lines joined by removing a terminator",
            |s| {
                let span = Span {
                    lo: s.line_end(2),
                    hi: s.line_start(3),
                };
                vec![Help::machine("h", vec![Edit::delete(span)])]
            },
            &["help: h", "  |", "2 ~   let x = 1  let y = x;"],
        ),
        (
            "a command has a blank number column and no marks",
            |_| vec![Help::suggest("h", vec![Edit::command("enrang run a.en")])],
            &["help: h", "  |", "  | enrang run a.en"],
        ),
        (
            "a command of several lines",
            |_| vec![Help::suggest("h", vec![Edit::command("one\ntwo")])],
            &["help: h", "  |", "  | one", "  | two"],
        ),
        (
            "helps with and without code, in the given order",
            |s| {
                vec![
                    Help::text("first"),
                    Help::machine("second", vec![Edit::insert(s.line_end(2), ";")]),
                    Help::text("third"),
                    Help::machine("fourth", vec![Edit::replace(s.on_line(3, "y"), "w")]),
                ]
            },
            &[
                "help: first",
                "help: second",
                "  |",
                "2 |   let x = 1;",
                "  |            +",
                "help: third",
                "help: fourth",
                "  |",
                "3 |   let w = x;",
                "  |       ~",
            ],
        ),
        (
            "each help numbers its lines as if alone",
            |s| {
                vec![
                    Help::machine("a", vec![Edit::insert(s.line_start(2), "x\n")]),
                    Help::machine("b", vec![Edit::insert(s.line_start(2), "y\n")]),
                ]
            },
            &["help: a", "  |", "2 + x", "help: b", "  |", "2 + y"],
        ),
    ]
}

fn register_code_rows(h: &mut Harness) {
    for (name, helps, expected) in code_rows() {
        h.case(format!("helps/{name}"), move || {
            let src = Src::new("a.en", SRC);
            let mut diag = base(&src);
            diag.helps = helps(&src);
            let mut want: Vec<&str> = HEAD.to_vec();
            want.extend_from_slice(expected);
            same(&src.one(diag), &lines(&want));
        });
    }
}

fn register_sources(h: &mut Harness) {
    render_table(
        h,
        "helps/sources",
        vec![
            row(
                "a whole-line edit ignores white space after the line",
                "let a = 1;   \nlet b = 2;\n",
                |s| {
                    vec![warn(s.find("a"), "p").with_help(Help::suggest(
                        "h",
                        vec![
                            Edit::replace(s.find("let a = 1;"), "let x = 1;"),
                            Edit::replace(s.find("let b = 2;"), "let y = 2;"),
                        ],
                    ))]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:5",
                    "  |",
                    "1 | let a = 1;   ",
                    "  |     ^ p",
                    "  |",
                    "help: h",
                    "  |",
                    "1 ~ let x = 1;   ",
                    "2 ~ let y = 2;",
                ],
            ),
            row(
                "marks count scalars, not bytes",
                "日本語 = x\n",
                |s| {
                    vec![
                        warn(s.find("x"), "p")
                            .with_help(Help::machine("h", vec![Edit::replace(s.find("x"), "yz")])),
                    ]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:7",
                    "  |",
                    "1 | 日本語 = x",
                    "  |       ^ p",
                    "  |",
                    "help: h",
                    "  |",
                    "1 | 日本語 = yz",
                    "  |       ~~",
                ],
            ),
            row(
                "non-ASCII replacement text is as wide as its scalars",
                "x\n",
                |s| {
                    vec![warn(s.find("x"), "p").with_help(Help::machine(
                        "h",
                        vec![Edit::replace(s.find("x"), "日本語")],
                    ))]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | x",
                    "  | ^ p",
                    "  |",
                    "help: h",
                    "  |",
                    "1 | 日本語",
                    "  | ~~~",
                ],
            ),
            row(
                "tabs render as one space in a suggestion too",
                "\tx\n",
                |s| {
                    vec![
                        warn(s.find("x"), "p").with_help(Help::machine(
                            "h",
                            vec![Edit::replace(s.find("x"), "a\tb")],
                        )),
                    ]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:2",
                    "  |",
                    "1 |  x",
                    "  |  ^ p",
                    "  |",
                    "help: h",
                    "  |",
                    "1 |  a b",
                    "  |  ~~~",
                ],
            ),
            row(
                "a tab in an inserted line renders as one space",
                "x\n",
                |s| {
                    vec![warn(s.find("x"), "p").with_help(Help::machine(
                        "h",
                        vec![Edit::insert(s.line_start(1), "\ty\n")],
                    ))]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | x",
                    "  | ^ p",
                    "  |",
                    "help: h",
                    "  |",
                    "1 +  y",
                ],
            ),
            row(
                "a CRLF source: an insertion at the line end goes before the CR",
                "ab\r\ncd\r\n",
                |s| {
                    vec![
                        warn(s.find("cd"), "p")
                            .with_help(Help::machine("h", vec![Edit::insert(s.line_end(1), ";")])),
                    ]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:2:1",
                    "  |",
                    "2 | cd",
                    "  | ^^ p",
                    "  |",
                    "help: h",
                    "  |",
                    "1 | ab;",
                    "  |   +",
                ],
            ),
            row(
                "a CRLF source: an inserted line with CRLF shows no CR",
                "ab\r\ncd\r\n",
                |s| {
                    vec![warn(s.find("cd"), "p").with_help(Help::machine(
                        "h",
                        vec![Edit::insert(s.line_start(2), "new\r\n")],
                    ))]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:2:1",
                    "  |",
                    "2 | cd",
                    "  | ^^ p",
                    "  |",
                    "help: h",
                    "  |",
                    "2 + new",
                ],
            ),
            row(
                "a CRLF source: a line inserted after another",
                "ab\r\ncd\r\n",
                |s| {
                    vec![warn(s.find("cd"), "p").with_help(Help::machine(
                        "h",
                        vec![Edit::insert(s.line_end(1), "\r\nnew")],
                    ))]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:2:1",
                    "  |",
                    "2 | cd",
                    "  | ^^ p",
                    "  |",
                    "help: h",
                    "  |",
                    "2 + new",
                ],
            ),
            row(
                "a CRLF source: a whole line replaced with its terminator",
                "ab\r\ncd\r\nef\r\n",
                |s| {
                    let span = s.span(0, 4);
                    vec![warn(s.find("cd"), "p").with_help(Help::machine(
                        "h",
                        vec![
                            Edit::replace(span, "xy\r\n"),
                            Edit::insert(s.line_start(3), "new\r\n"),
                        ],
                    ))]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:2:1",
                    "  |",
                    "2 | cd",
                    "  | ^^ p",
                    "  |",
                    "help: h",
                    "  |",
                    "1 ~ xy",
                    "3 + new",
                ],
            ),
            row(
                "a line at the end of a file with no final newline",
                "abc",
                |s| {
                    vec![
                        warn(s.find("abc"), "p")
                            .with_help(Help::machine("h", vec![Edit::insert(s.eof().lo, "\nnew")])),
                    ]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | abc",
                    "  | ^^^ p",
                    "  |",
                    "help: h",
                    "  |",
                    "2 + new",
                ],
            ),
            row(
                "text added to an empty file",
                "",
                |s| {
                    vec![
                        warn(s.eof(), "p")
                            .with_help(Help::machine("h", vec![Edit::insert(s.eof().lo, "new\n")])),
                    ]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 |",
                    "  | ^ p",
                    "  |",
                    "help: h",
                    "  |",
                    "1 + new",
                ],
            ),
            row(
                "text with no line break added to the empty last line",
                "a\n",
                |s| {
                    vec![
                        warn(s.find("a"), "p")
                            .with_help(Help::machine("h", vec![Edit::insert(s.eof().lo, "b")])),
                    ]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | a",
                    "  | ^ p",
                    "  |",
                    "help: h",
                    "  |",
                    "2 | b",
                    "  | +",
                ],
            ),
            row(
                "a help's edit in the byte order mark's line",
                "\u{FEFF}ab\n",
                |s| {
                    vec![warn(s.find("b"), "p").with_help(Help::machine(
                        "h",
                        vec![Edit::insert(s.line_start(1), "x\n")],
                    ))]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:2",
                    "  |",
                    "1 | ab",
                    "  |  ^ p",
                    "  |",
                    "help: h",
                    "  |",
                    "1 + x",
                ],
            ),
            row(
                "a spanless diagnostic's edits name their file",
                "abc\n",
                |s| {
                    vec![
                        Diagnostic::spanless(Code::EN0430, "m")
                            .with_help(Help::machine("h", vec![Edit::replace(s.find("b"), "x")])),
                    ]
                },
                &[
                    "warning[EN0430]: m",
                    "help: h",
                    " --> a.en:1:2",
                    "  |",
                    "1 | axc",
                    "  |  ~",
                ],
            ),
        ],
    );
}

fn register_multi_file(h: &mut Harness) {
    let a = "one\n";
    let b = "two\nthree\n";
    type Build = fn(&Src) -> Diagnostic;
    let table: [(&str, Build, &[&str]); 5] = [
        (
            "a location line points at the file's first edit",
            |s| {
                warn(s.f(0).find("one"), "p").with_help(Help::machine(
                    "h",
                    vec![
                        Edit::replace(s.f(1).find("three"), "x"),
                        Edit::replace(s.f(1).find("two"), "y"),
                    ],
                ))
            },
            &[
                "warning[EN0430]: m",
                " --> a.en:1:1",
                "  |",
                "1 | one",
                "  | ^^^ p",
                "  |",
                "help: h",
                " --> b.en:1:1",
                "  |",
                "1 ~ y",
                "2 ~ x",
            ],
        ),
        (
            "an edit in another file gets a location line",
            |s| {
                warn(s.f(0).find("one"), "p").with_help(Help::machine(
                    "h",
                    vec![Edit::replace(s.f(1).find("three"), "x")],
                ))
            },
            &[
                "warning[EN0430]: m",
                " --> a.en:1:1",
                "  |",
                "1 | one",
                "  | ^^^ p",
                "  |",
                "help: h",
                " --> b.en:2:1",
                "  |",
                "2 | x",
                "  | ~",
            ],
        ),
        (
            "edits in two files: the diagnostic's own file first and unlocated",
            |s| {
                warn(s.f(1).find("two"), "p").with_help(Help::machine(
                    "h",
                    vec![
                        Edit::insert(s.f(0).line_end(1), ";"),
                        Edit::insert(s.f(1).line_end(2), ";"),
                    ],
                ))
            },
            &[
                "warning[EN0430]: m",
                " --> b.en:1:1",
                "  |",
                "1 | two",
                "  | ^^^ p",
                "  |",
                "help: h",
                "  |",
                "2 | three;",
                "  |      +",
                " --> a.en:1:4",
                "  |",
                "1 | one;",
                "  |    +",
            ],
        ),
        (
            "a replaced line counts as multi-line across files",
            |s| {
                warn(s.f(0).find("one"), "p").with_help(Help::machine(
                    "h",
                    vec![
                        Edit::replace(s.f(0).whole_line(1), "uno"),
                        Edit::replace(s.f(1).on_line(1, "w"), "x"),
                    ],
                ))
            },
            &[
                "warning[EN0430]: m",
                " --> a.en:1:1",
                "  |",
                "1 | one",
                "  | ^^^ p",
                "  |",
                "help: h",
                "  |",
                "1 ~ uno",
                " --> b.en:1:2",
                "  |",
                "1 | txo",
                "  |  ~",
            ],
        ),
        (
            "a command before source edits",
            |s| {
                warn(s.f(0).find("one"), "p").with_help(Help::suggest(
                    "h",
                    vec![
                        Edit::insert(s.f(0).line_end(1), ";"),
                        Edit::command("enrang run"),
                    ],
                ))
            },
            &[
                "warning[EN0430]: m",
                " --> a.en:1:1",
                "  |",
                "1 | one",
                "  | ^^^ p",
                "  |",
                "help: h",
                "  |",
                "  | enrang run",
                "  |",
                "1 | one;",
                "  |    +",
            ],
        ),
    ];
    for (name, build, expected) in table {
        h.case(format!("helps/multi file/{name}"), move || {
            let src = Src::files(&[("a.en", a), ("b.en", b)]);
            same(&src.one(build(&src)), &lines(expected));
        });
    }
}

fn register_error_tail(h: &mut Harness) {
    h.case("helps/the explain line follows the last help block", || {
        let src = Src::new("a.en", "x\n");
        let diag = Diagnostic::new(Code::EN0301, "m", src.find("x"), "p")
            .with_help(Help::machine("h", vec![Edit::replace(src.find("x"), "y")]));
        same(
            &src.one(diag),
            &lines(&[
                "error[EN0301]: m",
                " --> a.en:1:1",
                "  |",
                "1 | x",
                "  | ^ p",
                "  |",
                "help: h",
                "  |",
                "1 | y",
                "  | ~",
                "  = explain: run `enrang explain EN0301`",
                "",
                "error: aborting due to 1 previous error",
            ]),
        );
    });
    h.case(
        "helps/an overlapping edit renders without panicking",
        || {
            // apply_fixes refuses these; a renderer still shows whatever it was given.
            let src = Src::new("a.en", "abcdef\n");
            let diag = warn(src.find("abcdef"), "p").with_help(Help::suggest(
                "h",
                vec![
                    Edit::replace(src.find("abcd"), "X"),
                    Edit::replace(src.find("cdef"), "Y"),
                ],
            ));
            same(
                &src.one(diag),
                &lines(&[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | abcdef",
                    "  | ^^^^^^ p",
                    "  |",
                    "help: h",
                    "  |",
                    "1 | XY",
                    "  | ~~",
                ]),
            );
        },
    );
}

pub fn register(h: &mut Harness) {
    register_code_rows(h);
    register_sources(h);
    register_multi_file(h);
    register_error_tail(h);
}
