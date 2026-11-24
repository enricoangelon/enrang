//! Annotation lines: several spans on one line, overlaps, zero-width spans, the
//! ends of files and lines, CRLF, tabs and non-ASCII columns.

use enrang_base::{BytePos, Span};
use enrang_testkit::Harness;

use crate::support::{Src, render_table, row, warn};

const LINE: &str = "let alpha = beta + gamma;\n";

fn several_spans(h: &mut Harness) {
    render_table(
        h,
        "labels/one line",
        vec![
            row(
                "primary then a secondary to its right",
                LINE,
                |s| vec![warn(s.find("alpha"), "p").with_secondary(s.find("beta"), "s")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:5",
                    "  |",
                    "1 | let alpha = beta + gamma;",
                    "  |     ^^^^^ p",
                    "  |             ---- s",
                ],
            ),
            row(
                "primary first although a secondary is further left",
                LINE,
                |s| vec![warn(s.find("gamma"), "p").with_secondary(s.find("alpha"), "s")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:20",
                    "  |",
                    "1 | let alpha = beta + gamma;",
                    "  |                    ^^^^^ p",
                    "  |     ----- s",
                ],
            ),
            row(
                "the left secondary goes first though it is the wider",
                "abcdef gh ij\n",
                |s| {
                    vec![
                        warn(s.find("ij"), "p")
                            .with_secondary(s.find("gh"), "narrow")
                            .with_secondary(s.find("abcdef"), "wide"),
                    ]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:11",
                    "  |",
                    "1 | abcdef gh ij",
                    "  |           ^^ p",
                    "  | ------ wide",
                    "  |        -- narrow",
                ],
            ),
            row(
                "secondaries go left to right whatever their order",
                LINE,
                |s| {
                    vec![
                        warn(s.find("beta"), "p")
                            .with_secondary(s.find("gamma"), "third")
                            .with_secondary(s.find("let"), "first")
                            .with_secondary(s.find("alpha"), "second"),
                    ]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:13",
                    "  |",
                    "1 | let alpha = beta + gamma;",
                    "  |             ^^^^ p",
                    "  | --- first",
                    "  |     ----- second",
                    "  |                    ----- third",
                ],
            ),
            row(
                "secondaries on both sides of the primary",
                LINE,
                |s| {
                    vec![
                        warn(s.find("beta"), "p")
                            .with_secondary(s.find("gamma"), "right")
                            .with_secondary(s.find("alpha"), "left"),
                    ]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:13",
                    "  |",
                    "1 | let alpha = beta + gamma;",
                    "  |             ^^^^ p",
                    "  |     ----- left",
                    "  |                    ----- right",
                ],
            ),
            row(
                "a span shares the primary's start: the primary still comes first",
                LINE,
                |s| {
                    let beta = s.find("beta");
                    vec![
                        warn(
                            Span {
                                lo: beta.lo,
                                hi: beta.lo + 2,
                            },
                            "p",
                        )
                        .with_secondary(beta, "wide")
                        .with_secondary(beta.to(s.find("+")), "wider"),
                    ]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:13",
                    "  |",
                    "1 | let alpha = beta + gamma;",
                    "  |             ^^ p",
                    "  |             ---- wide",
                    "  |             ------ wider",
                ],
            ),
            row(
                "equal starts: the narrower secondary first",
                LINE,
                |s| {
                    let beta = s.find("beta");
                    vec![
                        warn(s.find("let"), "p")
                            .with_secondary(beta.to(s.find("+")), "wider")
                            .with_secondary(
                                Span {
                                    lo: beta.lo,
                                    hi: beta.lo + 1,
                                },
                                "narrow",
                            ),
                    ]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | let alpha = beta + gamma;",
                    "  | ^^^ p",
                    "  |             - narrow",
                    "  |             ------ wider",
                ],
            ),
            row(
                "identical spans keep the order they were given",
                LINE,
                |s| {
                    vec![
                        warn(s.find("let"), "p")
                            .with_secondary(s.find("beta"), "one")
                            .with_secondary(s.find("beta"), "two")
                            .with_secondary(s.find("beta"), "three"),
                    ]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | let alpha = beta + gamma;",
                    "  | ^^^ p",
                    "  |             ---- one",
                    "  |             ---- two",
                    "  |             ---- three",
                ],
            ),
            row(
                "a secondary identical to the primary",
                LINE,
                |s| vec![warn(s.find("beta"), "p").with_secondary(s.find("beta"), "s")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:13",
                    "  |",
                    "1 | let alpha = beta + gamma;",
                    "  |             ^^^^ p",
                    "  |             ---- s",
                ],
            ),
            row(
                "overlapping spans each get a whole line",
                LINE,
                |s| {
                    let beta = s.find("beta");
                    let gamma = s.find("gamma");
                    vec![warn(s.find("alpha").to(beta), "p").with_secondary(beta.to(gamma), "s")]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:5",
                    "  |",
                    "1 | let alpha = beta + gamma;",
                    "  |     ^^^^^^^^^^^^ p",
                    "  |             ------------ s",
                ],
            ),
            row(
                "a span nested in the primary",
                LINE,
                |s| {
                    vec![
                        warn(s.find("alpha").to(s.find("gamma")), "p")
                            .with_secondary(s.find("+"), "s"),
                    ]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:5",
                    "  |",
                    "1 | let alpha = beta + gamma;",
                    "  |     ^^^^^^^^^^^^^^^^^^^^ p",
                    "  |                  - s",
                ],
            ),
            row(
                "adjacent spans",
                LINE,
                |s| {
                    let eq = s.find(" = ");
                    vec![warn(s.find("alpha"), "p").with_secondary(eq, "s")]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:5",
                    "  |",
                    "1 | let alpha = beta + gamma;",
                    "  |     ^^^^^ p",
                    "  |          --- s",
                ],
            ),
            row(
                "the whole line",
                LINE,
                |s| vec![warn(s.whole_line(1), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | let alpha = beta + gamma;",
                    "  | ^^^^^^^^^^^^^^^^^^^^^^^^^ p",
                ],
            ),
            row(
                "an empty label leaves no trailing space",
                LINE,
                |s| vec![warn(s.find("beta"), "").with_secondary(s.find("alpha"), "")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:13",
                    "  |",
                    "1 | let alpha = beta + gamma;",
                    "  |             ^^^^",
                    "  |     -----",
                ],
            ),
            row(
                "a label's line break aligns under its text",
                LINE,
                |s| vec![warn(s.find("beta"), "first\nsecond\n\nfourth")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:13",
                    "  |",
                    "1 | let alpha = beta + gamma;",
                    "  |             ^^^^ first",
                    "  |                  second",
                    "  |",
                    "  |                  fourth",
                ],
            ),
            row(
                "several lines with several spans each",
                "ab cd\nef gh\n",
                |s| {
                    vec![
                        warn(s.on_line(2, "gh"), "p")
                            .with_secondary(s.on_line(1, "cd"), "s1")
                            .with_secondary(s.on_line(2, "ef"), "s2")
                            .with_secondary(s.on_line(1, "ab"), "s3"),
                    ]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:2:4",
                    "  |",
                    "1 | ab cd",
                    "  | -- s3",
                    "  |    -- s1",
                    "2 | ef gh",
                    "  |    ^^ p",
                    "  | -- s2",
                ],
            ),
        ],
    );
}

fn zero_width(h: &mut Harness) {
    render_table(
        h,
        "labels/zero width",
        vec![
            row(
                "at column 1",
                "abc\n",
                |s| vec![warn(s.point(1, 1), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | abc",
                    "  | ^ p",
                ],
            ),
            row(
                "in the middle",
                "abc\n",
                |s| vec![warn(s.point(1, 2), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:2",
                    "  |",
                    "1 | abc",
                    "  |  ^ p",
                ],
            ),
            row(
                "past the last character, as in G01",
                "abc\n",
                |s| vec![warn(s.eol(1), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:4",
                    "  |",
                    "1 | abc",
                    "  |    ^ p",
                ],
            ),
            row(
                "on an empty line",
                "a\n\nb\n",
                |s| vec![warn(s.point(2, 1), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:2:1",
                    "  |",
                    "2 |",
                    "  | ^ p",
                ],
            ),
            row(
                "a zero-width secondary among others",
                "abc def\n",
                |s| vec![warn(s.find("abc"), "p").with_secondary(s.point(1, 4), "s")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | abc def",
                    "  | ^^^ p",
                    "  |    - s",
                ],
            ),
            row(
                "two zero-width spans at one place",
                "abc\n",
                |s| vec![warn(s.point(1, 2), "p").with_secondary(s.point(1, 2), "s")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:2",
                    "  |",
                    "1 | abc",
                    "  |  ^ p",
                    "  |  - s",
                ],
            ),
            row(
                "a zero-width span keeps its order beside a one-column span",
                "abc\n",
                |s| {
                    vec![
                        warn(s.find("c"), "p")
                            .with_secondary(s.find("b"), "wide")
                            .with_secondary(s.point(1, 2), "point"),
                    ]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:3",
                    "  |",
                    "1 | abc",
                    "  |   ^ p",
                    "  |  - wide",
                    "  |  - point",
                ],
            ),
        ],
    );
}

fn end_of_file(h: &mut Harness) {
    render_table(
        h,
        "labels/end of file",
        vec![
            row(
                "after the final newline is the empty last line",
                "abc\n",
                |s| vec![warn(s.eof(), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:2:1",
                    "  |",
                    "2 |",
                    "  | ^ p",
                ],
            ),
            row(
                "with no final newline it is past the last character",
                "abc",
                |s| vec![warn(s.eof(), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:4",
                    "  |",
                    "1 | abc",
                    "  |    ^ p",
                ],
            ),
            row(
                "an empty file has an empty line 1",
                "",
                |s| vec![warn(s.eof(), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 |",
                    "  | ^ p",
                ],
            ),
            row(
                "the last character with no final newline",
                "abc",
                |s| vec![warn(s.find("c"), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:3",
                    "  |",
                    "1 | abc",
                    "  |   ^ p",
                ],
            ),
            row(
                "a span taking in the final newline stops at the line end",
                "abc\n",
                |s| vec![warn(s.span(1, 4), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:2",
                    "  |",
                    "1 | abc",
                    "  |  ^^ p",
                ],
            ),
            row(
                "the span of just the final newline",
                "abc\n",
                |s| vec![warn(s.span(3, 4), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:4",
                    "  |",
                    "1 | abc",
                    "  |    ^ p",
                ],
            ),
            row(
                "a multi-line span marks from its start to that line's end",
                "abcd\nefgh\nijkl\n",
                |s| vec![warn(s.find("cd\nefgh\nij"), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:3",
                    "  |",
                    "1 | abcd",
                    "  |   ^^ p",
                ],
            ),
            row(
                "a multi-line span starting at a line end",
                "abcd\nefgh\n",
                |s| vec![warn(s.span(4, 7), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:5",
                    "  |",
                    "1 | abcd",
                    "  |     ^ p",
                ],
            ),
            row(
                "a span whose end is past the file is cut at the line",
                "abc\n",
                |s| {
                    vec![warn(
                        Span {
                            lo: s.at(1),
                            hi: BytePos(s.start + 4000),
                        },
                        "p",
                    )]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:2",
                    "  |",
                    "1 | abc",
                    "  |  ^^ p",
                ],
            ),
            row(
                "an inverted span gets one mark at its start",
                "abc\n",
                |s| {
                    vec![warn(
                        Span {
                            lo: s.at(2),
                            hi: s.at(1),
                        },
                        "p",
                    )]
                },
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:3",
                    "  |",
                    "1 | abc",
                    "  |   ^ p",
                ],
            ),
            row(
                "whitespace at the end of a source line is kept",
                "abc  \n",
                |s| vec![warn(s.find("abc"), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | abc  ",
                    "  | ^^^ p",
                ],
            ),
        ],
    );
}

fn crlf(h: &mut Harness) {
    render_table(
        h,
        "labels/crlf",
        vec![
            row(
                "the carriage return is not shown",
                "one\r\ntwo\r\n",
                |s| vec![warn(s.find("two"), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:2:1",
                    "  |",
                    "2 | two",
                    "  | ^^^ p",
                ],
            ),
            row(
                "a span taking in CRLF stops at the line end",
                "one\r\ntwo\r\n",
                |s| vec![warn(s.find("one\r\n"), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | one",
                    "  | ^^^ p",
                ],
            ),
            row(
                "a span of just the carriage return",
                "one\r\n",
                |s| vec![warn(s.find("\r"), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:4",
                    "  |",
                    "1 | one",
                    "  |    ^ p",
                ],
            ),
            row(
                "a zero-width span before the carriage return",
                "one\r\n",
                |s| vec![warn(s.eol(1), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:4",
                    "  |",
                    "1 | one",
                    "  |    ^ p",
                ],
            ),
            row(
                "a position between the carriage return and the line feed",
                "one\r\n",
                |s| vec![warn(s.point_at(4), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:5",
                    "  |",
                    "1 | one",
                    "  |     ^ p",
                ],
            ),
            row(
                "an empty CRLF line",
                "one\r\n\r\nthree\r\n",
                |s| vec![warn(s.point(2, 1), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:2:1",
                    "  |",
                    "2 |",
                    "  | ^ p",
                ],
            ),
            row(
                "unlabelled lines of a gap lose theirs too",
                "a\r\nb\r\nc\r\n",
                |s| vec![warn(s.find("c"), "p").with_secondary(s.find("a"), "s")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:3:1",
                    "  |",
                    "1 | a",
                    "  | - s",
                    "2 | b",
                    "3 | c",
                    "  | ^ p",
                ],
            ),
            row(
                "end of file after a final CRLF",
                "a\r\n",
                |s| vec![warn(s.eof(), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:2:1",
                    "  |",
                    "2 |",
                    "  | ^ p",
                ],
            ),
            row(
                "a carriage return inside a line is one column of space",
                "a\rb\n",
                |s| vec![warn(s.find("b"), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:3",
                    "  |",
                    "1 | a b",
                    "  |   ^ p",
                ],
            ),
            row(
                "mixed terminators count the same lines",
                "a\nb\r\nc\n",
                |s| vec![warn(s.find("c"), "p").with_secondary(s.find("b"), "s")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:3:1",
                    "  |",
                    "2 | b",
                    "  | - s",
                    "3 | c",
                    "  | ^ p",
                ],
            ),
        ],
    );
}

fn columns(h: &mut Harness) {
    render_table(
        h,
        "labels/columns",
        vec![
            row(
                "a two-byte scalar is one column",
                "é x\n",
                |s| vec![warn(s.find("x"), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:3",
                    "  |",
                    "1 | é x",
                    "  |   ^ p",
                ],
            ),
            row(
                "a three-byte scalar is one column",
                "日本語 x\n",
                |s| vec![warn(s.find("x"), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:5",
                    "  |",
                    "1 | 日本語 x",
                    "  |     ^ p",
                ],
            ),
            row(
                "a four-byte scalar is one column",
                "🦀🦀 x\n",
                |s| vec![warn(s.find("x"), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:4",
                    "  |",
                    "1 | 🦀🦀 x",
                    "  |    ^ p",
                ],
            ),
            row(
                "a span over non-ASCII text is as wide as its scalars",
                "x = \"日本語\";\n",
                |s| vec![warn(s.find("日本語"), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:6",
                    "  |",
                    "1 | x = \"日本語\";",
                    "  |      ^^^ p",
                ],
            ),
            row(
                "a combining mark is its own scalar",
                "e\u{301}x\n",
                |s| vec![warn(s.find("x"), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:3",
                    "  |",
                    "1 | e\u{301}x",
                    "  |   ^ p",
                ],
            ),
            row(
                "a position inside a scalar gets that scalar's column",
                "aéb\n",
                |s| vec![warn(s.point_at(2), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:2",
                    "  |",
                    "1 | aéb",
                    "  |  ^ p",
                ],
            ),
            row(
                "a span ending inside a scalar takes in that scalar",
                "aéb\n",
                |s| vec![warn(s.span(0, 2), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | aéb",
                    "  | ^^ p",
                ],
            ),
            row(
                "a byte order mark is outside line 1",
                "\u{FEFF}abc\n",
                |s| vec![warn(s.find("b"), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:2",
                    "  |",
                    "1 | abc",
                    "  |  ^ p",
                ],
            ),
            row(
                "a position in the byte order mark is column 1",
                "\u{FEFF}abc\n",
                |s| vec![warn(s.span(1, 4), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | abc",
                    "  | ^ p",
                ],
            ),
            row(
                "a leading tab is one column of space",
                "\tabc\n",
                |s| vec![warn(s.find("abc"), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:2",
                    "  |",
                    "1 |  abc",
                    "  |  ^^^ p",
                ],
            ),
            row(
                "tabs between tokens",
                "a\t\tb\n",
                |s| vec![warn(s.find("b"), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:4",
                    "  |",
                    "1 | a  b",
                    "  |    ^ p",
                ],
            ),
            row(
                "a span over a tab counts it once",
                "a\tb\n",
                |s| vec![warn(s.find("a\tb"), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 | a b",
                    "  | ^^^ p",
                ],
            ),
            row(
                "a tab-only line is one space",
                "\t\na\n",
                |s| vec![warn(s.point(1, 1), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:1",
                    "  |",
                    "1 |  ",
                    "  | ^ p",
                ],
            ),
            row(
                "an escape byte in the source cannot reach the terminal",
                "a\u{1b}[31mb\n",
                |s| vec![warn(s.find("b"), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:1:7",
                    "  |",
                    "1 | a [31mb",
                    "  |       ^ p",
                ],
            ),
        ],
    );
}

/// A name, the diagnostic and the exact output.
type MultiFileRow = (
    &'static str,
    fn(&Src) -> enrang_diag::Diagnostic,
    &'static [&'static str],
);

fn multi_file(h: &mut Harness) {
    let text_a = "alpha\nbeta\ngamma\n";
    let text_b = "one\ntwo\nthree\n";
    let text_c = "\n\n\n\n\n\n\n\n\n\n\nlate\n";
    let tests: Vec<MultiFileRow> = vec![
        (
            "a secondary in another file gets its own location",
            |s| warn(s.f(0).find("beta"), "p").with_secondary(s.f(1).find("two"), "s"),
            &[
                "warning[EN0430]: m",
                " --> a.en:2:1",
                "  |",
                "2 | beta",
                "  | ^^^^ p",
                " --> b.en:2:1",
                "  |",
                "2 | two",
                "  | --- s",
            ],
        ),
        (
            "the primary's file comes first even when it is the later one",
            |s| warn(s.f(1).find("two"), "p").with_secondary(s.f(0).find("beta"), "s"),
            &[
                "warning[EN0430]: m",
                " --> b.en:2:1",
                "  |",
                "2 | two",
                "  | ^^^ p",
                " --> a.en:2:1",
                "  |",
                "2 | beta",
                "  | ---- s",
            ],
        ),
        (
            "other files follow in file order",
            |s| {
                warn(s.f(1).find("one"), "p")
                    .with_secondary(s.f(2).find("late"), "c")
                    .with_secondary(s.f(0).find("alpha"), "a")
            },
            &[
                "warning[EN0430]: m",
                "  --> b.en:1:1",
                "   |",
                " 1 | one",
                "   | ^^^ p",
                "  --> a.en:1:1",
                "   |",
                " 1 | alpha",
                "   | ----- a",
                "  --> c.en:12:1",
                "   |",
                "12 | late",
                "   | ---- c",
            ],
        ),
        (
            "a file's location points at its first span",
            |s| {
                warn(s.f(0).find("alpha"), "p")
                    .with_secondary(s.f(1).find("three"), "later")
                    .with_secondary(s.f(1).find("two"), "earlier")
            },
            &[
                "warning[EN0430]: m",
                " --> a.en:1:1",
                "  |",
                "1 | alpha",
                "  | ^^^^^ p",
                " --> b.en:2:1",
                "  |",
                "2 | two",
                "  | --- earlier",
                "3 | three",
                "  | ----- later",
            ],
        ),
        (
            "the gap rule does not cross files",
            |s| warn(s.f(0).find("gamma"), "p").with_secondary(s.f(1).find("one"), "s"),
            &[
                "warning[EN0430]: m",
                " --> a.en:3:1",
                "  |",
                "3 | gamma",
                "  | ^^^^^ p",
                " --> b.en:1:1",
                "  |",
                "1 | one",
                "  | --- s",
            ],
        ),
        (
            "one gutter width serves every file",
            |s| warn(s.f(0).find("alpha"), "p").with_secondary(s.f(2).find("late"), "s"),
            &[
                "warning[EN0430]: m",
                "  --> a.en:1:1",
                "   |",
                " 1 | alpha",
                "   | ^^^^^ p",
                "  --> c.en:12:1",
                "   |",
                "12 | late",
                "   | ---- s",
            ],
        ),
        (
            "the bare gutter comes once, after the last file",
            |s| {
                warn(s.f(0).find("alpha"), "p")
                    .with_secondary(s.f(1).find("one"), "s")
                    .note("n")
            },
            &[
                "warning[EN0430]: m",
                " --> a.en:1:1",
                "  |",
                "1 | alpha",
                "  | ^^^^^ p",
                " --> b.en:1:1",
                "  |",
                "1 | one",
                "  | --- s",
                "  |",
                "  = note: n",
            ],
        ),
        (
            "with no primary span the secondaries still show",
            |s| {
                let mut diag = warn(Span::DUMMY, "");
                diag.secondary.push(enrang_diag::Label {
                    span: s.f(1).find("two"),
                    text: "s".to_owned(),
                });
                diag
            },
            &[
                "warning[EN0430]: m",
                " --> b.en:2:1",
                "  |",
                "2 | two",
                "  | --- s",
            ],
        ),
    ];
    for (name, build, expected) in tests {
        h.case(format!("labels/multi file/{name}"), move || {
            let src = Src::files(&[("a.en", text_a), ("b.en", text_b), ("c.en", text_c)]);
            crate::support::same(&src.one(build(&src)), &crate::support::lines(expected));
        });
    }
    h.case(
        "labels/multi file/end of one file is not the start of the next",
        || {
            let src = Src::files(&[("a.en", "abc"), ("b.en", "def")]);
            let at_end = warn(src.f(0).eof(), "end");
            let at_start = warn(src.f(1).point_at(0), "start");
            crate::support::same(
                &src.render(&[at_end, at_start]),
                &crate::support::lines(&[
                    "warning[EN0430]: m",
                    " --> a.en:1:4",
                    "  |",
                    "1 | abc",
                    "  |    ^ end",
                    "",
                    "warning[EN0430]: m",
                    " --> b.en:1:1",
                    "  |",
                    "1 | def",
                    "  | ^ start",
                ]),
            );
        },
    );
}

pub fn register(h: &mut Harness) {
    several_spans(h);
    zero_width(h);
    end_of_file(h);
    crlf(h);
    columns(h);
    multi_file(h);
}
