//! What reaches the terminal: text from outside a source file is escaped, and source
//! text keeps its columns. Nothing a user types can act on the terminal or break the
//! shape of SPEC 13.1.

use enrang_diag::{Code, Diagnostic, Edit, Help, shown};
use enrang_testkit::Harness;

use crate::support::{Src, lines, same, warn};

/// Control characters and the characters `char::is_control` does not see: the
/// `Bidi_Control` property, which reorders a line on screen, and the Unicode line and
/// paragraph separators. The list is written out here, separately from the renderer's.
const DISTURBING: [char; 22] = [
    '\t', '\r', '\x07', '\x08', '\x1b', '\x7f', '\u{85}', '\u{9b}', '\u{61c}', '\u{200e}',
    '\u{200f}', '\u{202a}', '\u{202b}', '\u{202c}', '\u{202d}', '\u{202e}', '\u{2066}', '\u{2067}',
    '\u{2068}', '\u{2069}', '\u{2028}', '\u{2029}',
];

/// A place in a diagnostic, and a diagnostic carrying `text` there.
type Place = (&'static str, fn(&Src, &str) -> Diagnostic);

fn places() -> Vec<Place> {
    vec![
        ("message", |_, text| {
            Diagnostic::spanless(Code::EN1301, text)
        }),
        ("label", |src, text| warn(src.find("abc"), text)),
        ("label's second line", |src, text| {
            warn(src.find("abc"), &format!("first\n{text}"))
        }),
        ("secondary label", |src, text| {
            warn(src.find("abc"), "p").with_secondary(src.find("def"), text)
        }),
        ("note", |_, text| {
            Diagnostic::spanless(Code::EN1301, "m").note(text)
        }),
        ("note's second line", |_, text| {
            Diagnostic::spanless(Code::EN1301, "m").note(format!("first\n{text}"))
        }),
        ("help", |_, text| {
            Diagnostic::spanless(Code::EN1301, "m").with_help(Help::text(text))
        }),
        ("help with code", |src, text| {
            warn(src.find("abc"), "p").with_help(Help::machine(
                text,
                vec![Edit::replace(src.find("abc"), "x")],
            ))
        }),
        ("suggested text", |src, text| {
            warn(src.find("abc"), "p").with_help(Help::machine(
                "h",
                vec![Edit::replace(src.find("abc"), text)],
            ))
        }),
        ("command", |_, text| {
            Diagnostic::spanless(Code::EN1301, "m")
                .with_help(Help::suggest("h", vec![Edit::command(text)]))
        }),
    ]
}

fn assert_undisturbed(text: &str) {
    for c in DISTURBING {
        assert!(!text.contains(c), "{c:?} reached the output: {text:?}");
    }
}

fn registers_every_place(h: &mut Harness) {
    for (place, build) in places() {
        for c in DISTURBING {
            h.case(
                format!("terminal/{place} cannot carry {:#x}", u32::from(c)),
                move || {
                    let src = Src::new("a.en", "abc def\n");
                    let clean = src.one(build(&src, "ab"));
                    let dirty = src.one(build(&src, &format!("a{c}b")));
                    assert_undisturbed(&dirty);
                    assert_eq!(dirty.lines().count(), clean.lines().count(), "{dirty:?}");
                },
            );
        }
    }
}

fn exact_rows(h: &mut Harness) {
    h.case("terminal/a message shows the escape", || {
        let src = Src::new("a.en", "");
        same(
            &src.one(Diagnostic::spanless(
                Code::EN0909,
                "`--cpu=\x1b[2J` is not a CPU level",
            )),
            &lines(&[
                "error[EN0909]: `--cpu=\\u{1b}[2J` is not a CPU level",
                "  = explain: run `enrang explain EN0909`",
                "",
                "error: aborting due to 1 previous error",
            ]),
        );
    });
    h.case(
        "terminal/a line break in a message is no second line",
        || {
            let src = Src::new("a.en", "");
            let text = src.one(Diagnostic::spanless(Code::EN0430, "one\ntwo"));
            same(&text, "warning[EN0430]: one\\ntwo\n");
        },
    );
    h.case("terminal/a path keeps the location on one line", || {
        let src = Src::new("a\x1b[31m\nb.en", "abc\n");
        same(
            &src.one(warn(src.find("abc"), "p")),
            &lines(&[
                "warning[EN0430]: m",
                " --> a\\u{1b}[31m\\nb.en:1:1",
                "  |",
                "1 | abc",
                "  | ^^^ p",
            ]),
        );
    });
    h.case(
        "terminal/a path in another file's location is escaped",
        || {
            let src = Src::files(&[("a.en", "abc\n"), ("b\x07.en", "def\n")]);
            let text = src.one(warn(src.f(0).find("abc"), "p").with_help(Help::machine(
                "h",
                vec![Edit::replace(src.f(1).find("def"), "x")],
            )));
            assert!(text.contains(" --> b\\u{7}.en:1:1\n"), "{text}");
            assert_undisturbed(&text);
        },
    );
    h.case("terminal/a label's line break stays a continuation", || {
        let src = Src::new("a.en", "abc\n");
        same(
            &src.one(warn(src.find("abc"), "one\ntwo")),
            &lines(&[
                "warning[EN0430]: m",
                " --> a.en:1:1",
                "  |",
                "1 | abc",
                "  | ^^^ one",
                "  |     two",
            ]),
        );
    });
    h.case(
        "terminal/an entry's line break stays a continuation",
        || {
            let src = Src::new("a.en", "");
            same(
                &src.one(Diagnostic::spanless(Code::EN0430, "m").note("one\ntwo")),
                &lines(&["warning[EN0430]: m", "  = note: one", "          two"]),
            );
        },
    );
    h.case("terminal/a help's line break is no second line", || {
        let src = Src::new("a.en", "");
        same(
            &src.one(Diagnostic::spanless(Code::EN0430, "m").with_help(Help::text("one\ntwo"))),
            &lines(&["warning[EN0430]: m", "help: one\\ntwo"]),
        );
    });
    h.case("terminal/a bidi override is seen in the message", || {
        let src = Src::new("a.en", "");
        let text = src.one(Diagnostic::spanless(Code::EN0430, "\u{202e}evil"));
        same(&text, "warning[EN0430]: \\u{202e}evil\n");
    });
    // A source line, and the one line and annotation it must render to: each such
    // character takes one column as a space, so that a mark stays under its text.
    let source_lines: &[(&str, &str, &str, &str)] = &[
        ("a tab", "a\tb x\n", "1 | a b x", "  |     ^ p"),
        ("an escape", "a\x1bb x\n", "1 | a b x", "  |     ^ p"),
        (
            "a bidi override",
            "a\u{202e}b x\n",
            "1 | a b x",
            "  |     ^ p",
        ),
        (
            "a bidi isolate",
            "a\u{2066}b x\n",
            "1 | a b x",
            "  |     ^ p",
        ),
        (
            "a directional mark",
            "a\u{200f}b x\n",
            "1 | a b x",
            "  |     ^ p",
        ),
        (
            "a line separator",
            "a\u{2028}b x\n",
            "1 | a b x",
            "  |     ^ p",
        ),
        (
            "a paragraph separator",
            "a\u{2029}b x\n",
            "1 | a b x",
            "  |     ^ p",
        ),
    ];
    for &(name, text, line, annotation) in source_lines {
        h.case(format!("terminal/a source line with {name}"), move || {
            let src = Src::new("a.en", text);
            same(
                &src.one(warn(src.find("x"), "p")),
                &lines(&[
                    "warning[EN0430]: m",
                    " --> a.en:1:5",
                    "  |",
                    line,
                    annotation,
                ]),
            );
        });
    }
    h.case("terminal/an accented source line is not touched", || {
        let src = Src::new("a.en", "é x\n");
        let text = src.one(warn(src.find("x"), "p"));
        assert!(text.contains("1 | é x\n"), "{text}");
    });
    h.case("terminal/json carries the text as it is", || {
        let src = Src::new("a.en", "");
        let json = src.json(&[Diagnostic::spanless(Code::EN1301, "a\u{202e}b\x1bc")]);
        assert!(
            json.contains("\"message\":\"a\u{202e}b\\u001bc\""),
            "{json}"
        );
    });
}

fn shown_table(h: &mut Harness) {
    let rows: &[(&str, &str)] = &[
        ("", ""),
        ("plain", "plain"),
        ("two words", "two words"),
        ("é→β", "é→β"),
        ("\\", "\\"),
        ("a\u{200d}b", "a\u{200d}b"),
        ("\n", "\\n"),
        ("\r", "\\r"),
        ("\t", "\\t"),
        ("\x1b[31m", "\\u{1b}[31m"),
        ("\u{9b}31m", "\\u{9b}31m"),
        ("\u{61c}", "\\u{61c}"),
        ("\u{200e}\u{200f}", "\\u{200e}\\u{200f}"),
        ("\u{202a}\u{202e}", "\\u{202a}\\u{202e}"),
        ("\u{2066}\u{2069}", "\\u{2066}\\u{2069}"),
        ("\u{2028}\u{2029}", "\\u{2028}\\u{2029}"),
    ];
    for &(text, expected) in rows {
        h.case(format!("terminal/shown of {text:?}"), move || {
            assert_eq!(shown(text), expected);
        });
    }
    h.case("terminal/shown leaves the neighbours of each range", || {
        for c in [
            '\u{61b}', '\u{61d}', '\u{200d}', '\u{2010}', '\u{2027}', '\u{202f}', '\u{2065}',
            '\u{206a}',
        ] {
            assert_eq!(shown(&c.to_string()), c.to_string(), "{c:?}");
        }
    });
}

pub fn register(h: &mut Harness) {
    registers_every_place(h);
    exact_rows(h);
    shown_table(h);
}
