//! Colour is off unless asked for, and asked for it changes nothing but escapes.

use enrang_diag::{Code, Diagnostic, Edit, Help, RenderOpts};
use enrang_testkit::Harness;

use crate::support::{Src, err, same, strip_ansi, warn};

const ESC: char = '\x1b';

fn sample(src: &Src) -> Vec<Diagnostic> {
    vec![
        err(src.find("abc"), "p")
            .with_secondary(src.find("def"), "s")
            .note("n\nm")
            .with_help(Help::text("h"))
            .with_help(Help::machine(
                "i",
                vec![
                    Edit::replace(src.find("abc"), "x"),
                    Edit::insert(src.line_end(1), "y"),
                    Edit::insert(src.line_start(2), "z\n"),
                ],
            )),
        warn(src.find("def"), "q").with_help(Help::machine(
            "j",
            vec![
                Edit::replace(src.whole_line(1), "1"),
                Edit::replace(src.whole_line(2), "2"),
            ],
        )),
        Diagnostic::new(Code::T0001, "t", src.find("ghi"), "r"),
        Diagnostic::spanless(Code::EN1301, "u"),
    ]
}

const SOURCE: &str = "abc\ndef\n\n\n\n\n\nghi\n";

pub fn register(h: &mut Harness) {
    h.case("color/default options have none", || {
        assert_eq!(RenderOpts::default(), RenderOpts { color: false });
        let src = Src::new("a.en", SOURCE);
        assert!(!src.render(&sample(&src)).contains(ESC));
    });
    h.case("color/asked for, it is there", || {
        let src = Src::new("a.en", SOURCE);
        assert!(src.render_colored(&sample(&src)).contains(ESC));
    });
    h.case("color/removing the escapes gives the plain bytes", || {
        let src = Src::new("a.en", SOURCE);
        let diags = sample(&src);
        same(
            &strip_ansi(&src.render_colored(&diags)),
            &src.render(&diags),
        );
    });
    h.case(
        "color/the escape sequences are SGR only and all reset",
        || {
            let src = Src::new("a.en", SOURCE);
            let colored = src.render_colored(&sample(&src));
            let opens = colored.matches(ESC).count();
            let resets = colored.matches("\x1b[0m").count();
            assert_eq!(opens, resets * 2, "every paint is closed");
            strip_ansi(&colored);
        },
    );
    let lines_by_severity = [
        (
            "error",
            Code::EN0301,
            "\x1b[1;31merror[EN0301]\x1b[0m: \x1b[1mm\x1b[0m\n",
        ),
        (
            "warning",
            Code::EN0430,
            "\x1b[1;33mwarning[EN0430]\x1b[0m: \x1b[1mm\x1b[0m\n",
        ),
        (
            "fail",
            Code::T0001,
            "\x1b[1;35mfail[T0001]\x1b[0m: \x1b[1mm\x1b[0m\n",
        ),
    ];
    for (name, code, expected) in lines_by_severity {
        h.case(format!("color/the header of a {name}"), move || {
            let src = Src::new("a.en", "x\n");
            let colored = src.render_colored(&[Diagnostic::spanless(code, "m")]);
            assert!(colored.starts_with(expected), "{colored:?}");
        });
    }
    h.case("color/a primary mark takes the severity's colour", || {
        let src = Src::new("a.en", "x\n");
        let colored = src.render_colored(&[warn(src.find("x"), "p")]);
        assert!(
            colored.contains("\x1b[1;33m^\x1b[0m \x1b[1;33mp\x1b[0m"),
            "{colored:?}"
        );
    });
    h.case("color/a secondary mark is blue", || {
        let src = Src::new("a.en", "x\n");
        let colored =
            src.render_colored(&[warn(src.find("x"), "p").with_secondary(src.find("x"), "s")]);
        assert!(
            colored.contains("\x1b[1;34m-\x1b[0m \x1b[1;34ms\x1b[0m"),
            "{colored:?}"
        );
    });
    h.case("color/`+` is green and `~` is yellow", || {
        let src = Src::new("a.en", "ab\n");
        let diag = warn(src.find("a"), "p").with_help(Help::machine(
            "h",
            vec![
                Edit::insert(src.find("a").lo, "x"),
                Edit::replace(src.find("b"), "y"),
            ],
        ));
        let colored = src.render_colored(&[diag]);
        assert!(colored.contains("\x1b[32m+\x1b[0m"), "{colored:?}");
        assert!(colored.contains("\x1b[33m~\x1b[0m"), "{colored:?}");
    });
    h.case("color/a marks run keeps its plain spaces", || {
        let src = Src::new("a.en", "a b\n");
        let diag = warn(src.find("a"), "p").with_help(Help::machine(
            "h",
            vec![
                Edit::replace(src.find("a"), "x"),
                Edit::replace(src.find("b"), "y"),
            ],
        ));
        let colored = src.render_colored(&[diag]);
        assert!(
            colored.contains("\x1b[33m~\x1b[0m \x1b[33m~\x1b[0m"),
            "{colored:?}"
        );
    });
    h.case("color/the final line paints its word", || {
        let src = Src::new("a.en", "x\n");
        let colored = src.render_colored(&[err(src.find("x"), "p")]);
        assert!(
            colored.ends_with("\x1b[1;31merror\x1b[0m: aborting due to 1 previous error\n"),
            "{colored:?}"
        );
    });
    h.case("color/source text is never painted", || {
        let src = Src::new("a.en", "x\n");
        let colored = src.render_colored(&[warn(src.find("x"), "p")]);
        assert!(colored.contains(" x\n"), "{colored:?}");
    });
    h.case("color/a note paints its word in bold", || {
        let src = Src::new("a.en", "x\n");
        let colored = src.render_colored(&[Diagnostic::bare_note(Code::EN0909, "m")]);
        assert_eq!(colored, "\x1b[1mnote\x1b[0m: \x1b[1mm\x1b[0m\n");
    });
    h.case("color/every line of a label is painted", || {
        let src = Src::new("a.en", "abc\n");
        let colored = src.render_colored(&[err(src.find("abc"), "first\nsecond")]);
        assert!(colored.contains("\x1b[1;31mfirst\x1b[0m"), "{colored:?}");
        assert!(colored.contains("\x1b[1;31msecond\x1b[0m"), "{colored:?}");
        same(
            &strip_ansi(&colored),
            &src.render(&[err(src.find("abc"), "first\nsecond")]),
        );
    });
    h.case("color/an empty message gets no escape pair", || {
        let src = Src::new("a.en", "x\n");
        let colored = src.render_colored(&[Diagnostic::spanless(Code::EN1301, "")]);
        assert!(!colored.contains("\x1b[1m\x1b[0m"), "{colored:?}");
        assert!(
            colored.starts_with("\x1b[1;31merror[EN1301]\x1b[0m: \n"),
            "{colored:?}"
        );
    });
    h.case("color/a quoted escape is not an escape", || {
        let src = Src::new("a.en", "x\n");
        let colored = src.render_colored(&[Diagnostic::spanless(Code::EN1301, "a\x1b[2Jb")]);
        assert!(colored.contains("a\\u{1b}[2Jb"), "{colored:?}");
        assert_eq!(
            strip_ansi(&colored),
            src.render(&[Diagnostic::spanless(Code::EN1301, "a\x1b[2Jb")])
        );
    });
    h.case("color/an empty label paints nothing", || {
        let src = Src::new("a.en", "x\n");
        let colored = src.render_colored(&[warn(src.find("x"), "")]);
        assert!(colored.ends_with("\x1b[1;33m^\x1b[0m\n"), "{colored:?}");
    });
}
