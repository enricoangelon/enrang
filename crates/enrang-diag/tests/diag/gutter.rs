//! Gutter width: the digit count of the largest line number shown anywhere in a
//! diagnostic, snippets and suggestions alike, and right-aligned numbers.

use enrang_diag::{Diagnostic, Edit, Help};
use enrang_testkit::Harness;

use crate::support::{Src, err, lines, numbered_source, same, warn};

/// Line numbers around every digit boundary up to five digits.
const LINE_NUMBERS: [u32; 15] = [
    1, 2, 9, 10, 11, 99, 100, 101, 999, 1000, 1001, 9999, 10000, 10001, 12345,
];

fn register_single_line(h: &mut Harness) {
    for line in LINE_NUMBERS {
        h.case(format!("gutter/one label on line {line}"), move || {
            let src = Src::new("a.en", &numbered_source(line + 1));
            let width = line.to_string().len();
            let pad = " ".repeat(width);
            let expected = format!(
                "warning[EN0430]: m\n{pad}--> a.en:{line}:1\n{pad} |\n{line} | l{line}\n{pad} | {} p\n",
                "^".repeat(width + 1),
            );
            same(&src.one(warn(src.on_line(line, &format!("l{line}")), "p")), &expected);
        });
    }
}

/// Primary and secondary lines, in either order: the wider number sets the gutter
/// and the narrower one is right-aligned to it.
fn register_two_lines(h: &mut Harness) {
    let pairs: [(u32, u32); 12] = [
        (9, 10),
        (10, 9),
        (99, 100),
        (100, 99),
        (999, 1000),
        (1000, 999),
        (8, 11),
        (5, 120),
        (120, 5),
        (9, 1000),
        (98, 101),
        (10, 13),
    ];
    for (primary, secondary) in pairs {
        h.case(
            format!("gutter/primary {primary} secondary {secondary}"),
            move || {
                let source = numbered_source(primary.max(secondary));
                let src = Src::new("a.en", &source);
                let diag = warn(src.on_line(primary, "l"), "p")
                    .with_secondary(src.on_line(secondary, "l"), "s");
                let width = primary.max(secondary).to_string().len();
                let pad = " ".repeat(width);
                let (first, second) = (primary.min(secondary), primary.max(secondary));
                let annotation = |line: u32| {
                    if line == primary {
                        format!("{pad} | ^ p\n")
                    } else {
                        format!("{pad} | - s\n")
                    }
                };
                let gap = second - first - 1;
                let between = if gap > 2 {
                    "...\n".to_owned()
                } else {
                    (first + 1..second)
                        .map(|n| format!("{n:>width$} | l{n}\n"))
                        .collect()
                };
                let expected = format!(
                    "warning[EN0430]: m\n{pad}--> a.en:{primary}:1\n{pad} |\n\
                 {first:>width$} | l{first}\n{}{between}{second:>width$} | l{second}\n{}",
                    annotation(first),
                    annotation(second),
                );
                same(&src.one(diag), &expected);
            },
        );
    }
}

/// A suggestion alone can widen the gutter, as G12 does.
fn register_help_widens(h: &mut Harness) {
    let cases: [(u32, u32); 7] = [
        (8, 11),
        (9, 10),
        (99, 100),
        (5, 1000),
        (1, 10),
        (1, 100),
        (1000, 10000),
    ];
    for (primary, target) in cases {
        h.case(
            format!("gutter/help on line {target} widens line {primary}"),
            move || {
                let source = numbered_source(primary.max(target));
                let src = Src::new("a.en", &source);
                let diag = warn(src.on_line(primary, "l"), "p").with_help(Help::suggest(
                    "h",
                    vec![Edit::insert(src.line_start(target), "new\n")],
                ));
                let width = target.to_string().len();
                let pad = " ".repeat(width);
                let expected = format!(
                    "warning[EN0430]: m\n{pad}--> a.en:{primary}:1\n{pad} |\n\
                 {primary:>width$} | l{primary}\n{pad} | ^ p\n{pad} |\nhelp: h\n{pad} |\n\
                 {target:>width$} + new\n"
                );
                same(&src.one(diag), &expected);
            },
        );
    }
}

/// Lines of inserted text count at the number they will occupy.
fn register_inserted_numbers(h: &mut Harness) {
    h.case("gutter/the second inserted line widens it", || {
        let src = Src::new("a.en", &numbered_source(9));
        let diag = warn(src.on_line(9, "l"), "p").with_help(Help::suggest(
            "h",
            vec![Edit::insert(src.line_start(9), "one\ntwo\n")],
        ));
        same(
            &src.one(diag),
            &lines(&[
                "warning[EN0430]: m",
                "  --> a.en:9:1",
                "   |",
                " 9 | l9",
                "   | ^ p",
                "   |",
                "help: h",
                "   |",
                " 9 + one",
                "10 + two",
            ]),
        );
    });
    h.case("gutter/a line inserted after line 9 is line 10", || {
        let src = Src::new("a.en", "l1\nl2\nl3\nl4\nl5\nl6\nl7\nl8\nl9");
        let diag = warn(src.on_line(9, "l"), "p").with_help(Help::suggest(
            "h",
            vec![Edit::insert(src.line_end(9), "\nnew")],
        ));
        same(
            &src.one(diag),
            &lines(&[
                "warning[EN0430]: m",
                "  --> a.en:9:1",
                "   |",
                " 9 | l9",
                "   | ^ p",
                "   |",
                "help: h",
                "   |",
                "10 + new",
            ]),
        );
    });
    h.case(
        "gutter/a multi-line replacement counts its last line",
        || {
            let src = Src::new("a.en", &numbered_source(9));
            let diag = warn(src.on_line(9, "l9"), "p").with_help(Help::suggest(
                "h",
                vec![Edit::replace(src.on_line(9, "l9"), "a\nb")],
            ));
            same(
                &src.one(diag),
                &lines(&[
                    "warning[EN0430]: m",
                    "  --> a.en:9:1",
                    "   |",
                    " 9 | l9",
                    "   | ^^ p",
                    "   |",
                    "help: h",
                    "   |",
                    " 9 ~ a",
                    "10 ~ b",
                ]),
            );
        },
    );
}

fn register_padding(h: &mut Harness) {
    for line in [1u32, 10, 100, 1000] {
        h.case(
            format!("gutter/`=` lines up with `|` at line {line}"),
            move || {
                let src = Src::new("a.en", &numbered_source(line));
                let diag = err(src.on_line(line, "l"), "p")
                    .note("n")
                    .why("w")
                    .rule("r")
                    .from_typescript("t")
                    .with_help(Help::text("h"));
                let rendered = src.one(diag);
                let width = line.to_string().len();
                let bar_column = width + 1;
                for text in rendered.lines() {
                    let is_gutter = text.chars().nth(bar_column) == Some('|');
                    let is_entry = text.chars().nth(bar_column) == Some('=');
                    let free = text.starts_with("error")
                        || text.starts_with("help:")
                        || text.contains("-->")
                        || text.is_empty();
                    assert!(is_gutter || is_entry || free, "{text:?} in\n{rendered}");
                }
                let entries = rendered.lines().filter(|text| text.contains(" = ")).count();
                assert_eq!(entries, 5, "{rendered}");
            },
        );
    }
    h.case("gutter/each diagnostic has its own width", || {
        let src = Src::new("a.en", &numbered_source(100));
        let diags: Vec<Diagnostic> = vec![
            warn(src.on_line(5, "l"), "p"),
            warn(src.on_line(100, "l"), "p"),
            warn(src.on_line(50, "l"), "p"),
        ];
        same(
            &src.render(&diags),
            &lines(&[
                "warning[EN0430]: m",
                " --> a.en:5:1",
                "  |",
                "5 | l5",
                "  | ^ p",
                "",
                "warning[EN0430]: m",
                "   --> a.en:100:1",
                "    |",
                "100 | l100",
                "    | ^ p",
                "",
                "warning[EN0430]: m",
                "  --> a.en:50:1",
                "   |",
                "50 | l50",
                "   | ^ p",
            ]),
        );
    });
    h.case(
        "gutter/`...` hides lines and leaves the width to the shown ones",
        || {
            let src = Src::new("a.en", &numbered_source(12));
            let diag = warn(src.on_line(9, "l"), "p").with_secondary(src.on_line(5, "l"), "s");
            same(
                &src.one(diag),
                &lines(&[
                    "warning[EN0430]: m",
                    " --> a.en:9:1",
                    "  |",
                    "5 | l5",
                    "  | - s",
                    "...",
                    "9 | l9",
                    "  | ^ p",
                ]),
            );
        },
    );
    h.case(
        "gutter/a line of the file that is not shown does not count",
        || {
            let src = Src::new("a.en", &numbered_source(5000));
            same(
                &src.one(warn(src.on_line(3, "l"), "p")),
                &lines(&[
                    "warning[EN0430]: m",
                    " --> a.en:3:1",
                    "  |",
                    "3 | l3",
                    "  | ^ p",
                ]),
            );
        },
    );
    h.case(
        "gutter/with no line numbers `=` stands where one digit puts it",
        || {
            let src = Src::new("a.en", "x\n");
            let diag = Diagnostic::spanless(enrang_diag::Code::EN1302, "m")
                .note("n")
                .with_help(Help::text("h"));
            same(
                &src.one(diag),
                &lines(&[
                    "error[EN1302]: m",
                    "  = note: n",
                    "help: h",
                    "  = explain: run `enrang explain EN1302`",
                    "",
                    "error: aborting due to 1 previous error",
                ]),
            );
        },
    );
}

pub fn register(h: &mut Harness) {
    register_single_line(h);
    register_two_lines(h);
    register_help_widens(h);
    register_inserted_numbers(h);
    register_padding(h);
}
