//! The gap rule: unlabelled lines between two labelled ones print when there are at
//! most two; otherwise a line holding only `...` replaces them.

use enrang_testkit::Harness;

use crate::support::{Src, lines, numbered_source, render_table, row, same, warn};

/// Gaps from nothing to well past the limit, at several places in the number range.
fn every_gap_length(h: &mut Harness) {
    for gap in 0u32..=12 {
        for first in [1u32, 8, 97] {
            h.case(format!("gaps/{gap} lines after line {first}"), move || {
                let second = first + gap + 1;
                let src = Src::new("a.en", &numbered_source(second + 2));
                let diag = warn(src.on_line(second, "l"), "p")
                    .with_secondary(src.on_line(first, "l"), "s");
                let width = second.to_string().len();
                let pad = " ".repeat(width);
                let mut expected = format!(
                    "warning[EN0430]: m\n{pad}--> a.en:{second}:1\n{pad} |\n\
                     {first:>width$} | l{first}\n{pad} | - s\n"
                );
                if gap <= 2 {
                    for line in first + 1..second {
                        expected.push_str(&format!("{line:>width$} | l{line}\n"));
                    }
                } else {
                    expected.push_str("...\n");
                }
                expected.push_str(&format!("{second:>width$} | l{second}\n{pad} | ^ p\n"));
                same(&src.one(diag), &expected);
            });
        }
    }
}

fn three_labels(h: &mut Harness) {
    let table: [(&str, [u32; 3], &[&str]); 7] = [
        (
            "both gaps printed",
            [1, 3, 6],
            &[
                "warning[EN0430]: m",
                " --> a.en:1:1",
                "  |",
                "1 | l1",
                "  | ^ p",
                "2 | l2",
                "3 | l3",
                "  | - s",
                "4 | l4",
                "5 | l5",
                "6 | l6",
                "  | - t",
            ],
        ),
        (
            "first gap elided, second printed",
            [1, 5, 7],
            &[
                "warning[EN0430]: m",
                " --> a.en:1:1",
                "  |",
                "1 | l1",
                "  | ^ p",
                "...",
                "5 | l5",
                "  | - s",
                "6 | l6",
                "7 | l7",
                "  | - t",
            ],
        ),
        (
            "first printed, second elided",
            [1, 3, 8],
            &[
                "warning[EN0430]: m",
                " --> a.en:1:1",
                "  |",
                "1 | l1",
                "  | ^ p",
                "2 | l2",
                "3 | l3",
                "  | - s",
                "...",
                "8 | l8",
                "  | - t",
            ],
        ),
        (
            "both elided",
            [1, 5, 9],
            &[
                "warning[EN0430]: m",
                " --> a.en:1:1",
                "  |",
                "1 | l1",
                "  | ^ p",
                "...",
                "5 | l5",
                "  | - s",
                "...",
                "9 | l9",
                "  | - t",
            ],
        ),
        (
            "all adjacent",
            [2, 3, 4],
            &[
                "warning[EN0430]: m",
                " --> a.en:2:1",
                "  |",
                "2 | l2",
                "  | ^ p",
                "3 | l3",
                "  | - s",
                "4 | l4",
                "  | - t",
            ],
        ),
        (
            "the primary in the middle of the snippet",
            [5, 1, 9],
            &[
                "warning[EN0430]: m",
                " --> a.en:5:1",
                "  |",
                "1 | l1",
                "  | - s",
                "...",
                "5 | l5",
                "  | ^ p",
                "...",
                "9 | l9",
                "  | - t",
            ],
        ),
        (
            "the primary last, secondaries given out of order",
            [9, 6, 1],
            &[
                "warning[EN0430]: m",
                " --> a.en:9:1",
                "  |",
                "1 | l1",
                "  | - t",
                "...",
                "6 | l6",
                "  | - s",
                "7 | l7",
                "8 | l8",
                "9 | l9",
                "  | ^ p",
            ],
        ),
    ];
    for (name, [primary, s, t], expected) in table {
        h.case(format!("gaps/three labels/{name}"), move || {
            let src = Src::new("a.en", &numbered_source(9));
            let diag = warn(src.on_line(primary, "l"), "p")
                .with_secondary(src.on_line(s, "l"), "s")
                .with_secondary(src.on_line(t, "l"), "t");
            same(&src.one(diag), &lines(expected));
        });
    }
}

fn shapes(h: &mut Harness) {
    render_table(
        h,
        "gaps/shapes",
        vec![
            row(
                "a blank line in a gap has no trailing space",
                "a\n\nb\n",
                |s| vec![warn(s.find("b"), "p").with_secondary(s.find("a"), "s")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:3:1",
                    "  |",
                    "1 | a",
                    "  | - s",
                    "2 |",
                    "3 | b",
                    "  | ^ p",
                ],
            ),
            row(
                "two blank lines still print",
                "a\n\n\nb\n",
                |s| vec![warn(s.find("b"), "p").with_secondary(s.find("a"), "s")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:4:1",
                    "  |",
                    "1 | a",
                    "  | - s",
                    "2 |",
                    "3 |",
                    "4 | b",
                    "  | ^ p",
                ],
            ),
            row(
                "three blank lines elide",
                "a\n\n\n\nb\n",
                |s| vec![warn(s.find("b"), "p").with_secondary(s.find("a"), "s")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:5:1",
                    "  |",
                    "1 | a",
                    "  | - s",
                    "...",
                    "5 | b",
                    "  | ^ p",
                ],
            ),
            row(
                "the `...` line has no gutter at any width",
                "a\n\n\n\n\n\n\n\n\n\nb\n",
                |s| vec![warn(s.find("b"), "p").with_secondary(s.find("a"), "s")],
                &[
                    "warning[EN0430]: m",
                    "  --> a.en:11:1",
                    "   |",
                    " 1 | a",
                    "   | - s",
                    "...",
                    "11 | b",
                    "   | ^ p",
                ],
            ),
            row(
                "a tab in an unlabelled line renders as one space",
                "a\n\tx\nb\n",
                |s| vec![warn(s.find("b"), "p").with_secondary(s.find("a"), "s")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:3:1",
                    "  |",
                    "1 | a",
                    "  | - s",
                    "2 |  x",
                    "3 | b",
                    "  | ^ p",
                ],
            ),
            row(
                "a gap crossing a digit boundary keeps numbers aligned",
                "1\n2\n3\n4\n5\n6\n7\n8\n9\n10\n11\n",
                |s| vec![warn(s.on_line(11, "11"), "p").with_secondary(s.on_line(9, "9"), "s")],
                &[
                    "warning[EN0430]: m",
                    "  --> a.en:11:1",
                    "   |",
                    " 9 | 9",
                    "   | - s",
                    "10 | 10",
                    "11 | 11",
                    "   | ^^ p",
                ],
            ),
            row(
                "nothing is printed before the first or after the last label",
                "a\nb\nc\nd\ne\n",
                |s| vec![warn(s.find("c"), "p")],
                &[
                    "warning[EN0430]: m",
                    " --> a.en:3:1",
                    "  |",
                    "3 | c",
                    "  | ^ p",
                ],
            ),
        ],
    );
}

pub fn register(h: &mut Harness) {
    every_gap_length(h);
    three_labels(h);
    shapes(h);
}
