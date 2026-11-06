//! The written results of `for...of` programs that a review traced by hand and through
//! `rustc` and `node`. No checker exists before M2 and M3, so nothing else stops these
//! results drifting back to the wrong ones. Everything here reads `docs/`, and nothing
//! writes there.

use enrang_testkit::Harness;

use crate::docs::line_starting;
use crate::support::read;

fn testing() -> String {
    read("docs/TESTING.md")
}

/// The fixture and the result of a two-cell table row. A pipe inside code is written
/// `\|`, so only ` | ` separates the cells.
pub fn split_row(row: &str) -> (String, String) {
    let inner = row
        .strip_prefix("| ")
        .and_then(|rest| rest.strip_suffix(" |"))
        .unwrap_or_else(|| panic!("not a table row: {row}"));
    let (fixture, result) = inner
        .rsplit_once(" | ")
        .unwrap_or_else(|| panic!("not two cells: {row}"));
    (fixture.to_owned(), result.to_owned())
}

/// What the one table row of `doc` that holds `program` must give.
fn result_for(doc: &str, program: &str) -> String {
    let found: Vec<&str> = doc
        .lines()
        .filter(|line| line.starts_with('|') && line.contains(program))
        .collect();
    assert_eq!(found.len(), 1, "rows holding {program:?}: {found:?}");
    split_row(found[0]).1
}

/// The numbered steps of `check_for_of`, in ARCHITECTURE 4.
fn check_for_of_steps() -> String {
    let doc = read("docs/ARCHITECTURE.md");
    let after = doc
        .split("**`check_for_of`** runs in this order:")
        .nth(1)
        .expect("the list");
    let steps: Vec<&str> = after
        .lines()
        .skip_while(|line| line.is_empty())
        .take_while(|line| !line.is_empty())
        .collect();
    steps.join("\n")
}

pub fn register(h: &mut Harness) {
    h.case("for_of/SPEC 4.8 gives the state after the loop", || {
        let bullet = line_starting(&read("docs/SPEC.md"), "- **`for...of`.** ");
        let rule = "The state after the loop is the join of the head's exit edge with the state at every `break` of this loop, labelled or not";
        assert!(bullet.contains(rule), "{bullet}");
    });
    h.case("for_of/check_for_of records each break", || {
        let step = line_starting(&check_for_of_steps(), "5. ");
        assert!(
            step.contains(
                "each `continue` and each `break` of this loop, labelled or not, records its state"
            ),
            "{step}"
        );
    });
    h.case("for_of/check_for_of joins at the exit edge", || {
        let step = line_starting(&check_for_of_steps(), "7. ");
        assert!(step.contains("join of the head's exit edge"), "{step}");
        assert!(step.contains("never the head's state alone"), "{step}");
    });
    h.case("for_of/H24 covers the exit edge", || {
        let row = line_starting(&read("docs/SPEC.md"), "| H24 |");
        assert!(row.contains("exit edge"), "{row}");
    });
    h.case("for_of/M2's gate covers the state after the loop", || {
        let row = line_starting(&testing(), "| **M2** |");
        assert!(row.contains("the state after the loop"), "{row}");
    });
    let lost: &[(&str, &str, &str)] = &[
        (
            "`break`",
            "`for (const x of p) { p = null; break; } console.log(p.length);`",
            "EN0303; EN0401",
        ),
        (
            "`break outer`",
            "`outer: for (const a of p) { for (const x of p) { p = null; break outer; } } console.log(p.length);`",
            "EN0303; EN0401",
        ),
        (
            "a conditional `break`",
            "`for (const x of p) { if (c) { p = null; break; } } console.log(p.length);`",
            "EN0303 each",
        ),
        (
            "a fact restored only on the back edge",
            "`for (const x of p) { p = null; if (p == null) { break; } } console.log(p.length);`",
            "EN0303 each",
        ),
        (
            "`break outer` through a `while`",
            "`outer: for (const a of p) { while (c) { p = null; break outer; } }`",
            "EN0401 at the source",
        ),
        (
            "facts kept on every way out",
            "`for (const x of p) { if (c) { break; } } console.log(p.length);`",
            "Compiles with no warning",
        ),
        (
            "a `return`, which is no way out to the join",
            "`for (const x of p) { if (c) { p = null; return; } } console.log(p.length);`",
            "Compiles with no warning",
        ),
        (
            "`break outer`, which is no `break` of the inner loop",
            "`outer: for (const a of p) { for (const x of p) { if (c) { p = null; break outer; } } console.log(p.length); }`",
            "Compiles with no warning",
        ),
    ];
    for &(name, program, wanted) in lost {
        h.case(format!("for_of/reading `p` after {name}"), move || {
            let result = result_for(&testing(), program);
            assert!(result.starts_with(wanted), "{result}");
        });
    }
    h.case(
        "for_of/`keep` overwritten at once conflicts only at the head",
        || {
            let result = result_for(
                &testing(),
                "for (const x of &mut q) { keep = x; } use(keep);",
            );
            assert!(result.starts_with("One EN0708 at the source"), "{result}");
            assert!(result.contains("twin E0502 only"), "{result}");
        },
    );
    h.case("for_of/`keep` kept conditionally conflicts at both", || {
        let result = result_for(
            &testing(),
            "for (const x of &mut q) { if (c) { keep = x; } } use(keep);",
        );
        assert!(result.starts_with("One EN0707"), "{result}");
        assert!(result.contains("twin E0502 and E0499"), "{result}");
    });
    h.case(
        "for_of/ARCHITECTURE's Ref-wins example has both conflicts",
        || {
            let line = line_starting(
                &read("docs/ARCHITECTURE.md"),
                "- Conflicts are keyed on (loan, access span).",
            );
            assert!(
                line.contains(
                    "for (const x of &mut q) { if (c) { keep = x; } } use(keep);` is one EN0707"
                ),
                "{line}"
            );
            assert!(line.contains("one EN0708"), "{line}");
        },
    );
    h.case(
        "for_of/a sibling field moved every turn is rejected",
        || {
            let doc = testing();
            assert!(!doc.contains("a sibling field move"));
            let result = result_for(&doc, "`take(h.other);` with no reinitialisation");
            assert!(result.contains("EN0611 at the move"), "{result}");
            assert!(result.contains("twin E0382"), "{result}");
        },
    );
    h.case(
        "for_of/a sibling field move that is made good compiles",
        || {
            let result = result_for(&testing(), "`take(h.other); h.other = [];`");
            assert!(result.starts_with("Compiles with no warning"), "{result}");
            let again = result_for(&testing(), "`take(h.other); break;`");
            assert_eq!(result, again);
        },
    );
    h.case(
        "for_of/SPEC 5.6 claims JS parity only where JS agrees",
        || {
            let line = line_starting(
                &read("docs/SPEC.md"),
                "**A path source holds no borrow between turns.**",
            );
            let claim = line
                .split(". ")
                .find(|sentence| sentence.contains("as JS does"))
                .expect("the claim");
            assert!(!claim.contains("assign"), "{claim}");
            assert!(line.contains("Assignment differs from JS"), "{line}");
        },
    );
    h.case(
        "for_of/assignment has a fixture that shows the difference",
        || {
            let result = result_for(&testing(), "{ console.log(x); q = []; }");
            assert!(result.starts_with("Warns"), "{result}");
            assert!(result.contains("JS prints `1 2 3`"), "{result}");
        },
    );
    h.case(
        "for_of/DEV_RUNTIME keeps the reference rule for a path source",
        || {
            let dev = read("docs/DEV_RUNTIME.md");
            for wrong in [
                "keeps no reference between turns",
                "these limits do not reach it",
            ] {
                assert!(!dev.contains(wrong), "{wrong}");
            }
            let line = line_starting(&dev, "**Frames in `for...of` loops.**");
            assert!(line.contains("adds no hidden reference"), "{line}");
            assert!(
                line.contains("`const r = &queue; for (const job of r)` refuses"),
                "{line}"
            );
        },
    );
    h.case(
        "for_of/ADV rows cover both sides of the reference rule",
        || {
            let dev = read("docs/DEV_RUNTIME.md");
            let refused = line_starting(&dev, "| 51 |");
            assert!(
                refused.contains("`const r = &queue; for (const job of r)`"),
                "{refused}"
            );
            assert!(refused.contains("`longest = x`"), "{refused}");
            assert!(refused.contains("Replacement refused"), "{refused}");
            let taken = line_starting(&dev, "| 52 |");
            assert!(taken.contains("Replacement can apply"), "{taken}");
        },
    );
    let rows: &[(&str, &str, &str)] = &[
        ("| `a` | EN1 |", "`a`", "EN1"),
        ("| `a \\| b` | EN1 |", "`a \\| b`", "EN1"),
        ("| `a` | b \\| c |", "`a`", "b \\| c"),
    ];
    for &(row, fixture, result) in rows {
        h.case(format!("for_of/splits {row:?}"), move || {
            assert_eq!(split_row(row), (fixture.to_owned(), result.to_owned()));
        });
    }
}
