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
            "`for (const x of &p) { p = null; break; } console.log(p.length());`",
            "EN0303; EN0401",
        ),
        (
            "`break outer`",
            "`outer: for (const a of &p) { for (const x of &p) { p = null; break outer; } } console.log(p.length());`",
            "EN0303; EN0401",
        ),
        (
            "a conditional `break`",
            "`for (const x of &p) { if (c) { p = null; break; } } console.log(p.length());`",
            "EN0303 each",
        ),
        (
            "a fact restored only on the back edge",
            "`for (const x of &p) { p = null; if (p == null) { break; } } console.log(p.length());`",
            "EN0303 each",
        ),
        (
            "`break outer` through a `while`",
            "`outer: for (const a of &p) { while (c) { p = null; break outer; } }`",
            "Compiles with no warning",
        ),
        (
            "facts kept on every way out",
            "`for (const x of &p) { if (c) { break; } } console.log(p.length());`",
            "Compiles with no warning",
        ),
        (
            "a `return`, which is no way out to the join",
            "`for (const x of &p) { if (c) { p = null; return; } } console.log(p.length());`",
            "Compiles with no warning",
        ),
        (
            "`break outer`, which is no `break` of the inner loop",
            "`outer: for (const a of &p) { for (const x of &p) { if (c) { p = null; break outer; } } console.log(p.length()); }`",
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
        "for_of/`keep` overwritten at once compiles and writes the last element",
        || {
            let result = result_for(&testing(), "for (const x of &q) { keep = x; } use(keep);");
            assert!(result.starts_with("Compiles, "), "{result}");
            assert!(
                result.contains("over `q = [1, 5, 3, 7]` prints `[1, 5, 3, 0]`"),
                "{result}"
            );
            assert!(result.contains("twin over `iter_mut` agrees"), "{result}");
        },
    );
    h.case("for_of/`keep` kept conditionally compiles", || {
        let result = result_for(
            &testing(),
            "for (const x of &q) { if (c) { keep = x; } } use(keep);",
        );
        assert!(result.starts_with("Compile, "), "{result}");
        assert!(result.contains("the first prints `[9, 9, 3]`"), "{result}");
        assert!(result.contains("twins over `iter_mut` agree"), "{result}");
        assert!(
            result.contains(
                "every turn binds at the loop's one bind site, whose loans the loop's own head and bind skip"
            ),
            "{result}"
        );
    });
    h.case(
        "for_of/a kept binding still conflicts with another access to `q`",
        || {
            let result = result_for(&testing(), "`OQ26-keys`");
            assert!(
                result.starts_with("EN0708 at the second loop's `&q`; EN0708 at `q[0]`"),
                "{result}"
            );
            assert!(result.contains("twin E0502 each"), "{result}");
        },
    );
    h.case(
        "for_of/ARCHITECTURE's Ref-wins example is one code at the second loop",
        || {
            let line = line_starting(
                &read("docs/ARCHITECTURE.md"),
                "- Conflicts are keyed on (loan, access span).",
            );
            for rule in [
                "the `Ref` wins, then the hold, which gives EN0706, EN0707 or EN0708 by mode, and never a second code",
                "for (const x of &q) { if (c) { keep = x; } } for (const y of &q) { console.log(y); } use(keep);` is one EN0708 at the second loop's source",
                "The first loop alone compiles",
            ] {
                assert!(line.contains(rule), "{rule}: {line}");
            }
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
        "for_of/SPEC 5.6 holds the source while a next head is reachable",
        || {
            let line = line_starting(&read("docs/SPEC.md"), "**The loop holds its source (N9).**");
            assert!(
                line.contains("so they are live while a next head is reachable"),
                "{line}"
            );
            let (rejected, valid) = line
                .split_once(" are rejected, while ")
                .expect("the rejected and the valid forms");
            let rejected = rejected
                .rsplit_once(": ")
                .expect("the list of rejected forms")
                .1;
            for form in [
                "`q = []`",
                "`q.push(9)`",
                "`q[0] = 9`",
                "`q = []; continue;`",
            ] {
                assert!(rejected.contains(form), "{form} in {rejected}");
            }
            let valid = valid
                .split_once(", because no later turn exists")
                .expect("the reason")
                .0;
            for form in [
                "`q = []; break;`",
                "`q = []; return;`",
                "`q.push(1); break;`",
            ] {
                assert!(valid.contains(form), "{form} in {valid}");
            }
            assert!(!valid.contains("continue"), "{valid}");
            assert!(
                line.contains(
                    "`take(q);` and `take(q); q = [];` are errors and `take(q); break;` is accepted"
                ),
                "{line}"
            );
            assert!(
                line.contains("also when a written loop variable has made the hold exclusive"),
                "{line}"
            );
            let doc = testing();
            let changed = result_for(&doc, "`q[0] = 9`, `q = []; continue;`");
            assert!(changed.starts_with("EN0706 each"), "{changed}");
            let left = result_for(
                &doc,
                "`q.push(1); break;`, `q = []; break;`, `q.clear(); return;`, `q = []; return;`",
            );
            assert!(left.starts_with("Compiles"), "{left}");
        },
    );
    h.case(
        "for_of/SPEC 5.6 claims JS parity only where JS agrees",
        || {
            let spec = read("docs/SPEC.md");
            let section = spec
                .split("\n### 5.6 ")
                .nth(1)
                .and_then(|rest| rest.split("\n### 5.7 ").next())
                .expect("SPEC 5.6");
            for gone in [
                "holds no borrow between turns",
                "as JS does",
                "Assignment differs from JS",
                "EN0719",
            ] {
                assert!(!section.contains(gone), "{gone}");
            }
            let line = line_starting(&spec, "So `for (const job of &queue) { queue.push(\"retry\"); }`");
            let claim = line
                .split(". ")
                .find(|sentence| sentence.contains("prints"))
                .expect("the claim");
            assert!(
                claim.contains(
                    "`let q = [1, 2, 3]; for (const x of q.clone()) { console.log(x); q = []; }` prints `1 2 3`"
                ),
                "{claim}"
            );
            assert!(claim.contains("and so does the same loop over `[...q]`"), "{claim}");
            assert!(!claim.contains("of &q"), "{claim}");
        },
    );
    h.case(
        "for_of/assignment has a fixture that shows the difference",
        || {
            let result = result_for(
                &testing(),
                "`let q = [1, 2, 3]; for (const x of &q) { console.log(x); q = []; }`",
            );
            assert!(
                result.starts_with("EN0706, `cannot reassign `q` during iteration` (G21)"),
                "{result}"
            );
            assert!(
                result.contains("Over `q.clone()` or `[...q]` both compile and print `1 2 3`"),
                "{result}"
            );
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
