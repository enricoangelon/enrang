//! `did_you_mean`: Damerau-Levenshtein with threshold `max(1, len / 3)`.

use enrang_diag::{Code, did_you_mean};
use enrang_testkit::Harness;

fn thresholds(h: &mut Harness) {
    // (name length, the largest distance that is still suggested)
    let table: [(usize, usize); 13] = [
        (1, 1),
        (2, 1),
        (3, 1),
        (4, 1),
        (5, 1),
        (6, 2),
        (7, 2),
        (8, 2),
        (9, 3),
        (11, 3),
        (12, 4),
        (15, 5),
        (30, 10),
    ];
    for (len, limit) in table {
        h.case(
            format!("did you mean/length {len} allows {limit} edits"),
            move || {
                let name = "a".repeat(len);
                // Appending changes the length, so it tests the distance, not substitution.
                let within = format!("{name}{}", "b".repeat(limit));
                let beyond = format!("{name}{}", "b".repeat(limit + 1));
                assert_eq!(
                    did_you_mean(&name, &[within.as_str()]),
                    Some(within.as_str())
                );
                assert_eq!(did_you_mean(&name, &[beyond.as_str()]), None);
            },
        );
        h.case(
            format!("did you mean/length {len} by substitution"),
            move || {
                let name = "a".repeat(len);
                let mut within = "b".repeat(limit);
                within.push_str(&"a".repeat(len.saturating_sub(limit)));
                assert_eq!(
                    did_you_mean(&name, &[within.as_str()]),
                    Some(within.as_str())
                );
                if limit < len {
                    let mut beyond = "b".repeat(limit + 1);
                    beyond.push_str(&"a".repeat(len - limit - 1));
                    assert_eq!(did_you_mean(&name, &[beyond.as_str()]), None);
                }
            },
        );
    }
}

fn table(h: &mut Harness) {
    type Row = (&'static str, &'static [&'static str], Option<&'static str>);
    let rows: [(&str, Row); 26] = [
        ("G06", ("totl", &["total"], Some("total"))),
        ("a deletion", ("totals", &["total"], Some("total"))),
        ("a substitution", ("tatal", &["total"], Some("total"))),
        ("a transposition", ("toatl", &["total"], Some("total"))),
        (
            "a transposition at the start",
            ("otal", &["toal"], Some("toal")),
        ),
        (
            "a transposition at the end",
            ("tota", &["toat"], Some("toat")),
        ),
        ("the exact name", ("total", &["total"], Some("total"))),
        ("too far", ("abc", &["xyz"], None)),
        (
            "one short of the threshold is enough",
            ("abcdef", &["abcxyz"], None),
        ),
        ("no candidates", ("abc", &[], None)),
        ("an empty name", ("", &["a"], None)),
        ("an empty candidate", ("a", &[""], None)),
        (
            "an empty candidate beside a good one",
            ("ab", &["", "ax"], Some("ax")),
        ),
        ("case differs: one edit per letter", ("ABC", &["abc"], None)),
        ("one letter of case", ("Abc", &["abc"], Some("abc"))),
        (
            "the closest wins",
            ("length", &["lengthen", "lenght"], Some("lenght")),
        ),
        (
            "the closest wins in any order",
            ("length", &["lenght", "lengthen"], Some("lenght")),
        ),
        (
            "a tie goes to the first alphabetically",
            ("cat", &["cut", "bat"], Some("bat")),
        ),
        ("a tie, other order", ("cat", &["bat", "cut"], Some("bat"))),
        (
            "non-ASCII counts scalars",
            ("日本語", &["日本人"], Some("日本人")),
        ),
        (
            "non-ASCII transposed",
            ("語本日x", &["本語日x"], Some("本語日x")),
        ),
        (
            "length counts scalars, not bytes",
            ("日本語", &["日本人語人"], None),
        ),
        (
            "a combining mark is an edit",
            ("cafe", &["cafe\u{301}"], Some("cafe\u{301}")),
        ),
        (
            "duplicate candidates",
            ("cat", &["bat", "bat"], Some("bat")),
        ),
        (
            "many candidates, one close",
            ("push", &["pop", "peek", "pusher", "pushy"], Some("pushy")),
        ),
        (
            "a single letter name is close to any single letter",
            ("a", &["b"], Some("b")),
        ),
    ];
    for (name, (wanted, candidates, expected)) in rows {
        h.case(format!("did you mean/{name}"), move || {
            assert_eq!(did_you_mean(wanted, candidates), expected);
        });
    }
}

/// `ca` to `abc` takes two edits when transposed letters may have text inserted
/// between them, and three under the restricted form. The threshold for a name of
/// length 6 is 2, so the difference decides the answer.
fn unrestricted(h: &mut Harness) {
    let rows: [(&str, &str, Option<&str>); 4] = [
        ("xxxxca", "xxxxabc", Some("xxxxabc")),
        ("cabxxx", "abcxxx", Some("abcxxx")),
        ("xcaxxx", "xabcxxx", Some("xabcxxx")),
        ("xxxxcd", "xxxxabc", None),
    ];
    for (name, candidate, expected) in rows {
        h.case(
            format!("did you mean/unrestricted/{name} {candidate}"),
            move || {
                assert_eq!(did_you_mean(name, &[candidate]), expected);
            },
        );
    }
}

fn codes(h: &mut Harness) {
    h.case(
        "did you mean/codes: a transposed digit finds the code",
        || {
            let names: Vec<&str> = Code::ALL.iter().map(|code| code.name()).collect();
            assert_eq!(did_you_mean("T0010", &names), Some("T0001"));
        },
    );
    h.case(
        "did you mean/codes: a tie among codes goes to the first",
        || {
            // One substitution from EN0001, one transposition from EN0601.
            let names: Vec<&str> = Code::ALL.iter().map(|code| code.name()).collect();
            assert_eq!(did_you_mean("EN6001", &names), Some("EN0001"));
            assert_eq!(did_you_mean("EN6001", &["EN0601"]), Some("EN0601"));
        },
    );
    h.case(
        "did you mean/codes: a retired code suggests a real one, not itself",
        || {
            let names: Vec<&str> = Code::ALL.iter().map(|code| code.name()).collect();
            let suggestion = did_you_mean("EN0704", &names).expect("a neighbour exists");
            assert_ne!(suggestion, "EN0704");
            assert!(Code::from_name(suggestion).is_some());
        },
    );
    h.case(
        "did you mean/codes: a word is not close to any code",
        || {
            let names: Vec<&str> = Code::ALL.iter().map(|code| code.name()).collect();
            assert_eq!(did_you_mean("hello", &names), None);
        },
    );
}

pub fn register(h: &mut Harness) {
    thresholds(h);
    table(h);
    unrestricted(h);
    codes(h);
}
