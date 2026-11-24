//! Compile-test anchors (TESTING 7): reading them, reading a rendered stderr, and
//! comparing the two.

use enrang_testkit::{
    Anchor, Harness, Mismatch, Reported, anchors, compare, fixture_target, reported,
};

fn anchor(line: usize, code: &str, substring: Option<&str>) -> Anchor {
    Anchor {
        line,
        code: code.to_owned(),
        substring: substring.map(str::to_owned),
    }
}

fn diag(code: &str, message: &str, line: Option<usize>) -> Reported {
    Reported {
        code: code.to_owned(),
        message: message.to_owned(),
        at: line.map(|line| ("f.en".to_owned(), line, 1)),
    }
}

/// A rendered stderr in the shape of SPEC 13.1, as `enrang check` prints it.
const RENDERED: &str = "\
error[EN0201]: `===` does not exist in Enrang
 --> g03.en:2:7
  |
2 | if (n === 3) {
  |       ^^^ use `==` here
  |
  = explain: run `enrang explain EN0201`

warning[EN0430]: a warning
  --> src/a b.en:12:30
   |
12 | x
   | ^
   |

error[EN1305]: file not found: `x.en`
  = explain: run `enrang explain EN1305`

note: a note is no diagnostic of its own
error: aborting due to 2 previous errors
";

pub fn register(h: &mut Harness) {
    h.case(
        "anchors/a fixture's target is read from its first line alone (M2 plan g.4)",
        || {
            assert_eq!(fixture_target(""), Ok(None));
            assert_eq!(fixture_target("const a = 1;\n"), Ok(None));
            assert_eq!(
                fixture_target("//! target: i386-none\nconst a = 1;\n"),
                Ok(Some("i386-none".to_owned()))
            );
            assert_eq!(
                fixture_target(" //! target:  x86_64-linux \n"),
                Ok(Some("x86_64-linux".to_owned()))
            );
            for broken in [
                "//! target:\n",
                "//! target:   \n",
                "const a = 1;\n//! target: i386-none\n",
                "//! target: i386-none\n//! target: i386-none\n",
            ] {
                assert!(fixture_target(broken).is_err(), "{broken:?}");
            }
        },
    );
    let read: &[(&str, &str, Result<Vec<Anchor>, usize>)] = &[
        ("none", "const x = 1;\n", Ok(vec![])),
        (
            "a code",
            "x; //~ EN0101\n",
            Ok(vec![anchor(1, "EN0101", None)]),
        ),
        (
            "a code and a substring",
            "a\nif (a === b) {} //~ EN0201 \"`===` does not exist\"\n",
            Ok(vec![anchor(2, "EN0201", Some("`===` does not exist"))]),
        ),
        (
            "two on one line",
            "\"abc //~ EN0004 //~ EN0101\n",
            Ok(vec![anchor(1, "EN0004", None), anchor(1, "EN0101", None)]),
        ),
        (
            "no space after the marker",
            "x; //~EN0101\n",
            Ok(vec![anchor(1, "EN0101", None)]),
        ),
        (
            "a test-runner code",
            "x; //~ T0001\n",
            Ok(vec![anchor(1, "T0001", None)]),
        ),
        (
            "lines count from one, over CRLF too",
            "a\r\nb\r\nc; //~ EN0100\r\n",
            Ok(vec![anchor(3, "EN0100", None)]),
        ),
        ("an empty anchor", "x; //~\n", Err(1)),
        ("a lower-case code", "a\nx; //~ en0101\n", Err(2)),
        ("digits only", "x; //~ 0101\n", Err(1)),
        ("letters only", "x; //~ EN\n", Err(1)),
        ("prose after the code", "x; //~ EN0101 here\n", Err(1)),
        ("an unclosed substring", "x; //~ EN0101 \"here\n", Err(1)),
        ("an empty substring", "x; //~ EN0101 \"\"\n", Err(1)),
        (
            "text after the substring",
            "x; //~ EN0101 \"a\" b\n",
            Err(1),
        ),
    ];
    for (name, text, expected) in read {
        let (text, expected) = (*text, expected.clone());
        h.case(format!("anchors::read::{name}"), move || {
            let found = anchors(text).map_err(|error| error.line);
            assert_eq!(found, expected);
        });
    }
    h.case("anchors::read::an_error_names_its_line", || {
        let error = anchors("a\nb //~ EN\n").unwrap_err();
        assert_eq!(
            error.to_string(),
            "line 2: `//~` must name a code, not \"EN\""
        );
    });

    h.case("anchors::reported::every_coded_diagnostic", || {
        assert_eq!(
            reported(RENDERED),
            [
                Reported {
                    code: "EN0201".to_owned(),
                    message: "`===` does not exist in Enrang".to_owned(),
                    at: Some(("g03.en".to_owned(), 2, 7)),
                },
                Reported {
                    code: "EN0430".to_owned(),
                    message: "a warning".to_owned(),
                    at: Some(("src/a b.en".to_owned(), 12, 30)),
                },
                Reported {
                    code: "EN1305".to_owned(),
                    message: "file not found: `x.en`".to_owned(),
                    at: None,
                },
            ]
        );
    });
    h.case("anchors::reported::nothing_in_an_empty_stderr", || {
        assert_eq!(reported(""), []);
        assert_eq!(reported("error: aborting due to 1 previous error\n"), []);
    });
    h.case("anchors::reported::not_an_indented_or_quoted_head", || {
        let stderr = "  error[EN0101]: indented\n= note: error[EN0101]: inside\nerror[EN0101] x\n";
        assert_eq!(reported(stderr), []);
    });
    h.case(
        "anchors::reported::a_place_needs_a_line_and_a_column",
        || {
            let found = reported("error[EN0101]: m\n --> f.en:x:1\n");
            assert_eq!(found[0].at, None);
            let found = reported("error[EN0101]: m\n --> c:/a.en:3:4\n");
            assert_eq!(found[0].at, Some(("c:/a.en".to_owned(), 3, 4)));
        },
    );

    let anchored = || {
        vec![
            anchor(2, "EN0201", Some("does not exist")),
            anchor(5, "EN0101", None),
        ]
    };
    h.case("anchors::compare::the_same_set_passes", move || {
        let run = [
            diag("EN0201", "`===` does not exist in Enrang", Some(2)),
            diag("EN0101", "missing `;`", Some(5)),
        ];
        assert_eq!(compare(&anchored(), &run), Ok(()));
    });
    h.case(
        "anchors::compare::two_reports_of_one_pair_are_one_pair",
        move || {
            let run = [
                diag("EN0201", "`===` does not exist in Enrang", Some(2)),
                diag("EN0201", "`!==` does not exist in Enrang", Some(2)),
                diag("EN0101", "missing `;`", Some(5)),
            ];
            assert_eq!(compare(&anchored(), &run), Ok(()));
        },
    );
    h.case("anchors::compare::a_missing_pair_fails", move || {
        let run = [diag("EN0201", "`===` does not exist", Some(2))];
        let mismatch = compare(&anchored(), &run).unwrap_err();
        assert_eq!(mismatch.missing, [(5, "EN0101".to_owned())]);
        assert!(mismatch.unexpected.is_empty());
    });
    h.case("anchors::compare::an_unanchored_pair_fails", move || {
        let run = [
            diag("EN0201", "`===` does not exist", Some(2)),
            diag("EN0101", "missing `;`", Some(5)),
            diag("EN0100", "unexpected", Some(7)),
        ];
        let mismatch = compare(&anchored(), &run).unwrap_err();
        assert_eq!(mismatch.unexpected, [(Some(7), "EN0100".to_owned())]);
        assert_eq!(
            mismatch.to_string(),
            "line 7: EN0100 is reported but not anchored\n"
        );
    });
    h.case(
        "anchors::compare::the_right_code_on_the_wrong_line_fails",
        move || {
            let run = [
                diag("EN0201", "`===` does not exist", Some(3)),
                diag("EN0101", "missing `;`", Some(5)),
            ];
            let mismatch = compare(&anchored(), &run).unwrap_err();
            assert_eq!(mismatch.missing, [(2, "EN0201".to_owned())]);
            assert_eq!(mismatch.unexpected, [(Some(3), "EN0201".to_owned())]);
        },
    );
    h.case(
        "anchors::compare::a_placeless_diagnostic_fails",
        move || {
            let run = [
                diag("EN0201", "`===` does not exist", Some(2)),
                diag("EN0101", "missing `;`", Some(5)),
                diag("EN1305", "file not found", None),
            ];
            let mismatch = compare(&anchored(), &run).unwrap_err();
            assert_eq!(mismatch.unexpected, [(None, "EN1305".to_owned())]);
            assert_eq!(
                mismatch.to_string(),
                "EN1305 is reported with no place, so no anchor can name it\n"
            );
        },
    );
    h.case("anchors::compare::a_wrong_message_fails", move || {
        let run = [
            diag("EN0201", "something else", Some(2)),
            diag("EN0101", "missing `;`", Some(5)),
        ];
        let mismatch = compare(&anchored(), &run).unwrap_err();
        assert_eq!(
            mismatch,
            Mismatch {
                wrong_message: vec![(
                    anchor(2, "EN0201", Some("does not exist")),
                    vec!["something else".to_owned()]
                )],
                ..Mismatch::default()
            }
        );
        assert_eq!(
            mismatch.to_string(),
            "line 2: no EN0201 message holds \"does not exist\"; the messages are [\"something else\"]\n"
        );
    });
    h.case(
        "anchors::compare::one_matching_message_of_two_is_enough",
        move || {
            let run = [
                diag("EN0201", "something else", Some(2)),
                diag("EN0201", "it does not exist", Some(2)),
                diag("EN0101", "missing `;`", Some(5)),
            ];
            assert_eq!(compare(&anchored(), &run), Ok(()));
        },
    );
    h.case("anchors::compare::no_anchors_and_no_reports_pass", || {
        assert_eq!(compare(&[], &[]), Ok(()));
        let mismatch = compare(&[], &[diag("EN0100", "x", Some(1))]).unwrap_err();
        assert!(!mismatch.is_empty());
    });
    h.case("anchors::compare::over_a_rendered_stderr", || {
        let found = reported(RENDERED);
        let wanted = [
            anchor(2, "EN0201", Some("`===`")),
            anchor(12, "EN0430", None),
        ];
        let mismatch = compare(&wanted, &found).unwrap_err();
        assert_eq!(mismatch.unexpected, [(None, "EN1305".to_owned())]);
        assert!(mismatch.missing.is_empty() && mismatch.wrong_message.is_empty());
        assert_eq!(compare(&wanted, &found[..2]), Ok(()));
    });
}
