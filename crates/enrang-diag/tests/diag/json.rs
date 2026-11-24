//! `render_json`: versioned, one object per diagnostic, the fields of the text form,
//! and fix-its as byte-span edits. Exact strings pin the format, since a consumer
//! depends on the bytes. The G cases then run through a real JSON reader.

use enrang_base::Span;
use enrang_diag::{Applicability, Code, Diagnostic, Edit, Help, JSON_VERSION, apply_fixes};
use enrang_testkit::Harness;

use crate::goldens::{BUILDERS, built};
use crate::json_value::{J, parse};
use crate::support::{Src, err, same, warn};

/// A name, the diagnostics and the exact output.
type ExactRow = (&'static str, fn(&Src) -> Vec<Diagnostic>, &'static str);

fn exact(h: &mut Harness) {
    let table: Vec<ExactRow> = vec![
        ("no diagnostics are no output", |_| vec![], ""),
        (
            "a bare error",
            |s| vec![err(s.find("abc"), "p")],
            concat!(
                r#"{"version":1,"severity":"error","code":"EN0301","message":"m","#,
                r#""primary":{"text":"p","span":{"file":"a.en","lo":0,"hi":3,"line":1,"col":1,"end_line":1,"end_col":4}},"#,
                r#""secondary":[],"entries":[],"helps":[],"explain":"enrang explain EN0301"}"#,
                "\n",
            ),
        ),
        (
            "a warning has no explain command",
            |s| vec![warn(s.find("abc"), "p")],
            concat!(
                r#"{"version":1,"severity":"warning","code":"EN0430","message":"m","#,
                r#""primary":{"text":"p","span":{"file":"a.en","lo":0,"hi":3,"line":1,"col":1,"end_line":1,"end_col":4}},"#,
                r#""secondary":[],"entries":[],"helps":[],"explain":null}"#,
                "\n",
            ),
        ),
        (
            "a test verdict",
            |s| vec![Diagnostic::new(Code::T0001, "m", s.find("abc"), "p")],
            concat!(
                r#"{"version":1,"severity":"fail","code":"T0001","message":"m","#,
                r#""primary":{"text":"p","span":{"file":"a.en","lo":0,"hi":3,"line":1,"col":1,"end_line":1,"end_col":4}},"#,
                r#""secondary":[],"entries":[],"helps":[],"explain":"enrang explain T0001"}"#,
                "\n",
            ),
        ),
        (
            "a note has no code and no explain command",
            |_| vec![Diagnostic::bare_note(Code::EN0909, "m")],
            concat!(
                r#"{"version":1,"severity":"note","code":null,"message":"m","#,
                r#""primary":{"text":"","span":null},"#,
                r#""secondary":[],"entries":[],"helps":[],"explain":null}"#,
                "\n",
            ),
        ),
        (
            "a spanless diagnostic",
            |_| vec![Diagnostic::spanless(Code::EN1302, "m")],
            concat!(
                r#"{"version":1,"severity":"error","code":"EN1302","message":"m","#,
                r#""primary":{"text":"","span":null},"#,
                r#""secondary":[],"entries":[],"helps":[],"explain":"enrang explain EN1302"}"#,
                "\n",
            ),
        ),
        (
            "every field in its place",
            |s| {
                vec![
                    warn(s.find("abc"), "p")
                        .with_secondary(s.find("def"), "s")
                        .note("n")
                        .why("w")
                        .rule("r")
                        .from_typescript("t")
                        .with_help(Help::text("plain"))
                        .with_help(Help::machine(
                            "m",
                            vec![
                                Edit::insert(s.line_end(1), ";"),
                                Edit::replace(s.find("def"), "x"),
                            ],
                        ))
                        .with_help(Help {
                            message: "q".to_owned(),
                            edits: vec![Edit::command("enrang run")],
                            applicability: Applicability::HasPlaceholders,
                        }),
                ]
            },
            concat!(
                r#"{"version":1,"severity":"warning","code":"EN0430","message":"m","#,
                r#""primary":{"text":"p","span":{"file":"a.en","lo":0,"hi":3,"line":1,"col":1,"end_line":1,"end_col":4}},"#,
                r#""secondary":[{"text":"s","span":{"file":"a.en","lo":4,"hi":7,"line":2,"col":1,"end_line":2,"end_col":4}}],"#,
                r#""entries":[{"kind":"note","text":"n"},{"kind":"why","text":"w"},{"kind":"rule","text":"r"},{"kind":"from TypeScript","text":"t"}],"#,
                r#""helps":[{"message":"plain","applicability":"maybe-incorrect","edits":[],"commands":[]},"#,
                r#"{"message":"m","applicability":"machine-applicable","edits":[{"file":"a.en","lo":3,"hi":3,"replacement":";"},{"file":"a.en","lo":4,"hi":7,"replacement":"x"}],"commands":[]},"#,
                r#"{"message":"q","applicability":"has-placeholders","edits":[],"commands":["enrang run"]}],"#,
                r#""explain":null}"#,
                "\n",
            ),
        ),
        (
            "one line per diagnostic, in the given order",
            |s| {
                vec![
                    Diagnostic::spanless(Code::EN1301, "b"),
                    Diagnostic::spanless(Code::EN1302, "a"),
                ]
                .into_iter()
                .chain(std::iter::once(warn(s.find("abc"), "")))
                .collect()
            },
            concat!(
                r#"{"version":1,"severity":"error","code":"EN1301","message":"b","primary":{"text":"","span":null},"secondary":[],"entries":[],"helps":[],"explain":"enrang explain EN1301"}"#,
                "\n",
                r#"{"version":1,"severity":"error","code":"EN1302","message":"a","primary":{"text":"","span":null},"secondary":[],"entries":[],"helps":[],"explain":"enrang explain EN1302"}"#,
                "\n",
                r#"{"version":1,"severity":"warning","code":"EN0430","message":"m","primary":{"text":"","span":{"file":"a.en","lo":0,"hi":3,"line":1,"col":1,"end_line":1,"end_col":4}},"secondary":[],"entries":[],"helps":[],"explain":null}"#,
                "\n",
            ),
        ),
        (
            "text is escaped",
            |_| {
                vec![Diagnostic::spanless(
                    Code::EN1302,
                    "q\" b\\ n\n r\r t\t c\u{1} d\u{7f} é日🦀",
                )]
            },
            concat!(
                r#"{"version":1,"severity":"error","code":"EN1302","message":"q\" b\\ n\n r\r t\t c\u0001 d\u007f é日🦀","#,
                r#""primary":{"text":"","span":null},"secondary":[],"entries":[],"helps":[],"explain":"enrang explain EN1302"}"#,
                "\n",
            ),
        ),
    ];
    for (name, build, expected) in table {
        h.case(format!("json/exact/{name}"), move || {
            let src = Src::new("a.en", "abc\ndef\n");
            same(&src.json(&build(&src)), expected);
        });
    }
}

fn spans(h: &mut Harness) {
    h.case(
        "json/the first object of G01 is what a consumer needs",
        || {
            let (src, diags) = built("G01");
            let object = parse(src.json(&diags).trim_end()).expect("valid JSON");
            assert_eq!(object.get("version").int(), 1);
            assert_eq!(object.get("code").str(), "EN0101");
            let span = object.get("primary").get("span");
            assert_eq!(span.get("file").str(), "g01.en");
            assert_eq!((span.get("line").int(), span.get("col").int()), (1, 12));
            let edit = &object.get("helps").arr()[0].get("edits").arr()[0];
            assert_eq!(edit.get("replacement").str(), ";");
            assert_eq!(edit.get("lo").int(), edit.get("hi").int());
            let lo = edit.get("lo").int() as usize;
            assert_eq!(&src.text[lo - 1..lo], "1", "the offset is just after `1`");
        },
    );
    h.case(
        "json/offsets are relative to the file, not the session",
        || {
            let src = Src::files(&[("a.en", "0123456789\n"), ("b.en", "abc\n")]);
            let diag = warn(src.f(1).find("b"), "p");
            let object = parse(src.json(&[diag]).trim_end()).unwrap();
            let span = object.get("primary").get("span");
            assert_eq!(span.get("file").str(), "b.en");
            assert_eq!((span.get("lo").int(), span.get("hi").int()), (1, 2));
        },
    );
    h.case("json/a span past the end of its file stops there", || {
        let src = Src::new("a.en", "abc\n");
        let json = src.json(&[err(src.span(1, 999), "p")]);
        assert!(json.contains("\"lo\":1,\"hi\":4,"), "{json}");
    });
    h.case("json/an edit past the end of its file stops there", || {
        let src = Src::new("a.en", "abc\n");
        let help = Help::machine("h", vec![Edit::replace(src.span(1, 999), "x")]);
        let json = src.json(&[err(src.find("abc"), "p").with_help(help)]);
        assert!(
            json.contains("\"edits\":[{\"file\":\"a.en\",\"lo\":1,\"hi\":4,"),
            "{json}"
        );
    });
    h.case("json/end positions count scalars", || {
        let src = Src::new("a.en", "日本語\n");
        let diag = warn(src.find("本語"), "p");
        let object = parse(src.json(&[diag]).trim_end()).unwrap();
        let span = object.get("primary").get("span");
        assert_eq!((span.get("lo").int(), span.get("hi").int()), (3, 9));
        assert_eq!((span.get("col").int(), span.get("end_col").int()), (2, 4));
    });
    h.case("json/a span across lines has both ends", || {
        let src = Src::new("a.en", "abc\ndef\n");
        let diag = warn(src.find("c\nd"), "p");
        let object = parse(src.json(&[diag]).trim_end()).unwrap();
        let span = object.get("primary").get("span");
        assert_eq!((span.get("line").int(), span.get("col").int()), (1, 3));
        assert_eq!(
            (span.get("end_line").int(), span.get("end_col").int()),
            (2, 2)
        );
    });
    h.case("json/CRLF offsets include the carriage return", || {
        let src = Src::new("a.en", "ab\r\ncd\r\n");
        let diag = warn(src.find("cd"), "p");
        let object = parse(src.json(&[diag]).trim_end()).unwrap();
        let span = object.get("primary").get("span");
        assert_eq!((span.get("lo").int(), span.get("hi").int()), (4, 6));
        assert_eq!((span.get("line").int(), span.get("col").int()), (2, 1));
    });
    h.case("json/a BOM counts in offsets and not in columns", || {
        let src = Src::new("a.en", "\u{FEFF}ab\n");
        let diag = warn(src.find("b"), "p");
        let object = parse(src.json(&[diag]).trim_end()).unwrap();
        let span = object.get("primary").get("span");
        assert_eq!((span.get("lo").int(), span.get("col").int()), (4, 2));
    });
    h.case(
        "json/an inverted span reads as empty and a long one is cut at the file",
        || {
            let src = Src::new("a.en", "abc\n");
            let inverted = warn(
                Span {
                    lo: src.at(2),
                    hi: src.at(1),
                },
                "p",
            );
            let long = warn(
                Span {
                    lo: src.at(1),
                    hi: src.at(4000),
                },
                "p",
            );
            let text = src.json(&[inverted, long]);
            let objects: Vec<J> = text.lines().map(|line| parse(line).unwrap()).collect();
            let span = |object: &J| {
                let span = object.get("primary").get("span");
                (span.get("lo").int(), span.get("hi").int())
            };
            assert_eq!(span(&objects[0]), (2, 2));
            assert_eq!(span(&objects[1]), (1, 4));
        },
    );
    h.case("json/the version constant is the one written", || {
        let src = Src::new("a.en", "x\n");
        let object = parse(src.json(&[warn(src.find("x"), "p")]).trim_end()).unwrap();
        assert_eq!(object.get("version").int(), i64::from(JSON_VERSION));
        assert_eq!(JSON_VERSION, 1);
    });
    h.case(
        "json/every severity, kind and applicability has its spelling",
        || {
            let kinds = [
                (Applicability::MachineApplicable, "machine-applicable"),
                (Applicability::MaybeIncorrect, "maybe-incorrect"),
                (Applicability::HasPlaceholders, "has-placeholders"),
            ];
            for (applicability, name) in kinds {
                assert_eq!(applicability.name(), name);
            }
        },
    );
}

/// The whole text, from a diagnostic's JSON, by the rules a consumer would use.
fn check_against_diagnostic(object: &J, diag: &Diagnostic, src: &Src) {
    assert_eq!(
        object.keys(),
        [
            "version",
            "severity",
            "code",
            "message",
            "primary",
            "secondary",
            "entries",
            "helps",
            "explain"
        ]
    );
    assert_eq!(object.get("severity").str(), diag.severity.name());
    assert_eq!(object.get("code").str(), diag.code.name());
    assert_eq!(object.get("message").str(), diag.message);
    assert_eq!(object.get("primary").get("text").str(), diag.primary.text);
    let secondary = object.get("secondary").arr();
    assert_eq!(secondary.len(), diag.secondary.len());
    for (json, label) in secondary.iter().zip(&diag.secondary) {
        assert_eq!(json.get("text").str(), label.text);
        let span = json.get("span");
        assert_eq!(span.get("lo").int(), i64::from(label.span.lo.0 - src.start));
        assert_eq!(span.get("hi").int(), i64::from(label.span.hi.0 - src.start));
    }
    let entries = object.get("entries").arr();
    assert_eq!(entries.len(), diag.entries.len());
    for (json, entry) in entries.iter().zip(&diag.entries) {
        assert_eq!(json.get("kind").str(), entry.kind.name());
        assert_eq!(json.get("text").str(), entry.text);
    }
    let helps = object.get("helps").arr();
    assert_eq!(helps.len(), diag.helps.len());
    for (json, help) in helps.iter().zip(&diag.helps) {
        assert_eq!(json.get("message").str(), help.message);
        assert_eq!(json.get("applicability").str(), help.applicability.name());
        check_edits_apply(json, help, src);
    }
}

/// Byte-span edits from the JSON, applied by hand, give what `apply_fixes` gives.
fn check_edits_apply(json: &J, help: &Help, src: &Src) {
    let edits = json.get("edits").arr();
    assert_eq!(edits.len(), help.edits.len());
    if edits.is_empty() {
        return;
    }
    let mut ordered: Vec<(usize, usize, &str)> = edits
        .iter()
        .map(|edit| {
            assert_eq!(
                edit.get("file").str(),
                src.map.file(src.id).path.to_str().unwrap()
            );
            (
                edit.get("lo").int() as usize,
                edit.get("hi").int() as usize,
                edit.get("replacement").str(),
            )
        })
        .collect();
    ordered.sort();
    let mut by_hand = src.text.to_string();
    for &(lo, hi, replacement) in ordered.iter().rev() {
        by_hand.replace_range(lo..hi, replacement);
    }
    let applied = apply_fixes(&src.text, src.base(), &help.edits).expect("the fix applies");
    same(&by_hand, &applied);
}

fn golden_cases(h: &mut Harness) {
    for (id, _) in BUILDERS {
        h.case(
            format!("json/{id}/parses and matches its diagnostics"),
            move || {
                let (src, diags) = built(id);
                let text = src.json(&diags);
                assert!(text.ends_with('\n'));
                let objects: Vec<&str> = text.lines().collect();
                assert_eq!(objects.len(), diags.len(), "one object per diagnostic");
                for (line, diag) in objects.iter().zip(&diags) {
                    let object = parse(line).unwrap_or_else(|error| panic!("{error}: {line}"));
                    check_against_diagnostic(&object, diag, &src);
                }
            },
        );
        h.case(format!("json/{id}/is stable across runs"), move || {
            let (src, diags) = built(id);
            let first = src.json(&diags);
            let (again, rebuilt) = built(id);
            same(&again.json(&rebuilt), &first);
        });
    }
}

pub fn register(h: &mut Harness) {
    exact(h);
    spans(h);
    golden_cases(h);
}
