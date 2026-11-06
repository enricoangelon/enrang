//! The case extractor: the real `docs/SPEC.md`, then every rule of SPEC 14 on
//! synthetic documents, then mutations of the real document that must be caught.

use std::collections::BTreeSet;
use std::sync::OnceLock;

use enrang_testkit::{
    Case, ExtractErrors, Harness, StreamSource, extract_cases, headings_without_cases,
};

use crate::support::read_doc;

use StreamSource::{Block, Inline, Unnamed};

fn spec() -> &'static str {
    static SPEC: OnceLock<String> = OnceLock::new();
    SPEC.get_or_init(|| read_doc("SPEC.md"))
}

fn spec_cases() -> &'static [Case] {
    static CASES: OnceLock<Vec<Case>> = OnceLock::new();
    CASES.get_or_init(|| extract_cases(spec()).unwrap_or_else(|errors| panic!("{errors}")))
}

fn spec_case(id: &str) -> &'static Case {
    spec_cases()
        .iter()
        .find(|case| case.id == id)
        .unwrap_or_else(|| panic!("SPEC has no case {id}"))
}

fn file_names(case: &Case) -> Vec<&str> {
    case.files.iter().map(|file| file.name.as_str()).collect()
}

/// Case, files, command, exit, and the sources of stdout, stderr and serial, copied
/// by hand from the markers of SPEC.
type Row = (
    &'static str,
    &'static [&'static str],
    &'static str,
    i32,
    StreamSource,
    StreamSource,
    StreamSource,
);

const MARKERS: [Row; 37] = [
    (
        "tour",
        &["tour.en"],
        "enrang run tour.en",
        0,
        Inline,
        Unnamed,
        Unnamed,
    ),
    (
        "ownership",
        &["ownership.en"],
        "enrang check ownership.en",
        0,
        Unnamed,
        Unnamed,
        Unnamed,
    ),
    (
        "tour-kernel",
        &["hello.en"],
        "enrang build --target=i386-none --image=hdd hello.en",
        0,
        Unnamed,
        Unnamed,
        Unnamed,
    ),
    (
        "G01",
        &["g01.en"],
        "enrang check g01.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G02",
        &["g02.en"],
        "enrang check g02.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G03",
        &["g03.en"],
        "enrang check g03.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G04",
        &["g04.en"],
        "enrang check g04.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G05",
        &["g05.en"],
        "enrang check g05.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G06",
        &["g06.en"],
        "enrang check g06.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G07",
        &["g07.en"],
        "enrang check g07.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G08",
        &["g08.en"],
        "enrang check g08.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G09",
        &["g09.en"],
        "enrang check g09.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G10",
        &["g10.en"],
        "enrang check g10.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G11",
        &["g11.en"],
        "enrang check g11.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G12",
        &["g12.en"],
        "enrang check g12.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G13",
        &["g13.en"],
        "enrang check g13.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G14",
        &["g14.en"],
        "enrang build --target=i386-none g14.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G15",
        &["g15.en"],
        "enrang build --target=i386-linux --cpu=i386 g15.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G16",
        &["g16.en"],
        "enrang check g16.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G17",
        &["g17.en"],
        "enrang check g17.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G18",
        &["g18.en"],
        "enrang check g18.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G19",
        &["g19.en"],
        "enrang check g19.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G20",
        &["g20.en"],
        "enrang check g20.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G21",
        &["g21.en"],
        "enrang check g21.en",
        0,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G22",
        &["g22.en"],
        "enrang check g22.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "G23",
        &["g23.en"],
        "enrang check g23.en",
        1,
        Unnamed,
        Block,
        Unnamed,
    ),
    (
        "S1",
        &["s01.en"],
        "enrang run s01.en",
        0,
        Block,
        Unnamed,
        Unnamed,
    ),
    (
        "S2",
        &["s02.en"],
        "enrang run s02.en",
        0,
        Block,
        Unnamed,
        Unnamed,
    ),
    (
        "S3",
        &["s03.en"],
        "enrang run s03.en",
        0,
        Block,
        Unnamed,
        Unnamed,
    ),
    (
        "S4",
        &["s04.en"],
        "enrang run s04.en",
        0,
        Block,
        Unnamed,
        Unnamed,
    ),
    (
        "S5",
        &["s05.en"],
        "enrang run s05.en",
        0,
        Block,
        Unnamed,
        Unnamed,
    ),
    (
        "S6",
        &["s06.en"],
        "enrang run s06.en",
        0,
        Block,
        Unnamed,
        Unnamed,
    ),
    (
        "S7",
        &["s07.en"],
        "enrang run s07.en",
        1,
        Block,
        Inline,
        Unnamed,
    ),
    (
        "S8",
        &["s08.en"],
        "enrang run s08.en",
        101,
        Block,
        Block,
        Unnamed,
    ),
    (
        "S9",
        &["kernel.en"],
        "enrang build --target=i386-none --cpu=i386 --image=floppy kernel.en",
        0,
        Unnamed,
        Unnamed,
        Block,
    ),
    (
        "S10",
        &["src/math.en", "src/math.test.en"],
        "enrang test --ci src/math.test.en",
        0,
        Block,
        Unnamed,
        Unnamed,
    ),
    (
        "S11",
        &["s11.en"],
        "enrang run s11.en",
        0,
        Block,
        Block,
        Unnamed,
    ),
];

/// A one-file case with these marker attributes after `files`, and this body.
fn doc(attributes: &str, body: &str) -> String {
    format!("<!-- case: X files=a.en {attributes} -->\n{body}")
}

const TS: &str = "```ts\nsource\n```\n";

fn errors_of(document: &str) -> ExtractErrors {
    match extract_cases(document) {
        Ok(cases) => panic!("this was accepted, with {} cases:\n{document}", cases.len()),
        Err(errors) => errors,
    }
}

fn one_case(document: &str) -> Case {
    let mut cases = extract_cases(document).unwrap_or_else(|errors| panic!("{errors}"));
    assert_eq!(cases.len(), 1, "{cases:?}");
    cases.remove(0)
}

/// Replaces the first `from` after the first `anchor`, which must both exist.
fn replace_after(text: &str, anchor: &str, from: &str, to: &str) -> String {
    let start = text
        .find(anchor)
        .unwrap_or_else(|| panic!("no anchor {anchor:?}"));
    let offset = text[start..]
        .find(from)
        .unwrap_or_else(|| panic!("no {from:?} after {anchor:?}"));
    let at = start + offset;
    format!("{}{to}{}", &text[..at], &text[at + from.len()..])
}

/// Every prose line of the real document turned into noise, leaving only what the
/// extractor may read: markers, headings, blocks, and the two `inline` sentences.
fn with_garbled_prose(document: &str) -> String {
    let mut out = String::new();
    let mut in_fence = false;
    for line in document.split('\n') {
        let is_fence = line.starts_with("```");
        if is_fence {
            in_fence = !in_fence;
        }
        let keep = is_fence
            || in_fence
            || line.is_empty()
            || line.starts_with('#')
            || line.starts_with("<!-- case:")
            || line.starts_with("Output: `")
            || line.starts_with("Stderr: `");
        out.push_str(if keep {
            line
        } else {
            "Noise, with a `span` and punctuation. More noise! `another`?"
        });
        out.push('\n');
    }
    out.pop();
    out
}

/// The little of Markdown the extractor reads. Each row is the text after a source
/// block, in a case whose stderr is an inline-free `text` block when it has one, and
/// what the extractor must find.
fn register_markdown(h: &mut Harness) {
    let cmd = "cmd=\"c\" exit=0";
    // Text after the source, in a case with one file and no stream: none of these
    // lines opens a block, which would either add a file or never close.
    let plain_lines: &[(&str, &str)] = &[
        (
            "a_four_space_fence_is_no_fence",
            "    ```ts\n    y\n    ```\n",
        ),
        ("two_backticks_are_no_fence", "``\n"),
        ("two_tildes_are_no_fence", "~~\n"),
        (
            "a_backtick_in_the_info_string_is_inline_code",
            "```a``` b\n",
        ),
    ];
    for &(name, after) in plain_lines {
        h.case(format!("doc_cases::markdown::{name}"), move || {
            let case = one_case(&doc(cmd, &format!("{TS}\n{after}")));
            assert_eq!(file_names(&case), ["a.en"]);
            assert_eq!(case.files[0].contents, "source\n");
        });
    }
    // A source block written with these lines, and the source it must come to.
    let blocks: &[(&str, &str, &str)] = &[
        ("a_longer_fence_closes", "```ts\nx\n````\n", "x\n"),
        ("a_same_length_fence_closes", "```ts\nx\n```\n", "x\n"),
        ("a_three_space_fence_closes", "```ts\nx\n   ```\n", "x\n"),
        (
            "a_deep_indent_does_not_close",
            "```ts\nx\n    ```\ny\n```\n",
            "x\n    ```\ny\n",
        ),
        (
            "a_shorter_fence_does_not_close",
            "````ts\nx\n```\ny\n````\n",
            "x\n```\ny\n",
        ),
        ("a_three_space_fence_opens", "   ```ts\n   x\n```\n", "x\n"),
        ("a_tilde_fence", "~~~ts\nx\n~~~\n", "x\n"),
    ];
    for &(name, block, source) in blocks {
        h.case(format!("doc_cases::markdown::{name}"), move || {
            let case = one_case(&doc(cmd, block));
            assert_eq!(case.files[0].contents, source);
        });
    }
    // A line between the source and the block a marker names. A heading would end the
    // case's scope and lose the block.
    let not_headings: &[(&str, &str)] = &[
        ("seven_hashes_are_no_heading", "####### not a heading\n"),
        ("a_deep_indent_is_no_heading", "    ## not a heading\n"),
        ("a_hash_with_no_space_is_no_heading", "##not a heading\n"),
    ];
    for &(name, line) in not_headings {
        h.case(format!("doc_cases::markdown::{name}"), move || {
            let body = format!("{TS}\n{line}\n```text\ne\n```\n");
            let case = one_case(&doc(&format!("{cmd} stderr=block"), &body));
            assert_eq!(case.stderr.text, "e\n");
        });
    }
    let headings: &[(&str, &str)] = &[
        ("six_hashes_are_a_heading", "###### a heading\n"),
        ("a_three_space_indent_is_a_heading", "   ## a heading\n"),
    ];
    for &(name, line) in headings {
        h.case(format!("doc_cases::markdown::{name}"), move || {
            let body = format!("{TS}\n{line}\n```text\ne\n```\n");
            let errors = errors_of(&doc(&format!("{cmd} stderr=block"), &body));
            let text = errors.to_string();
            assert!(text.contains("0 `text` blocks follow"), "{text}");
        });
    }
}

pub fn register(h: &mut Harness) {
    register_markdown(h);
    register_real_document(h);
    register_valid_documents(h);
    register_malformed_documents(h);
    register_mutations(h);
    register_heading_rule(h);
}

fn register_real_document(h: &mut Harness) {
    h.case("doc_cases::real::finds_exactly_the_37_markers", || {
        assert_eq!(spec_cases().len(), 37);
        assert_eq!(spec_cases().len(), MARKERS.len());
    });
    h.case(
        "doc_cases::real::the_marker_count_agrees_with_the_raw_text",
        || {
            let raw = spec()
                .lines()
                .filter(|line| line.starts_with("<!-- case:"))
                .count();
            assert_eq!(raw, 37);
        },
    );
    h.case(
        "doc_cases::real::the_marker_quoted_in_prose_is_not_a_case",
        || {
            let quoted = spec()
                .lines()
                .find(|line| line.contains("<!-- case: ID files=a.en,b.en"))
                .expect("SPEC 14 defines the marker in a sentence");
            assert!(!quoted.starts_with("<!--"));
            assert!(spec_cases().iter().all(|case| case.id != "ID"));
        },
    );
    h.case("doc_cases::real::ids_in_document_order", || {
        let found: Vec<&str> = spec_cases().iter().map(|case| case.id.as_str()).collect();
        let expected: Vec<&str> = MARKERS.iter().map(|row| row.0).collect();
        assert_eq!(found, expected);
    });
    h.case("doc_cases::real::g01_to_g23_are_all_there", || {
        let found: BTreeSet<&str> = spec_cases().iter().map(|case| case.id.as_str()).collect();
        for number in 1..=23 {
            assert!(
                found.contains(format!("G{number:02}").as_str()),
                "G{number:02}"
            );
        }
    });
    h.case("doc_cases::real::s1_to_s11_are_all_there", || {
        let found: BTreeSet<&str> = spec_cases().iter().map(|case| case.id.as_str()).collect();
        for number in 1..=11 {
            assert!(found.contains(format!("S{number}").as_str()), "S{number}");
        }
    });
    h.case("doc_cases::real::marker_lines_point_at_markers", || {
        let lines: Vec<&str> = spec().split('\n').collect();
        for case in spec_cases() {
            let line = lines[case.line - 1];
            assert!(
                line.starts_with(&format!("<!-- case: {} ", case.id)),
                "{line:?}"
            );
        }
    });
    for &(id, files, cmd, exit, stdout, stderr, serial) in &MARKERS {
        h.case(format!("doc_cases::real::{id}::marker"), move || {
            let case = spec_case(id);
            assert_eq!(file_names(case), files);
            assert_eq!(case.cmd, cmd);
            assert_eq!(case.exit, exit);
            assert_eq!(case.stdout.source, stdout);
            assert_eq!(case.stderr.source, stderr);
            assert_eq!(case.serial.source, serial);
        });
        h.case(
            format!("doc_cases::real::{id}::streams_follow_their_sources"),
            move || {
                let case = spec_case(id);
                for (name, stream) in [
                    ("stdout", &case.stdout),
                    ("stderr", &case.stderr),
                    ("serial", &case.serial),
                ] {
                    match stream.source {
                        Unnamed => assert_eq!(stream.text, "", "{name} is not named"),
                        Block | Inline => {
                            assert!(!stream.text.is_empty(), "{name} is named but empty");
                            assert!(stream.text.ends_with('\n'), "{name}: {:?}", stream.text);
                            assert!(!stream.text.ends_with("\n\n"), "{name}: {:?}", stream.text);
                        }
                    }
                }
            },
        );
        h.case(
            format!("doc_cases::real::{id}::files_end_with_one_newline"),
            move || {
                for file in &spec_case(id).files {
                    assert!(file.contents.ends_with('\n'), "{}", file.name);
                    assert!(!file.contents.ends_with("\n\n"), "{}", file.name);
                    assert!(
                        file.contents.len() > 10,
                        "{}: {:?}",
                        file.name,
                        file.contents
                    );
                }
            },
        );
        h.case(
            format!("doc_cases::real::{id}::comes_from_the_right_place"),
            move || {
                let lines: Vec<&str> = spec().split('\n').collect();
                let case = spec_case(id);
                assert_eq!(
                    lines[case.line], "```ts",
                    "a `ts` block follows the marker directly"
                );
                let first = case.files[0].contents.lines().next().unwrap();
                assert_eq!(lines[case.line + 1], first, "the first source line");
            },
        );
    }
    // G21 and S11 have warnings alone, and G23 opens with its warning.
    for number in (1..=23).filter(|number| *number != 21) {
        h.case(
            format!("doc_cases::real::G{number:02}::is_a_full_diagnostic"),
            move || {
                let case = spec_case(&format!("G{number:02}"));
                let stderr = &case.stderr.text;
                let head = if number == 23 {
                    "warning[EN"
                } else {
                    "error[EN"
                };
                assert!(stderr.starts_with(head), "{stderr}");
                let last = stderr.lines().last().unwrap();
                assert!(last.starts_with("error: aborting due to "), "{stderr}");
                let name = &case.files[0].name;
                assert!(stderr.contains(&format!(" --> {name}:")), "{stderr}");
                assert_eq!(case.exit, 1);
            },
        );
    }
    for id in ["G21", "S11"] {
        h.case(
            format!("doc_cases::real::{id}::is_a_warning_alone"),
            move || {
                let case = spec_case(id);
                let stderr = &case.stderr.text;
                assert!(stderr.starts_with("warning[EN"), "{stderr}");
                assert!(!stderr.contains("error"), "{stderr}");
                assert!(!stderr.contains("aborting"), "{stderr}");
                assert!(!stderr.contains("= explain:"), "{stderr}");
                let name = &case.files[0].name;
                assert!(stderr.contains(&format!(" --> {name}:")), "{stderr}");
                assert_eq!(case.exit, 0);
            },
        );
    }
    h.case("doc_cases::real::G23::counts_its_warning", || {
        let last = spec_case("G23").stderr.text.lines().last().unwrap();
        assert_eq!(
            last,
            "error: aborting due to 1 previous error; 1 warning emitted"
        );
    });
    // Exact bytes where a misassignment or an off-by-one would show.
    let exact: &[(&str, fn(&Case) -> &str, &str)] = &[
        (
            "tour_inline_stdout",
            |c| &c.stdout.text,
            "top = 42\n[vm] done\nresult 42\n",
        ),
        (
            "s7_block_stdout",
            |c| &c.stdout.text,
            "42\ncaught: not a number: x\n",
        ),
        (
            "s7_inline_stderr",
            |c| &c.stderr.text,
            "error: negative age\n",
        ),
        ("s8_stdout", |c| &c.stdout.text, "2\n-2147483648\n0\n"),
        (
            "s8_stderr",
            |c| &c.stderr.text,
            "panic: index 3 is out of bounds for length 3\n  --> s08.en:7:15\nstack:\n  main (s08.en:7:15)\n",
        ),
        (
            "s9_serial",
            |c| &c.serial.text,
            "Hello from Enrang\nsum = 5050\nboots = 1\n",
        ),
        (
            "s10_stdout",
            |c| &c.stdout.text,
            "PASS src/math.test.en\n  gcd > common factor\n  gcd > zero\n  gcd > rejects mixed widths\n\nTests  3 passed, 3 total\n",
        ),
        (
            "s1_stdout",
            |c| &c.stdout.text,
            "Hello, Enrang\n9 5 14\n3.5\n7 / 2 = 3, rem 1\n3.75 0.30000000000000004\n44 -3 -1\n",
        ),
        (
            "g01_source",
            |c| &c.files[0].contents,
            "function main(): void {\n  const x = 1\n  console.log(x);\n}\n",
        ),
        (
            "g01_stderr",
            |c| &c.stderr.text,
            "error[EN0101]: missing `;` after this statement\n --> g01.en:2:14\n  |\n2 |   const x = 1\n  |              ^ expected `;` here\n  |\n  = from TypeScript: Enrang has no automatic semicolon insertion.\nhelp: add the semicolon\n  |\n2 |   const x = 1;\n  |              +\n  = explain: run `enrang explain EN0101`\n\nerror: aborting due to 1 previous error\n",
        ),
        (
            "s11_stdout",
            |c| &c.stdout.text,
            "0 1 2 3 7 8\n2 4\nx xy\n7 3 2 1 1 0\n",
        ),
        (
            "s10_second_file",
            |c| &c.files[1].contents,
            "describe(\"gcd\", () => {\n  test(\"common factor\", () => {\n    expect(gcd(84, 36)).toBe(12);\n  });\n\n  test(\"zero\", () => {\n    expect(gcd(7, 0)).toBe(7);\n  });\n\n  compileFails(\"rejects mixed widths\", raw`\n    function f(a: i32, b: i64): i64 { return a + b; } //~ EN0402\n    function main(): void {}\n  `);\n});\n",
        ),
    ];
    for &(name, field, expected) in exact {
        h.case(format!("doc_cases::real::exact::{name}"), move || {
            let id = match name.split('_').next().unwrap() {
                "tour" => "tour".to_owned(),
                short => short.to_uppercase(),
            };
            assert_eq!(field(spec_case(&id)), expected);
        });
    }
    let first_lines: &[(&str, &str, usize)] = &[
        ("tour", "// tour.en: run with `enrang run tour.en`", 0),
        (
            "ownership",
            "function total(xs: &i64[]): i64 { let t = 0; for (const x of xs) { t += x; } return t; }",
            0,
        ),
        (
            "tour-kernel",
            "// hello.en: enrang build --target=i386-none --image=hdd hello.en",
            0,
        ),
        ("S9", "import { vga, serial } from \"os\";", 0),
        ("S10", "export function gcd(a: i64, b: i64): i64 {", 0),
        ("S10", "describe(\"gcd\", () => {", 1),
    ];
    for &(id, line, index) in first_lines {
        h.case(
            format!("doc_cases::real::first_line::{id}[{index}]"),
            move || {
                assert_eq!(
                    spec_case(id).files[index].contents.lines().next(),
                    Some(line)
                );
            },
        );
    }
    let artefacts: &[(&str, bool)] = &[
        ("tour", false),
        ("ownership", false),
        ("tour-kernel", true),
        ("G01", false),
        ("G14", true),
        ("S1", false),
        ("S9", true),
        ("S10", false),
    ];
    for &(id, may) in artefacts {
        h.case(format!("doc_cases::real::artefact_rule::{id}"), move || {
            assert_eq!(spec_case(id).may_write_artefact(), may);
        });
    }
    h.case(
        "doc_cases::real::other_documents_have_no_markers_today",
        || {
            for name in ["TESTING.md", "ARCHITECTURE.md", "DEV_RUNTIME.md"] {
                let cases = extract_cases(&read_doc(name))
                    .unwrap_or_else(|errors| panic!("{name}: {errors}"));
                assert_eq!(cases.len(), 0, "{name}");
            }
        },
    );
}

fn register_valid_documents(h: &mut Harness) {
    let cmd = "cmd=\"enrang run a.en\" exit=0";
    h.case("doc_cases::valid::no_markers_no_cases", || {
        assert_eq!(
            extract_cases("# Title\n\nProse.\n\n```ts\ncode\n```\n").unwrap(),
            []
        );
        assert_eq!(extract_cases("").unwrap(), []);
    });
    h.case("doc_cases::valid::an_unnamed_stream_is_empty", move || {
        let case = one_case(&doc(cmd, TS));
        assert_eq!(case.id, "X");
        assert_eq!(case.line, 1);
        assert_eq!(case.exit, 0);
        assert_eq!(case.cmd, "enrang run a.en");
        for stream in [&case.stdout, &case.stderr, &case.serial] {
            assert_eq!(stream.source, Unnamed);
            assert_eq!(stream.text, "");
        }
        assert_eq!(file_names(&case), ["a.en"]);
        assert_eq!(case.files[0].contents, "source\n");
    });
    h.case(
        "doc_cases::valid::several_files_keep_the_marker_order",
        || {
            let text = "<!-- case: X files=z.en,a.en,m/n.en cmd=\"c\" exit=0 -->\n\
                    ```ts\none\n```\nprose\n```ts\ntwo\n```\n\n```ts\nthree\n```\n";
            let case = one_case(text);
            assert_eq!(file_names(&case), ["z.en", "a.en", "m/n.en"]);
            let contents: Vec<&str> = case.files.iter().map(|f| f.contents.as_str()).collect();
            assert_eq!(contents, ["one\n", "two\n", "three\n"]);
        },
    );
    // The streams a marker names and the `text` blocks after the source, in order.
    let blocks: &[(&str, &str, &str, &str)] = &[
        ("stdout=block", "O\n", "", ""),
        ("stderr=block", "", "E\n", ""),
        ("serial=block", "", "", "C\n"),
        ("stdout=block stderr=block", "O\n", "E\n", ""),
        ("stdout=block serial=block", "O\n", "", "C\n"),
        ("stderr=block serial=block", "", "E\n", "C\n"),
        (
            "stdout=block stderr=block serial=block",
            "O\n",
            "E\n",
            "C\n",
        ),
    ];
    for &(attributes, stdout, stderr, serial) in blocks {
        h.case(
            format!("doc_cases::valid::blocks::{attributes}"),
            move || {
                let mut body = TS.to_owned();
                for (word, text) in [("O", stdout), ("E", stderr), ("C", serial)] {
                    if !text.is_empty() {
                        body.push_str(&format!("Words.\n\n```text\n{word}\n```\n\n"));
                    }
                }
                let case = one_case(&doc(&format!("cmd=\"c\" exit=3 {attributes}"), &body));
                assert_eq!(case.exit, 3);
                assert_eq!(case.stdout.text, stdout);
                assert_eq!(case.stderr.text, stderr);
                assert_eq!(case.serial.text, serial);
                let source = |text: &str| if text.is_empty() { Unnamed } else { Block };
                assert_eq!(case.stdout.source, source(stdout));
                assert_eq!(case.stderr.source, source(stderr));
                assert_eq!(case.serial.source, source(serial));
            },
        );
    }
    // Inline streams: the marker's attributes, the prose after the source, stdout, stderr.
    let inline: &[(&str, &str, &str, &str, &str)] = &[
        ("stdout_word", "stdout=inline", "Stdout: `a`.\n", "a\n", ""),
        (
            "stdout_lowercase",
            "stdout=inline",
            "The stdout is `a`.\n",
            "a\n",
            "",
        ),
        ("stdout_upper", "stdout=inline", "STDOUT `a`\n", "a\n", ""),
        (
            "output_names_stdout",
            "stdout=inline",
            "Output: `a`, `b`, `c`.\n",
            "a\nb\nc\n",
            "",
        ),
        (
            "stderr_word",
            "stderr=inline",
            "Stderr: `e`. Exit status 1.\n",
            "",
            "e\n",
        ),
        (
            "a_later_sentence_is_not_read",
            "stderr=inline",
            "Stderr: `e`. Then `other`.\n",
            "",
            "e\n",
        ),
        (
            "an_earlier_sentence_is_not_read",
            "stderr=inline",
            "See `other`. Stderr: `e`.\n",
            "",
            "e\n",
        ),
        (
            "an_earlier_paragraph_is_not_read",
            "stderr=inline",
            "See `other`.\n\nStderr: `e`.\n",
            "",
            "e\n",
        ),
        (
            "a_period_in_a_span_does_not_end_the_sentence",
            "stdout=inline",
            "Stdout: `a.b c` and `d.`\n",
            "a.b c\nd.\n",
            "",
        ),
        (
            "a_question_ends_a_sentence",
            "stderr=inline",
            "Why `x`? Stderr: `e`.\n",
            "",
            "e\n",
        ),
        (
            "an_exclamation_ends_a_sentence",
            "stderr=inline",
            "Now `x`! Stderr: `e`.\n",
            "",
            "e\n",
        ),
        (
            "a_dot_in_a_word_does_not_end_a_sentence",
            "stderr=inline",
            "Stderr of s08.en: `e`.\n",
            "",
            "e\n",
        ),
        (
            "a_sentence_may_span_lines",
            "stderr=inline",
            "Stderr, on the\nnext line: `e`.\n",
            "",
            "e\n",
        ),
        (
            "a_blank_line_ends_a_sentence",
            "stderr=inline",
            "Stderr:\n\n`e`.\n",
            "",
            "",
        ),
        (
            "a_line_break_in_a_span_is_a_space",
            "stdout=inline",
            "Stdout: `a\nb`.\n",
            "a b\n",
            "",
        ),
        (
            "a_longer_run_does_not_close_a_span",
            "stdout=inline",
            "Stdout: `a``b`.\n",
            "a``b\n",
            "",
        ),
        (
            "a_shorter_run_does_not_close_a_span",
            "stdout=inline",
            "Stdout: ``a`b`` and `c`.\n",
            "a`b\nc\n",
            "",
        ),
        (
            "double_backticks_hold_a_backtick",
            "stdout=inline",
            "Stdout: ``a`b``.\n",
            "a`b\n",
            "",
        ),
        (
            "double_backticks_lose_their_padding",
            "stdout=inline",
            "Stdout: `` `a` ``.\n",
            "`a`\n",
            "",
        ),
        (
            "spaces_in_a_span_stay",
            "stdout=inline",
            "Stdout: `  a  `.\n",
            " a \n",
            "",
        ),
        (
            "an_escaped_backtick_is_no_span",
            "stdout=inline",
            "Stdout \\`no\\` `yes`.\n",
            "yes\n",
            "",
        ),
        (
            "an_unclosed_backtick_is_no_span",
            "stdout=inline",
            "Stdout `yes` then ` nope.\n",
            "yes\n",
            "",
        ),
        (
            "stream_name_in_a_span_does_not_count",
            "stderr=inline",
            "`stderr` is it. Stderr: `e`.\n",
            "",
            "e\n",
        ),
        (
            "output_of_stderr_is_not_stdout",
            "stdout=inline stderr=inline",
            "Stderr output: `e`. Stdout: `o`.\n",
            "o\n",
            "e\n",
        ),
        (
            "both_inline",
            "stdout=inline stderr=inline",
            "Stdout: `o`. Stderr: `e`.\n",
            "o\n",
            "e\n",
        ),
        (
            "both_in_one_sentence",
            "stdout=inline stderr=inline",
            "Stdout and stderr: `x`.\n",
            "x\n",
            "x\n",
        ),
        (
            "output_alias_with_inline_stderr",
            "stdout=inline stderr=inline",
            "Output: `o`.\n\nStderr: `e`.\n",
            "o\n",
            "e\n",
        ),
        (
            "inline_with_a_block_after",
            "stdout=inline stderr=block",
            "Stdout: `o`.\n\n```text\nE\n```\n",
            "o\n",
            "E\n",
        ),
        (
            "inline_after_a_block",
            "stdout=block stderr=inline",
            "Stdout:\n\n```text\nO\n```\n\nStderr: `e`.\n",
            "O\n",
            "e\n",
        ),
    ];
    for &(name, attributes, prose, stdout, stderr) in inline {
        h.case(format!("doc_cases::valid::inline::{name}"), move || {
            let body = format!("{TS}\n{prose}");
            let marker = format!("cmd=\"c\" exit=0 {attributes}");
            if name == "a_blank_line_ends_a_sentence" {
                // `Stderr:` has no span, and the span after the blank line is another
                // sentence, so this must be refused rather than guessed.
                let errors = errors_of(&doc(&marker, &body));
                assert!(errors.to_string().contains("has no code span"), "{errors}");
                return;
            }
            let case = one_case(&doc(&marker, &body));
            assert_eq!(case.stdout.text, stdout);
            assert_eq!(case.stderr.text, stderr);
        });
    }
    h.case("doc_cases::valid::inline_sources_are_marked", || {
        let marker = "cmd=\"c\" exit=0 stdout=inline stderr=block";
        let case = one_case(&doc(
            marker,
            &format!("{TS}Stdout: `o`.\n\n```text\nE\n```\n"),
        ));
        assert_eq!(case.stdout.source, Inline);
        assert_eq!(case.stderr.source, Block);
    });
    let structure: &[(&str, &str, &str)] = &[
        (
            "prose_between_blocks_is_not_read",
            "stdout=block",
            "Stdout: `not this`.\n\n```ts\nsource\n```\n\nStdout: `nor this`.\n\n```text\nO\n```\n",
        ),
        (
            "a_quoted_marker_is_not_a_case",
            "stdout=block",
            "```ts\nsource\n```\n\nThe form is `<!-- case: Y files=a cmd=\"c\" exit=0 -->`.\n\n```text\nO\n```\n",
        ),
        (
            "a_marker_after_words_is_not_a_case",
            "stdout=block",
            "```ts\nsource\n```\n\nsee <!-- case: Y files=a cmd=\"c\" exit=0 -->\n\n```text\nO\n```\n",
        ),
        (
            "a_marker_in_a_block_is_data",
            "stdout=block",
            "```ts\nsource\n```\n\n```text\n<!-- case: Y files=a cmd=\"c\" exit=0 -->\n```\n",
        ),
        (
            "a_heading_in_a_block_is_data",
            "stdout=block",
            "```ts\nsource\n```\n\n```text\n# not a heading\nO\n```\n",
        ),
        (
            "other_block_languages_are_skipped",
            "stdout=block",
            "```rust\nnot it\n```\n```ts\nsource\n```\n```\nnot it\n```\n```text\nO\n```\n",
        ),
        (
            "another_comment_is_skipped",
            "stdout=block",
            "<!-- a note about the case -->\n```ts\nsource\n```\n<!-- case study -->\n```text\nO\n```\n",
        ),
        (
            "a_tilde_fence_is_a_block",
            "stdout=block",
            "~~~ts\nsource\n~~~\n~~~text\nO\n~~~\n",
        ),
        (
            "an_info_string_after_the_language",
            "stdout=block",
            "```ts title=\"a\"\nsource\n```\n```text more\nO\n```\n",
        ),
        (
            "a_long_fence_holds_a_short_one",
            "stdout=block",
            "```ts\nsource\n```\n````text\n```\nO\n```\n````\n",
        ),
        (
            "an_indented_fence_loses_its_indent",
            "stdout=block",
            "  ```ts\n  source\n  ```\n  ```text\n  O\n  ```\n",
        ),
    ];
    for &(name, attributes, body) in structure {
        h.case(format!("doc_cases::valid::structure::{name}"), move || {
            let case = one_case(&doc(&format!("cmd=\"c\" exit=0 {attributes}"), body));
            assert_eq!(case.id, "X");
            assert_eq!(case.files[0].contents, "source\n");
            assert!(case.stdout.text.contains('O') || case.stdout.text.contains("case: Y"));
        });
    }
    h.case("doc_cases::valid::block_bytes_are_verbatim", || {
        let text = "  indented\n\ntrailing space \n\ttab\n\u{3b1}\n\n";
        let body = format!("{TS}```text\n{text}```\n");
        let case = one_case(&doc("cmd=\"c\" exit=0 stdout=block", &body));
        assert_eq!(case.stdout.text, text);
    });
    h.case(
        "doc_cases::valid::a_long_fence_keeps_the_short_one_as_text",
        || {
            let body = format!("{TS}````text\n```\nO\n```\n````\n");
            let case = one_case(&doc("cmd=\"c\" exit=0 stdout=block", &body));
            assert_eq!(case.stdout.text, "```\nO\n```\n");
        },
    );
    h.case(
        "doc_cases::valid::a_fence_with_words_after_it_does_not_close",
        || {
            let body = format!("{TS}```text\n``` not a close\nO\n```\n");
            let case = one_case(&doc("cmd=\"c\" exit=0 stdout=block", &body));
            assert_eq!(case.stdout.text, "``` not a close\nO\n");
        },
    );
    h.case("doc_cases::valid::a_scope_ends_at_the_next_marker", || {
        let text = "<!-- case: A files=a cmd=\"c\" exit=0 -->\n```ts\nA\n```\n\
                    <!-- case: B files=b cmd=\"c\" exit=1 stderr=block -->\n```ts\nB\n```\n```text\nE\n```\n";
        let cases = extract_cases(text).unwrap();
        assert_eq!(cases.len(), 2);
        assert_eq!(cases[0].stderr.text, "");
        assert_eq!(cases[0].exit, 0);
        assert_eq!(cases[1].stderr.text, "E\n");
        assert_eq!(cases[1].line, 5);
    });
    h.case("doc_cases::valid::a_scope_ends_at_the_next_heading", || {
        let text = "<!-- case: A files=a cmd=\"c\" exit=0 -->\n```ts\nA\n```\n\n## Next\n\n```text\nnot its output\n```\n\n```ts\nnor its source\n```\n";
        let case = one_case(text);
        assert_eq!(case.stdout.text, "");
        assert_eq!(case.files.len(), 1);
    });
    h.case(
        "doc_cases::valid::a_hash_without_a_space_is_no_heading",
        || {
            let body = format!("{TS}#hashtag\n\n```text\nO\n```\n");
            let case = one_case(&doc("cmd=\"c\" exit=0 stdout=block", &body));
            assert_eq!(case.stdout.text, "O\n");
        },
    );
    h.case("doc_cases::valid::inline_search_stops_at_a_heading", || {
        let text = "<!-- case: X files=a cmd=\"c\" exit=0 stderr=inline -->\n```ts\nA\n```\n\n## Next\n\nStderr: `e`.\n";
        let errors = errors_of(text);
        assert!(errors.to_string().contains("no sentence names it"), "{errors}");
    });
    let commands: &[(&str, bool)] = &[
        ("enrang dev a.en", true),
        ("enrang build a.en", true),
        ("enrang build --target=i386-none a.en", true),
        ("enrang run a.en", false),
        ("enrang check a.en", false),
        ("enrang test --ci a.en", false),
        ("enrang", false),
        ("build", false),
    ];
    for &(command, may) in commands {
        h.case(
            format!("doc_cases::valid::artefact_rule::{command:?}"),
            move || {
                let case = one_case(&doc(&format!("cmd=\"{command}\" exit=0"), TS));
                assert_eq!(case.may_write_artefact(), may);
            },
        );
    }
    let accepted_exits: &[(&str, i32)] = &[
        ("0", 0),
        ("1", 1),
        ("101", 101),
        ("255", 255),
        ("007", 7),
        ("2147483647", i32::MAX),
    ];
    for &(text, value) in accepted_exits {
        h.case(format!("doc_cases::valid::exit::{text}"), move || {
            let case = one_case(&doc(&format!("cmd=\"c\" exit={text}"), TS));
            assert_eq!(case.exit, value);
        });
    }
    h.case(
        "doc_cases::valid::a_quoted_command_keeps_equals_and_flags",
        || {
            let case = one_case(&doc("cmd=\"enrang build --a=b --c=d e.en\" exit=0", TS));
            assert_eq!(case.cmd, "enrang build --a=b --c=d e.en");
        },
    );
    h.case("doc_cases::valid::ids_may_have_dashes_and_digits", || {
        let case = one_case(&format!(
            "<!-- case: tour-kernel-2 files=a cmd=\"c\" exit=0 -->\n{TS}"
        ));
        assert_eq!(case.id, "tour-kernel-2");
    });
}

fn register_malformed_documents(h: &mut Harness) {
    const C: &str = "cmd=\"c\" exit=0";
    // A whole document, the line of the error and what its message must say.
    let table: &[(&str, String, usize, &str)] = &[
        (
            "no_closing",
            format!("<!-- case: X files=a {C}\n{TS}"),
            1,
            "must end with ` -->`",
        ),
        (
            "closing_on_the_next_line",
            format!("<!-- case: X files=a {C}\n-->\n{TS}"),
            1,
            "must end with ` -->`",
        ),
        (
            "no_id",
            format!("<!-- case: files=a {C} -->\n{TS}"),
            1,
            "is not a case ID",
        ),
        (
            "nothing_at_all",
            "<!-- case:  -->\n".to_owned(),
            1,
            "needs an ID",
        ),
        (
            "id_with_a_bad_character",
            format!("<!-- case: X_1 files=a {C} -->\n{TS}"),
            1,
            "`X_1` is not a case ID",
        ),
        (
            "near_miss_no_space",
            format!("<!--case: X files=a {C} -->\n{TS}"),
            1,
            "must start the line",
        ),
        (
            "near_miss_capital",
            format!("<!-- Case: X files=a {C} -->\n{TS}"),
            1,
            "must start the line",
        ),
        (
            "near_miss_space_before_colon",
            format!("<!-- case : X files=a {C} -->\n{TS}"),
            1,
            "must start the line",
        ),
        (
            "near_miss_indented",
            format!("  <!-- case: X files=a {C} -->\n{TS}"),
            1,
            "must start the line",
        ),
        (
            "no_files",
            format!("<!-- case: X {C} -->\n{TS}"),
            1,
            "the marker has no `files`",
        ),
        (
            "no_cmd",
            format!("<!-- case: X files=a exit=0 -->\n{TS}"),
            1,
            "the marker has no `cmd`",
        ),
        (
            "no_exit",
            format!("<!-- case: X files=a cmd=\"c\" -->\n{TS}"),
            1,
            "the marker has no `exit`",
        ),
        (
            "exit_a_word",
            format!("<!-- case: X files=a cmd=\"c\" exit=one -->\n{TS}"),
            1,
            "`exit=one`",
        ),
        (
            "exit_empty",
            format!("<!-- case: X files=a cmd=\"c\" exit= -->\n{TS}"),
            1,
            "`exit=`",
        ),
        (
            "exit_negative",
            format!("<!-- case: X files=a cmd=\"c\" exit=-1 -->\n{TS}"),
            1,
            "`exit=-1`",
        ),
        (
            "exit_signed",
            format!("<!-- case: X files=a cmd=\"c\" exit=+1 -->\n{TS}"),
            1,
            "`exit=+1`",
        ),
        (
            "exit_overflows",
            format!("<!-- case: X files=a cmd=\"c\" exit=2147483648 -->\n{TS}"),
            1,
            "`exit=2147483648`",
        ),
        (
            "cmd_unquoted",
            format!("<!-- case: X files=a cmd=c exit=0 -->\n{TS}"),
            1,
            "must be double-quoted",
        ),
        (
            "cmd_never_closed",
            format!("<!-- case: X files=a cmd=\"c exit=0 -->\n{TS}"),
            1,
            "never closed",
        ),
        (
            "cmd_empty",
            format!("<!-- case: X files=a cmd=\"\" exit=0 -->\n{TS}"),
            1,
            "`cmd` is empty",
        ),
        (
            "cmd_blank",
            format!("<!-- case: X files=a cmd=\"  \" exit=0 -->\n{TS}"),
            1,
            "`cmd` is empty",
        ),
        (
            "unknown_attribute",
            format!("<!-- case: X files=a {C} since=M1 -->\n{TS}"),
            1,
            "unknown attribute `since`",
        ),
        (
            "a_word_with_no_value",
            format!("<!-- case: X files=a {C} flag -->\n{TS}"),
            1,
            "`flag` is not an attribute",
        ),
        (
            "repeated_attribute",
            format!("<!-- case: X files=a files=b {C} -->\n{TS}"),
            1,
            "`files` is repeated or out of order",
        ),
        (
            "repeated_stream",
            format!("<!-- case: X files=a {C} stdout=block stdout=block -->\n{TS}"),
            1,
            "`stdout` is repeated",
        ),
        (
            "exit_before_cmd",
            format!("<!-- case: X files=a exit=0 cmd=\"c\" -->\n{TS}"),
            1,
            "`cmd` is repeated or out of order",
        ),
        (
            "stderr_before_stdout",
            format!("<!-- case: X files=a {C} stderr=block stdout=block -->\n{TS}"),
            1,
            "`stdout` is repeated or out of order",
        ),
        (
            "serial_before_stderr",
            format!("<!-- case: X files=a {C} serial=block stderr=block -->\n{TS}"),
            1,
            "`stderr` is repeated or out of order",
        ),
        (
            "stdout_bad_value",
            format!("<!-- case: X files=a {C} stdout=file -->\n{TS}"),
            1,
            "`stdout` must be `block` or `inline`, not `file`",
        ),
        (
            "stderr_bad_value",
            format!("<!-- case: X files=a {C} stderr= -->\n{TS}"),
            1,
            "`stderr` must be `block` or `inline`, not ``",
        ),
        (
            "serial_inline",
            format!("<!-- case: X files=a {C} serial=inline -->\n{TS}"),
            1,
            "`serial` must be `block`, not `inline`",
        ),
        (
            "files_empty",
            format!("<!-- case: X files= {C} -->\n{TS}"),
            1,
            "`files` has an empty name",
        ),
        (
            "files_empty_element",
            format!("<!-- case: X files=a,,b {C} -->\n{TS}"),
            1,
            "`files` has an empty name",
        ),
        (
            "files_trailing_comma",
            format!("<!-- case: X files=a, {C} -->\n{TS}"),
            1,
            "`files` has an empty name",
        ),
        (
            "files_absolute",
            format!("<!-- case: X files=/etc/a {C} -->\n{TS}"),
            1,
            "`/etc/a` is not a path inside the case",
        ),
        (
            "files_parent",
            format!("<!-- case: X files=../a {C} -->\n{TS}"),
            1,
            "`../a` is not a path inside the case",
        ),
        (
            "files_inner_parent",
            format!("<!-- case: X files=b/../../a {C} -->\n{TS}"),
            1,
            "is not a path inside the case",
        ),
        (
            "files_twice",
            format!("<!-- case: X files=a,b,a {C} -->\n{TS}"),
            1,
            "`a` is listed twice",
        ),
        (
            "no_source_block",
            format!("<!-- case: X files=a {C} -->\nprose\n"),
            1,
            "`files` lists 1 but 0 `ts` blocks follow",
        ),
        (
            "too_few_source_blocks",
            format!("<!-- case: X files=a,b {C} -->\n{TS}"),
            1,
            "`files` lists 2 but 1 `ts` blocks follow",
        ),
        (
            "too_many_source_blocks",
            format!("<!-- case: X files=a {C} -->\n{TS}{TS}"),
            1,
            "`files` lists 1 but 2 `ts` blocks follow",
        ),
        (
            "a_source_after_an_output",
            format!("<!-- case: X files=a {C} stdout=block -->\n{TS}```text\nO\n```\n{TS}"),
            8,
            "a `ts` block comes after a `text` block",
        ),
        (
            "an_output_before_the_source",
            format!("<!-- case: X files=a {C} stdout=block -->\n```text\nO\n```\n{TS}"),
            5,
            "a `ts` block comes after a `text` block",
        ),
        (
            "missing_output_block",
            format!("<!-- case: X files=a {C} stdout=block -->\n{TS}"),
            1,
            "names 1 `block` streams but 0 `text` blocks follow",
        ),
        (
            "one_of_two_output_blocks",
            format!(
                "<!-- case: X files=a {C} stdout=block stderr=block -->\n{TS}```text\nO\n```\n"
            ),
            1,
            "names 2 `block` streams but 1 `text` blocks follow",
        ),
        (
            "an_extra_output_block",
            format!(
                "<!-- case: X files=a {C} stdout=block -->\n{TS}```text\nO\n```\n```text\nE\n```\n"
            ),
            1,
            "names 1 `block` streams but 2 `text` blocks follow",
        ),
        (
            "an_output_for_no_stream",
            format!("<!-- case: X files=a {C} -->\n{TS}```text\nO\n```\n"),
            1,
            "names 0 `block` streams but 1 `text` blocks follow",
        ),
        (
            "an_inline_stream_with_a_block",
            format!(
                "<!-- case: X files=a {C} stdout=inline -->\n{TS}Stdout: `o`.\n\n```text\nO\n```\n"
            ),
            1,
            "names 0 `block` streams but 1 `text` blocks follow",
        ),
        (
            "an_empty_output_block",
            format!("<!-- case: X files=a {C} stdout=block -->\n{TS}```text\n```\n"),
            5,
            "stdout is named `block` but its block is empty",
        ),
        (
            "an_empty_source_block",
            format!("<!-- case: X files=a {C} -->\n```ts\n```\n"),
            2,
            "source file `a` is empty",
        ),
        (
            "a_source_with_a_blank_last_line",
            format!("<!-- case: X files=a {C} -->\n```ts\nsource\n\n```\n"),
            2,
            "must end with one newline",
        ),
        (
            "inline_with_no_sentence",
            format!("<!-- case: X files=a {C} stdout=inline -->\n{TS}"),
            1,
            "stdout is `inline` but no sentence names it",
        ),
        (
            "inline_naming_another_stream",
            format!("<!-- case: X files=a {C} stderr=inline -->\n{TS}Stdout: `o`.\n"),
            1,
            "stderr is `inline` but no sentence names it",
        ),
        (
            "inline_with_no_span",
            format!("<!-- case: X files=a {C} stderr=inline -->\n{TS}Stderr is empty.\n"),
            1,
            "stderr is `inline` but the sentence naming it has no code span",
        ),
        (
            "inline_only_in_a_span",
            format!("<!-- case: X files=a {C} stderr=inline -->\n{TS}See `stderr`.\n"),
            1,
            "stderr is `inline` but no sentence names it",
        ),
        (
            "inline_only_before_the_source",
            format!("<!-- case: X files=a {C} stderr=inline -->\nStderr: `e`.\n\n{TS}"),
            1,
            "stderr is `inline` but no sentence names it",
        ),
        (
            "a_fence_never_closed",
            format!("<!-- case: X files=a {C} -->\ntext\n```ts\nsource\n"),
            3,
            "never closed",
        ),
        (
            "a_shorter_fence_does_not_close",
            format!("<!-- case: X files=a {C} -->\n````ts\nsource\n```\n"),
            2,
            "never closed",
        ),
        (
            "a_carriage_return",
            format!("# Title\n\n<!-- case: X files=a {C} -->\r\n{TS}"),
            3,
            "carriage return",
        ),
    ];
    for (name, text, line, message) in table.iter().cloned() {
        h.case(format!("doc_cases::malformed::{name}"), move || {
            let errors = errors_of(&text);
            let found = errors
                .0
                .iter()
                .find(|error| error.message.contains(message))
                .unwrap_or_else(|| panic!("no error says {message:?}: {errors}"));
            assert_eq!(found.line, line, "{errors}");
        });
    }
    h.case("doc_cases::malformed::a_duplicate_id", || {
        let text = "<!-- case: A files=a cmd=\"c\" exit=0 -->\n```ts\nA\n```\n\
                    <!-- case: A files=a cmd=\"c\" exit=0 -->\n```ts\nA\n```\n";
        let errors = errors_of(text);
        assert_eq!(errors.0.len(), 1, "{errors}");
        assert_eq!(errors.0[0].line, 5);
        assert!(
            errors.0[0].message.contains("case A: the ID is used twice"),
            "{errors}"
        );
    });
    h.case(
        "doc_cases::malformed::every_problem_is_reported_at_once",
        || {
            let text = "<!-- case: A files=a cmd=\"c\" exit=x -->\n```ts\nA\n```\n\
                    <!-- case: B files=b cmd=\"c\" exit=0 stdout=block -->\n```ts\nB\n```\n\
                    <!-- case: C files=c cmd=\"c\" exit=0 -->\n```ts\nC\n```\n";
            let errors = errors_of(text);
            let lines: Vec<usize> = errors.0.iter().map(|error| error.line).collect();
            assert_eq!(lines, [1, 5], "{errors}");
        },
    );
    h.case("doc_cases::malformed::errors_print_their_lines", || {
        let errors = errors_of(&format!("\n\n<!-- case: X files=a cmd=\"c\" -->\n{TS}"));
        assert_eq!(
            errors.to_string(),
            "line 3: case X: the marker has no `exit`\n"
        );
    });
    h.case(
        "doc_cases::malformed::a_bad_marker_closes_the_scope_before_it",
        || {
            let text = "<!-- case: A files=a cmd=\"c\" exit=0 -->\n```ts\nA\n```\n\
                    <!-- case: B -->\n```text\nnot the output of A\n```\n";
            let errors = errors_of(text);
            assert_eq!(errors.0.len(), 1, "{errors}");
            assert_eq!(errors.0[0].line, 5, "{errors}");
        },
    );
}

fn register_mutations(h: &mut Harness) {
    h.case("doc_cases::mutation::prose_is_never_read", || {
        let garbled = with_garbled_prose(spec());
        assert_ne!(garbled, spec());
        let cases = extract_cases(&garbled).unwrap_or_else(|errors| panic!("{errors}"));
        assert_eq!(cases, spec_cases());
    });
    h.case(
        "doc_cases::mutation::prose_can_change_without_changing_a_case",
        || {
            let changed = spec().replace("Stdout:\n", "Stdout: `decoy`.\n");
            assert_ne!(changed, spec());
            assert_eq!(extract_cases(&changed).unwrap(), spec_cases());
        },
    );
    h.case("doc_cases::mutation::a_quoted_marker_adds_no_case", || {
        let changed = spec().replace(
            "## 15. Sample programs",
            "Quoted: `<!-- case: FAKE files=f.en cmd=\"x\" exit=0 -->`.\n\n## 15. Sample programs",
        );
        assert_ne!(changed, spec());
        assert_eq!(extract_cases(&changed).unwrap().len(), 37);
    });
    h.case(
        "doc_cases::mutation::an_inline_sentence_is_the_source",
        || {
            let changed = spec().replace("Output: `top = 42`", "Output: `top = 43`");
            assert_ne!(changed, spec());
            let cases = extract_cases(&changed).unwrap();
            let tour = cases.iter().find(|case| case.id == "tour").unwrap();
            assert_eq!(tour.stdout.text, "top = 43\n[vm] done\nresult 42\n");
        },
    );
    h.case("doc_cases::mutation::a_block_is_the_source", || {
        let changed = replace_after(spec(), "### S9 ", "sum = 5050", "sum = 5051");
        let cases = extract_cases(&changed).unwrap();
        let kernel = cases.iter().find(|case| case.id == "S9").unwrap();
        assert!(
            kernel.serial.text.contains("sum = 5051"),
            "{}",
            kernel.serial.text
        );
    });
    h.case("doc_cases::mutation::a_new_marker_is_found", || {
        let changed = spec().replace(
            "## 16. Deferred features",
            "<!-- case: NEW files=n.en cmd=\"enrang check n.en\" exit=0 -->\n```ts\nx\n```\n\n## 16. Deferred features",
        );
        let cases = extract_cases(&changed).unwrap();
        assert_eq!(cases.len(), 38);
        assert_eq!(cases[37].id, "NEW");
    });
    // A mutation of the real document, and what the refusal must say.
    let refused: &[(&str, &str, &str, &str, &str)] = &[
        (
            "mislabelled_output",
            "<!-- case: G05",
            "```text",
            "```txt",
            "case G05: the marker names 1 `block` streams but 0",
        ),
        (
            "mislabelled_source",
            "<!-- case: G05",
            "```ts",
            "```tsx",
            "case G05: `files` lists 1 but 0",
        ),
        (
            "stdout_block_with_no_block",
            "<!-- case: G05",
            "stderr=block",
            "stdout=block stderr=block",
            "case G05: the marker names 2",
        ),
        (
            "a_second_file",
            "<!-- case: S3",
            "files=s03.en",
            "files=s03.en,extra.en",
            "case S3: `files` lists 2 but 1",
        ),
        (
            "lost_inline_sentence",
            "<!-- case: S7",
            "Stderr: `error: negative age`.",
            "Stderr went away.",
            "case S7: stderr is `inline` but",
        ),
        (
            "lost_exit",
            "<!-- case: G12",
            " exit=1",
            "",
            "case G12: the marker has no `exit`",
        ),
        (
            "renamed_stream",
            "<!-- case: S9",
            "serial=block",
            "com1=block",
            "case S9: unknown attribute `com1`",
        ),
        (
            "inline_serial",
            "<!-- case: S9",
            "serial=block",
            "serial=inline",
            "case S9: `serial` must be `block`",
        ),
        (
            "a_second_G01",
            "<!-- case: G02",
            "case: G02",
            "case: G01",
            "case G01: the ID is used twice",
        ),
    ];
    for &(name, anchor, from, to, message) in refused {
        h.case(format!("doc_cases::mutation::refused::{name}"), move || {
            let changed = replace_after(spec(), anchor, from, to);
            let errors = errors_of(&changed);
            assert!(errors.to_string().contains(message), "{errors}");
        });
    }
    h.case(
        "doc_cases::mutation::a_lost_marker_loses_only_its_case",
        || {
            let line = spec()
                .lines()
                .find(|line| line.starts_with("<!-- case: G07"))
                .unwrap();
            let changed = spec().replace(&format!("{line}\n"), "");
            let cases = extract_cases(&changed).unwrap();
            assert_eq!(cases.len(), 36);
            assert!(cases.iter().all(|case| case.id != "G07"));
        },
    );
}

fn register_heading_rule(h: &mut Harness) {
    h.case(
        "doc_cases::headings::every_g_and_s_heading_of_spec_has_its_marker",
        || {
            assert_eq!(
                headings_without_cases(spec()).unwrap(),
                Vec::<String>::new()
            );
        },
    );
    for (heading_prefix, id) in [
        ("<!-- case: G07", "G07"),
        ("<!-- case: S10", "S10"),
        ("<!-- case: S1 ", "S1"),
    ] {
        h.case(
            format!("doc_cases::headings::a_lost_marker_is_found::{id}"),
            move || {
                let line = spec()
                    .lines()
                    .find(|line| line.starts_with(heading_prefix))
                    .unwrap();
                let changed = spec().replace(&format!("{line}\n"), "");
                assert_eq!(headings_without_cases(&changed).unwrap(), [id]);
            },
        );
    }
    h.case(
        "doc_cases::headings::a_marker_with_another_id_does_not_count",
        || {
            let changed = spec().replace("<!-- case: S3 ", "<!-- case: S33 ");
            assert_ne!(changed, spec());
            assert_eq!(headings_without_cases(&changed).unwrap(), ["S3"]);
        },
    );
    let table: &[(&str, &str, &[&str])] = &[
        ("no_headings", "text\n", &[]),
        (
            "other_headings",
            "## 14. Golden\n### Summary\n### S\n### G\n### Gx1\n",
            &[],
        ),
        ("one_missing", "### G01 One\n\ntext\n", &["G01"]),
        (
            "several_in_order",
            "### S1 a\n\n### G02 b\n\n### S3 c\n",
            &["S1", "G02", "S3"],
        ),
        (
            "satisfied",
            "### G01 One\n<!-- case: G01 files=a cmd=\"c\" exit=0 -->\n",
            &[],
        ),
        (
            "prose_before_the_marker",
            "### S9 x\n\nProse.\n\n<!-- case: S9 files=a cmd=\"c\" exit=0 -->\n",
            &[],
        ),
        (
            "a_marker_under_the_next_heading",
            "### G01 One\n\n### G02 Two\n<!-- case: G01 files=a cmd=\"c\" exit=0 -->\n",
            &["G01", "G02"],
        ),
        (
            "a_malformed_marker_does_not_count",
            "### G01 One\n<!-- case: G01 -->\n",
            &["G01"],
        ),
        ("a_heading_in_a_fence", "```\n### G01 One\n```\n", &[]),
        ("any_heading_level", "# G1\n## S2\n", &["G1", "S2"]),
    ];
    for &(name, text, expected) in table {
        h.case(format!("doc_cases::headings::{name}"), move || {
            assert_eq!(headings_without_cases(text).unwrap(), expected);
        });
    }
    h.case(
        "doc_cases::headings::an_unterminated_fence_is_refused",
        || {
            assert!(headings_without_cases("```\n### G01 One\n").is_err());
        },
    );
}
