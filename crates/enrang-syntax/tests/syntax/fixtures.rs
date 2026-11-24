//! The anchored compile fixtures of the codes this crate reports (TESTING 7 and 18,
//! M1 plan d.6), run in process, as `check` runs phase 1.
//!
//! A fixture is `tests/compile/<CODE>/<name>.fail.en`: each line that must report a
//! code carries `//~ <CODE>`, and the set of (line, code) pairs reported must equal
//! the set the anchors name. The name is TESTING 7's for an anchored snippet file,
//! which `enrang fmt` skips, so no anchor ever moves off its line. A near-miss,
//! `<name>.pass.en`, carries no anchor and reports nothing. `enrang-cli` runs the same files through `enrang check` as a process and
//! keeps their rendered output as goldens, and the gating meta-test counts them as
//! the evidence of each `Compile` row; here they run against the parser alone, so a
//! failure names the diagnostic and not just the transcript.

use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;
use std::sync::Arc;

use enrang_base::{FileOrigin, SourceMap};
use enrang_diag::{CURRENT_MILESTONE, Code, DiagCtx, FixtureKind, Milestone, Owner, Phase};
use enrang_syntax::{
    Contextual, NodeIdGen, ParseMode, TokenKind, decode_source, lex, parse_file,
    report_invalid_utf8,
};
use enrang_testkit::{Harness, Reported, RunOptions, anchors, compare, workspace_root};

/// Where the fixtures are, from the workspace root.
const FIXTURES: &str = "tests/compile";

/// One fixture file.
#[derive(Clone, Debug)]
struct Fixture {
    /// Its path from the workspace root, as diagnostics show it.
    path: String,
    /// The code its directory names.
    code: Code,
    /// A near-miss, which must report nothing.
    near_miss: bool,
    bytes: Vec<u8>,
}

/// Every fixture of a code this crate reports, in path order.
fn fixtures() -> Vec<Fixture> {
    let root = workspace_root().join(FIXTURES);
    let mut found = Vec::new();
    let mut directories: Vec<_> = fs::read_dir(&root)
        .unwrap_or_else(|error| panic!("cannot read {FIXTURES}: {error}"))
        .map(|entry| entry.expect("an entry").file_name())
        .collect();
    directories.sort();
    for directory in directories {
        let name = directory.to_string_lossy().into_owned();
        let Some(code) = Code::from_name(&name) else {
            continue;
        };
        if !is_ours(code) {
            continue;
        }
        let mut files: Vec<_> = fs::read_dir(root.join(&name))
            .expect("a fixture directory")
            .map(|entry| entry.expect("an entry").file_name())
            .collect();
        files.sort();
        for file in files {
            let file = file.to_string_lossy().into_owned();
            if !file.ends_with(".en") {
                continue;
            }
            assert!(
                file.ends_with(".fail.en") || file.ends_with(".pass.en"),
                "{FIXTURES}/{name}/{file} is neither <name>.fail.en nor <name>.pass.en"
            );
            let path = format!("{FIXTURES}/{name}/{file}");
            let bytes = fs::read(workspace_root().join(&path)).expect("a fixture");
            found.push(Fixture {
                near_miss: file.ends_with(".pass.en"),
                path,
                code,
                bytes,
            });
        }
    }
    found
}

/// The firing fixtures of a phase 1 code whose anchors phase 2 reports, each with
/// why: the code is "also phase 2" in the registry.
const PHASE_TWO: &[(&str, &str)] = &[(
    "tests/compile/EN0214/rr-05.fail.en",
    "a `readonly` before a named result type waits for name resolution (S:253-257, RR-05)",
)];

/// Whether this crate reports `code`: a phase 1 code of the `syntax` owner.
fn is_ours(code: Code) -> bool {
    code.owner() == Owner::Syntax
        && code.phase() == Phase::Syntax
        && code.fixture() == FixtureKind::Compile
}

/// What phase 1 reports for a file, as the driver runs it for `check`.
fn phase_one(path: &str, bytes: &[u8]) -> Vec<Reported> {
    let decoded = decode_source(bytes);
    let mut map = SourceMap::new();
    let text: Arc<str> = Arc::from(decoded.text.as_str());
    let id = map.add(PathBuf::from(path), text, FileOrigin::User);
    let file = map.file(id).clone();
    let mut dcx = DiagCtx::new();
    report_invalid_utf8(&file, &decoded.invalid, &mut dcx);
    parse_file(&file, &mut NodeIdGen::new(), ParseMode::Test, &mut dcx);
    dcx.take()
        .into_iter()
        .map(|diag| {
            let span = diag.primary.span;
            let at = (!span.is_dummy()).then(|| {
                let loc = map.loc(span.lo);
                (path.to_owned(), loc.line as usize, loc.col as usize)
            });
            Reported {
                code: diag.code.name().to_owned(),
                message: diag.message,
                at,
            }
        })
        .collect()
}

fn listing(reported: &[Reported]) -> String {
    reported
        .iter()
        .map(|diag| match diag.line() {
            Some(line) => format!("  line {line}: {}: {}\n", diag.code, diag.message),
            None => format!("  no place: {}: {}\n", diag.code, diag.message),
        })
        .collect()
}

/// A firing fixture names its own code and reports exactly what it anchors.
fn fires(fixture: &Fixture) -> Result<(), String> {
    let text = String::from_utf8_lossy(&fixture.bytes);
    let anchors = anchors(&text).map_err(|error| format!("{}: {error}", fixture.path))?;
    if !anchors
        .iter()
        .any(|anchor| anchor.code == fixture.code.name())
    {
        return Err(format!(
            "{} is in the directory of {} but anchors no {}",
            fixture.path, fixture.code, fixture.code
        ));
    }
    let reported = phase_one(&fixture.path, &fixture.bytes);
    // A fixture whose anchors only phase 2 reports: phase 1 reports nothing for it,
    // and the cli suite checks the anchors through `check`.
    if PHASE_TWO.iter().any(|(path, _)| *path == fixture.path) {
        return match reported.is_empty() {
            true => Ok(()),
            false => Err(format!(
                "{}: phase 1 reports, though its anchors are phase 2's:\n{}",
                fixture.path,
                listing(&reported)
            )),
        };
    }
    compare(&anchors, &reported).map_err(|mismatch| {
        format!(
            "{}:\n{mismatch}reported:\n{}",
            fixture.path,
            listing(&reported)
        )
    })
}

/// A near-miss has no anchor and reports nothing.
fn passes(fixture: &Fixture) -> Result<(), String> {
    let text = String::from_utf8_lossy(&fixture.bytes);
    let anchors = anchors(&text).map_err(|error| format!("{}: {error}", fixture.path))?;
    if !anchors.is_empty() {
        return Err(format!("the near-miss {} has anchors", fixture.path));
    }
    let reported = phase_one(&fixture.path, &fixture.bytes);
    if reported.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "the near-miss {} reports:\n{}",
            fixture.path,
            listing(&reported)
        ))
    }
}

/// The names every module sees without declaring them (SPEC 12, "Implicit in every
/// module"): the primitive types, the `core` and `alloc` names, `console`, and the
/// compiler forms of SPEC 6. The contextual words of SPEC 2 (`test`, `from`, ...) are
/// never counted as uses.
const PRELUDE: &[&str] = &[
    "i8",
    "i16",
    "i32",
    "i64",
    "i128",
    "u8",
    "u16",
    "u32",
    "u64",
    "u128",
    "isize",
    "usize",
    "int",
    "f32",
    "f64",
    "bool",
    "char",
    "string",
    "Copy",
    "Clone",
    "Eq",
    "Ord",
    "Display",
    "Error",
    "Formatter",
    "Result",
    "Failure",
    "Slice",
    "Ok",
    "Err",
    "Box",
    "GlobalAllocator",
    "FreeListHeap",
    "console",
    "mem",
    "ptr",
    "panic",
    "dispose",
    "sizeOf",
    "alignOf",
    "offsetOf",
];

/// A token of a near-miss, as the name check reads it.
struct Word {
    text: String,
    ident: bool,
    space_before: bool,
}

fn words(text: &str) -> Vec<Word> {
    let mut map = SourceMap::new();
    let id = map.add(PathBuf::from("x.en"), Arc::from(text), FileOrigin::User);
    let mut dcx = DiagCtx::new();
    lex(map.file(id), &mut dcx)
        .into_iter()
        .filter(|token| token.kind != TokenKind::Eof)
        .map(|token| {
            let (text, ident) = match token.kind {
                TokenKind::Ident(name) => (name.as_str().to_owned(), true),
                TokenKind::Keyword(word) => (word.as_str().to_owned(), false),
                TokenKind::Punct(punct) => (punct.as_str().to_owned(), false),
                _ => ("<literal>".to_owned(), false),
            };
            Word {
                text,
                ident,
                space_before: token.space_before,
            }
        })
        .collect()
}

/// The index of the bracket that closes the one at `open`, if it closes before a
/// `;`. A `>>` or `>>>` closes two or three angle brackets.
fn closing(words: &[Word], open: usize) -> Option<usize> {
    let (opens, closes): (&str, &[&str]) = match words[open].text.as_str() {
        "(" => ("(", &[")"]),
        "[" => ("[", &["]"]),
        "{" => ("{", &["}"]),
        "<" => ("<", &[">", ">>", ">>>"]),
        _ => return None,
    };
    let mut depth = 0usize;
    for (at, word) in words.iter().enumerate().skip(open) {
        if word.text == opens {
            depth += 1;
        } else if let Some(width) = closes.iter().position(|close| word.text == *close) {
            depth = depth.saturating_sub(width + 1);
            if depth == 0 {
                return Some(at);
            }
        } else if word.text == ";" && opens != "{" {
            return None;
        }
    }
    None
}

/// The type parameters between the angle brackets at `open` and `close`: each name
/// right after the `<` or a `,` of that level, as `T` in `<T extends Shape & Named>`.
fn type_parameters(words: &[Word], open: usize, close: usize, declared: &mut BTreeSet<String>) {
    let mut depth = 0usize;
    for at in open..close {
        match words[at].text.as_str() {
            "<" => depth += 1,
            ">" => depth = depth.saturating_sub(1),
            _ => {}
        }
        let starts = depth == 1 && (words[at].text == "<" || words[at].text == ",");
        if starts && words[at + 1].ident {
            declared.insert(words[at + 1].text.clone());
        }
    }
}

/// The names `text` uses that it does not declare and the prelude does not hold,
/// read from its tokens. Scopes are ignored, so a name declared anywhere counts:
/// the check is for names nothing declares, which name resolution reports from M2
/// (EN0301 and EN0302), whatever phase 1 says now.
fn undeclared(text: &str) -> Vec<String> {
    let words = words(text);
    let is = |at: usize, wanted: &str| words.get(at).is_some_and(|word| word.text == wanted);
    let mut declared = BTreeSet::new();
    for (at, word) in words.iter().enumerate() {
        if !word.ident {
            let declares = [
                "const",
                "let",
                "function",
                "class",
                "interface",
                "enum",
                "type",
            ];
            if declares.contains(&word.text.as_str()) {
                if words.get(at + 1).is_some_and(|next| next.ident) {
                    declared.insert(words[at + 1].text.clone());
                    if is(at + 2, "<")
                        && let Some(close) = closing(&words, at + 2)
                    {
                        type_parameters(&words, at + 2, close, &mut declared);
                    }
                    if word.text == "enum"
                        && is(at + 2, "{")
                        && let Some(close) = closing(&words, at + 2)
                    {
                        for case in at + 3..close {
                            let first = is(case - 1, "{") || is(case - 1, ",");
                            if first && words[case].ident {
                                declared.insert(words[case].text.clone());
                            }
                        }
                    }
                } else if (is(at + 1, "[") || is(at + 1, "{"))
                    && let Some(close) = closing(&words, at + 1)
                {
                    for inner in &words[at + 2..close] {
                        if inner.ident {
                            declared.insert(inner.text.clone());
                        }
                    }
                }
            }
            if word.text == "import"
                && is(at + 1, "{")
                && let Some(close) = closing(&words, at + 1)
            {
                for inner in &words[at + 2..close] {
                    if inner.ident {
                        declared.insert(inner.text.clone());
                    }
                }
            }
            if word.text == "as" && words.get(at + 1).is_some_and(|next| next.ident) {
                let imported = words[..at].iter().rev().any(|w| w.text == "import")
                    && !words[..at]
                        .iter()
                        .rev()
                        .take_while(|w| w.text != "import")
                        .any(|w| w.text == ";");
                if imported {
                    declared.insert(words[at + 1].text.clone());
                }
            }
            continue;
        }
        // A parameter, a field, a key or a label.
        if is(at + 1, ":") || (is(at + 1, "?") && is(at + 2, ":")) || is(at + 1, "=>") {
            declared.insert(word.text.clone());
        }
        // A function or method signature, `name<T>(...)` followed by `:` or `{`, and
        // an arrow's parameters, `(x, y) =>`.
        let mut after = at + 1;
        let mut generics = None;
        if is(after, "<")
            && !words[after].space_before
            && let Some(close) = closing(&words, after)
        {
            generics = Some((after, close));
            after = close + 1;
        }
        if is(after, "(")
            && let Some(close) = closing(&words, after)
        {
            if is(close + 1, ":") || is(close + 1, "{") {
                declared.insert(word.text.clone());
                if let Some((open, close)) = generics {
                    type_parameters(&words, open, close, &mut declared);
                }
            }
        }
        if is(at.wrapping_sub(1), "(")
            && let Some(close) = closing(&words, at - 1)
            && is(close + 1, "=>")
        {
            for inner in &words[at..close] {
                if inner.ident {
                    declared.insert(inner.text.clone());
                }
            }
        }
    }
    let mut used = BTreeSet::new();
    for (at, word) in words.iter().enumerate() {
        let member = at > 0 && (is(at - 1, ".") || is(at - 1, "@"));
        let key = is(at + 1, ":") || (is(at + 1, "?") && is(at + 2, ":"));
        let contextual = Contextual::from_name(&word.text).is_some();
        if word.ident && !member && !key && !contextual {
            used.insert(word.text.clone());
        }
    }
    used.into_iter()
        .filter(|name| !declared.contains(name) && !PRELUDE.contains(&name.as_str()))
        .collect()
}

/// The codes of this crate whose fixtures must exist now: those due by the milestone
/// being built, M1, or by the current one when that is later.
fn due() -> Vec<Code> {
    let by = CURRENT_MILESTONE.max(Milestone::M1);
    Code::ALL
        .iter()
        .copied()
        .filter(|&code| is_ours(code) && code.since() <= by)
        .collect()
}

/// Registers a case for each of `fixtures`. The real fixtures and the self-test's
/// both go through here, so no case can skip its fixture.
fn register_fixtures(h: &mut Harness, fixtures: Vec<Fixture>) {
    for fixture in fixtures {
        let name = fixture.path.trim_start_matches("tests/").to_owned();
        if fixture.near_miss {
            h.case(format!("fixtures/{name} reports nothing"), move || {
                passes(&fixture)
            });
        } else {
            h.case(
                format!("fixtures/{name} reports what it anchors"),
                move || fires(&fixture),
            );
        }
    }
}

pub fn register(h: &mut Harness) {
    register_fixtures(h, fixtures());
    h.case(
        "fixtures/the registered cases fail fixtures that break their rules",
        || {
            let fixture = |name: &str, text: &str| Fixture {
                path: format!("tests/compile/EN0201/{name}"),
                code: Code::EN0201,
                near_miss: name.ends_with(".pass.en"),
                bytes: text.as_bytes().to_vec(),
            };
            let mut inner = Harness::new("fixtures");
            register_fixtures(
                &mut inner,
                vec![
                    fixture("good.fail.en", "const y = a === b; //~ EN0201\n"),
                    fixture("good.pass.en", "const y = a == b;\n"),
                    fixture("broken.pass.en", "const broken = a == ;\n"),
                    fixture("anchored.pass.en", "const y = a == b; //~ EN0201\n"),
                    fixture("silent.fail.en", "const y = a == b; //~ EN0201\n"),
                    fixture("wrong_code.fail.en", "const y = a === b; //~ EN0202\n"),
                ],
            );
            let quiet = RunOptions {
                quiet: true,
                ..RunOptions::default()
            };
            let report = inner.run_with(&quiet, &mut Vec::new());
            let failed: Vec<&str> = report.failed.iter().map(String::as_str).collect();
            assert_eq!(
                failed,
                [
                    "fixtures/compile/EN0201/broken.pass.en reports nothing",
                    "fixtures/compile/EN0201/anchored.pass.en reports nothing",
                    "fixtures/compile/EN0201/silent.fail.en reports what it anchors",
                    "fixtures/compile/EN0201/wrong_code.fail.en reports what it anchors",
                ]
            );
            assert_eq!(report.passed, 2, "{report:?}");
        },
    );
    h.case(
        "fixtures/every code due by M1 has a firing fixture and a near-miss",
        || {
            let all = fixtures();
            let due = due();
            assert!(due.len() >= 65, "{}", due.len());
            for code in due {
                let mine = || all.iter().filter(move |fixture| fixture.code == code);
                assert!(mine().any(|f| !f.near_miss), "{code} has no firing fixture");
                assert!(mine().any(|f| f.near_miss), "{code} has no near-miss");
            }
        },
    );
    h.case(
        "fixtures/a near-miss declares every name it uses, so names resolve from M2",
        || {
            let mut missing = Vec::new();
            for fixture in fixtures().iter().filter(|fixture| fixture.near_miss) {
                let names = undeclared(&String::from_utf8_lossy(&fixture.bytes));
                if !names.is_empty() {
                    missing.push(format!("{}: {}", fixture.path, names.join(", ")));
                }
            }
            assert!(missing.is_empty(), "undeclared:\n{}", missing.join("\n"));
        },
    );
    let rows: &[(&str, &[&str])] = &[
        ("const file = open(\"log\");\n", &["open"]),
        (
            "const file = open(\"log\");\nfunction open(p: &string): i64 { return 1; }\n",
            &[],
        ),
        (
            "public function show<T extends Shape & Named>(s: &T): void { console.log(s); }\n",
            &["Named", "Shape"],
        ),
        ("let go = true;\nouter: while (go) { break outer; }\n", &[]),
        (
            "public class A {\n  private n: i64 = 0;\n\n  public m(): i64 { return this.n; }\n}\n",
            &[],
        ),
        (
            "public enum E { A, B }\nconst e = E.A;\nconsole.log(e, F);\n",
            &["F"],
        ),
        ("const f = (x, y) => x + y;\nconst g = z => z;\n", &[]),
        ("const [a, b] = [1, 2];\nconst { c, d } = p;\n", &["p"]),
        (
            "wrap<Foo>(1);\nf(a < b, c > (d));\n",
            &["Foo", "a", "b", "c", "d", "f", "wrap"],
        ),
        ("import { x as y } from \"./m\";\nconsole.log(y);\n", &[]),
        (
            "const q = 0 as *Box<i32>;\nconst r = new Point { x: 1 };\n",
            &["Point"],
        ),
    ];
    for (text, expected) in rows {
        let (text, expected) = (*text, *expected);
        h.case(
            format!("fixtures/the names {text:?} leaves undeclared"),
            move || {
                assert_eq!(undeclared(text), expected);
            },
        );
    }
    h.case(
        "fixtures/the checks fail a fixture that does not fire, or fires more",
        || {
            let fixture = |path: &str, text: &str| Fixture {
                path: path.to_owned(),
                code: Code::EN0201,
                near_miss: path.ends_with(".pass.en"),
                bytes: text.as_bytes().to_vec(),
            };
            let good = fixture("x.en", "const y = a === b; //~ EN0201\n");
            assert_eq!(fires(&good), Ok(()));
            let silent = fixture("x.en", "const y = a == b; //~ EN0201\n");
            assert!(fires(&silent).is_err());
            let more = fixture("x.en", "const y = a === b //~ EN0201\nf();\n");
            assert!(fires(&more).unwrap_err().contains("EN0101 is reported"));
            let elsewhere = fixture("x.en", "const y = a !== b; //~ EN0101\n");
            assert!(fires(&elsewhere).unwrap_err().contains("anchors no EN0201"));
            let wrong_line = fixture("x.en", "//~ EN0201\nconst y = a === b;\n");
            assert!(fires(&wrong_line).is_err());
            let wrong_words = fixture("x.en", "const y = a === b; //~ EN0201 \"`!==`\"\n");
            assert!(
                fires(&wrong_words)
                    .unwrap_err()
                    .contains("no EN0201 message")
            );
            let near = fixture("x.pass.en", "const y = a == b;\n");
            assert_eq!(passes(&near), Ok(()));
            let noisy = fixture("x.pass.en", "const y = a === b;\n");
            assert!(passes(&noisy).is_err());
            let anchored = fixture("x.pass.en", "const y = a == b; //~ EN0201\n");
            assert!(passes(&anchored).unwrap_err().contains("has anchors"));
        },
    );
}
