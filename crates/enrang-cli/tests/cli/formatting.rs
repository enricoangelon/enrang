//! `enrang fmt` and `fmt --check` as processes, passing the four tests of TESTING 17
//! with its Quotes and import-order cases (TESTING 23, M1).
//!
//! Each input goes through the real binary, from a file and from standard input, and
//! must pass the four tests: the tree is the same after formatting, apart from the
//! order of import lines and of the names in each import list; a second run changes
//! nothing, and `fmt --check` agrees; every comment keeps its text and order, apart
//! from the leading spaces of its first line and of `*` lines and trailing spaces;
//! and every `ts` block of SPEC except G01-G04 is already formatted. The inputs are
//! TESTING 17's fixed cases, `EF-05` for the Quotes rule and `EF-11` for the Imports
//! rule, read from the document, each as it is and with comments around it. The
//! syntax suite runs the same tests in process, on many more inputs.

use std::fs;

use enrang_diag::RenderOpts;
use enrang_driver::Session;
use enrang_syntax::ast::{File, ImportKind};
use enrang_syntax::{ParseMode, TokenKind, erase, lex};
use enrang_testkit::{Harness, TempDir, extract_cases, fenced_blocks, workspace_root};

use crate::support::{enrang_fed, enrang_in, strings};

/// The G cases SPEC 14 gives syntax errors on purpose.
const INVALID: [&str; 4] = ["G01", "G02", "G03", "G04"];

/// EF-11's group sorted as TESTING 17 states: `public import { Z } from "./z";`
/// first, then the paths `"a"`, `"b"` and `"core"`, each in the double quotes the
/// Quotes rule gives them.
const EF11_SORTED: &str = "public import { Z } from \"./z\";\n\
                           import { b } from \"a\";\n\
                           import { a } from \"b\";\n\
                           import * as core from \"core\";\n";

fn doc(name: &str) -> String {
    let path = workspace_root().join("docs").join(name);
    fs::read_to_string(&path).unwrap_or_else(|error| panic!("docs/{name}: {error}"))
}

fn backticked(line: &str) -> Vec<String> {
    line.split('`')
        .skip(1)
        .step_by(2)
        .map(str::to_owned)
        .collect()
}

/// The code spans of the line of TESTING 17 that fixes EF-05 and EF-11.
fn ef_spans() -> Vec<String> {
    let testing = doc("TESTING.md");
    let line = testing
        .lines()
        .find(|line| line.contains("(`EF-05`)") && line.contains("(`EF-11`)"))
        .expect("TESTING 17 states EF-05 and EF-11");
    backticked(line)
}

/// EF-05's pairs: each literal between `EF-05` and `EF-11`, and the one it becomes.
fn ef05() -> Vec<(String, String)> {
    let spans = ef_spans();
    let from = spans.iter().position(|s| s == "EF-05").expect("EF-05") + 1;
    let to = spans.iter().position(|s| s == "EF-11").expect("EF-11");
    spans[from..to]
        .chunks(2)
        .filter(|pair| pair.len() == 2)
        .map(|pair| (pair[0].clone(), pair[1].clone()))
        .collect()
}

/// EF-11's group as TESTING 17 writes it: the import lines after `EF-11`, until one
/// repeats.
fn ef11() -> String {
    let spans = ef_spans();
    let from = spans.iter().position(|s| s == "EF-11").expect("EF-11") + 1;
    let mut lines: Vec<&String> = Vec::new();
    for span in &spans[from..] {
        if !span.contains("import ") || lines.contains(&span) {
            break;
        }
        lines.push(span);
    }
    lines.iter().map(|line| format!("{line}\n")).collect()
}

/// An input of the four tests, and its canonical text where TESTING 17 fixes it.
#[derive(Clone, Debug)]
struct Input {
    name: String,
    text: String,
    canonical: Option<String>,
}

fn inputs() -> Vec<Input> {
    let mut inputs = Vec::new();
    for (index, (from, to)) in ef05().into_iter().enumerate() {
        let n = index + 1;
        inputs.push(Input {
            name: format!("EF-05 #{n}"),
            text: format!("const s = {from};\n"),
            canonical: Some(format!("const s = {to};\n")),
        });
        inputs.push(Input {
            name: format!("EF-05 #{n} with comments"),
            text: format!("// EF-05, case {n}\nconst s = {from}; // the quote\n/* last */\n"),
            canonical: None,
        });
    }
    let group = ef11();
    inputs.push(Input {
        name: "EF-11".to_owned(),
        text: group.clone(),
        canonical: Some(EF11_SORTED.to_owned()),
    });
    inputs.push(Input {
        name: "EF-11 with comments".to_owned(),
        text: format!("// the group of EF-11\n\n{group}\n/* after the group */\n"),
        canonical: None,
    });
    inputs
}

/// `enrang fmt` of `text` read from standard input.
fn fmt_stdin(text: &str) -> Result<String, String> {
    let dir = TempDir::new("fmt-stdin");
    let ran = enrang_fed(dir.path(), &strings(&["fmt"]), text.as_bytes());
    if (ran.code, ran.stderr.as_str()) != (0, "") {
        return Err(format!("`enrang fmt` of standard input: {ran:?}"));
    }
    Ok(ran.stdout)
}

/// `enrang fmt f.en` of `text`, which rewrites the file in place and prints nothing.
fn fmt_file(text: &str) -> Result<String, String> {
    let dir = TempDir::new("fmt-file");
    dir.write("f.en", text);
    let ran = enrang_in(dir.path(), &strings(&["fmt", "f.en"]));
    if (ran.code, ran.stdout.as_str(), ran.stderr.as_str()) != (0, "", "") {
        return Err(format!("`enrang fmt f.en`: {ran:?}"));
    }
    Ok(fs::read_to_string(dir.join("f.en")).expect("the file"))
}

/// Whether `enrang fmt --check` says `text` would change, from a file and from
/// standard input, which must agree and leave the file as it was.
fn would_change(text: &str) -> Result<bool, String> {
    let dir = TempDir::new("fmt-check");
    dir.write("f.en", text);
    let file = enrang_in(dir.path(), &strings(&["fmt", "--check", "f.en"]));
    let kept = fs::read_to_string(dir.join("f.en")).expect("the file");
    if kept != text {
        return Err("`fmt --check` changed the file".to_owned());
    }
    let stdin = enrang_fed(dir.path(), &strings(&["fmt", "--check"]), text.as_bytes());
    let says = |path: &str| format!("{path} would be reformatted\n1 of 1 file would change\n");
    let changed = (file.code, file.stdout.clone(), file.stderr.as_str()) == (1, says("f.en"), "")
        && (stdin.code, stdin.stdout.clone(), stdin.stderr.as_str()) == (1, says("<stdin>"), "");
    let unchanged = (file.code, file.stdout.as_str(), file.stderr.as_str()) == (0, "", "")
        && (stdin.code, stdin.stdout.as_str(), stdin.stderr.as_str()) == (0, "", "");
    match (changed, unchanged) {
        (true, false) => Ok(true),
        (false, true) => Ok(false),
        _ => Err(format!(
            "`fmt --check`: from a file {file:?}, from standard input {stdin:?}"
        )),
    }
}

/// The erased tree of `text`, or the diagnostics it gives.
fn tree(text: &str) -> Result<File, String> {
    let mut session = Session::new();
    let id = session.add_source("f.en".into(), text.as_bytes());
    let tree = session.parse(id, ParseMode::Test);
    let rendered = session.render(&RenderOpts { color: false });
    if rendered.is_empty() {
        Ok(erase(&tree))
    } else {
        Err(format!("{rendered}in:\n{text}"))
    }
}

/// `file` with its import lines in the order of the Imports rule of SPEC 12.5, for an
/// input whose imports form one group with no comment in it: stably by the value of
/// each path, and the names of each list by the name imported, in byte order.
fn imports_sorted(mut file: File) -> File {
    file.imports
        .sort_by(|a, b| a.path.value.as_str().cmp(b.path.value.as_str()));
    for import in &mut file.imports {
        if let ImportKind::Named(names) = &mut import.kind {
            names.sort_by(|a, b| a.name.name.as_str().cmp(b.name.name.as_str()));
        }
    }
    file
}

/// The comments of `text`, found in the gaps between its tokens, as TESTING 17
/// compares them: without the leading spaces of the first line and of `*` lines, and
/// without trailing spaces.
fn comments(text: &str) -> Vec<String> {
    let mut session = Session::new();
    let id = session.add_source("c.en".into(), text.as_bytes());
    let file = session.map.file(id);
    let start = file.start.0 as usize;
    let tokens = lex(file, &mut session.dcx);
    let mut found = Vec::new();
    let mut lo = 0;
    for token in &tokens {
        let hi = token.span.lo.0 as usize - start;
        let mut gap = &text[lo..hi];
        while let Some(at) = gap.find('/') {
            let tail = &gap[at..];
            let len = if tail.starts_with("//") {
                tail.find('\n').unwrap_or(tail.len())
            } else if let Some(body) = tail.strip_prefix("/*") {
                body.find("*/").map_or(tail.len(), |end| end + 4)
            } else {
                gap = &gap[at + 1..];
                continue;
            };
            let lines: Vec<String> = tail[..len]
                .split('\n')
                .enumerate()
                .map(|(index, line)| {
                    let line = line.trim_end();
                    if index == 0 || line.trim_start().starts_with('*') {
                        line.trim_start().to_owned()
                    } else {
                        line.to_owned()
                    }
                })
                .collect();
            found.push(lines.join("\n"));
            gap = &tail[len..];
        }
        lo = token.span.hi.0 as usize - start;
        if token.kind == TokenKind::Eof {
            break;
        }
    }
    found
}

/// Every `ts` block of SPEC except those of G01-G04, as a path in a directory and its
/// text: each case's files under `case-<ID>/` with the names its marker gives, and
/// every other block as `block-<line>.en`, or `.test.en` when it holds a test item at
/// its top level, as SPEC 12.1 and 12.3 write test files.
fn spec_blocks() -> Vec<(String, String)> {
    let spec = doc("SPEC.md");
    let cases = extract_cases(&spec).unwrap_or_else(|errors| panic!("{errors}"));
    let mut in_cases = Vec::new();
    let mut blocks = Vec::new();
    for case in &cases {
        for file in &case.files {
            in_cases.push(file.contents.clone());
            if !INVALID.contains(&case.id.as_str()) {
                blocks.push((
                    format!("case-{}/{}", case.id, file.name),
                    file.contents.clone(),
                ));
            }
        }
    }
    for block in fenced_blocks(&spec).unwrap_or_else(|errors| panic!("{errors}")) {
        if block.lang != "ts" || in_cases.contains(&block.contents) {
            continue;
        }
        let tests = block.contents.lines().any(|line| {
            ["describe(", "test(", "test.", "compileFails(", "compileOk("]
                .iter()
                .any(|start| line.starts_with(start))
        });
        let suffix = if tests { ".test.en" } else { ".en" };
        blocks.push((format!("block-{:04}{suffix}", block.line), block.contents));
    }
    blocks
}

/// A directory holding every SPEC block under `spec/`, and the canary file
/// `spec/zz-canary.en`, which is not formatted, so that `fmt --check` names how many
/// files it read.
fn spec_tree() -> (TempDir, Vec<(String, String)>) {
    let dir = TempDir::new("fmt-spec");
    let blocks = spec_blocks();
    for (path, text) in &blocks {
        dir.write(&format!("spec/{path}"), text);
    }
    dir.write("spec/zz-canary.en", "const   canary=1;\n");
    (dir, blocks)
}

pub fn register(h: &mut Harness) {
    h.case(
        "formatting/the fixed cases are read from TESTING 17",
        || {
            let names: Vec<String> = inputs().into_iter().map(|input| input.name).collect();
            assert_eq!(names.len(), 8, "{names:?}");
            assert_eq!(ef05().len(), 3);
            assert_eq!(ef11().lines().count(), 4);
            assert_eq!(
                imports_sorted(tree(&ef11()).expect("EF-11 parses")),
                tree(EF11_SORTED).expect("the sorted group parses")
            );
        },
    );
    for input in inputs() {
        let name = input.name.clone();
        let case = input.clone();
        h.case(
            format!("formatting/{name}/the tree is the same after fmt"),
            move || -> Result<(), String> {
                let out = fmt_stdin(&case.text)?;
                if fmt_file(&case.text)? != out {
                    return Err("a file and standard input are formatted apart".to_owned());
                }
                let before = imports_sorted(tree(&case.text)?);
                let after = tree(&out)?;
                if before != after {
                    return Err(format!("the tree changed; fmt printed:\n{out}"));
                }
                Ok(())
            },
        );
        let case = input.clone();
        h.case(
            format!("formatting/{name}/a second fmt changes nothing, and --check agrees"),
            move || -> Result<(), String> {
                let out = fmt_stdin(&case.text)?;
                let again = fmt_stdin(&out)?;
                if again != out {
                    return Err(format!("a second run changed\n{out}into\n{again}"));
                }
                if would_change(&out)? {
                    return Err(format!("`fmt --check` would change its own output:\n{out}"));
                }
                if would_change(&case.text)? != (case.text != out) {
                    return Err("`fmt --check` disagrees with `fmt`".to_owned());
                }
                Ok(())
            },
        );
        let case = input.clone();
        h.case(
            format!("formatting/{name}/every comment keeps its text and order"),
            move || -> Result<(), String> {
                let out = fmt_stdin(&case.text)?;
                let (before, after) = (comments(&case.text), comments(&out));
                if before != after {
                    return Err(format!("comments {before:?} became {after:?}"));
                }
                Ok(())
            },
        );
        let case = input;
        h.case(
            format!("formatting/{name}/fmt gives the text TESTING 17 fixes"),
            move || -> Result<(), String> {
                let out = fmt_stdin(&case.text)?;
                match &case.canonical {
                    Some(canonical) if *canonical != out => Err(format!(
                        "fmt printed\n{out}where TESTING 17 says\n{canonical}"
                    )),
                    Some(_) => Ok(()),
                    // No text is fixed, so this is the comment test's own input: it
                    // must hold more comments than the case without them.
                    None if comments(&case.text).len() >= 2 => Ok(()),
                    None => Err("the input has no comments to keep".to_owned()),
                }
            },
        );
    }
    h.case(
        "formatting/fmt --check finds every SPEC block but G01-G04 formatted",
        || {
            let (dir, blocks) = spec_tree();
            assert!(blocks.len() > 55, "{} blocks", blocks.len());
            let ran = enrang_in(dir.path(), &strings(&["fmt", "--check", "spec"]));
            let total = blocks.len() + 1;
            assert_eq!(
                (ran.code, ran.stdout.as_str(), ran.stderr.as_str()),
                (
                    1,
                    format!(
                        "spec/zz-canary.en would be reformatted\n1 of {total} files would change\n"
                    )
                    .as_str(),
                    ""
                ),
                "only the canary may change"
            );
        },
    );
    h.case(
        "formatting/fmt leaves every SPEC block but G01-G04 as it is",
        || {
            let (dir, blocks) = spec_tree();
            let ran = enrang_in(dir.path(), &strings(&["fmt", "spec"]));
            assert_eq!(
                (ran.code, ran.stdout.as_str(), ran.stderr.as_str()),
                (0, "", "")
            );
            for (path, text) in &blocks {
                let after = fs::read_to_string(dir.join(&format!("spec/{path}"))).expect("kept");
                assert_eq!(&after, text, "{path}");
            }
            let canary = fs::read_to_string(dir.join("spec/zz-canary.en")).expect("kept");
            assert_eq!(canary, "const canary = 1;\n");
        },
    );
    h.case("formatting/the four tests see what they must", || {
        // A changed tree, a dropped comment and an unstable text are each caught.
        assert_ne!(
            imports_sorted(tree("const a = 1;\n").expect("parses")),
            tree("const a = 2;\n").expect("parses")
        );
        assert_eq!(
            comments("a(); /* x  \n     y\n   * z */ // w  \n"),
            ["/* x\n     y\n* z */", "// w"]
        );
        assert_ne!(comments("// a\n// b\n"), comments("// b\n// a\n"));
        assert!(would_change("const   x=1;\n").expect("it runs"));
        assert!(!would_change("const x = 1;\n").expect("it runs"));
        assert!(tree("const x = 1\n").is_err());
    });
}
