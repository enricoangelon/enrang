//! `enrang fmt` through the parser (SPEC 12.5, TESTING 17). The four tests of
//! TESTING 17 run on every `ts` block of SPEC except G01-G04: the tree is the same
//! after printing, apart from the order of imports; a second print changes nothing;
//! every comment keeps its text and order; and the block is already formatted. The
//! fixed cases EF-05 and EF-11 are read from TESTING 17, and every SPEC block is
//! run again with comments added in every place one can go without changing a
//! token. Every input must parse with no diagnostic, under the name SPEC would give
//! it. The rules one by one are in `printer_rules.rs` and `printer_comments.rs`,
//! generated inputs in `printer_props.rs` and `gen.rs`.

use std::collections::BTreeSet;

use enrang_base::{BytePos, SourceFile};
use enrang_diag::DiagCtx;
use enrang_syntax::ast::*;
use enrang_syntax::{TokenKind, erase, lex, print_file};
use enrang_testkit::{Harness, line_diff};

use crate::parser::{Parsed, spec_sources};
use crate::support::{backticked, doc, source};

/// The `ts` blocks of SPEC that are not in the canonical style although SPEC 12.5
/// says every block is, each named by a line it holds, with the reason. For these
/// the fourth test is replaced by its opposite: the printer must still change the
/// block, so an entry that is no longer needed fails. The other three tests still
/// run on them.
const NOT_CANONICAL: &[(&str, &str)] = &[];

/// The name a SPEC-style file holding `text` has: a test file when a line starts a
/// test item, as SPEC 12.1 and 12.3 write test files, so that EN1112 does not fire.
pub fn file_name(text: &str) -> &'static str {
    let tests = text.lines().any(|line| {
        ["describe(", "test(", "test.", "compileFails(", "compileOk("]
            .iter()
            .any(|start| line.starts_with(start))
    });
    if tests { "fmt.test.en" } else { "fmt.en" }
}

/// `text` parsed as file `name`, or the diagnostics it reported.
pub fn try_parse(name: &str, text: &str) -> Result<(SourceFile, File), String> {
    let parsed = Parsed::new(name, text);
    if parsed.diags.is_empty() {
        Ok((parsed.file, parsed.tree))
    } else {
        Err(parsed.listing())
    }
}

/// `text` parsed under [`file_name`]; it must parse with no diagnostic.
pub fn parse(text: &str) -> (SourceFile, File) {
    parse_as(file_name(text), text)
}

/// `text` parsed as file `name`; it must parse with no diagnostic.
pub fn parse_as(name: &str, text: &str) -> (SourceFile, File) {
    try_parse(name, text)
        .unwrap_or_else(|listing| panic!("the input does not parse:\n{listing}{text}"))
}

/// `text` printed by `fmt`.
pub fn fmt(text: &str) -> String {
    fmt_as(file_name(text), text)
}

/// `text` printed by `fmt` as file `name`.
pub fn fmt_as(name: &str, text: &str) -> String {
    let (file, tree) = parse_as(name, text);
    print_file(&file, &tree)
}

/// `text`'s tree printed with no source, as a generated tree is.
pub fn fmt_bare(text: &str) -> String {
    fmt_bare_as(file_name(text), text)
}

/// [`fmt_bare`] of file `name`.
pub fn fmt_bare_as(name: &str, text: &str) -> String {
    let (_, tree) = parse_as(name, text);
    print_file(&source("bare.en", ""), &erase(&tree))
}

/// The four tests of TESTING 17 on `input`, whose formatted form is `expected`
/// (`None`: not checked). Errors name what broke, with a diff.
pub fn four_tests(input: &str, expected: Option<&str>) -> Result<(), String> {
    four_tests_as(file_name(input), input, expected)
}

/// [`four_tests`] on a file named `name`.
pub fn four_tests_as(name: &str, input: &str, expected: Option<&str>) -> Result<(), String> {
    let (source, before) = try_parse(name, input)
        .map_err(|listing| format!("the input does not parse:\n{listing}"))?;
    let out = print_file(&source, &before);
    if let Some(expected) = expected
        && out != expected
    {
        return Err(format!(
            "formatted text differs (- expected, + printed):\n{}",
            line_diff(expected, &out)
        ));
    }
    let (out_source, after) = try_parse(name, &out)
        .map_err(|listing| format!("the output does not parse:\n{listing}{out}"))?;
    let again = print_file(&out_source, &after);
    if again != out {
        return Err(format!(
            "a second run changes the text:\n{}",
            line_diff(&out, &again)
        ));
    }
    let want = sorted_imports(&source, &before);
    let got = erase(&after);
    if want != got {
        return Err(format!(
            "the tree changed:\n{}\nprinted:\n{out}",
            line_diff(&format!("{want:#?}"), &format!("{got:#?}"))
        ));
    }
    let (want, got) = (comments(input), comments(&out));
    if want != got {
        return Err(format!(
            "comments changed (- input, + printed):\n{}\nprinted:\n{out}",
            line_diff(&want.join("\n"), &got.join("\n"))
        ));
    }
    Ok(())
}

/// The erased tree of `source` with its imports in the order SPEC 12.5's Imports
/// rule gives, worked out here from the source text and not by the printer: a blank
/// line ends a group; a group holding a comment, from its first import to the end
/// of its last import's line, stays as written, and so does a group right after
/// `// enrang-fmt-ignore`, which keeps its first import where it is written and so
/// the whole group (SPEC 12.5 Opting out; the group is the unit that sorting
/// moves); any other group's lines sort, stably, by the value of their path, and the
/// names of each brace list by the imported name, both in byte order.
pub fn sorted_imports(source: &SourceFile, file: &File) -> File {
    let text: &str = &source.text;
    let at = |pos: BytePos| (pos.0 - source.start.0) as usize;
    let spans = comment_spans(text);
    let comment_starts: Vec<usize> = spans.iter().map(|&(lo, _)| lo).collect();
    let ignored = |first: usize| {
        spans
            .iter()
            .rev()
            .find(|&&(_, hi)| hi <= first)
            .is_some_and(|&(lo, hi)| {
                text[lo..hi].trim_end() == "// enrang-fmt-ignore"
                    && text[hi..first].trim().is_empty()
            })
    };
    let mut groups: Vec<Vec<usize>> = Vec::new();
    for (index, import) in file.imports.iter().enumerate() {
        let joins = index > 0 && {
            let gap = &text[at(file.imports[index - 1].span.hi)..at(import.span.lo)];
            let lines: Vec<&str> = gap.split('\n').collect();
            let blank = lines.len() > 2
                && lines[1..lines.len() - 1]
                    .iter()
                    .any(|line| line.trim().is_empty());
            !blank
        };
        match groups.last_mut() {
            Some(group) if joins => group.push(index),
            _ => groups.push(vec![index]),
        }
    }
    let erased = erase(file);
    let mut imports = Vec::with_capacity(erased.imports.len());
    for group in groups {
        let first = at(file.imports[group[0]].span.lo);
        let last_end = at(file.imports[group[group.len() - 1]].span.hi);
        let line_end = text[last_end..]
            .find('\n')
            .map_or(text.len(), |n| last_end + n);
        let commented = ignored(first)
            || comment_starts
                .iter()
                .any(|&start| start >= first && start < line_end);
        let mut lines: Vec<Import> = group.iter().map(|&i| erased.imports[i].clone()).collect();
        if !commented {
            lines.sort_by(|a, b| a.path.value.as_str().cmp(b.path.value.as_str()));
            for line in &mut lines {
                if let ImportKind::Named(names) = &mut line.kind {
                    names.sort_by(|a, b| a.name.name.as_str().cmp(b.name.name.as_str()));
                }
            }
        }
        imports.extend(lines);
    }
    File { imports, ..erased }
}

/// The byte ranges of the comments of `text`, found between its tokens. A gap
/// between tokens holds only white space and comments in a file that lexes clean.
pub fn comment_spans(text: &str) -> Vec<(usize, usize)> {
    let mut spans = Vec::new();
    for (lo, hi) in gaps(text) {
        let gap = &text[lo..hi];
        let mut offset = 0;
        while let Some(found) = gap[offset..].find('/') {
            let start = offset + found;
            let tail = &gap[start..];
            let len = if tail.starts_with("//") {
                tail.find('\n').unwrap_or(tail.len())
            } else if let Some(body) = tail.strip_prefix("/*") {
                body.find("*/").map_or(tail.len(), |len| len + 4)
            } else {
                offset = start + 1;
                continue;
            };
            spans.push((lo + start, lo + start + len));
            offset = start + len;
        }
    }
    spans
}

/// The gaps of `text`: the byte range before each token, the end of file's
/// included, each with the token that ends it.
fn gaps(text: &str) -> Vec<(usize, usize)> {
    gaps_with_tokens(text)
        .into_iter()
        .map(|(lo, hi, _)| (lo, hi))
        .collect()
}

fn gaps_with_tokens(text: &str) -> Vec<(usize, usize, TokenKind)> {
    let file = source("c.en", text);
    let tokens = lex(&file, &mut DiagCtx::new());
    let at = |pos: BytePos| (pos.0 - file.start.0) as usize;
    let mut found = Vec::new();
    let mut lo = 0usize;
    for token in &tokens {
        found.push((lo, at(token.span.lo), token.kind));
        lo = at(token.span.hi);
        if token.kind == TokenKind::Eof {
            break;
        }
    }
    found
}

/// Every comment of `text`, as TESTING 17 compares them: in order, with the
/// leading spaces of the first line and of each `*` line removed, and the trailing
/// spaces of every line. Every other line of a block comment keeps its indentation,
/// since SPEC 12.5 prints such a comment as written.
pub fn comments(text: &str) -> Vec<String> {
    comment_spans(text)
        .into_iter()
        .map(|(lo, hi)| {
            let lines: Vec<&str> = text[lo..hi]
                .lines()
                .enumerate()
                .map(|(index, line)| {
                    let line = line.trim_end();
                    if index == 0 || line.trim_start().starts_with('*') {
                        line.trim_start()
                    } else {
                        line
                    }
                })
                .collect();
            lines.join("\n")
        })
        .collect()
}

/// Where [`with_comments`] adds a comment.
#[derive(Copy, Clone, Debug)]
enum Place {
    /// `/* cN */` at the end of every gap that holds something, right before the
    /// next token.
    BeforeToken,
    /// `/* cN */` at the start of every gap that holds something, right after the
    /// previous token (never after a `/`, which would make it a line comment).
    AfterToken,
    /// ` // cN` at the end of every line that ends in a gap holding only spaces
    /// before its line break.
    LineEnd,
    /// `// cN` on a line of its own before every line that starts in a gap.
    OwnLine,
    /// A `*` block comment over three lines, on lines of its own, before every line
    /// that starts in a gap.
    StarBlock,
}

impl Place {
    const ALL: [Place; 5] = [
        Place::BeforeToken,
        Place::AfterToken,
        Place::LineEnd,
        Place::OwnLine,
        Place::StarBlock,
    ];

    fn describe(self) -> &'static str {
        match self {
            Place::BeforeToken => "a block comment before every token after a space",
            Place::AfterToken => "a block comment after every token before a space",
            Place::LineEnd => "a line comment at the end of every line",
            Place::OwnLine => "a line comment on its own line before every line",
            Place::StarBlock => "a star block comment before every line",
        }
    }
}

/// The places in `gap` (relative to it) where a line break lies outside every
/// comment, with whether only spaces come before it in the gap.
fn line_breaks(gap: &str) -> Vec<(usize, bool)> {
    let mut found = Vec::new();
    let mut rest = 0;
    let mut clean = true;
    while rest < gap.len() {
        let tail = &gap[rest..];
        if tail.starts_with("//") {
            rest += tail.find('\n').unwrap_or(tail.len());
            clean = false;
        } else if let Some(body) = tail.strip_prefix("/*") {
            rest += body.find("*/").map_or(tail.len(), |len| len + 4);
            clean = false;
        } else {
            let c = tail.chars().next().unwrap_or(' ');
            if c == '\n' {
                found.push((rest, clean));
            }
            rest += c.len_utf8();
        }
    }
    found
}

/// `text` with a comment added at every `place`, each with its own text, so that
/// the comment test sees any loss or reordering. No token changes, and none gains
/// or loses the space before it, so the tree is the same.
fn with_comments(text: &str, place: Place) -> String {
    let mut out = String::with_capacity(text.len() * 3);
    let mut count = 0;
    let mut next = || {
        count += 1;
        count
    };
    let mut prev_hi = 0;
    for (lo, hi, _) in gaps_with_tokens(text) {
        out.push_str(&text[prev_hi..lo]);
        let gap = &text[lo..hi];
        prev_hi = hi;
        if gap.is_empty() {
            continue;
        }
        match place {
            Place::BeforeToken => {
                out.push_str(gap);
                out.push_str(&format!("/* c{} */", next()));
            }
            Place::AfterToken => {
                if !out.ends_with('/') {
                    out.push_str(&format!("/* c{} */", next()));
                }
                out.push_str(gap);
            }
            Place::LineEnd => match line_breaks(gap).first() {
                Some(&(at, true)) if lo > 0 => {
                    out.push_str(&gap[..at]);
                    out.push_str(&format!(" // c{}", next()));
                    out.push_str(&gap[at..]);
                }
                _ => out.push_str(gap),
            },
            Place::OwnLine | Place::StarBlock => match line_breaks(gap).last() {
                Some(&(at, _)) => {
                    out.push_str(&gap[..=at]);
                    let n = next();
                    if let Place::OwnLine = place {
                        out.push_str(&format!("// c{n}\n"));
                    } else {
                        out.push_str(&format!("/*\n * c{n}\n   * more {n}\n */\n"));
                    }
                    out.push_str(&gap[at + 1..]);
                }
                None => out.push_str(gap),
            },
        }
    }
    out.push_str(&text[prev_hi..]);
    out
}

pub fn register(h: &mut Harness) {
    register_spec(h);
    register_fixed(h);
    register_bare(h);
}

/// The SPEC blocks, as they are and with comments everywhere.
fn register_spec(h: &mut Harness) {
    for (index, spec) in spec_sources().iter().enumerate() {
        let not_canonical = NOT_CANONICAL
            .iter()
            .find(|(line, _)| spec.text.lines().any(|l| l == *line));
        h.case(
            format!("fmt/SPEC is formatted/{index:02} {}", spec.label),
            move || match not_canonical {
                None => four_tests_as(&spec.name, &spec.text, Some(&spec.text)),
                Some((_, reason)) => {
                    four_tests_as(&spec.name, &spec.text, None)?;
                    let (file, tree) = try_parse(&spec.name, &spec.text)?;
                    if print_file(&file, &tree) == spec.text {
                        return Err(format!(
                            "listed in NOT_CANONICAL ({reason}), but already formatted"
                        ));
                    }
                    Ok(())
                }
            },
        );
        for place in Place::ALL {
            h.case(
                format!(
                    "fmt/SPEC with comments everywhere/{index:02} {}: {}",
                    spec.label,
                    place.describe()
                ),
                move || {
                    let input = with_comments(&spec.text, place);
                    if comments(&input).len() <= comments(&spec.text).len() {
                        return Err("no comment was added".to_owned());
                    }
                    four_tests_as(&spec.name, &input, None)
                        .map_err(|why| format!("{why}\ninput:\n{input}"))
                },
            );
        }
    }
    h.case("fmt/NOT_CANONICAL names one block each", || {
        for (line, reason) in NOT_CANONICAL {
            let found = spec_sources()
                .iter()
                .filter(|spec| spec.text.lines().any(|l| l == *line))
                .count();
            assert_eq!(found, 1, "{line:?} ({reason}) names {found} blocks");
        }
    });
    h.case("fmt/comments everywhere adds comments where it says", || {
        let text = "const a = f(x, y);\nif (a) {\n  b();\n}\n";
        let rows = [
            (
                Place::BeforeToken,
                "const /* c1 */a /* c2 */= /* c3 */f(x, /* c4 */y);\n/* c5 */if /* c6 */(a) /* c7 */{\n  /* c8 */b();\n/* c9 */}\n/* c10 */",
            ),
            (
                Place::AfterToken,
                "const/* c1 */ a/* c2 */ =/* c3 */ f(x,/* c4 */ y);/* c5 */\nif/* c6 */ (a)/* c7 */ {/* c8 */\n  b();/* c9 */\n}/* c10 */\n",
            ),
            (
                Place::LineEnd,
                "const a = f(x, y); // c1\nif (a) { // c2\n  b(); // c3\n} // c4\n",
            ),
            (
                Place::OwnLine,
                "const a = f(x, y);\n// c1\nif (a) {\n// c2\n  b();\n// c3\n}\n// c4\n",
            ),
        ];
        for (place, want) in rows {
            assert_eq!(with_comments(text, place), want, "{place:?}");
        }
        let star = with_comments("a();\nb();\n", Place::StarBlock);
        assert_eq!(
            star,
            "a();\n/*\n * c1\n   * more 1\n */\nb();\n/*\n * c2\n   * more 2\n */\n"
        );
    });
    h.case("fmt/the comment test sees what TESTING 17 forbids", || {
        // The first line and `*` lines may lose their indentation, every line its
        // trailing spaces; other lines of a block comment keep theirs.
        assert_eq!(
            comments("a(); /* x  \n     y\n   * z */ // w  \n"),
            ["/* x\n     y\n* z */", "// w"]
        );
        assert_ne!(comments("/* x\n  y */\n"), comments("/* x\n y */\n"));
    });
}

/// TESTING 17's fixed cases: EF-05 for the Quotes rule and EF-11 for the Imports
/// rule, read from the document.
fn register_fixed(h: &mut Harness) {
    for (index, (input, output)) in ef05().into_iter().enumerate() {
        h.case(format!("fmt/EF-05 #{}: {input}", index + 1), move || {
            let input = format!("const s = {input};\n");
            let output = format!("const s = {output};\n");
            four_tests(&input, Some(&output))
        });
    }
    h.case("fmt/EF-05 has its three cases", || {
        assert_eq!(ef05().len(), 3, "{:?}", ef05());
    });
    h.case("fmt/EF-11: imports sort by path value", || {
        let (input, output) = ef11();
        assert_eq!(
            output,
            "public import { Z } from \"./z\";\n\
             import { b } from \"a\";\n\
             import { a } from \"b\";\n\
             import * as core from \"core\";\n"
        );
        four_tests(&input, Some(&output))
    });
    h.case(
        "fmt/EF-11: a key from the spelling would fail the second run",
        || {
            let input = "import { a } from \"b\";\nimport { b } from 'a';\n";
            let once = fmt(input);
            assert_eq!(once, "import { b } from \"a\";\nimport { a } from \"b\";\n");
            assert_eq!(fmt(&once), once);
        },
    );
    h.case(
        "fmt/EF-11: lines with one path keep their order, names sort by imported name",
        || {
            let input = "import { z as a, b } from \"p\";\nimport { y } from 'p';\n\
                         public import { C } from \"./c\";\n";
            let output = "public import { C } from \"./c\";\n\
                          import { b, z as a } from \"p\";\nimport { y } from \"p\";\n";
            four_tests(input, Some(output))
        },
    );
}

/// A tree with no source, as `GenSyntax` makes: strings escaped from their value,
/// templates rebuilt from their parts, `raw` literals from their text.
fn register_bare(h: &mut Harness) {
    let bare: &[(&str, &str, &str)] = &[
        (
            "quotes by the same count",
            "const a = 'it\\'s';\nconst b = 'say \"hi\"';\nconst c = \"tie '\\\"\";\n",
            "const a = \"it's\";\nconst b = 'say \"hi\"';\nconst c = \"tie '\\\"\";\n",
        ),
        (
            "escapes for backslash and control characters",
            "const a = \"a\\tb\\\\c\\nd\\re\\0f\\x01\";\n",
            "const a = \"a\\tb\\\\c\\nd\\re\\0f\\u{1}\";\n",
        ),
        (
            "templates rebuilt from their parts",
            "const t = `a\\`b\\${c}${d + 1}\\\\e\nf`;\n",
            "const t = `a\\`b\\${c}${d + 1}\\\\e\\nf`;\n",
        ),
        (
            "raw literals from their text",
            "const r = raw`\\d+`;\ncompileFails(\"bad\", raw`const x = ;\n`);\n",
            "const r = raw`\\d+`;\ncompileFails(\n  \"bad\",\n  raw`const x = ;\n`,\n);\n",
        ),
        (
            "no comments and no blank lines",
            "// gone\nconst a = 1;\n\n\nconst b = 2;  // gone too\n",
            "const a = 1;\nconst b = 2;\n",
        ),
    ];
    for &(name, input, output) in bare {
        h.case(format!("fmt/a tree with no source: {name}"), move || {
            let printed = fmt_bare(input);
            if printed != output {
                return Err(line_diff(output, &printed));
            }
            let (_, want) = parse(input);
            let (_, got) = parse(&printed);
            if erase(&want) != erase(&got) {
                return Err("the tree changed".to_string());
            }
            Ok(())
        });
    }
    h.case("fmt/every SPEC block is checked", || {
        let names: BTreeSet<&str> = spec_sources().iter().map(|s| s.name.as_str()).collect();
        assert!(spec_sources().len() > 55, "{} blocks", spec_sources().len());
        assert!(names.contains("tour.en") && names.contains("spec.test.en"));
    });
}

/// The line of TESTING 17 that fixes EF-05 and EF-11.
fn ef_line() -> &'static str {
    doc("TESTING.md")
        .lines()
        .find(|line| line.contains("(`EF-05`)") && line.contains("(`EF-11`)"))
        .expect("TESTING 17 states EF-05 and EF-11")
}

/// EF-05's pairs: each backticked literal between `EF-05` and `EF-11`, and the one
/// it becomes.
fn ef05() -> Vec<(String, String)> {
    let spans = backticked(ef_line());
    let from = spans.iter().position(|span| span == "EF-05").unwrap_or(0) + 1;
    let to = spans
        .iter()
        .position(|span| span == "EF-11")
        .unwrap_or(spans.len());
    spans[from..to]
        .chunks(2)
        .filter(|pair| pair.len() == 2)
        .map(|pair| (pair[0].clone(), pair[1].clone()))
        .collect()
}

/// EF-11's group as TESTING 17 writes it, and the group in the order it states: the
/// line it names first, then the lines whose paths it names, in its order, each path
/// in the double quotes of the Quotes rule.
fn ef11() -> (String, String) {
    let spans = backticked(ef_line());
    let from = spans
        .iter()
        .position(|span| span == "EF-11")
        .expect("EF-11")
        + 1;
    let rest = &spans[from..];
    let mut lines: Vec<&String> = Vec::new();
    for span in rest {
        if !span.contains("import ") || lines.contains(&span) {
            break;
        }
        lines.push(span);
    }
    let count = lines.len();
    let mut output = format!("{}\n", rest[count]);
    for path in &rest[count + 1..count + 4] {
        let value = path.trim_matches(['"', '\'']);
        let line = lines
            .iter()
            .find(|line| {
                line.ends_with(&format!("\"{value}\";")) || line.ends_with(&format!("'{value}';"))
            })
            .expect("a line of the group has the path");
        let head = &line[..line.len() - value.len() - 3];
        output.push_str(&format!("{head}\"{value}\";\n"));
    }
    let input: String = lines.iter().map(|line| format!("{line}\n")).collect();
    (input, output)
}
