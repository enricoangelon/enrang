//! Helpers shared by the suite: sources with spans found by content, multi-line
//! expectations written line by line, and the documents the suite reads.

use std::collections::BTreeMap;
use std::fs;
use std::ops::Deref;
use std::path::PathBuf;
use std::sync::{Arc, OnceLock};

use enrang_base::{BytePos, FileId, FileOrigin, SourceMap, Span};
use enrang_diag::{Diagnostic, RenderOpts, render_json, render_text};
use enrang_testkit::{line_diff, workspace_root};

/// One file's text and where the map placed it. Line arithmetic here is written
/// independently of the source map, so that a test cannot inherit its bugs.
#[derive(Clone)]
pub struct FileSpans {
    pub id: FileId,
    pub start: u32,
    pub text: Arc<str>,
}

impl FileSpans {
    pub fn base(&self) -> BytePos {
        BytePos(self.start)
    }

    pub fn at(&self, offset: usize) -> BytePos {
        BytePos(self.start + offset as u32)
    }

    pub fn span(&self, lo: usize, hi: usize) -> Span {
        Span {
            lo: self.at(lo),
            hi: self.at(hi),
        }
    }

    pub fn point_at(&self, offset: usize) -> Span {
        self.span(offset, offset)
    }

    /// The only occurrence of `needle` in the file.
    pub fn find(&self, needle: &str) -> Span {
        let mut found = self.text.match_indices(needle);
        let (lo, _) = found
            .next()
            .unwrap_or_else(|| panic!("`{needle}` is not in the source"));
        assert!(found.next().is_none(), "`{needle}` occurs more than once");
        self.span(lo, lo + needle.len())
    }

    /// The offset where the 1-based `line` begins. Line 1 starts after a BOM.
    pub fn line_offset(&self, line: u32) -> usize {
        let bom = if self.text.starts_with('\u{FEFF}') {
            3
        } else {
            0
        };
        let mut offset = bom;
        for _ in 1..line {
            let next = self.text[offset..]
                .find('\n')
                .unwrap_or_else(|| panic!("the source has no line {line}"));
            offset += next + 1;
        }
        offset
    }

    /// The text of `line`, without its terminator.
    pub fn line(&self, line: u32) -> &str {
        let start = self.line_offset(line);
        let rest = &self.text[start..];
        let end = rest.find('\n').unwrap_or(rest.len());
        rest[..end].strip_suffix('\r').unwrap_or(&rest[..end])
    }

    /// The first occurrence of `needle` on `line`.
    pub fn on_line(&self, line: u32, needle: &str) -> Span {
        self.nth_on_line(line, needle, 0)
    }

    /// The occurrence of `needle` on `line` that `n` others precede.
    pub fn nth_on_line(&self, line: u32, needle: &str, n: usize) -> Span {
        let start = self.line_offset(line);
        let text = self.line(line);
        let (at, _) = text
            .match_indices(needle)
            .nth(n)
            .unwrap_or_else(|| panic!("no occurrence {n} of `{needle}` on line {line}"));
        self.span(start + at, start + at + needle.len())
    }

    /// The zero-width span at the start of `line`.
    pub fn line_start(&self, line: u32) -> BytePos {
        self.at(self.line_offset(line))
    }

    /// The zero-width position just after the text of `line`.
    pub fn line_end(&self, line: u32) -> BytePos {
        self.at(self.line_offset(line) + self.line(line).len())
    }

    /// The span of all the text of `line`, without its terminator.
    pub fn whole_line(&self, line: u32) -> Span {
        Span {
            lo: self.line_start(line),
            hi: self.line_end(line),
        }
    }

    /// The zero-width span at 1-based scalar column `col` of `line`.
    pub fn point(&self, line: u32, col: usize) -> Span {
        let start = self.line_offset(line);
        let text = self.line(line);
        let bytes = text
            .char_indices()
            .nth(col - 1)
            .map_or(text.len(), |(at, _)| at);
        self.point_at(start + bytes)
    }

    /// The zero-width span at the end of `line`.
    pub fn eol(&self, line: u32) -> Span {
        let at = self.line_end(line);
        Span { lo: at, hi: at }
    }

    /// The zero-width span at the very end of the file.
    pub fn eof(&self) -> Span {
        self.point_at(self.text.len())
    }
}

/// A source map and its files. It derefs to the first file, which is the only one
/// most tests have.
pub struct Src {
    pub map: SourceMap,
    pub files: Vec<FileSpans>,
}

impl Src {
    pub fn new(name: &str, text: &str) -> Src {
        Src::files(&[(name, text)])
    }

    pub fn files(files: &[(&str, &str)]) -> Src {
        let mut map = SourceMap::new();
        let spans = files
            .iter()
            .map(|&(name, text)| {
                let text: Arc<str> = Arc::from(text);
                let id = map.add(PathBuf::from(name), text.clone(), FileOrigin::User);
                FileSpans {
                    id,
                    start: map.file(id).start.0,
                    text,
                }
            })
            .collect();
        Src { map, files: spans }
    }

    /// The `index`th file.
    pub fn f(&self, index: usize) -> &FileSpans {
        &self.files[index]
    }

    pub fn render(&self, diags: &[Diagnostic]) -> String {
        render_text(diags, &self.map, &RenderOpts::default())
    }

    pub fn render_colored(&self, diags: &[Diagnostic]) -> String {
        render_text(diags, &self.map, &RenderOpts { color: true })
    }

    pub fn json(&self, diags: &[Diagnostic]) -> String {
        render_json(diags, &self.map)
    }

    pub fn one(&self, diag: Diagnostic) -> String {
        self.render(std::slice::from_ref(&diag))
    }
}

impl Deref for Src {
    type Target = FileSpans;

    fn deref(&self) -> &FileSpans {
        &self.files[0]
    }
}

/// Each string as one line, newline included. Expectations are written this way so
/// that leading white space stands out and trailing white space cannot hide.
pub fn lines(parts: &[&str]) -> String {
    let mut text = String::new();
    for part in parts {
        text.push_str(part);
        text.push('\n');
    }
    text
}

/// A source of `count` numbered lines: `l1`, `l2`, and so on.
pub fn numbered_source(count: u32) -> String {
    (1..=count).map(|n| format!("l{n}\n")).collect()
}

/// Fails with a line diff unless the texts are byte-equal.
#[track_caller]
pub fn same(actual: &str, expected: &str) {
    if actual != expected {
        panic!(
            "output differs (- expected, + actual):\n{}\nactual bytes:\n{actual:?}",
            line_diff(expected, actual)
        );
    }
}

/// `text` with ANSI colour sequences removed. Written here rather than shared with
/// the renderer, so a mismatch in either direction shows.
pub fn strip_ansi(text: &str) -> String {
    let mut out = String::new();
    let mut chars = text.chars();
    while let Some(c) = chars.next() {
        if c == '\x1b' {
            assert_eq!(chars.next(), Some('['), "an escape that is not a CSI");
            loop {
                let c = chars.next().expect("an unterminated CSI");
                if c == 'm' {
                    break;
                }
                assert!(c.is_ascii_digit() || c == ';', "not an SGR sequence: {c:?}");
            }
        } else {
            out.push(c);
        }
    }
    out
}

/// A document of `docs/`, read once.
pub fn doc(name: &str) -> &'static str {
    static DOCS: OnceLock<BTreeMap<&'static str, String>> = OnceLock::new();
    let docs = DOCS.get_or_init(|| {
        ["SPEC.md", "TESTING.md", "DEV_RUNTIME.md", "ARCHITECTURE.md"]
            .into_iter()
            .map(|name| {
                let path = workspace_root().join("docs").join(name);
                let text = fs::read_to_string(&path)
                    .unwrap_or_else(|error| panic!("cannot read docs/{name}: {error}"));
                (name, text)
            })
            .collect()
    });
    docs.get(name)
        .unwrap_or_else(|| panic!("docs/{name} is not known to the suite"))
}

/// Builds a test's diagnostics from its source.
pub type Build = fn(&Src) -> Vec<Diagnostic>;

/// One row of a rendering table: a source, the diagnostics, and the exact output.
pub struct Row {
    pub name: &'static str,
    pub src: &'static str,
    pub build: Build,
    pub expected: &'static [&'static str],
}

pub fn row(
    name: &'static str,
    src: &'static str,
    build: Build,
    expected: &'static [&'static str],
) -> Row {
    Row {
        name,
        src,
        build,
        expected,
    }
}

/// Registers each row as a case that renders `src`, named `a.en`, and compares.
pub fn render_table(h: &mut enrang_testkit::Harness, prefix: &str, rows: Vec<Row>) {
    for row in rows {
        h.case(format!("{prefix}/{}", row.name), move || {
            let src = Src::new("a.en", row.src);
            same(&src.render(&(row.build)(&src)), &lines(row.expected));
        });
    }
}

/// A warning: its output has no `= explain` and no final line, which leaves a table
/// row showing only what it is about. Its primary label is `label`.
pub fn warn(span: Span, label: &str) -> Diagnostic {
    Diagnostic::new(enrang_diag::Code::EN0430, "m", span, label)
}

/// An error with the code and message most tests do not care about.
pub fn err(span: Span, label: &str) -> Diagnostic {
    Diagnostic::new(enrang_diag::Code::EN0301, "m", span, label)
}
