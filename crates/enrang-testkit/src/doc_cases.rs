//! The document case extractor (SPEC 14, TESTING 17).
//!
//! A case is a marker line and the blocks after it, up to the next marker or
//! heading:
//!
//! ```text
//! <!-- case: ID files=a.en,b.en cmd="..." exit=N [stdout=block|inline] [stderr=block|inline] [serial=block] -->
//! ```
//!
//! The `ts` blocks are the source files, in `files` order. The `text` blocks after
//! them are the outputs the marker names `block`, in the order stdout, stderr,
//! serial. Prose is not read, with one exception that SPEC 14 itself makes: an
//! `inline` stream is the code spans of the next sentence that names the stream.
//!
//! Everything the marker promises is checked, so a drifted document fails here
//! instead of passing with less being tested. Each code span of an `inline` stream
//! is one whole line of output: SPEC writes the tour's three lines as
//! `` Output: `top = 42`, `[vm] done`, `result 42`. ``

use std::collections::BTreeSet;
use std::fmt;

use crate::markdown::{self, Block, Item, heading_level};

/// One extracted case.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Case {
    pub id: String,
    /// The line of the marker.
    pub line: usize,
    /// The source files, in `files` order.
    pub files: Vec<CaseFile>,
    pub cmd: String,
    pub exit: i32,
    pub stdout: Expected,
    pub stderr: Expected,
    pub serial: Expected,
}

impl Case {
    /// Whether the command may leave an artefact besides its named streams:
    /// SPEC 14 allows that for `dev` and `build` commands only.
    pub fn may_write_artefact(&self) -> bool {
        matches!(self.cmd.split_whitespace().nth(1), Some("dev" | "build"))
    }
}

/// A source file of a case.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CaseFile {
    pub name: String,
    pub contents: String,
}

/// The expected bytes of one output stream.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Expected {
    pub source: StreamSource,
    pub text: String,
}

/// Where a stream's expectation came from.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum StreamSource {
    /// The marker does not name the stream, so it is expected to be empty.
    Unnamed,
    Block,
    Inline,
}

/// A problem in a document, at a 1-based line.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct ExtractError {
    pub line: usize,
    pub message: String,
}

/// Every problem found in a document, in line order.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct ExtractErrors(pub Vec<ExtractError>);

impl fmt::Display for ExtractErrors {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for error in &self.0 {
            writeln!(f, "line {}: {}", error.line, error.message)?;
        }
        Ok(())
    }
}

impl std::error::Error for ExtractErrors {}

/// Extracts every case of a document, or reports every malformed one.
pub fn extract_cases(doc: &str) -> Result<Vec<Case>, ExtractErrors> {
    let items = scan(doc)?;
    let mut errors = Vec::new();
    let mut cases = Vec::new();
    let mut seen = BTreeSet::new();
    let mut index = 0;
    while index < items.len() {
        let Some((line, text)) = marker_like(&items[index]) else {
            index += 1;
            continue;
        };
        let end = scope_end(&items, index + 1);
        match parse_marker(text) {
            Err(message) => errors.push(ExtractError { line, message }),
            Ok(marker) => {
                if !seen.insert(marker.id.clone()) {
                    errors.push(ExtractError {
                        line,
                        message: format!("case {}: the ID is used twice", marker.id),
                    });
                }
                match build_case(marker, line, &items[index + 1..end]) {
                    Ok(case) => cases.push(case),
                    Err(mut problems) => errors.append(&mut problems),
                }
            }
        }
        index = end;
    }
    if errors.is_empty() {
        Ok(cases)
    } else {
        Err(ExtractErrors(errors))
    }
}

/// A fenced code block of a document.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct FencedBlock {
    /// The line of the opening fence.
    pub line: usize,
    /// The first word of the info string, such as `ts`, or empty.
    pub lang: String,
    /// The lines between the fences, each ending in a newline, with the opening
    /// fence's indentation taken off.
    pub contents: String,
}

/// Every fenced code block of a document, in order, read by the same rules as the
/// case extractor: a suite that checks each `ts` block of SPEC sees the blocks the
/// cases are made of.
pub fn fenced_blocks(doc: &str) -> Result<Vec<FencedBlock>, ExtractErrors> {
    let blocks = scan(doc)?
        .into_iter()
        .filter_map(|item| match item {
            Item::Block(block) => Some(FencedBlock {
                line: block.line,
                lang: block.lang.to_owned(),
                contents: block.contents,
            }),
            Item::Line { .. } => None,
        })
        .collect();
    Ok(blocks)
}

/// The `G` and `S` headings with no marker of the same ID under them. SPEC 14
/// requires a meta-test that this is empty.
pub fn headings_without_cases(doc: &str) -> Result<Vec<String>, ExtractErrors> {
    let items = scan(doc)?;
    let mut missing = Vec::new();
    let mut open: Option<&str> = None;
    for item in &items {
        let Item::Line { text, .. } = item else {
            continue;
        };
        if heading_level(text).is_some() {
            missing.extend(open.take().map(str::to_owned));
            open = case_heading_id(text);
        } else if marker_like(item).is_some()
            && let Ok(marker) = parse_marker(text)
            && open == Some(marker.id.as_str())
        {
            open = None;
        }
    }
    missing.extend(open.map(str::to_owned));
    Ok(missing)
}

/// The ID of a heading like `### G01 Missing semicolon` or `### S9 Freestanding`.
fn case_heading_id(heading: &str) -> Option<&str> {
    let word = heading.trim_start_matches([' ', '#']).split(' ').next()?;
    let digits = word.strip_prefix(['G', 'S'])?;
    (!digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit())).then_some(word)
}

fn scan(doc: &str) -> Result<Vec<Item<'_>>, ExtractErrors> {
    let one = |line, message: &str| {
        ExtractErrors(vec![ExtractError {
            line,
            message: message.to_owned(),
        }])
    };
    if let Some(at) = doc.find('\r') {
        // Expectations are compared byte for byte, so a converted checkout would
        // otherwise fail every case with an invisible difference.
        let line = doc[..at].matches('\n').count() + 1;
        return Err(one(line, "the document has a carriage return"));
    }
    markdown::scan(doc).map_err(|fence| one(fence.line, "this code fence is never closed"))
}

/// A line that is, or is trying to be, a marker. A near miss such as
/// `<!--case: X` must be an error: dropped silently, its case would never be
/// tested. A marker quoted in prose does not start the line, so is no marker.
fn marker_like<'a>(item: &Item<'a>) -> Option<(usize, &'a str)> {
    let Item::Line { line, text } = item else {
        return None;
    };
    let comment = text.trim_start().strip_prefix("<!--")?.trim_start();
    let word = comment.get(..4)?;
    let after = comment[4..].trim_start();
    (word.eq_ignore_ascii_case("case") && after.starts_with(':')).then_some((*line, *text))
}

fn scope_end(items: &[Item<'_>], from: usize) -> usize {
    items[from..]
        .iter()
        .position(|item| {
            marker_like(item).is_some()
                || matches!(item, Item::Line { text, .. } if heading_level(text).is_some())
        })
        .map_or(items.len(), |offset| from + offset)
}

struct Marker {
    id: String,
    files: Vec<String>,
    cmd: String,
    exit: i32,
    stdout: StreamSource,
    stderr: StreamSource,
    serial: StreamSource,
}

/// The attributes in the order the marker's form fixes.
const ATTRIBUTES: [&str; 6] = ["files", "cmd", "exit", "stdout", "stderr", "serial"];

fn parse_marker(line: &str) -> Result<Marker, String> {
    let body = line
        .strip_prefix("<!-- case: ")
        .ok_or("a case marker must start the line with `<!-- case: `")?
        .strip_suffix(" -->")
        .ok_or("a case marker must end with ` -->` on the same line")?;
    let mut words = marker_words(body)?.into_iter();
    let id = words.next().ok_or("a case marker needs an ID")?;
    if !is_valid_id(id) {
        return Err(format!("`{id}` is not a case ID"));
    }
    let bad = |message: String| format!("case {id}: {message}");

    let mut marker = Marker {
        id: id.to_owned(),
        files: Vec::new(),
        cmd: String::new(),
        exit: 0,
        stdout: StreamSource::Unnamed,
        stderr: StreamSource::Unnamed,
        serial: StreamSource::Unnamed,
    };
    let mut reached = 0;
    let mut required = BTreeSet::from(["files", "cmd", "exit"]);
    for word in words {
        let (key, value) = word
            .split_once('=')
            .ok_or_else(|| bad(format!("`{word}` is not an attribute")))?;
        let rank = ATTRIBUTES
            .iter()
            .position(|&name| name == key)
            .ok_or_else(|| bad(format!("unknown attribute `{key}`")))?;
        if rank < reached {
            return Err(bad(format!(
                "`{key}` is repeated or out of order; the order is files, cmd, exit, stdout, stderr, serial"
            )));
        }
        reached = rank + 1;
        required.remove(key);
        match key {
            "files" => marker.files = parse_files(value).map_err(&bad)?,
            "cmd" => marker.cmd = parse_cmd(value).map_err(&bad)?,
            "exit" => marker.exit = parse_exit(value).map_err(&bad)?,
            "stdout" => marker.stdout = parse_stream(key, value, true).map_err(&bad)?,
            "stderr" => marker.stderr = parse_stream(key, value, true).map_err(&bad)?,
            _ => marker.serial = parse_stream(key, value, false).map_err(&bad)?,
        }
    }
    if let Some(key) = required.first() {
        return Err(bad(format!("the marker has no `{key}`")));
    }
    Ok(marker)
}

/// Splits on spaces, keeping a quoted value whole. There are no escapes: SPEC 14
/// defines none, and no command in the document needs a quote.
fn marker_words(body: &str) -> Result<Vec<&str>, String> {
    let mut words = Vec::new();
    let mut rest = body.trim_start();
    while !rest.is_empty() {
        let end = match (rest.find(' '), rest.find('"')) {
            (Some(space), Some(quote)) if quote < space => close_quote(rest, quote)?,
            (None, Some(quote)) => close_quote(rest, quote)?,
            (Some(space), _) => space,
            (None, None) => rest.len(),
        };
        words.push(&rest[..end]);
        rest = rest[end..].trim_start();
    }
    Ok(words)
}

fn close_quote(text: &str, open: usize) -> Result<usize, String> {
    let closing = text[open + 1..]
        .find('"')
        .ok_or("a quoted value in the marker is never closed")?;
    Ok(open + 1 + closing + 1)
}

fn is_valid_id(id: &str) -> bool {
    id.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
}

fn parse_files(value: &str) -> Result<Vec<String>, String> {
    let mut seen = BTreeSet::new();
    let mut files = Vec::new();
    for name in value.split(',') {
        if name.is_empty() {
            return Err("`files` has an empty name".to_owned());
        }
        if name.starts_with('/') || name.split('/').any(|part| part == "..") {
            return Err(format!("`{name}` is not a path inside the case"));
        }
        if !seen.insert(name) {
            return Err(format!("`{name}` is listed twice in `files`"));
        }
        files.push(name.to_owned());
    }
    Ok(files)
}

fn parse_cmd(value: &str) -> Result<String, String> {
    let inner = value
        .strip_prefix('"')
        .and_then(|rest| rest.strip_suffix('"'))
        .ok_or("`cmd` must be double-quoted")?;
    if inner.trim().is_empty() {
        return Err("`cmd` is empty".to_owned());
    }
    Ok(inner.to_owned())
}

fn parse_exit(value: &str) -> Result<i32, String> {
    let digits = !value.is_empty() && value.bytes().all(|b| b.is_ascii_digit());
    digits
        .then(|| value.parse().ok())
        .flatten()
        .ok_or_else(|| format!("`exit={value}` is not an exit status"))
}

fn parse_stream(key: &str, value: &str, may_be_inline: bool) -> Result<StreamSource, String> {
    match value {
        "block" => Ok(StreamSource::Block),
        "inline" if may_be_inline => Ok(StreamSource::Inline),
        _ if may_be_inline => Err(format!(
            "`{key}` must be `block` or `inline`, not `{value}`"
        )),
        _ => Err(format!("`{key}` must be `block`, not `{value}`")),
    }
}

fn build_case(marker: Marker, line: usize, scope: &[Item<'_>]) -> Result<Case, Vec<ExtractError>> {
    let id = marker.id.clone();
    let mut errors = Vec::new();
    let mut report = |line: usize, message: String| {
        errors.push(ExtractError {
            line,
            message: format!("case {id}: {message}"),
        });
    };

    let mut sources: Vec<&Block<'_>> = Vec::new();
    let mut outputs: Vec<&Block<'_>> = Vec::new();
    let mut after_sources = 0;
    for (index, item) in scope.iter().enumerate() {
        let Item::Block(block) = item else { continue };
        match block.lang {
            "ts" if outputs.is_empty() => {
                sources.push(block);
                after_sources = index + 1;
            }
            "ts" => report(
                block.line,
                "a `ts` block comes after a `text` block".to_owned(),
            ),
            "text" => outputs.push(block),
            _ => {}
        }
    }

    if sources.len() != marker.files.len() {
        report(
            line,
            format!(
                "`files` lists {} but {} `ts` blocks follow",
                marker.files.len(),
                sources.len()
            ),
        );
    }
    let mut files = Vec::new();
    for (name, block) in marker.files.iter().zip(&sources) {
        if block.contents.is_empty() {
            report(block.line, format!("source file `{name}` is empty"));
        } else if block.contents.ends_with("\n\n") {
            report(
                block.line,
                format!("source file `{name}` must end with one newline"),
            );
        }
        files.push(CaseFile {
            name: name.clone(),
            contents: block.contents.clone(),
        });
    }

    let streams = [
        ("stdout", marker.stdout),
        ("stderr", marker.stderr),
        ("serial", marker.serial),
    ];
    let wanted = streams
        .iter()
        .filter(|(_, source)| *source == StreamSource::Block)
        .count();
    if outputs.len() != wanted {
        report(
            line,
            format!(
                "the marker names {wanted} `block` streams but {} `text` blocks follow",
                outputs.len()
            ),
        );
    }

    let mut unused_outputs = outputs.iter();
    let mut expected = Vec::new();
    for (name, source) in streams {
        let text = match source {
            StreamSource::Unnamed => String::new(),
            StreamSource::Block => match unused_outputs.next() {
                Some(block) if block.contents.is_empty() => {
                    report(
                        block.line,
                        format!("{name} is named `block` but its block is empty"),
                    );
                    String::new()
                }
                Some(block) => block.contents.clone(),
                None => String::new(),
            },
            StreamSource::Inline => match inline_text(name, &scope[after_sources..]) {
                Ok(text) => text,
                Err(message) => {
                    report(line, message);
                    String::new()
                }
            },
        };
        expected.push(Expected { source, text });
    }

    if !errors.is_empty() {
        return Err(errors);
    }
    let serial = expected.pop().expect("three streams");
    let stderr = expected.pop().expect("three streams");
    let stdout = expected.pop().expect("three streams");
    Ok(Case {
        id: marker.id,
        line,
        files,
        cmd: marker.cmd,
        exit: marker.exit,
        stdout,
        stderr,
        serial,
    })
}

/// The expectation of an `inline` stream: each code span of the next sentence
/// that names it is one line of output.
fn inline_text(stream: &str, scope: &[Item<'_>]) -> Result<String, String> {
    let sentence = paragraphs(scope)
        .iter()
        .flat_map(|paragraph| sentences(paragraph))
        .find(|sentence| sentence.names(stream))
        .ok_or_else(|| format!("{stream} is `inline` but no sentence names it"))?;
    if sentence.spans.is_empty() {
        return Err(format!(
            "{stream} is `inline` but the sentence naming it has no code span"
        ));
    }
    let mut text = sentence.spans.join("\n");
    text.push('\n');
    Ok(text)
}

fn paragraphs(scope: &[Item<'_>]) -> Vec<String> {
    let mut paragraphs = Vec::new();
    let mut current = String::new();
    for item in scope {
        match item {
            Item::Line { text, .. } if !text.trim().is_empty() => {
                if !current.is_empty() {
                    current.push('\n');
                }
                current.push_str(text);
            }
            _ => {
                if !current.is_empty() {
                    paragraphs.push(std::mem::take(&mut current));
                }
            }
        }
    }
    if !current.is_empty() {
        paragraphs.push(current);
    }
    paragraphs
}

#[derive(Default)]
struct Sentence {
    prose: String,
    spans: Vec<String>,
}

impl Sentence {
    /// Whether the prose, outside code spans, names a stream. The tour says
    /// `Output:` for its stdout, so that word also names stdout, unless the
    /// sentence is about one of the other streams.
    fn names(&self, stream: &str) -> bool {
        let lowered = self.prose.to_ascii_lowercase();
        let has = |name: &str| {
            lowered
                .split(|c: char| !c.is_ascii_alphanumeric())
                .any(|word| word == name)
        };
        has(stream) || (stream == "stdout" && has("output") && !has("stderr") && !has("serial"))
    }
}

/// Splits a paragraph at `.`, `!` and `?` followed by white space, outside code
/// spans, so that `` `a.b c` `` is one span and not a sentence end.
fn sentences(paragraph: &str) -> Vec<Sentence> {
    let chars: Vec<char> = paragraph.chars().collect();
    let mut done = Vec::new();
    let mut current = Sentence::default();
    let mut at = 0;
    while at < chars.len() {
        let c = chars[at];
        if c == '\\' && chars.get(at + 1) == Some(&'`') {
            current.prose.push('`');
            at += 2;
            continue;
        }
        if c == '`' {
            let run = chars[at..].iter().take_while(|&&c| c == '`').count();
            if let Some(close) = closing_run(&chars, at + run, run) {
                current.spans.push(span_text(&chars[at + run..close]));
                at = close + run;
            } else {
                current.prose.extend(std::iter::repeat_n('`', run));
                at += run;
            }
            continue;
        }
        current.prose.push(c);
        at += 1;
        let at_end = chars.get(at).is_none_or(|next| next.is_whitespace());
        if matches!(c, '.' | '!' | '?') && at_end {
            done.push(std::mem::take(&mut current));
        }
    }
    done.push(current);
    done
}

/// Where the backtick run closing a code span starts: exactly `run` backticks.
fn closing_run(chars: &[char], from: usize, run: usize) -> Option<usize> {
    let mut at = from;
    while at < chars.len() {
        if chars[at] == '`' {
            let length = chars[at..].iter().take_while(|&&c| c == '`').count();
            if length == run {
                return Some(at);
            }
            at += length;
        } else {
            at += 1;
        }
    }
    None
}

/// A code span's text: line breaks are spaces, and one space of padding on both
/// sides goes, so that `` `` `a` `` `` can hold a backtick.
fn span_text(chars: &[char]) -> String {
    let text: String = chars
        .iter()
        .map(|&c| if c == '\n' { ' ' } else { c })
        .collect();
    let padded = text.len() >= 2
        && text.starts_with(' ')
        && text.ends_with(' ')
        && !text.trim_matches(' ').is_empty();
    if padded {
        text[1..text.len() - 1].to_owned()
    } else {
        text
    }
}
