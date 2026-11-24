//! Compile-test anchors (TESTING 7).
//!
//! A fixture marks each line that must report a code with `//~ EN0201`, and may also
//! name a piece of the message, `//~ EN0201 "does not exist"`. A line that reports
//! two codes carries two anchors, `//~ EN0004 //~ EN0101`. The anchors are written
//! by hand, so blessing a golden never changes which error is expected (TESTING 17).
//!
//! A run passes when the set of (line, code) pairs it reports is exactly the set the
//! anchors name, so a fixture cannot pass because of an unrelated mistake, and when
//! each anchored substring is in the message of a diagnostic with that code on that
//! line. What a run reports is read from its rendered diagnostics (SPEC 13.1): each
//! `error[CODE]: message` or `warning[CODE]: message` line, and the `--> path:line:col`
//! line under it when the diagnostic has a place.

use std::collections::BTreeSet;
use std::fmt;

/// One `//~` anchor.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Anchor {
    /// The line it is on, from 1.
    pub line: usize,
    pub code: String,
    /// A piece of the message, when the anchor names one.
    pub substring: Option<String>,
}

/// A malformed anchor, at its 1-based line.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct AnchorError {
    pub line: usize,
    pub message: String,
}

impl fmt::Display for AnchorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}: {}", self.line, self.message)
    }
}

impl std::error::Error for AnchorError {}

/// Whether `word` is spelt as a code: capitals, then digits (`EN0601`, `T0001`).
fn is_code(word: &str) -> bool {
    let digits = word.trim_start_matches(|c: char| c.is_ascii_uppercase());
    digits.len() < word.len() && !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit())
}

/// One anchor's text after its `//~`.
fn parse_anchor(line: usize, text: &str) -> Result<Anchor, AnchorError> {
    let error = |message: String| AnchorError { line, message };
    let text = text.trim();
    let (code, rest) = text.split_once(char::is_whitespace).unwrap_or((text, ""));
    if !is_code(code) {
        return Err(error(format!("`//~` must name a code, not {code:?}")));
    }
    let rest = rest.trim();
    if rest.is_empty() {
        return Ok(Anchor {
            line,
            code: code.to_owned(),
            substring: None,
        });
    }
    let quoted = rest
        .strip_prefix('"')
        .and_then(|inner| inner.strip_suffix('"'))
        .filter(|inner| !inner.contains('"') && !inner.is_empty());
    match quoted {
        Some(substring) => Ok(Anchor {
            line,
            code: code.to_owned(),
            substring: Some(substring.to_owned()),
        }),
        None => Err(error(format!(
            "after {code}, an anchor holds only a quoted piece of the message, not {rest:?}"
        ))),
    }
}

/// The anchors of a fixture, in line order. Text that is not UTF-8 is read lossily
/// by the caller, since a fixture of EN0001 holds bytes that are not.
pub fn anchors(text: &str) -> Result<Vec<Anchor>, AnchorError> {
    let mut found = Vec::new();
    for (index, line) in text.lines().enumerate() {
        let Some((_, after)) = line.split_once("//~") else {
            continue;
        };
        for piece in after.split("//~") {
            found.push(parse_anchor(index + 1, piece)?);
        }
    }
    Ok(found)
}

/// The target a compile fixture's header names, `//! target: <name>`, for a rule
/// only that target has (M2 plan g.4), which the fixture is checked with
/// `--target=<name>`; `None` for a fixture checked for the host's target. A header
/// naming nothing, or one after the header lines, is a broken fixture: the error
/// says why ([`fixture_header`]).
pub fn fixture_target(text: &str) -> Result<Option<String>, String> {
    fixture_header(text).map(|header| header.target)
}

/// What a compile fixture's header asks of the run that checks it.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FixtureHeader {
    /// `//! target: <name>`: checked with `--target=<name>`.
    pub target: Option<String>,
    /// `//! library`: loaded as a library module, through `check`'s internal
    /// `--library` flag, for a rule only library code can meet (G50: `extend` on an
    /// object type or a tuple, EN0439).
    pub library: bool,
}

impl FixtureHeader {
    /// The arguments of `enrang check` before the file: the internal `--library`
    /// first, then `--target=`.
    pub fn check_flags(&self) -> Vec<String> {
        let mut flags = Vec::new();
        if self.library {
            flags.push("--library".to_owned());
        }
        if let Some(target) = &self.target {
            flags.push(format!("--target={target}"));
        }
        flags
    }
}

/// A fixture's header: its leading lines that are `//! target: <name>` or
/// `//! library`, in either order, each at most once (`//! covers:` lines may stand
/// anywhere and are read elsewhere). Either header on a line after a line that is
/// neither is a broken fixture, and so is a target that names nothing: the error
/// says why. The CLI fixture runner, the meta gate and the page runner read it
/// here, so they run a fixture alike.
pub fn fixture_header(text: &str) -> Result<FixtureHeader, String> {
    fn target(line: &str) -> Option<&str> {
        line.trim_start().strip_prefix("//! target:").map(str::trim)
    }
    fn library(line: &str) -> bool {
        line.trim() == "//! library"
    }
    let mut header = FixtureHeader::default();
    let mut lines = text.lines().peekable();
    while let Some(line) = lines.peek() {
        if let Some(name) = target(line) {
            if header.target.is_some() {
                return Err("names its target on a line after its first; \
                            its header holds one `//! target: <name>`"
                    .to_owned());
            }
            if name.is_empty() {
                return Err("names no target on its `//! target:` line".to_owned());
            }
            header.target = Some(name.to_owned());
        } else if library(line) {
            if header.library {
                return Err("says `//! library` twice".to_owned());
            }
            header.library = true;
        } else {
            break;
        }
        lines.next();
    }
    for line in lines {
        if target(line).is_some() {
            let why = "names its target on a line after its first; \
                       only the header lines that open it may hold `//! target: <name>`";
            return Err(why.to_owned());
        }
        if library(line) {
            let why = "says `//! library` on a line after its first; \
                       only the header lines that open it may";
            return Err(why.to_owned());
        }
    }
    Ok(header)
}

/// One coded diagnostic of a rendered stderr.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Reported {
    pub code: String,
    pub message: String,
    /// Where its first label is, if it has a place: the path as shown, then the line
    /// and the column, both from 1.
    pub at: Option<(String, usize, usize)>,
}

impl Reported {
    pub fn line(&self) -> Option<usize> {
        self.at.as_ref().map(|(_, line, _)| *line)
    }
}

/// `path:line:col` from the text after `--> `.
fn place(text: &str) -> Option<(String, usize, usize)> {
    let mut parts = text.rsplitn(3, ':');
    let column = parts.next()?.parse().ok()?;
    let line = parts.next()?.parse().ok()?;
    let path = parts.next()?;
    Some((path.to_owned(), line, column))
}

/// The coded diagnostics of a rendered stderr, in order. Notes, the final
/// `error: aborting ...` line and anything indented are not diagnostics.
pub fn reported(stderr: &str) -> Vec<Reported> {
    let lines: Vec<&str> = stderr.lines().collect();
    let mut found = Vec::new();
    for (index, line) in lines.iter().enumerate() {
        let Some(rest) = ["error[", "warning["]
            .iter()
            .find_map(|head| line.strip_prefix(head))
        else {
            continue;
        };
        let Some((code, tail)) = rest.split_once(']') else {
            continue;
        };
        let Some(message) = tail.strip_prefix(": ") else {
            continue;
        };
        let at = lines
            .get(index + 1)
            .and_then(|next| next.trim_start().strip_prefix("--> "))
            .and_then(place);
        found.push(Reported {
            code: code.to_owned(),
            message: message.to_owned(),
            at,
        });
    }
    found
}

/// How a run differs from its anchors.
#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub struct Mismatch {
    /// Anchored (line, code) pairs that nothing reported.
    pub missing: Vec<(usize, String)>,
    /// Reported (line, code) pairs that no anchor names; a diagnostic with no place
    /// has no line.
    pub unexpected: Vec<(Option<usize>, String)>,
    /// Anchors whose substring is in no message of their line and code, with the
    /// messages that were there.
    pub wrong_message: Vec<(Anchor, Vec<String>)>,
}

impl Mismatch {
    pub fn is_empty(&self) -> bool {
        self.missing.is_empty() && self.unexpected.is_empty() && self.wrong_message.is_empty()
    }
}

impl fmt::Display for Mismatch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (line, code) in &self.missing {
            writeln!(f, "line {line}: {code} is anchored but not reported")?;
        }
        for (line, code) in &self.unexpected {
            match line {
                Some(line) => writeln!(f, "line {line}: {code} is reported but not anchored")?,
                None => writeln!(
                    f,
                    "{code} is reported with no place, so no anchor can name it"
                )?,
            }
        }
        for (anchor, messages) in &self.wrong_message {
            writeln!(
                f,
                "line {}: no {} message holds {:?}; the messages are {messages:?}",
                anchor.line,
                anchor.code,
                anchor.substring.as_deref().unwrap_or("")
            )?;
        }
        Ok(())
    }
}

/// Compares what a run reported with its fixture's anchors.
pub fn compare(anchors: &[Anchor], reported: &[Reported]) -> Result<(), Mismatch> {
    let expected: BTreeSet<(Option<usize>, &str)> = anchors
        .iter()
        .map(|anchor| (Some(anchor.line), anchor.code.as_str()))
        .collect();
    let actual: BTreeSet<(Option<usize>, &str)> = reported
        .iter()
        .map(|diag| (diag.line(), diag.code.as_str()))
        .collect();
    let mut mismatch = Mismatch {
        missing: expected
            .difference(&actual)
            .map(|(line, code)| (line.unwrap_or(0), (*code).to_owned()))
            .collect(),
        unexpected: actual
            .difference(&expected)
            .map(|(line, code)| (*line, (*code).to_owned()))
            .collect(),
        wrong_message: Vec::new(),
    };
    for anchor in anchors {
        let Some(substring) = &anchor.substring else {
            continue;
        };
        let messages: Vec<String> = reported
            .iter()
            .filter(|diag| diag.line() == Some(anchor.line) && diag.code == anchor.code)
            .map(|diag| diag.message.clone())
            .collect();
        if !messages.is_empty() && !messages.iter().any(|message| message.contains(substring)) {
            mismatch.wrong_message.push((anchor.clone(), messages));
        }
    }
    if mismatch.is_empty() {
        Ok(())
    } else {
        Err(mismatch)
    }
}
