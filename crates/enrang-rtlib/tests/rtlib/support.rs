//! Reading the documents and the library's text. This crate depends on nothing
//! that parses (ARCHITECTURE 1), so these cases read `lib/` as lines: the printer
//! puts one declaration on each line, which `stub.rs` checks through the sema
//! suite's round trip, and a canonical file is all `lib/` holds.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use enrang_rtlib::lookup;
use enrang_testkit::workspace_root;

/// A file of the workspace, by its path from the root.
pub fn read(path: &str) -> String {
    let full = workspace_root().join(Path::new(path));
    fs::read_to_string(&full).unwrap_or_else(|e| panic!("{}: {e}", full.display()))
}

/// The source of library module `key`.
pub fn module(key: &str) -> &'static str {
    lookup(key).unwrap_or_else(|| panic!("no library module `{key}`"))
}

/// The text under the heading that starts with `heading` (`"### 8.1 "`), up to
/// the next heading of the same or a higher level.
pub fn section<'a>(doc: &'a str, heading: &str) -> &'a str {
    let level = heading.chars().take_while(|c| *c == '#').count();
    let start = doc
        .lines()
        .scan(0, |at, line| {
            let here = *at;
            *at += line.len() + 1;
            Some((here, line))
        })
        .find(|(_, line)| line.starts_with(heading))
        .map(|(at, line)| at + line.len() + 1)
        .unwrap_or_else(|| panic!("no heading `{heading}`"));
    let rest = &doc[start.min(doc.len())..];
    let mut end = rest.len();
    let mut at = 0;
    for line in rest.lines() {
        let hashes = line.chars().take_while(|c| *c == '#').count();
        if hashes > 0 && hashes <= level && line[hashes..].starts_with(' ') {
            end = at;
            break;
        }
        at += line.len() + 1;
    }
    &rest[..end]
}

/// The first line of `text` that contains `marker`.
pub fn line_with<'a>(text: &'a str, marker: &str) -> &'a str {
    text.lines()
        .find(|line| line.contains(marker))
        .unwrap_or_else(|| panic!("no line with `{marker}`"))
}

/// A backticked span: its text, and the prose just before and after it.
#[derive(Clone, Debug)]
pub struct Span {
    pub text: String,
    pub before: String,
    pub after: String,
    /// Where the span's text starts in the text it was read from.
    pub at: usize,
}

/// The backticked spans of `text`, fenced code blocks left out. A double-backtick
/// quote, which the docs use for a message that holds code, reads as prose with
/// single-backtick spans inside.
pub fn spans(text: &str) -> Vec<Span> {
    let mut prose = String::with_capacity(text.len());
    let mut fenced = false;
    for line in text.split_inclusive('\n') {
        let fence = line.trim_start().starts_with("```");
        if fence {
            fenced = !fenced;
        }
        if fence || fenced {
            prose.extend(line.bytes().map(|b| if b == b'\n' { '\n' } else { ' ' }));
        } else {
            prose.push_str(line);
        }
    }
    let mut out = Vec::new();
    let mut open: Option<usize> = None;
    for (i, c) in prose.char_indices() {
        if c != '`' {
            continue;
        }
        match open {
            None => open = Some(i + 1),
            Some(start) => {
                let before_from = floor_char(&prose, start.saturating_sub(8));
                let after_to = ceil_char(&prose, (i + 9).min(prose.len()));
                out.push(Span {
                    text: prose[start..i].to_owned(),
                    before: prose[before_from..start - 1].to_owned(),
                    after: prose[i + 1..after_to].to_owned(),
                    at: start,
                });
                open = None;
            }
        }
    }
    out
}

fn floor_char(s: &str, mut i: usize) -> usize {
    while !s.is_char_boundary(i) {
        i -= 1;
    }
    i
}

fn ceil_char(s: &str, mut i: usize) -> usize {
    while !s.is_char_boundary(i) {
        i += 1;
    }
    i
}

pub fn is_ident(s: &str) -> bool {
    let mut chars = s.chars();
    chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// A name that a call in a span makes: `copy` in `unsafe copy<T>(d: *T)`, with
/// its receiver, `mem` in `mem.copy(dst, src, n)`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Called {
    pub receiver: Option<String>,
    pub name: String,
}

/// Every name called in `span`: an identifier followed by `(`, or by type
/// arguments and then `(`. A decorator (`@requires(`) is no call.
pub fn calls(span: &str) -> Vec<Called> {
    let bytes = span.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i];
        if !(c.is_ascii_alphabetic() || c == b'_') || (i > 0 && is_word(bytes[i - 1])) {
            i += 1;
            continue;
        }
        let start = i;
        while i < bytes.len() && is_word(bytes[i]) {
            i += 1;
        }
        let name = &span[start..i];
        let mut j = i;
        if j < bytes.len() && bytes[j] == b'<' {
            let mut depth = 0;
            while j < bytes.len() {
                match bytes[j] {
                    b'<' => depth += 1,
                    b'>' => {
                        depth -= 1;
                        if depth == 0 {
                            j += 1;
                            break;
                        }
                    }
                    _ => {}
                }
                j += 1;
            }
        }
        let decorator = start > 0 && bytes[start - 1] == b'@';
        if j < bytes.len() && bytes[j] == b'(' && !decorator {
            let receiver = (start > 1 && bytes[start - 1] == b'.')
                .then(|| {
                    let end = start - 1;
                    let mut k = end;
                    while k > 0 && is_word(bytes[k - 1]) {
                        k -= 1;
                    }
                    span[k..end].to_owned()
                })
                .filter(|r| is_ident(r));
            out.push(Called {
                receiver,
                name: name.to_owned(),
            });
        }
    }
    out
}

fn is_word(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

fn is_word_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// The identifiers of a span made of nothing else, separated by spaces, a
/// leading `.` allowed (`.startsWith`, `sqrt floor ceil`); empty otherwise.
pub fn words(span: &str) -> Vec<String> {
    let span = span.strip_prefix('.').unwrap_or(span);
    let words: Vec<&str> = span.split(' ').collect();
    if words.iter().all(|w| is_ident(w)) {
        words.into_iter().map(str::to_owned).collect()
    } else {
        Vec::new()
    }
}

/// Whether `span` is an item of a list of spans: `` `a`, `b` ``, `` `a` and `b` ``,
/// `` `a` or `b` ``.
pub fn in_list(span: &Span) -> bool {
    const AFTER: [&str; 3] = [", `", " and `", " or `"];
    const BEFORE: [&str; 3] = ["`, ", "` and ", "` or "];
    AFTER.iter().any(|a| span.after.starts_with(a))
        || BEFORE.iter().any(|b| span.before.ends_with(b))
}

/// The names `source` declares, one declaration a line: items, members, fields,
/// enum cases, and what its imports bind. With `public_only`, the names another
/// module may import: `public` items and `public import`s.
pub fn declared(source: &str, public_only: bool) -> BTreeSet<String> {
    const MODIFIERS: [&str; 13] = [
        "public",
        "private",
        "protected",
        "static",
        "abstract",
        "override",
        "readonly",
        "let",
        "const",
        "move",
        "unsafe",
        "declare",
        "final",
    ];
    const ITEMS: [&str; 5] = ["function", "class", "interface", "enum", "type"];
    let mut out = BTreeSet::new();
    for line in source.lines() {
        let top = !line.starts_with(' ');
        let mut rest = line.trim();
        if rest.starts_with("//") {
            continue;
        }
        while let Some(after) = rest.strip_prefix('@') {
            let name_end = after.find(|c| !is_word_char(c)).unwrap_or(after.len());
            let mut tail = &after[name_end..];
            if tail.starts_with('(') {
                let close = tail.find(')').expect("a decorator's `)`");
                tail = &tail[close + 1..];
            }
            rest = tail.trim_start();
        }
        if let Some(import) = rest.strip_prefix("public import ").or_else(|| {
            (!public_only)
                .then(|| rest.strip_prefix("import "))
                .flatten()
        }) {
            if let Some(alias) = import.strip_prefix("* as ") {
                out.insert(alias.split(' ').next().unwrap_or("").to_owned());
            } else if let (Some(open), Some(close)) = (import.find('{'), import.find('}')) {
                for name in import[open + 1..close].split(',') {
                    let bound = name.split(" as ").last().unwrap_or("").trim();
                    out.insert(bound.to_owned());
                }
            }
            continue;
        }
        let is_public = rest.starts_with("public ");
        let mut words = rest.split(' ').peekable();
        while words.peek().is_some_and(|w| MODIFIERS.contains(w)) {
            words.next();
        }
        let Some(word) = words.next() else {
            continue;
        };
        if ITEMS.contains(&word) {
            if let Some(name) = words.next() {
                let end = name.find(|c| !is_word_char(c)).unwrap_or(name.len());
                if !public_only || (top && is_public) {
                    out.insert(name[..end].to_owned());
                }
            }
            continue;
        }
        if public_only || word == "extend" || word == "return" {
            continue;
        }
        let end = word.find(|c| !is_word_char(c)).unwrap_or(word.len());
        let (name, tail) = word.split_at(end);
        let next = tail
            .chars()
            .next()
            .or_else(|| words.peek().and_then(|w| w.chars().next()));
        if is_ident(name) && next.is_none_or(|c| "(<?:,{;".contains(c)) {
            out.insert(name.to_owned());
        }
    }
    out
}

/// Every method `source` declares, by name, and whether it is `@mustUse`.
pub fn methods(source: &str) -> Vec<(String, bool)> {
    let mut out = Vec::new();
    for line in source.lines() {
        if !line.starts_with("  ") || line.starts_with("   ") {
            continue;
        }
        let member = line.trim_start();
        let must_use = member.starts_with("@mustUse ");
        for name in declared(member, false) {
            if member.contains(&format!("{name}(")) || member.contains(&format!("{name}<")) {
                out.push((name, must_use));
            }
        }
    }
    out
}
