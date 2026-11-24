//! What the suite reads from `docs/` and the sources it builds.

use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;
use std::sync::{Arc, OnceLock};

use enrang_base::{FileOrigin, SourceFile, SourceMap};
use enrang_testkit::workspace_root;

/// A document of `docs/`, read once.
pub fn doc(name: &str) -> &'static str {
    static DOCS: OnceLock<BTreeMap<&'static str, String>> = OnceLock::new();
    let docs = DOCS.get_or_init(|| {
        ["SPEC.md", "ARCHITECTURE.md", "TESTING.md"]
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

/// The text of `doc` from the line starting with `heading` to the next heading of
/// the same or a higher level.
pub fn section(doc: &'static str, heading: &str) -> &'static str {
    let level = heading.chars().take_while(|&c| c == '#').count();
    let start = doc
        .find(&format!("\n{heading}"))
        .unwrap_or_else(|| panic!("no heading {heading:?}"))
        + 1;
    let rest = &doc[start..];
    let end = rest
        .match_indices("\n#")
        .find(|&(at, _)| {
            let hashes = rest[at + 1..].chars().take_while(|&c| c == '#').count();
            hashes <= level
        })
        .map_or(rest.len(), |(at, _)| at + 1);
    &rest[..end]
}

/// The double-quoted terminals of the EBNF production `name` in `text`, in order. The
/// production runs from the line starting with `name` to its first `;` outside quotes.
pub fn terminals(text: &str, name: &str) -> Vec<String> {
    let start = text
        .lines()
        .scan(0, |offset, line| {
            let at = *offset;
            *offset += line.len() + 1;
            Some((at, line))
        })
        .find(|(_, line)| {
            line.strip_prefix(name)
                .is_some_and(|rest| rest.trim_start().starts_with('='))
        })
        .map(|(at, _)| at)
        .unwrap_or_else(|| panic!("no production {name}"));
    let mut found = Vec::new();
    let mut chars = text[start..].chars();
    while let Some(c) = chars.next() {
        match c {
            ';' => return found,
            '"' => {
                let word: String = chars.by_ref().take_while(|&c| c != '"').collect();
                found.push(word);
            }
            _ => {}
        }
    }
    panic!("production {name} does not end");
}

/// The backticked spans of `line`, in order.
pub fn backticked(line: &str) -> Vec<String> {
    line.split('`')
        .skip(1)
        .step_by(2)
        .map(str::to_owned)
        .collect()
}

/// `text` as file `name` of a fresh source map, which the file keeps alive.
pub fn source(name: &str, text: &str) -> SourceFile {
    let mut map = SourceMap::new();
    let id = map.add(PathBuf::from(name), Arc::from(text), FileOrigin::User);
    map.file(id).clone()
}
