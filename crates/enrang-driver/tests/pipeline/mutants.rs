//! TESTING 14's `Mutants` generator (M3 plan f.7, its last paragraph): one
//! violation from a fixed list inserted into an accepted program, which `check`
//! must then reject with the intended code and nothing else.
//!
//! The hosts are every near-miss of a `since(M3)` code,
//! `tests/compile/<CODE>/<name>.pass.en`, checked for the target and with the
//! library flag its header asks for and beside the files its relative imports
//! read, and every program of this suite that phase 3 accepts. Each host is one
//! case. The generator of the case, `rng_for` of its name, draws a violation and
//! orders the places where a statement may begin: just after a `{` that opens a
//! block, just after a `;` that ends a statement in one (but not a `return`,
//! `break`, `continue` or `throw`), and the end of the file, among the top-level
//! statements. At each place in turn the violation's fixed twin goes in first, on
//! a line of its own. The place is taken only when the twin type-checks there,
//! passes `check` whole and is reached: its first local lies in a block reachable
//! from its body's entry, since dead code, which mirbuild leaves out, would hide
//! any violation. A twin that type-checks and is rejected keeps every rule all the
//! same, so its rejection is a failure too, unless an [`Excuse`] covers it: the
//! one rule of a place, before `super(...)`, or a compiler disagreement that a
//! case of [`PINNED`] holds. Then the violation goes in at the same place,
//! anchored as a compile fixture is (`//~ CODE "piece"`, TESTING 7), and `check`
//! must report exactly its anchor; where only the violation fails phases 1 and 2,
//! the place is not taken. `scaled(1)` places are taken in each case.
//!
//! Each violation is one line of fresh `mutant_` locals, with what it needs at the
//! top level, a class, appended to the file (choice: a fresh local type-checks
//! wherever a statement may stand, so the host's own types never decide whether a
//! violation applies; what varies is the place, in a loop, a branch, an arrow, a
//! method, a constructor or among the top-level statements).
//!
//! A failure prints `ENRANG_SEED` and shrinks by whole lines, the violation's line
//! and the header kept, while it still fails; the shrunk program is the regression
//! case to keep, `corpus/regress/mutants/<name>.fail.en` for a violation, anchored,
//! and `<name>-twin.pass.en` for a rejected twin, which `ENRANG_BLESS=1` writes.
//! Every file there runs as a permanent case: `check` reports exactly its anchors,
//! or passes a file that has none.

use std::fs;
use std::path::Path;
use std::sync::Arc;

use enrang_diag::{Code, Milestone, Phase, RenderOpts, Severity};
use enrang_driver::{CheckError, CheckOptions, Checked, Session, check_with};
use enrang_mir::{Cfg, StatementKind};
use enrang_target::{TargetOpts, host_target, resolve};
use enrang_testkit::{
    BlessMode, Harness, Reported, Rng, Shrink, TempDir, anchors, catch_panic, compare,
    fixture_header, reported, rng_for, scaled, seed, shrink_within, workspace_root,
};

/// Where the shrunk failures are kept, each a permanent case.
const REGRESS: &str = "corpus/regress/mutants";

/// How many checks a failure's shrinking may make, two per candidate.
const SHRINK_LIMIT: usize = 200;

/// One violation of the fixed list and its fixed twin.
#[derive(Copy, Clone, Debug)]
pub struct Violation {
    /// How a failure names it.
    pub name: &'static str,
    /// The intended code.
    pub code: &'static str,
    /// A piece of the intended message, which tells the two EN0706 violations
    /// apart.
    pub piece: &'static str,
    /// The line that breaks the rule.
    pub broken: &'static str,
    /// The same line with the rule kept.
    pub fixed: &'static str,
    /// The first local both lines declare, in the body that holds them.
    pub marker: &'static str,
    /// What both lines need at the top level, appended to the file.
    pub decls: &'static str,
}

/// The fixed list (M3 plan f.7): a use after move, a push to a held source, a
/// write through a `const`, a store into a capture, an exclusive borrow beside a
/// live shared one, and a return of a local reference.
pub const VIOLATIONS: [Violation; 6] = [
    Violation {
        name: "a use after move",
        code: "EN0601",
        piece: "`mutant_s` was moved into `mutant_t`",
        broken: "let mutant_s = \"m\".toString(); const mutant_t = mutant_s; \
                 const mutant_n = mutant_s.length();",
        fixed: "let mutant_s = \"m\".toString(); const mutant_t = mutant_s.clone(); \
                const mutant_n = mutant_s.length();",
        marker: "mutant_s",
        decls: "",
    },
    Violation {
        name: "a push to a held source",
        code: "EN0706",
        piece: "cannot mutate `mutant_q` while iterating over it",
        broken: "let mutant_q: i64[] = [1]; \
                 for (const mutant_x of &mutant_q) { mutant_q.push(2); }",
        fixed: "let mutant_q: i64[] = [1]; \
                for (const mutant_x of [...mutant_q]) { mutant_q.push(2); }",
        marker: "mutant_q",
        decls: "",
    },
    Violation {
        name: "a write through a const",
        code: "EN0608",
        piece: "because `mutant_c` is `const`",
        broken: "const mutant_c: i64[] = [1]; mutant_c[0] = 2;",
        fixed: "let mutant_c: i64[] = [1]; mutant_c[0] = 2;",
        marker: "mutant_c",
        decls: "",
    },
    Violation {
        name: "a store into a capture",
        code: "EN0616",
        piece: "cannot store a reference into",
        broken: "let mutant_a: i64 = 1; let mutant_b: i64 = 2; \
                 let mutant_c = new MutantCell(&mutant_a); \
                 const mutant_f = (): void => { mutant_c.set(&mutant_b); }; mutant_f();",
        fixed: "let mutant_a: i64 = 1; let mutant_b: i64 = 2; \
                let mutant_c = new MutantCell(&mutant_a); mutant_c.set(&mutant_b); \
                const mutant_f = (): i64 => mutant_c.get(); mutant_f();",
        marker: "mutant_a",
        decls: "private class MutantCell { private r: &i64; \
                public constructor(r: &i64) { this.r = r; } \
                public set(r: &i64): void { this.r = r; } \
                public get(): i64 { return *this.r; } }",
    },
    Violation {
        name: "an exclusive borrow beside a live shared one",
        code: "EN0706",
        piece: "`mutant_v` cannot change while `mutant_e` still points into it",
        broken: "let mutant_v: i64[] = [1]; const mutant_e = &mutant_v[0]; \
                 const mutant_w = &mutant_v; mutant_w.push(2); const mutant_k = *mutant_e;",
        fixed: "let mutant_v: i64[] = [1]; const mutant_e = &mutant_v[0]; \
                const mutant_k = *mutant_e; const mutant_w = &mutant_v; mutant_w.push(2);",
        marker: "mutant_v",
        decls: "",
    },
    Violation {
        name: "a return of a local reference",
        code: "EN0710",
        piece: "cannot return a reference to local `mutant_l`",
        broken: "const mutant_f = (): &i64 => { const mutant_l: i64 = 1; return &mutant_l; };",
        fixed: "const mutant_f = (): i64 => { const mutant_l: i64 = 1; return mutant_l; };",
        marker: "mutant_f",
        decls: "",
    },
];

impl Violation {
    /// The broken line with its anchor.
    fn anchored(&self) -> String {
        format!("{} //~ {} \"{}\"", self.broken, self.code, self.piece)
    }
}

/// An accepted program a violation goes into.
#[derive(Clone, Debug)]
pub struct Host {
    /// How its case names it: its path, or its case in this suite.
    pub name: String,
    /// The name of its file, as `check` reads it.
    pub file: String,
    pub text: String,
    /// The `//! target:` of its header; the host's otherwise.
    pub target: Option<String>,
    /// Its header's `//! library`.
    pub library: bool,
    /// The files its relative imports read, by name beside it, with their text.
    pub imports: Vec<(String, String)>,
    /// Why it cannot be a host: its file cannot be read or its header is broken.
    pub broken: Option<String>,
}

impl Host {
    /// A program of this suite, checked as `main.en`.
    fn memory(name: String, text: String) -> Host {
        Host {
            name,
            file: "main.en".to_owned(),
            text,
            target: None,
            library: false,
            imports: Vec::new(),
            broken: None,
        }
    }

    /// A file of the workspace, by its path from the root, with its header and
    /// the files its relative imports read; a header that does not parse makes the
    /// host's case fail rather than the registration of every case.
    fn disk(path: &str) -> Host {
        let read = fs::read_to_string(workspace_root().join(path)).map_err(|e| e.to_string());
        let text = read.clone().unwrap_or_default();
        let header = read.and_then(|text| fixture_header(&text));
        let (dir, file) = path.rsplit_once('/').unwrap_or(("", path));
        Host {
            name: path.to_owned(),
            file: file.to_owned(),
            imports: imports_of(dir, &text),
            text,
            target: header.as_ref().ok().and_then(|h| h.target.clone()),
            library: header.as_ref().is_ok_and(|h| h.library),
            broken: header.err(),
        }
    }

    /// The same host with another text.
    fn with_text(&self, text: String) -> Host {
        Host {
            text,
            ..self.clone()
        }
    }
}

/// The files that `text`, a file of `dir`, reads by its relative imports
/// (`from "./name"` reads `name.en` beside it), and theirs, by name.
fn imports_of(dir: &str, text: &str) -> Vec<(String, String)> {
    let mut found: Vec<(String, String)> = Vec::new();
    let mut work = vec![text.to_owned()];
    while let Some(text) = work.pop() {
        for piece in text.split("from \"./").skip(1) {
            let Some((name, _)) = piece.split_once('"') else {
                continue;
            };
            let file = format!("{name}.en");
            if found.iter().any(|(seen, _)| *seen == file) {
                continue;
            }
            if let Ok(imported) = fs::read_to_string(workspace_root().join(dir).join(&file)) {
                work.push(imported.clone());
                found.push((file, imported));
            }
        }
    }
    found.sort();
    found
}

/// The near-misses of every code M3 delivers, in path order.
fn near_misses() -> Vec<String> {
    let root = workspace_root().join("tests/compile");
    let mut dirs: Vec<String> = fs::read_dir(&root)
        .map(|entries| {
            (entries.flatten())
                .map(|entry| entry.file_name().to_string_lossy().into_owned())
                .collect()
        })
        .unwrap_or_default();
    dirs.retain(|dir| Code::from_name(dir).is_some_and(|code| code.since() == Milestone::M3));
    dirs.sort();
    let mut found = Vec::new();
    for dir in dirs {
        let mut files: Vec<String> = fs::read_dir(root.join(&dir))
            .map(|entries| {
                (entries.flatten())
                    .map(|entry| entry.file_name().to_string_lossy().into_owned())
                    .filter(|name| name.ends_with(".pass.en"))
                    .collect()
            })
            .unwrap_or_default();
        files.sort();
        found.extend(
            files
                .into_iter()
                .map(|file| format!("tests/compile/{dir}/{file}")),
        );
    }
    found
}

/// Every host: the near-misses of M3's codes, then this suite's accepted programs.
pub fn hosts() -> Vec<Host> {
    let mut hosts: Vec<Host> = near_misses().iter().map(|path| Host::disk(path)).collect();
    let programs = [
        crate::programs::accepted(),
        crate::fixes::accepted(),
        crate::review3::accepted(),
        crate::soundfix::accepted(),
        crate::integrate::accepted(),
    ];
    for (name, text) in programs.into_iter().flatten() {
        hosts.push(Host::memory(name, text));
    }
    hosts
}

/// The name of a host's case, which also names its generator.
fn case_name(host: &Host) -> String {
    format!(
        "mutants/{}: a violation is rejected with its intended code",
        host.name
    )
}

/// What `check` made of a program.
pub enum Outcome {
    /// Phases 1 or 2 reject it: it does not type-check.
    Untyped,
    /// It passes.
    Passed(Box<Checked>),
    /// Phase 3 or 4 rejects it: its errors, as the rendered report gives them.
    Rejected(Vec<Reported>, String),
}

/// `check` of `host`, phases 1 to 4, in a fresh directory holding its file and the
/// files its imports read; an internal error, a panic or an unreadable file is
/// the error.
pub fn run(host: &Host) -> Result<Outcome, String> {
    let dir = TempDir::new("mutants");
    dir.write(&host.file, &host.text);
    for (name, text) in &host.imports {
        dir.write(name, text);
    }
    let name = host.target.as_deref().unwrap_or(host_target());
    let target = resolve(name, &TargetOpts::default())
        .map_err(|_| format!("no target `{name}`"))?
        .0;
    let options = CheckOptions {
        library_entry: host.library,
        project: None,
    };
    let mut session = Session::new();
    let mut result = None;
    let entry = Path::new(&host.file);
    if let Some(panic) = catch_panic(|| {
        result = Some(check_with(
            &mut session,
            dir.path(),
            entry,
            Arc::new(target),
            &options,
        ))
    }) {
        return Err(format!("check panicked: {panic}"));
    }
    match result.expect("ran") {
        Ok(checked) => Ok(Outcome::Passed(Box::new(checked))),
        Err(CheckError::Aborted(_)) => {
            let rendered = session.render(&RenderOpts { color: false });
            let errors: Vec<Reported> = (reported(&rendered).into_iter())
                .filter(|diag| {
                    Code::from_name(&diag.code).is_some_and(|c| c.severity() == Severity::Error)
                })
                .collect();
            let early = errors
                .iter()
                .any(|diag| Code::from_name(&diag.code).is_some_and(|c| c.phase() <= Phase::Types));
            match early {
                true => Ok(Outcome::Untyped),
                false => Ok(Outcome::Rejected(errors, rendered)),
            }
        }
        Err(CheckError::Internal(internal)) => Err(format!("internal error: {}", internal.0)),
        Err(CheckError::Unreadable { path, error }) => {
            Err(format!("cannot read {}: {error}", path.display()))
        }
    }
}

/// Whether a local named `marker` lies in a block reachable from its body's entry
/// in what `check` built.
fn reached(checked: &Checked, marker: &str) -> bool {
    checked.mir.values().any(|body| {
        let locals: Vec<_> = (body.locals.iter_enumerated())
            .filter(|(_, decl)| decl.name.is_some_and(|name| name.as_str() == marker))
            .map(|(local, _)| local)
            .collect();
        if locals.is_empty() {
            return false;
        }
        let cfg = Cfg::new(body);
        (body.blocks.iter_enumerated()).any(|(id, block)| {
            cfg.reachable.contains(id)
                && block.stmts.iter().any(|stmt| {
                    matches!(stmt.kind, StatementKind::StorageLive(local) if locals.contains(&local))
                })
        })
    })
}

/// What a `{` opens, or a `(` or `[`.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Open {
    Paren,
    Bracket,
    /// A block of statements.
    Block,
    /// Braces that hold no statements: a class, an object, a type, a `match`.
    Braces,
}

/// An open bracket and where the statement, or element, now being read in it
/// began.
struct Frame {
    open: Open,
    start: usize,
}

/// The byte offset after a string, a character or a template literal that starts
/// at `at`, or after a comment.
fn skip_literal(bytes: &[u8], at: usize) -> usize {
    let quote = bytes[at];
    if quote == b'/' {
        if bytes.get(at + 1) == Some(&b'/') {
            return (at..bytes.len())
                .find(|&i| bytes[i] == b'\n')
                .unwrap_or(bytes.len());
        }
        let mut i = at + 2;
        while i + 1 < bytes.len() && !(bytes[i] == b'*' && bytes[i + 1] == b'/') {
            i += 1;
        }
        return (i + 2).min(bytes.len());
    }
    let mut i = at + 1;
    let mut depth = 0usize;
    while i < bytes.len() {
        match bytes[i] {
            b'\\' => i += 1,
            b'$' if quote == b'`' && bytes.get(i + 1) == Some(&b'{') => {
                depth += 1;
                i += 1;
            }
            b'}' if depth > 0 => depth -= 1,
            b if b == quote && depth == 0 => return i + 1,
            _ => {}
        }
        i += 1;
    }
    bytes.len()
}

/// Whether a `{` whose head, the text of its statement before it, is `head` opens
/// a block of statements; `in_block` says whether the `{` stands where a
/// statement may.
fn opens_block(head: &str, in_block: bool) -> bool {
    let words: Vec<&str> = head
        .split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .filter(|word| !word.is_empty())
        .collect();
    let declares = ["class", "interface", "enum", "match", "namespace"];
    if words.iter().any(|word| declares.contains(word)) {
        return false;
    }
    let keyword = ["else", "do", "try", "finally", "unsafe"]
        .iter()
        .any(|kw| words.last() == Some(kw) && head.ends_with(kw));
    let returns = head
        .rsplit_once(')')
        .is_some_and(|(_, rest)| rest.trim_start().starts_with(':') && !rest.contains('='));
    (head.is_empty() && in_block)
        || head.ends_with(')')
        || head.ends_with("=>")
        || keyword
        || returns
        || words.first() == Some(&"test")
}

/// Whether the statement `text` leaves its block: what follows it in the block is
/// not reached.
fn jumps(text: &str) -> bool {
    let text = text.trim_start();
    ["return", "break", "continue", "throw"].iter().any(|kw| {
        text.strip_prefix(kw)
            .is_some_and(|rest| !rest.starts_with(|c: char| c.is_alphanumeric() || c == '_'))
    })
}

/// Whether the first word after `at`, past spaces and comments, continues the
/// statement before it.
fn continues(bytes: &[u8], mut at: usize) -> bool {
    loop {
        while at < bytes.len() && bytes[at].is_ascii_whitespace() {
            at += 1;
        }
        if bytes.get(at) == Some(&b'/') && matches!(bytes.get(at + 1), Some(b'/' | b'*')) {
            at = skip_literal(bytes, at);
            continue;
        }
        break;
    }
    let rest = &bytes[at.min(bytes.len())..];
    ["else", "catch", "finally"].iter().any(|kw| {
        rest.starts_with(kw.as_bytes())
            && !rest
                .get(kw.len())
                .is_some_and(|b| b.is_ascii_alphanumeric() || *b == b'_')
    })
}

/// The places of `text` where a statement may begin, as byte offsets in order:
/// after a `{` that opens a block and after a `;` that ends a statement of one or
/// of the top level, outside literals and comments, unless the statement leaves
/// its block or the next word continues it; and the end of the file.
pub fn sites(text: &str) -> Vec<usize> {
    let bytes = text.as_bytes();
    let mut stack: Vec<Frame> = Vec::new();
    let mut top = 0;
    let mut found = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        let start = stack.last().map_or(top, |frame| frame.start);
        let in_block = stack.last().is_none_or(|frame| frame.open == Open::Block);
        match b {
            b'"' | b'\'' | b'`' => {
                i = skip_literal(bytes, i);
                continue;
            }
            b'/' if matches!(bytes.get(i + 1), Some(b'/' | b'*')) => {
                i = skip_literal(bytes, i);
                continue;
            }
            b'(' | b'[' => stack.push(Frame {
                open: if b == b'(' {
                    Open::Paren
                } else {
                    Open::Bracket
                },
                start: i + 1,
            }),
            b'{' => {
                let head = text[start..i].trim();
                let open = match opens_block(head, in_block) {
                    true => Open::Block,
                    false => Open::Braces,
                };
                stack.push(Frame { open, start: i + 1 });
                if open == Open::Block {
                    found.push(i + 1);
                }
            }
            b')' | b']' => {
                stack.pop();
            }
            b'}' => {
                // A block, a class or a `match` ends the statement it closes; an
                // object's braces end none, but nothing after them in their
                // statement opens a block or leaves one.
                stack.pop();
                match stack.last_mut() {
                    Some(frame) => frame.start = i + 1,
                    None => top = i + 1,
                }
            }
            b';' | b',' => {
                if b == b';' && in_block && !jumps(&text[start..i]) && !continues(bytes, i + 1) {
                    found.push(i + 1);
                }
                match stack.last_mut() {
                    Some(frame) => frame.start = i + 1,
                    None => top = i + 1,
                }
            }
            _ => {}
        }
        i += 1;
    }
    if found.last() != Some(&text.len()) {
        found.push(text.len());
    }
    found
}

/// `text` with `line` inserted on a line of its own at `site`, and `decls`
/// appended; and the number of the inserted line.
pub fn insert(text: &str, site: usize, line: &str, decls: &str) -> (String, usize) {
    let (before, after) = text.split_at(site);
    let mut out = before.to_owned();
    if !out.is_empty() && !out.ends_with('\n') {
        out.push('\n');
    }
    let number = out.matches('\n').count() + 1;
    out.push_str(line);
    out.push('\n');
    out.push_str(after);
    if !decls.is_empty() {
        if !out.ends_with('\n') {
            out.push('\n');
        }
        out.push_str(decls);
        out.push('\n');
    }
    (out, number)
}

/// What a place came to.
#[derive(Debug)]
pub enum Place {
    /// The twin passed there and the violation was rejected as intended.
    Taken,
    /// The twin does not type-check there, or is not reached, or meets the one
    /// rule of a place, EN0610 before `super(...)`; or only the violation does
    /// not type-check: no violation can be judged there.
    Unusable,
}

/// What a violation's twin came to at a place.
enum Twin {
    /// It passes and is reached: the place is usable.
    Passes,
    /// No violation can be judged there ([`Place::Unusable`]).
    Unusable,
    /// Phase 3 or 4 rejects it, though it keeps every rule: the report.
    Rejected(String),
}

/// A rejection of a twin that is no failure of this generator, with its reason:
/// a rule of the place, or a compiler disagreement pinned by [`PINNED`], whose
/// excuse goes once the compiler accepts the program.
struct Excuse {
    why: &'static str,
    /// Whether it covers a rejection of `violation`'s twin on line `line`, with
    /// these errors and this report.
    covers: fn(&Violation, &[Reported], &str, usize) -> bool,
}

/// Before `super(...)` only an own field may be assigned (A:998).
fn before_super(_: &Violation, errors: &[Reported], _: &str, _: usize) -> bool {
    !errors.is_empty() && errors.iter().all(|diag| diag.code == "EN0610")
}

/// [`PINNED`]'s row, met by any twin between a pair and its `return`.
fn call_before_pair_return(
    _: &Violation,
    errors: &[Reported],
    rendered: &str,
    line: usize,
) -> bool {
    rendered.contains("returns two references that may point at the same data")
        && (errors.iter()).all(|diag| diag.code == "EN0616" && diag.line() != Some(line))
}

/// Every [`Excuse`].
const EXCUSES: [Excuse; 2] = [
    Excuse {
        why: "before `super(...)` only an own field may be assigned (A:998), so no \
              statement may stand there",
        covers: before_super,
    },
    Excuse {
        why: "compiler disagreement, pinned: a call between a pair of references and \
              its `return` makes the pair read-only (T:686)",
        covers: call_before_pair_return,
    },
];

/// The compiler disagreements the twins found, each a program that keeps every
/// rule, with what shows it, and what phase 3 reports today as (code, line); a fix
/// fails its case, and then its [`Excuse`] goes with the row.
const PINNED: [(&str, &str, &[(&str, usize)]); 1] = [(
    "TK-01-local with a call between the pair and its `return` (T:686: the local \
         is written or borrowed for writing nowhere before the `return`)",
    "let pr = new Pair { a: 0, b: 0 };
const r = both(&pr); *r[0] = 1; *r[1] = 2;

public class Pair { public a: i64; public b: i64; }

private function both(p: &Pair): [&i64, &i64] {
  const t: [&i64, &i64] = [&p.a, &p.b];
  console.log(1);
  return t;
}
",
    &[("EN0616", 2), ("EN0616", 2)],
)];

/// What `check` makes of `text`, `violation`'s twin inserted into `host` on line
/// `line`.
fn twin(host: &Host, text: String, violation: &Violation, line: usize) -> Result<Twin, String> {
    match run(&host.with_text(text))? {
        Outcome::Passed(checked) if reached(&checked, violation.marker) => Ok(Twin::Passes),
        Outcome::Passed(_) | Outcome::Untyped => Ok(Twin::Unusable),
        Outcome::Rejected(errors, rendered) => {
            let excused = (EXCUSES.iter()).any(|e| (e.covers)(violation, &errors, &rendered, line));
            match excused {
                true => Ok(Twin::Unusable),
                false => Ok(Twin::Rejected(rendered)),
            }
        }
    }
}

/// What `check` makes of a mutant, judged against its anchors.
enum Judged {
    /// It reports exactly its anchors.
    AsAnchored,
    /// Phases 1 or 2 reject it: no verdict.
    Untyped,
    /// It passes, or reports something else: how.
    Otherwise(String),
}

/// `check` of `mutant`, anchored, inserted into `host`, against its anchors.
fn judge(host: &Host, mutant: &str) -> Result<Judged, String> {
    let wanted = anchors(mutant).map_err(|e| format!("line {}: {}", e.line, e.message))?;
    match run(&host.with_text(mutant.to_owned()))? {
        Outcome::Untyped => Ok(Judged::Untyped),
        Outcome::Passed(_) => Ok(Judged::Otherwise("check passes it".to_owned())),
        Outcome::Rejected(errors, rendered) => match compare(&wanted, &errors) {
            Ok(()) => Ok(Judged::AsAnchored),
            Err(mismatch) => Ok(Judged::Otherwise(format!("{mismatch}{rendered}"))),
        },
    }
}

/// A line of a failing mutant, kept or removed whole while it shrinks.
#[derive(Clone, Debug)]
struct Line(String);

impl Shrink for Line {
    fn candidates(&self) -> Box<dyn Iterator<Item = Line> + '_> {
        Box::new(std::iter::empty())
    }
}

/// A failing mutant cut at its violation's line: its header lines, kept, then the
/// lines before and after the violation, which shrinking removes.
#[derive(Clone, Debug)]
struct Cut {
    header: Vec<String>,
    parts: (Vec<Line>, Vec<Line>),
}

impl Shrink for Cut {
    fn candidates(&self) -> Box<dyn Iterator<Item = Cut> + '_> {
        Box::new(self.parts.candidates().map(|parts| Cut {
            header: self.header.clone(),
            parts,
        }))
    }
}

impl Cut {
    fn new(text: &str, number: usize) -> Cut {
        let lines: Vec<&str> = text.lines().collect();
        let header_len = (lines.iter())
            .take(number - 1)
            .take_while(|line| line.trim_start().starts_with("//!"))
            .count();
        let line = |s: &&str| Line((*s).to_owned());
        Cut {
            header: lines[..header_len]
                .iter()
                .map(|s| (*s).to_owned())
                .collect(),
            parts: (
                lines[header_len..number - 1].iter().map(line).collect(),
                lines[number..].iter().map(line).collect(),
            ),
        }
    }

    /// The number of the violation's line.
    fn number(&self) -> usize {
        self.header.len() + self.parts.0.len() + 1
    }

    /// The program with `middle` on the violation's line.
    fn text(&self, middle: &str) -> String {
        let mut out = String::new();
        let lines = (self.header.iter())
            .chain(self.parts.0.iter().map(|line| &line.0))
            .chain(std::iter::once(&middle.to_owned()))
            .chain(self.parts.1.iter().map(|line| &line.0))
            .cloned()
            .collect::<Vec<String>>();
        for line in lines {
            out.push_str(&line);
            out.push('\n');
        }
        out
    }
}

/// The name of a regression case: its host and violation, slugged, and `end`.
fn regress_name(host: &Host, violation: &Violation, end: &str) -> String {
    let host = (host.name.strip_prefix("tests/compile/"))
        .and_then(|rest| rest.strip_suffix(".pass.en"))
        .unwrap_or(&host.name);
    let mut slug = String::new();
    for c in format!("{host}-{}", violation.name)
        .chars()
        .flat_map(char::to_lowercase)
    {
        let c = if c.is_ascii_alphanumeric() { c } else { '-' };
        if !(c == '-' && (slug.is_empty() || slug.ends_with('-'))) {
            slug.push(c);
        }
    }
    format!("{}{end}", slug.trim_end_matches('-'))
}

/// Where a shrunk failure is kept: printed with the seed, and written to
/// [`REGRESS`] when `bless`, as `ENRANG_BLESS=1` asks; what to say of it.
fn keep(path: &str, text: &str, bless: bool) -> String {
    match bless {
        true => {
            let full = workspace_root().join(path);
            let made = (full.parent())
                .map_or(Ok(()), fs::create_dir_all)
                .and_then(|()| fs::write(&full, text));
            match made {
                Ok(()) => format!("written to {path}"),
                Err(error) => format!("not written to {path}: {error}"),
            }
        }
        false => format!("to keep as {path} (ENRANG_BLESS=1 writes it)"),
    }
}

/// The line that ends a regression case, naming where it came from.
fn provenance(host: &Host, violation: &Violation, what: &str) -> String {
    format!(
        "// Mutants (TESTING 14): {what} of {} into {}, ENRANG_SEED={:#x}.\n",
        violation.name,
        host.name,
        seed()
    )
}

/// The report of a failing mutant, `line` its violation's line, anchored: shrunk
/// by whole lines while the twin still passes and the violation still fails.
fn failure(
    host: &Host,
    violation: &Violation,
    line: &str,
    mutant: &str,
    number: usize,
    why: &str,
    bless: bool,
) -> String {
    let still_fails = |cut: &Cut| -> bool {
        matches!(
            twin(host, cut.text(violation.fixed), violation, cut.number()),
            Ok(Twin::Passes)
        ) && matches!(judge(host, &cut.text(line)), Ok(Judged::Otherwise(_)))
    };
    let small = shrink_within(Cut::new(mutant, number), SHRINK_LIMIT, still_fails);
    let mut text = small.text(line);
    text.push_str(&provenance(host, violation, "the violation"));
    let path = format!("{REGRESS}/{}", regress_name(host, violation, ".fail.en"));
    format!(
        "{} into {} at line {number} is not rejected as its anchor says \
         (ENRANG_SEED={:#x}):\n{why}\nshrunk, {}:\n{text}",
        violation.name,
        host.name,
        seed(),
        keep(&path, &text, bless)
    )
}

/// The report of a twin that keeps every rule and is rejected: shrunk by whole
/// lines while it still is, kept as a regression case that must pass.
fn rejected_twin(
    host: &Host,
    violation: &Violation,
    twin_text: &str,
    number: usize,
    why: &str,
    bless: bool,
) -> String {
    let still_fails = |cut: &Cut| -> bool {
        matches!(
            twin(host, cut.text(violation.fixed), violation, cut.number()),
            Ok(Twin::Rejected(_))
        )
    };
    let small = shrink_within(Cut::new(twin_text, number), SHRINK_LIMIT, still_fails);
    let mut text = small.text(violation.fixed);
    text.push_str(&provenance(host, violation, "the fixed twin"));
    let path = format!(
        "{REGRESS}/{}",
        regress_name(host, violation, "-twin.pass.en")
    );
    format!(
        "the fixed twin of {} into {} at line {number} keeps every rule, but check \
         rejects it (ENRANG_SEED={:#x}):\n{why}\nshrunk, {}:\n{text}",
        violation.name,
        host.name,
        seed(),
        keep(&path, &text, bless)
    )
}

/// `violation` at `site` of `host`: its twin first, then the violation itself; the
/// error is the failure's report, shrunk, and its regression case written when
/// `bless`.
pub fn try_place(
    host: &Host,
    violation: &Violation,
    site: usize,
    bless: bool,
) -> Result<Place, String> {
    try_lines(host, violation, site, &violation.anchored(), bless)
}

/// [`try_place`] with `line` as the violation's line, anchored.
fn try_lines(
    host: &Host,
    violation: &Violation,
    site: usize,
    line: &str,
    bless: bool,
) -> Result<Place, String> {
    let in_host = |e: String| format!("{}: {e}", host.name);
    let (twin_text, number) = insert(&host.text, site, violation.fixed, violation.decls);
    match twin(host, twin_text.clone(), violation, number).map_err(in_host)? {
        Twin::Passes => {}
        Twin::Unusable => return Ok(Place::Unusable),
        Twin::Rejected(why) => {
            return Err(rejected_twin(
                host, violation, &twin_text, number, &why, bless,
            ));
        }
    }
    let (mutant, number) = insert(&host.text, site, line, violation.decls);
    match judge(host, &mutant).map_err(in_host)? {
        Judged::AsAnchored => Ok(Place::Taken),
        // A violation that does not type-check where its twin does is no verdict.
        Judged::Untyped => Ok(Place::Unusable),
        Judged::Otherwise(why) => Err(failure(host, violation, line, &mutant, number, &why, bless)),
    }
}

/// The violation a host's generator draws, and the order of its places.
fn draw(host: &Host) -> (Violation, Vec<usize>) {
    let mut rng = rng_for(&case_name(host));
    let violation = VIOLATIONS[rng.below(VIOLATIONS.len() as u64) as usize];
    let mut places = sites(&host.text);
    for i in (1..places.len()).rev() {
        let j = rng.below(i as u64 + 1) as usize;
        places.swap(i, j);
    }
    (violation, places)
}

/// One host's case: `scaled(1)` places taken, the violation rejected as intended
/// at each.
fn one(host: &Host) -> Result<(), String> {
    if let Some(why) = &host.broken {
        return Err(format!("{}: cannot be a host: {why}", host.name));
    }
    let (violation, places) = draw(host);
    let wanted = scaled(1);
    let bless = matches!(BlessMode::from_env(), BlessMode::Bless);
    let mut taken = 0;
    for site in places {
        if let Place::Taken = try_place(host, &violation, site, bless)? {
            taken += 1;
            if taken == wanted {
                return Ok(());
            }
        }
    }
    match taken {
        0 => Err(format!(
            "{}: no place takes the twin of {} (ENRANG_SEED={:#x})",
            host.name,
            violation.name,
            seed()
        )),
        _ => Ok(()),
    }
}

/// The shrunk failures of earlier runs, each a permanent case, as `(file name,
/// text)` in name order: `corpus/regress/mutants/*.en`.
fn regressions() -> Vec<(String, String)> {
    let dir = workspace_root().join(REGRESS);
    let mut found: Vec<(String, String)> = fs::read_dir(&dir)
        .map(|entries| {
            (entries.flatten())
                .map(|entry| entry.path())
                .filter(|path| path.extension().is_some_and(|ext| ext == "en"))
                .map(|path| {
                    let name = path.file_name().unwrap_or_default().to_string_lossy();
                    let text = fs::read_to_string(&path).unwrap_or_default();
                    (name.into_owned(), text)
                })
                .collect()
        })
        .unwrap_or_default();
    found.sort();
    found
}

/// A regression case: `check` reports exactly its anchors, or passes one that
/// has none, a fixed twin's (`-twin.pass.en`).
fn regression(name: &str, text: &str) -> Result<(), String> {
    let wanted = anchors(text).map_err(|e| format!("line {}: {}", e.line, e.message))?;
    let header = fixture_header(text)?;
    let host = Host {
        name: format!("{REGRESS}/{name}"),
        file: name.to_owned(),
        text: text.to_owned(),
        target: header.target,
        library: header.library,
        imports: Vec::new(),
        broken: None,
    };
    match (wanted.is_empty(), judge(&host, text)?) {
        (false, Judged::AsAnchored) => Ok(()),
        (true, Judged::Otherwise(why)) if why == "check passes it" => Ok(()),
        (true, Judged::Otherwise(why)) => Err(format!("{name} must pass check:\n{why}")),
        (_, Judged::Untyped) => Err(format!("{name} does not type-check")),
        (_, Judged::Otherwise(why)) => Err(format!("{name}:\n{why}")),
        (true, Judged::AsAnchored) => unreachable!("no anchors, and errors that match none"),
    }
}

/// A small program with a place of each kind: the top level, a function body, a
/// loop, a branch, an arrow, a method and a constructor.
const SMALL: &str = "const pad = 1;
console.log(f(3), pad);
let c = new Counter(1);
c.bump();

private function f(n: i64): i64 {
  let total = 0;
  for (let i = 0; i < n; i += 1) {
    if (i > 1) {
      total += i;
    } else {
      total -= 1;
    }
  }
  const g = (x: i64): i64 => { return x + 1; };
  return g(total);
}

private class Counter {
  private n: i64 = 0;
  public constructor(start: i64) {
    this.n = start;
  }
  public bump(): void {
    this.n += 1;
  }
}
";

pub fn register(h: &mut Harness) {
    let hosts = hosts();
    let near = hosts
        .iter()
        .filter(|host| host.file.ends_with(".pass.en"))
        .count();
    let programs = hosts.len() - near;
    h.case(
        "mutants/the hosts are every near-miss of an M3 code and the accepted pipeline programs",
        move || {
            assert!(near >= 700, "only {near} near-misses");
            assert!(programs >= 50, "only {programs} programs");
        },
    );
    let names: Vec<String> = hosts.iter().map(case_name).collect();
    h.case(
        "mutants/every violation is drawn for some host",
        move || {
            let drawn: Vec<&str> = (names.iter())
                .map(|name| {
                    let mut rng = rng_for(name);
                    VIOLATIONS[rng.below(VIOLATIONS.len() as u64) as usize].name
                })
                .collect();
            for violation in VIOLATIONS {
                assert!(
                    drawn.contains(&violation.name),
                    "{} is never drawn",
                    violation.name
                );
            }
        },
    );
    h.case(
        "mutants/the places where a statement may begin",
        || {
            let text = "function f(): void { const p = new P { a: 1 }; if (true) { return; } g(\"{;\"); }\n\
                        private class P { public a: i64 = 0; }\n";
            let at = |piece: &str| text.find(piece).expect("a piece") + piece.len();
            assert_eq!(
                sites(text),
                [
                    at("void {"),
                    at("a: 1 };"),
                    at("(true) {"),
                    at("\"{;\");"),
                    text.len()
                ]
            );
            // An arrow's block in an argument, a `match` arm's, an `else`, and a
            // loop's head are told apart.
            let text = "xs.forEach((x: &i64) => { log(x); });\n\
                        match (s) { S.A => { a(); }, default => {} }\n\
                        if (c) { a(); } else { b(); }\n\
                        for (let i = 0; i < 2; i += 1) { a(); }\n";
            let at = |piece: &str| text.find(piece).expect("a piece") + piece.len();
            assert_eq!(
                sites(text),
                [
                    at("=> {"),
                    at("log(x);"),
                    at("});"),
                    at("S.A => {"),
                    at("S.A => { a();"),
                    at("default => {"),
                    at("if (c) {"),
                    at("if (c) { a();"),
                    at("else {"),
                    at("else { b();"),
                    at("i += 1) {"),
                    at("i += 1) { a();"),
                    text.len()
                ]
            );
        },
    );
    h.case(
        "mutants/each violation is rejected as intended at every usable place of a small program",
        || {
            let host = Host::memory("small".to_owned(), SMALL.to_owned());
            let mut problems = Vec::new();
            for violation in &VIOLATIONS {
                let mut taken = 0;
                for site in sites(SMALL) {
                    match try_place(&host, violation, site, false) {
                        Ok(Place::Taken) => taken += 1,
                        Ok(Place::Unusable) => {}
                        Err(failure) => problems.push(failure),
                    }
                }
                if taken < 10 {
                    problems.push(format!("{}: only {taken} places taken", violation.name));
                }
            }
            assert!(problems.is_empty(), "\n{}", problems.join("\n"));
        },
    );
    h.case(
        "mutants/the twin of a violation passes where the violation is rejected",
        || {
            for violation in &VIOLATIONS {
                let host = Host::memory("top".to_owned(), "const pad = 1;\n".to_owned());
                let site = "const pad = 1;".len();
                let (fixed, _) = insert(&host.text, site, violation.fixed, violation.decls);
                let passes = matches!(twin(&host, fixed, violation, 2), Ok(Twin::Passes));
                assert!(passes, "{}", violation.name);
                let (mutant, line) =
                    insert(&host.text, site, &violation.anchored(), violation.decls);
                assert_eq!(line, 2);
                let judged = judge(&host, &mutant);
                assert!(
                    matches!(judged, Ok(Judged::AsAnchored)),
                    "{}",
                    violation.name
                );
            }
        },
    );
    h.case(
        "mutants/a violation not rejected, or a twin rejected, fails, shrinks and names its case",
        || {
            // The twin anchored as if it broke the rule: `check` passes it, so the
            // generator must fail, shrink away the lines the failure does not need,
            // and name the regression case.
            let text =
                "const pad1 = 1;\nconst pad2 = 2;\nfunction f(): void {\n  const a = 1;\n}\nf();\n";
            let host = Host::memory("selftest".to_owned(), text.to_owned());
            let violation = VIOLATIONS[0];
            let site = text.find("const a = 1;").expect("a site") + "const a = 1;".len();
            let line = format!("{} //~ {}", violation.fixed, violation.code);
            let failed = try_lines(&host, &violation, site, &line, false).expect_err("a failure");
            assert!(failed.contains("check passes it"), "{failed}");
            assert!(
                failed.contains("corpus/regress/mutants/selftest-a-use-after-move.fail.en"),
                "{failed}"
            );
            let shrunk = failed.split("shrunk, ").nth(1).expect("the shrunk program");
            assert!(
                !shrunk.contains("pad1") && !shrunk.contains("pad2"),
                "{failed}"
            );
            assert!(shrunk.contains("ENRANG_SEED="), "{failed}");
            // A twin that breaks the rule after all is rejected: a failure too, kept
            // as a case that must pass.
            let bad = Violation {
                fixed: violation.broken,
                ..violation
            };
            let failed = try_place(&host, &bad, site, false).expect_err("a failure");
            assert!(failed.contains("keeps every rule, but check"), "{failed}");
            assert!(
                failed.contains("corpus/regress/mutants/selftest-a-use-after-move-twin.pass.en"),
                "{failed}"
            );
            let shrunk = failed.split("shrunk, ").nth(1).expect("the shrunk program");
            assert!(
                !shrunk.contains("pad1") && !shrunk.contains("pad2"),
                "{failed}"
            );
        },
    );
    h.case(
        "mutants/a regression case reports exactly its anchors, or passes with none",
        || {
            let violation = VIOLATIONS[2];
            let host = "const pad = 1;\n";
            let site = "const pad = 1;".len();
            let (mutant, _) = insert(host, site, &violation.anchored(), violation.decls);
            let (fixed, _) = insert(host, site, violation.fixed, violation.decls);
            assert_eq!(regression("m.fail.en", &mutant), Ok(()));
            assert_eq!(regression("t-twin.pass.en", &fixed), Ok(()));
            // A twin anchored with an error check never reports, and a violation
            // with no anchor, fail.
            let anchored =
                fixed.replace(violation.fixed, &format!("{} //~ EN0608", violation.fixed));
            assert!(regression("t-twin.pass.en", &anchored).is_err());
            let (bare, _) = insert(host, site, violation.broken, violation.decls);
            assert!(regression("m.fail.en", &bare).is_err());
        },
    );
    h.case(
        "mutants/each excuse of a rejected twin has its reason, and each pinned one its row",
        || {
            let pinned = (EXCUSES.iter())
                .filter(|e| e.why.contains("pinned"))
                .count();
            assert!(EXCUSES.iter().all(|e| !e.why.is_empty()));
            assert_eq!(pinned, PINNED.len());
        },
    );
    h.case(
        "mutants/a borrowing class made in a loop body from a local of the body compiles, \
         by `new` as by a static factory (`SetTable` starts the local's new value)",
        || {
            for make in ["new Cell(&a)", "Cell.make(&a)"] {
                let source = format!(
                    "let i = 0;
while (i < 2) {{
  let a: i64 = 1;
  let c = {make};
  console.log(c.get());
  i += 1;
}}

private class Cell {{
  private r: &i64;
  public constructor(r: &i64) {{ this.r = r; }}
  public static make(r: &i64): Cell {{ return new Cell(r); }}
  public get(): i64 {{ return *this.r; }}
}}
"
                );
                let host = Host::memory("contrast".to_owned(), source);
                match run(&host)? {
                    Outcome::Passed(_) => {}
                    Outcome::Untyped => return Err(format!("{make}: it does not type-check")),
                    Outcome::Rejected(_, rendered) => return Err(format!("{make}: {rendered}")),
                }
            }
            Ok(())
        },
    );
    for (name, source, today) in PINNED {
        h.case(
            format!("mutants/disagreement: {name}: rejected today (pinned)"),
            move || {
                let host = Host::memory("pinned".to_owned(), source.to_owned());
                let found: Vec<(String, usize)> = match run(&host)? {
                    Outcome::Rejected(errors, _) => (errors.iter())
                        .map(|diag| (diag.code.clone(), diag.line().unwrap_or(0)))
                        .collect(),
                    Outcome::Passed(_) => Vec::new(),
                    Outcome::Untyped => return Err("it does not type-check".to_owned()),
                };
                let today: Vec<(String, usize)> = (today.iter())
                    .map(|(code, line)| ((*code).to_owned(), *line))
                    .collect();
                match found == today {
                    true => Ok(()),
                    false => Err(format!(
                        "phase 3 now reports {found:?}, not {today:?}: if it accepts the \
                         program, remove this row and its excuse"
                    )),
                }
            },
        );
    }
    for host in hosts {
        h.case(case_name(&host), move || one(&host));
    }
    for (name, text) in regressions() {
        h.case(
            format!("mutants/regress/{name}: check reports exactly its anchors"),
            move || regression(&name, &text),
        );
    }
}
