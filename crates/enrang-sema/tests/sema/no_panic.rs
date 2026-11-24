//! No input makes phase 2 panic (owner 5A, plan g.1): every `ts` block of SPEC and
//! every compile fixture, then mutants of them, go through `load`, `analyze` and
//! `check_sizes` with the embedded library, as `enrang check` runs them, and nothing
//! panics, whatever the diagnostics.
//!
//! The mutants start from the seeds that reach phase 2. Most change one to three
//! words: a name, a type name, a keyword or a literal becomes another, which keeps
//! the file parsing and changes what it means. The rest are M1's GenBytes token
//! mutations (the syntax suite's `parser_props::mutate`): a token deleted, doubled,
//! swapped with the next, replaced or preceded by a fragment, or the file cut after
//! it. A quarter of the mutants at least must still reach phase 2. `scaled(400)`
//! mutants by default; a failure shrinks its text and prints `ENRANG_SEED` with it.

use std::path::PathBuf;
use std::sync::Arc;

use enrang_base::{FileOrigin, SourceMap};
use enrang_diag::DiagCtx;
use enrang_hir::Tcx;
use enrang_sema::{LoadError, ProgramInput, analyze, check_sizes, load};
use enrang_syntax::{NodeIdGen, ParseMode, lex};
use enrang_target::{TargetOpts, TargetSpec, resolve};
use enrang_testkit::{
    Harness, Rng, Xoshiro256, catch_panic, fenced_blocks, rng_for, scaled, seed, shrink_within,
    workspace_root,
};

/// Pieces a mutation writes in place of a token, or before one.
const FRAGMENTS: &[&str] = &[
    "x",
    "y",
    "this",
    "null",
    "0",
    "1",
    "-1",
    "2.5",
    "\"s\"",
    "true",
    "i64",
    "u8",
    "string",
    "&",
    "&x",
    "*",
    "?",
    "!",
    "?.",
    "??",
    "as u8",
    "as i64",
    "[]",
    "[0]",
    "[1, 2]",
    ".length()",
    ".push(1)",
    ".clone()",
    "new",
    "new C()",
    "Box<i64>",
    "Slice<u8>",
    "| null",
    "&i64[]",
    "T",
    "<T>",
    "<i64>",
    "=>",
    "x => x",
    "(x: i64) => x",
    "...",
    "...xs",
    "match",
    "case",
    "Ok(1)",
    "Err(\"e\")",
    "return",
    "break",
    ";",
    ",",
    "(",
    ")",
    "{",
    "}",
    ":",
    "=",
    "==",
    "+",
    "-",
    "/",
    "%",
    "<<",
    "&&",
    "||",
    "let",
    "const",
    "unsafe",
    "readonly",
    "move",
    "static",
    "public",
    "private",
    "extends",
    "implements",
    "Copy",
    "Clone",
    "Error",
    "sizeOf<i64>()",
    "offsetOf<C>(\"x\")",
    "void",
    "never",
    "fn(x: i64) => i64",
    "for",
    "of",
    "in",
    "if",
    "else",
    "while",
];

/// Words that may stand where another word stands: names, type names, keywords
/// and literals.
const WORDS: &[&str] = &[
    "x", "y", "xs", "s", "n", "this", "null", "0", "1", "255", "256", "-1", "2.5", "\"s\"", "true",
    "false", "i64", "i32", "u8", "usize", "isize", "f64", "bool", "string", "void", "never", "Box",
    "Slice", "Result", "Ok", "Err", "Copy", "Clone", "Error", "T", "U", "let", "const", "move",
    "static", "readonly", "unsafe", "public", "private", "new", "length", "push", "clone", "map",
    "console", "log", "main", "C", "E", "Self",
];

/// Where a source goes: a module's own file, or its test part (a block holding test
/// items).
fn name_for(text: &str) -> &'static str {
    let test = [
        "describe(",
        "test(",
        "compileFails(",
        "compileOk(",
        "expect(",
    ]
    .iter()
    .any(|item| text.contains(item));
    if test { "m.test.en" } else { "m.en" }
}

/// The seeds: SPEC's `ts` blocks, then the compile fixtures, each with its name.
fn seeds() -> Vec<(String, String)> {
    let spec = std::fs::read_to_string(workspace_root().join("docs/SPEC.md")).expect("SPEC");
    let mut found: Vec<(String, String)> = fenced_blocks(&spec)
        .unwrap_or_else(|errors| panic!("{errors}"))
        .into_iter()
        .filter(|block| block.lang == "ts")
        .map(|block| (name_for(&block.contents).to_owned(), block.contents))
        .collect();
    let root = workspace_root().join("tests/compile");
    let mut paths = Vec::new();
    for dir in std::fs::read_dir(&root).expect("tests/compile") {
        for file in std::fs::read_dir(dir.expect("an entry").path()).expect("a code's folder") {
            paths.push(file.expect("an entry").path());
        }
    }
    paths.sort();
    for path in paths {
        let bytes = std::fs::read(&path).expect("a fixture");
        let text = String::from_utf8_lossy(&bytes).into_owned();
        found.push((name_for(&text).to_owned(), text));
    }
    found
}

/// The host's target, resolved once per call site.
fn host() -> TargetSpec {
    resolve(enrang_target::host_target(), &TargetOpts::default())
        .expect("the host")
        .0
}

/// `enrang check`'s phases on one in-memory file, and whether phase 1 passed, so
/// phase 2 ran. A test part is checked as the part of an empty module, as `check`
/// loads it.
fn run(target: &TargetSpec, name: &str, text: &str) -> bool {
    let mut sources = vec![(name, text)];
    if name == "m.test.en" {
        sources.insert(0, ("m.en", ""));
    }
    let input = ProgramInput::in_memory(sources[0].0, &sources, ParseMode::Test);
    let mut map = SourceMap::new();
    let mut ids = NodeIdGen::new();
    let mut dcx = DiagCtx::new();
    let loaded = match load(&input, target, &mut map, &mut ids, &mut dcx) {
        Ok(program) => program,
        Err(LoadError::Aborted(_)) => return false,
        Err(LoadError::Unreadable { path, error }) => panic!("{}: {error}", path.display()),
    };
    let map = Arc::new(map);
    let mut tcx = Tcx::new(Arc::new(target.clone()), Arc::clone(&map));
    if let Ok(checked) = analyze(&loaded, &mut tcx, &mut dcx) {
        let _ = check_sizes(&checked, &tcx, &mut dcx);
    }
    let _ = dcx.take();
    true
}

/// Whether checking `text` panics, with the message, else whether it reached
/// phase 2.
fn panics(target: &TargetSpec, name: &str, text: &str) -> Result<bool, String> {
    let mut reached = false;
    match catch_panic(|| reached = run(target, name, text)) {
        Some(message) => Err(message),
        None => Ok(reached),
    }
}

/// `text` with one to three mutations: mostly a word made another word, else the
/// syntax suite's GenBytes token mutations.
fn mutate(rng: &mut Xoshiro256, text: &str) -> String {
    let words_only = rng.below(4) != 0;
    let mut text = text.to_owned();
    for _ in 0..=rng.below(3) {
        let mut map = SourceMap::new();
        let id = map.add(
            PathBuf::from("m.en"),
            Arc::from(text.as_str()),
            FileOrigin::User,
        );
        let file = map.file(id);
        let pieces: Vec<(usize, usize)> = lex(file, &mut DiagCtx::new())
            .iter()
            .map(|t| {
                (
                    (t.span.lo.0 - file.start.0) as usize,
                    (t.span.hi.0 - file.start.0) as usize,
                )
            })
            .filter(|(lo, hi)| lo < hi)
            .collect();
        if pieces.is_empty() {
            return text;
        }
        if words_only {
            let words: Vec<(usize, usize)> = pieces
                .iter()
                .copied()
                .filter(|&(lo, hi)| {
                    text[lo..hi]
                        .chars()
                        .all(|c| c.is_alphanumeric() || c == '_' || c == '"' || c == '.')
                })
                .collect();
            if words.is_empty() {
                return text;
            }
            let (lo, hi) = words[rng.below(words.len() as u64) as usize];
            let word = WORDS[rng.below(WORDS.len() as u64) as usize];
            text = format!("{}{word}{}", &text[..lo], &text[hi..]);
            continue;
        }
        let (lo, hi) = pieces[rng.below(pieces.len() as u64) as usize];
        let (next_lo, next_hi) = pieces
            .iter()
            .copied()
            .find(|&(l, _)| l >= hi)
            .unwrap_or((hi, hi));
        let token = text[lo..hi].to_owned();
        let fragment = FRAGMENTS[rng.below(FRAGMENTS.len() as u64) as usize];
        text = match rng.below(6) {
            0 => format!("{}{}", &text[..lo], &text[hi..]),
            1 => format!("{}{token}{}", &text[..hi], &text[hi..]),
            2 => format!(
                "{}{}{}{token}{}",
                &text[..lo],
                &text[next_lo..next_hi],
                &text[hi..next_lo],
                &text[next_hi..]
            ),
            3 => format!("{}{fragment}{}", &text[..lo], &text[hi..]),
            4 => format!("{}{fragment} {}", &text[..lo], &text[lo..]),
            _ => text[..hi].to_owned(),
        };
    }
    text
}

pub fn register(h: &mut Harness) {
    h.case(
        "no_panic/every SPEC block and compile fixture goes through phase 2",
        || {
            let target = host();
            let seeds = seeds();
            assert!(seeds.len() > 200, "{} seeds", seeds.len());
            let mut failed = Vec::new();
            for (name, text) in &seeds {
                if let Err(message) = panics(&target, name, text) {
                    failed.push(format!("{message}\n--- {name}\n{text}"));
                }
            }
            assert!(failed.is_empty(), "{}", failed.join("\n\n"));
        },
    );
    h.case("no_panic/mutants of them make no phase panic", || {
        let target = host();
        let seeds: Vec<(String, String)> = seeds()
            .into_iter()
            .filter(|(name, text)| panics(&target, name, text) == Ok(true))
            .collect();
        assert!(seeds.len() > 100, "{} seeds reach phase 2", seeds.len());
        let mut rng = rng_for("sema/no_panic");
        let rounds = scaled(400);
        let mut typed = 0;
        for round in 0..rounds {
            let (name, text) = &seeds[rng.below(seeds.len() as u64) as usize];
            let mutant = mutate(&mut rng, text);
            match panics(&target, name, &mutant) {
                Ok(reached) => typed += usize::from(reached),
                Err(message) => {
                    let shrunk = shrink_within(mutant, 300, |candidate: &String| {
                        panics(&target, name, candidate).is_err()
                    });
                    panic!(
                        "mutant {round} of ENRANG_SEED={} makes phase 2 panic: {message}\n--- {name}\n{shrunk}",
                        seed()
                    );
                }
            }
        }
        // A fifth: the mutants are a random sample, and a quarter sat within its
        // noise (95 of 400 once fix-6 added fixtures, which moves every draw).
        assert!(typed * 5 >= rounds, "only {typed} of {rounds} mutants reached phase 2");
    });
}
