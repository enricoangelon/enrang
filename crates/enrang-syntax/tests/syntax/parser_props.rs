//! The parser on generated input (TESTING 11 and 14), seeded by `ENRANG_SEED` and
//! sized by `ENRANG_SCALE`: random token soups, and mutations of every `ts` block of
//! SPEC at token boundaries. On every input the parser returns, without a panic and
//! the same way twice; it reports only phase 1 codes, each inside the file; and its
//! tree spans the file, with unique node ids and every span inside the file. Input
//! nested past the parser's limit is an error, not a stack overflow.

use std::collections::BTreeSet;

use enrang_base::Span;
use enrang_diag::{Code, DiagCtx, Phase};
use enrang_syntax::ast::NodeId;
use enrang_syntax::{Keyword, MutVisitor, Punct, Reserved, Walk, erase, lex};
use enrang_testkit::{
    Harness, Rng, Xoshiro256, catch_panic, fenced_blocks, rng_for, scaled, seed, shrink,
};

use crate::parser::Parsed;
use crate::support::{doc, source};

fn pick<'a, T>(rng: &mut Xoshiro256, items: &'a [T]) -> &'a T {
    &items[rng.below(items.len() as u64) as usize]
}

/// Words and literals a soup draws from, besides every punctuator, keyword and
/// reserved word.
const FRAGMENTS: &[&str] = &[
    "a",
    "b",
    "x",
    "T",
    "Box",
    "i64",
    "u8",
    "Ok",
    "Err",
    "console",
    "log",
    "sizeOf",
    "offsetOf",
    "describe",
    "test",
    "expect",
    "compileFails",
    "raw",
    "extends",
    "from",
    "of",
    "not",
    "in",
    "out",
    "clobbers",
    "assert",
    "extend",
    "where",
    "toMatchPattern",
    "1",
    "0x1F",
    "1.5",
    "1e3",
    "\"s\"",
    "'t'",
    "`t`",
    "`a${",
    "}b`",
    "`${x}`",
    "raw`r`",
    "'a",
    "// c\n",
    "/* c */",
    "=>",
    "...",
    "..",
    "?.",
    "??",
    "<",
    ">",
    ">>",
    ">=",
    "(",
    ")",
    "{",
    "}",
    "[",
    "]",
];

const SEPARATORS: &[&str] = &["", " ", " ", " ", "\n"];

/// Every fragment a soup draws from.
pub fn soup_words() -> Vec<&'static str> {
    let mut words = FRAGMENTS.to_vec();
    words.extend(Punct::ALL.iter().map(|p| p.as_str()));
    words.extend(Keyword::ALL.iter().map(|k| k.as_str()));
    words.extend(Reserved::ALL.iter().map(|r| r.as_str()));
    words
}

fn soup(rng: &mut Xoshiro256, words: &[&'static str]) -> String {
    let mut text = String::new();
    for _ in 0..rng.below(60) {
        text.push_str(pick(rng, words));
        text.push_str(pick(rng, SEPARATORS));
    }
    text
}

/// The `ts` blocks of SPEC, each with the name it parses under.
fn spec_blocks() -> Vec<(String, String)> {
    fenced_blocks(doc("SPEC.md"))
        .unwrap_or_else(|errors| panic!("{errors}"))
        .into_iter()
        .filter(|block| block.lang == "ts")
        .map(|block| {
            let test =
                block.contents.contains("describe(") || block.contents.contains("compileOk(");
            let name = if test { "m.test.en" } else { "m.en" };
            (name.to_owned(), block.contents)
        })
        .collect()
}

/// `text` with one to three token-level mutations: a token deleted, doubled,
/// swapped with the next, replaced or preceded by a fragment, or the file cut after
/// a token.
pub fn mutate(rng: &mut Xoshiro256, text: &str, words: &[&'static str]) -> String {
    let mut text = text.to_owned();
    for _ in 0..=rng.below(3) {
        let file = source("m.en", &text);
        let tokens = lex(&file, &mut DiagCtx::new());
        let pieces: Vec<(usize, usize)> = tokens
            .iter()
            .map(|t| {
                (
                    (t.span.lo.0 - file.start.0) as usize,
                    (t.span.hi.0 - file.start.0) as usize,
                )
            })
            .collect();
        let (lo, hi) = *pick(rng, &pieces);
        let (next_lo, next_hi) = pieces
            .iter()
            .copied()
            .find(|&(l, _)| l >= hi)
            .unwrap_or((hi, hi));
        let token = text[lo..hi].to_owned();
        let fragment = *pick(rng, words);
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

/// Parses `text` twice and checks every invariant of the result.
fn check(name: &str, text: &str) -> Result<(), String> {
    let mut first = None;
    if let Some(message) = catch_panic(|| first = Some(Parsed::new(name, text))) {
        return Err(format!("the parser panicked: {message}"));
    }
    let parsed = first.expect("set when the parser returns");
    let again = Parsed::new(name, text);
    if again.tree != parsed.tree || again.diags != parsed.diags {
        return Err("two runs differ".to_owned());
    }
    let (start, end) = (parsed.file.start, parsed.file.end());
    for diag in &parsed.diags {
        let span = diag.primary.span;
        if span.lo < start || span.hi > end || span.lo > span.hi {
            return Err(format!("{} has a span outside the file", diag.code));
        }
        if diag.code.phase() != Phase::Syntax || diag.code == Code::EN0001 {
            return Err(format!("the parser reported {}", diag.code));
        }
    }
    check_tree(&parsed)
}

/// The tree spans its file, its node ids are unique, and every span lies inside
/// the file on character boundaries.
pub fn check_tree(parsed: &Parsed) -> Result<(), String> {
    #[derive(Default)]
    struct Collect {
        ids: Vec<NodeId>,
        spans: Vec<Span>,
    }

    impl MutVisitor for Collect {
        fn visit_span(&mut self, span: &mut Span) {
            self.spans.push(*span);
        }

        fn visit_id(&mut self, id: &mut NodeId) {
            self.ids.push(*id);
        }
    }

    let (start, end) = (parsed.file.start, parsed.file.end());
    if parsed.tree.span != (Span { lo: start, hi: end }) {
        return Err("the tree does not span its file".to_owned());
    }
    let mut tree = parsed.tree.clone();
    let mut collect = Collect::default();
    tree.walk(&mut collect);
    let unique: BTreeSet<NodeId> = collect.ids.iter().copied().collect();
    if unique.len() != collect.ids.len() {
        return Err("two nodes share an id".to_owned());
    }
    for span in collect.spans {
        let inside = span.lo >= start && span.hi <= end && span.lo <= span.hi;
        let text = &parsed.file.text;
        let lo = (span.lo.0 - start.0.min(span.lo.0)) as usize;
        let hi = (span.hi.0 - start.0.min(span.hi.0)) as usize;
        if !inside || !text.is_char_boundary(lo) || !text.is_char_boundary(hi) {
            return Err(format!("a node spans {span:?}, outside {start:?}..{end:?}"));
        }
    }
    Ok(())
}

/// Text nested `depth` times by `open` and `close` around `core`.
fn nested(open: &str, core: &str, close: &str, depth: usize) -> String {
    format!("{}{core}{}", open.repeat(depth), close.repeat(depth))
}

pub fn register(h: &mut Harness) {
    h.case("parser properties/token soups", || {
        let mut rng = rng_for("parser-soups");
        let words = soup_words();
        for _ in 0..scaled(3_000) {
            let text = soup(&mut rng, &words);
            if check("soup.en", &text).is_err() {
                let small = shrink(text, |t| check("soup.en", t).is_err());
                let why = check("soup.en", &small).expect_err("still fails");
                return Err(format!("ENRANG_SEED={:#x}: {small:?}: {why}", seed()));
            }
        }
        Ok(())
    });
    h.case("parser properties/mutated SPEC blocks", || {
        let mut rng = rng_for("parser-mutations");
        let words = soup_words();
        let blocks = spec_blocks();
        assert!(blocks.len() > 50, "{} blocks", blocks.len());
        for _ in 0..scaled(2_000) {
            let (name, text) = pick(&mut rng, &blocks);
            let text = mutate(&mut rng, text, &words);
            if check(name, &text).is_err() {
                let small = shrink(text, |t| check(name, t).is_err());
                let why = check(name, &small).expect_err("still fails");
                return Err(format!("ENRANG_SEED={:#x}: {small:?}: {why}", seed()));
            }
        }
        Ok(())
    });
    h.case("parser properties/SPEC blocks keep every invariant", || {
        for (name, text) in spec_blocks() {
            check(&name, &text).map_err(|why| format!("{text}\n{why}"))?;
        }
        Ok::<(), String>(())
    });
    let deep: &[(&str, &str, &str, &str)] = &[
        ("parens", "(", "a", ")"),
        ("brackets", "[", "a", "]"),
        ("blocks", "{", "", "}"),
        ("prefix operators", "!", "a", ""),
        ("prefix minus", "- ", "a", ""),
        ("coalescing", "a ?? ", "a", ""),
        ("assignments", "a = ", "a", ""),
        ("ternaries", "a ? b : ", "c", ""),
        ("arrows", "x => ", "x", ""),
        ("sums", "a + ", "a", ""),
        ("casts", "", "a", " as T"),
        ("member chains", "", "a", ".b"),
        ("calls", "", "f", "()"),
        ("nested types", "let x: Box<", "T", ">"),
        ("reference types", "let x: &", "T", ""),
        ("array types", "let x: T", "", "[]"),
        ("tuple patterns", "const ", "a", ""),
        ("else ifs", "if (a) {} else ", "{}", ""),
        ("templates", "`${", "a", "}`"),
        ("arrow parameters", "(a) => (", "a", ")"),
    ];
    for &(label, open, core, close) in deep {
        h.case(
            format!("parser properties/deep nesting is an error, not a crash/{label}"),
            move || {
                let text = nested(open, core, close, 20_000);
                check("deep.en", &text)?;
                let parsed = Parsed::new("deep.en", &text);
                if !parsed.diags.iter().any(|diag| diag.code == Code::EN0100) {
                    return Err("no EN0100 for nesting 20000 deep".to_owned());
                }
                Ok::<(), String>(())
            },
        );
    }
    // A failed speculation is parsed again the other way, so without its memo
    // each level of these would double the work: sixty levels would not finish.
    let guesses: &[(&str, String, bool)] = &[
        (
            "an annotated arrow in a ternary",
            format!("{}z;\n", "a ? (x): T => ".repeat(60)),
            true,
        ),
        (
            "type arguments after a path",
            format!("{}0{};\n", "x<T[".repeat(60), "]>".repeat(60)),
            false,
        ),
        (
            "type arguments after `as`",
            format!("y = {}0{} z;\n", "x as T<U[".repeat(60), "]>".repeat(60)),
            false,
        ),
        (
            "an annotated arrow's head",
            format!("{}0{};\n", "(a: T[".repeat(60), "]): R".repeat(60)),
            false,
        ),
        ("unclosed parentheses", "(a;\n".repeat(5_000), false),
    ];
    for (label, text, clean) in guesses.iter().cloned() {
        h.case(
            format!("parser properties/a failed guess is not tried twice/{label}"),
            move || {
                check("guess.en", &text)?;
                let parsed = Parsed::new("guess.en", &text);
                if clean && !parsed.diags.is_empty() {
                    return Err(parsed.listing());
                }
                Ok::<(), String>(())
            },
        );
    }
    // Each `(` of these opens an arrow head's guess, which looks for its `)`; with
    // the closers of EN0102 all at the end of the one line, a search per `(` made
    // the parse quadratic: minutes in a debug build, where this takes a second.
    let long_lines: Vec<(&str, String)> = vec![
        (
            "a line of unclosed `(`",
            format!("f({});\n", "(x: T, ".repeat(40_000)),
        ),
        ("unclosed `(` before `;`", "(a;\n".repeat(40_000)),
    ];
    for (label, text) in long_lines {
        h.case(
            format!("parser properties/a long input parses in time/{label}"),
            move || {
                let start = std::time::Instant::now();
                check("long.en", &text)?;
                let took = start.elapsed();
                if took > std::time::Duration::from_secs(20) {
                    return Err(format!("the parse took {took:?}"));
                }
                Ok::<(), String>(())
            },
        );
    }
    h.case("parser properties/long flat chains parse", || {
        for text in [
            format!("const s = {}\"a\";\n", "\"a\" + ".repeat(1_000)),
            format!("const s = x{};\n", ".f()".repeat(500)),
            format!("const s = {}a;\n", "a as T + ".repeat(300)),
            format!(
                "public function f(): void {{\n  if (x) {{\n    g({}a);\n  }}\n}}\n",
                "a + ".repeat(1_000)
            ),
        ] {
            let parsed = Parsed::new("chain.en", &text);
            if !parsed.diags.is_empty() {
                return Err(format!("{}\n{}", &text[..80], parsed.listing()));
            }
            check("chain.en", &text)?;
        }
        Ok::<(), String>(())
    });
    h.case("parser properties/a chain past the limit says so", || {
        let text = format!("const s = {}a;\n", "a + ".repeat(2_000));
        let parsed = Parsed::new("chain.en", &text);
        let messages: Vec<&str> = parsed.diags.iter().map(|d| d.message.as_str()).collect();
        assert_eq!(
            messages,
            ["this expression has too many operators in a row"]
        );
    });
    h.case("parser properties/ordinary nesting parses", || {
        for text in [
            format!("{};\n", nested("(", "a", ")", 100)),
            format!("{};\n", nested("[", "a", "]", 100)),
            format!("{}\n", nested("{", "", "}", 100)),
            format!("{};\n", nested("!", "a", "", 100)),
            format!("{};\n", nested("- ", "a", "", 100)),
            format!("{}a;\n", "a + ".repeat(100)),
            format!("let x: {} = y;\n", nested("Box<", "T", ">", 60)),
        ] {
            let parsed = Parsed::new("nest.en", &text);
            if !parsed.diags.is_empty() {
                return Err(format!("{text}\n{}", parsed.listing()));
            }
            check("nest.en", &text)?;
        }
        Ok::<(), String>(())
    });
    h.case("parser properties/erase blanks a parsed tree", || {
        let parsed = Parsed::new("e.en", "const x = f(1, [a, ...b]);\n");
        let again = Parsed::new("e.en", "const  x = f( 1 , [ a , ...b ] ) ;\n");
        assert_ne!(parsed.tree, again.tree);
        assert_eq!(erase(&parsed.tree), erase(&again.tree));
    });
}
