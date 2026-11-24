//! Generated inputs for the printer, seeded by `ENRANG_SEED` and sized by
//! `ENRANG_SCALE` (TESTING 14): the canonical style does not depend on the spaces
//! the author typed, a tree with no source prints back to itself, no output line
//! passes 100 columns without a literal or a comment to excuse it, and a tree printed
//! against a source it did not come from never panics.

use enrang_diag::DiagCtx;
use enrang_syntax::ast::*;
use enrang_syntax::{TokenKind, erase, lex, print_file};
use enrang_testkit::{Harness, Rng, Xoshiro256, catch_panic, line_diff, rng_for, scaled, seed};

use crate::fmt::{fmt_as, fmt_bare_as, four_tests_as, parse_as};
use crate::parser::spec_sources;
use crate::support::source;

fn pick<'a, T>(rng: &mut Xoshiro256, items: &'a [T]) -> &'a T {
    &items[rng.below(items.len() as u64) as usize]
}

/// `text` with the white space between its tokens changed where SPEC 12.5 says the
/// layout does not depend on it: each run of spaces within a line becomes 1 to 3
/// spaces, and each run holding line breaks keeps them but gets a new indentation.
/// Comments, empty gaps and the inside of a template, holes included, stay.
fn perturb(rng: &mut Xoshiro256, text: &str) -> String {
    let file = source("p.en", text);
    let tokens = lex(&file, &mut DiagCtx::new());
    let at = |pos: enrang_base::BytePos| (pos.0 - file.start.0) as usize;
    let mut out = String::with_capacity(text.len() * 2);
    let mut gap_lo = 0;
    let mut holes = 0usize;
    for token in &tokens {
        let gap = &text[gap_lo..at(token.span.lo)];
        if holes > 0 {
            out.push_str(gap);
        } else {
            perturb_gap(rng, gap, &mut out);
        }
        out.push_str(&text[at(token.span.lo)..at(token.span.hi)]);
        gap_lo = at(token.span.hi);
        match token.kind {
            TokenKind::TemplateHead(_) => holes += 1,
            TokenKind::TemplateTail(_) => holes = holes.saturating_sub(1),
            _ => {}
        }
    }
    out.push_str(&text[gap_lo..]);
    out
}

fn perturb_gap(rng: &mut Xoshiro256, gap: &str, out: &mut String) {
    let mut rest = gap;
    while !rest.is_empty() {
        let len = if rest.starts_with("//") {
            rest.find('\n').unwrap_or(rest.len())
        } else if let Some(body) = rest.strip_prefix("/*") {
            body.find("*/").map_or(rest.len(), |len| len + 4)
        } else {
            let len = rest
                .find(|c: char| !c.is_whitespace())
                .unwrap_or(rest.len());
            let run = &rest[..len];
            let breaks = run.matches('\n').count();
            if breaks == 0 {
                let spaces = 1 + rng.below(3) as usize;
                out.extend(std::iter::repeat_n(' ', spaces));
            } else {
                out.extend(std::iter::repeat_n('\n', breaks));
                let indent = rng.below(7) as usize;
                out.extend(std::iter::repeat_n(' ', indent));
            }
            rest = &rest[len..];
            continue;
        };
        out.push_str(&rest[..len]);
        rest = &rest[len..];
    }
}

/// `text` with comments added between its tokens where they change no token: a
/// block comment at either end of a gap that already holds white space, so no
/// token's `space_before` changes (never right after a `/`, which would make it a
/// line comment), and a line comment before a line break, so it
/// ends where a line already did. Each comment's text is unique, so the comment
/// test of TESTING 17 sees any reordering.
fn add_comments(rng: &mut Xoshiro256, text: &str) -> String {
    let file = source("c.en", text);
    let tokens = lex(&file, &mut DiagCtx::new());
    let at = |pos: enrang_base::BytePos| (pos.0 - file.start.0) as usize;
    let mut out = String::with_capacity(text.len() * 2);
    let mut gap_lo = 0;
    let mut count = 0;
    for token in &tokens {
        let gap = &text[gap_lo..at(token.span.lo)];
        if gap.is_empty() || gap_lo == 0 || rng.below(4) != 0 {
            out.push_str(gap);
        } else {
            count += 1;
            match (rng.below(3), gap.find('\n')) {
                (0, Some(newline)) => {
                    out.push_str(&gap[..newline]);
                    out.push_str(&format!(" // c{count}"));
                    out.push_str(&gap[newline..]);
                }
                (1, _) if !out.ends_with('/') => {
                    out.push_str(&format!("/* c{count} */"));
                    out.push_str(gap);
                }
                _ => {
                    out.push_str(gap);
                    out.push_str(&format!("/* c{count} */"));
                }
            }
        }
        out.push_str(&text[at(token.span.lo)..at(token.span.hi)]);
        gap_lo = at(token.span.hi);
    }
    out.push_str(&text[gap_lo..]);
    out
}

/// The blocks the generators start from: every SPEC block but those kept as written
/// by an opt-out comment, each with its label and the file name it parses under.
/// Every input made from a block keeps that name: worked out again from a
/// perturbed text, which may indent a `describe(` line, it would name a test file
/// as a module (EN1112).
fn blocks() -> Vec<(String, String, String)> {
    spec_sources()
        .iter()
        .filter(|spec| !spec.text.contains("enrang-fmt-ignore"))
        .map(|spec| (spec.label.clone(), spec.name.clone(), spec.text.clone()))
        .collect()
}

/// The erased tree of `text`, file `name`, with every import in one group, sorted
/// as the Imports rule sorts a group: a tree with no source has no blank lines and
/// no comments.
fn sorted_as_one_group(name: &str, text: &str) -> File {
    let (_, tree) = parse_as(name, text);
    let mut tree = erase(&tree);
    tree.imports
        .sort_by(|a, b| a.path.value.as_str().cmp(b.path.value.as_str()));
    for import in &mut tree.imports {
        if let ImportKind::Named(names) = &mut import.kind {
            names.sort_by(|a, b| a.name.name.as_str().cmp(b.name.name.as_str()));
        }
    }
    tree
}

/// SPEC 12.5 Width: a line may pass 100 columns only when it holds a string or
/// template literal, which is never broken, or a comment, which does not count.
fn over_width(text: &str) -> Option<&str> {
    text.lines().find(|line| {
        let excused = ["\"", "'", "`", "//", "/*"]
            .iter()
            .any(|mark| line.contains(mark));
        line.chars().count() > 100 && !excused
    })
}

/// A random edit of `text` that keeps it valid UTF-8: a character deleted, a slice
/// duplicated, or a character of SPEC 2's punctuation inserted.
fn mutate(rng: &mut Xoshiro256, text: &str) -> String {
    let chars: Vec<char> = text.chars().collect();
    if chars.is_empty() {
        return "{".into();
    }
    let at = rng.below(chars.len() as u64) as usize;
    let mut out: Vec<char> = chars.clone();
    match rng.below(3) {
        0 => {
            out.remove(at);
        }
        1 => {
            let end = (at + 1 + rng.below(16) as usize).min(chars.len());
            let slice: Vec<char> = chars[at..end].to_vec();
            out.splice(at..at, slice);
        }
        _ => {
            let c = *pick(
                rng,
                &['{', '}', '(', ')', '"', '\'', '`', '/', '*', '\n', ' ', '<'],
            );
            out.insert(at, c);
        }
    }
    out.into_iter().collect()
}

pub fn register(h: &mut Harness) {
    h.case(
        "printer properties/the layout does not depend on the spaces typed",
        || {
            let blocks = blocks();
            let mut rng = rng_for("printer-spaces");
            let mut changed = 0;
            for _ in 0..scaled(200) {
                let (heading, name, block) = pick(&mut rng, &blocks);
                let input = perturb(&mut rng, block);
                changed += usize::from(input != *block);
                let out = fmt_as(name, &input);
                if out != *block {
                    return Err(format!(
                        "ENRANG_SEED={:#x}, block under {heading:?}, input:\n{input}\n\
                     printed (- block, + printed):\n{}",
                        seed(),
                        line_diff(block, &out)
                    ));
                }
            }
            assert!(
                changed > scaled(200) / 2,
                "only {changed} inputs were perturbed"
            );
            Ok(())
        },
    );
    h.case(
        "printer properties/added comments keep their text, order and tree",
        || {
            let blocks = blocks();
            let mut rng = rng_for("printer-comments");
            for _ in 0..scaled(200) {
                let (heading, name, block) = pick(&mut rng, &blocks);
                let input = add_comments(&mut rng, block);
                let outcome = catch_panic(|| four_tests_as(name, &input, None))
                    .map_or_else(|| Ok(()), |panic| Err(format!("panicked: {panic}")));
                if let Err(why) = outcome.and_then(|()| four_tests_as(name, &input, None)) {
                    return Err(format!(
                        "ENRANG_SEED={:#x}, block under {heading:?}, input:\n{input}\n{why}",
                        seed()
                    ));
                }
            }
            Ok(())
        },
    );
    h.case(
        "printer properties/a tree with no source prints back to itself",
        || {
            for (heading, name, block) in blocks() {
                let out = fmt_bare_as(&name, &block);
                let (_, tree) = parse_as(&name, &out);
                let want = sorted_as_one_group(&name, &block);
                if erase(&tree) != want {
                    return Err(format!(
                        "block under {heading:?}: the tree changed:\n{}",
                        line_diff(&format!("{want:#?}"), &format!("{:#?}", erase(&tree)))
                    ));
                }
                let again = fmt_as(&name, &out);
                if again != out {
                    return Err(format!(
                        "block under {heading:?}: printing the output with its source \
                     changes it:\n{}",
                        line_diff(&out, &again)
                    ));
                }
            }
            Ok(())
        },
    );
    h.case(
        "printer properties/no line passes 100 columns unexcused",
        || {
            let blocks = blocks();
            for (heading, name, block) in &blocks {
                for text in [fmt_as(name, block), fmt_bare_as(name, block)] {
                    if let Some(line) = over_width(&text) {
                        return Err(format!("block under {heading:?}: {line}"));
                    }
                }
            }
            let mut rng = rng_for("printer-width");
            for _ in 0..scaled(50) {
                let (heading, name, block) = pick(&mut rng, &blocks);
                let out = fmt_as(name, &perturb(&mut rng, block));
                if let Some(line) = over_width(&out) {
                    return Err(format!(
                        "ENRANG_SEED={:#x}, block under {heading:?}: {line}",
                        seed()
                    ));
                }
            }
            Ok(())
        },
    );
    h.case(
        "printer properties/a tree printed against another source never panics",
        || {
            let blocks = blocks();
            let trees: Vec<File> = blocks
                .iter()
                .map(|(_, name, block)| parse_as(name, block).1)
                .collect();
            let mut rng = rng_for("printer-mismatch");
            for _ in 0..scaled(300) {
                let tree = pick(&mut rng, &trees);
                let (_, _, other) = pick(&mut rng, &blocks);
                let mut text = other.clone();
                for _ in 0..rng.below(4) {
                    text = mutate(&mut rng, &text);
                }
                let file = source("m.en", &text);
                if let Some(panic) = catch_panic(|| print_file(&file, tree)) {
                    return Err(format!(
                        "ENRANG_SEED={:#x}: panicked: {panic}\nsource:\n{text}",
                        seed()
                    ));
                }
            }
            Ok(())
        },
    );
}
