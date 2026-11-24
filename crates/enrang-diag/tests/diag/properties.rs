//! Generated inputs, seeded by `ENRANG_SEED` and sized by `ENRANG_SCALE`.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use enrang_base::{BytePos, Span};
use enrang_diag::{
    Code, DiagCtx, Diagnostic, Edit, FixConflict, Help, apply_fixes, did_you_mean,
    did_you_mean_ordered,
};
use enrang_testkit::{Harness, Rng, Xoshiro256, rng_for, scaled};

use crate::json_value::parse;
use crate::support::{Src, strip_ansi};

fn pick<'a, T>(rng: &mut Xoshiro256, items: &'a [T]) -> &'a T {
    &items[rng.below(items.len() as u64) as usize]
}

const FRAGMENTS: [&str; 17] = [
    "\u{FEFF}",
    "a",
    "bc",
    " ",
    "  ",
    "\t",
    "é",
    "日本",
    "🦀",
    "\n",
    "\n",
    "\r\n",
    "\n\n",
    "let x = 1;",
    "{",
    "}",
    "\u{301}",
];

fn random_text(rng: &mut Xoshiro256) -> String {
    let mut text = String::new();
    for _ in 0..rng.below(24) {
        text.push_str(pick(rng, &FRAGMENTS));
    }
    text
}

/// Every offset of `text` that is a scalar boundary.
fn boundaries(text: &str) -> Vec<usize> {
    text.char_indices()
        .map(|(at, _)| at)
        .chain(std::iter::once(text.len()))
        .collect()
}

/// Mostly proper spans, then the odd ones a buggy phase could produce: positions
/// inside a scalar, inverted spans and ends past the file must still render.
fn random_span(rng: &mut Xoshiro256, src: &Src, file: usize) -> Span {
    let file = src.f(file);
    if rng.below(8) == 0 {
        let len = file.text.len() as u64 + 1;
        let (lo, hi) = (rng.below(len) as usize, rng.below(len + 8) as usize);
        return file.span(lo, hi);
    }
    let bounds = boundaries(&file.text);
    let a = *pick(rng, &bounds);
    let b = if rng.below(4) == 0 {
        a
    } else {
        *pick(rng, &bounds)
    };
    file.span(a.min(b), a.max(b))
}

/// The codes a generated diagnostic can have: one of each severity, and spanless.
const CODES: [Code; 5] = [
    Code::EN0301,
    Code::EN0430,
    Code::T0001,
    Code::EN1301,
    Code::EN0601,
];

fn random_edit(rng: &mut Xoshiro256, src: &Src, file: usize) -> Edit {
    let span = random_span(rng, src, file);
    let replacement = random_text(rng);
    match rng.below(8) {
        0 => Edit::command(replacement),
        1 => Edit::insert(span.lo, replacement),
        _ => Edit::replace(span, replacement),
    }
}

fn random_diagnostic(rng: &mut Xoshiro256, src: &Src) -> Diagnostic {
    let code = *pick(rng, &CODES);
    let files = src.files.len() as u64;
    let span = if rng.below(10) == 0 {
        Span::DUMMY
    } else {
        let file = rng.below(files) as usize;
        random_span(rng, src, file)
    };
    let mut diag = Diagnostic::new(code, "message", span, "label");
    for _ in 0..rng.below(4) {
        let file = rng.below(files) as usize;
        diag = diag.with_secondary(random_span(rng, src, file), "secondary");
    }
    for _ in 0..rng.below(3) {
        diag = diag.note("one\ntwo");
    }
    for _ in 0..rng.below(4) {
        let edits = (0..rng.below(4))
            .map(|_| {
                let file = rng.below(files) as usize;
                random_edit(rng, src, file)
            })
            .collect();
        diag = diag.with_help(Help::suggest("help", edits));
    }
    diag
}

/// Layout that holds for every rendering: whatever the input, each snippet line has
/// its gutter at the one column the digits of its diagnostic give.
fn check_layout(rendered: &str) {
    let mut bar: Option<usize> = None;
    for line in rendered.lines() {
        if line.is_empty() {
            bar = None;
            continue;
        }
        let free = line.starts_with("error")
            || line.starts_with("warning[")
            || line.starts_with("fail[")
            || line.starts_with("help: ")
            || line == "...";
        if free {
            continue;
        }
        if let Some(rest) = line.trim_start().strip_prefix("--> ") {
            let width = line.len() - line.trim_start().len();
            assert!(rest.contains(':'), "{line:?}");
            bar = Some(width + 1);
            continue;
        }
        // The continuation of the note `one\ntwo` is indented further on purpose.
        if line.trim_start() == "two" {
            continue;
        }
        let column = line
            .chars()
            .position(|c| matches!(c, '|' | '+' | '~' | '='));
        let column = column.unwrap_or_else(|| panic!("no gutter in {line:?}\n{rendered}"));
        if let Some(bar) = bar {
            assert_eq!(column, bar, "{line:?} in\n{rendered}");
        }
        bar = Some(column);
        let before = &line[..column];
        assert!(
            before.ends_with(' ') && before.trim().chars().all(|c| c.is_ascii_digit()),
            "{line:?} in\n{rendered}"
        );
    }
}

fn random_renderings(h: &mut Harness) {
    h.case("properties/any diagnostic renders, consistently", || {
        let mut rng = rng_for("diag-render");
        for _ in 0..scaled(400) {
            let (a, b) = (random_text(&mut rng), random_text(&mut rng));
            let src = Src::files(&[("a.en", &a), ("b.en", &b)]);
            let diags: Vec<Diagnostic> = (0..rng.below(4))
                .map(|_| random_diagnostic(&mut rng, &src))
                .collect();
            let plain = src.render(&diags);
            assert_eq!(plain, src.render(&diags), "rendering is deterministic");
            assert_eq!(strip_ansi(&src.render_colored(&diags)), plain);
            check_layout(&plain);
            if !plain.is_empty() {
                assert!(
                    plain.ends_with('\n') && !plain.ends_with("\n\n"),
                    "{plain:?}"
                );
            }
            let json = src.json(&diags);
            assert_eq!(json.lines().count(), diags.len());
            for (line, diag) in json.lines().zip(&diags) {
                let object = parse(line).unwrap_or_else(|error| panic!("{error}: {line}"));
                assert_eq!(object.get("code").str(), diag.code.name());
                assert_eq!(object.get("helps").arr().len(), diag.helps.len());
            }
        }
    });
    h.case("properties/the location line agrees with the marks", || {
        let mut rng = rng_for("diag-location");
        for _ in 0..scaled(400) {
            let text = random_text(&mut rng);
            let src = Src::new("a.en", &text);
            let span = random_span(&mut rng, &src, 0);
            if span.is_dummy() {
                continue;
            }
            let rendered = src.one(Diagnostic::new(Code::EN0430, "m", span, "p"));
            let location = rendered.lines().nth(1).expect("a location line");
            let digits_col = location.rsplit(':').next().expect("a column");
            let col: usize = digits_col.parse().expect("a number");
            let line: usize = location
                .rsplit(':')
                .nth(1)
                .expect("a line")
                .parse()
                .expect("a number");
            let width = line.to_string().len();
            let source_line = rendered.lines().nth(3).expect("the source line");
            assert!(source_line.starts_with(&format!("{line} |")), "{rendered}");
            let marks = rendered.lines().nth(4).expect("the annotation line");
            let mark_at = marks.chars().position(|c| c == '^').expect("a mark");
            assert_eq!(mark_at, width + 3 + col - 1, "{rendered}");
        }
    });
}

/// A reference for `apply_fixes` on non-overlapping edits: back to front on bytes.
fn apply_from_the_back(text: &str, edits: &[(usize, usize, String)]) -> String {
    let mut sorted = edits.to_vec();
    sorted.sort_by_key(|edit| (edit.0, edit.1));
    let mut out = text.to_owned();
    for (lo, hi, replacement) in sorted.iter().rev() {
        out.replace_range(*lo..*hi, replacement);
    }
    out
}

fn random_fixes(h: &mut Harness) {
    h.case(
        "properties/non-overlapping edits apply as the reference does",
        || {
            let mut rng = rng_for("diag-fixes");
            for _ in 0..scaled(400) {
                let text = random_text(&mut rng);
                let src = Src::new("a.en", &text);
                let mut bounds = boundaries(&text);
                bounds.retain(|_| rng.below(3) != 0);
                // Pairs of consecutive boundaries cannot overlap.
                let mut raw = Vec::new();
                for pair in bounds.chunks(2) {
                    let (lo, hi) = (pair[0], *pair.last().expect("a chunk is not empty"));
                    raw.push((lo, hi, random_text(&mut rng)));
                }
                let mut edits: Vec<Edit> = raw
                    .iter()
                    .map(|(lo, hi, replacement)| {
                        Edit::replace(src.span(*lo, *hi), replacement.clone())
                    })
                    .collect();
                let expected = apply_from_the_back(&text, &raw);
                assert_eq!(apply_fixes(&text, src.base(), &edits), Ok(expected.clone()));
                for _ in 0..edits.len() {
                    let (a, b) = (rng.below(edits.len() as u64), rng.below(edits.len() as u64));
                    edits.swap(a as usize, b as usize);
                }
                assert_eq!(
                    apply_fixes(&text, src.base(), &edits),
                    Ok(expected),
                    "list order must not matter"
                );
            }
        },
    );
    h.case(
        "properties/a conflict is found exactly when spans overlap",
        || {
            let mut rng = rng_for("diag-conflicts");
            for _ in 0..scaled(600) {
                let text = "0123456789";
                let src = Src::new("a.en", text);
                let mut spans = Vec::new();
                for index in 0..rng.below(4) + 2 {
                    let a = rng.below(11) as usize;
                    let b = rng.below(11) as usize;
                    spans.push((a.min(b), a.max(b), format!("{index}")));
                }
                let conflicts = (0..spans.len()).any(|i| {
                    (i + 1..spans.len()).any(|j| {
                        let (a, b) = (&spans[i], &spans[j]);
                        let same_place = (a.0, a.1) == (b.0, b.1);
                        let overlap = a.0 < b.1 && b.0 < a.1;
                        same_place || overlap
                    })
                });
                let edits: Vec<Edit> = spans
                    .iter()
                    .map(|(lo, hi, text)| Edit::replace(src.span(*lo, *hi), text.clone()))
                    .collect();
                match apply_fixes(text, src.base(), &edits) {
                    Ok(_) => assert!(!conflicts, "{spans:?}"),
                    Err(FixConflict::Overlap { .. }) => assert!(conflicts, "{spans:?}"),
                    Err(other) => panic!("{other} for {spans:?}"),
                }
            }
        },
    );
}

/// The distance by its definition: the fewest of insert, delete, substitute and
/// swap-adjacent that turn `a` into `b`, found by breadth-first search.
fn distance_by_search(a: &str, b: &str, alphabet: &[char]) -> usize {
    let start: Vec<char> = a.chars().collect();
    let goal: Vec<char> = b.chars().collect();
    let longest = start.len().max(goal.len()) + 2;
    let mut seen: BTreeMap<Vec<char>, usize> = BTreeMap::from([(start.clone(), 0)]);
    let mut queue = VecDeque::from([start]);
    while let Some(word) = queue.pop_front() {
        let depth = seen[&word];
        if word == goal {
            return depth;
        }
        let mut next: Vec<Vec<char>> = Vec::new();
        for at in 0..=word.len() {
            if word.len() < longest {
                for &c in alphabet {
                    let mut grown = word.clone();
                    grown.insert(at, c);
                    next.push(grown);
                }
            }
            if at < word.len() {
                let mut shrunk = word.clone();
                shrunk.remove(at);
                next.push(shrunk);
                for &c in alphabet {
                    let mut changed = word.clone();
                    changed[at] = c;
                    next.push(changed);
                }
            }
            if at + 1 < word.len() {
                let mut swapped = word.clone();
                swapped.swap(at, at + 1);
                next.push(swapped);
            }
        }
        for candidate in next {
            if !seen.contains_key(&candidate) {
                seen.insert(candidate.clone(), depth + 1);
                queue.push_back(candidate);
            }
        }
    }
    unreachable!("every word reaches every other");
}

fn random_suggestions(h: &mut Harness) {
    h.case(
        "properties/did_you_mean agrees with the distance by definition",
        || {
            let mut rng = rng_for("diag-distance");
            let alphabet = ['a', 'b', 'c'];
            let word = |rng: &mut Xoshiro256| -> String {
                (0..rng.below(6)).map(|_| *pick(rng, &alphabet)).collect()
            };
            for _ in 0..scaled(150) {
                let (name, candidate) = (word(&mut rng), word(&mut rng));
                if name.is_empty() || candidate.is_empty() {
                    continue;
                }
                let distance = distance_by_search(&name, &candidate, &alphabet);
                let limit = (name.chars().count() / 3).max(1);
                let expected = (distance <= limit).then_some(candidate.as_str());
                assert_eq!(
                    did_you_mean(&name, &[candidate.as_str()]),
                    expected,
                    "{name} to {candidate} is {distance} with limit {limit}"
                );
            }
        },
    );
    h.case(
        "properties/did_you_mean does not depend on candidate order",
        || {
            let mut rng = rng_for("diag-order");
            let alphabet = ['a', 'b', 'c', 'd'];
            for _ in 0..scaled(300) {
                let word = |rng: &mut Xoshiro256| -> String {
                    (0..=rng.below(7)).map(|_| *pick(rng, &alphabet)).collect()
                };
                let name = word(&mut rng);
                let mut candidates: Vec<String> = (0..6).map(|_| word(&mut rng)).collect();
                let as_refs = |list: &[String]| -> Option<String> {
                    let refs: Vec<&str> = list.iter().map(String::as_str).collect();
                    did_you_mean(&name, &refs).map(str::to_owned)
                };
                let first = as_refs(&candidates);
                candidates.reverse();
                assert_eq!(as_refs(&candidates), first);
                candidates.rotate_left(2);
                assert_eq!(as_refs(&candidates), first);
            }
        },
    );
    h.case(
        "properties/did_you_mean_ordered finds as near a candidate, a tie going to the first",
        || {
            let mut rng = rng_for("diag-ordered");
            let alphabet = ['a', 'b', 'c'];
            for _ in 0..scaled(150) {
                let word = |rng: &mut Xoshiro256| -> String {
                    (0..=rng.below(5)).map(|_| *pick(rng, &alphabet)).collect()
                };
                let name = word(&mut rng);
                let candidates: Vec<String> = (0..4).map(|_| word(&mut rng)).collect();
                let refs: Vec<&str> = candidates.iter().map(String::as_str).collect();
                let ordered = did_you_mean_ordered(&name, &refs);
                let by_name = did_you_mean(&name, &refs);
                assert_eq!(ordered.is_some(), by_name.is_some(), "{name} {refs:?}");
                let (Some(ordered), Some(by_name)) = (ordered, by_name) else {
                    continue;
                };
                let far = |c: &str| distance_by_search(&name, c, &alphabet);
                assert_eq!(far(ordered), far(by_name), "{name} {refs:?}");
                let first = refs
                    .iter()
                    .find(|c| far(c) == far(by_name))
                    .expect("the nearest is a candidate");
                assert_eq!(ordered, *first, "{name} {refs:?}");
            }
        },
    );
    h.case(
        "properties/did_you_mean_ordered: a local listed first beats an item of one distance",
        || {
            assert_eq!(did_you_mean("todo", &["Todo", "todos"]), Some("Todo"));
            assert_eq!(
                did_you_mean_ordered("todo", &["todos", "Todo"]),
                Some("todos")
            );
            assert_eq!(
                did_you_mean_ordered("todo", &["Todo", "todos"]),
                Some("Todo")
            );
            assert_eq!(did_you_mean_ordered("todo", &["tod", "todos"]), Some("tod"));
            assert_eq!(did_you_mean_ordered("todo", &["xxxx"]), None);
        },
    );
}

fn random_contexts(h: &mut Harness) {
    h.case(
        "properties/any emission order gives one sorted, deduped result",
        || {
            let mut rng = rng_for("diag-ctx");
            for _ in 0..scaled(200) {
                let src = Src::files(&[("a.en", "abcdefgh\n"), ("b.en", "ijklmnop\n")]);
                let mut emitted: Vec<(Code, Span)> = Vec::new();
                for _ in 0..rng.below(30) {
                    let file = rng.below(2) as usize;
                    let lo = rng.below(8) as usize;
                    let hi = lo + rng.below(2) as usize;
                    let code = *pick(&mut rng, &[Code::EN0301, Code::EN0302, Code::EN0430]);
                    emitted.push((code, src.f(file).span(lo, hi)));
                }
                let mut dcx = DiagCtx::new();
                for &(code, span) in &emitted {
                    dcx.emit(Diagnostic::new(code, "m", span, ""));
                }
                let taken = dcx.take();
                let distinct: BTreeSet<(Code, Span)> = emitted.iter().copied().collect();
                assert_eq!(taken.len(), distinct.len());
                let keys: Vec<(BytePos, BytePos)> = taken
                    .iter()
                    .map(|d| (d.primary.span.lo, d.primary.span.hi))
                    .collect();
                let mut sorted = keys.clone();
                sorted.sort();
                assert_eq!(keys, sorted);
                let failed = emitted.iter().any(|&(code, _)| code != Code::EN0430);
                assert_eq!(dcx.has_errors(), failed);
            }
        },
    );
}

pub fn register(h: &mut Harness) {
    random_renderings(h);
    random_fixes(h);
    random_suggestions(h);
    random_contexts(h);
}
