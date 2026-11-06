//! A line diff readable in test output.
//!
//! The format is a slimmer unified diff: `-` lines are expected, `+` lines are
//! actual, and a hunk header gives the line each side starts at. Bytes that
//! would look identical on a terminal are spelled out, so a diff can never show
//! two lines that appear equal.

use std::fmt::Write;

/// Unchanged lines shown on each side of a change.
const CONTEXT: usize = 3;

/// The largest table the line matcher builds. Past this the differing region is
/// shown as one wholesale replacement, which is still correct and is cheap.
const MAX_TABLE_CELLS: usize = 4_000_000;

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum Op {
    Same,
    Removed,
    Added,
}

/// The difference between two texts, empty exactly when they are equal.
pub fn line_diff(expected: &str, actual: &str) -> String {
    let old: Vec<&str> = expected.split_inclusive('\n').collect();
    let new: Vec<&str> = actual.split_inclusive('\n').collect();
    render(&old, &new, &edit_script(&old, &new))
}

fn edit_script(old: &[&str], new: &[&str]) -> Vec<Op> {
    let prefix = old.iter().zip(new).take_while(|(a, b)| a == b).count();
    let suffix = old[prefix..]
        .iter()
        .rev()
        .zip(new[prefix..].iter().rev())
        .take_while(|(a, b)| a == b)
        .count();
    let old_mid = &old[prefix..old.len() - suffix];
    let new_mid = &new[prefix..new.len() - suffix];

    let mut script = vec![Op::Same; prefix];
    match_middle(old_mid, new_mid, &mut script);
    script.resize(script.len() + suffix, Op::Same);
    script
}

/// A longest common subsequence, removals before additions where both fit.
fn match_middle(old: &[&str], new: &[&str], script: &mut Vec<Op>) {
    let (n, m) = (old.len(), new.len());
    let cells = (n + 1).saturating_mul(m + 1);
    if cells > MAX_TABLE_CELLS {
        script.resize(script.len() + n, Op::Removed);
        script.resize(script.len() + m, Op::Added);
        return;
    }
    let width = m + 1;
    let mut table = vec![0u32; cells];
    for i in (0..n).rev() {
        for j in (0..m).rev() {
            table[i * width + j] = if old[i] == new[j] {
                table[(i + 1) * width + j + 1] + 1
            } else {
                table[(i + 1) * width + j].max(table[i * width + j + 1])
            };
        }
    }
    let (mut i, mut j) = (0, 0);
    while i < n && j < m {
        if old[i] == new[j] {
            script.push(Op::Same);
            i += 1;
            j += 1;
        } else if table[(i + 1) * width + j] >= table[i * width + j + 1] {
            script.push(Op::Removed);
            i += 1;
        } else {
            script.push(Op::Added);
            j += 1;
        }
    }
    script.resize(script.len() + (n - i), Op::Removed);
    script.resize(script.len() + (m - j), Op::Added);
}

fn render(old: &[&str], new: &[&str], script: &[Op]) -> String {
    let mut out = String::new();
    let changes: Vec<usize> = (0..script.len())
        .filter(|&at| script[at] != Op::Same)
        .collect();
    let mut next = 0;
    while next < changes.len() {
        let mut last = next;
        while last + 1 < changes.len() && changes[last + 1] - changes[last] <= 2 * CONTEXT + 1 {
            last += 1;
        }
        let start = changes[next].saturating_sub(CONTEXT);
        let end = (changes[last] + CONTEXT + 1).min(script.len());
        render_hunk(&mut out, old, new, script, start, end);
        next = last + 1;
    }
    out
}

fn render_hunk(
    out: &mut String,
    old: &[&str],
    new: &[&str],
    script: &[Op],
    start: usize,
    end: usize,
) {
    let mut old_at = script[..start]
        .iter()
        .filter(|&&op| op != Op::Added)
        .count();
    let mut new_at = script[..start]
        .iter()
        .filter(|&&op| op != Op::Removed)
        .count();
    let _ = writeln!(
        out,
        "@@ expected line {}, actual line {} @@",
        old_at + 1,
        new_at + 1
    );
    for &op in &script[start..end] {
        let (mark, line) = match op {
            Op::Same => (' ', old[old_at]),
            Op::Removed => ('-', old[old_at]),
            Op::Added => ('+', new[new_at]),
        };
        let _ = writeln!(out, "{mark} {}", visible(line));
        if !line.ends_with('\n') {
            out.push_str("\\ no newline at end of file\n");
        }
        if op != Op::Added {
            old_at += 1;
        }
        if op != Op::Removed {
            new_at += 1;
        }
    }
}

/// Spells out what a terminal would hide: control characters and trailing spaces.
fn visible(line: &str) -> String {
    let body = line.strip_suffix('\n').unwrap_or(line);
    let kept = body.trim_end_matches(' ');
    let mut out = String::with_capacity(body.len());
    for c in kept.chars() {
        match c {
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c if c.is_control() => {
                let _ = write!(out, "\\x{:02x}", u32::from(c));
            }
            c => out.push(c),
        }
    }
    for _ in kept.len()..body.len() {
        out.push('\u{b7}');
    }
    out
}
