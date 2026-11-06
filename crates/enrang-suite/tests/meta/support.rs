//! The repository and the command line, as the meta-tests see them.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use enrang_diag::Milestone;
use enrang_testkit::workspace_root;

/// The command line as a process: the same `main` as `enrang` (see `process.rs`).
pub const CLI: &str = env!("CARGO_BIN_EXE_enrang-suite-cli");

/// A process that panics inside the command line's entry point.
pub const ICE: &str = env!("CARGO_BIN_EXE_enrang-suite-ice");

/// Where the command line's whole-process transcripts are.
pub const TRANSCRIPTS: &str = "tests/golden/cli";

pub fn read(relative: &str) -> String {
    fs::read_to_string(workspace_root().join(relative))
        .unwrap_or_else(|error| panic!("cannot read {relative}: {error}"))
}

/// The directories under `dir`, sorted.
pub fn directories(dir: &Path) -> Vec<String> {
    let entries = fs::read_dir(dir).unwrap_or_else(|error| panic!("{}: {error}", dir.display()));
    let mut names: Vec<String> = entries
        .map(|entry| entry.expect("a directory entry"))
        .filter(|entry| entry.path().is_dir())
        .map(|entry| entry.file_name().to_string_lossy().into_owned())
        .collect();
    names.sort();
    names
}

/// Every crate of the workspace, by directory, which is also its package name.
pub fn crates() -> Vec<String> {
    directories(&workspace_root().join("crates"))
}

/// Files under `dir`, recursively, as sorted paths relative to it.
pub fn files_under(dir: &Path) -> Vec<String> {
    fn walk(dir: &Path, prefix: &str, found: &mut BTreeSet<String>) {
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            let relative = format!("{prefix}{name}");
            if entry.path().is_dir() {
                walk(&entry.path(), &format!("{relative}/"), found);
            } else {
                found.insert(relative);
            }
        }
    }
    let mut found = BTreeSet::new();
    walk(dir, "", &mut found);
    found.into_iter().collect()
}

/// A golden file: its name in its suite, and its text.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Golden {
    pub name: String,
    pub text: String,
}

/// Every whole-process transcript. An empty directory is an error, because each
/// gate over it would then pass by checking nothing.
pub fn transcripts() -> Vec<Golden> {
    let dir: PathBuf = workspace_root().join(TRANSCRIPTS);
    let goldens: Vec<Golden> = files_under(&dir)
        .into_iter()
        .map(|name| {
            let text = fs::read_to_string(dir.join(&name))
                .unwrap_or_else(|error| panic!("{name}: {error}"));
            Golden { name, text }
        })
        .collect();
    assert!(!goldens.is_empty(), "no golden in {TRANSCRIPTS}");
    goldens
}

/// A finished run of the command line.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Ran {
    pub stdout: String,
    pub stderr: String,
    pub code: i32,
}

pub fn finished(command: &mut Command) -> Ran {
    let output = command.output().expect("the binary runs");
    Ran {
        stdout: String::from_utf8(output.stdout).expect("stdout is UTF-8"),
        stderr: String::from_utf8(output.stderr).expect("stderr is UTF-8"),
        code: output.status.code().expect("the binary exits normally"),
    }
}

pub fn run_cli(args: &[String]) -> Ran {
    finished(Command::new(CLI).args(args))
}

impl Ran {
    /// What a transcript holds below its command line.
    pub fn body(&self) -> String {
        format!(
            "[exit {}]\n[stdout]\n{}[stderr]\n{}",
            self.code, self.stdout, self.stderr
        )
    }
}

/// The arguments of a transcript's first line: `$ enrang build 'two words' $'a\x1bb'`.
pub fn parse_command(line: &str) -> Result<Vec<String>, String> {
    let rest = line
        .strip_prefix("$ enrang")
        .ok_or_else(|| format!("not a command line: {line:?}"))?;
    let mut args = Vec::new();
    let mut chars = rest.chars().peekable();
    loop {
        while chars.peek() == Some(&' ') {
            chars.next();
        }
        let Some(&first) = chars.peek() else {
            return Ok(args);
        };
        let mut arg = String::new();
        if first == '$' || first == '\'' {
            let ansi_c = first == '$';
            if ansi_c {
                chars.next();
            }
            if chars.next() != Some('\'') {
                return Err(format!("a bad quote in {line:?}"));
            }
            loop {
                match chars.next() {
                    None => return Err(format!("an unclosed quote in {line:?}")),
                    Some('\'') => break,
                    Some('\\') if ansi_c => {
                        if chars.next() != Some('x') {
                            return Err(format!("only \\xNN escapes are used: {line:?}"));
                        }
                        let high = chars.next().and_then(|c| c.to_digit(16));
                        let low = chars.next().and_then(|c| c.to_digit(16));
                        let (Some(high), Some(low)) = (high, low) else {
                            return Err(format!("a bad \\x escape in {line:?}"));
                        };
                        let byte = char::from_u32(high * 16 + low).expect("below 256");
                        arg.push(byte);
                    }
                    Some(c) => arg.push(c),
                }
            }
        } else {
            while let Some(&c) = chars.peek() {
                if c == ' ' {
                    break;
                }
                arg.push(c);
                chars.next();
            }
        }
        args.push(arg);
    }
}

/// A golden's arguments, from its first line.
pub fn golden_args(golden: &Golden) -> Result<Vec<String>, String> {
    let first = golden.text.lines().next().unwrap_or("");
    parse_command(first).map_err(|error| format!("{}: {error}", golden.name))
}

/// What a transcript says the process wrote to stderr.
pub fn stderr_of(transcript: &str) -> &str {
    transcript
        .split_once("\n[stderr]\n")
        .map_or("", |(_, stderr)| stderr)
}

/// The codes whose diagnostics open a line of this stderr.
pub fn fired_codes(stderr: &str) -> BTreeSet<String> {
    stderr
        .lines()
        .filter_map(|line| {
            let rest = ["error[", "warning[", "fail["]
                .iter()
                .find_map(|head| line.strip_prefix(head))?;
            let (code, tail) = rest.split_once(']')?;
            tail.starts_with(':').then(|| code.to_owned())
        })
        .collect()
}

/// The text between backticks in `line`, in order.
pub fn backticked(line: &str) -> Vec<String> {
    line.split('`')
        .skip(1)
        .step_by(2)
        .map(str::to_owned)
        .collect()
}

/// The first milestone written in `text`.
pub fn milestone_in(text: &str) -> Option<Milestone> {
    text.split(|c: char| !c.is_ascii_alphanumeric())
        .find_map(|word| {
            Some(match word {
                "M0" => Milestone::M0,
                "M1" => Milestone::M1,
                "M2" => Milestone::M2,
                "M3" => Milestone::M3,
                "M4" => Milestone::M4,
                "M5" => Milestone::M5,
                "M6" => Milestone::M6,
                "M7" => Milestone::M7,
                "M8" => Milestone::M8,
                "M9" => Milestone::M9,
                "M10" => Milestone::M10,
                _ => return None,
            })
        })
}

/// The cells of a Markdown table row, trimmed.
pub fn cells(row: &str) -> Vec<String> {
    let inner = row.trim().trim_start_matches('|').trim_end_matches('|');
    inner
        .split('|')
        .map(|cell| cell.trim().to_owned())
        .collect()
}

/// The data rows of the table whose header row is exactly `header`.
pub fn table_after(doc: &str, header: &str) -> Vec<Vec<String>> {
    let mut lines = doc.lines();
    assert!(
        lines.any(|line| line == header),
        "no table with the header {header:?}"
    );
    lines
        .skip(1)
        .take_while(|line| line.trim_start().starts_with('|'))
        .map(cells)
        .collect()
}
