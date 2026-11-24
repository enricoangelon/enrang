//! The repository and the command line, as the meta-tests see them.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Mutex, OnceLock};

use enrang_diag::Milestone;
use enrang_testkit::{
    Anchor, AnchorError, FixtureHeader, TempDir, anchors, fixture_header, workspace_root,
};

/// The command line as a process: the same `main` as `enrang` (see `process.rs`).
pub const CLI: &str = env!("CARGO_BIN_EXE_enrang-suite-cli");

/// A process that panics inside the command line's entry point.
pub const ICE: &str = env!("CARGO_BIN_EXE_enrang-suite-ice");

/// Where the command line's whole-process transcripts are.
pub const TRANSCRIPTS: &str = "tests/golden/cli";

/// The transcripts of `check`, `fmt` and `init` that need a directory holding files,
/// or standard input (`enrang-cli`'s `PROJECT_SUITE`). Those under `initialised/` run
/// in a project that `enrang init` made; the others need files that only the CLI
/// suite lists, so the meta-tests read them and no meta-test runs them.
pub const PROJECT_TRANSCRIPTS: &str = "tests/golden/cli-project";

/// The anchored compile fixtures (TESTING 7, M1 plan d.6): `<CODE>/<name>.fail.en`
/// fires, and `<CODE>/<name>.pass.en` is a near-miss. A firing fixture is named as
/// TESTING 7 names an anchored snippet file, which `enrang fmt` skips.
pub const FIXTURES: &str = "tests/compile";

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

/// The goldens under `dir`, a directory of the workspace, named by their paths in it.
pub fn goldens_in(dir: &str) -> Vec<Golden> {
    let root: PathBuf = workspace_root().join(dir);
    files_under(&root)
        .into_iter()
        .map(|name| {
            let text = fs::read_to_string(root.join(&name))
                .unwrap_or_else(|error| panic!("{dir}/{name}: {error}"));
            Golden { name, text }
        })
        .collect()
}

/// Every whole-process transcript. An empty directory is an error, because each
/// gate over it would then pass by checking nothing.
pub fn transcripts() -> Vec<Golden> {
    let goldens = goldens_in(TRANSCRIPTS);
    assert!(!goldens.is_empty(), "no golden in {TRANSCRIPTS}");
    goldens
}

/// Where a run of the command line happens.
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub enum Place {
    /// This suite's own directory, which holds no project.
    Suite,
    /// A fresh project that `enrang init` made.
    Initialised,
    /// The workspace root, where a fixture's path starts.
    Root,
    /// A fresh directory holding these files.
    Files(Vec<(String, Vec<u8>)>),
}

/// Every transcript the gate runs again, each with the place it runs in: those of
/// `cli` here, those of `cli-project/initialised` in a new project.
pub fn gate_transcripts() -> Vec<(Golden, Place)> {
    let mut found: Vec<(Golden, Place)> = transcripts()
        .into_iter()
        .map(|golden| (golden, Place::Suite))
        .collect();
    let dir = format!("{PROJECT_TRANSCRIPTS}/initialised");
    let goldens = goldens_in(&dir);
    assert!(!goldens.is_empty(), "no golden in {dir}");
    for golden in goldens {
        let name = format!("cli-project/initialised/{}", golden.name);
        found.push((
            Golden {
                name,
                text: golden.text,
            },
            Place::Initialised,
        ));
    }
    found
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

/// The command line in `place`. A fresh project is made with this binary's `init`.
pub fn run_cli_at(place: &Place, args: &[String]) -> Ran {
    match place {
        Place::Suite => run_cli(args),
        Place::Root => finished(Command::new(CLI).args(args).current_dir(workspace_root())),
        Place::Initialised => {
            let project = TempDir::new("meta-project");
            let init = finished(Command::new(CLI).arg("init").current_dir(project.path()));
            assert_eq!(init.code, 0, "`enrang init` made no project: {init:?}");
            finished(Command::new(CLI).args(args).current_dir(project.path()))
        }
        Place::Files(files) => {
            let dir = TempDir::new("meta-files");
            for (name, bytes) in files {
                let path = dir.join(name);
                if let Some(parent) = path.parent() {
                    fs::create_dir_all(parent).expect("a parent");
                }
                fs::write(path, bytes).expect("a file");
            }
            finished(Command::new(CLI).args(args).current_dir(dir.path()))
        }
    }
}

/// [`run_cli_at`], once per place and arguments in this process: the command line is
/// deterministic (`determinism.rs`), and several gates run the same commands.
pub fn run_cached(place: &Place, args: &[String]) -> Ran {
    type Runs = Mutex<BTreeMap<(Place, Vec<String>), Ran>>;
    static RUNS: OnceLock<Runs> = OnceLock::new();
    let runs = RUNS.get_or_init(Runs::default);
    let key = (place.clone(), args.to_vec());
    if let Some(ran) = runs.lock().expect("the cache").get(&key) {
        return ran.clone();
    }
    let ran = run_cli_at(place, args);
    runs.lock().expect("the cache").insert(key, ran.clone());
    ran
}

/// An anchored compile fixture.
#[derive(Clone, Debug)]
pub struct Fixture {
    /// Its path from the workspace root.
    pub path: String,
    /// The name of its directory, which must be the code it is for.
    pub code: String,
    /// A near-miss, `<name>.pass.en`, which must pass `check`.
    pub near_miss: bool,
    /// Its anchors, read from its text; a fixture of EN0001 is read lossily.
    pub anchors: Result<Vec<Anchor>, AnchorError>,
    /// Its header (`enrang_testkit::fixture_header`): the target it is checked
    /// with, and whether it is loaded as a library module (`//! library`, G50), as
    /// the CLI fixture runner checks it.
    pub target: Result<FixtureHeader, String>,
}

impl Fixture {
    /// The arguments of `enrang check` on the fixture, from the workspace root,
    /// with the internal `--library` and `--target=` its header asks for; `None`
    /// for a fixture whose header is broken, which never passes.
    pub fn check_args(&self) -> Option<Vec<String>> {
        let header = self.target.as_ref().ok()?;
        let mut args = vec!["check".to_owned()];
        args.extend(header.check_flags());
        args.push(self.path.clone());
        Some(args)
    }
}

/// Every compile fixture, in path order. Files that are not `.en` are left out here,
/// and they and any other misnamed file are refused by a case of `fixtures.rs`.
pub fn fixtures() -> Vec<Fixture> {
    let root = workspace_root().join(FIXTURES);
    files_under(&root)
        .into_iter()
        .filter(|name| name.ends_with(".en"))
        .map(|name| {
            let bytes = fs::read(root.join(&name)).expect("a fixture");
            let code = name.split('/').next().unwrap_or("").to_owned();
            let text = String::from_utf8_lossy(&bytes);
            Fixture {
                path: format!("{FIXTURES}/{name}"),
                code,
                near_miss: name.ends_with(".pass.en"),
                anchors: anchors(&text),
                target: fixture_header(&text),
            }
        })
        .collect()
}

/// The milestone after `current`: the one being built, whose work may land before
/// the commit that closes it bumps `CURRENT_MILESTONE`. The last is its own.
pub fn being_built(current: Milestone) -> Milestone {
    use Milestone::*;
    const ORDER: [Milestone; 11] = [M0, M1, M2, M3, M4, M5, M6, M7, M8, M9, M10];
    let at = ORDER
        .iter()
        .position(|&milestone| milestone == current)
        .expect("a milestone");
    ORDER[(at + 1).min(ORDER.len() - 1)]
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
