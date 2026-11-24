//! `enrang fmt [paths] [--check]` (ARCHITECTURE 11, SPEC 12.5).
//!
//! Each path is a file, or a directory whose `.en` files are formatted, found in
//! name order at any depth; `*.fail.en` files are skipped wherever they are found
//! (SPEC 12.3). With no path, or `-`, standard input is formatted to standard output;
//! it is no file of any module, so it may hold test items, as a `.test.en` part may.
//! A file is rewritten only when its text changes. A file that does not parse is
//! left untouched and its errors are printed, which is exit status 1, as a file that
//! `--check` finds would change is, and as a file that cannot be written is.
//!
//! Every file is read before any is written. A path that does not exist, a directory
//! that cannot be listed or a file that cannot be read is EN1305, a usage error
//! (exit status 2), and nothing is formatted then.

use std::collections::BTreeSet;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use enrang_diag::{RenderOpts, shown};
use enrang_driver::Session;

use crate::Env;
use crate::commands::FMT;
use crate::outcome::{EXIT_FAILURE, EXIT_SUCCESS, EXIT_USAGE, Outcome};
use crate::report::{complaint, unreadable, write_failure};
use crate::table::table;

const USAGE: &str = "enrang fmt [paths] [--check]";

/// The name standard input goes by in what `fmt` prints.
const STDIN: &str = "<stdin>";

pub(crate) fn command(args: &[String], color: bool, env: &mut Env<'_>) -> Outcome {
    if let [flag] = args
        && (flag == "--help" || flag == "-h")
    {
        return Outcome::print(help());
    }
    let mut check = false;
    let mut paths: Vec<&str> = Vec::new();
    for arg in args {
        match arg.as_str() {
            "--check" if check => {
                return complaint("`--check` is given twice", None, Some(USAGE));
            }
            "--check" => check = true,
            "--help" | "-h" => {
                return complaint(
                    &format!("`{arg}` takes no other arguments"),
                    None,
                    Some(USAGE),
                );
            }
            "-" => paths.push(arg),
            flag if flag.starts_with('-') => {
                let name = flag.split_once('=').map_or(flag, |(name, _)| name);
                let help = enrang_diag::did_you_mean(name, &["--check", "--help"])
                    .map(|close| format!("did you mean `{close}`?"));
                return complaint(
                    &format!("`{}` is not a flag of `enrang fmt`", shown(flag)),
                    help.as_deref(),
                    Some(USAGE),
                );
            }
            path => paths.push(path),
        }
    }
    if paths.contains(&"-") && paths.len() > 1 {
        return complaint(
            "`-` is standard input, and takes no other path",
            None,
            Some(USAGE),
        );
    }
    let opts = RenderOpts { color };
    if paths.is_empty() || paths == ["-"] {
        standard_input(check, opts, env)
    } else {
        files(&paths, check, opts, env.dir)
    }
}

fn help() -> String {
    let rows: Vec<Vec<String>> = [
        (
            "  --check",
            "Change nothing; list the files that would change, and exit 1 if any would",
        ),
        ("  -h, --help", "Print this help"),
    ]
    .iter()
    .map(|(flag, what)| vec![(*flag).to_owned(), (*what).to_owned()])
    .collect();
    format!(
        "{}.\n\nUsage: {USAGE}\n\nEach path is a file, or a directory whose `.en` files are formatted at any depth;\n`*.fail.en` files are skipped. With no path, or `-`, standard input is formatted\nto standard output. A file that does not parse is left untouched, and its errors\nare printed. Nothing changes the layout: there are no options.\n\nFlags:\n{}",
        FMT.summary,
        table(&rows),
    )
}

/// What `--check` prints when some of `total` inputs would change.
fn would_change(changed: &[String], total: usize) -> String {
    let mut text = String::new();
    for path in changed {
        text.push_str(&format!("{} would be reformatted\n", shown(path)));
    }
    let noun = if total == 1 { "file" } else { "files" };
    text.push_str(&format!(
        "{} of {total} {noun} would change\n",
        changed.len()
    ));
    text
}

fn standard_input(check: bool, opts: RenderOpts, env: &mut Env<'_>) -> Outcome {
    let mut bytes = Vec::new();
    if let Err(error) = env.stdin.read_to_end(&mut bytes) {
        return Outcome::fail(
            format!("error: cannot read standard input: {}\n", error.kind()),
            EXIT_FAILURE,
        );
    }
    let mut session = Session::new();
    match enrang_driver::format_input(&mut session, PathBuf::from(STDIN), &bytes) {
        Err(_) => Outcome::fail(session.render(&opts), EXIT_FAILURE),
        Ok(text) if !check => Outcome::print(text),
        Ok(text) if text.as_bytes() == bytes => Outcome::print(String::new()),
        Ok(_) => Outcome {
            stdout: would_change(&[STDIN.to_owned()], 1),
            stderr: String::new(),
            code: EXIT_FAILURE,
        },
    }
}

/// Whether `fmt` skips a file of this name: a compile-test snippet, whose anchors
/// must stay on their lines (SPEC 12.3, TESTING 7).
fn skipped(path: &Path) -> bool {
    path.file_name()
        .is_some_and(|name| name.to_string_lossy().ends_with(".fail.en"))
}

fn is_source(path: &Path) -> bool {
    path.file_name()
        .is_some_and(|name| name.to_string_lossy().ends_with(".en"))
        && !skipped(path)
}

/// The files `fmt` formats, each read once, in the order the paths name them.
#[derive(Default)]
struct Inputs {
    files: Vec<(PathBuf, Vec<u8>)>,
    seen: BTreeSet<PathBuf>,
}

impl Inputs {
    /// Reads `path`, relative to `dir`, unless it was read already. A file that
    /// cannot be read is EN1305.
    fn add(&mut self, dir: &Path, path: PathBuf, session: &mut Session) {
        if !self.seen.insert(path.clone()) {
            return;
        }
        match fs::read(dir.join(&path)) {
            Ok(bytes) => self.files.push((path, bytes)),
            Err(error) => session.dcx.emit(unreadable(&path, &error)),
        }
    }
}

/// Reads the `.en` files under `shown`, a directory read relative to `dir`, in name
/// order at any depth. Symbolic links inside it are not followed, so no link can make
/// the walk loop. An unreadable directory is EN1305.
fn walk(dir: &Path, shown: &Path, found: &mut Inputs, session: &mut Session) {
    let entries = match fs::read_dir(dir.join(shown)) {
        Ok(entries) => entries,
        Err(error) => {
            session.dcx.emit(unreadable(shown, &error));
            return;
        }
    };
    let mut children: Vec<(PathBuf, bool)> = Vec::new();
    for entry in entries.flatten() {
        let Ok(kind) = entry.file_type() else {
            continue;
        };
        let path = shown.join(entry.file_name());
        if kind.is_dir() {
            children.push((path, true));
        } else if kind.is_file() && is_source(&path) {
            children.push((path, false));
        }
    }
    children.sort();
    for (path, is_dir) in children {
        if is_dir {
            walk(dir, &path, found, session);
        } else {
            found.add(dir, path, session);
        }
    }
}

fn files(paths: &[&str], check: bool, opts: RenderOpts, dir: &Path) -> Outcome {
    let mut session = Session::new();
    let mut inputs = Inputs::default();
    for path in paths {
        let path = Path::new(path);
        let meta = if path.as_os_str().is_empty() {
            Err(io::Error::from(io::ErrorKind::NotFound))
        } else {
            fs::metadata(dir.join(path))
        };
        match meta {
            Err(error) => session.dcx.emit(unreadable(path, &error)),
            Ok(meta) if meta.is_dir() => walk(dir, path, &mut inputs, &mut session),
            Ok(_) if skipped(path) => {}
            Ok(_) => inputs.add(dir, path.to_path_buf(), &mut session),
        }
    }
    if session.dcx.finish_phase().is_err() {
        return Outcome::fail(session.render(&opts), EXIT_USAGE);
    }

    let mut changed = Vec::new();
    let mut code = EXIT_SUCCESS;
    let mut lost = String::new();
    for (path, bytes) in &inputs.files {
        let Ok(text) = enrang_driver::format(&mut session, path.clone(), bytes) else {
            code = code.max(EXIT_FAILURE);
            continue;
        };
        if text.as_bytes() == bytes.as_slice() {
            continue;
        }
        if check {
            changed.push(path.to_string_lossy().into_owned());
        } else if let Err(error) = fs::write(dir.join(path), &text) {
            lost.push_str(&write_failure(path, &error));
        }
    }
    let stdout = if changed.is_empty() {
        String::new()
    } else {
        would_change(&changed, inputs.files.len())
    };
    if !changed.is_empty() || !lost.is_empty() {
        code = code.max(EXIT_FAILURE);
    }
    Outcome {
        stdout,
        stderr: format!("{lost}{}", session.render(&opts)),
        code,
    }
}
