//! `enrang init [name] [--kernel]` (ARCHITECTURE 11): a project with `enrang.json`,
//! `src/main.en`, `src/main.test.en` with one passing test, and a `.gitignore`
//! holding `/out/`, anchored so it cannot match a source directory.
//!
//! With a name, the project goes in the directory of that name, created when it is
//! missing, and the name is the last part of the path; with none, it goes in the
//! working directory, named after it. It never overwrites: if any of the four files
//! exists, or a directory it needs is not one, each is EN1307 and nothing is written.
//! The directories it needs are each part of the name, outermost first, then `src`.
//! `--kernel` arrives with M9.

use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Component, Path, PathBuf};

use enrang_diag::{Code, Diagnostic, Help, Milestone, RenderOpts, shown};
use enrang_driver::Session;
use enrang_target::host_target;

use crate::Env;
use crate::commands::INIT;
use crate::manifest::FILE;
use crate::outcome::{EXIT_FAILURE, EXIT_USAGE, Outcome};
use crate::report::{complaint, later_feature, write_failure};
use crate::table::table;

const USAGE: &str = "enrang init [name] [--kernel]";

/// The program of a new project: top-level statements, then a function its test
/// part can see, since a program's local functions are hidden from tests (SPEC 12.1).
/// Both files are in the canonical style, so `enrang fmt --check` passes on them.
const MAIN: &str = "console.log(greeting(\"world\"));

private function greeting(name: &string): string { return `Hello, ${name}!`; }
";

/// The test part of a new project, with one test that passes.
const MAIN_TEST: &str =
    "test(\"greets by name\", () => { expect(greeting(\"Ada\")).toBe(\"Hello, Ada!\"); });\n";

const GITIGNORE: &str = "/out/\n";

/// The name of a project whose directory has no name of its own.
const FALLBACK_NAME: &str = "project";

pub(crate) fn command(args: &[String], color: bool, env: &mut Env<'_>) -> Outcome {
    if let [flag] = args
        && (flag == "--help" || flag == "-h")
    {
        return Outcome::print(help());
    }
    let mut kernel = false;
    let mut names: Vec<&str> = Vec::new();
    for arg in args {
        match arg.as_str() {
            "--kernel" if kernel => {
                return complaint("`--kernel` is given twice", None, Some(USAGE));
            }
            "--kernel" => kernel = true,
            "--help" | "-h" => {
                return complaint(
                    &format!("`{arg}` takes no other arguments"),
                    None,
                    Some(USAGE),
                );
            }
            flag if flag.starts_with('-') => {
                let name = flag.split_once('=').map_or(flag, |(name, _)| name);
                let help = enrang_diag::did_you_mean(name, &["--kernel", "--help"])
                    .map(|close| format!("did you mean `{close}`?"));
                return complaint(
                    &format!("`{}` is not a flag of `enrang init`", shown(flag)),
                    help.as_deref(),
                    Some(USAGE),
                );
            }
            name => names.push(name),
        }
    }
    let name = match names.as_slice() {
        [] => None,
        [""] => return complaint("the name of a project cannot be empty", None, Some(USAGE)),
        [name] => Some(*name),
        _ => return complaint("`enrang init` takes one name", None, Some(USAGE)),
    };
    if kernel {
        return later_feature(
            "init --kernel",
            Milestone::M9,
            "M9 creates a project for a freestanding kernel",
        );
    }
    let place = name.map(PathBuf::from).unwrap_or_default();
    create(&place, &project_name(&place, env.dir), color, env.dir)
}

fn help() -> String {
    let rows: Vec<Vec<String>> = [
        (
            "  --kernel",
            "A freestanding kernel project, from milestone M9",
        ),
        ("  -h, --help", "Print this help"),
    ]
    .iter()
    .map(|(flag, what)| vec![(*flag).to_owned(), (*what).to_owned()])
    .collect();
    format!(
        "{}.\n\nUsage: {USAGE}\n\nCreates {FILE}, src/main.en, src/main.test.en with one passing test, and a\n.gitignore holding /out/, in the directory `name`, or here with no name. If any of\nthem exists, nothing is written.\n\nFlags:\n{}",
        INIT.summary,
        table(&rows),
    )
}

/// The last part of `place`, or the name of the directory it is when it has none of
/// its own, as `.` has not.
fn project_name(place: &Path, dir: &Path) -> String {
    if let Some(Component::Normal(name)) = place.components().next_back() {
        return name.to_string_lossy().into_owned();
    }
    fs::canonicalize(dir.join(place))
        .ok()
        .and_then(|path| {
            path.file_name()
                .map(|name| name.to_string_lossy().into_owned())
        })
        .unwrap_or_else(|| FALLBACK_NAME.to_owned())
}

/// `text` as a JSON string.
fn json_string(text: &str) -> String {
    let mut out = String::from("\"");
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if u32::from(c) < 0x20 => out.push_str(&format!("\\u{:04x}", u32::from(c))),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// `enrang.json` for a project, with its keys in the order ARCHITECTURE 11 writes
/// them, one per line.
fn manifest(name: &str) -> String {
    let fields = [
        ("name", name),
        ("entry", "src/main.en"),
        ("target", host_target()),
    ];
    let lines: Vec<String> = fields
        .iter()
        .map(|(key, value)| format!("  {}: {}", json_string(key), json_string(value)))
        .collect();
    format!("{{\n{}\n}}\n", lines.join(",\n"))
}

/// The directories a project in `place` needs, outermost first: each part of `place`
/// that names something, as `hello` and `hello/inner` for `hello/inner`, then its
/// `src`. Something already there that is not a directory, nor a link to one, is in
/// the way; below a file nothing is there, so only the outermost such part is named.
fn needed_directories(place: &Path) -> Vec<PathBuf> {
    let mut needed: Vec<PathBuf> = place
        .ancestors()
        .filter(|part| !part.as_os_str().is_empty())
        .map(Path::to_path_buf)
        .collect();
    needed.reverse();
    needed.push(place.join("src"));
    needed
}

fn create(place: &Path, name: &str, color: bool, dir: &Path) -> Outcome {
    let files: [(PathBuf, String); 4] = [
        (place.join(FILE), manifest(name)),
        (place.join("src").join("main.en"), MAIN.to_owned()),
        (place.join("src").join("main.test.en"), MAIN_TEST.to_owned()),
        (place.join(".gitignore"), GITIGNORE.to_owned()),
    ];
    let mut session = Session::new();
    let would_overwrite = |path: &Path| {
        let diag = Diagnostic::spanless(
            Code::EN1307,
            format!("`enrang init` would overwrite `{}`", path.to_string_lossy()),
        )
        .note("`init` never overwrites anything, so it wrote nothing");
        if place.as_os_str().is_empty() {
            diag.with_help(Help::text(
                "give a name, and the project goes in a new directory of that name",
            ))
        } else {
            diag
        }
    };
    for needed in needed_directories(place) {
        let at = dir.join(&needed);
        let in_the_way =
            fs::symlink_metadata(&at).is_ok() && !fs::metadata(&at).is_ok_and(|meta| meta.is_dir());
        if in_the_way {
            session.dcx.emit(would_overwrite(&needed));
        }
    }
    for (path, _) in &files {
        if fs::symlink_metadata(dir.join(path)).is_ok() {
            session.dcx.emit(would_overwrite(path));
        }
    }
    if session.dcx.finish_phase().is_err() {
        return Outcome::fail(session.render(&RenderOpts { color }), EXIT_USAGE);
    }

    let src = place.join("src");
    if let Err(error) = fs::create_dir_all(dir.join(&src)) {
        return Outcome::fail(write_failure(&src, &error), EXIT_FAILURE);
    }
    let mut stdout = String::new();
    for (path, text) in &files {
        let written = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(dir.join(path))
            .and_then(|mut file| file.write_all(text.as_bytes()));
        if let Err(error) = written {
            return Outcome {
                stdout,
                stderr: write_failure(path, &error),
                code: EXIT_FAILURE,
            };
        }
        stdout.push_str(&format!("created {}\n", shown(&path.to_string_lossy())));
    }
    Outcome::print(stdout)
}
