//! The anchored compile fixtures of `tests/compile/` through `enrang check`, as a
//! process run from the workspace root (TESTING 7 and 18, M1 plan d.6).
//!
//! A firing fixture `tests/compile/<CODE>/<name>.fail.en` must report exactly the
//! (line, code) pairs its hand-written `//~` anchors name, read from the rendered
//! diagnostics, with each anchored piece of a message, and exit 1 when an anchored
//! code is an error. Its whole transcript is the golden `compile/<CODE>/<name>.txt`,
//! which pins the column, the labels and the helps too; blessing rewrites the
//! golden, never the anchors (TESTING 17). A near-miss `<name>.pass.en` passes
//! `check`: exit 0, and nothing on either stream. A firing fixture is named as
//! TESTING 7 names an anchored snippet file, so `enrang fmt` skips it and its
//! anchors stay on their lines. A fixture whose header holds `//! target: <name>`
//! is checked with `--target=<name>`, for a rule only that target has (M2 plan g.4:
//! a C17 interrupt handler needs `i386-none`); the others run for the host's. One
//! whose header holds `//! library` is loaded as a library module, through
//! `check`'s internal `--library` flag, for a rule only library code can meet (G50:
//! EN0439). The header is the fixture's leading lines that are either, in either
//! order, read by `enrang_testkit::fixture_header`, as the meta gate reads it.
//!
//! Since the anchors are what guards the goldens, the runner is tested too: the
//! self-test registers broken fixtures in a temporary directory through the same
//! function that registers the real ones, and requires each of their cases to fail.

use std::fs;
use std::path::{Path, PathBuf};

use enrang_diag::{Code, Severity};
use enrang_testkit::{
    Anchor, FixtureHeader, Harness, RunOptions, TempDir, anchors, compare, fixture_header,
    fixture_target, golden, reported, workspace_root,
};

use crate::support::{COMPILE_SUITE, Ran, enrang_in, strings, transcript};

/// Where the fixtures are, from the workspace root.
pub const FIXTURES: &str = "tests/compile";

/// Where fixtures run from, and whether their transcripts are goldens.
#[derive(Clone, Debug)]
struct Runner {
    /// The directory that holds [`FIXTURES`], where `check` runs.
    root: PathBuf,
    /// The real fixtures each have a golden; the self-test's have none.
    goldens: bool,
}

/// The fixture files under `root`, as paths from it, in path order.
fn fixture_paths(root: &Path) -> Vec<String> {
    let names = |dir: &Path| {
        let mut names: Vec<String> = fs::read_dir(dir)
            .unwrap_or_else(|error| panic!("cannot read {}: {error}", dir.display()))
            .map(|entry| {
                entry
                    .expect("an entry")
                    .file_name()
                    .to_string_lossy()
                    .into_owned()
            })
            .collect();
        names.sort();
        names
    };
    let fixtures = root.join(FIXTURES);
    let mut paths = Vec::new();
    for directory in names(&fixtures) {
        for file in names(&fixtures.join(&directory)) {
            paths.push(format!("{FIXTURES}/{directory}/{file}"));
        }
    }
    paths
}

/// The target a fixture's header, `//! target: <name>`, names, if any
/// (`enrang_testkit::fixture_target`, which the meta gate reads too). A header that
/// names nothing, or one after the header lines, is a broken fixture.
fn target_of(path: &str, text: &str) -> Result<Option<String>, String> {
    fixture_target(text).map_err(|why| format!("{path} {why}"))
}

/// A fixture's whole header (`enrang_testkit::fixture_header`): its target and
/// whether it is headed `//! library`.
fn header_of(path: &str, text: &str) -> Result<FixtureHeader, String> {
    fixture_header(text).map_err(|why| format!("{path} {why}"))
}

/// `enrang check` on a fixture, from the runner's root, for the target it names,
/// with the internal `--library` for a fixture headed `//! library` (G50).
fn check(runner: &Runner, path: &str) -> Result<(Vec<String>, Ran), String> {
    let mut args = strings(&["check"]);
    args.extend(header_of(path, &text_of(runner, path))?.check_flags());
    args.push(path.to_owned());
    let ran = enrang_in(&runner.root, &args);
    Ok((args, ran))
}

/// The text of a fixture, read lossily: a fixture of EN0001 is not UTF-8.
fn text_of(runner: &Runner, path: &str) -> String {
    let bytes = fs::read(runner.root.join(path)).expect("a fixture");
    String::from_utf8_lossy(&bytes).into_owned()
}

/// Whether the run of a firing fixture is what it must be: exactly the (line, code)
/// pairs `anchors` name, exit 1 when an anchored code is an error and 0 when none
/// is, and nothing on stdout.
fn firing_verdict(path: &str, anchors: &[Anchor], ran: &Ran) -> Result<(), String> {
    compare(anchors, &reported(&ran.stderr))
        .map_err(|mismatch| format!("{path}:\n{mismatch}{}", ran.stderr))?;
    let errors = anchors.iter().any(|anchor| {
        Code::from_name(&anchor.code).is_some_and(|code| code.severity() == Severity::Error)
    });
    let status = i32::from(errors);
    if ran.code != status {
        return Err(format!("{path} exits {}, not {status}: {ran:?}", ran.code));
    }
    if !ran.stdout.is_empty() {
        return Err(format!("{path} prints on stdout: {ran:?}"));
    }
    Ok(())
}

/// Whether the run of a near-miss is what it must be: exit 0, and nothing on either
/// stream.
fn near_miss_verdict(path: &str, ran: &Ran) -> Result<(), String> {
    if (ran.code, ran.stdout.as_str(), ran.stderr.as_str()) == (0, "", "") {
        Ok(())
    } else {
        Err(format!("the near-miss {path} does not pass check: {ran:?}"))
    }
}

fn fires(runner: &Runner, path: &str) -> Result<(), String> {
    let anchors = anchors(&text_of(runner, path)).map_err(|error| format!("{path}: {error}"))?;
    if anchors.is_empty() {
        return Err(format!("{path} anchors nothing"));
    }
    let (args, ran) = check(runner, path)?;
    firing_verdict(path, &anchors, &ran)?;
    if !runner.goldens {
        return Ok(());
    }
    let name = path
        .strip_prefix(&format!("{FIXTURES}/"))
        .and_then(|rest| rest.strip_suffix(".fail.en"))
        .expect("a fixture path");
    golden(
        COMPILE_SUITE,
        &format!("{name}.txt"),
        &transcript(&args, &ran),
    )
    .map_err(|failure| failure.to_string())
}

fn passes(runner: &Runner, path: &str) -> Result<(), String> {
    let anchors = anchors(&text_of(runner, path)).map_err(|error| format!("{path}: {error}"))?;
    if !anchors.is_empty() {
        return Err(format!("the near-miss {path} has anchors"));
    }
    let (_, ran) = check(runner, path)?;
    near_miss_verdict(path, &ran)
}

/// The case of one fixture file, by its name: a firing fixture, a near-miss, or a
/// file that is neither.
fn fixture_case(runner: &Runner, path: &str) -> Result<(), String> {
    if path.ends_with(".pass.en") {
        passes(runner, path)
    } else if path.ends_with(".fail.en") {
        fires(runner, path)
    } else {
        Err(format!(
            "{path} is neither <name>.fail.en nor <name>.pass.en"
        ))
    }
}

/// The name of a fixture's case.
fn case_name(path: &str) -> String {
    let name = path.trim_start_matches("tests/");
    if path.ends_with(".pass.en") {
        format!("{name} passes check")
    } else if path.ends_with(".fail.en") {
        format!("{name} reports what it anchors")
    } else {
        format!("{name} is a fixture or a near-miss")
    }
}

/// Registers a case for each fixture under the runner's root. The real fixtures and
/// the self-test's both go through here, so no case can skip its fixture.
fn register_fixtures(h: &mut Harness, runner: &Runner) {
    for path in fixture_paths(&runner.root) {
        let runner = runner.clone();
        h.case(case_name(&path), move || fixture_case(&runner, &path));
    }
}

pub fn register(h: &mut Harness) {
    register_fixtures(
        h,
        &Runner {
            root: workspace_root(),
            goldens: true,
        },
    );
    h.case(
        "compile/the runner fails each fixture that breaks its rules",
        || {
            let dir = TempDir::new("cli-fixtures");
            let files = [
                ("good.fail.en", "const y = a === b; //~ EN0201\n"),
                (
                    "good.pass.en",
                    "const a = 1;\nconst b = 2;\nconst y = a == b;\n",
                ),
                (
                    "freestanding.pass.en",
                    "//! target: i386-none\nimport { serial } from \"os\";\n",
                ),
                ("hosted.pass.en", "import { serial } from \"os\";\n"),
                (
                    "two_targets.pass.en",
                    "//! target: i386-none\n//! target: i386-none\nconst a = 1;\n",
                ),
                ("no_target.pass.en", "//! target:\nconst a = 1;\n"),
                (
                    "late_target.pass.en",
                    "import { serial } from \"os\";\n//! target: i386-none\n",
                ),
                (
                    "freestanding.fail.en",
                    "//! target: i386-none\nimport { fs } from \"os\"; //~ EN0305\n",
                ),
                ("anchored.pass.en", "const y = a == b; //~ EN0201\n"),
                ("broken.pass.en", "const broken = a == ;\n"),
                ("silent.fail.en", "const y = a == b; //~ EN0201\n"),
                ("stray.txt", "const y = a == b;\n"),
                ("wrong_code.fail.en", "const y = a === b; //~ EN0202\n"),
            ];
            let code_dir = dir.join(&format!("{FIXTURES}/EN0201"));
            fs::create_dir_all(&code_dir).expect("a fixture directory");
            for (name, text) in files {
                fs::write(code_dir.join(name), text).expect("a fixture");
            }
            let mut inner = Harness::new("fixtures");
            let runner = Runner {
                root: dir.path().to_path_buf(),
                goldens: false,
            };
            register_fixtures(&mut inner, &runner);
            let quiet = RunOptions {
                quiet: true,
                ..RunOptions::default()
            };
            let report = inner.run_with(&quiet, &mut Vec::new());
            let failed: Vec<&str> = report.failed.iter().map(String::as_str).collect();
            assert_eq!(
                failed,
                [
                    "compile/EN0201/anchored.pass.en passes check",
                    "compile/EN0201/broken.pass.en passes check",
                    "compile/EN0201/hosted.pass.en passes check",
                    "compile/EN0201/late_target.pass.en passes check",
                    "compile/EN0201/no_target.pass.en passes check",
                    "compile/EN0201/silent.fail.en reports what it anchors",
                    "compile/EN0201/stray.txt is a fixture or a near-miss",
                    "compile/EN0201/two_targets.pass.en passes check",
                    "compile/EN0201/wrong_code.fail.en reports what it anchors",
                ]
            );
            assert_eq!(report.passed, 4, "{report:?}");
            // The broken headers fail for what is wrong with them, not because the
            // run they would make fails for another reason.
            let runner = Runner {
                root: dir.path().to_path_buf(),
                goldens: false,
            };
            let why = |name: &str| {
                fixture_case(&runner, &format!("{FIXTURES}/EN0201/{name}"))
                    .expect_err("a broken fixture")
            };
            assert!(why("two_targets.pass.en").contains("on a line after its first"));
            assert!(why("late_target.pass.en").contains("on a line after its first"));
            assert!(why("no_target.pass.en").contains("names no target"));
        },
    );
    h.case(
        "compile/a fixture's target is read from its first line alone (plan g.4)",
        || {
            assert_eq!(target_of("x", "const a = 1;\n"), Ok(None));
            assert_eq!(
                target_of("x", "//! target: i386-none\nconst a = 1;\n"),
                Ok(Some("i386-none".to_owned()))
            );
            assert_eq!(
                target_of("x", "  //! target:   i386-none  \n"),
                Ok(Some("i386-none".to_owned()))
            );
            assert!(target_of("x", "//! target:\n").is_err());
            assert!(target_of("x", "//! target: \n").is_err());
            assert!(target_of("x", "const a = 1;\n//! target: i386-none\n").is_err());
            assert!(target_of("x", "//! target: a\n//! target: a\n").is_err());
            assert!(
                target_of("tests/compile/E/x.pass.en", "//! target:\n")
                    .is_err_and(|why| why.starts_with("tests/compile/E/x.pass.en "))
            );
        },
    );
    h.case(
        "compile/a `//! library` header loads the fixture as a library module (G50)",
        || {
            assert_eq!(
                header_of("x", "//! library\nconst a = 1;\n"),
                Ok(FixtureHeader {
                    target: None,
                    library: true,
                })
            );
            let both = FixtureHeader {
                target: Some("i386-none".to_owned()),
                library: true,
            };
            assert_eq!(
                header_of("x", "//! library\n//! target: i386-none\n//! covers: C17\n"),
                Ok(both.clone())
            );
            assert_eq!(
                header_of("x", "//! target: i386-none\n//! library\n"),
                Ok(both.clone())
            );
            assert_eq!(both.check_flags(), ["--library", "--target=i386-none"]);
            assert!(header_of("x", "const a = 1;\n//! library\n").is_err());
            assert!(header_of("x", "//! library\n//! library\n").is_err());
            assert_eq!(
                header_of("x", "const a = 1;\n").map(|h| h.library),
                Ok(false)
            );
            // The same `extend` is EN0806 in user code and EN0439 in a library module.
            let dir = TempDir::new("compile-library-header");
            let text = "public type P = { x: i64 };\nextend P {\n  public h(): void {}\n}\n";
            fs::write(dir.path().join("p.en"), text).expect("a file");
            let user = enrang_in(dir.path(), &strings(&["check", "p.en"]));
            assert!(user.stderr.contains("error[EN0806]"), "{user:?}");
            let library = enrang_in(dir.path(), &strings(&["check", "--library", "p.en"]));
            assert!(library.stderr.contains("error[EN0439]"), "{library:?}");
            assert!(!library.stderr.contains("EN0806"), "{library:?}");
        },
    );
    h.case(
        "compile/a run passes only as its kind of fixture must run",
        || {
            let ran = |code: i32, stdout: &str, stderr: &str| Ran {
                stdout: stdout.to_owned(),
                stderr: stderr.to_owned(),
                code,
            };
            let near = "x.pass.en";
            assert_eq!(near_miss_verdict(near, &ran(0, "", "")), Ok(()));
            let warned = "warning[EN0430]: fake\n --> x.pass.en:1:1\n";
            assert!(near_miss_verdict(near, &ran(0, "", warned)).is_err());
            assert!(near_miss_verdict(near, &ran(0, "noise\n", "")).is_err());
            assert!(near_miss_verdict(near, &ran(1, "", "")).is_err());

            let fire = "x.fail.en";
            let anchored = anchors("x //~ EN0201\n").expect("an anchor");
            let fired = "error[EN0201]: fake\n --> x.fail.en:1:1\n";
            assert_eq!(firing_verdict(fire, &anchored, &ran(1, "", fired)), Ok(()));
            assert!(firing_verdict(fire, &anchored, &ran(0, "", fired)).is_err());
            assert!(firing_verdict(fire, &anchored, &ran(1, "noise\n", fired)).is_err());
            let other = "error[EN0202]: fake\n --> x.fail.en:1:1\n";
            assert!(firing_verdict(fire, &anchored, &ran(1, "", other)).is_err());
            // A fixture that anchors only a warning exits 0.
            let warning = anchors("x //~ EN0430\n").expect("an anchor");
            let warns = "warning[EN0430]: fake\n --> x.fail.en:1:1\n";
            assert_eq!(firing_verdict(fire, &warning, &ran(0, "", warns)), Ok(()));
            assert!(firing_verdict(fire, &warning, &ran(1, "", warns)).is_err());
        },
    );
}
