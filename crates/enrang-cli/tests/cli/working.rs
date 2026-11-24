//! `check`, `fmt` and `init` in this process, over tables: every target with every
//! `--cpu` and `--float` against what `enrang_target::resolve` says, the output
//! formats, colour, and what no process can show.

use std::io::{self, Read};
use std::path::Path;

use enrang_cli::{Env, Outcome, run_in};
use enrang_diag::{Code, RenderOpts};
use enrang_driver::Session;
use enrang_target::{Arch, CPU_ALIASES, CpuLevel, TargetOpts, all_targets, resolve};
use enrang_testkit::{Harness, TempDir, golden};

use crate::project::spec_case;
use crate::streams::without_escapes;
use crate::support::{INPROCESS_SUITE, inproc_at, strings};

/// The command line in this process, in `dir`, with empty standard input.
fn run_at(dir: &Path, args: &[&str], color: bool) -> Outcome {
    run_in(
        &strings(args),
        color,
        &mut Env {
            dir,
            stdin: &mut io::empty(),
        },
    )
}

/// A reader that always fails.
struct Unreadable;

impl Read for Unreadable {
    fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
        Err(io::Error::from(io::ErrorKind::InvalidData))
    }
}

/// Makes ANSI escapes visible in a golden, which stays reviewable text.
fn visible(text: &str) -> String {
    text.replace('\x1b', "<ESC>")
}

fn native_targets() -> Vec<&'static str> {
    all_targets()
        .iter()
        .copied()
        .filter(|name| {
            resolve(name, &TargetOpts::default()).is_ok_and(|(spec, _)| spec.arch != Arch::Mir)
        })
        .collect()
}

/// Every value `--cpu` might be given: each level of either architecture, each alias,
/// and two that are neither.
fn cpu_values() -> Vec<String> {
    let mut values: Vec<String> = CpuLevel::for_arch(Arch::I386)
        .iter()
        .chain(CpuLevel::for_arch(Arch::X86_64))
        .map(|level| level.name().to_owned())
        .collect();
    values.extend(CPU_ALIASES.iter().map(|alias| alias.name.to_owned()));
    values.extend(["native".to_owned(), "pentium5".to_owned()]);
    values.dedup();
    values
}

/// What `check` must print and return for this target and these flags, with a file
/// that has no syntax error: resolution's error as a phase-0 failure, or its notes.
fn expected(target: &str, opts: &TargetOpts) -> (String, u8) {
    let mut session = Session::new();
    let code = match resolve(target, opts) {
        Ok((_, notes)) => {
            for note in notes {
                session.dcx.emit(note);
            }
            0
        }
        Err(diag) => {
            session.dcx.emit(diag);
            2
        }
    };
    (session.render(&RenderOpts::default()), code)
}

pub fn register(h: &mut Harness) {
    for target in native_targets() {
        for cpu in cpu_values() {
            h.case(
                format!("working/check --target={target} --cpu={cpu}"),
                move || {
                    let dir = TempDir::new("cpu");
                    dir.write("main.en", "console.log(1);\n");
                    let opts = TargetOpts {
                        cpu: Some(cpu.clone()),
                        ..TargetOpts::default()
                    };
                    let target_flag = format!("--target={target}");
                    let cpu_flag = format!("--cpu={cpu}");
                    let outcome = inproc_at(
                        dir.path(),
                        &["check", &target_flag, &cpu_flag, "main.en"],
                        b"",
                    );
                    let (stderr, code) = expected(target, &opts);
                    assert_eq!(
                        (outcome.stderr.as_str(), outcome.code),
                        (stderr.as_str(), code)
                    );
                    assert_eq!(outcome.stdout, "");
                },
            );
        }
        for float in ["soft", "sse2", "x87", "quad"] {
            h.case(
                format!("working/check --target={target} --float={float}"),
                move || {
                    let dir = TempDir::new("float");
                    dir.write("main.en", "console.log(1);\n");
                    let opts = TargetOpts {
                        float: Some(float.to_owned()),
                        ..TargetOpts::default()
                    };
                    let target_flag = format!("--target={target}");
                    let float_flag = format!("--float={float}");
                    let outcome = inproc_at(
                        dir.path(),
                        &["check", &target_flag, &float_flag, "main.en"],
                        b"",
                    );
                    let (stderr, code) = expected(target, &opts);
                    assert_eq!(
                        (outcome.stderr.as_str(), outcome.code),
                        (stderr.as_str(), code)
                    );
                },
            );
        }
    }
    for vm in all_targets()
        .iter()
        .copied()
        .filter(|name| !native_targets().contains(name))
    {
        h.case(
            format!("working/check --target={vm} is no target"),
            move || {
                let dir = TempDir::new("vm");
                dir.write("main.en", "console.log(1);\n");
                let flag = format!("--target={vm}");
                let outcome = inproc_at(dir.path(), &["check", &flag, "main.en"], b"");
                assert_eq!(outcome.code, 2);
                assert!(
                    outcome
                        .stderr
                        .starts_with(&format!("error[EN1303]: unknown target `{vm}`\n")),
                    "{}",
                    outcome.stderr
                );
            },
        );
    }
    h.case("working/check takes the host's target by default", || {
        let dir = TempDir::new("host");
        dir.write("main.en", "console.log(1);\n");
        let outcome = inproc_at(dir.path(), &["check", "--cpu=x86-64", "main.en"], b"");
        assert_eq!(outcome.code, 0, "{outcome:?}");
        let outcome = inproc_at(dir.path(), &["check", "--cpu=i386", "main.en"], b"");
        let host = enrang_target::host_target();
        assert!(
            outcome.stderr.starts_with(&format!(
                "error[EN0912]: level `i386` does not apply to target `{host}`\n"
            )),
            "{}",
            outcome.stderr
        );
    });

    for id in ["G01", "G02", "G03", "G04"] {
        h.case(
            format!("working/{id} as JSON is one object per diagnostic"),
            move || {
                let case = spec_case(id);
                let dir = TempDir::new("json");
                for file in &case.files {
                    dir.write(&file.name, &file.contents);
                }
                let file = case.files[0].name.as_str();
                let human = inproc_at(dir.path(), &["check", file], b"");
                let json = inproc_at(dir.path(), &["check", "--error-format=json", file], b"");
                assert_eq!(json.code, human.code);
                let errors = human.stderr.matches("\nerror[").count()
                    + usize::from(human.stderr.starts_with("error["));
                let lines: Vec<&str> = json.stderr.lines().collect();
                assert_eq!(lines.len(), errors, "{}", json.stderr);
                for line in lines {
                    assert!(
                        line.starts_with("{\"version\":1,\"severity\":\"error\",\"code\":\"EN0"),
                        "{line}"
                    );
                    assert!(line.ends_with('}'), "{line}");
                    assert!(line.contains(&format!("\"file\":\"{file}\"")), "{line}");
                }
                assert!(!json.stderr.contains("aborting"));
            },
        );
    }
    h.case(
        "working/--color=auto follows the caller and the others do not",
        || {
            let case = spec_case("G01");
            let dir = TempDir::new("color");
            dir.write(&case.files[0].name, &case.files[0].contents);
            let file = case.files[0].name.as_str();
            let painted = |args: &[&str], color: bool| {
                run_at(dir.path(), args, color).stderr.contains('\x1b')
            };
            assert!(painted(&["check", file], true));
            assert!(!painted(&["check", file], false));
            assert!(painted(&["check", "--color=auto", file], true));
            assert!(!painted(&["check", "--color=auto", file], false));
            assert!(painted(&["check", "--color=always", file], false));
            assert!(!painted(&["check", "--color=never", file], true));
            assert!(!painted(
                &["check", "--color=always", "--error-format=json", file],
                true
            ));
            let plain = run_at(dir.path(), &["check", file], false).stderr;
            let colored = run_at(dir.path(), &["check", "--color=always", file], false).stderr;
            assert_eq!(without_escapes(&colored), plain);
        },
    );
    h.case(
        "working/fmt paints its syntax errors as the caller says",
        || {
            let dir = TempDir::new("fmt-color");
            dir.write("bad.en", "const x = 1\n");
            assert!(
                run_at(dir.path(), &["fmt", "bad.en"], true)
                    .stderr
                    .contains('\x1b')
            );
            assert!(
                !run_at(dir.path(), &["fmt", "bad.en"], false)
                    .stderr
                    .contains('\x1b')
            );
        },
    );
    h.case("golden/color/check_always.txt", || {
        let case = spec_case("G04");
        let dir = TempDir::new("color");
        dir.write(&case.files[0].name, &case.files[0].contents);
        let outcome = run_at(
            dir.path(),
            &["check", "--color=always", &case.files[0].name],
            false,
        );
        golden(
            INPROCESS_SUITE,
            "color/check_always.txt",
            &visible(&outcome.stderr),
        )
    });
    h.case("golden/color/check_phase_2.txt", || {
        let case = spec_case("G05");
        let dir = TempDir::new("color");
        dir.write(&case.files[0].name, &case.files[0].contents);
        let painted = run_at(
            dir.path(),
            &["check", "--color=always", &case.files[0].name],
            false,
        );
        let plain = run_at(dir.path(), &["check", &case.files[0].name], false);
        assert_eq!(painted.code, 1);
        assert_eq!(without_escapes(&painted.stderr), plain.stderr);
        assert_eq!(plain.stderr, case.stderr.text);
        golden(
            INPROCESS_SUITE,
            "color/check_phase_2.txt",
            &visible(&painted.stderr),
        )
    });
    h.case("golden/fmt/stdin_unreadable.txt", || {
        let outcome = run_in(
            &strings(&["fmt"]),
            false,
            &mut Env {
                dir: Path::new("."),
                stdin: &mut Unreadable,
            },
        );
        assert_eq!(outcome.code, 1);
        assert_eq!(outcome.stdout, "");
        golden(INPROCESS_SUITE, "fmt/stdin_unreadable.txt", &outcome.stderr)
    });

    h.case(
        "working/every code check reports is one SPEC 13.2 has",
        || {
            for code in [
                Code::EN0909,
                Code::EN0911,
                Code::EN0912,
                Code::EN1031,
                Code::EN1034,
                Code::EN1041,
                Code::EN1303,
                Code::EN1304,
                Code::EN1305,
                Code::EN1307,
            ] {
                assert_eq!(code.phase().to_string(), "0", "{code}");
                assert_eq!(code.since().to_string(), "M1", "{code}");
            }
        },
    );
}
