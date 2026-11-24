//! `enrang check [file]` (ARCHITECTURE 11), the pipeline as far as milestone M3 has
//! it, for the target resolved in phase 0: phase 1 loads and parses the file, its
//! `.test.en` part, every module they import and the target's library; phase 2
//! resolves names and checks types; phase 3 builds MIR, infers contracts and checks
//! borrows; phase 4 checks packed fields and sizes. Every error of a phase is
//! reported before the run stops (SPEC 13.1). Inside a project, phase 3 writes each
//! user module's interface file under `out/interfaces/` (M3 plan b.9).
//!
//! `--emit=mir` and `--emit=summary` print a checked program's elaborated MIR or
//! its contracts on stdout (M3 plan b.11, departure D23: ARCHITECTURE 11 lists
//! `--emit=` among the build flags, and `build` is M5's); any other value is a
//! usage message. A verifier failure on MIR the compiler built is an internal
//! error, exit status 3.
//!
//! Phase 0 comes first and is the command line's own, in two steps: the deferred
//! flags (EN1034, EN1041) with the target and its flags (`enrang_target::resolve`:
//! EN0909, EN0911, EN0912, EN1031, EN1303, EN1304), all reported together, and then
//! the file (EN1305). An error in either stops the run with exit status 2, as a usage
//! error does; an error of phase 1, 2 or 4 is a compile error, exit status 1.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use enrang_diag::{Code, Diagnostic, Help, RenderOpts, did_you_mean, shown};
use enrang_driver::{CheckError, CheckOptions, Emit, Internal, Session};
use enrang_target::{Arch, TargetOpts, TargetSpec, all_targets, host_target, resolve};

use crate::Env;
use crate::commands::CHECK;
use crate::flags::{self, Common, listed};
use crate::manifest::{self, FILE};
use crate::outcome::{EXIT_FAILURE, EXIT_SUCCESS, EXIT_USAGE, Outcome};
use crate::report::{complaint, not_found, noted_complaint, unreadable};
use crate::table::table;

const USAGE: &str = "enrang check [file] [flags]";

/// The internal flag that loads the file as a library module (G50).
pub const LIBRARY_FLAG: &str = "--library";

pub(crate) fn command(args: &[String], color: bool, env: &mut Env<'_>) -> Outcome {
    if let [flag] = args
        && (flag == "--help" || flag == "-h")
    {
        return Outcome::print(help());
    }
    if let Some(flag) = args.iter().find(|arg| *arg == "--help" || *arg == "-h") {
        return complaint(
            &format!("`{flag}` takes no other arguments"),
            None,
            Some(USAGE),
        );
    }
    // `--library`, internal and in no help: the compile-fixture runners' way to load
    // a fixture headed `//! library` as a library module (G50).
    let library = args.iter().any(|arg| arg == LIBRARY_FLAG);
    let args: Vec<String> = args
        .iter()
        .filter(|arg| *arg != LIBRARY_FLAG)
        .cloned()
        .collect();
    let args = args.as_slice();
    let (flags, files) = match flags::parse(args, "check", USAGE, &["--help"]) {
        Ok(parsed) => parsed,
        Err(outcome) => return outcome,
    };
    let file = match files.as_slice() {
        [] => None,
        [file] => Some(*file),
        _ => return complaint("`enrang check` takes one file", None, Some(USAGE)),
    };
    let emit = match flags.emit.as_deref() {
        None => None,
        Some(value) => match Emit::from_name(value) {
            Some(emit) => Some(emit),
            None => return bad_emit(value),
        },
    };
    let manifest = match manifest::read(env.dir) {
        Ok(manifest) => manifest,
        Err(outcome) => return outcome,
    };
    let mut run = Run {
        session: Session::new(),
        json: flags.json,
        color: flags.color.paints(color),
    };

    // The pipeline of ARCHITECTURE 11 resolves the target before it loads anything,
    // so a rejected flag stops the run before the file is looked for.
    for diag in flags::deferred_diagnostics(&flags.deferred) {
        run.session.dcx.emit(diag);
    }
    let target = resolve_target(&flags, manifest.as_ref(), &mut run.session);
    let (Ok(()), Some(target)) = (run.session.dcx.finish_phase(), target) else {
        return run.finish(EXIT_USAGE);
    };
    let Some(entry) = entry(file, manifest.as_ref(), env.dir, &mut run.session) else {
        return run.finish(EXIT_USAGE);
    };

    let options = CheckOptions {
        library_entry: library,
        project: manifest.is_some().then(|| env.dir.to_path_buf()),
    };
    let result = enrang_driver::check_with(&mut run.session, env.dir, &entry, target, &options);
    let emitted = match &result {
        Ok(checked) => emit.map(|what| enrang_driver::emit(checked, what)),
        Err(_) => None,
    };
    outcome(run, result.map(|_| emitted))
}

/// The outcome of a check that ended in `result`, with the text `--emit=` made
/// when it passed: an internal error, from phase 3 or from the emit, is exit 3
/// with nothing on stdout (SPEC 13, plan g.3).
fn outcome(mut run: Run, result: Result<Option<Result<String, Internal>>, CheckError>) -> Outcome {
    match result {
        Ok(None) => run.finish(EXIT_SUCCESS),
        Ok(Some(Ok(text))) => {
            let mut outcome = run.finish(EXIT_SUCCESS);
            outcome.stdout = text;
            outcome
        }
        Ok(Some(Err(Internal(message)))) => Outcome::internal(&message),
        Err(CheckError::Aborted(_)) => run.finish(EXIT_FAILURE),
        Err(CheckError::Internal(Internal(message))) => Outcome::internal(&message),
        Err(CheckError::Unreadable { path, error }) => {
            run.session.dcx.emit(unreadable(&path, &error));
            run.finish(EXIT_USAGE)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::EXIT_INTERNAL;

    fn run() -> Run {
        Run {
            session: Session::new(),
            json: false,
            color: false,
        }
    }

    const ICE: &str = "error: internal compiler error: the MIR of `f` fails the verifier\nnote: this is a bug in enrang, not in your command\n";

    #[test]
    fn a_verifier_failure_in_phase_3_is_exit_3() {
        let bad = Internal("the MIR of `f` fails the verifier".to_owned());
        let o = outcome(run(), Err(CheckError::Internal(bad)));
        assert_eq!(
            (o.code, o.stdout.as_str(), o.stderr.as_str()),
            (EXIT_INTERNAL, "", ICE)
        );
    }

    #[test]
    fn a_verifier_failure_in_the_emit_is_exit_3() {
        let bad = Internal("the MIR of `f` fails the verifier".to_owned());
        let o = outcome(run(), Ok(Some(Err(bad))));
        assert_eq!(
            (o.code, o.stdout.as_str(), o.stderr.as_str()),
            (EXIT_INTERNAL, "", ICE)
        );
    }

    #[test]
    fn an_emit_prints_its_text_on_stdout() {
        let o = outcome(run(), Ok(Some(Ok("module \"m\"\n".to_owned()))));
        assert_eq!(
            (o.code, o.stdout.as_str()),
            (EXIT_SUCCESS, "module \"m\"\n")
        );
    }
}

/// The usage message of an `--emit=` value `check` does not take: at M3 it prints
/// `mir` and `summary` only (M3 plan b.11).
fn bad_emit(value: &str) -> Outcome {
    let help =
        did_you_mean(value, &Emit::VALUES).map(|close| format!("did you mean `--emit={close}`?"));
    noted_complaint(
        &format!(
            "`--emit={}` is not a value `enrang check` takes",
            shown(value)
        ),
        help.as_deref(),
        Some("`enrang check` emits `mir` or `summary`"),
        Some(USAGE),
    )
}

/// A session and how to render it.
struct Run {
    session: Session,
    json: bool,
    color: bool,
}

impl Run {
    fn finish(mut self, code: u8) -> Outcome {
        let stderr = if self.json {
            self.session.render_json()
        } else {
            self.session.render(&RenderOpts { color: self.color })
        };
        Outcome {
            stdout: String::new(),
            stderr,
            code,
        }
    }
}

/// The targets `--target=` takes: the native rows, not the VM's.
fn native_targets() -> Vec<&'static str> {
    all_targets()
        .iter()
        .copied()
        .filter(|name| !is_vm_row(name))
        .collect()
}

fn is_vm_row(name: &str) -> bool {
    resolve(name, &TargetOpts::default()).is_ok_and(|(spec, _)| spec.arch == Arch::Mir)
}

/// Resolves the target the flags and the manifest name, the host's by default, and
/// reports what resolution says: a note for an alias, or the error, when there is
/// no target to return.
fn resolve_target(
    flags: &Common,
    manifest: Option<&manifest::Manifest>,
    session: &mut Session,
) -> Option<Arc<TargetSpec>> {
    let from_manifest = |field: fn(&manifest::Manifest) -> &Option<String>| {
        manifest.and_then(|manifest| field(manifest).clone())
    };
    let target = flags
        .target
        .clone()
        .or_else(|| from_manifest(|m| &m.target))
        .unwrap_or_else(|| host_target().to_owned());
    if is_vm_row(&target) {
        session.dcx.emit(
            Diagnostic::spanless(Code::EN1303, format!("unknown target `{target}`"))
                .note(format!("targets are {}", listed(&native_targets())))
                .with_help(Help::text(format!(
                    "`{target}` is a layout of the VM, chosen by `enrang run --vm --layout={target}` from milestone M4"
                ))),
        );
        return None;
    }
    let opts = TargetOpts {
        cpu: flags.cpu.clone().or_else(|| from_manifest(|m| &m.cpu)),
        float: flags.float.clone().or_else(|| from_manifest(|m| &m.float)),
        ..TargetOpts::default()
    };
    match resolve(&target, &opts) {
        Ok((spec, notes)) => {
            for note in notes {
                session.dcx.emit(note);
            }
            Some(Arc::new(spec))
        }
        Err(diag) => {
            session.dcx.emit(diag);
            None
        }
    }
}

/// The file to check: the one given, or the manifest's entry. Reports EN1305 when
/// there is none, or when it cannot be found.
fn entry(
    file: Option<&str>,
    manifest: Option<&manifest::Manifest>,
    dir: &Path,
    session: &mut Session,
) -> Option<PathBuf> {
    let entry = match (file, manifest) {
        (Some(file), _) => file.to_owned(),
        (None, Some(manifest)) => match &manifest.entry {
            Some(entry) => entry.clone(),
            None => {
                session.dcx.emit(
                    Diagnostic::spanless(Code::EN1305, format!("{FILE} names no `entry`"))
                        .with_help(Help::text(
                            "give `enrang check` a file, or add an `entry` to the manifest",
                        )),
                );
                return None;
            }
        },
        (None, None) => {
            session.dcx.emit(
                Diagnostic::spanless(Code::EN1305, format!("file not found: `{FILE}`")).with_help(
                    Help::text(
                        "give `enrang check` a file, or run `enrang init` to create a project",
                    ),
                ),
            );
            return None;
        }
    };
    let path = PathBuf::from(&entry);
    if entry.is_empty() {
        session.dcx.emit(not_found(&path));
        return None;
    }
    if let Err(error) = std::fs::metadata(dir.join(&path)) {
        session.dcx.emit(unreadable(&path, &error));
        return None;
    }
    Some(path)
}

fn help() -> String {
    let targets = native_targets();
    let (last, first) = targets.split_last().expect("targets exist");
    let target_values = format!("{} or {last}", first.join(", "));
    let rows: Vec<Vec<String>> = [
        ("  --target=<target>", target_values.as_str()),
        (
            "  --cpu=<level>",
            "A CPU level or an alias, as `enrang targets` lists them",
        ),
        ("  --float=<strategy>", "soft, sse2 or x87"),
        ("  --color=<when>", "auto, always or never"),
        ("  --error-format=<format>", "human or json"),
        (
            "  --emit=<what>",
            "mir or summary: print the checked MIR or the contracts",
        ),
        ("  -h, --help", "Print this help"),
    ]
    .iter()
    .map(|(flag, what)| vec![(*flag).to_owned(), (*what).to_owned()])
    .collect();
    format!(
        "{}.\n\nUsage: {USAGE}\n\nThe file's `.test.en` part, as `main.test.en` is of `main.en`, is checked with it\nwhen it exists. With no file, `check` takes the entry of `{FILE}` in this\ndirectory, whose `target`, `cpu` and `float` are the defaults of the flags below.\n\nFlags:\n{}",
        CHECK.summary,
        table(&rows),
    )
}
