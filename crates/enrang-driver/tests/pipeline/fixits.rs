//! Every fix-it of phase 3's firing compile fixtures compiles once applied (A:1314,
//! M3 plan d.13): each `tests/compile/<CODE>/<name>.fail.en` of a code of
//! borrowck's families, EN06, EN07 and EN08, through `check` in process, for the
//! target and as the module kind its header names, and each help that carries
//! edits, applied on its own to the fixture's text, removing one of its
//! diagnostics and adding no error (warnings allowed). The CLI suite pins the
//! fixtures' text; this is the apply-and-recheck loop of the G cases and the
//! wording programs, run over the fixtures as well. One more case pins what a
//! fix-it needed: the copy `this.clone()` that EN0603 offers for `return *this;`
//! builds MIR the verifier accepts.

use std::fs;
use std::path::Path;
use std::sync::Arc;

use enrang_base::BytePos;
use enrang_diag::{Code, Diagnostic, Severity, apply_fixes};
use enrang_driver::{CheckOptions, Session, check_with};
use enrang_target::{TargetOpts, host_target, resolve};
use enrang_testkit::{Harness, TempDir, fixture_header, workspace_root};

/// What `check` of one fixture reports, and where its file starts in the map.
struct Checked {
    diags: Vec<Diagnostic>,
    base: BytePos,
}

fn checked(source: &str, target: &str, library: bool) -> Checked {
    let dir = TempDir::new("pipeline-fixits");
    dir.write("main.en", source);
    let mut session = Session::new();
    let target = Arc::new(resolve(target, &TargetOpts::default()).expect("a target").0);
    let options = CheckOptions {
        library_entry: library,
        ..CheckOptions::default()
    };
    let _ = check_with(
        &mut session,
        dir.path(),
        Path::new("main.en"),
        target,
        &options,
    );
    let diags = session.dcx.take();
    let base = (diags.iter())
        .find(|d| !d.primary.span.is_dummy())
        .map_or(BytePos(0), |d| session.map.file_of(d.primary.span.lo).start);
    Checked { diags, base }
}

fn count(diags: &[Diagnostic], code: Code) -> usize {
    diags.iter().filter(|d| d.code == code).count()
}

/// Whether a fixture directory holds a code phase 3 or 4 reports: a fix-it of an
/// earlier phase may uncover what the phase after it reports, which is no error
/// the edit added.
fn of_phase3(code: &str) -> bool {
    ["EN06", "EN07", "EN08"].iter().any(|f| code.starts_with(f))
}

/// Phase 3's firing fixtures, as paths from the workspace root, in path order.
fn fixtures() -> Vec<String> {
    let root = workspace_root().join("tests/compile");
    let sorted = |dir: &Path| {
        let mut names: Vec<String> = fs::read_dir(dir)
            .unwrap_or_else(|e| panic!("cannot read {}: {e}", dir.display()))
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
    let mut paths = Vec::new();
    for code in sorted(&root).into_iter().filter(|c| of_phase3(c)) {
        for name in sorted(&root.join(&code)) {
            if name.ends_with(".fail.en") {
                paths.push(format!("tests/compile/{code}/{name}"));
            }
        }
    }
    paths
}

fn applies_and_compiles(path: &str) {
    let bytes = fs::read(workspace_root().join(path)).expect("a fixture");
    let Ok(source) = String::from_utf8(bytes) else {
        return; // EN0001's fixtures are not UTF-8, and offer no fix-it.
    };
    let header = fixture_header(&source).unwrap_or_else(|e| panic!("{path} {e}"));
    let target = header.target.as_deref().unwrap_or(host_target());
    let ran = checked(&source, target, header.library);
    for d in &ran.diags {
        for help in d.helps.iter().filter(|h| !h.edits.is_empty()) {
            let fixed = apply_fixes(&source, ran.base, &help.edits)
                .unwrap_or_else(|e| panic!("{path}: `{}`: {e}", help.message));
            let after = checked(&fixed, target, header.library);
            let added = (after.diags.iter())
                .filter(|x| x.severity == Severity::Error)
                .find(|x| count(&after.diags, x.code) > count(&ran.diags, x.code));
            assert!(
                count(&after.diags, d.code) < count(&ran.diags, d.code) && added.is_none(),
                "{path}: {} `{}` leaves\n{fixed}\n{:?}",
                d.code,
                help.message,
                (after.diags.iter())
                    .map(|x| format!("{} {}", x.code, x.message))
                    .collect::<Vec<_>>()
            );
        }
    }
}

pub fn register(h: &mut Harness) {
    // A `clone` of an object of a class that can be extended, reached through a
    // reference, has its exact-class check (A:943), as a method call's has: the
    // copy EN0603's fix-it writes for `return *this;` (fix-words).
    h.case(
        "fixits/a clone through a reference of an extensible class builds and checks",
        || {
            let source = "const u = new User(\"a\");\nconsole.log(copyOf(&u).me().name);\n\n\
                public function copyOf(u: &User): User { return u.clone(); }\n\
                public class User {\n  public constructor(public name: string) {}\n  \
                public me(): User { return this.clone(); }\n}\n";
            let dir = TempDir::new("pipeline-fixits");
            dir.write("main.en", source);
            let mut session = Session::new();
            let target = Arc::new(
                resolve(host_target(), &TargetOpts::default())
                    .expect("a target")
                    .0,
            );
            let options = CheckOptions::default();
            let ran = check_with(
                &mut session,
                dir.path(),
                Path::new("main.en"),
                target,
                &options,
            );
            assert!(ran.is_ok(), "{:?}", session.dcx.take());
        },
    );
    for path in fixtures() {
        let name = path.trim_start_matches("tests/").to_owned();
        h.case(
            format!("fixits/{name}: each fix-it removes its diagnostic and adds no error"),
            move || applies_and_compiles(&path),
        );
    }
}
