//! SPEC 14's G cases of milestone M3 in process (M3 plan f.2, stage 3): each
//! program through `check`, all four phases, its diagnostics equal to the ones
//! `enrang-diag`'s suite builds by hand (`crates/enrang-diag/tests/diag/goldens.rs`,
//! compared as `--error-format=json` renders them: messages, spans, labels, notes,
//! helps with their applicability and edits), its stderr SPEC's block byte for
//! byte, and every fix-it, applied on its own, removing its diagnostic and adding
//! no error (A:1314, warnings allowed).

use std::path::Path;
use std::sync::Arc;

use enrang_base::BytePos;
use enrang_diag::{Diagnostic, RenderOpts, Severity, apply_fixes, render_json, render_text};
use enrang_driver::{Session, check};
use enrang_target::{TargetOpts, host_target, resolve};
use enrang_testkit::{Case, Harness, TempDir, extract_cases};

use crate::diag_support::doc;
use crate::hand;

/// The cases `case_since.txt` marks `M3` (SPEC 14).
pub const M3_CASES: [&str; 10] = [
    "G07", "G08", "G09", "G10", "G11", "G16", "G18", "G21", "G23", "G24",
];

/// What `check` of one file in a fresh directory reports: the diagnostics, their
/// text and JSON renderings, and where the file starts in the session's map, which
/// the edits' positions are relative to.
pub(crate) struct Ran {
    pub diags: Vec<Diagnostic>,
    pub text: String,
    pub json: String,
    pub base: BytePos,
}

pub(crate) fn run(name: &str, source: &str) -> Ran {
    let dir = TempDir::new("pipeline-goldens");
    dir.write(name, source);
    let mut session = Session::new();
    let target = Arc::new(
        resolve(host_target(), &TargetOpts::default())
            .expect("a target")
            .0,
    );
    let _ = check(&mut session, dir.path(), Path::new(name), target);
    let diags = session.dcx.take();
    let base = (diags.iter())
        .find(|d| !d.primary.span.is_dummy())
        .map_or(BytePos(0), |d| session.map.file_of(d.primary.span.lo).start);
    Ran {
        text: render_text(&diags, &session.map, &RenderOpts::default()),
        json: render_json(&diags, &session.map),
        diags,
        base,
    }
}

fn spec_case(id: &str) -> Case {
    let cases = extract_cases(doc("SPEC.md")).unwrap_or_else(|e| panic!("{e}"));
    cases
        .into_iter()
        .find(|c| c.id == id)
        .unwrap_or_else(|| panic!("SPEC has no case {id}"))
}

pub(crate) fn of_code(r: &Ran, code: enrang_diag::Code) -> usize {
    r.diags.iter().filter(|x| x.code == code).count()
}

pub fn register(h: &mut Harness) {
    for id in M3_CASES {
        h.case(
            format!("goldens/{id} is the hand-built diagnostics, in process"),
            move || {
                let (src, built) = hand::built(id);
                let file = &spec_case(id).files[0];
                let ran = run(&file.name, &file.contents);
                assert_eq!(ran.json, src.json(&built), "{id}\n{}", ran.text);
            },
        );
        h.case(
            format!("goldens/{id} renders SPEC 14's block byte for byte"),
            move || {
                let case = spec_case(id);
                let file = &case.files[0];
                let ran = run(&file.name, &file.contents);
                assert_eq!(ran.text, case.stderr.text, "{id}");
            },
        );
        h.case(
            format!("goldens/{id}: each fix-it removes its diagnostic and adds no error"),
            move || {
                let case = spec_case(id);
                let file = &case.files[0];
                let ran = run(&file.name, &file.contents);
                let mut fixes = 0;
                for d in &ran.diags {
                    for help in d.helps.iter().filter(|h| !h.edits.is_empty()) {
                        let fixed = apply_fixes(&file.contents, ran.base, &help.edits)
                            .unwrap_or_else(|e| panic!("{id}: {e}"));
                        let after = run(&file.name, &fixed);
                        let added = (after.diags.iter())
                            .filter(|x| x.severity == Severity::Error)
                            .any(|x| of_code(&after, x.code) > of_code(&ran, x.code));
                        assert!(
                            of_code(&after, d.code) < of_code(&ran, d.code) && !added,
                            "{id}: `{}` leaves\n{fixed}\n{}",
                            help.message,
                            after.text
                        );
                        fixes += 1;
                    }
                }
                assert!(
                    fixes > 0 || matches!(id, "G09" | "G11"),
                    "{id} offers no fix-it"
                );
            },
        );
    }
}
