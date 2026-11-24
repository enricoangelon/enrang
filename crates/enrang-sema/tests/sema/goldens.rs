//! SPEC 14's G cases of M2 byte for byte in process (plan g.1, g.7): each case's
//! file run through `load`, `analyze` and `check_sizes` with the embedded library
//! on the host target, as `enrang check` runs them, rendered as it renders,
//! compared with the case's stderr, and its exit code read from whether an error
//! was reported.
//!
//! Stage 3A registered G05, G06 and G17 here; the stage-4 owners checked G12, G13,
//! G19, G20 and G22 in their own files; stage 5A gathers all eight (plan h.1). The
//! CLI suite runs the same cases through the binary.

use std::sync::Arc;

use enrang_base::SourceMap;
use enrang_diag::{DiagCtx, RenderOpts, render_text};
use enrang_hir::Tcx;
use enrang_sema::{LibSource, LoadError, ProgramInput, analyze, check_sizes, load};
use enrang_syntax::{NodeIdGen, ParseMode};
use enrang_target::{TargetOpts, resolve};
use enrang_testkit::{Case, Harness, extract_cases, line_diff, workspace_root};

/// The G cases of milestone M2 (`tests/trace/case_since.txt`).
const CASES: &[&str] = &["G05", "G06", "G12", "G13", "G17", "G19", "G20", "G22"];

pub fn register(h: &mut Harness) {
    for &id in CASES {
        h.case(
            format!("goldens/{id} byte-exact through load, analyze and check_sizes"),
            move || {
                let case = case(id);
                check(&case);
            },
        );
    }
    h.case(
        "goldens/the list is every check case of M2 in the side table",
        || {
            let since =
                std::fs::read_to_string(workspace_root().join("tests/trace/case_since.txt"))
                    .expect("the side table");
            let spec =
                std::fs::read_to_string(workspace_root().join("docs/SPEC.md")).expect("SPEC");
            let cases = extract_cases(&spec).expect("SPEC's cases extract");
            let m2: Vec<&str> = since
                .lines()
                .filter_map(|line| line.strip_suffix(" M2"))
                .filter(|id| {
                    cases
                        .iter()
                        .any(|c| c.id == *id && c.cmd.starts_with("enrang check "))
                })
                .collect();
            assert_eq!(m2, CASES);
        },
    );
}

/// The SPEC case `id`.
fn case(id: &str) -> Case {
    let spec = std::fs::read_to_string(workspace_root().join("docs/SPEC.md")).expect("SPEC");
    let cases = extract_cases(&spec).expect("SPEC's cases extract");
    cases
        .into_iter()
        .find(|c| c.id == id)
        .unwrap_or_else(|| panic!("no case {id}"))
}

/// Runs `case` as `enrang check <file>` runs it, phases 1, 2 and 4's size check, and
/// compares stderr and the exit code.
fn check(case: &Case) {
    assert_eq!(case.files.len(), 1, "{}: one file", case.id);
    assert_eq!(case.cmd, format!("enrang check {}", case.files[0].name));
    let file = &case.files[0];
    let (spec, _) =
        resolve(enrang_target::host_target(), &TargetOpts::default()).expect("the host");
    let input =
        ProgramInput::in_memory(&file.name, &[(&file.name, &file.contents)], ParseMode::Test);
    assert!(matches!(input.lib, LibSource::Embedded));
    let mut map = SourceMap::new();
    let mut ids = NodeIdGen::new();
    let mut dcx = DiagCtx::new();
    let loaded = match load(&input, &spec, &mut map, &mut ids, &mut dcx) {
        Ok(program) => Some(program),
        Err(LoadError::Aborted(_)) => None,
        Err(LoadError::Unreadable { path, error }) => {
            panic!("{}: {error}", path.display())
        }
    };
    let map = Arc::new(map);
    let mut tcx = Tcx::new(Arc::new(spec), Arc::clone(&map));
    if let Some(program) = loaded
        && let Ok(checked) = analyze(&program, &mut tcx, &mut dcx)
    {
        let _ = check_sizes(&checked, &tcx, &mut dcx);
    }
    let diags = dcx.take();
    let actual = render_text(&diags, &map, &RenderOpts { color: false });
    assert!(
        actual == case.stderr.text,
        "{}: {}",
        case.id,
        line_diff(&case.stderr.text, &actual)
    );
    let exit = i32::from(diags.iter().any(|d| d.severity.fails()));
    assert_eq!(exit, case.exit, "{}: exit code", case.id);
}
