//! Stage 2E's `for...of` tests (A:1223-1232, M3 plan d.5-d.6): the fixtures of
//! `tests/mir/borrowck/loops/c13/` run with c.13's spans, as mirbuild gives them
//! (the head's `Len` and `check_tag` run and the bind's checks and `Ref` carry the
//! loop's source span), so the one-report rule meets one span; and the turn keys,
//! renames and bind marks read from `held`.

use std::path::PathBuf;

use enrang_diag::{DiagCtx, RenderOpts, render_text};
use enrang_mir::{Bodies, Body, Rvalue, StatementKind, parse_module, verify};
use enrang_testkit::{Harness, anchors, compare, reported};

/// c.13's spans: a loop's own head and bind accesses carry its source's span.
pub fn c13_spans(b: &mut Body) {
    for lp in b.meta.loops.clone() {
        for st in b.blocks[lp.head].stmts.iter_mut() {
            let own = matches!(
                st.kind,
                StatementKind::CheckTag { .. }
                    | StatementKind::Assign {
                        value: Rvalue::Len(_),
                        ..
                    }
            );
            if own {
                st.span = lp.span;
            }
        }
        for st in b.blocks[lp.bind.block]
            .stmts
            .iter_mut()
            .take(lp.bind.index as usize + 1)
        {
            if matches!(
                st.kind,
                StatementKind::CheckTag { .. }
                    | StatementKind::CheckBounds { .. }
                    | StatementKind::Assign {
                        value: Rvalue::Ref { .. },
                        ..
                    }
            ) {
                st.span = lp.span;
            }
        }
    }
}

/// What phase 3 reports on `text` with c.13's spans.
fn run_c13(text: &str) -> String {
    let (tcx, mut list) = parse_module(text).unwrap_or_else(|e| panic!("{e}"));
    for b in &mut list {
        c13_spans(b);
        verify(&tcx, b).unwrap_or_else(|e| panic!("invalid MIR: {e:#?}"));
    }
    let bodies: Bodies = list.into_iter().map(|b| (b.owner, b)).collect();
    let mut dcx = DiagCtx::new();
    for b in bodies.values() {
        enrang_borrowck::check(&tcx, &bodies, b, &mut dcx);
    }
    render_text(&dcx.take(), tcx.map(), &RenderOpts { color: false })
}

pub fn register(h: &mut Harness) {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/mir/borrowck/loops/c13");
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .map(|d| d.map(|e| e.expect("an entry").path()).collect())
        .unwrap_or_default();
    files.sort();
    h.case("loops/the c13 fixtures exist", {
        let n = files.len();
        move || assert!(n >= 2)
    });
    for f in files {
        let name = f
            .file_stem()
            .expect("a name")
            .to_string_lossy()
            .into_owned();
        let text = std::fs::read_to_string(&f).expect("readable");
        h.case(
            format!("loops/c13/{name}: reports what its anchors say"),
            move || {
                let want = anchors(&text).unwrap_or_else(|e| panic!("{e}"));
                let rendered = run_c13(&text);
                if let Err(m) = compare(&want, &reported(&rendered)) {
                    panic!("{m}\n{rendered}");
                }
            },
        );
    }
}
