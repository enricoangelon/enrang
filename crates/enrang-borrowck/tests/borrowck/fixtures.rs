//! The `.mir` fixture runner (M3 plan g.1, 1B): each fixture is parsed, its
//! bodies verified, its contracts inferred, each body checked in owner order, and
//! what phase 3 reports compared with the fixture's anchors.

use std::path::PathBuf;

use enrang_diag::{DiagCtx, RenderOpts, render_text};
use enrang_mir::{Bodies, parse_module, verify};
use enrang_testkit::{Harness, anchors, compare, reported};

/// The areas, each a directory of fixtures.
const AREAS: [&str; 14] = [
    "smoke",
    "moves",
    "marks",
    "elaborate",
    "held",
    "access",
    "loops",
    "packed",
    "wlive",
    "infer",
    "parts",
    "r3",
    "fit",
    "narrowing",
];

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/mir/borrowck")
}

/// Every fixture: its area, name and text, in path order.
pub fn all() -> Vec<(String, String, String)> {
    let mut out = Vec::new();
    for area in AREAS {
        let Ok(entries) = std::fs::read_dir(root().join(area)) else {
            continue;
        };
        let mut files: Vec<PathBuf> = entries
            .map(|e| e.expect("an entry").path())
            .filter(|p| p.extension().is_some_and(|x| x == "mir"))
            .collect();
        files.sort();
        for f in files {
            let name = f
                .file_stem()
                .expect("a name")
                .to_string_lossy()
                .into_owned();
            let text = std::fs::read_to_string(&f).expect("a readable fixture");
            out.push((area.to_owned(), name, text));
        }
    }
    out
}

/// What phase 3 reports on `text`, rendered as `enrang check` prints it.
pub fn run(text: &str) -> String {
    let (tcx, list) = parse_module(text).unwrap_or_else(|e| panic!("{e}"));
    for b in &list {
        if let Err(e) = verify(&tcx, b) {
            panic!("the fixture's MIR is invalid: {e:#?}");
        }
    }
    let bodies: Bodies = list.into_iter().map(|b| (b.owner, b)).collect();
    let mut dcx = DiagCtx::new();
    enrang_borrowck::infer_contracts(&tcx, &bodies, &mut dcx);
    let mut order: Vec<_> = bodies.values().collect();
    order.sort_by_key(|b| b.span.lo);
    for b in order {
        enrang_borrowck::check(&tcx, &bodies, b, &mut dcx);
    }
    let diags = dcx.take();
    render_text(&diags, tcx.map(), &RenderOpts { color: false })
}

pub fn register(h: &mut Harness) {
    let found = all();
    h.case("fixtures/the smoke area has its fixture", move || {
        assert!(found.iter().any(|(a, _, _)| a == "smoke"));
    });
    for (area, name, text) in all() {
        h.case(
            format!("fixtures/{area}/{name}: reports what its anchors say"),
            move || {
                let want = anchors(&text).unwrap_or_else(|e| panic!("{e}"));
                let rendered = run(&text);
                if let Err(m) = compare(&want, &reported(&rendered)) {
                    panic!("{m}\n{rendered}");
                }
            },
        );
    }
}
