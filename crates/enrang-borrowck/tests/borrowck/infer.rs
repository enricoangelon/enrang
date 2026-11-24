//! Stage 2F's tests of contract inference (M3 plan d.8), and the fixture tools
//! the other 2F suites share.
//!
//! Each `.mir` under `tests/mir/borrowck/<area>/<sub>/` is parsed, verified,
//! inferred and checked body by body; every `//= ` line must be a line of the
//! module's `--emit=summary` text, and its `//~` anchors are what phase 3
//! reports. The fixtures sit one directory below the areas, so the 1B runner,
//! which runs every top-level fixture without these expectations, never sees
//! them. Fixtures that need stage 2E's `held` (sources, stores, R3, the part test)
//! are registered only once `held` finds keys, and are otherwise counted as
//! skipped.

use std::path::PathBuf;

use enrang_borrowck::{BodyCx, HeldResults, LoanKey, check, infer_contracts};
use enrang_diag::{DiagCtx, RenderOpts, render_text};
use enrang_hir::{ModuleId, Tcx};
use enrang_mir::{Bodies, DEFAULT_MODULE, parse_module, verify};
use enrang_testkit::{Harness, anchors, compare, reported, skip};

/// The `.mir` fixtures of `tests/mir/borrowck/<sub>`, name and text, in path order.
pub fn files(sub: &str) -> Vec<(String, String)> {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/mir/borrowck")
        .join(sub);
    let mut paths: Vec<PathBuf> = std::fs::read_dir(&dir)
        .map(|rd| {
            rd.map(|e| e.expect("an entry").path())
                .filter(|p| p.extension().is_some_and(|x| x == "mir"))
                .collect()
        })
        .unwrap_or_default();
    paths.sort();
    paths
        .into_iter()
        .map(|p| {
            let name = p
                .file_stem()
                .expect("a name")
                .to_string_lossy()
                .into_owned();
            (
                name,
                std::fs::read_to_string(&p).expect("a readable fixture"),
            )
        })
        .collect()
}

/// A parsed and verified fixture.
pub fn load(text: &str) -> (Tcx, Bodies) {
    let (tcx, list) = parse_module(text).unwrap_or_else(|e| panic!("{e}"));
    for b in &list {
        if let Err(e) = verify(&tcx, b) {
            panic!("the fixture's MIR is invalid: {e:#?}");
        }
    }
    (tcx, list.into_iter().map(|b| (b.owner, b)).collect())
}

pub fn main_module(tcx: &Tcx) -> ModuleId {
    tcx.modules()
        .find(|(_, m)| m.path.to_string() == DEFAULT_MODULE)
        .map(|(m, _)| m)
        .expect("the fixture's module")
}

/// What phase 3 found on one fixture.
pub struct Run {
    pub diags: String,
    pub summary: String,
}

/// Infers the fixture's contracts and checks each body in text order.
pub fn run(text: &str) -> Run {
    let (tcx, bodies) = load(text);
    let mut dcx = DiagCtx::new();
    let set = infer_contracts(&tcx, &bodies, &mut dcx);
    let mut order: Vec<_> = bodies.values().collect();
    order.sort_by_key(|b| b.span.lo);
    for b in order {
        check(&tcx, &bodies, b, &mut dcx);
    }
    let diags = render_text(&dcx.take(), tcx.map(), &RenderOpts { color: false });
    let summary = enrang_borrowck::summary::render(&tcx, &set, main_module(&tcx));
    Run { diags, summary }
}

/// The fixture's `//= ` lines against the summary, its anchors against the
/// diagnostics. Consecutive `//= ` lines are one block that must appear as
/// consecutive summary lines (a function and its witnesses); a line ending in
/// `)` may stop after a contract's `perms(..)`, matching the line's start.
pub fn expect(text: &str, summary: &str, diags: &str) -> Result<(), String> {
    let have: Vec<&str> = summary.lines().collect();
    let mut blocks: Vec<Vec<&str>> = Vec::new();
    let mut open = false;
    for l in text.lines() {
        match l.trim_start().strip_prefix("//= ") {
            Some(want) if open => blocks.last_mut().expect("a block").push(want),
            Some(want) => blocks.push(vec![want]),
            None => {}
        }
        open = l.trim_start().starts_with("//= ");
    }
    let fits = |h: &str, w: &str| {
        h == w || (w.ends_with(')') && h.strip_prefix(w).is_some_and(|r| r.starts_with(' ')))
    };
    for block in blocks {
        let found = (0..have.len()).any(|i| {
            block.len() <= have.len() - i && block.iter().zip(&have[i..]).all(|(w, h)| fits(h, w))
        });
        if !found {
            return Err(format!(
                "`{}` is not in the summary:\n{summary}",
                block.join("\n")
            ));
        }
    }
    let want = anchors(text).map_err(|e| e.to_string())?;
    compare(&want, &reported(diags)).map_err(|m| format!("{m}\n{diags}"))
}

/// Whether stage 2E's `held` runs in this build: a function returning its
/// reference parameter holds `Param(0)` in `_0`.
pub fn held_live() -> bool {
    let text = "fn id(_1: &i64) -> &i64 {\n  bb0: {\n    _0 = copy _1;\n    return;\n  }\n}\n";
    let (tcx, bodies) = load(text);
    let b = bodies.values().next().expect("a body");
    let cx = BodyCx::new(&tcx, &bodies, b, None);
    HeldResults::run(&cx, true)
        .ret_at_returns()
        .iter()
        .any(|(_, s)| s.contains_key(&LoanKey::Param(0)))
}

/// One case per fixture of `sub`; with `needs_held`, only once `held` runs.
pub fn register_dir(h: &mut Harness, sub: &str, needs_held: bool) {
    let found = files(sub);
    assert!(!found.is_empty(), "no fixture in {sub}");
    if needs_held && !held_live() {
        skip(
            "held",
            found.len(),
            "the fixture waits for stage 2E's held analysis",
        );
        for (name, text) in found {
            h.case(
                format!("{sub}/{name}: parses, verifies and runs"),
                move || {
                    run(&text);
                },
            );
        }
        return;
    }
    for (name, text) in found {
        h.case(format!("{sub}/{name}: summary and reports"), move || {
            let r = run(&text);
            expect(&text, &r.summary, &r.diags)
        });
    }
}

pub fn register(h: &mut Harness) {
    register_dir(h, "infer/perms", false);
    register_dir(h, "infer/flags", false);
    if !files("infer/held").is_empty() {
        register_dir(h, "infer/held", true);
    }
    declared(h);
}

/// Declared contracts from marks and SPEC 5.4's defaults (plan d.8).
fn declared(h: &mut Harness) {
    for (name, text) in files("infer/declared") {
        h.case(
            format!("infer/declared/{name}: contracts from marks"),
            move || {
                let (tcx, _) = load(&text);
                let mut failures = Vec::new();
                for line in text.lines() {
                    let Some((path, want)) = line
                        .trim_start()
                        .strip_prefix("//? ")
                        .and_then(|l| l.split_once(" => "))
                    else {
                        continue;
                    };
                    let d = tcx
                        .defs()
                        .find(|(_, x)| x.path.to_string() == path)
                        .map(|(d, _)| d)
                        .unwrap_or_else(|| panic!("no `{path}`"));
                    let got = show(&enrang_borrowck::contract(&tcx, d));
                    if got != want {
                        failures.push(format!("{path}: got `{got}`, want `{want}`"));
                    }
                }
                match failures.is_empty() {
                    true => Ok(()),
                    false => Err(failures.join("\n")),
                }
            },
        );
    }
}

/// A contract as `perms(..) sources(..) result ..`.
pub fn show(c: &enrang_hir::Contract) -> String {
    let perms: Vec<String> = c
        .perms
        .iter()
        .map(|p| format!("{p:?}").to_lowercase())
        .collect();
    let sources = match &c.sources {
        enrang_hir::RetSources::NoLoans => String::new(),
        enrang_hir::RetSources::Params(v) => {
            v.iter().map(u32::to_string).collect::<Vec<_>>().join(", ")
        }
    };
    let result = match &c.result {
        enrang_hir::ResultPerm::None => "none".to_owned(),
        enrang_hir::ResultPerm::Writable => "writable".to_owned(),
        enrang_hir::ResultPerm::ReadOnly(r) => format!("readonly({r:?})"),
    };
    format!(
        "perms({}) sources({sources}) result {result}",
        perms.join(", ")
    )
}
