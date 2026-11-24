//! Stage 2F's tests of fitting (M3 plan d.10): each fixture under
//! `tests/mir/borrowck/fit/sites/` is inferred, checked body by body, then by
//! `check_module` with a `CheckedProgram` holding the satisfactions its
//! `//! satisfies <found> <member>` lines name (each recorded at the found
//! function's name); its anchors are what phase 3 reports, its `//= ` lines
//! lines of the summary. Those under `fit/held/` need stage 2E's `held`.

use enrang_borrowck::{check, check_module, infer_contracts};
use enrang_diag::{DiagCtx, RenderOpts, render_text};
use enrang_hir::{CheckedProgram, SatisfactionRecord};
use enrang_testkit::{Harness, skip};

use crate::infer::{expect, files, load, main_module};

fn fit(text: &str) -> Result<(), String> {
    let (tcx, bodies) = load(text);
    let def = |path: &str| {
        tcx.defs()
            .find(|(_, d)| d.path.to_string() == path)
            .map(|(d, _)| d)
            .unwrap_or_else(|| panic!("no `{path}`"))
    };
    let mut program = CheckedProgram::default();
    for line in text.lines() {
        if let Some((found, member)) = line
            .strip_prefix("//! satisfies ")
            .and_then(|l| l.split_once(' '))
        {
            let (found, member) = (def(found), def(member));
            program.satisfactions.push(SatisfactionRecord {
                ty: tcx.common().void,
                iface: tcx.common().void,
                member,
                found,
                site: tcx.def(found).name_span,
            });
        }
    }
    let mut dcx = DiagCtx::new();
    let set = infer_contracts(&tcx, &bodies, &mut dcx);
    let mut order: Vec<_> = bodies.values().collect();
    order.sort_by_key(|b| b.span.lo);
    for b in order {
        check(&tcx, &bodies, b, &mut dcx);
    }
    let m = main_module(&tcx);
    check_module(&tcx, &program, &bodies, m, &mut dcx);
    let diags = render_text(&dcx.take(), tcx.map(), &RenderOpts { color: false });
    let summary = enrang_borrowck::summary::render(&tcx, &set, m);
    expect(text, &summary, &diags)
}

pub fn register(h: &mut Harness) {
    let found = files("fit/sites");
    assert!(!found.is_empty(), "no fit fixture");
    for (name, text) in found {
        h.case(format!("fit/sites/{name}: fitting reports"), move || {
            fit(&text)
        });
    }
    // Inferred stores need stage 2E's `held`.
    let held = files("fit/held");
    match crate::infer::held_live() {
        true => {
            for (name, text) in held {
                h.case(format!("fit/held/{name}: fitting reports"), move || {
                    fit(&text)
                });
            }
        }
        false => skip(
            "held",
            held.len(),
            "the fixture waits for stage 2E's held analysis",
        ),
    }
}
