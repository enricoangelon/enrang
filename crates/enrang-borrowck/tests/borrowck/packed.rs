//! Stage 2E's test of EN0804 (A:653, M3 plan d.6): `check_packed` over the fixtures
//! of `tests/mir/borrowck/packed/`, each class named `Pk` marked `@packed`, since the
//! text form has no such attribute; expected lines carry `//= EN0804`.

use enrang_diag::{DiagCtx, RenderOpts, render_text};
use enrang_mir::{Bodies, parse_module};
use enrang_testkit::{Harness, reported};

fn packed_lines(text: &str, mark: bool) -> Vec<usize> {
    let (mut tcx, list) = parse_module(text).unwrap_or_else(|e| panic!("{e}"));
    if mark {
        let pk: Vec<_> = tcx
            .adts()
            .filter(|(_, a)| a.name.as_str() == "Pk")
            .map(|(_, a)| a.def)
            .collect();
        for d in pk {
            tcx.def_mut(d).attrs.packed = true;
        }
    }
    let bodies: Bodies = list.into_iter().map(|b| (b.owner, b)).collect();
    let mut dcx = DiagCtx::new();
    enrang_borrowck::check_packed(&tcx, &bodies, &mut dcx);
    let rendered = render_text(&dcx.take(), tcx.map(), &RenderOpts { color: false });
    reported(&rendered)
        .iter()
        .inspect(|r| assert_eq!(r.code, "EN0804"))
        .filter_map(|r| r.line())
        .collect()
}

pub fn register(h: &mut Harness) {
    h.case(
        "packed/EN0804 at each reference to a packed field aligned above 1",
        || {
            let text = crate::held::fixture("packed", "packed");
            let want: Vec<usize> = text
                .lines()
                .enumerate()
                .filter(|(_, l)| !l.trim_start().starts_with("//") && l.ends_with("//= EN0804"))
                .map(|(i, _)| i + 1)
                .collect();
            assert_eq!(want.len(), 3);
            assert_eq!(packed_lines(&text, true), want);
            assert!(
                packed_lines(&text, false).is_empty(),
                "a class that is not packed"
            );
        },
    );
}
