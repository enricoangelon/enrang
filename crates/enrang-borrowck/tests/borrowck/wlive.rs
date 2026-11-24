//! Stage 2F's tests of write-liveness and modes (M3 plan d.7). Every `Ref` of a
//! fixture under `tests/mir/borrowck/wlive/modes/` gets a site loan and every
//! `for...of` its hold; `compute_modes` must make each exclusive exactly where its
//! line says `// exclusive` (`// shared` otherwise), a hold where its `loop` line
//! says `// hold exclusive`. The fixtures' contracts are inferred first, so rules
//! (b) and (d) read them.

use enrang_base::{IdVec, Idx, Span};
use enrang_borrowck::{
    BodyCx, HeldResults, Loan, LoanId, LoanKind, LoanPath, compute_modes, infer_contracts,
};
use enrang_diag::DiagCtx;
use enrang_mir::{Point, Rvalue, StatementKind};
use enrang_testkit::Harness;

use crate::infer::{files, load};

fn line_of<'t>(tcx: &enrang_hir::Tcx, text: &'t str, span: Span) -> &'t str {
    let line = tcx.map().loc(span.lo).line as usize;
    text.lines().nth(line - 1).unwrap_or_default()
}

fn modes(text: &str) -> Result<(), String> {
    let (tcx, bodies) = load(text);
    infer_contracts(&tcx, &bodies, &mut DiagCtx::new());
    let mut errors = Vec::new();
    for b in bodies.values() {
        let mut cx = BodyCx::new(&tcx, &bodies, b, None);
        cx.loans.table = IdVec::new();
        let mut want = Vec::new();
        for (bb, blk) in b.blocks.iter_enumerated() {
            for (i, st) in blk.stmts.iter().enumerate() {
                let StatementKind::Assign {
                    value: Rvalue::Ref { place, origin },
                    ..
                } = &st.kind
                else {
                    continue;
                };
                let line = line_of(&tcx, text, st.span);
                let marked = match (line.contains("// exclusive"), line.contains("// shared")) {
                    (true, false) => true,
                    (false, true) => false,
                    _ => {
                        errors.push(format!("unmarked borrow `{}`", line.trim()));
                        continue;
                    }
                };
                cx.loans.table.push(Loan {
                    path: LoanPath {
                        root: place.local,
                        through_ref: false,
                        steps: Vec::new(),
                    },
                    span: st.span,
                    origin: *origin,
                    site: Point::new(bb, i),
                    kind: LoanKind::Site,
                });
                want.push((line.trim().to_owned(), marked));
            }
        }
        for lp in &b.meta.loops {
            let line = line_of(&tcx, text, lp.span);
            cx.loans.table.push(Loan {
                path: LoanPath {
                    root: enrang_mir::Local(1),
                    through_ref: true,
                    steps: Vec::new(),
                },
                span: lp.span,
                origin: enrang_mir::BorrowOrigin::ForOfHidden,
                site: Point::new(lp.preheader, 0),
                kind: LoanKind::Hold(lp.id),
            });
            want.push((line.trim().to_owned(), line.contains("// hold exclusive")));
        }
        let m = compute_modes(&cx, &HeldResults::default());
        for (i, (line, w)) in want.iter().enumerate() {
            if m.exclusive(LoanId::new(i)) != *w {
                errors.push(format!("`{line}`: exclusive is {}", !w));
            }
        }
    }
    match errors.is_empty() {
        true => Ok(()),
        false => Err(errors.join("\n")),
    }
}

pub fn register(h: &mut Harness) {
    let found = files("wlive/modes");
    assert!(!found.is_empty(), "no wlive fixture");
    for (name, text) in found {
        h.case(format!("wlive/modes/{name}: modes as marked"), move || {
            modes(&text)
        });
    }
}
