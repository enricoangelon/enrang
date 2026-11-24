//! The narrowing check (N2, A:1362; M3 plan d.11; owner 2F): a reference typing
//! recorded against a fact that is a writer by N3 invalidates the fact until a
//! new test, and a narrowed use reached while it may be invalid is EN0401, once
//! per use, with the writing record as a secondary span.

use std::collections::BTreeMap;

use enrang_base::Span;
use enrang_diag::{Code, DiagCtx, Diagnostic};
use enrang_hir::{Fact, FactId};
use enrang_mir::{BlockId, Body, DataflowAnalysis, Place, Point, Statement, Terminator, solve};

use crate::cx::BodyCx;
use crate::wlive::WLive;

/// Forward: the facts that may be invalid, each with the first writing record.
struct Narrow {
    writes: BTreeMap<Point, Vec<(FactId, Span)>>,
    tests: Vec<(FactId, BlockId)>,
}

impl Narrow {
    fn apply(&self, s: &mut BTreeMap<FactId, Span>, at: Point) {
        for &(f, w) in self.writes.get(&at).into_iter().flatten() {
            s.insert(f, w);
        }
    }
}

impl DataflowAnalysis for Narrow {
    type Domain = BTreeMap<FactId, Span>;
    const FORWARD: bool = true;

    fn bottom(&self, _b: &Body) -> Self::Domain {
        BTreeMap::new()
    }

    fn entry(&self, _b: &Body) -> Self::Domain {
        BTreeMap::new()
    }

    fn join(&self, into: &mut Self::Domain, from: &Self::Domain) -> bool {
        let mut changed = false;
        for (&f, &w) in from {
            match into.get(&f) {
                Some(old) if old.lo <= w.lo => {}
                _ => {
                    into.insert(f, w);
                    changed = true;
                }
            }
        }
        changed
    }

    fn statement(&self, s: &mut Self::Domain, _st: &Statement, at: Point) {
        self.apply(s, at);
    }

    fn terminator(&self, s: &mut Self::Domain, _t: &Terminator, at: Point) {
        self.apply(s, at);
    }

    fn edge(&self, s: &mut Self::Domain, _from: BlockId, to: BlockId) {
        for &(f, bb) in &self.tests {
            if bb == to {
                s.remove(&f);
            }
        }
    }
}

pub fn check(cx: &BodyCx, dcx: &mut DiagCtx) {
    let b = cx.body;
    if b.meta.records.is_empty() || b.meta.narrowed_uses.is_empty() {
        return;
    }
    let w = WLive::compute(cx.tcx, b, cx.bodies, cx.scc, None);
    let mut writes: BTreeMap<Point, Vec<(FactId, Span)>> = BTreeMap::new();
    for r in &b.meta.records {
        if w.dest_live(r.at, Place::local(r.slot), &[]) {
            writes.entry(r.at).or_default().push((r.fact, r.span));
        }
    }
    let n = Narrow {
        writes,
        tests: b.meta.fact_tests.clone(),
    };
    let res = solve(b, n);
    for &(f, p) in &b.meta.narrowed_uses {
        let Some(&w) = res.before(b, p).get(&f) else {
            continue;
        };
        let fact = &b.meta.facts[f];
        let name = fact_text(cx, fact);
        let what = match fact.fact {
            Fact::NonNull => "be `null`",
            Fact::Case(_) => "no longer be that case",
        };
        let span = match b.stmt_at(p) {
            Some(st) => st.span,
            None => b.blocks[p.block].term.span,
        };
        // S:744: the narrowed path, the writing line, and the note.
        dcx.emit(
            Diagnostic::new(
                Code::EN0401,
                format!("`{name}` may {what} here"),
                span,
                "the test before this may no longer hold",
            )
            .with_secondary(w, "this may write through it")
            .note(format!("a writing reference may have changed `{name}`")),
        );
    }
}

/// A fact's path as the source names it: `h.item`, `h.shape`, `s`; a deref and a
/// nullable's payload print nothing. In an arrow, a path through its capture
/// `*(*_1).k` starts at the variable the capture holds (S:744).
fn fact_text(cx: &BodyCx, fact: &enrang_mir::MirFact) -> String {
    use enrang_hir::{PathStep, TyKind};
    let (tcx, b) = (cx.tcx, cx.body);
    let mut ty = b.locals[fact.root].ty;
    let mut steps = &fact.steps[..];
    let captured = match (b.locals[fact.root].name, steps) {
        (None, [PathStep::Deref, PathStep::Field(f), rest @ ..])
            if fact.root == enrang_mir::Local(1)
                && matches!(b.owner, enrang_mir::BodyOwner::Arrow(..)) =>
        {
            let field = enrang_mir::PlaceTy::of(ty)
                .project(tcx, enrang_mir::Proj::Deref)
                .and_then(|t| t.project(tcx, enrang_mir::Proj::Field(*f)));
            crate::report::capture_name(cx, enrang_base::Idx::index(*f))
                .zip(field)
                .map(|(name, field)| (name, field.ty, rest))
        }
        _ => None,
    };
    let mut out = match (captured, b.locals[fact.root].name) {
        (Some((name, field, rest)), _) => {
            // A capture by reference holds `&x`: its deref is the variable.
            match (tcx.kind(field), rest) {
                (TyKind::Ref(t), [PathStep::Deref, more @ ..]) => {
                    ty = t;
                    steps = more;
                }
                _ => {
                    ty = field;
                    steps = rest;
                }
            }
            name
        }
        (None, Some(s)) => s.to_string(),
        (None, None) => fact.root.to_string(),
    };
    for step in steps {
        // A field is read through any references and payloads before it.
        let mut base = ty;
        while let TyKind::Ref(t) | TyKind::Boxed(t) | TyKind::Nullable(t) = tcx.kind(base) {
            base = t;
        }
        ty = match (step, tcx.kind(ty)) {
            (PathStep::Deref, TyKind::Ref(t) | TyKind::Boxed(t)) => t,
            (PathStep::Payload, TyKind::Nullable(t)) => t,
            (PathStep::Field(f), _) => match tcx.kind(base) {
                TyKind::Adt(adt, args) => {
                    out = format!("{out}.{}", tcx.field_def(adt, None, *f).name);
                    tcx.field_ty(adt, None, *f, args)
                }
                _ => return out,
            },
            _ => ty,
        };
    }
    out
}
