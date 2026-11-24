//! Rebinding a captured reference (S:972, A:1295, N13): an arrow or a local
//! function that assigns a captured reference local itself, `r = &b`, is EN0616
//! at the assignment. Neither can repoint the outer local: an arrow's capture of
//! a reference local is a copy of the reference in its environment (A:971's
//! through-reference lowering), and a local function's hidden argument is a copy
//! too, so the write would change only that copy while the code reads as if `r`
//! changed. Writes through the reference, `*r += 1`, are ordinary captures.

use enrang_base::{Idx, Span, Symbol};
use enrang_diag::{Code, Diagnostic, Help};
use enrang_hir::Tcx;
use enrang_mir::{Body, BodyOwner, CaptureKind, Local, LocalKind, Proj, StatementKind};

/// One rebinding: where, and the captured variable it repoints.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rebind {
    pub span: Span,
    pub name: Symbol,
    /// `Some(f)` inside the local function `f`, `None` inside an arrow.
    pub function: Option<Symbol>,
}

/// Whether a store into `dest` repoints an arrow's copy of a captured reference
/// local, `(*_env).k` of a capture through a reference: EN0616 is its one report
/// (A:1270), and the store changes only the environment's copy, so it is no
/// write through the environment, and the arrow's caller never sees the captured
/// reference written through for it.
pub(crate) fn repoints_capture(b: &Body, dest: enrang_mir::Place) -> bool {
    matches!(b.projs(dest), [Proj::Deref, Proj::Field(k)]
        if b.locals[dest.local].kind == LocalKind::ClosureEnv
            && matches!(b.owner, BodyOwner::Arrow(..))
            && b.captures.get(k.index()).is_some_and(|c| c.kind == CaptureKind::ThroughRef))
}

/// Every rebinding of a captured reference in `b`, in point order.
pub fn check(tcx: &Tcx, b: &Body) -> Vec<Rebind> {
    // The locals and environment fields that hold a captured reference.
    let hidden: Vec<Local> = match b.owner {
        BodyOwner::Fn(d) => crate::r3::hidden(tcx, d, b)
            .into_iter()
            .map(|i| Local(i + 1))
            .collect(),
        _ => Vec::new(),
    };
    let function = match b.owner {
        BodyOwner::Fn(d) => tcx.def(d).name(),
        _ => None,
    };
    let mut out = Vec::new();
    for blk in b.blocks.iter() {
        for st in &blk.stmts {
            let StatementKind::Assign { dest, .. } = &st.kind else {
                continue;
            };
            let name = match b.projs(*dest) {
                // A whole hidden argument of a local function: the variable's
                // own value, a reference (an owned one is written through `*`).
                [] if hidden.contains(&dest.local) => b.locals[dest.local].name,
                // `(*_env).k` of a capture through a reference: the copy of a
                // captured reference local.
                [Proj::Deref, Proj::Field(k)] if repoints_capture(b, *dest) => {
                    b.captures.get(k.index()).map(|c| c.name)
                }
                _ => None,
            };
            if let Some(name) = name {
                out.push(Rebind {
                    span: st.span,
                    name,
                    function: match b.owner {
                        BodyOwner::Arrow(..) => None,
                        _ => function,
                    },
                });
            }
        }
    }
    out
}

/// EN0616 at a rebinding (plan e's choice of head).
pub fn report(r: &Rebind) -> Diagnostic {
    let inside = match r.function {
        Some(f) => format!("`{f}`"),
        None => "the arrow".to_owned(),
    };
    Diagnostic::new(
        Code::EN0616,
        format!("cannot repoint captured `{}` inside {inside}", r.name),
        r.span,
        "repointed here",
    )
    .note(format!(
        "{inside} holds its own copy of the reference `{}`, so the change would not reach the variable outside",
        r.name
    ))
    .with_help(Help::text(format!(
        "return the new reference and assign it to `{}` outside, or write through it with `*{}`",
        r.name, r.name
    )))
}
