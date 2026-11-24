//! Scopes and scheduled drops (A:940; S:1031-1042; M3 plan c.3): the scope stack,
//! each scope's locals and temporaries in creation order, statement temporaries per
//! D2's boundaries, and the exits that run them on the way out, innermost scope
//! first, each scope's entries in reverse.

use enrang_base::Span;
use enrang_hir::LoopId;
use enrang_mir::{BlockId, DropOrigin, Local, Place, StatementKind, TerminatorKind};

use crate::builder::Builder;

/// What opened a scope.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ScopeKind {
    /// The function body: the parameters' drops (S:1032).
    Body,
    /// A `{ }` block.
    Block,
    /// One statement's temporaries (D2).
    Statement,
    /// A loop, the target of `break` and `continue`; `head` is where `continue`
    /// goes, `exit` where `break` goes. It holds nothing itself.
    Loop {
        id: LoopId,
        head: BlockId,
        exit: BlockId,
    },
    /// A `match` arm.
    Arm,
}

/// Where an exit goes.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ExitTarget {
    Return,
    Break(LoopId),
    Continue(LoopId),
}

/// What a scope ends on the way out.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Entry {
    /// A local or temporary: its `Drop` when its type needs one, then its
    /// `StorageDead`.
    Local(Local),
    /// A scheduled `Drop` alone (a parameter, `schedule_drop`).
    Drop(Place),
}

/// One open scope, its entries in creation order (run in reverse), and the span
/// its fall-through exit carries: a block's closing brace, a statement's span.
#[derive(Clone, Debug)]
pub struct Scope {
    pub kind: ScopeKind,
    pub entries: Vec<Entry>,
    pub end: Span,
}

impl Builder<'_> {
    /// Ends `entries` in reverse creation order (plan c.3).
    pub(crate) fn run_exits(&mut self, entries: &[Entry], span: Span) {
        for e in entries.iter().rev() {
            match *e {
                Entry::Local(l) => {
                    if self.cx.tcx.needs_drop(self.body.locals[l].ty) {
                        self.push(StatementKind::Drop(l.into(), DropOrigin::Scope), span);
                    }
                    self.push(StatementKind::StorageDead(l), span);
                }
                Entry::Drop(p) => self.push(StatementKind::Drop(p, DropOrigin::Scope), span),
            }
        }
    }

    /// Leaves for `target`: every scope crossed, innermost first, then `goto` the
    /// loop's exit or continue block, or `return`.
    pub(crate) fn exit(&mut self, target: ExitTarget, span: Span) {
        let found =
            |id: LoopId, s: &Scope| matches!(s.kind, ScopeKind::Loop { id: l, .. } if l == id);
        let (stop, dest) = match target {
            ExitTarget::Return => (0, None),
            ExitTarget::Break(id) | ExitTarget::Continue(id) => {
                let Some(i) = self.scopes.iter().rposition(|s| found(id, s)) else {
                    return;
                };
                let ScopeKind::Loop { head, exit, .. } = self.scopes[i].kind else {
                    unreachable!("a loop scope")
                };
                let to = if matches!(target, ExitTarget::Break(_)) {
                    exit
                } else {
                    head
                };
                (i + 1, Some(to))
            }
        };
        let crossed: Vec<Entry> = self.scopes[stop..]
            .iter()
            .flat_map(|s| s.entries.iter().copied())
            .collect();
        self.run_exits(&crossed, span);
        match dest {
            Some(b) => self.goto(b, span),
            None => self.terminate(TerminatorKind::Return, span),
        }
    }

    /// Registers `l` in the innermost scope: its `Drop` and `StorageDead` run at
    /// the scope's exits.
    pub(crate) fn scope_local(&mut self, l: Local) {
        if let Some(scope) = self.scopes.last_mut()
            && !scope.entries.contains(&Entry::Local(l))
        {
            scope.entries.push(Entry::Local(l));
        }
    }

    /// Runs `f` in a statement temporary scope (D2) ending with `span`.
    pub(crate) fn in_temps<R>(&mut self, span: Span, f: impl FnOnce(&mut Self) -> R) -> R {
        self.open(ScopeKind::Statement, span);
        let r = f(self);
        self.pop_scope();
        r
    }
}
