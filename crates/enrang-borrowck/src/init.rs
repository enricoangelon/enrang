//! `MaybeInit` and `MaybeUninit` over move paths (A:989; M3 plan d.1; owner 2D),
//! forward, union at joins, through `enrang_mir::dataflow`. An `Assign` inits its
//! path and the children, a `Move` uninits them, `StorageLive`, `StorageDead` and
//! `Drop` uninit, a call inits its destination on the `next` edge, and the
//! receivers of `MoveData::effects` add theirs. A `Move` recorded as an
//! assignment's kept value is not applied (EN0621). Entry: the arguments init,
//! every other local uninit; in a constructor `super` and the fields of `this`
//! uninit, those a class below may override maybe-init (A:1003).

use enrang_base::{BitSet, IdVec};
use enrang_mir::{
    BlockId, Body, Callee, GenKill, GenKillAnalysis, Local, Operand, Point, Rvalue, Statement,
    StatementKind, Terminator, TerminatorKind, solve,
};

use crate::movepaths::{Effect, MoveData, MovePathIdx};

/// The init states at each block's start.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct InitResults {
    pub maybe_init: IdVec<BlockId, BitSet<MovePathIdx>>,
    pub maybe_uninit: IdVec<BlockId, BitSet<MovePathIdx>>,
}

/// The operands an rvalue reads.
pub(crate) fn operands(v: &Rvalue) -> Vec<&Operand> {
    match v {
        Rvalue::Use(a)
        | Rvalue::Unary(_, a)
        | Rvalue::CheckedNeg(a)
        | Rvalue::Cast(_, a, _)
        | Rvalue::Convert(_, a) => vec![a],
        Rvalue::Binary(_, a, b) | Rvalue::Checked(_, a, b) => vec![a, b],
        Rvalue::Aggregate(_, ops) => ops.iter().collect(),
        _ => Vec::new(),
    }
}

/// The operands a point reads, a call's callee operand included.
pub(crate) fn point_operands(b: &Body, p: Point) -> Vec<&Operand> {
    match b.stmt_at(p).map(|s| &s.kind) {
        Some(StatementKind::Assign { value, .. }) => operands(value),
        Some(StatementKind::FieldInit { value, .. }) => vec![value],
        Some(StatementKind::CheckBounds { index, len }) => vec![index, len],
        Some(StatementKind::Intrinsic { args, .. } | StatementKind::HostCall { args, .. }) => {
            args.iter().collect()
        }
        Some(StatementKind::Asm(a)) => a.ins.iter().map(|(_, o)| o).collect(),
        Some(_) => Vec::new(),
        None => match &b.blocks[p.block].term.kind {
            TerminatorKind::Call { callee, args, .. } => {
                let mut ops: Vec<&Operand> = match callee {
                    Callee::FnPtr(o) | Callee::Virtual { table: o, .. } => vec![o],
                    _ => Vec::new(),
                };
                ops.extend(args);
                ops
            }
            TerminatorKind::Switch { value, .. } => vec![value],
            _ => Vec::new(),
        },
    }
}

/// The places a point writes whole: destinations, a field initialiser's field,
/// `asm` outputs.
pub(crate) fn point_dests(b: &Body, p: Point) -> Vec<enrang_mir::Place> {
    match b.stmt_at(p).map(|s| &s.kind) {
        Some(
            StatementKind::Assign { dest, .. }
            | StatementKind::FieldInit { field: dest, .. }
            | StatementKind::Intrinsic {
                dest: Some(dest), ..
            }
            | StatementKind::HostCall {
                dest: Some(dest), ..
            },
        ) => vec![*dest],
        Some(StatementKind::Asm(a)) => a.outs.iter().filter_map(|(_, o)| *o).collect(),
        Some(_) => Vec::new(),
        None => match &b.blocks[p.block].term.kind {
            TerminatorKind::Call { dest, .. } => vec![*dest],
            _ => Vec::new(),
        },
    }
}

/// What point `p` does to the init states, in order.
pub(crate) fn effects(b: &Body, md: &MoveData, p: Point) -> Vec<(MovePathIdx, Effect)> {
    let exact = |pl: &enrang_mir::Place| md.lookup.get(pl).filter(|x| x.1).map(|x| x.0);
    let kept = b.meta.assign_values.contains(&p);
    let mut out: Vec<(MovePathIdx, Effect)> = Vec::new();
    for op in point_operands(b, p) {
        if let Operand::Move(pl) = op
            && !kept
            // A move out of a constructor's `this` is EN0603, and one out of a
            // class with a destructor EN0607: reported, not applied.
            && !(md.ctor_fields.is_some() && pl.local == Local(1))
            && !md.dtor_moves.contains(pl)
            && let Some(m) = exact(pl)
        {
            out.push((m, Effect::Move));
        }
    }
    match b.stmt_at(p).map(|s| &s.kind) {
        Some(StatementKind::StorageLive(l) | StatementKind::StorageDead(l)) => {
            out.push((md.root(*l), Effect::Kill));
        }
        Some(StatementKind::Drop(pl, _) | StatementKind::DropGlue(pl)) => {
            out.extend(exact(pl).map(|m| (m, Effect::Kill)));
        }
        _ => {}
    }
    for d in point_dests(b, p) {
        out.extend(exact(&d).map(|m| (m, Effect::Init)));
    }
    out.extend(md.effects.get(&p).into_iter().flatten().copied());
    out
}

/// Applies one effect to a `MaybeInit` (`uninit` false) or `MaybeUninit` set.
pub(crate) fn apply(
    md: &MoveData,
    set: &mut BitSet<MovePathIdx>,
    n: MovePathIdx,
    e: Effect,
    uninit: bool,
) {
    let on = (e == Effect::Init) != uninit;
    for m in md.subtree(n) {
        match on {
            true => set.insert(m),
            false => set.remove(m),
        };
    }
}

/// The states at entry: (`MaybeInit`, `MaybeUninit`).
pub(crate) fn entry(b: &Body, md: &MoveData) -> (BitSet<MovePathIdx>, BitSet<MovePathIdx>) {
    let n = md.paths.len();
    let mut init = BitSet::new(n);
    for l in b.args() {
        apply(md, &mut init, md.root(l), Effect::Init, false);
    }
    let fields = md.ctor_fields.iter().flatten();
    for f in fields.clone() {
        init.remove(f.1);
    }
    let mut uninit = BitSet::full(n);
    uninit.subtract(&init);
    for f in fields.filter(|f| f.3) {
        init.insert(f.1);
    }
    (init, uninit)
}

struct Flow<'a> {
    b: &'a Body,
    md: &'a MoveData,
    uninit: bool,
}

impl GenKillAnalysis for Flow<'_> {
    type Idx = MovePathIdx;
    const FORWARD: bool = true;

    fn domain_size(&self, _b: &Body) -> usize {
        self.md.paths.len()
    }

    fn entry_set(&self, b: &Body, set: &mut BitSet<MovePathIdx>) {
        let (i, u) = entry(b, self.md);
        set.union(if self.uninit { &u } else { &i });
    }

    fn statement_effect(&self, set: &mut BitSet<MovePathIdx>, _st: &Statement, at: Point) {
        for (n, e) in effects(self.b, self.md, at) {
            apply(self.md, set, n, e, self.uninit);
        }
    }

    fn terminator_effect(&self, set: &mut BitSet<MovePathIdx>, _t: &Terminator, at: Point) {
        self.statement_effect(set, &Statement::new(StatementKind::Nop, self.b.span), at);
    }
}

impl InitResults {
    /// Solves both analyses; empty for a `MoveData` not built yet.
    pub fn compute(b: &Body, moves: &MoveData) -> InitResults {
        if moves.lookup.is_empty() {
            return InitResults::default();
        }
        let run = |uninit| {
            solve(
                b,
                GenKill(Flow {
                    b,
                    md: moves,
                    uninit,
                }),
            )
            .at_block
        };
        InitResults {
            maybe_init: run(false),
            maybe_uninit: run(true),
        }
    }

    /// Calls `f` before every point, blocks then statements, with the states
    /// (`MaybeInit`, `MaybeUninit`) there.
    pub fn replay(
        &self,
        b: &Body,
        md: &MoveData,
        mut f: impl FnMut(Point, &BitSet<MovePathIdx>, &BitSet<MovePathIdx>),
    ) {
        for (bb, block) in b.blocks.iter_enumerated() {
            let (mut i, mut u) = (self.maybe_init[bb].clone(), self.maybe_uninit[bb].clone());
            for idx in 0..=block.stmts.len() {
                let p = Point::new(bb, idx);
                f(p, &i, &u);
                for (n, e) in effects(b, md, p) {
                    apply(md, &mut i, n, e, false);
                    apply(md, &mut u, n, e, true);
                }
            }
        }
    }
}

/// Whether `n`, an ancestor, or (for a whole place) a descendant may be uninit.
pub(crate) fn unset(
    md: &MoveData,
    u: &BitSet<MovePathIdx>,
    n: MovePathIdx,
    whole: bool,
) -> Option<MovePathIdx> {
    let mut cur = Some(n);
    while let Some(c) = cur {
        if u.contains(c) {
            return Some(c);
        }
        cur = md.paths[c].parent;
    }
    whole
        .then(|| md.subtree(n).into_iter().find(|&d| u.contains(d)))
        .flatten()
}
