//! The dataflow framework (A:795-799; M3 plan b.8): forward and backward analyses
//! over any join semilattice, gen/kill analyses over bit sets as a special case, and
//! a deterministic solver.
//!
//! The solver's worklist starts with every reachable block in reverse postorder
//! (postorder for a backward analysis) and is first in, first out, each block queued
//! at most once at a time. Unreachable blocks keep `bottom`. A `Call`'s destination
//! is written by the terminator transfer and so flows along `next`; there are no
//! unwind edges (A:452). `edge` refines the state along one edge, as a `Switch`
//! arm's facts do.

use std::collections::VecDeque;

use enrang_base::{BitSet, IdVec, Idx};

use crate::body::{Body, Statement, Terminator};
use crate::cfg::Cfg;
use crate::ids::{BlockId, Point};

/// An analysis: a domain with a join, a starting state, and transfer functions.
pub trait DataflowAnalysis {
    type Domain: Clone + Eq;
    const FORWARD: bool;

    /// The least state, held by unreachable blocks and the start of every join.
    fn bottom(&self, b: &Body) -> Self::Domain;
    /// Forward: the state at `bb0`'s start; backward: at the end of every block
    /// with no successor (`Return`, `Unreachable`, a call that returns `never`).
    fn entry(&self, b: &Body) -> Self::Domain;
    /// Joins `from` into `into`; true when `into` changed.
    fn join(&self, into: &mut Self::Domain, from: &Self::Domain) -> bool;
    fn statement(&self, s: &mut Self::Domain, st: &Statement, at: Point);
    fn terminator(&self, s: &mut Self::Domain, t: &Terminator, at: Point);
    /// The effect of taking the edge `from -> to`, after `from`'s terminator.
    fn edge(&self, _s: &mut Self::Domain, _from: BlockId, _to: BlockId) {}
}

/// A solved analysis: the state at each block's start (forward) or end (backward).
pub struct Results<A: DataflowAnalysis> {
    pub analysis: A,
    pub at_block: IdVec<BlockId, A::Domain>,
}

/// Solves `a` over `b` to its least fixpoint.
pub fn solve<A: DataflowAnalysis>(b: &Body, a: A) -> Results<A> {
    let cfg = Cfg::new(b);
    let n = b.blocks.len();
    let mut at_block = IdVec::from_elem(a.bottom(b), n);
    let order: Vec<BlockId> = match A::FORWARD {
        true => cfg.rpo.clone(),
        false => cfg.rpo.iter().rev().copied().collect(),
    };
    if A::FORWARD {
        if n > 0 {
            at_block[BlockId::ENTRY] = a.entry(b);
        }
    } else {
        for &block in &order {
            if b.blocks[block].term.kind.successors().is_empty() {
                at_block[block] = a.entry(b);
            }
        }
    }
    let mut queued = BitSet::new(n);
    let mut work: VecDeque<BlockId> = VecDeque::new();
    for &block in &order {
        queued.insert(block);
        work.push_back(block);
    }
    while let Some(block) = work.pop_front() {
        queued.remove(block);
        let data = &b.blocks[block];
        let mut state = at_block[block].clone();
        if A::FORWARD {
            for (i, st) in data.stmts.iter().enumerate() {
                a.statement(&mut state, st, Point::new(block, i));
            }
            a.terminator(&mut state, &data.term, Point::new(block, data.stmts.len()));
            for s in data.term.kind.successors() {
                if s.index() >= n {
                    continue;
                }
                let mut out = state.clone();
                a.edge(&mut out, block, s);
                if a.join(&mut at_block[s], &out) && queued.insert(s) {
                    work.push_back(s);
                }
            }
        } else {
            a.terminator(&mut state, &data.term, Point::new(block, data.stmts.len()));
            for (i, st) in data.stmts.iter().enumerate().rev() {
                a.statement(&mut state, st, Point::new(block, i));
            }
            for &p in &cfg.preds[block] {
                if !cfg.reachable.contains(p) {
                    continue;
                }
                let mut out = state.clone();
                a.edge(&mut out, p, block);
                if a.join(&mut at_block[p], &out) && queued.insert(p) {
                    work.push_back(p);
                }
            }
        }
    }
    Results {
        analysis: a,
        at_block,
    }
}

impl<A: DataflowAnalysis> Results<A> {
    /// The states of every point of `block`, before and after each, in order.
    fn block_states(&self, b: &Body, block: BlockId) -> Vec<(A::Domain, A::Domain)> {
        let data = &b.blocks[block];
        let a = &self.analysis;
        let count = data.stmts.len() + 1;
        let mut out = Vec::with_capacity(count);
        let mut state = self.at_block[block].clone();
        if A::FORWARD {
            for i in 0..count {
                let before = state.clone();
                match data.stmts.get(i) {
                    Some(st) => a.statement(&mut state, st, Point::new(block, i)),
                    None => a.terminator(&mut state, &data.term, Point::new(block, i)),
                }
                out.push((before, state.clone()));
            }
        } else {
            for i in (0..count).rev() {
                let after = state.clone();
                match data.stmts.get(i) {
                    Some(st) => a.statement(&mut state, st, Point::new(block, i)),
                    None => a.terminator(&mut state, &data.term, Point::new(block, i)),
                }
                out.push((state.clone(), after));
            }
            out.reverse();
        }
        out
    }

    /// The state just before `p` runs, in program order.
    pub fn before(&self, b: &Body, p: Point) -> A::Domain {
        self.block_states(b, p.block)[p.index as usize].0.clone()
    }

    /// The state just after `p` runs, in program order.
    pub fn after(&self, b: &Body, p: Point) -> A::Domain {
        self.block_states(b, p.block)[p.index as usize].1.clone()
    }

    /// Calls `f` at every point, blocks in order then statements, the terminator
    /// last, with the states before and after it.
    pub fn visit(&self, b: &Body, mut f: impl FnMut(Point, &A::Domain, &A::Domain)) {
        for block in b.blocks.indices() {
            for (i, (before, after)) in self.block_states(b, block).iter().enumerate() {
                f(Point::new(block, i), before, after);
            }
        }
    }
}

/// A gen/kill analysis over a bit set: transfers insert (gen) and remove (kill)
/// bits; joins are union, or intersection for a must analysis.
pub trait GenKillAnalysis {
    type Idx: Idx;
    const FORWARD: bool;
    /// Intersection at joins instead of union; `bottom` is then the full set.
    const MUST: bool = false;

    fn domain_size(&self, b: &Body) -> usize;
    /// Adds the starting bits (`entry`) to the empty set.
    fn entry_set(&self, _b: &Body, _set: &mut BitSet<Self::Idx>) {}
    fn statement_effect(&self, set: &mut BitSet<Self::Idx>, st: &Statement, at: Point);
    fn terminator_effect(&self, set: &mut BitSet<Self::Idx>, t: &Terminator, at: Point);
}

/// A gen/kill analysis as a [`DataflowAnalysis`].
pub struct GenKill<A>(pub A);

impl<A: GenKillAnalysis> DataflowAnalysis for GenKill<A> {
    type Domain = BitSet<A::Idx>;
    const FORWARD: bool = A::FORWARD;

    fn bottom(&self, b: &Body) -> BitSet<A::Idx> {
        match A::MUST {
            true => BitSet::full(self.0.domain_size(b)),
            false => BitSet::new(self.0.domain_size(b)),
        }
    }

    fn entry(&self, b: &Body) -> BitSet<A::Idx> {
        let mut set = BitSet::new(self.0.domain_size(b));
        self.0.entry_set(b, &mut set);
        set
    }

    fn join(&self, into: &mut BitSet<A::Idx>, from: &BitSet<A::Idx>) -> bool {
        match A::MUST {
            true => into.intersect(from),
            false => into.union(from),
        }
    }

    fn statement(&self, s: &mut BitSet<A::Idx>, st: &Statement, at: Point) {
        self.0.statement_effect(s, st, at);
    }

    fn terminator(&self, s: &mut BitSet<A::Idx>, t: &Terminator, at: Point) {
        self.0.terminator_effect(s, t, at);
    }
}
