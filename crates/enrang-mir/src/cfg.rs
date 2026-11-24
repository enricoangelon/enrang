//! CFG tools (M3 plan b.8): predecessors, reverse postorder, reachability,
//! dominators, back edges, natural loops with their pre-headers, and "does this
//! point reach that block again" (EN0611, liveness tests).
//!
//! Everything is deterministic: successors in terminator order (a `Switch`'s arms in
//! order, then `otherwise`), predecessors sorted, the postorder a depth-first walk
//! from `bb0` taking successors in that order.

use enrang_base::{BitSet, IdVec, Idx};

use crate::body::{Body, Terminator};
use crate::ids::{BlockId, Point};

/// A body's control-flow facts, computed once.
#[derive(Clone, Debug)]
pub struct Cfg {
    pub preds: IdVec<BlockId, Vec<BlockId>>,
    /// The reachable blocks in reverse postorder from `bb0`.
    pub rpo: Vec<BlockId>,
    pub reachable: BitSet<BlockId>,
    /// Each reachable block's immediate dominator; `bb0`'s is itself, an
    /// unreachable block's `None`.
    pub idom: IdVec<BlockId, Option<BlockId>>,
    rpo_index: IdVec<BlockId, usize>,
}

/// A natural loop: its head, the blocks whose back edges reach it, its blocks, and
/// its pre-header, the head's one predecessor outside the loop when it has exactly
/// one.
#[derive(Clone, Debug)]
pub struct Loop {
    pub head: BlockId,
    pub latches: Vec<BlockId>,
    pub blocks: BitSet<BlockId>,
    pub preheader: Option<BlockId>,
}

impl Cfg {
    pub fn new(b: &Body) -> Cfg {
        let n = b.blocks.len();
        let mut preds: IdVec<BlockId, Vec<BlockId>> = IdVec::from_elem(Vec::new(), n);
        for (id, block) in b.blocks.iter_enumerated() {
            for s in Cfg::successors(&block.term) {
                if s.index() < n {
                    preds[s].push(id);
                }
            }
        }
        for p in preds.iter_mut() {
            p.sort();
            p.dedup();
        }
        let mut reachable = BitSet::new(n);
        let mut post = Vec::new();
        if n > 0 {
            // An explicit stack of (block, next successor) keeps deep bodies off the
            // native stack.
            let mut stack = vec![(BlockId::ENTRY, 0usize)];
            reachable.insert(BlockId::ENTRY);
            while let Some((block, i)) = stack.pop() {
                let succs = Cfg::successors(&b.blocks[block].term);
                if let Some(&s) = succs.get(i) {
                    stack.push((block, i + 1));
                    if s.index() < n && reachable.insert(s) {
                        stack.push((s, 0));
                    }
                } else {
                    post.push(block);
                }
            }
        }
        let rpo: Vec<BlockId> = post.into_iter().rev().collect();
        let mut rpo_index = IdVec::from_elem(usize::MAX, n);
        for (i, &block) in rpo.iter().enumerate() {
            rpo_index[block] = i;
        }
        let mut cfg = Cfg {
            preds,
            rpo,
            reachable,
            idom: IdVec::from_elem(None, n),
            rpo_index,
        };
        cfg.dominators();
        cfg
    }

    /// The successors of a terminator: `Switch` arms in order, then `otherwise`, a
    /// `Call`'s `next`.
    pub fn successors(t: &Terminator) -> Vec<BlockId> {
        t.kind.successors()
    }

    /// Cooper, Harvey and Kennedy's iterative algorithm over the reverse postorder.
    fn dominators(&mut self) {
        let Some(&entry) = self.rpo.first() else {
            return;
        };
        self.idom[entry] = Some(entry);
        let mut changed = true;
        while changed {
            changed = false;
            for &b in &self.rpo[1..] {
                let mut new: Option<BlockId> = None;
                for &p in &self.preds[b] {
                    if self.idom[p].is_none() {
                        continue;
                    }
                    new = Some(match new {
                        None => p,
                        Some(cur) => self.intersect(p, cur),
                    });
                }
                if new.is_some() && self.idom[b] != new {
                    self.idom[b] = new;
                    changed = true;
                }
            }
        }
    }

    fn intersect(&self, mut a: BlockId, mut b: BlockId) -> BlockId {
        while a != b {
            while self.rpo_index[a] > self.rpo_index[b] {
                a = self.idom[a].expect("a processed block has a dominator");
            }
            while self.rpo_index[b] > self.rpo_index[a] {
                b = self.idom[b].expect("a processed block has a dominator");
            }
        }
        a
    }

    /// Whether `a` dominates `b`; nothing dominates an unreachable block, whose
    /// `idom` is `None`, not even itself.
    pub fn dominates(&self, a: BlockId, b: BlockId) -> bool {
        if !self.reachable.contains(a) {
            return false;
        }
        let mut cur = b;
        loop {
            if cur == a {
                return true;
            }
            match self.idom[cur] {
                Some(d) if d != cur => cur = d,
                _ => return false,
            }
        }
    }

    /// The edges whose target dominates their source, as `(source, target)`, in
    /// block order.
    pub fn back_edges(&self, b: &Body) -> Vec<(BlockId, BlockId)> {
        let mut out = Vec::new();
        for (id, block) in b.blocks.iter_enumerated() {
            if !self.reachable.contains(id) {
                continue;
            }
            for s in Cfg::successors(&block.term) {
                if self.dominates(s, id) {
                    out.push((id, s));
                }
            }
        }
        out
    }

    /// The heads of the natural loops, in block order.
    pub fn loop_heads(&self, b: &Body) -> Vec<BlockId> {
        let mut heads: Vec<BlockId> = self.back_edges(b).into_iter().map(|(_, h)| h).collect();
        heads.sort();
        heads.dedup();
        heads
    }

    /// The natural loops, one per head, in head order: each back edge's loop is the
    /// head and every block that reaches the latch without passing the head.
    pub fn loops(&self, b: &Body) -> Vec<Loop> {
        let edges = self.back_edges(b);
        self.loop_heads(b)
            .into_iter()
            .map(|head| {
                let latches: Vec<BlockId> = edges
                    .iter()
                    .filter(|(_, h)| *h == head)
                    .map(|(s, _)| *s)
                    .collect();
                let mut blocks = BitSet::new(b.blocks.len());
                blocks.insert(head);
                let mut work = latches.clone();
                while let Some(x) = work.pop() {
                    if blocks.insert(x) {
                        work.extend(
                            self.preds[x]
                                .iter()
                                .copied()
                                .filter(|p| self.reachable.contains(*p)),
                        );
                    }
                }
                let outside: Vec<BlockId> = self.preds[head]
                    .iter()
                    .copied()
                    .filter(|p| !blocks.contains(*p) && self.reachable.contains(*p))
                    .collect();
                let preheader = match outside[..] {
                    [one] => Some(one),
                    _ => None,
                };
                Loop {
                    head,
                    latches,
                    blocks,
                    preheader,
                }
            })
            .collect()
    }

    /// Whether control at `from` can come to the start of `to` later: through a
    /// successor of `from`'s block, so `from`'s own block counts only around a cycle.
    pub fn reaches(&self, b: &Body, from: Point, to: BlockId) -> bool {
        let mut seen = BitSet::new(b.blocks.len());
        let mut work = Cfg::successors(&b.blocks[from.block].term);
        while let Some(x) = work.pop() {
            if x.index() >= b.blocks.len() || !seen.insert(x) {
                continue;
            }
            if x == to {
                return true;
            }
            work.extend(Cfg::successors(&b.blocks[x].term));
        }
        false
    }
}
