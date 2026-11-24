//! The dataflow framework (M3 plan b.8) on small graphs with known fixpoints:
//! backward liveness and forward maybe- and must-analyses as gen/kill sets, a
//! constant-propagation lattice, the edge hook forward and backward, a backward
//! entry state at every exit, the per-point replay, unreachable blocks, and
//! determinism.

use std::collections::BTreeSet;

use enrang_base::BitSet;
use enrang_mir::{
    BlockId, Body, ConstKind, DataflowAnalysis, GenKill, GenKillAnalysis, Local, Operand, Point,
    Rvalue, Statement, StatementKind, Terminator, TerminatorKind, solve, statement_places,
    terminator_places,
};
use enrang_testkit::Harness;

use crate::support::parse;

fn body(text: &str) -> Body {
    parse(text).1.pop().expect("a body")
}

fn set(locals: &[u32], n: usize) -> BitSet<Local> {
    let mut s = BitSet::new(n);
    for &l in locals {
        s.insert(Local(l));
    }
    s
}

/// The whole local a statement assigns, if any.
fn assigned(b: &Body, st: &StatementKind) -> Option<Local> {
    match st {
        StatementKind::Assign { dest, .. } if dest.is_local() => Some(dest.local),
        _ => None,
    }
    .filter(|l| l.0 < b.locals.len() as u32)
}

/// Backward liveness of locals: a whole-local assignment kills, every other place
/// reads its local, `return` reads `_0`.
struct Liveness<'b>(&'b Body);

impl GenKillAnalysis for Liveness<'_> {
    type Idx = Local;
    const FORWARD: bool = false;

    fn domain_size(&self, b: &Body) -> usize {
        b.locals.len()
    }

    fn statement_effect(&self, set: &mut BitSet<Local>, st: &Statement, _at: Point) {
        let killed = assigned(self.0, &st.kind);
        if let Some(l) = killed {
            set.remove(l);
        }
        for (i, p) in statement_places(&st.kind).into_iter().enumerate() {
            if !(i == 0 && killed.is_some()) {
                set.insert(p.local);
            }
        }
    }

    fn terminator_effect(&self, set: &mut BitSet<Local>, t: &Terminator, _at: Point) {
        if let TerminatorKind::Call { dest, .. } = &t.kind
            && dest.is_local()
        {
            set.remove(dest.local);
        }
        for p in terminator_places(&t.kind) {
            set.insert(p.local);
        }
        if t.kind == TerminatorKind::Return {
            set.insert(Local::RETURN);
        }
    }
}

/// Forward initialisation of whole locals, the arguments at the entry: a may
/// analysis, or with `MUST` a must analysis.
struct Init<'b, const MUST: bool>(&'b Body);

impl<const M: bool> GenKillAnalysis for Init<'_, M> {
    type Idx = Local;
    const FORWARD: bool = true;
    const MUST: bool = M;

    fn domain_size(&self, b: &Body) -> usize {
        b.locals.len()
    }

    fn entry_set(&self, b: &Body, set: &mut BitSet<Local>) {
        for l in b.args() {
            set.insert(l);
        }
    }

    fn statement_effect(&self, set: &mut BitSet<Local>, st: &Statement, _at: Point) {
        if let Some(l) = assigned(self.0, &st.kind) {
            set.insert(l);
        }
    }

    fn terminator_effect(&self, _set: &mut BitSet<Local>, _t: &Terminator, _at: Point) {}
}

/// A flat constant lattice for one local.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Cp {
    Bottom,
    Const(u128),
    Top,
}

struct ConstProp(Local);

impl DataflowAnalysis for ConstProp {
    type Domain = Cp;
    const FORWARD: bool = true;

    fn bottom(&self, _b: &Body) -> Cp {
        Cp::Bottom
    }

    fn entry(&self, _b: &Body) -> Cp {
        Cp::Top
    }

    fn join(&self, into: &mut Cp, from: &Cp) -> bool {
        let joined = match (*into, *from) {
            (Cp::Bottom, x) | (x, Cp::Bottom) => x,
            (Cp::Const(a), Cp::Const(b)) if a == b => Cp::Const(a),
            _ => Cp::Top,
        };
        let changed = joined != *into;
        *into = joined;
        changed
    }

    fn statement(&self, s: &mut Cp, st: &Statement, _at: Point) {
        if let StatementKind::Assign { dest, value } = &st.kind
            && dest.is_local()
            && dest.local == self.0
        {
            *s = match value {
                Rvalue::Use(Operand::Const(c)) => match c.kind {
                    ConstKind::Value(enrang_hir::ConstValue::Int(v, _)) => Cp::Const(v),
                    _ => Cp::Top,
                },
                _ => Cp::Top,
            };
        }
    }

    fn terminator(&self, _s: &mut Cp, _t: &Terminator, _at: Point) {}
}

/// What a `Switch` on `_1` chose, known only along an arm's edge.
struct Chosen<'b>(&'b Body);

impl DataflowAnalysis for Chosen<'_> {
    type Domain = Cp;
    const FORWARD: bool = true;

    fn bottom(&self, _b: &Body) -> Cp {
        Cp::Bottom
    }

    fn entry(&self, _b: &Body) -> Cp {
        Cp::Top
    }

    fn join(&self, into: &mut Cp, from: &Cp) -> bool {
        ConstProp(Local(0)).join(into, from)
    }

    fn statement(&self, _s: &mut Cp, _st: &Statement, _at: Point) {}

    fn terminator(&self, s: &mut Cp, _t: &Terminator, _at: Point) {
        *s = Cp::Top;
    }

    fn edge(&self, s: &mut Cp, from: BlockId, to: BlockId) {
        if let TerminatorKind::Switch { arms, .. } = &self.0.blocks[from].term.kind
            && let Some((v, _)) = arms.iter().find(|(_, b)| *b == to)
        {
            *s = Cp::Const(*v);
        }
    }
}

/// A backward gen/kill analysis whose exits start with `_3`, which no transfer
/// touches, so it reaches every block that reaches an exit.
struct AtExit;

impl GenKillAnalysis for AtExit {
    type Idx = Local;
    const FORWARD: bool = false;

    fn domain_size(&self, b: &Body) -> usize {
        b.locals.len()
    }

    fn entry_set(&self, _b: &Body, set: &mut BitSet<Local>) {
        set.insert(Local(3));
    }

    fn statement_effect(&self, _set: &mut BitSet<Local>, _st: &Statement, _at: Point) {}

    fn terminator_effect(&self, _set: &mut BitSet<Local>, _t: &Terminator, _at: Point) {}
}

/// Every edge a backward analysis crossed, as `(from, to)` in program order.
struct Edges;

impl DataflowAnalysis for Edges {
    type Domain = BTreeSet<(u32, u32)>;
    const FORWARD: bool = false;

    fn bottom(&self, _b: &Body) -> Self::Domain {
        BTreeSet::new()
    }

    fn entry(&self, _b: &Body) -> Self::Domain {
        BTreeSet::new()
    }

    fn join(&self, into: &mut Self::Domain, from: &Self::Domain) -> bool {
        let before = into.len();
        into.extend(from.iter().copied());
        into.len() != before
    }

    fn statement(&self, _s: &mut Self::Domain, _st: &Statement, _at: Point) {}

    fn terminator(&self, _s: &mut Self::Domain, _t: &Terminator, _at: Point) {}

    fn edge(&self, s: &mut Self::Domain, from: BlockId, to: BlockId) {
        s.insert((from.0, to.0));
    }
}

/// A `return` exit and a `never` call exit, and a block nothing reaches.
const EXITS: &str = "@declare fn stop() -> never;
fn exits(_1: bool) -> void {
  let _2: never temp;
  let _3: void temp;
  bb0: {
    switch copy _1 [0: bb2, otherwise: bb1];
  }
  bb1: {
    return;
  }
  bb2: {
    _2 = stop() -> !;
  }
  bb3: {
    goto bb1;
  }
}
";

const LOOP: &str = "fn live(_1: i64, _2: bool) -> i64 {
  let _3: i64 temp;
  bb0: {
    _3 = copy _1;
    goto bb1;
  }
  bb1: {
    switch copy _2 [0: bb3, otherwise: bb2];
  }
  bb2: {
    _3 = add(copy _3, const 1: i64);
    goto bb1;
  }
  bb3: {
    _0 = copy _3;
    return;
  }
}
";

const DIAMOND: &str = "fn init(_1: bool) -> void {
  let _2: i64 temp;
  let _3: i64 temp;
  bb0: {
    switch copy _1 [0: bb2, otherwise: bb1];
  }
  bb1: {
    _2 = const 1: i64;
    _3 = const 1: i64;
    goto bb3;
  }
  bb2: {
    _2 = const 2: i64;
    goto bb3;
  }
  bb3: {
    return;
  }
  bb4: {
    _3 = const 3: i64;
    goto bb3;
  }
}
";

fn cp_loop(body_stmt: &str) -> Body {
    body(&format!(
        "fn cp(_1: bool) -> void {{
  let _2: i64 temp;
  bb0: {{
    _2 = const 1: i64;
    goto bb1;
  }}
  bb1: {{
    switch copy _1 [0: bb3, otherwise: bb2];
  }}
  bb2: {{
    {body_stmt};
    goto bb1;
  }}
  bb3: {{
    return;
  }}
}}
"
    ))
}

pub fn register(h: &mut Harness) {
    h.case(
        "dataflow/a backward block runs its statements last to first",
        || {
            let b = body(
                "fn order(_1: i64, _2: i64) -> i64 {
  bb0: {
    goto bb1;
  }
  bb1: {
    _1 = copy _2;
    _2 = const 0: i64;
    _0 = add(copy _1, copy _2);
    return;
  }
}
",
            );
            let r = solve(&b, GenKill(Liveness(&b)));
            let n = b.locals.len();
            assert_eq!(
                r.at_block[BlockId(0)],
                set(&[2], n),
                "`_2` is read before it is reset, `_1` is set before it is read"
            );
        },
    );
    h.case(
        "dataflow/liveness around a loop: the known fixpoint",
        || {
            let b = body(LOOP);
            let r = solve(&b, GenKill(Liveness(&b)));
            let n = b.locals.len();
            assert_eq!(r.at_block[BlockId(0)], set(&[2, 3], n));
            assert_eq!(r.at_block[BlockId(1)], set(&[2, 3], n));
            assert_eq!(r.at_block[BlockId(2)], set(&[2, 3], n));
            assert_eq!(
                r.at_block[BlockId(3)],
                set(&[], n),
                "the exit's end is the entry state"
            );
            assert_eq!(r.before(&b, Point::new(BlockId(0), 0)), set(&[1, 2], n));
            assert_eq!(r.before(&b, Point::new(BlockId(3), 0)), set(&[3], n));
            assert_eq!(r.after(&b, Point::new(BlockId(3), 0)), set(&[0], n));
            assert_eq!(r.before(&b, Point::new(BlockId(3), 1)), set(&[0], n));
        },
    );
    h.case(
        "dataflow/maybe and must initialisation over a diamond",
        || {
            let b = body(DIAMOND);
            let n = b.locals.len();
            let may = solve(&b, GenKill(Init::<false>(&b)));
            let must = solve(&b, GenKill(Init::<true>(&b)));
            assert_eq!(may.at_block[BlockId(3)], set(&[1, 2, 3], n));
            assert_eq!(must.at_block[BlockId(3)], set(&[1, 2], n));
            assert_eq!(
                may.at_block[BlockId(4)],
                set(&[], n),
                "an unreachable block keeps bottom"
            );
            assert_eq!(
                must.at_block[BlockId(4)],
                BitSet::full(n),
                "a must analysis's bottom is full"
            );
        },
    );
    h.case(
        "dataflow/constant propagation: one value around a loop, two make top",
        || {
            let same = cp_loop("_2 = const 1: i64");
            let r = solve(&same, ConstProp(Local(2)));
            assert_eq!(r.at_block[BlockId(1)], Cp::Const(1));
            assert_eq!(r.at_block[BlockId(3)], Cp::Const(1));
            let other = cp_loop("_2 = const 2: i64");
            let r = solve(&other, ConstProp(Local(2)));
            assert_eq!(r.at_block[BlockId(1)], Cp::Top);
            assert_eq!(r.at_block[BlockId(2)], Cp::Top);
            let counting = cp_loop("_2 = add(copy _2, const 1: i64)");
            assert_eq!(
                solve(&counting, ConstProp(Local(2))).at_block[BlockId(3)],
                Cp::Top
            );
        },
    );
    h.case("dataflow/the edge hook refines a switch arm only", || {
        let b = body(DIAMOND);
        let r = solve(&b, Chosen(&b));
        assert_eq!(r.at_block[BlockId(2)], Cp::Const(0), "the `0` arm");
        assert_eq!(
            r.at_block[BlockId(1)],
            Cp::Top,
            "`otherwise` learns nothing"
        );
        assert_eq!(r.at_block[BlockId(3)], Cp::Top);
    });
    h.case(
        "dataflow/visit gives every point once, before and after agreeing",
        || {
            let b = body(LOOP);
            let r = solve(&b, GenKill(Liveness(&b)));
            let mut seen = Vec::new();
            r.visit(&b, |p, before, after| {
                assert_eq!(*before, r.before(&b, p));
                assert_eq!(*after, r.after(&b, p));
                seen.push(p);
            });
            let points: usize = b.blocks.iter().map(|bl| bl.stmts.len() + 1).sum();
            assert_eq!(seen.len(), points);
            let mut sorted = seen.clone();
            sorted.sort();
            assert_eq!(seen, sorted, "blocks in order, then statements");
        },
    );
    h.case(
        "dataflow/a backward analysis starts every exit with its entry state",
        || {
            let b = body(EXITS);
            let r = solve(&b, GenKill(AtExit));
            let n = b.locals.len();
            let exit = set(&[3], n);
            assert_eq!(r.at_block[BlockId(1)], exit, "the `return` exit");
            assert_eq!(r.at_block[BlockId(2)], exit, "the `never` call exit");
            assert_eq!(r.at_block[BlockId(0)], exit, "flows back to the entry");
            assert_eq!(r.before(&b, Point::new(BlockId(0), 0)), exit);
            assert_eq!(
                r.at_block[BlockId(3)],
                set(&[], n),
                "unreachable keeps bottom"
            );
        },
    );
    h.case(
        "dataflow/a backward edge hook runs once per edge, from the predecessor",
        || {
            let b = body(EXITS);
            let r = solve(&b, Edges);
            let at = |n: u32| r.at_block[BlockId(n)].iter().copied().collect::<Vec<_>>();
            assert_eq!(at(0), [(0, 1), (0, 2)], "both arms of the switch");
            assert_eq!(at(1), [], "an exit's end crosses no edge");
            assert_eq!(at(3), [], "an unreachable predecessor is not fed");
        },
    );
    h.case("dataflow/solving twice gives the same states", || {
        let b = body(DIAMOND);
        let a = solve(&b, GenKill(Init::<false>(&b)));
        let c = solve(&b, GenKill(Init::<false>(&b)));
        assert!(a.at_block.iter().eq(c.at_block.iter()));
    });
}
