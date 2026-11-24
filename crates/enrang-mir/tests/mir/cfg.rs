//! The CFG tools (M3 plan b.8) on small graphs: predecessors, reverse postorder,
//! reachability, dominators, back edges, natural loops and pre-headers, and
//! whether a point reaches a block again.

use enrang_mir::{BlockId, Body, Cfg, Point};
use enrang_testkit::Harness;

use crate::support::parse;

/// One body whose blocks are `blocks`, each `bbN: { <term>; }`, taking `_1: bool`.
pub fn graph(blocks: &[&str]) -> Body {
    let mut text = String::from("fn g(_1: bool) -> void {\n  let _2: void temp;\n");
    for (i, t) in blocks.iter().enumerate() {
        text.push_str(&format!("  bb{i}: {{\n    {t};\n  }}\n"));
    }
    text.push_str("}\n");
    let (_, mut bodies) = parse(&format!(
        "@declare fn stop() -> never;\n@declare fn work() -> void;\n{text}"
    ));
    bodies.pop().expect("a body")
}

fn bbs(v: &[u32]) -> Vec<BlockId> {
    v.iter().map(|&n| BlockId(n)).collect()
}

const DIAMOND: [&str; 4] = [
    "switch copy _1 [0: bb2, otherwise: bb1]",
    "goto bb3",
    "goto bb3",
    "return",
];

const LOOP: [&str; 4] = [
    "goto bb1",
    "switch copy _1 [0: bb3, otherwise: bb2]",
    "goto bb1",
    "return",
];

/// Two loops, one inside the other, and a block nothing reaches.
const NESTED: [&str; 7] = [
    "goto bb1",
    "switch copy _1 [0: bb5, otherwise: bb2]",
    "switch copy _1 [0: bb4, otherwise: bb3]",
    "goto bb2",
    "goto bb1",
    "return",
    "goto bb5",
];

pub fn register(h: &mut Harness) {
    h.case("cfg/diamond: predecessors, order and dominators", || {
        let b = graph(&DIAMOND);
        let cfg = Cfg::new(&b);
        assert_eq!(cfg.preds[BlockId(3)], bbs(&[1, 2]));
        assert_eq!(cfg.rpo, bbs(&[0, 1, 2, 3]));
        assert_eq!(cfg.idom[BlockId(3)], Some(BlockId(0)));
        assert!(cfg.dominates(BlockId(0), BlockId(3)));
        assert!(!cfg.dominates(BlockId(1), BlockId(3)));
        assert!(cfg.back_edges(&b).is_empty());
        assert!(cfg.loops(&b).is_empty());
    });
    h.case("cfg/a loop: its back edge, blocks and pre-header", || {
        let b = graph(&LOOP);
        let cfg = Cfg::new(&b);
        assert_eq!(cfg.back_edges(&b), [(BlockId(2), BlockId(1))]);
        let loops = cfg.loops(&b);
        assert_eq!(loops.len(), 1);
        assert_eq!(loops[0].head, BlockId(1));
        assert_eq!(loops[0].latches, bbs(&[2]));
        assert_eq!(loops[0].blocks.iter().collect::<Vec<_>>(), bbs(&[1, 2]));
        assert_eq!(loops[0].preheader, Some(BlockId(0)));
        assert!(
            cfg.reaches(&b, Point::new(BlockId(2), 0), BlockId(2)),
            "around the back edge"
        );
        assert!(cfg.reaches(&b, Point::new(BlockId(1), 0), BlockId(1)));
        assert!(!cfg.reaches(&b, Point::new(BlockId(3), 0), BlockId(1)));
        assert!(
            !cfg.reaches(&b, Point::new(BlockId(0), 0), BlockId(0)),
            "no way back to the entry"
        );
    });
    h.case("cfg/nested loops and an unreachable block", || {
        let b = graph(&NESTED);
        let cfg = Cfg::new(&b);
        assert!(!cfg.reachable.contains(BlockId(6)));
        assert!(!cfg.rpo.contains(&BlockId(6)));
        assert_eq!(cfg.idom[BlockId(6)], None);
        assert_eq!(
            cfg.preds[BlockId(5)],
            bbs(&[1, 6]),
            "predecessors list every block"
        );
        assert_eq!(
            cfg.back_edges(&b),
            [(BlockId(3), BlockId(2)), (BlockId(4), BlockId(1))]
        );
        let loops = cfg.loops(&b);
        let heads: Vec<BlockId> = loops.iter().map(|l| l.head).collect();
        assert_eq!(heads, bbs(&[1, 2]));
        assert_eq!(
            loops[0].blocks.iter().collect::<Vec<_>>(),
            bbs(&[1, 2, 3, 4])
        );
        assert_eq!(loops[1].blocks.iter().collect::<Vec<_>>(), bbs(&[2, 3]));
        assert_eq!(loops[1].preheader, Some(BlockId(1)));
        assert!(cfg.dominates(BlockId(2), BlockId(4)));
        assert!(
            !cfg.dominates(BlockId(6), BlockId(5)),
            "an unreachable block dominates nothing"
        );
        assert!(
            !cfg.dominates(BlockId(6), BlockId(6)),
            "nothing dominates an unreachable block, itself included"
        );
    });
    h.case(
        "cfg/a head with two outside predecessors has no pre-header",
        || {
            let b = graph(&[
                "switch copy _1 [0: bb2, otherwise: bb1]",
                "goto bb2",
                "switch copy _1 [0: bb3, otherwise: bb2]",
                "return",
            ]);
            let loops = Cfg::new(&b).loops(&b);
            assert_eq!(loops.len(), 1);
            assert_eq!(loops[0].head, BlockId(2));
            assert_eq!(loops[0].latches, bbs(&[2]), "a self loop");
            assert_eq!(loops[0].preheader, None);
        },
    );
    h.case(
        "cfg/an unreachable block jumping into a loop is outside it",
        || {
            let mut blocks = LOOP.to_vec();
            blocks.push("goto bb1");
            blocks.push("goto bb2");
            let b = graph(&blocks);
            let loops = Cfg::new(&b).loops(&b);
            assert_eq!(loops[0].blocks.iter().collect::<Vec<_>>(), bbs(&[1, 2]));
            assert_eq!(loops[0].preheader, Some(BlockId(0)), "bb4 is no way in");
        },
    );
    h.case("cfg/two arms to one block make one predecessor", || {
        let b = graph(&["switch copy _1 [0: bb1, otherwise: bb1]", "return"]);
        assert_eq!(Cfg::new(&b).preds[BlockId(1)], bbs(&[0]));
    });
    h.case(
        "cfg/calls: `next` is a successor, a call to `never` ends the block",
        || {
            let b = graph(&["_2 = work() -> bb1", "_2 = stop() -> !"]);
            let cfg = Cfg::new(&b);
            assert_eq!(cfg.rpo, bbs(&[0, 1]));
            assert!(Cfg::successors(&b.blocks[BlockId(1)].term).is_empty());
        },
    );
    h.case(
        "cfg/successors: switch arms in order, then otherwise",
        || {
            let b = graph(&[
                "switch copy _1 [1: bb2, 0: bb1, otherwise: bb3]",
                "return",
                "return",
                "return",
            ]);
            assert_eq!(Cfg::successors(&b.blocks[BlockId(0)].term), bbs(&[2, 1, 3]));
            assert_eq!(Cfg::new(&b).rpo, bbs(&[0, 3, 1, 2]));
        },
    );
}
