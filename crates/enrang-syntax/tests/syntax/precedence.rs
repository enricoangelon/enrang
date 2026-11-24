//! The operator enums against SPEC 3.5's precedence table.

use std::collections::BTreeSet;

use enrang_syntax::Punct;
use enrang_syntax::ast::{
    ASSIGN_PRECEDENCE, AssignOp, BinOp, CAST_PRECEDENCE, COALESCE_PRECEDENCE, LogOp,
    TERNARY_PRECEDENCE,
};
use enrang_testkit::Harness;

use crate::support::{backticked, doc, section};

/// One row of the table: its level, the operators it lists, and its associativity.
struct Level {
    prec: u8,
    ops: Vec<String>,
    assoc: String,
}

fn table() -> Vec<Level> {
    let text = section(doc("SPEC.md"), "### 3.5 Operator precedence");
    let mut levels = Vec::new();
    for line in text.lines() {
        // A `|` inside a cell is written `\|`.
        let cells: Vec<String> = line
            .replace("\\|", "\u{0}")
            .split('|')
            .map(|cell| cell.replace('\u{0}', "|").trim().to_owned())
            .collect();
        let Some(prec) = cells.get(1).and_then(|cell| cell.parse::<u8>().ok()) else {
            continue;
        };
        levels.push(Level {
            prec,
            ops: backticked(&cells[2]),
            assoc: cells[3].clone(),
        });
    }
    assert_eq!(levels.len(), 17, "SPEC 3.5 has 17 levels");
    levels
}

fn level(prec: u8) -> Level {
    table()
        .into_iter()
        .find(|level| level.prec == prec)
        .unwrap_or_else(|| panic!("no level {prec}"))
}

pub fn register(h: &mut Harness) {
    h.case("precedence/each binary operator is at its level", || {
        for &op in BinOp::ALL {
            let row = level(op.precedence());
            assert!(row.ops.contains(&op.as_str().to_owned()), "{op:?}");
        }
    });
    h.case(
        "precedence/levels 4 to 11 hold binary operators only",
        || {
            for row in table()
                .into_iter()
                .filter(|row| (4..=11).contains(&row.prec))
            {
                for spelled in &row.ops {
                    let punct = Punct::from_name(spelled).expect("a punctuator");
                    let op = BinOp::from_punct(punct).expect("a binary operator");
                    assert_eq!(op.precedence(), row.prec, "{spelled}");
                }
            }
        },
    );
    h.case(
        "precedence/comparisons are the levels that do not associate",
        || {
            for &op in BinOp::ALL {
                let row = level(op.precedence());
                assert_eq!(op.is_comparison(), row.assoc == "none", "{op:?}");
            }
        },
    );
    h.case("precedence/&& and || are levels 12 and 13", || {
        for op in [LogOp::And, LogOp::Or] {
            let row = level(op.precedence());
            assert_eq!(row.ops, [op.as_str()]);
            let punct = Punct::from_name(op.as_str()).expect("a punctuator");
            assert_eq!(LogOp::from_punct(punct), Some(op));
        }
    });
    h.case("precedence/the other levels", || {
        assert_eq!(level(COALESCE_PRECEDENCE).ops, ["??"]);
        assert_eq!(level(COALESCE_PRECEDENCE).assoc, "right");
        assert_eq!(level(TERNARY_PRECEDENCE).ops, ["? :"]);
        assert_eq!(level(CAST_PRECEDENCE).ops, ["as"]);
        let assign: BTreeSet<String> = level(ASSIGN_PRECEDENCE).ops.into_iter().collect();
        let ours: BTreeSet<String> = AssignOp::ALL
            .iter()
            .map(|op| op.as_str().to_owned())
            .collect();
        assert_eq!(ours, assign);
        assert_eq!(level(ASSIGN_PRECEDENCE).assoc, "right");
    });
    h.case(
        "precedence/assignment operators come from their punctuators",
        || {
            for &op in AssignOp::ALL {
                let punct = Punct::from_name(op.as_str()).expect("a punctuator");
                assert_eq!(AssignOp::from_punct(punct), Some(op));
                assert_eq!(BinOp::from_punct(punct), None, "{op:?}");
            }
        },
    );
    h.case("precedence/no punctuator is two kinds of operator", || {
        for &p in Punct::ALL {
            let kinds = [
                BinOp::from_punct(p).is_some(),
                LogOp::from_punct(p).is_some(),
                AssignOp::from_punct(p).is_some(),
            ];
            assert!(kinds.iter().filter(|&&k| k).count() <= 1, "{p:?}");
        }
    });
}
