//! Stage 2D's tests of read-only marks (M3 plan d.3): the marks `MarkResults`
//! gives a slot, the loop a mark came through, and the site each report lands at.
//! The fixtures themselves run in `fixtures.rs`; their flows need only the stub
//! `held` of stage 2E.

use enrang_borrowck::{BodyCx, HeldResults, MarkOrigin, MarkResults, SlotId};
use enrang_mir::{BlockId, Bodies, Local, Point, parse_module};
use enrang_testkit::Harness;

use crate::moves::{fixture, reported};

/// The marks of slot `l` before `p` in body `name` of `text`, the loop of each.
fn marks(text: &str, name: &str, p: Point, l: u32) -> Vec<(MarkOrigin, Option<u32>)> {
    let (tcx, list) = parse_module(text).expect("parsed");
    let bodies: Bodies = list.iter().cloned().map(|b| (b.owner, b)).collect();
    let b = list
        .iter()
        .find(|b| match b.owner {
            enrang_mir::BodyOwner::Fn(d) => tcx.def(d).path.to_string().ends_with(name),
            _ => false,
        })
        .expect("the body");
    let cx = BodyCx::new(&tcx, &bodies, b, None);
    let m = MarkResults::run(&cx, &HeldResults::default());
    m.marks_at(p, SlotId::Local(Local(l)))
        .into_iter()
        .map(|(o, l)| (o, l.map(|l| l.0)))
        .collect()
}

pub fn register(h: &mut Harness) {
    h.case(
        "marks/a `const` root's borrow marks the slot, a `let` one's does not",
        || {
            let text = fixture("marks", "const_root");
            let at = |bb, i| Point::new(BlockId(bb), i);
            assert_eq!(
                marks(&text, "g16", at(0, 3), 3),
                [(MarkOrigin::ConstRoot(Local(2)), None)]
            );
            assert!(marks(&text, "fine", at(1, 1), 2).is_empty(), "`let ys`");
            assert!(
                marks(&text, "fine", at(3, 1), 2).is_empty(),
                "a statement temporary"
            );
            assert_eq!(
                marks(&text, "args", at(0, 4), 4),
                [(MarkOrigin::ConstRoot(Local(2)), None)],
                "a conversion carries the mark"
            );
        },
    );
    h.case(
        "marks/a loop's bind marks via the loop, also in a copy after it",
        || {
            let text = fixture("marks", "loops");
            let k = |name| (name, Point::new(BlockId(4), 0));
            let (_, at) = k("keep");
            let got = marks(&text, "keep", at, 6);
            assert_eq!(got.len(), 1);
            assert!(matches!(got[0], (MarkOrigin::TopConst(_), Some(0))));
            let after = marks(&text, "keep", Point::new(BlockId(6), 1), 1);
            assert!(matches!(after[..], [(MarkOrigin::TopConst(_), Some(0))]));
        },
    );
    h.case(
        "marks/the pre-header makes a mark of its loop plain",
        || {
            let text = fixture("marks", "loops");
            let at = |bb, i| marks(&text, "nested", Point::new(BlockId(bb), i), 2);
            let copied = at(5, 1);
            assert!(matches!(copied[..], [(MarkOrigin::TopConst(_), Some(0))]));
            let preheader = at(2, 0);
            assert!(matches!(preheader[..], [(MarkOrigin::TopConst(_), None)]));
            // At the head this run's mark meets the earlier runs' plain one: plain.
            let after = at(6, 0);
            assert!(matches!(after[..], [(MarkOrigin::TopConst(_), None)]));
        },
    );
    h.case(
        "marks/reports land at the write, the loop's source or the call",
        || {
            let got: Vec<String> = reported(&fixture("marks", "loops"))
                .into_iter()
                .map(|(c, s)| format!("{c} {s}"))
                .collect();
            assert_eq!(
                got,
                [
                    "EN0608 loop l0: once _1 preheader bb0 head bb1 bind bb2[2] binding _5;",
                    "EN0608 loop l0: once _2 preheader bb1 head bb2 bind bb3[2] binding _6;",
                    "EN0608 loop l0: path _2 preheader bb1 head bb2 bind bb3[2] binding _7;",
                ]
            );
            let got = reported(&fixture("marks", "calls"));
            assert_eq!(got[0].0, "EN0608");
            assert_eq!(got[0].1, "_3 = Library::book(move _2, const 1: i64) -> bb2");
            assert_eq!(got[1].0, "EN0614");
            assert_eq!(
                got[2],
                ("EN0608".to_owned(), "(*_1).buf = move _3".to_owned())
            );
            let got = reported(&fixture("marks", "const_root"));
            assert_eq!(
                got[1].1, "_4 = convert(array_to_slice, move _3)",
                "at the argument"
            );
        },
    );
    h.case(
        "marks/a read-only result's own reason wins over a source argument's",
        || {
            let got = reported(&fixture("marks", "readonly"));
            let longest = got
                .iter()
                .find(|(_, s)| s.starts_with("*_6"))
                .expect("the write");
            assert_eq!(longest.0, "EN0616");
        },
    );
}
