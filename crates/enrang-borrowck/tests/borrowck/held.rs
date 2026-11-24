//! Stage 2E's tests of slots, loans, keys and `held` (M3 plan d.4-d.5): each
//! fixture under `tests/mir/borrowck/held/` also runs through the fixture runner;
//! here its sets are read at named points. Keys print as `L3` (a site loan, `@t`
//! this turn, `@e` an earlier turn of this run, `@r` an earlier run), `P0`, `F0`,
//! `R0` (a parameter's keys), `H0` (a hold); `?` marks a bare key, `^0` a mark via
//! loop 0's bind.

use std::path::PathBuf;

use enrang_borrowck::{BodyCx, HeldResults, LoanKey, Set, SlotId, Turn};
use enrang_hir::Tcx;
use enrang_mir::{BlockId, Bodies, Body, Local, Point, parse_module};
use enrang_testkit::Harness;

/// A parsed fixture.
pub struct Fx {
    pub tcx: Tcx,
    pub bodies: Bodies,
}

pub fn fixture(area: &str, name: &str) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/mir/borrowck")
        .join(area)
        .join(format!("{name}.mir"));
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

impl Fx {
    pub fn new(text: &str) -> Fx {
        let (tcx, list) = parse_module(text).unwrap_or_else(|e| panic!("{e}"));
        Fx {
            tcx,
            bodies: list.into_iter().map(|b| (b.owner, b)).collect(),
        }
    }

    pub fn load(area: &str, name: &str) -> Fx {
        Fx::new(&fixture(area, name))
    }

    pub fn body(&self, name: &str) -> &Body {
        self.bodies
            .values()
            .find(|b| match b.owner {
                enrang_mir::BodyOwner::Fn(d) => self
                    .tcx
                    .def(d)
                    .path
                    .segments
                    .last()
                    .is_some_and(|s| s.as_str() == name),
                _ => false,
            })
            .unwrap_or_else(|| panic!("no body `{name}`"))
    }

    pub fn cx(&self, name: &str) -> BodyCx<'_> {
        BodyCx::new(&self.tcx, &self.bodies, self.body(name), None)
    }

    /// The solved `held` of body `name`.
    pub fn held(&self, name: &str) -> (BodyCx<'_>, HeldResults) {
        let cx = self.cx(name);
        let h = HeldResults::run(&cx, false);
        (cx, h)
    }
}

/// The local a `// name` comment names.
pub fn local(b: &Body, name: &str) -> SlotId {
    b.locals
        .iter_enumerated()
        .find(|(_, d)| d.name.is_some_and(|n| n.as_str() == name))
        .map(|(l, _)| SlotId::Local(l))
        .unwrap_or_else(|| panic!("no local `{name}`"))
}

pub fn pt(block: u32, index: usize) -> Point {
    Point::new(BlockId(block), index)
}

pub fn l(i: u32) -> SlotId {
    SlotId::Local(Local(i))
}

/// A set as the module doc prints it, keys in order.
pub fn show(s: &Set) -> String {
    let mut out = Vec::new();
    for (k, b) in s {
        let mut t = match k {
            LoanKey::Site(l, turn) => format!(
                "L{}{}",
                l.0,
                match turn {
                    Turn::Any => "",
                    Turn::This => "@t",
                    Turn::EarlierThisRun => "@e",
                    Turn::EarlierRuns => "@r",
                }
            ),
            LoanKey::Param(i) => format!("P{i}"),
            LoanKey::Fields(i) => format!("F{i}"),
            LoanKey::RFields(i) => format!("R{i}"),
            LoanKey::Hold(l) => format!("H{}", l.0),
        };
        if b.bare {
            t.push('?');
        }
        if let Some(m) = b.mark {
            t.push_str(&format!("^{}", m.0));
        }
        out.push(t);
    }
    out.join(" ")
}

/// `held`, `fields`, `rfields` (and `wfields` when not empty) of `s` before `p`.
pub fn sets(h: &HeldResults, p: Point, s: SlotId) -> String {
    let mut out = format!(
        "{} | {} | {}",
        show(&h.held_at(p, s)),
        show(&h.fields_at(p, s)),
        show(&h.rfields_at(p, s))
    );
    let w = h.wfields_at(p, s);
    if !w.is_empty() {
        out.push_str(&format!(" | {}", show(&w)));
    }
    out
}

/// The loan table, one `L<id>=<path>@<site>:<kind>` per loan.
pub fn loans(cx: &BodyCx) -> Vec<String> {
    cx.loans
        .table
        .iter_enumerated()
        .map(|(id, l)| {
            let steps: Vec<String> = l.path.steps.iter().map(|s| format!("{s:?}")).collect();
            format!(
                "L{}={}{}{}{}@{}:{:?}",
                id.0,
                if l.path.through_ref { "*" } else { "" },
                l.path.root,
                if steps.is_empty() { "" } else { "." },
                steps.join("."),
                l.site,
                l.kind
            )
        })
        .collect()
}

/// Asserts `sets` of each `(body, point, slot, want)` of one fixture.
pub fn expect(area: &str, file: &str, rows: &[(&str, Point, &str, &str)]) {
    let fx = Fx::load(area, file);
    for (name, p, slot, want) in rows {
        let (cx, h) = fx.held(name);
        let s = match *slot {
            "_0" => l(0),
            "hold" => SlotId::Hold(enrang_hir::LoopId(0)),
            n if n.starts_with("caller") => SlotId::Caller(n[6..].parse().expect("an index")),
            n if n.starts_with('_') => l(n[1..].parse().expect("a local")),
            n => local(cx.body, n),
        };
        assert_eq!(sets(&h, *p, s), *want, "{name} at {p}, {slot}");
    }
}

/// The diagnostics `check` reports on fixture `text`, as `line:code` pairs.
pub fn codes(text: &str) -> Vec<String> {
    let rendered = crate::fixtures::run(text);
    enrang_testkit::reported(&rendered)
        .iter()
        .map(|r| format!("{}:{}", r.line().unwrap_or(0), r.code))
        .collect()
}

pub fn register(h: &mut Harness) {
    h.case(
        "held/slots: kinds, holds and caller slots, none for an Own `this` (A:1036)",
        || {
            let fx = Fx::load("held", "rows-ref");
            let kinds = |name: &str| -> Vec<String> {
                let cx = fx.cx(name);
                cx.slots
                    .list
                    .iter()
                    .map(|(s, k)| format!("{s:?}:{k:?}"))
                    .collect()
            };
            assert_eq!(
                kinds("own"),
                [
                    "Local(Local(0)):Plain",
                    "Local(Local(1)):PtrBorrowing",
                    "Local(Local(3)):ValueBorrowing",
                    "Local(Local(4)):PtrBorrowing",
                    "Caller(0):Plain",
                    "Caller(3):Plain",
                ],
                "`n: isize` holds nothing; `h: &Copier | null` has a caller slot"
            );
            let fx = Fx::load("held", "rows-use");
            let cx = fx.cx("take");
            assert!(!cx.slots.has(SlotId::Caller(0)), "a `move` method's `this`");
            let fx = Fx::load("loops", "holds");
            assert!(fx.cx("g21").slots.has(SlotId::Hold(enrang_hir::LoopId(0))));
            let fx = Fx::load("loops", "tk03");
            assert!(
                !fx.cx("tail")
                    .slots
                    .list
                    .iter()
                    .any(|(s, _)| matches!(s, SlotId::Hold(_))),
                "a once source has no hold"
            );
        },
    );
    h.case(
        "held/loans: the normal form of each crossing (A:1028-1034)",
        || {
            let fx = Fx::load("held", "rows-ref");
            assert_eq!(
                loans(&fx.cx("own")),
                ["L0=*_1.Field(FieldIdx(2))@bb0[0]:Site"]
            );
            assert_eq!(
                loans(&fx.cx("rd")),
                ["L0=*_1.Fields.Field(FieldIdx(0)).Elem@bb0[2]:Site"],
                "through `*t` and a field, whose step stays (plan d.14)"
            );
            assert_eq!(
                loans(&fx.cx("loc")),
                [
                    "L0=*_1@bb0[1]:Site",
                    "L1=*_2@bb0[2]:Site",
                    "L2=_4@bb1[4]:Site",
                    "L3=*_4.Field(FieldIdx(0)).Elem@bb1[7]:Site",
                ],
                "through a local's field the field step stays (plan d.14)"
            );
            let fx = Fx::load("held", "stores");
            let arrow = fx
                .bodies
                .values()
                .find(|b| matches!(b.owner, enrang_mir::BodyOwner::Arrow(..)))
                .expect("the arrow");
            let cx = BodyCx::new(&fx.tcx, &fx.bodies, arrow, None);
            assert_eq!(
                loans(&cx),
                ["L0=*_2@bb0[0]:Site", "L1=*_1.Capture(0)@bb0[1]:Site"],
                "inside an arrow"
            );
            let fx = Fx::load("held", "rows-use");
            assert_eq!(
                loans(&fx.cx("ncopy")),
                ["L0=*_1@bb0[1]:Payload"],
                "a nullable copy's payload"
            );
            assert_eq!(
                loans(&fx.cx("fcopy")),
                ["L0=*_1.Fields.Field(FieldIdx(1))@bb0[0]:Copy"],
                "a field copy's, the field's step kept"
            );
            assert_eq!(
                loans(&fx.cx("tcopy"))[..2],
                [
                    "L0=*_1.Field(FieldIdx(0))@bb0[1]:Part([0])",
                    "L1=*_1.Field(FieldIdx(1))@bb0[1]:Part([1])"
                ],
                "a tuple copy's, one per part"
            );
            let fx = Fx::load("loops", "holds");
            assert_eq!(
                loans(&fx.cx("retarget"))[..3],
                [
                    "L0=*_1.Fields.Field(FieldIdx(0))@bb0[2]:Hold(LoopId(0))",
                    "L1=_1@bb0[2]:HoldCrossing(LoopId(0))",
                    "L2=*_1.Field(FieldIdx(0))@bb0[2]:HoldCrossing(LoopId(0))",
                ],
                "a hold, and a shared loan on the slot and on the field it crosses"
            );
        },
    );
    h.case("held/entry: each parameter's keys, bare (A:1038)", || {
        expect(
            "held",
            "rows-ref",
            &[
                ("own", pt(0, 0), "_1", "P0? F0? R0? | F0? R0? | R0?"),
                ("own", pt(0, 0), "_3", "P2? | P2? | P2? | P2?"),
                ("own", pt(0, 0), "_4", "P3? F3? R3? | F3? R3? | R3?"),
            ],
        );
    });
    h.case(
        "held/Ref: `&this.own` keeps the key of `this` and no key of its fields",
        || {
            expect(
                "held",
                "rows-ref",
                &[("own", pt(0, 1), "_0", "L0 P0 | L0 P0? | L0 P0?")],
            );
        },
    );
    h.case(
        "held/Ref: through a `readonly &` field only the read set",
        || {
            expect(
                "held",
                "rows-ref",
                &[
                    ("rd", pt(0, 3), "_0", "L0 R0 | L0 R0? | L0 R0?"),
                    ("wr", pt(0, 3), "_0", "L0 F0 R0 | L0 F0? R0? | L0 F0? R0?"),
                    ("loc", pt(1, 8), "_11", "L3 P0? | L3 P0? | L3 P0?"),
                ],
            );
        },
    );
    h.case(
        "held/Ref: `&lx` keeps what `lx` holds, its read set beside",
        || {
            expect(
                "held",
                "rows-ref",
                &[
                    ("loc", pt(1, 3), "w", "L1 P0? P1 | L1 P0? P1 | P0? | L1 P1"),
                    ("loc", pt(1, 5), "r", "L1 L2 P0? P1 | L1 P0? P1 | P0?"),
                ],
            );
        },
    );
    h.case(
        "held/Ref: N4 gives a copy of a reference no loan when nothing writes",
        || {
            expect(
                "held",
                "rows-ref",
                &[("whole", pt(0, 1), "_2", "P0? F0? R0? | F0? R0? | R0?")],
            );
            expect(
                "held",
                "rows-use",
                &[("conv", pt(0, 2), "_0", "P0? | P0? | P0?")],
            );
        },
    );
    h.case(
        "held/Use: copies out of a field take a loan through the value",
        || {
            expect(
                "held",
                "rows-use",
                &[
                    (
                        "fcopy",
                        pt(0, 1),
                        "_0",
                        "L0 F0 R0 | L0 F0? R0? | L0 F0? R0?",
                    ),
                    ("fcopyRo", pt(0, 1), "_0", "L0 R0 | L0 R0? | L0 R0?"),
                ],
            );
        },
    );
    h.case(
        "held/Use: a tuple copy, a nullable copy, `*t`, a move out of `this`",
        || {
            expect(
                "held",
                "rows-use",
                &[
                    ("tcopy", pt(0, 3), "_0", "P0? | P0? | P0? | P0?"),
                    ("ncopy", pt(0, 2), "c", "L0 P0 |  | "),
                    (
                        "lexCopy",
                        pt(0, 1),
                        "_0",
                        "F0? R0? | F0? R0? | R0? | F0? R0?",
                    ),
                    ("take", pt(0, 1), "_0", "F0? R0? | F0? R0? | R0? | F0? R0?"),
                    ("wrap", pt(0, 2), "_0", "P0? | P0? | P0?"),
                    ("unwrap", pt(0, 2), "_0", "P0? |  | "),
                    ("pair", pt(0, 3), "_0", "P0? P1? | P0? P1? |  | P0? P1?"),
                ],
            );
        },
    );
    h.case(
        "held/covered keys: TK-01-copy-join, -pick-param, -repoint, -owned-fields, -pick",
        || {
            expect(
                "held",
                "tk01",
                &[
                    (
                        "lanes",
                        pt(3, 0),
                        "second",
                        "L1 L2 P0? | L1 L2 P0? | L1 L2 P0?",
                    ),
                    ("pick", pt(3, 0), "q", "L1 P0? | L1 P0? | L1 P0?"),
                    ("repoint", pt(0, 5), "k", "L0 P0 | L0 P0? | L0 P0?"),
                    ("repoint", pt(0, 9), "k", "P0? | P0? | P0?"),
                    ("repoint", pt(0, 9), "_1", "P0? | P0? | P0?"),
                    ("both", pt(0, 2), "_2", "L0 P0 | L0 P0? | L0 P0?"),
                    ("both", pt(0, 2), "_3", "L1 P0 | L1 P0? | L1 P0?"),
                    (
                        "pickView",
                        pt(3, 0),
                        "p",
                        "L0 L1 P0 F0 R0 | L0 L1 P0? F0? R0? | L0 L1 P0? F0? R0?",
                    ),
                ],
            );
        },
    );
    h.case(
        "held/turn keys: renames at the bind and the pre-header, marks (TK-03)",
        || {
            expect(
                "loops",
                "tk03",
                &[
                    (
                        "markLiteral",
                        pt(4, 0),
                        "x",
                        "L3@t P0^0 | L3@t P0?^0 | L3@t P0?^0",
                    ),
                    (
                        "markLiteral",
                        pt(4, 4),
                        "t",
                        "L3@t P0? | L3@t P0? |  | L3@t P0?",
                    ),
                    (
                        "staleRuns",
                        pt(5, 2),
                        "keep",
                        "L3@t P0^0 | L3@t P0^0 | L3@t P0^0",
                    ),
                    (
                        "staleRuns",
                        pt(5, 0),
                        "keep",
                        "L0 L3@e L3@r P0 | L0 L3@e L3@r P0 | L0 L3@e L3@r P0",
                    ),
                    (
                        "staleRuns",
                        pt(2, 0),
                        "keep",
                        "L0 L3@t L3@r P0 | L0 L3@t L3@r P0 | L0 L3@t L3@r P0",
                    ),
                    (
                        "staleRuns",
                        pt(2, 1),
                        "keep",
                        "L0 L3@r P0 | L0 L3@r P0 | L0 L3@r P0",
                    ),
                    (
                        "innerPair",
                        pt(4, 0),
                        "x",
                        "L4@t L4@e P0?^0 P1?^0 | L4@t L4@e P0?^0 P1?^0 | L4@t L4@e P0?^0 P1?^0",
                    ),
                    (
                        "tail",
                        pt(4, 0),
                        "x",
                        "L1@t P0?^0 | L1@t P0?^0 | L1@t P0?^0",
                    ),
                    (
                        "markJoin",
                        pt(6, 3),
                        "y",
                        "L3@t^1 L7@t P0^1 | L3@t^1 L7@t P0^1 | L3@t^1 L7@t P0^1",
                    ),
                    (
                        "markJoin",
                        pt(5, 0),
                        "keep",
                        "L3@t L4 L7@t L7@e P0 | L3@t L4 L7@t L7@e P0 | L3@t L4 L7@t L7@e P0",
                    ),
                ],
            );
        },
    );
    h.case(
        "held/the hold: its loan and the shared loans of what its path crosses",
        || {
            expect(
                "loops",
                "tk03",
                &[("markLiteral", pt(2, 0), "hold", "L2 H0 |  | ")],
            );
            expect(
                "loops",
                "holds",
                &[("retarget", pt(1, 0), "hold", "L1 L2 H0 |  | ")],
            );
        },
    );
    h.case(
        "held/call results: `through_fields` and `through_read` (A:1150, A:1215)",
        || {
            expect(
                "access",
                "d-rows",
                &[
                    ("core7", pt(2, 2), "_12", "L4 P0? | P0? | P0?"),
                    ("core7", pt(3, 0), "a", "P0? | P0? | P0?"),
                    ("peek", pt(2, 0), "_0", "P0? | P0? | P0?"),
                    ("peek", pt(2, 0), "c", "L1 P0? P1 | L1 P0? P1 | P0? | L1 P1"),
                ],
            );
        },
    );
    h.case("held/keys_only skips the bind marks", || {
        let fx = Fx::load("loops", "tk03");
        let cx = fx.cx("markLiteral");
        let h = HeldResults::run(&cx, true);
        assert_eq!(show(&h.held_at(pt(4, 0), local(cx.body, "x"))), "L3@t P0");
    });
    h.case(
        "held/stores: the caller's value, read set beside (A:1192)",
        || {
            let fx = Fx::load("held", "stores");
            let (_, h) = fx.held("fromParam");
            let (held, rfields) = h.caller_at_returns(0);
            assert_eq!(
                (show(&held), show(&rfields)),
                ("P1?".to_owned(), "P1?".to_owned())
            );
            let (_, h) = fx.held("reset");
            let (held, rfields) = h.caller_at_returns(0);
            assert_eq!(
                (show(&held), show(&rfields)),
                ("P1?".to_owned(), "P1?".to_owned()),
                "a whole value"
            );
            let (_, h) = fx.held("fused");
            assert_eq!(
                show(&h.caller_at_returns(0).1),
                "L0 F0 R0",
                "the failing store still lands"
            );
            assert_eq!(h.ret_at_returns().len(), 1);
        },
    );
    h.case(
        "held/stores: each EN0616 of `store` and of a write's read-set check",
        || {
            let fx = Fx::load("held", "stores");
            let kinds = |name: &str| -> Vec<String> {
                fx.held(name)
                    .1
                    .store_errors
                    .iter()
                    .map(|e| format!("{}:{:?}:{}", e.at, e.kind, e.call))
                    .collect()
            };
            assert_eq!(kinds("fused"), ["bb0[1]:ReadSet:false"]);
            assert!(
                kinds("fromParam").is_empty()
                    && kinds("fromSrc").is_empty()
                    && kinds("reset").is_empty()
            );
            assert_eq!(
                kinds("local"),
                ["bb1[6]:ReadSet:false"],
                "the local part, `wfields(w)`"
            );
            assert_eq!(
                kinds("nested"),
                ["bb2[4]:ReadSet:false"],
                "a nested value, all of `held(o)`"
            );
            assert_eq!(kinds("byval"), ["bb0[4]:Consumed(0):true"]);
            assert_eq!(kinds("consume"), ["bb0[2]:Consumed(0):true"]);
            let arrow = fx
                .bodies
                .values()
                .find(|b| matches!(b.owner, enrang_mir::BodyOwner::Arrow(..)))
                .expect("the arrow");
            let cx = BodyCx::new(&fx.tcx, &fx.bodies, arrow, None);
            let e: Vec<String> = HeldResults::run(&cx, false)
                .store_errors
                .iter()
                .map(|e| format!("{:?}", e.kind))
                .collect();
            assert_eq!(e, ["Captured"]);
        },
    );
}
