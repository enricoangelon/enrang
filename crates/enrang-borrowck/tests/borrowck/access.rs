//! Stage 2E's tests of liveness and the access check (A:1231-1266, M3 plan d.6):
//! `overlap` and `loans_overlap`, the conflict data, the one-report rule at a call,
//! liveness, and the rows whose code needs plan d.7's argument modes, read here
//! from `held` (D20-core-1, D20-core-2, FV-02-store-snapshot).

use enrang_borrowck::{
    AccessKind, LiveSlots, LoanPath, SlotId, Step, Turn, access_check, compute_modes,
    loans_overlap, overlap,
};
use enrang_hir::{FieldIdx, LoopId, VariantIdx};
use enrang_mir::Local;
use enrang_testkit::Harness;

use crate::held::{Fx, codes, l, local, pt, show};

fn path(root: u32, through_ref: bool, steps: &[Step]) -> LoanPath {
    LoanPath {
        root: Local(root),
        through_ref,
        steps: steps.to_vec(),
    }
}

const COPIER: &str = "@final class Copier writes_through_fields {
  src: readonly &Slice<u8>;
  dst: &Slice<u8>;
  pos: isize;
}
fn Copier::setSrc(_1: &Copier, _2: &Slice<u8>) -> void perms(write, read) sources() stores(1 -> 0 read) result none;
static fn Copier::make(_1: &Slice<u8>, _2: &Slice<u8>) -> Copier perms(read, write) sources(0, 1) result none;
";

/// FV-02-upcast-local's `const p = w.dst; w.setSrc(p);`, with `const e = &w;`
/// written through after the call when `held_e`.
fn upcast(held_e: bool) -> String {
    let e = if held_e {
        "    _7 = &_3 [explicit];\n"
    } else {
        ""
    };
    let w = if held_e {
        "    (*_7).pos = const 1: isize;\n"
    } else {
        ""
    };
    format!(
        "{COPIER}
fn upcast(_1: &Slice<u8>, _2: &Slice<u8>) -> void {{
  let _3: Copier; // w
  let _4: &Slice<u8> temp;
  let _5: &Slice<u8> temp;
  let _6: &Slice<u8>; // p
  let _7: &Copier; // e
  let _8: &Copier temp;
  let _9: &Slice<u8> temp;
  let _10: void temp;
  bb0: {{
    storage_live(_3);
    _4 = &*_1 [reborrow];
    _5 = &*_2 [reborrow];
    _3 = Copier::make(move _4, move _5) -> bb1;
  }}
  bb1: {{
    storage_live(_6);
    _6 = copy _3.dst;
    storage_live(_7);
{e}    _9 = &*_6 [reborrow];
    _8 = &_3 [auto-borrow];
    _10 = Copier::setSrc(move _8, move _9) -> bb2;
  }}
  bb2: {{
{w}    storage_dead(_7);
    storage_dead(_6);
    storage_dead(_3);
    return;
  }}
}}
"
    )
}

/// The line of the first line of `text` containing `piece`.
fn line_of(text: &str, piece: &str) -> usize {
    text.lines()
        .position(|l| l.contains(piece))
        .expect("present")
        + 1
}

pub fn register(h: &mut Harness) {
    h.case(
        "access/overlap: prefixes, `[*]`, fields, cases, `Fields`, shallow",
        || {
            let f = |i| Step::Field(FieldIdx(i));
            let v = |i| Step::Variant(VariantIdx(i));
            assert!(overlap(
                &path(1, false, &[]),
                &path(1, false, &[f(0)]),
                false
            ));
            assert!(overlap(
                &path(1, false, &[f(0), Step::Elem]),
                &path(1, false, &[f(0)]),
                false
            ));
            assert!(
                !overlap(&path(1, false, &[f(0)]), &path(1, false, &[f(1)]), false),
                "fields"
            );
            assert!(
                !overlap(&path(1, false, &[f(0)]), &path(2, false, &[f(0)]), false),
                "roots"
            );
            assert!(
                overlap(
                    &path(1, false, &[Step::Elem]),
                    &path(1, false, &[Step::Elem, f(0)]),
                    false
                ),
                "[*]"
            );
            assert!(
                !overlap(
                    &path(1, false, &[v(0), f(0)]),
                    &path(1, false, &[v(1), f(0)]),
                    false
                ),
                "cases"
            );
            assert!(
                !overlap(
                    &path(1, true, &[Step::Fields]),
                    &path(1, true, &[f(0)]),
                    false
                ),
                "`Fields`"
            );
            assert!(
                overlap(&path(1, false, &[]), &path(1, true, &[f(0)]), false),
                "a loan on the slot"
            );
            assert!(
                !overlap(&path(1, true, &[]), &path(1, false, &[]), true),
                "a shallow end of `r`"
            );
            assert!(
                overlap(&path(1, true, &[]), &path(1, false, &[]), false),
                "a deep one"
            );
            assert!(
                overlap(&path(1, false, &[]), &path(1, false, &[]), true),
                "an owned root, shallow"
            );
        },
    );
    h.case(
        "access/loans_overlap: two turns of one run are disjoint (A:1244)",
        || {
            let fx = Fx::load("loops", "tk03");
            let cx = fx.cx("markLiteral");
            let (bind, whole) = (enrang_borrowck::LoanId(3), enrang_borrowck::LoanId(0));
            assert!(!loans_overlap(
                &cx,
                (bind, Turn::This),
                (bind, Turn::EarlierThisRun)
            ));
            assert!(!loans_overlap(
                &cx,
                (bind, Turn::EarlierThisRun),
                (bind, Turn::This)
            ));
            assert!(loans_overlap(&cx, (bind, Turn::This), (bind, Turn::This)));
            assert!(loans_overlap(
                &cx,
                (bind, Turn::EarlierThisRun),
                (bind, Turn::EarlierThisRun)
            ));
            assert!(loans_overlap(
                &cx,
                (bind, Turn::EarlierRuns),
                (bind, Turn::This)
            ));
            assert!(
                loans_overlap(&cx, (whole, Turn::Any), (bind, Turn::This)),
                "`*xs` and `xs[*]`"
            );
        },
    );
    h.case(
        "access/a conflict's data: holder, later use, loan, kind (G11)",
        || {
            let fx = Fx::load("access", "g11-dead-scope");
            let cx = fx.cx("g11");
            let held = enrang_borrowck::HeldResults::run(&cx, false);
            let live = LiveSlots::compute(&cx);
            let modes = compute_modes(&cx, &held);
            let c = access_check(&cx, &held, &live, &modes);
            assert_eq!(c.len(), 1);
            let r = local(cx.body, "r");
            assert_eq!(c[0].access.kind, AccessKind::StorageDead);
            assert_eq!(c[0].loan, enrang_borrowck::LoanId(0));
            assert_eq!(c[0].holder.map(SlotId::Local), Some(r));
            let SlotId::Local(rl) = r else { unreachable!() };
            let (u, span) = c[0].later_use.expect("a later use");
            assert_eq!(u, rl);
            let text = crate::held::fixture("access", "g11-dead-scope");
            let line = fx.tcx.map().loc(span.lo).line;
            assert_eq!(line as usize, line_of(&text, "_3 = &*_1 [reborrow];"));
        },
    );
    h.case("access/the method a receiver's borrow is for", || {
        let fx = Fx::load("access", "d-rows");
        let cx = fx.cx("core4");
        let held = enrang_borrowck::HeldResults::run(&cx, false);
        let c = access_check(&cx, &held, &LiveSlots::compute(&cx), &compute_modes(&cx, &held));
        assert!(c.iter().all(|c| c.access.method.is_none()), "drops name no method");
        let text = format!(
            "{COPIER}\nfn m(_1: Copier, _2: &Slice<u8>) -> void {{\n  let _3: &Copier temp;\n  let _4: &Slice<u8> temp;\n  let _5: void temp;\n  let _6: &Copier; // e\n  bb0: {{\n    _6 = &_1 [explicit];\n    _4 = &*_2 [reborrow];\n    _3 = &_1 [auto-borrow];\n    _5 = Copier::setSrc(move _3, move _4) -> bb1;\n  }}\n  bb1: {{\n    (*_6).pos = const 1: isize;\n    drop(_1);\n    return;\n  }}\n}}\n"
        );
        let fx = Fx::new(&text);
        let cx = fx.cx("m");
        let held = enrang_borrowck::HeldResults::run(&cx, false);
        let c = access_check(&cx, &held, &LiveSlots::compute(&cx), &compute_modes(&cx, &held));
        assert_eq!(c.len(), 1);
        assert_eq!(c[0].access.method.map(|s| s.as_str().to_owned()).as_deref(), Some("setSrc"));
    });
    h.case(
        "access/one report per mistake at a call: no read-set EN0616 where a borrow conflicted",
        || {
            let text = upcast(true);
            let got = codes(&text);
            let call = line_of(&text, "Copier::setSrc(move _8");
            let borrow = line_of(&text, "_8 = &_3 [auto-borrow]");
            assert!(!got.contains(&format!("{call}:EN0616")), "{got:?}");
            assert!(
                got.iter().any(|c| c.starts_with(&format!("{borrow}:EN07"))),
                "{got:?}"
            );
            // Without `e`, exactly one of the two names the aliasing, whatever the modes.
            let text = upcast(false);
            let got = codes(&text);
            let call = line_of(&text, "Copier::setSrc(move _8");
            let borrow = line_of(&text, "_8 = &_3 [auto-borrow]");
            let rs = got.contains(&format!("{call}:EN0616"));
            let cf = got.iter().any(|c| c.starts_with(&format!("{borrow}:EN07")));
            assert!(rs != cf, "{got:?}");
        },
    );
    h.case("access/liveness: a destructor's drop is a use, a hold lives to its head, `caller` to the return", || {
        let fx = Fx::load("access", "o11");
        let live = |name: &str| LiveSlots::compute(&fx.cx(name));
        let g = live("guard");
        assert!(g.live_before(pt(1, 1)).contains(&l(2)), "`drop(g)` runs `Guard`'s destructor");
        let t = live("plain");
        assert!(!t.live_after(pt(1, 0)).contains(&l(2)), "`Tagged` has none");
        let g10 = live("g10");
        assert!(g10.live_after(pt(0, 2)).contains(&l(0)), "`_0` is read by the return");
        let fx = Fx::load("loops", "holds");
        let hold = SlotId::Hold(LoopId(0));
        let r = LiveSlots::compute(&fx.cx("g21"));
        assert!(r.live_before(pt(2, 0)).contains(&hold), "the head uses the hold");
        assert!(!r.live_before(pt(1, 2)).contains(&hold), "the pre-header defines it");
        assert!(r.live_after(pt(4, 2)).contains(&hold), "the head is reachable");
        let r = LiveSlots::compute(&fx.cx("g21Break"));
        assert!(!r.live_after(pt(4, 2)).contains(&hold), "`break` leaves the loop");
        let fx = Fx::load("held", "stores");
        let r = LiveSlots::compute(&fx.cx("fromParam"));
        assert!(r.live_before(pt(0, 2)).contains(&SlotId::Caller(0)));
    });
    h.case(
        "access/kill: the cursor keeps only the parameter's key (SPEC 5.3)",
        || {
            let fx = Fx::load("held", "kill");
            let (cx, h) = fx.held("last");
            assert_eq!(show(&h.held_at(pt(1, 0), local(cx.body, "cur"))), "P0?");
            assert_eq!(show(&h.held_at(pt(2, 3), local(cx.body, "cur"))), "P0?");
        },
    );
    h.case("access/D20-core-1, D20-core-2: what the stored and returned sets hold", || {
        let text = "@final class Grower writes_through_fields {
  v: &i64[];
}
fn Grower::setV(_1: &Grower, _2: &i64[]) -> void perms(write, write) sources() stores(1 -> 0) result none;
fn Grower::first(_1: &Grower) -> &i64 perms(read) sources(0) result writable;
fn core1(_1: Grower, _2: i64[]) -> void {
  let _3: &Grower temp;
  let _4: &i64[] temp;
  let _5: void temp;
  let _6: &i64; // e
  bb0: {
    _4 = &_2 [explicit];
    _3 = &_1 [auto-borrow];
    _5 = Grower::setV(move _3, move _4) -> bb1;
  }
  bb1: {
    _3 = &_1 [auto-borrow];
    _6 = Grower::first(move _3) -> bb2;
  }
  bb2: {
    drop(_2);
    return;
  }
}
";
        let fx = Fx::new(text);
        let (_, h) = fx.held("core1");
        assert_eq!(show(&h.held_at(pt(1, 0), l(1))), "L0 P0?", "`g` keeps the stored loan on `data`");
        assert_eq!(show(&h.held_at(pt(2, 0), l(6))), "L0 L2 P0?", "`e` holds the receiver's loan");
    });
    h.case("access/FV-02-store-snapshot: one call's stores read the sets before it", || {
        let text = "class H {
  c: &C;
}
class C {
  s: &Slice<i64>;
}
fn link(_1: &H, _2: &C, _3: &Slice<i64>) -> void perms(write, write, read) sources() stores(2 -> 1, 1 -> 0) result none;
fn snap(_1: H, _2: C, _3: &Slice<i64>) -> void {
  let _4: &H temp;
  let _5: &C temp;
  let _6: &Slice<i64> temp;
  let _7: void temp;
  bb0: {
    _4 = &_1 [explicit];
    _5 = &_2 [explicit];
    _6 = &*_3 [reborrow];
    _7 = link(move _4, move _5, move _6) -> bb1;
  }
  bb1: {
    return;
  }
}
";
        let fx = Fx::new(text);
        let (_, h) = fx.held("snap");
        assert_eq!(show(&h.held_at(pt(1, 0), l(2))), "P1? P2?", "`c` takes the slice's set");
        assert_eq!(show(&h.held_at(pt(1, 0), l(1))), "L1 P0? P1?", "`h` takes `&c`'s set before the call");
    });
}
