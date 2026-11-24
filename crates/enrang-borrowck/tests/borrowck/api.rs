//! The API as the skeleton leaves it (stage 1B): a declared contract from marks
//! when the memo has none, the memo when it has one, a class flag's default, a
//! call's contract mapped to its reference arguments, elaboration's `Drop`s made
//! `DropGlue`s that the verifier accepts, and the modes stub's N3 rule (a) on
//! loans made by hand (plan g.2).

use enrang_base::Span;
use enrang_borrowck::{
    BodyCx, HeldResults, Loan, LoanId, LoanKind, LoanPath, call_info, class_contract,
    compute_modes, contract, elaborate_drops,
};
use enrang_hir::{Perm, ResultPerm, RetSources};
use enrang_mir::{
    BlockId, Bodies, BorrowOrigin, Local, MirPhase, Point, StatementKind, TerminatorKind,
    parse_module, verify,
};
use enrang_testkit::Harness;

const TEXT: &str = "class P {
  x: i64;
}
fn mark(let _1: &P, _2: &i64, _3: i64) -> readonly &i64;
fn stated(let _1: &P) -> &i64 perms(write) sources(0) result writable;

fn f(_1: &P, _2: P) -> void {
  let _3: &i64 temp;
  let _4: &P temp;
  bb0: {
    _4 = &*_1 [reborrow];
    _3 = mark(move _4, copy _3, const 1: i64) -> bb1;
  }
  bb1: {
    drop(_2);
    return;
  }
}
";

/// `_3` is written through, `_4` only read, `_5` reassigned before the write
/// through it, `_7` written through by an intrinsic, `_3` again by a call.
const MODES: &str = "fn id(_1: i64) -> i64;
fn w() -> void {
  let _1: i64; // x
  let _2: i64 temp;
  let _3: &i64; // r
  let _4: &i64; // s
  let _5: &i64; // t
  let _6: usize; // n
  let _7: &usize; // u
  bb0: {
    _3 = &_1 [explicit];
    *_3 = const 1: i64;
    _4 = &_1 [explicit];
    _2 = copy *_4;
    _5 = &_1 [explicit];
    _5 = &_1 [explicit];
    *_5 = const 2: i64;
    _7 = &_6 [explicit];
    *_7 = intrinsic SizeOf<i64>();
    _3 = &_1 [explicit];
    *_3 = id(const 3: i64) -> bb1;
  }
  bb1: {
    return;
  }
}
";

/// A `for...of` whose body writes through its binding.
const HOLD: &str = "fn each(_1: &i64[]) -> void {
  let _2: isize #i;
  let _3: isize #n;
  let _4: bool temp;
  let _5: &i64; // x
  loop l0: path *_1 preheader bb0 head bb1 bind bb2[2] binding _5;
  bb0: {
    storage_live(_2);
    _2 = const 0: isize;
    goto bb1;
  }
  bb1: {
    _3 = len(*_1);
    _4 = lt(copy _2, copy _3);
    switch move _4 [0: bb4, otherwise: bb2];
  }
  bb2: {
    storage_live(_5);
    check_bounds(copy _2, copy _3);
    _5 = &(*_1)[_2] [for-of-element];
    _2 = add(copy _2, const 1: isize);
    goto bb3;
  }
  bb3: {
    *_5 = const 0: i64;
    storage_dead(_5);
    goto bb1;
  }
  bb4: {
    return;
  }
}
";

/// The modes `compute_modes` gives loans made by hand, one per `(site, kind)`.
fn modes_of(text: &str, loans: &[(Point, LoanKind)]) -> Vec<bool> {
    let (tcx, list) = parse_module(text).expect("parsed");
    let bodies: Bodies = list.iter().cloned().map(|b| (b.owner, b)).collect();
    let mut cx = BodyCx::new(&tcx, &bodies, &list[0], None);
    // Only the loans made here, whatever `Loans::collect` found (2E).
    cx.loans.table = enrang_base::IdVec::new();
    for (site, kind) in loans {
        cx.loans.table.push(Loan {
            path: LoanPath {
                root: Local(1),
                through_ref: false,
                steps: Vec::new(),
            },
            span: Span::DUMMY,
            origin: BorrowOrigin::Explicit,
            site: *site,
            kind: kind.clone(),
        });
    }
    let modes = compute_modes(&cx, &HeldResults::default());
    (0..loans.len() as u32)
        .map(|i| modes.exclusive(LoanId(i)))
        .collect()
}

fn def(tcx: &enrang_hir::Tcx, path: &str) -> enrang_hir::DefId {
    tcx.defs()
        .find(|(_, d)| d.path.to_string() == path)
        .map(|(d, _)| d)
        .expect("declared")
}

pub fn register(h: &mut Harness) {
    h.case("api/a declared contract comes from the marks", || {
        let (tcx, _) = parse_module(TEXT).expect("parsed");
        let c = contract(&tcx, def(&tcx, "main::mark"));
        assert_eq!(c.perms, [Perm::Write, Perm::Read]);
        assert_eq!(c.sources, RetSources::Params(vec![0, 1]));
        assert!(matches!(c.result, ResultPerm::ReadOnly(_)));
        let stated = contract(&tcx, def(&tcx, "main::stated"));
        assert_eq!(stated.sources, RetSources::Params(vec![0]));
        let p = tcx.adts().next().map(|(a, _)| a).expect("a class");
        assert!(!class_contract(&tcx, p).writes_through_fields);
    });
    h.case(
        "api/a call's contract indices are its argument positions",
        || {
            let (tcx, list) = parse_module(TEXT).expect("parsed");
            let bodies: Bodies = list.into_iter().map(|b| (b.owner, b)).collect();
            let body = bodies.values().next().expect("a body");
            let cx = BodyCx::new(&tcx, &bodies, body, None);
            let TerminatorKind::Call { callee, args, .. } = &body.blocks[BlockId(0)].term.kind
            else {
                panic!("a call");
            };
            let info = call_info(&cx, callee, args);
            assert_eq!(info.args_map, [0, 1, 2]);
            assert_eq!(info.perms, [Perm::Write, Perm::Read]);
        },
    );
    h.case(
        "api/the skeleton's elaboration makes drops into glue the verifier accepts",
        || {
            let (tcx, list) = parse_module(TEXT).expect("parsed");
            let bodies: Bodies = list.iter().cloned().map(|b| (b.owner, b)).collect();
            let mut dcx = enrang_diag::DiagCtx::new();
            let facts = enrang_borrowck::check(&tcx, &bodies, &list[0], &mut dcx);
            assert!(!dcx.has_errors());
            let b = elaborate_drops(&tcx, list[0].clone(), &facts);
            assert_eq!(b.phase, MirPhase::Elaborated);
            assert!(matches!(
                b.blocks[BlockId(1)].stmts[0].kind,
                StatementKind::DropGlue(_)
            ));
            verify(&tcx, &b).expect("valid");
        },
    );
    h.case(
        "api/modes stub: a borrow is exclusive when a write through its local follows",
        || {
            let at = |i| (Point::new(BlockId(0), i), LoanKind::Site);
            assert_eq!(
                modes_of(MODES, &[at(0), at(2), at(4), at(5), at(7), at(9)]),
                [true, false, false, true, true, true],
                "written through, only read, reassigned first, then written through, by an \
                 intrinsic, by a call"
            );
        },
    );
    h.case(
        "api/modes stub: a write through a `for...of` binding makes its borrow and hold exclusive",
        || {
            let (_, list) = parse_module(HOLD).expect("parsed");
            let l = list[0].meta.loops[0].id;
            // The hold's site is no borrow: its mode comes from the loop's bind.
            let loans = [
                (Point::new(BlockId(2), 2), LoanKind::Site),
                (Point::new(BlockId(0), 0), LoanKind::Hold(l)),
            ];
            assert_eq!(modes_of(HOLD, &loans), [true, true]);
            let read = HOLD.replace("    *_5 = const 0: i64;\n", "");
            assert_eq!(modes_of(&read, &loans), [false, false]);
        },
    );
    h.case("api/a summary names its module", || {
        let (tcx, _) = parse_module(TEXT).expect("parsed");
        let m = tcx.modules().next().map(|(m, _)| m).expect("a module");
        let text =
            enrang_borrowck::summary::render(&tcx, &enrang_borrowck::ContractSet::default(), m);
        assert_eq!(
            text,
            "module \"main\"\nfn stated(let _1: &P) -> &i64 perms(write) sources(0) result writable;\n"
        );
    });
}
