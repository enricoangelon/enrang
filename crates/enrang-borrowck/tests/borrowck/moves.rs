//! Stage 2D's tests of move paths, init and move reports (M3 plan d.1-d.2): the
//! primary spans of the fixtures' reports, and the move paths and init states the
//! fixtures' bodies give. The fixtures themselves run in `fixtures.rs`.

use std::path::PathBuf;

use enrang_base::BitSet;
use enrang_borrowck::{InitResults, MoveData, MovePathIdx};
use enrang_diag::DiagCtx;
use enrang_mir::{BlockId, Bodies, Body, Local, MovePathKey, MoveStep, Place, parse_module};
use enrang_testkit::Harness;

pub fn fixture(area: &str, name: &str) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join(format!("tests/mir/borrowck/{area}/{name}.mir"));
    std::fs::read_to_string(path).expect("a fixture")
}

/// What `check` reports on `text`: each code with its primary span's text, in
/// report order.
pub fn reported(text: &str) -> Vec<(String, String)> {
    let (tcx, list) = parse_module(text).unwrap_or_else(|e| panic!("{e}"));
    let bodies: Bodies = list.iter().cloned().map(|b| (b.owner, b)).collect();
    let mut dcx = DiagCtx::new();
    for b in &list {
        enrang_borrowck::check(&tcx, &bodies, b, &mut dcx);
    }
    dcx.take()
        .into_iter()
        .map(|d| {
            (
                d.code.to_string(),
                tcx.map().text(d.primary.span).to_owned(),
            )
        })
        .collect()
}

fn pairs(want: &[(&str, &str)]) -> Vec<(String, String)> {
    want.iter()
        .map(|(c, s)| (c.to_string(), s.to_string()))
        .collect()
}

/// The body named `name` of `text`, with the `Tcx` it was parsed into.
fn body(text: &str, name: &str) -> (enrang_hir::Tcx, Body) {
    let (tcx, list) = parse_module(text).expect("parsed");
    let b = list
        .into_iter()
        .find(|b| match b.owner {
            enrang_mir::BodyOwner::Fn(d) => tcx.def(d).path.to_string().ends_with(name),
            _ => false,
        })
        .expect("the body");
    (tcx, b)
}

fn key(local: u32, steps: &[MoveStep]) -> MovePathKey {
    MovePathKey {
        local: Local(local),
        steps: steps.to_vec(),
    }
}

/// `for (const x of &q) { take(q); }` (A:1007): the move is the hold's EN0709
/// (stage 2E), so no EN0611; over another array, `take(q)` is EN0611. Kept out of
/// the fixture directory, since the merged checker also reports the EN0709.
const HELD: &str = "@final class User {
  name: string;
}
fn drain(_1: User[]) -> void;

fn held(_1: User[], _2: User[]) -> void {
  let _3: isize #i;
  let _4: isize #n;
  let _5: bool temp;
  let _6: &User; // x
  let _7: void temp;
  loop l0: path _1 preheader bb0 head bb1 bind bb2[2] binding _6;
  bb0: {
    storage_live(_3);
    _3 = const 0: isize;
    goto bb1;
  }
  bb1: {
    _4 = len(_1);
    _5 = lt(copy _3, copy _4);
    switch move _5 [0: bb5, otherwise: bb2];
  }
  bb2: {
    storage_live(_6);
    check_bounds(copy _3, copy _4);
    _6 = &_1[_3] [for-of-element];
    _3 = add(copy _3, const 1: isize);
    goto bb3;
  }
  bb3: {
    _7 = drain(move _1) -> bb4;
  }
  bb4: {
    storage_dead(_6);
    goto bb1;
  }
  bb5: {
    drop(_1);
    return;
  }
}
";

pub fn register(h: &mut Harness) {
    h.case(
        "moves/a move of the loop's own held source is no EN0611",
        || {
            let ours = |text: &str| -> Vec<String> {
                let got = reported(text).into_iter().map(|(c, _)| c);
                got.filter(|c| c == "EN0601" || c == "EN0611").collect()
            };
            assert!(ours(HELD).is_empty());
            // Only the hold's EN0709 is reported, since it names the cause (A:1007).
            let got = reported(HELD);
            assert_eq!(got, pairs(&[("EN0709", "_7 = drain(move _1) -> bb4")]));
            let other = HELD.replace("drain(move _1)", "drain(move _2)");
            assert_eq!(ours(&other), ["EN0611"]);
        },
    );
    h.case("moves/EN0601 is at the use, EN0611 at the move", || {
        let got = reported(&fixture("moves", "loops"));
        let want = pairs(&[
            ("EN0611", "_3 = archive(move _2) -> bb1"),
            ("EN0611", "_8 = archive(move _2) -> bb6"),
            ("EN0601", "_4 = &_2 [auto-borrow]"),
            ("EN0611", "_3 = archive(move _2) -> bb1"),
        ]);
        assert_eq!(got, want);
        let got = reported(&fixture("moves", "use_after_move"));
        assert_eq!(
            got[0],
            pairs(&[("EN0601", "_2 = archive(move _1) -> bb3")])[0]
        );
        assert_eq!(got[2], pairs(&[("EN0601", "_3 = &_1 [auto-borrow]")])[0]);
    });
    h.case(
        "moves/constructor reports are at the use, the exit or the call",
        || {
            let got = reported(&fixture("moves", "ctor_fields"));
            let want = pairs(&[
                ("EN0610", "_4 = &*_1 [reborrow]"),
                ("EN0610", "_6 = copy (*_1).b.n"),
                ("EN0610", "return"),
                ("EN0610", "(*_1).owner = move _2"),
            ]);
            assert_eq!(got, want);
            let got = reported(&fixture("moves", "ctor_order"));
            assert_eq!(
                got,
                pairs(&[("EN0610", "_4 = Animal::#ctor(move _5, move _2) -> bb1")])
            );
        },
    );
    h.case("moves/crossing reports name the moving statement", || {
        let got: Vec<String> = reported(&fixture("moves", "crossing"))
            .into_iter()
            .map(|(c, s)| format!("{c} {s}"))
            .collect();
        assert_eq!(
            got,
            [
                "EN0603 _2 = archive(move *_1) -> bb1",
                "EN0603 _0 = move (*_1).name",
                "EN0603 _0 = move (*_2).name",
                "EN0605 _2 = archive(move *_1) -> bb1",
                "EN0604 _4 = move _1[_2]",
                "EN0607 _2 = keep(move _1.name) -> bb1",
            ]
        );
    });
    h.case(
        "moves/MoveData::collect has the roots only until built",
        || {
            let (tcx, b) = body(&fixture("moves", "use_after_move"), "twice");
            let roots = MoveData::collect(&b);
            assert_eq!(roots.paths.len(), b.locals.len());
            assert!(roots.lookup.is_empty());
            assert_eq!(InitResults::compute(&b, &roots), InitResults::default());
            let md = MoveData::build(&tcx, &b);
            assert_eq!(
                md.paths.len(),
                b.locals.len(),
                "a root per local, nothing deeper"
            );
            assert!(md.super_path.is_none() && md.ctor_fields.is_none());
        },
    );
    h.case(
        "moves/a constructor tracks `super` and each field of `this`",
        || {
            let (tcx, b) = body(&fixture("moves", "ctor_order"), "Dog::#ctor");
            let md = MoveData::build(&tcx, &b);
            let s = md.super_path.expect("a class with a base has `super`");
            assert!(md.paths[s].key.is_none());
            let fields = md.ctor_fields.as_ref().expect("a constructor");
            let shape: Vec<(u32, bool, bool)> = fields.iter().map(|f| (f.0.0, f.2, f.3)).collect();
            assert_eq!(
                shape,
                [(0, false, false), (1, true, false)],
                "inherited `name`, own `owner`"
            );
            let owner = md.by_key[&key(1, &[MoveStep::Field(enrang_hir::FieldIdx(1))])];
            assert_eq!(fields[1].1, owner);
            assert_eq!(md.supers.len(), 1);
            assert_eq!(md.exempt.len(), 2, "the reborrow and the upcast of `this`");
        },
    );
    h.case(
        "moves/a field the class below may override starts maybe-init",
        || {
            let text = fixture("elaborate", "ctor_flag");
            let (tcx, b) = body(&text, "Named::#ctor");
            let md = MoveData::build(&tcx, &b);
            let tag = md.ctor_fields.as_ref().expect("a constructor")[0];
            assert!(tag.3, "no default, in a class that can be extended");
            let init = InitResults::compute(&b, &md);
            assert!(init.maybe_init[BlockId(0)].contains(tag.1));
            assert!(init.maybe_uninit[BlockId(0)].contains(tag.1));
        },
    );
    h.case(
        "moves/a move on one branch leaves the path maybe-init at the join",
        || {
            let (tcx, b) = body(&fixture("moves", "use_after_move"), "branch");
            let md = MoveData::build(&tcx, &b);
            let init = InitResults::compute(&b, &md);
            let u: MovePathIdx = md.root(Local(2));
            let at = |bb: u32| {
                let i: &BitSet<MovePathIdx> = &init.maybe_init[BlockId(bb)];
                (i.contains(u), init.maybe_uninit[BlockId(bb)].contains(u))
            };
            assert_eq!(at(0), (false, true), "before the `let`");
            assert_eq!(at(2), (true, false), "the moving branch");
            assert_eq!(at(3), (true, true), "the join");
            assert_eq!(md.lookup[&Place::local(Local(2))], (u, true));
        },
    );
    h.case("moves/a kept assignment value is not applied", || {
        let (tcx, b) = body(&fixture("moves", "assign_value"), "kept");
        let md = MoveData::build(&tcx, &b);
        let init = InitResults::compute(&b, &md);
        let s = md.root(Local(1));
        assert!(
            !init.maybe_uninit[BlockId(2)].contains(s),
            "`s` stays initialised"
        );
    });
}
