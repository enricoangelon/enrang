//! Stage 2D's tests of drop elaboration (M3 plan d.12): each fixture under
//! `tests/mir/borrowck/elaborate/` checks clean, each body is elaborated and
//! verified again, and the printed module is compared with `<name>.out` beside it
//! (`ENRANG_BLESS=1` rewrites it).

use std::path::PathBuf;
use std::sync::Arc;

use enrang_diag::DiagCtx;
use enrang_mir::{BlockId, Bodies, MirPhase, StatementKind, parse_module, print_module, verify};
use enrang_testkit::{BlessMode, GoldenStore, Harness};

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/mir/borrowck")
}

/// Every body of `text` elaborated, printed as a module.
pub fn elaborated(text: &str) -> String {
    let (tcx, list) = parse_module(text).unwrap_or_else(|e| panic!("{e}"));
    let bodies: Bodies = list.iter().cloned().map(|b| (b.owner, b)).collect();
    let mut dcx = DiagCtx::new();
    enrang_borrowck::infer_contracts(&tcx, &bodies, &mut dcx);
    let mut out = Vec::new();
    for b in &list {
        let facts = enrang_borrowck::check(&tcx, &bodies, b, &mut dcx);
        let e = enrang_borrowck::elaborate_drops(&tcx, b.clone(), &facts);
        assert_eq!(e.phase, MirPhase::Elaborated);
        if let Err(errors) = verify(&tcx, &e) {
            panic!(
                "elaborated MIR is invalid: {errors:#?}\n{}",
                print_module(&tcx, [&e])
            );
        }
        out.push(e);
    }
    assert!(!dcx.has_errors(), "an elaboration fixture checks clean");
    print_module(&tcx, &out)
}

pub fn register(h: &mut Harness) {
    let store = Arc::new(GoldenStore::new(root(), BlessMode::from_env()));
    let mut names: Vec<String> = std::fs::read_dir(root().join("elaborate"))
        .expect("the elaborate fixtures")
        .map(|e| e.expect("an entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "mir"))
        .map(|p| {
            p.file_stem()
                .expect("a name")
                .to_string_lossy()
                .into_owned()
        })
        .collect();
    names.sort();
    for name in names {
        let store = store.clone();
        h.case(format!("elaborate/{name}: matches {name}.out"), move || {
            let text = std::fs::read_to_string(root().join(format!("elaborate/{name}.mir")))
                .expect("a fixture");
            let got = elaborated(&text);
            if let Err(d) = store.check("elaborate", &format!("{name}.out"), &got) {
                panic!("{d}");
            }
        });
    }
    h.case("elaborate/twice gives the same text", || {
        let text = std::fs::read_to_string(root().join("elaborate/ladder.mir")).expect("a fixture");
        assert_eq!(elaborated(&text), elaborated(&text));
    });
    h.case(
        "elaborate/a moved local's drop flag records its path",
        || {
            let text =
                std::fs::read_to_string(root().join("elaborate/flags.mir")).expect("a fixture");
            let (tcx, list) = parse_module(&text).expect("parsed");
            let bodies: Bodies = list.iter().cloned().map(|b| (b.owner, b)).collect();
            let mut dcx = DiagCtx::new();
            let maybe = list.iter().find(|b| b.arg_count == 1).expect("`maybe`");
            let facts = enrang_borrowck::check(&tcx, &bodies, maybe, &mut dcx);
            let e = enrang_borrowck::elaborate_drops(&tcx, maybe.clone(), &facts);
            assert_eq!(e.drop_flags.len(), 1);
            let (flag, key) = &e.drop_flags[0];
            assert_eq!(key.local.0, 2);
            assert!(key.steps.is_empty());
            assert_eq!(e.locals[*flag].kind, enrang_mir::LocalKind::DropFlag);
            let glue = e.blocks.iter().flat_map(|b| &b.stmts);
            assert_eq!(
                glue.filter(|s| matches!(s.kind, StatementKind::DropGlue(_)))
                    .count(),
                1
            );
            assert!(
                !e.blocks[BlockId(0)].stmts.is_empty(),
                "the flag starts cleared at entry"
            );
        },
    );
}
