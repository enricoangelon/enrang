//! The suite of enrang-mirbuild (M3 plan f.1): hand-built HIR for the shapes that
//! need no front end; most tests of MIR building run source programs in the
//! driver's `pipeline` suite. Stage 1B: the skeleton's builder and entry points.

#![forbid(unsafe_code)]

use std::process::ExitCode;
use std::sync::Arc;

use enrang_base::{FileId, SourceMap, Span};
use enrang_diag::DiagCtx;
use enrang_hir::{self as hir, CheckedProgram, ModuleId, Tcx};
use enrang_mir::{BlockId, BodyOwner, LocalKind, Place, StatementKind, TerminatorKind, verify};
use enrang_mirbuild::{BuildCx, Builder, ExitTarget, ScopeKind, build, build_program};
use enrang_testkit::Harness;

/// This suite's share of the 4,000 more cases TESTING 23 asks of M3 (M3 plan f.9,
/// which forecast 50; most tests of MIR building run source programs in the
/// driver's `pipeline` suite): every case it registers, all of them M3's.
/// `enrang-suite`'s meta-tests check that the shares of M3's suites add up.
pub const M3_SHARE: usize = 3;

/// A context with one user module, `ModuleId(0)`.
fn tcx() -> Tcx {
    let mut tcx = Tcx::for_target("x86_64-linux", Arc::new(SourceMap::new())).expect("a target");
    tcx.define_module(hir::ModuleInfo::new(
        hir::ModulePath::new("main"),
        false,
        FileId(0),
    ));
    tcx
}

fn statements_body(tcx: &Tcx) -> hir::Body {
    let module = ModuleId(0);
    hir::Body::empty(
        hir::BodyOwner::Statements(module),
        tcx.common().void,
        Span::DUMMY,
    )
}

fn main() -> ExitCode {
    let mut h = Harness::new("mirbuild");
    h.case("skeleton/an empty program builds no body", || {
        let tcx = tcx();
        let mut dcx = DiagCtx::new();
        let bodies = build_program(&tcx, &CheckedProgram::default(), ModuleId(0), &mut dcx);
        assert!(bodies.is_empty());
    });
    h.case("skeleton/a body builds to verified MIR", || {
        let tcx = tcx();
        let program = CheckedProgram::default();
        let hir = statements_body(&tcx);
        let mut dcx = DiagCtx::new();
        let built = build(&tcx, &program, &hir, &mut dcx);
        assert_eq!(built.len(), 1);
        assert_eq!(built[0].owner, BodyOwner::Statements(ModuleId(0)));
        verify(&tcx, &built[0]).expect("valid");
    });
    h.case(
        "skeleton/the builder's blocks, temps, scopes and exits",
        || {
            let tcx = tcx();
            let program = CheckedProgram::default();
            let cx = BuildCx {
                tcx: &tcx,
                program: &program,
            };
            let hir = statements_body(&tcx);
            let mut b = Builder::new(&cx, &hir);
            let t = b.new_temp(tcx.common().i64, Span::DUMMY);
            assert_eq!(b.body.locals[t].kind, LocalKind::Temp);
            b.push_scope(ScopeKind::Block);
            b.schedule_drop(Place::local(t));
            b.pop_scope();
            let next = b.new_block();
            b.terminate(TerminatorKind::Goto(next), Span::DUMMY);
            assert!(b.cursor.is_none());
            b.switch_to(next);
            b.exit_to(ExitTarget::Return, Span::DUMMY);
            let entry = &b.body.blocks[BlockId(0)];
            assert!(matches!(entry.stmts[0].kind, StatementKind::Drop(..)));
            assert_eq!(b.body.blocks[next].term.kind, TerminatorKind::Return);
        },
    );
    let m3 = h.len();
    h.case(
        "count/this suite holds its share of M3's cases",
        move || {
            assert!(m3 >= M3_SHARE, "{m3} cases, short of {M3_SHARE}");
        },
    );
    h.run()
}
