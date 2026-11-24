//! The suite of enrang-hir (plan b.10): the interner, `Tcx`, the predicates, member
//! lookup, the printing of types as SPEC 13's diagnostics print them, the lang and
//! intrinsic tables against the documents, item paths and path places.

#![forbid(unsafe_code)]

mod consts;
mod contract;
mod display;
mod interner;
mod member;
mod paths;
mod phase3;
mod places;
mod predicates;
mod support;
mod tables;
mod tcx;

use std::process::ExitCode;

use enrang_testkit::Harness;

/// This suite's share of the 2,500 more cases TESTING 23 asks of M2 (plan g.8):
/// every case here is M2's. `enrang-suite`'s meta-tests check that the shares of the
/// suites add up to the count TESTING 23 gives.
pub const M2_SHARE: usize = 150;

fn main() -> ExitCode {
    let mut h = Harness::new("hir");
    interner::register(&mut h);
    tcx::register(&mut h);
    display::register(&mut h);
    predicates::register(&mut h);
    member::register(&mut h);
    tables::register(&mut h);
    paths::register(&mut h);
    places::register(&mut h);
    consts::register(&mut h);
    contract::register(&mut h);
    phase3::register(&mut h);
    let m2 = h.len();
    h.case(
        "count/this suite holds its share of M2's cases",
        move || {
            assert!(m2 >= M2_SHARE, "{m2} cases, short of {M2_SHARE}");
        },
    );
    h.run()
}
