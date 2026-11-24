//! The suite of enrang-mir (M3 plan f.4): the text form's round trip over
//! hand-written modules and its pinned spellings and errors, the verifier on valid
//! MIR and a mutant per condition of each rule, the CFG tools and the dataflow
//! framework on small graphs with known fixpoints, and `remap_ids`.

#![forbid(unsafe_code)]

mod cfg;
mod dataflow;
mod remap;
mod roundtrip;
mod spellings;
mod support;
mod verify;

use std::process::ExitCode;

use enrang_testkit::Harness;

/// This suite's share of the 4,000 more cases TESTING 23 asks of M3 (M3 plan f.9,
/// which forecast 400): every case it registers, all of them M3's. `enrang-suite`'s
/// meta-tests check that the shares of M3's suites add up.
pub const M3_SHARE: usize = 215;

fn main() -> ExitCode {
    let mut h = Harness::new("mir");
    roundtrip::register(&mut h);
    roundtrip::register_more(&mut h);
    cfg::register(&mut h);
    dataflow::register(&mut h);
    remap::register(&mut h);
    spellings::register(&mut h);
    verify::register(&mut h);
    let m3 = h.len();
    h.case(
        "count/this suite holds its share of M3's cases",
        move || {
            assert!(m3 >= M3_SHARE, "{m3} cases, short of {M3_SHARE}");
        },
    );
    h.run()
}
