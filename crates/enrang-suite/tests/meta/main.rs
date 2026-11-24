//! The meta-tests of TESTING 18 that can run at this milestone. They look at the
//! repository and at the command line as a process, not at any one crate's insides.
//! The gates TESTING 23's M3 row adds are enforced since the bump that closed M3:
//! each of their lines is due, but those a later milestone's code or `H` row
//! brings.

#![forbid(unsafe_code)]

mod cases;
mod counts;
mod coverage;
mod covers;
mod determinism;
mod disagreements;
mod docs;
mod fixtures;
mod for_of_docs;
mod forbid;
mod gating;
mod goldens;
mod hermetic;
mod process;
mod readme;
mod row;
mod support;

use std::process::ExitCode;

use enrang_testkit::Harness;

/// This suite's share of the 4,000 more cases TESTING 23 asks of M3 (M3 plan f.9),
/// counted by [`is_m3`]: the cases of the gates TESTING 23's M3 row adds.
/// `counts.rs` checks that the shares of M3's suites add up.
pub const M3_SHARE: usize = 85;

/// The prefixes of the names of [`is_m3`]'s cases.
const M3_PREFIXES: [&str; 4] = ["covers/M3", "row/M3", "counts/M3", "disagreements/"];

/// Whether a case is one of the M3 gates'.
fn is_m3(name: &str) -> bool {
    M3_PREFIXES.iter().any(|prefix| name.starts_with(prefix))
}

fn main() -> ExitCode {
    let mut h = Harness::new("meta");
    hermetic::register(&mut h);
    forbid::register(&mut h);
    gating::register(&mut h);
    fixtures::register(&mut h);
    cases::register(&mut h);
    counts::register(&mut h);
    goldens::register(&mut h);
    determinism::register(&mut h);
    coverage::register(&mut h);
    covers::register(&mut h);
    disagreements::register(&mut h);
    docs::register(&mut h);
    for_of_docs::register(&mut h);
    readme::register(&mut h);
    process::register(&mut h);
    // Last but the share: it checks that every case TESTING 23's M2 and M3 rows are
    // mapped to is registered.
    row::register(&mut h);
    let m3 = h.names().filter(|name| is_m3(name)).count();
    h.case(
        "count/this suite holds its share of M3's cases",
        move || {
            assert!(m3 >= M3_SHARE, "{m3} cases, short of {M3_SHARE}");
        },
    );
    h.run()
}
