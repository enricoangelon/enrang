//! The suite of enrang-borrowck (M3 plan f.1): every `.mir` fixture under
//! `tests/mir/borrowck/<area>/` runs through phase 3 with no front end, its
//! diagnostics compared with its `//~ CODE "piece"` anchors (TESTING 7); and the
//! API's skeleton behaviour (stage 1B). Areas: smoke (1B); moves, marks,
//! elaborate (2D); held, access, loops, packed (2E); wlive, infer, parts, r3, fit,
//! narrowing (2F).

#![forbid(unsafe_code)]

mod access;
mod api;
mod elaborate;
mod fit;
mod fixtures;
mod held;
mod infer;
mod loops;
mod marks;
mod moves;
mod narrowing;
mod packed;
mod parts;
mod r3;
mod wlive;

use std::process::ExitCode;

use enrang_testkit::Harness;

/// This suite's share of the 4,000 more cases TESTING 23 asks of M3 (M3 plan f.9,
/// which forecast 900): every case it registers, all of them M3's. `enrang-suite`'s
/// meta-tests check that the shares of M3's suites add up.
pub const M3_SHARE: usize = 1_450;

fn main() -> ExitCode {
    let mut h = Harness::new("borrowck");
    fixtures::register(&mut h);
    api::register(&mut h);
    moves::register(&mut h);
    marks::register(&mut h);
    elaborate::register(&mut h);
    held::register(&mut h);
    access::register(&mut h);
    loops::register(&mut h);
    packed::register(&mut h);
    wlive::register(&mut h);
    infer::register(&mut h);
    parts::register(&mut h);
    r3::register(&mut h);
    fit::register(&mut h);
    narrowing::register(&mut h);
    let m3 = h.len();
    h.case(
        "count/this suite holds its share of M3's cases",
        move || {
            assert!(m3 >= M3_SHARE, "{m3} cases, short of {M3_SHARE}");
        },
    );
    h.run()
}
