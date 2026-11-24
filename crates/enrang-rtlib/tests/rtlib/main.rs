//! The suite of enrang-rtlib: the embedded table against `lib/` on disk, lookup,
//! folders and the per-target map, and the signature stub read as text against
//! SPEC and ARCHITECTURE. This crate depends on nothing that parses (ARCHITECTURE
//! 1), so parsing the library in library mode and printing it back is the sema
//! suite's (`library.rs`).

#![forbid(unsafe_code)]

mod api;
mod layers;
mod support;
mod table;
mod targets;

use std::process::ExitCode;

use enrang_testkit::Harness;

/// This suite's share of the 2,500 more cases TESTING 23 asks of M2 (plan g.8):
/// every case here is M2's. `enrang-suite`'s meta-tests check that the shares of the
/// suites add up to the count TESTING 23 gives. The plan's 50 was a forecast; the
/// table needed fewer cases, and the shares still add up (M2 bump).
pub const M2_SHARE: usize = 20;

fn main() -> ExitCode {
    let mut h = Harness::new("rtlib");
    table::register(&mut h);
    targets::register(&mut h);
    layers::register(&mut h);
    api::register(&mut h);
    let m2 = h.len();
    h.case(
        "count/this suite holds its share of M2's cases",
        move || {
            assert!(m2 >= M2_SHARE, "{m2} cases, short of {M2_SHARE}");
        },
    );
    h.run()
}
