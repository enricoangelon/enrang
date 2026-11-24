//! The suite of enrang-layout (plan a.2, g.1): SPEC 11's tables read from
//! `docs/SPEC.md` and laid out on both pointer widths, so the document and the code
//! cannot drift apart; every other worked size SPEC 11 and 7.6 state; classes,
//! objects, tuples, enums and nullables; the size limits; the errors; and generated
//! types checked against an independent model and the invariants of any layout.

#![forbid(unsafe_code)]

mod api;
mod classes;
mod enums;
mod forms;
mod limits;
mod objects;
mod props;
mod support;
mod table;
mod worked;

use std::process::ExitCode;

use enrang_testkit::Harness;

/// This suite's share of the 2,500 cases TESTING 23 asks of M2 (plan g.8): every
/// case here is M2's.
pub const M2_SHARE: usize = 150;

fn main() -> ExitCode {
    let mut h = Harness::new("layout");
    table::register(&mut h);
    worked::register(&mut h);
    forms::register(&mut h);
    classes::register(&mut h);
    objects::register(&mut h);
    enums::register(&mut h);
    limits::register(&mut h);
    props::register(&mut h);
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
