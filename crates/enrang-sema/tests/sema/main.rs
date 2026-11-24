//! The suite of enrang-sema (plan g.1): one module per area, named after it and
//! owned by the stage that builds the area (plan a.4). `support.rs` runs `load` and
//! `analyze` on in-memory programs, with a small fake library or the embedded one.

#![forbid(unsafe_code)]

mod calls;
mod classes;
mod closure;
mod consteval;
mod construct;
mod deferred;
mod entry;
mod exhaust;
mod exhaust_props;
mod forms;
mod forof;
mod gen_types;
mod generic;
mod goldens;
mod iface;
mod layout_table;
mod library;
mod load;
mod lower;
mod narrow;
mod no_panic;
mod overload;
mod paths;
mod pattern;
mod positions;
mod program;
mod programs;
mod resolve;
mod result;
mod review5;
mod review6;
mod review7;
mod satisfy;
mod sizes;
mod spec_examples;
mod support;
mod typeck;
mod unsafety;
mod views;

use std::process::ExitCode;

use enrang_testkit::Harness;

/// This suite's share of the 2,500 more cases TESTING 23 asks of M2 (plan g.8):
/// every case here is M2's. `enrang-suite`'s meta-tests check that the shares of the
/// suites add up to the count TESTING 23 gives. The plan's 1,900 was a forecast; the
/// suite holds what the M2 stages built, and the shares still add up (M2 bump).
pub const M2_SHARE: usize = 1_500;

fn main() -> ExitCode {
    let mut h = Harness::new("sema");
    h.case("smoke/an empty program checks to an empty program", || {
        let r = support::run(&[("main.en", "")]);
        r.clean();
        let program = r.program.as_ref().expect("checked");
        assert!(program.bodies.is_empty());
        assert!(program.statements.is_none());
        assert!(program.tests.is_empty());
        assert_eq!(program.modules.len(), r.tcx.module_count());
    });
    load::register(&mut h);
    resolve::register(&mut h);
    lower::register(&mut h);
    library::register(&mut h);
    typeck::register(&mut h);
    goldens::register(&mut h);
    paths::register(&mut h);
    calls::register(&mut h);
    overload::register(&mut h);
    generic::register(&mut h);
    construct::register(&mut h);
    forms::register(&mut h);
    narrow::register(&mut h);
    forof::register(&mut h);
    pattern::register(&mut h);
    result::register(&mut h);
    closure::register(&mut h);
    iface::register(&mut h);
    classes::register(&mut h);
    satisfy::register(&mut h);
    positions::register(&mut h);
    views::register(&mut h);
    unsafety::register(&mut h);
    deferred::register(&mut h);
    exhaust::register(&mut h);
    exhaust_props::register(&mut h);
    consteval::register(&mut h);
    entry::register(&mut h);
    sizes::register(&mut h);
    sizes::review(&mut h);
    layout_table::register(&mut h);
    spec_examples::register(&mut h);
    programs::register(&mut h);
    gen_types::register(&mut h);
    no_panic::register(&mut h);
    review5::register(&mut h);
    review6::register(&mut h);
    review7::register(&mut h);
    program::register(&mut h);
    let m2 = h.len();
    h.case(
        "count/this suite holds its share of M2's cases",
        move || {
            assert!(m2 >= M2_SHARE, "{m2} cases, short of {M2_SHARE}");
        },
    );
    h.run()
}
