//! The acceptance suite of enrang-diag.
//!
//! Every case registers on the testkit harness, so `--list` shows the whole suite
//! and a filter can select any row of any table.

#![forbid(unsafe_code)]

mod color;
mod ctx;
mod docs;
mod entries;
mod explain;
mod fixes;
mod gaps;
mod goldens;
mod gutter;
mod helps;
mod json;
mod json_value;
mod labels;
mod properties;
mod registry;
mod suggest;
mod summary;
mod support;
mod terminal;

use std::process::ExitCode;

use enrang_diag::{Code, Milestone};
use enrang_testkit::Harness;

/// This suite's share of the 2,500 more cases TESTING 23 asks of M2, counted by
/// [`is_m2`]: the cases of the explain pages of M2's codes, which TESTING 23's
/// "every `since(M2)` code" asks for beside a fixture and a near-miss. The rest of
/// the suite is M0's. `enrang-suite`'s meta-tests check that the shares of the suites
/// add up to the count TESTING 23 gives (M2 bump).
pub const M2_SHARE: usize = 300;

/// Whether a case checks the explain page of an M2 code: `explain/<CODE>/...`.
fn is_m2(name: &str) -> bool {
    name.strip_prefix("explain/")
        .and_then(|rest| rest.split_once('/'))
        .and_then(|(code, _)| Code::from_name(code))
        .is_some_and(|code| code.since() == Milestone::M2)
}

/// This suite's share of the 4,000 more cases TESTING 23 asks of M3, counted by
/// [`is_m3`]: the cases of the explain pages of M3's codes, which TESTING 23's
/// "every `since(M3)` code" asks for beside a fixture and a near-miss (M3 plan f.9,
/// which forecast 60).
pub const M3_SHARE: usize = 85;

/// Whether a case checks the explain page of an M3 code: `explain/<CODE>/...`.
fn is_m3(name: &str) -> bool {
    name.strip_prefix("explain/")
        .and_then(|rest| rest.split_once('/'))
        .and_then(|(code, _)| Code::from_name(code))
        .is_some_and(|code| code.since() == Milestone::M3)
}

fn main() -> ExitCode {
    let mut h = Harness::new("diag");
    goldens::register(&mut h);
    registry::register(&mut h);
    gutter::register(&mut h);
    labels::register(&mut h);
    gaps::register(&mut h);
    entries::register(&mut h);
    helps::register(&mut h);
    summary::register(&mut h);
    color::register(&mut h);
    json_value::register(&mut h);
    json::register(&mut h);
    fixes::register(&mut h);
    suggest::register(&mut h);
    ctx::register(&mut h);
    explain::register(&mut h);
    docs::register(&mut h);
    terminal::register(&mut h);
    properties::register(&mut h);
    let m2 = h.names().filter(|name| is_m2(name)).count();
    let m3 = h.names().filter(|name| is_m3(name)).count();
    h.case(
        "count/this suite holds its share of M2's cases",
        move || {
            assert!(m2 >= M2_SHARE, "{m2} cases, short of {M2_SHARE}");
        },
    );
    h.case(
        "count/this suite holds its share of M3's cases",
        move || {
            assert!(m3 >= M3_SHARE, "{m3} cases, short of {M3_SHARE}");
        },
    );
    h.case("count/the M2 cases are the pages of M2's codes", || {
        assert!(is_m2("explain/EN0401/its rule is one paragraph"));
        assert!(!is_m2("explain/EN0201/its rule is one paragraph"));
        assert!(!is_m2("explain/EN0601/its rule is one paragraph"));
        assert!(!is_m2("explain/EN0401"));
        assert!(!is_m2("registry/row/EN0401"));
    });
    h.case("count/the M3 cases are the pages of M3's codes", || {
        assert!(is_m3("explain/EN0601/its rule is one paragraph"));
        assert!(!is_m3("explain/EN0401/its rule is one paragraph"));
        assert!(!is_m3("explain/EN0601"));
        assert!(!is_m3("registry/row/EN0601"));
    });
    h.run()
}
