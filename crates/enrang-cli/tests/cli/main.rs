//! The acceptance suite of the `enrang` binary.
//!
//! Golden cases run the real binary as a process. The broad tables run the same
//! function in-process, since they ask the same question hundreds of times.

#![forbid(unsafe_code)]

mod arguments;
mod compile;
mod emit;
mod evidence;
mod explain;
mod formatting;
mod goldens;
mod help;
mod internal;
mod project;
mod streams;
mod support;
mod targets;
mod typos;
mod working;

use std::process::ExitCode;

use enrang_diag::{Code, Milestone};
use enrang_testkit::Harness;

/// This suite's share of the 2,500 cases TESTING 23 asks of M1, counted by
/// [`is_m1`]. `enrang-suite`'s meta-tests check that the shares of the suites add up
/// to the count TESTING 23 gives.
pub const M1_SHARE: usize = 950;

/// This suite's share of the 2,500 more cases TESTING 23 asks of M2, counted by
/// [`is_m2`]: the compile fixtures of M2's codes (plan g.8, which forecast 250).
pub const M2_SHARE: usize = 500;

/// This suite's share of the 4,000 more cases TESTING 23 asks of M3, counted by
/// [`is_m3`]: the compile fixtures of M3's codes, each firing fixture with its fixed
/// near-miss of the same name (M3 plan f.9, which forecast 1,700).
pub const M3_SHARE: usize = 1_390;

/// Whether a case tests what M1 delivers here: `check`, `fmt` and `init` with their
/// flags, transcripts and phase 0 codes, and the compile fixtures of M1's codes and
/// the runner's own cases, whose goldens are compared inside their `compile/` cases.
/// The names of other commands, typos of command names and explain pages are M0's,
/// whatever the code, and a fixture of an M2 or M3 code is that milestone's
/// ([`is_m2`], [`is_m3`]), counted once.
fn is_m1(name: &str) -> bool {
    M1_PREFIXES.iter().any(|prefix| name.starts_with(prefix)) && !is_m2(name) && !is_m3(name)
}

/// Whether a case runs a compile fixture of an M2 code: `compile/<CODE>/<file> ...`,
/// its directory a code that M2 delivers.
fn is_m2(name: &str) -> bool {
    name.strip_prefix("compile/")
        .and_then(|rest| rest.split_once('/'))
        .and_then(|(code, _)| Code::from_name(code))
        .is_some_and(|code| code.since() == Milestone::M2)
}

/// Whether a case runs a compile fixture of an M3 code: `compile/<CODE>/<file> ...`,
/// its directory a code that M3 delivers. Such fixtures land before M3's share is
/// declared, and count for no earlier milestone.
fn is_m3(name: &str) -> bool {
    name.strip_prefix("compile/")
        .and_then(|rest| rest.split_once('/'))
        .and_then(|(code, _)| Code::from_name(code))
        .is_some_and(|code| code.since() == Milestone::M3)
}

/// The prefixes of the names of [`is_m1`]'s cases.
const M1_PREFIXES: [&str; 11] = [
    "golden/check/",
    "golden/fmt/",
    "golden/init/",
    "golden/cli-project/",
    "project/",
    "working/",
    "compile/",
    "formatting/",
    "typo/check -",
    "typo/fmt -",
    "typo/init -",
];

fn main() -> ExitCode {
    let mut h = Harness::new("cli");
    h.goldens(support::SUITE);
    h.goldens(support::INPROCESS_SUITE);
    h.goldens(support::PROJECT_SUITE);
    h.goldens(support::COMPILE_SUITE);
    goldens::register(&mut h);
    help::register(&mut h);
    explain::register(&mut h);
    targets::register(&mut h);
    evidence::register(&mut h);
    arguments::register(&mut h);
    typos::register(&mut h);
    streams::register(&mut h);
    internal::register(&mut h);
    project::register(&mut h);
    working::register(&mut h);
    compile::register(&mut h);
    formatting::register(&mut h);
    let m1 = h.names().filter(|name| is_m1(name)).count();
    let m2 = h.names().filter(|name| is_m2(name)).count();
    let m3 = h.names().filter(|name| is_m3(name)).count();
    let dead: Vec<&str> = M1_PREFIXES
        .iter()
        .copied()
        .filter(|prefix| !h.names().any(|name| name.starts_with(prefix)))
        .collect();
    h.case("count/every prefix of M1's cases names some", move || {
        assert_eq!(dead, Vec::<&str>::new());
    });
    h.case(
        "count/this suite holds its share of M1's cases",
        move || {
            assert!(m1 >= M1_SHARE, "{m1} cases, short of {M1_SHARE}");
        },
    );
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
    h.case("count/a fixture of an M2 code counts for M2 alone", || {
        let m2 = "compile/EN0401/c05.fail.en reports what it anchors";
        let m1 = "compile/EN0201/a.fail.en reports what it anchors";
        let runner = "compile/the runner fails each fixture that breaks its rules";
        assert!(is_m2(m2) && !is_m1(m2));
        assert!(is_m1(m1) && !is_m2(m1));
        assert!(is_m1(runner) && !is_m2(runner));
        assert!(!is_m2("explain/every code/EN0401"));
    });
    h.case(
        "count/a fixture of an M3 code counts for no earlier share",
        || {
            let m3 = "compile/EN0706/hold_push.fail.en reports what it anchors";
            assert!(is_m3(m3) && !is_m2(m3) && !is_m1(m3));
            assert!(!is_m3("compile/EN0401/c05.fail.en reports what it anchors"));
            assert!(!is_m3("explain/every code/EN0706"));
        },
    );
    h.run()
}
