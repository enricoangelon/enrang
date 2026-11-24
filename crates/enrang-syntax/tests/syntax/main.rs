//! The acceptance suite of enrang-syntax.
//!
//! Every case registers on the testkit harness, so `--list` shows the whole suite
//! and a filter can select any row of any table. Where SPEC states a table, the
//! suite reads it from `docs/`, so code and document cannot drift apart.

#![forbid(unsafe_code)]

mod api;
mod explain;
mod fixtures;
mod fmt;
mod r#gen;
mod hints;
mod lexer;
mod lexer_props;
mod parser;
mod parser_props;
mod precedence;
mod printer_comments;
mod printer_props;
mod printer_rules;
mod recovery;
mod support;
mod tokens;
mod trees;

use std::process::ExitCode;

use enrang_testkit::Harness;

/// This suite's share of the 2,500 cases TESTING 23 asks of M1: every case here is
/// M1's. `enrang-suite`'s meta-tests check that the shares of the suites add up to
/// the count TESTING 23 gives.
pub const M1_SHARE: usize = 1_800;

fn main() -> ExitCode {
    let mut h = Harness::new("syntax");
    tokens::register(&mut h);
    lexer::register(&mut h);
    lexer_props::register(&mut h);
    parser::register(&mut h);
    parser_props::register(&mut h);
    precedence::register(&mut h);
    trees::register(&mut h);
    recovery::register(&mut h);
    hints::register(&mut h);
    api::register(&mut h);
    explain::register(&mut h);
    fixtures::register(&mut h);
    fmt::register(&mut h);
    printer_rules::register(&mut h);
    printer_comments::register(&mut h);
    printer_props::register(&mut h);
    r#gen::register(&mut h);
    let m1 = h.len();
    h.case(
        "count/this suite holds its share of M1's cases",
        move || {
            assert!(m1 >= M1_SHARE, "{m1} cases, short of {M1_SHARE}");
        },
    );
    h.run()
}
