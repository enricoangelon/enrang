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

use enrang_testkit::Harness;

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
    h.run()
}
