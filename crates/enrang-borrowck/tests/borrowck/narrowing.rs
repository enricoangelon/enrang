//! Stage 2F's tests of the narrowing check (N2, M3 plan d.11): each fixture
//! under `tests/mir/borrowck/narrowing/check/` runs through phase 3, its anchors
//! the EN0401s a writing record leaves before a narrowed use.

use enrang_testkit::Harness;

pub fn register(h: &mut Harness) {
    crate::infer::register_dir(h, "narrowing/check", false);
}
