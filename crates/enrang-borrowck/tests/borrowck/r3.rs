//! Stage 2F's tests of R3's definition check (M3 plan d.9): the fixtures under
//! `tests/mir/borrowck/r3/held/` need stage 2E's `held`, so they run once it
//! finds keys and are counted as skipped before.

use enrang_testkit::Harness;

pub fn register(h: &mut Harness) {
    crate::infer::register_dir(h, "r3/held", true);
}
