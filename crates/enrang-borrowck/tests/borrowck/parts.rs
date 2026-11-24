//! Stage 2F's tests of stage 4's part test (M3 plan d.8): the fixtures under
//! `tests/mir/borrowck/parts/held/` need stage 2E's `held`, so they run once it
//! finds keys and are counted as skipped before.

use enrang_testkit::Harness;

pub fn register(h: &mut Harness) {
    crate::infer::register_dir(h, "parts/held", true);
}
