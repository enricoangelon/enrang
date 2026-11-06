//! The meta-tests of TESTING 18 that can run at this milestone. They look at the
//! repository and at the command line as a process, not at any one crate's insides.

#![forbid(unsafe_code)]

mod coverage;
mod determinism;
mod docs;
mod for_of_docs;
mod forbid;
mod gating;
mod goldens;
mod hermetic;
mod process;
mod readme;
mod support;

use std::process::ExitCode;

use enrang_testkit::Harness;

fn main() -> ExitCode {
    let mut h = Harness::new("meta");
    hermetic::register(&mut h);
    forbid::register(&mut h);
    gating::register(&mut h);
    goldens::register(&mut h);
    determinism::register(&mut h);
    coverage::register(&mut h);
    docs::register(&mut h);
    for_of_docs::register(&mut h);
    readme::register(&mut h);
    process::register(&mut h);
    h.run()
}
