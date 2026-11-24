//! A panic is exit status 3. `enrang-suite` shows the same from outside a process.

use enrang_cli::{EXIT_INTERNAL, Outcome, guarded};
use enrang_testkit::{Harness, golden};

use crate::support::{INPROCESS_SUITE, inproc};

fn good() -> Outcome {
    inproc(&["--version"])
}

pub fn register(h: &mut Harness) {
    h.case(
        "internal/a body that returns passes through untouched",
        || {
            assert_eq!(guarded(good), good());
            assert_eq!(guarded(|| inproc(&["lsp"])), inproc(&["lsp"]));
        },
    );
    h.case("internal/a panic with a text is exit status 3", || {
        let outcome = guarded(|| -> Outcome { panic!("the table is empty") });
        assert_eq!(outcome.code, EXIT_INTERNAL);
        assert_eq!(outcome.stdout, "");
        assert_eq!(
            outcome.stderr,
            "error: internal compiler error: the table is empty\nnote: this is a bug in enrang, not in your command\n"
        );
    });
    h.case("internal/a panic with a formatted text keeps it", || {
        let row = 7;
        let outcome = guarded(|| -> Outcome { panic!("row {row} is wrong") });
        assert!(
            outcome.stderr.contains("row 7 is wrong"),
            "{}",
            outcome.stderr
        );
    });
    h.case("internal/a panic with no text still reports", || {
        let outcome = guarded(|| -> Outcome { std::panic::panic_any(5_u32) });
        assert_eq!(outcome.code, EXIT_INTERNAL);
        assert!(
            outcome.stderr.contains("a panic with no message"),
            "{}",
            outcome.stderr
        );
    });
    h.case(
        "internal/control characters in a panic stay out of the terminal",
        || {
            let outcome = guarded(|| -> Outcome { panic!("bad\x1b[2Jtext") });
            assert!(
                outcome.stderr.contains("bad\\u{1b}[2Jtext"),
                "{}",
                outcome.stderr
            );
            assert!(!outcome.stderr.contains('\x1b'));
        },
    );
    h.case("golden/internal_error.txt", || {
        let outcome = guarded(|| -> Outcome { panic!("a deliberate panic") });
        golden(INPROCESS_SUITE, "internal_error.txt", &outcome.stderr)
    });
    h.case("golden/internal_error_with_no_text.txt", || {
        let outcome = guarded(|| -> Outcome { std::panic::panic_any(5_u32) });
        golden(
            INPROCESS_SUITE,
            "internal_error_with_no_text.txt",
            &outcome.stderr,
        )
    });
}
