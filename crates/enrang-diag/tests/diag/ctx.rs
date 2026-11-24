//! `DiagCtx`: buffering, deduplication on code and primary span, phases and order.

use enrang_base::Span;
use enrang_diag::{Aborted, Code, DiagCtx, Diagnostic, Severity};
use enrang_testkit::Harness;

use crate::support::{Src, err, warn};

fn messages(diags: &[Diagnostic]) -> Vec<&str> {
    diags.iter().map(|diag| diag.message.as_str()).collect()
}

fn named(code: Code, message: &str, span: Span) -> Diagnostic {
    Diagnostic::new(code, message, span, "")
}

pub fn register(h: &mut Harness) {
    h.case("ctx/a new context has nothing", || {
        let mut dcx = DiagCtx::new();
        assert!(!dcx.has_errors());
        assert_eq!(dcx.finish_phase(), Ok(()));
        assert_eq!(dcx.take(), Vec::new());
    });
    h.case("ctx/default is new", || {
        let mut dcx = DiagCtx::default();
        assert!(!dcx.has_errors());
        assert_eq!(dcx.take(), Vec::new());
    });
    h.case(
        "ctx/take returns what was emitted and empties the buffer",
        || {
            let src = Src::new("a.en", "x\n");
            let mut dcx = DiagCtx::new();
            dcx.emit(err(src.find("x"), "p"));
            assert_eq!(dcx.take().len(), 1);
            assert_eq!(dcx.take().len(), 0);
        },
    );
    h.case("ctx/take sorts by position", || {
        let src = Src::new("a.en", "abc\n");
        let mut dcx = DiagCtx::new();
        dcx.emit(named(Code::EN0301, "c", src.find("c")));
        dcx.emit(named(Code::EN0301, "a", src.find("a")));
        dcx.emit(named(Code::EN0301, "b", src.find("b")));
        assert_eq!(messages(&dcx.take()), ["a", "b", "c"]);
    });
    h.case("ctx/take sorts by file, then position", || {
        let src = Src::files(&[("a.en", "ab\n"), ("b.en", "ab\n")]);
        let mut dcx = DiagCtx::new();
        dcx.emit(named(Code::EN0301, "b2", src.f(1).find("b")));
        dcx.emit(named(Code::EN0301, "a2", src.f(0).find("b")));
        dcx.emit(named(Code::EN0301, "b1", src.f(1).find("a")));
        dcx.emit(named(Code::EN0301, "a1", src.f(0).find("a")));
        assert_eq!(messages(&dcx.take()), ["a1", "a2", "b1", "b2"]);
    });
    h.case("ctx/one start sorts by span end", || {
        let src = Src::new("a.en", "abc\n");
        let mut dcx = DiagCtx::new();
        dcx.emit(named(Code::EN0301, "long", src.find("abc")));
        dcx.emit(named(Code::EN0302, "short", src.find("a")));
        assert_eq!(messages(&dcx.take()), ["short", "long"]);
    });
    h.case(
        "ctx/equal spans keep the order they were emitted in",
        || {
            let src = Src::new("a.en", "abc\n");
            let span = src.find("a");
            let mut dcx = DiagCtx::new();
            dcx.emit(named(Code::EN0303, "third code first", span));
            dcx.emit(named(Code::EN0301, "first code second", span));
            dcx.emit(named(Code::EN0302, "second code third", span));
            assert_eq!(
                messages(&dcx.take()),
                ["third code first", "first code second", "second code third"]
            );
        },
    );
    h.case("ctx/diagnostics with no span come first", || {
        let src = Src::new("a.en", "abc\n");
        let mut dcx = DiagCtx::new();
        dcx.emit(named(Code::EN0301, "placed", src.find("a")));
        dcx.emit(Diagnostic::spanless(Code::EN1301, "spanless"));
        assert_eq!(messages(&dcx.take()), ["spanless", "placed"]);
    });
    h.case("ctx/a repeat of code and primary span is dropped", || {
        let src = Src::new("a.en", "abc\n");
        let mut dcx = DiagCtx::new();
        dcx.emit(named(Code::EN0301, "first", src.find("a")));
        dcx.emit(named(Code::EN0301, "second", src.find("a")));
        assert_eq!(messages(&dcx.take()), ["first"]);
    });
    h.case(
        "ctx/dedupe ignores everything else in the diagnostic",
        || {
            let src = Src::new("a.en", "abc\n");
            let mut dcx = DiagCtx::new();
            dcx.emit(err(src.find("a"), "one").note("n"));
            dcx.emit(err(src.find("a"), "other").with_secondary(src.find("b"), "s"));
            assert_eq!(dcx.take().len(), 1);
        },
    );
    h.case("ctx/another code on one span is kept", || {
        let src = Src::new("a.en", "abc\n");
        let mut dcx = DiagCtx::new();
        dcx.emit(named(Code::EN0301, "a", src.find("a")));
        dcx.emit(named(Code::EN0302, "b", src.find("a")));
        assert_eq!(dcx.take().len(), 2);
    });
    h.case("ctx/one code on another span is kept", || {
        let src = Src::new("a.en", "abc\n");
        let mut dcx = DiagCtx::new();
        dcx.emit(named(Code::EN0301, "a", src.find("a")));
        dcx.emit(named(Code::EN0301, "b", src.find("b")));
        dcx.emit(named(Code::EN0301, "ab", src.find("ab")));
        assert_eq!(dcx.take().len(), 3);
    });
    h.case(
        "ctx/the same offset in another file is another span",
        || {
            let src = Src::files(&[("a.en", "x\n"), ("b.en", "x\n")]);
            let mut dcx = DiagCtx::new();
            dcx.emit(named(Code::EN0301, "a", src.f(0).find("x")));
            dcx.emit(named(Code::EN0301, "b", src.f(1).find("x")));
            assert_eq!(dcx.take().len(), 2);
        },
    );
    h.case("ctx/reported knows each code and span emitted", || {
        let src = Src::new("a.en", "abc\n");
        let mut dcx = DiagCtx::new();
        assert!(!dcx.reported(Code::EN0301, src.find("a")));
        dcx.emit(named(Code::EN0301, "a", src.find("a")));
        assert!(dcx.reported(Code::EN0301, src.find("a")));
        assert!(!dcx.reported(Code::EN0302, src.find("a")), "another code");
        assert!(!dcx.reported(Code::EN0301, src.find("b")), "another span");
        assert!(!dcx.reported(Code::EN0301, src.find("ab")), "a wider span");
        dcx.take();
        assert!(dcx.reported(Code::EN0301, src.find("a")), "taken or not");
    });
    h.case("ctx/reported is false for a dummy span", || {
        let mut dcx = DiagCtx::new();
        dcx.emit(Diagnostic::spanless(Code::EN1301, "spanless"));
        assert!(!dcx.reported(Code::EN1301, Span::DUMMY));
    });
    h.case("ctx/a dedupe outlasts take", || {
        let src = Src::new("a.en", "abc\n");
        let mut dcx = DiagCtx::new();
        dcx.emit(err(src.find("a"), "p"));
        dcx.take();
        dcx.emit(err(src.find("a"), "p"));
        assert_eq!(dcx.take().len(), 0);
    });
    h.case("ctx/a dedupe outlasts a phase", || {
        let src = Src::new("a.en", "abc\n");
        let mut dcx = DiagCtx::new();
        dcx.emit(warn(src.find("a"), "p"));
        assert_eq!(dcx.finish_phase(), Ok(()));
        dcx.emit(warn(src.find("a"), "p"));
        assert_eq!(dcx.take().len(), 1);
    });
    h.case(
        "ctx/spanless diagnostics are different by their message",
        || {
            let mut dcx = DiagCtx::new();
            dcx.emit(Diagnostic::spanless(
                Code::EN1304,
                "`--image` and `--format`",
            ));
            dcx.emit(Diagnostic::spanless(Code::EN1304, "`--stack-size`"));
            dcx.emit(Diagnostic::spanless(Code::EN1305, "file not found: a.en"));
            dcx.emit(Diagnostic::spanless(Code::EN1305, "file not found: b.en"));
            assert_eq!(
                messages(&dcx.take()),
                [
                    "`--image` and `--format`",
                    "`--stack-size`",
                    "file not found: a.en",
                    "file not found: b.en"
                ]
            );
        },
    );
    h.case("ctx/a spanless repeat is still one mistake", || {
        let mut dcx = DiagCtx::new();
        dcx.emit(Diagnostic::spanless(Code::EN1301, "a"));
        dcx.emit(Diagnostic::spanless(Code::EN1301, "a"));
        dcx.emit(Diagnostic::spanless(Code::EN1302, "a"));
        assert_eq!(messages(&dcx.take()), ["a", "a"]);
    });
    h.case("ctx/a spanless repeat outlasts take", || {
        let mut dcx = DiagCtx::new();
        dcx.emit(Diagnostic::spanless(Code::EN1301, "a"));
        dcx.take();
        dcx.emit(Diagnostic::spanless(Code::EN1301, "a"));
        assert_eq!(dcx.take().len(), 0);
    });
    h.case("ctx/a note fails nothing and is still reported", || {
        let mut dcx = DiagCtx::new();
        dcx.emit(Diagnostic::bare_note(Code::EN0909, "resolves"));
        assert_eq!(dcx.finish_phase(), Ok(()));
        assert!(!dcx.has_errors());
        assert_eq!(messages(&dcx.take()), ["resolves"]);
    });
    h.case("ctx/an error fails its phase", || {
        let src = Src::new("a.en", "x\n");
        let mut dcx = DiagCtx::new();
        dcx.emit(err(src.find("x"), "p"));
        assert_eq!(dcx.finish_phase(), Err(Aborted));
    });
    h.case("ctx/a test verdict fails its phase", || {
        let src = Src::new("a.en", "x\n");
        let mut dcx = DiagCtx::new();
        dcx.emit(Diagnostic::new(Code::T0001, "m", src.find("x"), "p"));
        assert_eq!(dcx.finish_phase(), Err(Aborted));
        assert!(dcx.has_errors());
    });
    h.case("ctx/a warning does not fail its phase", || {
        let src = Src::new("a.en", "x\n");
        let mut dcx = DiagCtx::new();
        dcx.emit(warn(src.find("x"), "p"));
        assert_eq!(dcx.finish_phase(), Ok(()));
        assert!(!dcx.has_errors());
        assert_eq!(dcx.take().len(), 1, "the warning is still reported");
    });
    h.case("ctx/a warning after an error leaves it failed", || {
        let src = Src::new("a.en", "ab\n");
        let mut dcx = DiagCtx::new();
        dcx.emit(err(src.find("a"), "p"));
        dcx.emit(warn(src.find("b"), "p"));
        assert_eq!(dcx.finish_phase(), Err(Aborted));
    });
    h.case("ctx/finish_phase looks only at this phase", || {
        let src = Src::new("a.en", "ab\n");
        let mut dcx = DiagCtx::new();
        dcx.emit(err(src.find("a"), "p"));
        assert_eq!(dcx.finish_phase(), Err(Aborted));
        assert_eq!(dcx.finish_phase(), Ok(()), "that phase is over");
        dcx.emit(warn(src.find("b"), "p"));
        assert_eq!(dcx.finish_phase(), Ok(()));
    });
    h.case("ctx/has_errors outlasts its phase and take", || {
        let src = Src::new("a.en", "x\n");
        let mut dcx = DiagCtx::new();
        dcx.emit(err(src.find("x"), "p"));
        assert!(dcx.has_errors());
        let _ = dcx.finish_phase();
        assert!(dcx.has_errors());
        dcx.take();
        assert!(dcx.has_errors());
    });
    h.case("ctx/a dropped repeat does not fail a later phase", || {
        let src = Src::new("a.en", "x\n");
        let mut dcx = DiagCtx::new();
        dcx.emit(err(src.find("x"), "p"));
        assert_eq!(dcx.finish_phase(), Err(Aborted));
        dcx.emit(err(src.find("x"), "p"));
        assert_eq!(dcx.finish_phase(), Ok(()));
    });
    h.case(
        "ctx/the driver's loop: phases until the first failing one",
        || {
            let src = Src::new("a.en", "abc\n");
            let mut dcx = DiagCtx::new();
            let mut reached = Vec::new();
            let phases: [(&str, Vec<Diagnostic>); 3] = [
                ("syntax", vec![warn(src.find("a"), "p")]),
                (
                    "sema",
                    vec![err(src.find("c"), "p"), err(src.find("b"), "p")],
                ),
                ("borrowck", vec![err(src.find("a"), "p")]),
            ];
            for (name, diags) in phases {
                reached.push(name);
                for diag in diags {
                    dcx.emit(diag);
                }
                if dcx.finish_phase().is_err() {
                    break;
                }
            }
            assert_eq!(reached, ["syntax", "sema"]);
            let severities: Vec<Severity> = dcx.take().iter().map(|diag| diag.severity).collect();
            assert_eq!(
                severities,
                [Severity::Warning, Severity::Error, Severity::Error]
            );
        },
    );
}
