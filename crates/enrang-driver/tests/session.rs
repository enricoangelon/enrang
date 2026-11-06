//! A session buffers diagnostics and renders them as SPEC 13.1 says.

#![forbid(unsafe_code)]

use std::path::PathBuf;
use std::sync::Arc;

use enrang_base::{BytePos, FileOrigin, SourceMap, Span};
use enrang_diag::{Code, DiagCtx, Diagnostic, Help, RenderOpts};
use enrang_driver::Session;

fn plain() -> RenderOpts {
    RenderOpts::default()
}

/// A session over a map holding one file, and where the map placed it.
fn with_file(text: &str) -> (Session, u32) {
    let mut map = SourceMap::new();
    let id = map.add(PathBuf::from("a.en"), Arc::from(text), FileOrigin::User);
    let start = map.file(id).start.0;
    let session = Session {
        map: Arc::new(map),
        dcx: DiagCtx::new(),
    };
    (session, start)
}

fn span(start: u32, lo: u32, hi: u32) -> Span {
    Span {
        lo: BytePos(start + lo),
        hi: BytePos(start + hi),
    }
}

#[test]
fn a_new_session_has_nothing_to_say() {
    let mut session = Session::new();
    assert!(!session.dcx.has_errors());
    assert_eq!(session.render(&plain()), "");
}

#[test]
fn a_session_renders_against_the_map_it_was_given() {
    let (mut session, start) = with_file("let x;\n");
    session.dcx.emit(Diagnostic::new(
        Code::EN0601,
        "used after a move",
        span(start, 4, 5),
        "here",
    ));
    assert_eq!(
        session.render(&plain()),
        "error[EN0601]: used after a move\n --> a.en:1:5\n  |\n1 | let x;\n  |     ^ here\n  |\n  = explain: run `enrang explain EN0601`\n\nerror: aborting due to 1 previous error\n",
    );
}

#[test]
fn a_command_line_error_renders_with_its_explain_line_and_the_abort_line() {
    let mut session = Session::new();
    session
        .dcx
        .emit(Diagnostic::spanless(Code::EN1301, "`enrang fmt` is out"));
    assert!(session.dcx.has_errors());
    assert_eq!(
        session.render(&plain()),
        "error[EN1301]: `enrang fmt` is out\n  = explain: run `enrang explain EN1301`\n\nerror: aborting due to 1 previous error\n",
    );
}

#[test]
fn entries_and_helps_render_in_the_order_of_the_format() {
    let mut session = Session::new();
    session.dcx.emit(
        Diagnostic::spanless(Code::EN1302, "head")
            .note("a note")
            .with_help(Help::text("a help")),
    );
    assert_eq!(
        session.render(&plain()),
        "error[EN1302]: head\n  = note: a note\nhelp: a help\n  = explain: run `enrang explain EN1302`\n\nerror: aborting due to 1 previous error\n",
    );
}

#[test]
fn diagnostics_with_equal_spans_keep_the_order_they_were_emitted_in() {
    let mut session = Session::new();
    session.dcx.emit(Diagnostic::spanless(Code::EN1302, "one"));
    session.dcx.emit(Diagnostic::spanless(Code::EN1301, "two"));
    assert_eq!(
        session.render(&plain()),
        "error[EN1302]: one\n  = explain: run `enrang explain EN1302`\n\nerror[EN1301]: two\n  = explain: run `enrang explain EN1301`\n\nerror: aborting due to 2 previous errors\n",
    );
}

#[test]
fn diagnostics_with_places_render_in_order_of_position() {
    let (mut session, start) = with_file("abc\n");
    session
        .dcx
        .emit(Diagnostic::new(Code::EN0601, "late", span(start, 2, 3), ""));
    session.dcx.emit(Diagnostic::new(
        Code::EN0601,
        "early",
        span(start, 0, 1),
        "",
    ));
    let text = session.render(&plain());
    let early = text.find("error[EN0601]: early").expect("the first");
    let late = text.find("error[EN0601]: late").expect("the second");
    assert!(early < late, "{text}");
}

#[test]
fn the_same_code_and_message_with_no_place_is_reported_once() {
    let mut session = Session::new();
    session.dcx.emit(Diagnostic::spanless(Code::EN1301, "same"));
    session.dcx.emit(Diagnostic::spanless(Code::EN1301, "same"));
    let text = session.render(&plain());
    assert_eq!(text.matches("error[EN1301]: same\n").count(), 1, "{text}");
    assert!(
        text.ends_with("error: aborting due to 1 previous error\n"),
        "{text}"
    );
}

#[test]
fn different_command_line_errors_under_one_code_are_all_reported() {
    let mut session = Session::new();
    session.dcx.emit(Diagnostic::spanless(
        Code::EN1304,
        "`--image` and `--format` cannot be combined",
    ));
    session.dcx.emit(Diagnostic::spanless(
        Code::EN1304,
        "`--stack-size` does not fit target `i386-linux`",
    ));
    session
        .dcx
        .emit(Diagnostic::spanless(Code::EN1305, "file not found: a.en"));
    session
        .dcx
        .emit(Diagnostic::spanless(Code::EN1305, "file not found: b.en"));
    let text = session.render(&plain());
    for head in [
        "error[EN1304]: `--image` and `--format` cannot be combined\n",
        "error[EN1304]: `--stack-size` does not fit target `i386-linux`\n",
        "error[EN1305]: file not found: a.en\n",
        "error[EN1305]: file not found: b.en\n",
    ] {
        assert!(text.contains(head), "{head}: {text}");
    }
    assert!(
        text.ends_with("error: aborting due to 4 previous errors\n"),
        "{text}"
    );
}

#[test]
fn a_warning_alone_is_not_an_error_and_aborts_nothing() {
    let mut session = Session::new();
    session
        .dcx
        .emit(Diagnostic::spanless(Code::EN0430, "truncates"));
    assert!(!session.dcx.has_errors());
    assert_eq!(session.render(&plain()), "warning[EN0430]: truncates\n");
}

#[test]
fn a_note_alone_is_not_an_error_and_aborts_nothing() {
    let mut session = Session::new();
    session
        .dcx
        .emit(Diagnostic::bare_note(Code::EN0909, "resolves"));
    assert!(!session.dcx.has_errors());
    assert_eq!(session.dcx.finish_phase(), Ok(()));
    assert_eq!(session.render(&plain()), "note: resolves\n");
}

#[test]
fn rendering_empties_the_buffer_but_keeps_the_verdict() {
    let mut session = Session::new();
    session.dcx.emit(Diagnostic::spanless(Code::EN1301, "once"));
    assert!(!session.render(&plain()).is_empty());
    assert_eq!(session.render(&plain()), "");
    assert!(session.dcx.has_errors());
}

#[test]
fn colour_is_exactly_what_the_options_ask_for() {
    let diag = || Diagnostic::spanless(Code::EN1301, "head");
    let mut plain_session = Session::new();
    plain_session.dcx.emit(diag());
    let plain_text = plain_session.render(&plain());
    assert!(!plain_text.contains('\x1b'), "{plain_text:?}");

    let mut painted_session = Session::new();
    painted_session.dcx.emit(diag());
    let painted = painted_session.render(&RenderOpts { color: true });
    assert!(painted.contains("\x1b["), "{painted:?}");
    assert_ne!(painted, plain_text);
}
