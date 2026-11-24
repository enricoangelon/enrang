//! A session buffers diagnostics and renders them as SPEC 13.1 says, and the
//! pipeline loads, parses, type-checks and formats files through it: `check` runs
//! phases 1, 2 and 4's size check for the target it is given.

#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::sync::{Arc, OnceLock};

use enrang_base::{BytePos, FileOrigin, SourceMap, Span};
use enrang_diag::{Code, Diagnostic, Help, RenderOpts};
use enrang_driver::{CheckError, Session, check, format, test_part_of};
use enrang_target::{TargetOpts, TargetSpec, resolve};
use enrang_testkit::{Case, TempDir, extract_cases, workspace_root};

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
        ..Session::new()
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

/// The extracted cases of SPEC, read once.
fn spec_cases() -> &'static [Case] {
    static CASES: OnceLock<Vec<Case>> = OnceLock::new();
    CASES.get_or_init(|| {
        let spec = std::fs::read_to_string(workspace_root().join("docs/SPEC.md")).expect("SPEC");
        extract_cases(&spec).unwrap_or_else(|errors| panic!("{errors}"))
    })
}

fn spec_case(id: &str) -> &'static Case {
    spec_cases()
        .iter()
        .find(|case| case.id == id)
        .unwrap_or_else(|| panic!("SPEC has no case {id}"))
}

/// The target named `name`, as the command line resolves it.
fn target(name: &str) -> Arc<TargetSpec> {
    Arc::new(resolve(name, &TargetOpts::default()).expect("a target").0)
}

/// `check` of one file in a fresh session for `on`: the number of files of the
/// entry's module (its file, and its `.test.en` part when one was loaded), or why it
/// stopped, and the rendered stderr.
fn checked_on(dir: &Path, entry: &str, on: &str) -> (Result<usize, String>, String) {
    let mut session = Session::new();
    let result = match check(&mut session, dir, Path::new(entry), target(on)) {
        Ok(checked) => {
            let (_, module) = checked.tcx.modules().next().expect("the entry module");
            assert!(!module.library);
            Ok(1 + usize::from(module.test_part.is_some()))
        }
        Err(CheckError::Aborted(_)) => Err("aborted".to_owned()),
        Err(CheckError::Unreadable { path, error }) => {
            Err(format!("unreadable {}: {}", path.display(), error.kind()))
        }
        Err(CheckError::Internal(e)) => Err(format!("internal: {}", e.0)),
    };
    assert_eq!(
        session.target.as_ref().map(|spec| spec.name),
        Some(target(on).name),
        "the session keeps the target it checked for"
    );
    (result, session.render(&plain()))
}

/// [`checked_on`] the host's target.
fn checked(dir: &Path, entry: &str) -> (Result<usize, String>, String) {
    checked_on(dir, entry, enrang_target::host_target())
}

#[test]
fn the_g_cases_of_m1_and_m2_render_byte_for_byte_through_check() {
    for id in [
        "G01", "G02", "G03", "G04", "G05", "G06", "G12", "G13", "G17", "G19", "G20", "G22",
    ] {
        let case = spec_case(id);
        let dir = TempDir::new("g");
        for file in &case.files {
            dir.write(&file.name, &file.contents);
        }
        let entry = &case.files[0].name;
        assert_eq!(case.cmd, format!("enrang check {entry}"), "{id}");
        let (result, stderr) = checked(dir.path(), entry);
        assert_eq!(result, Err("aborted".to_owned()), "{id}");
        assert_eq!(stderr, case.stderr.text, "{id}");
    }
}

#[test]
fn the_ownership_block_and_the_tour_pass_phases_1_and_2() {
    for id in ["ownership", "tour"] {
        let case = spec_case(id);
        let dir = TempDir::new("spec");
        for file in &case.files {
            dir.write(&file.name, &file.contents);
        }
        let (result, stderr) = checked(dir.path(), &case.files[0].name);
        assert_eq!(result, Ok(1), "{id}: {stderr}");
        assert_eq!(stderr, "", "{id}");
    }
}

#[test]
fn a_module_is_its_file_then_its_test_part() {
    let dir = TempDir::new("parts");
    dir.write("m.en", "const a = 1\n");
    dir.write("m.test.en", "const b = 2\ntest(\"t\", () => {});\n");
    let (result, stderr) = checked(dir.path(), "m.en");
    assert_eq!(result, Err("aborted".to_owned()));
    let first = stderr.find(" --> m.en:1:12").expect("the file's error");
    let second = stderr
        .find(" --> m.test.en:1:12")
        .expect("the part's error");
    assert!(first < second, "{stderr}");
    assert!(
        stderr.ends_with("error: aborting due to 2 previous errors\n"),
        "{stderr}"
    );
    assert!(
        !stderr.contains("EN1112"),
        "a test part holds tests: {stderr}"
    );
}

#[test]
fn a_module_with_no_test_part_is_one_file() {
    let dir = TempDir::new("one");
    dir.write("m.en", "const a = 1;\n");
    assert_eq!(checked(dir.path(), "m.en"), (Ok(1), String::new()));
    dir.write("m.test.en", "test(\"t\", () => {});\n");
    assert_eq!(checked(dir.path(), "m.en"), (Ok(2), String::new()));
}

#[test]
fn a_test_part_given_alone_is_checked_alone() {
    // A part whose module file does not exist has nothing else to see.
    let dir = TempDir::new("alone");
    dir.write("m.test.en", "test(\"t\", () => {});\n");
    assert_eq!(checked(dir.path(), "m.test.en"), (Ok(1), String::new()));
}

/// A part sees its module's private items (SPEC 3.1, TESTING 1), so a part given as
/// the entry checks its module with it, as `enrang test` names a module by its part
/// (review 5A: a fresh `enrang init` project's `check src/main.test.en` was a false
/// EN0301).
#[test]
fn a_test_part_given_as_the_entry_checks_its_module_with_it() {
    let dir = TempDir::new("part");
    dir.write(
        "src/m.en",
        "private function greet(): string {\n  return \"hi\";\n}\n",
    );
    dir.write(
        "src/m.test.en",
        "test(\"t\", () => { expect(greet()).toBe(\"hi\"); });\n",
    );
    for spelled in ["src/m.test.en", "./src/../src/m.test.en"] {
        assert_eq!(
            checked(dir.path(), spelled),
            (Ok(2), String::new()),
            "{spelled}"
        );
    }
    dir.write("src/m.en", "const a = 1\n");
    let (result, stderr) = checked(dir.path(), "src/m.test.en");
    assert_eq!(result, Err("aborted".to_owned()));
    assert!(stderr.contains(" --> src/m.en:1:12\n"), "{stderr}");
}

/// An absolute entry keeps its root, so `./x` is read beside it, whatever the
/// directory (review 5A: a false EN0305, then EN0301, for an absolute entry).
#[test]
fn an_absolute_entry_reads_its_relative_imports_beside_it() {
    let dir = TempDir::new("absolute");
    dir.write(
        "app/main.en",
        "import { twice } from \"./util\";\n\nconsole.log(twice(2));\n",
    );
    dir.write(
        "app/util.en",
        "public function twice(x: i64): i64 {\n  return x * 2;\n}\n",
    );
    let entry = dir.path().join("app/main.en");
    assert!(entry.is_absolute(), "{}", entry.display());
    let entry = entry.to_str().expect("a UTF-8 path").to_owned();
    assert_eq!(checked(dir.path(), &entry), (Ok(1), String::new()));
    let elsewhere = TempDir::new("elsewhere");
    assert_eq!(checked(elsewhere.path(), &entry), (Ok(1), String::new()));
    assert_eq!(checked(dir.path(), "app/main.en"), (Ok(1), String::new()));
    // A file that is missing beside it is still reported, at its absolute path.
    dir.write(
        "app/main.en",
        "import { twice } from \"./nope\";\n\nconsole.log(twice(2));\n",
    );
    let (result, stderr) = checked(dir.path(), &entry);
    assert_eq!(result, Err("aborted".to_owned()));
    assert!(stderr.contains(&format!(" --> {entry}:1:23\n")), "{stderr}");
    assert!(
        stderr.contains("aborting due to 1 previous error"),
        "{stderr}"
    );
}

#[test]
fn a_directory_where_the_test_part_would_be_is_no_part() {
    let dir = TempDir::new("dirpart");
    dir.write("m.en", "const a = 1;\n");
    std::fs::create_dir(dir.join("m.test.en")).expect("a directory");
    assert_eq!(checked(dir.path(), "m.en"), (Ok(1), String::new()));
}

/// A file is shown by its path relative to the directory, normalised, so a module
/// has one name however the entry was spelled (M2 plan d.2).
#[test]
fn paths_are_read_from_the_directory_and_shown_relative_to_it() {
    let dir = TempDir::new("shown");
    dir.write("src/main.en", "const a = 1\n");
    let (_, stderr) = checked(dir.path(), "src/main.en");
    assert!(stderr.contains(" --> src/main.en:1:12\n"), "{stderr}");
    for spelled in ["./src/main.en", "src/./main.en", "src/../src/main.en"] {
        let (_, stderr) = checked(dir.path(), spelled);
        assert!(
            stderr.contains(" --> src/main.en:1:12\n"),
            "{spelled}: {stderr}"
        );
    }
    assert!(
        !stderr.contains(&dir.path().display().to_string()),
        "{stderr}"
    );
}

#[test]
fn an_unreadable_entry_is_reported_with_its_path_as_written() {
    let dir = TempDir::new("missing");
    let (result, stderr) = checked(dir.path(), "nope.en");
    assert_eq!(
        result,
        Err("unreadable nope.en: entity not found".to_owned())
    );
    assert_eq!(stderr, "");
    std::fs::create_dir(dir.join("src")).expect("a directory");
    let (result, _) = checked(dir.path(), "src");
    assert_eq!(result, Err("unreadable src: is a directory".to_owned()));
}

/// A test part that exists and cannot be read stops `check` as an unreadable entry
/// does, naming the part: the module is never checked without it. File modes exist
/// only on unix and bind nobody who runs as root, who reads it, so the test then
/// says so and checks nothing.
#[cfg(unix)]
#[test]
fn an_unreadable_test_part_is_reported_and_never_skipped() {
    use std::os::unix::fs::PermissionsExt;
    let dir = TempDir::new("unreadable-part");
    dir.write("m.en", "const a = 1;\n");
    let part = dir.write("m.test.en", "test(\"t\", () => {});\n");
    let set_mode = |mode: u32| {
        std::fs::set_permissions(&part, std::fs::Permissions::from_mode(mode)).expect("a mode");
    };
    set_mode(0o000);
    if std::fs::read(&part).is_ok() {
        set_mode(0o644);
        eprintln!("file modes do not bind this user: nothing checked");
        return;
    }
    let outcome = checked(dir.path(), "m.en");
    set_mode(0o644);
    assert_eq!(
        outcome,
        (
            Err("unreadable m.test.en: permission denied".to_owned()),
            String::new()
        )
    );
}

#[test]
fn phase_2_runs_after_phase_1_and_reports_every_error_it_finds() {
    let dir = TempDir::new("phase2");
    dir.write("m.en", "const a: string = 1;\nconst b = totl;\n");
    let (result, stderr) = checked(dir.path(), "m.en");
    assert_eq!(result, Err("aborted".to_owned()));
    let first = stderr.find("error[EN0401]").expect("the type error");
    let second = stderr.find("error[EN0301]").expect("the unresolved name");
    assert!(first < second, "{stderr}");
    assert!(
        stderr.ends_with("error: aborting due to 2 previous errors\n"),
        "{stderr}"
    );
}

#[test]
fn a_syntax_error_stops_check_before_phase_2() {
    let dir = TempDir::new("phase1");
    dir.write("m.en", "const a: string = 1\n");
    let (result, stderr) = checked(dir.path(), "m.en");
    assert_eq!(result, Err("aborted".to_owned()));
    assert!(stderr.contains("error[EN0101]"), "{stderr}");
    assert!(!stderr.contains("EN0401"), "{stderr}");
}

#[test]
fn imports_are_loaded_and_checked_with_the_entry() {
    let dir = TempDir::new("imports");
    dir.write(
        "main.en",
        "import { twice } from \"./util\";\nconsole.log(twice(2));\n",
    );
    dir.write(
        "util.en",
        "public function twice(x: i64): i64 { return x * 2; }\n",
    );
    assert_eq!(checked(dir.path(), "main.en"), (Ok(1), String::new()));
    dir.write(
        "util.en",
        "public function twice(x: i64): string { return x * 2; }\n",
    );
    let (result, stderr) = checked(dir.path(), "main.en");
    assert_eq!(result, Err("aborted".to_owned()));
    assert!(stderr.contains(" --> util.en:1:"), "{stderr}");
}

#[test]
fn the_test_part_is_type_checked_with_the_module() {
    let dir = TempDir::new("typed-part");
    dir.write(
        "m.en",
        "public function greet(n: &string): string { return `Hi, ${n}`; }\n",
    );
    dir.write(
        "m.test.en",
        "test(\"greets\", () => { expect(greet(\"Ada\")).toBe(\"Hi, Ada\"); });\n",
    );
    assert_eq!(checked(dir.path(), "m.en"), (Ok(2), String::new()));
    dir.write(
        "m.test.en",
        "test(\"greets\", () => { expect(greet(5)).toBe(\"Hi\"); });\n",
    );
    let (result, stderr) = checked(dir.path(), "m.en");
    assert_eq!(result, Err("aborted".to_owned()));
    assert!(stderr.contains(" --> m.test.en:1:"), "{stderr}");
}

/// A clean program comes back checked: its user modules in topological order, each
/// after the modules it imports, ties broken by module path (A:884), whatever order
/// the imports were written and loaded in.
#[test]
fn a_clean_program_is_checked_in_topological_order() {
    let dir = TempDir::new("order");
    dir.write(
        "main.en",
        "import { b } from \"./b\";\nimport { a } from \"./a\";\nconsole.log(a() + b());\n",
    );
    dir.write(
        "b.en",
        "import { c } from \"./c\";\n\npublic function b(): i64 {\n  return c();\n}\n",
    );
    dir.write("a.en", "public function a(): i64 {\n  return 1;\n}\n");
    dir.write("c.en", "public function c(): i64 {\n  return 2;\n}\n");
    let mut session = Session::new();
    let checked = check(
        &mut session,
        dir.path(),
        Path::new("main.en"),
        target("x86_64-linux"),
    )
    .unwrap_or_else(|_| panic!("{}", session.render(&plain())));
    let order: Vec<&str> = checked
        .program
        .modules
        .iter()
        .map(|&m| checked.tcx.module(m))
        .filter(|module| !module.library)
        .map(|module| module.path.as_str())
        .collect();
    assert_eq!(order, ["a", "c", "b", "main"]);
    assert_eq!(session.render(&plain()), "");
}

/// The target reaches phase 4: an array of 3,000,000,000 bytes is more than
/// `isize.MAX` on a 32-bit target only (EN0435, SPEC 11).
#[test]
fn the_size_check_is_the_targets() {
    let dir = TempDir::new("sizes");
    dir.write(
        "m.en",
        "private class Big {\n  public a: u8[3000000000] = [0; 3000000000];\n}\n",
    );
    assert_eq!(
        checked_on(dir.path(), "m.en", "x86_64-linux"),
        (Ok(1), String::new())
    );
    let (result, stderr) = checked_on(dir.path(), "m.en", "i386-linux");
    assert_eq!(result, Err("aborted".to_owned()));
    assert!(
        stderr.starts_with("error[EN0435]: `u8[3000000000]` is too large for `i386-linux`\n"),
        "{stderr}"
    );
}

/// The library is the target's: `os` is its layer, so a module only one layer has
/// is found on that target and is EN0305 on another (SPEC 4.12, 8).
#[test]
fn the_library_layer_is_the_targets() {
    let case = spec_case("tour-kernel");
    let dir = TempDir::new("layers");
    for file in &case.files {
        dir.write(&file.name, &file.contents);
    }
    let entry = case.files[0].name.as_str();
    assert_eq!(
        checked_on(dir.path(), entry, "i386-none"),
        (Ok(1), String::new())
    );
    let (result, stderr) = checked_on(dir.path(), entry, "x86_64-linux");
    assert_eq!(result, Err("aborted".to_owned()));
    assert!(stderr.contains("error[EN0305]"), "{stderr}");
}

#[test]
fn invalid_utf8_is_en0001_once_per_place_and_never_en0008() {
    let mut session = Session::new();
    let file = session.add_source(
        PathBuf::from("bad.en"),
        b"const s = 1; \xe2\x82\nconst t = 2; \xc3\n",
    );
    session.parse(file, enrang_syntax::ParseMode::Test);
    let diags = session.dcx.take();
    let codes: Vec<Code> = diags.iter().map(|diag| diag.code).collect();
    assert_eq!(codes, [Code::EN0001, Code::EN0001], "{diags:?}");
    assert!(session.dcx.has_errors());
}

#[test]
fn ids_are_unique_across_the_files_of_a_session() {
    let mut session = Session::new();
    let a = session.add_source(PathBuf::from("a.en"), b"const a = 1;\n");
    let b = session.add_source(PathBuf::from("b.en"), b"const b = 2;\n");
    session.parse(a, enrang_syntax::ParseMode::Test);
    let after_a = session.ids.count();
    session.parse(b, enrang_syntax::ParseMode::Test);
    assert!(after_a > 0);
    assert!(session.ids.count() > after_a);
}

#[test]
fn test_parts_are_named_by_the_module_file() {
    let rows: &[(&str, Option<&str>)] = &[
        ("math.en", Some("math.test.en")),
        ("src/main.en", Some("src/main.test.en")),
        ("./a.b.en", Some("./a.b.test.en")),
        ("math.test.en", None),
        ("math", None),
        ("math.ts", None),
        (".en", None),
        ("", None),
    ];
    for (path, part) in rows {
        assert_eq!(
            test_part_of(Path::new(path)),
            part.map(PathBuf::from),
            "{path}"
        );
    }
}

#[test]
fn format_prints_the_canonical_style() {
    let mut session = Session::new();
    let text = format(&mut session, PathBuf::from("a.en"), b"const   x=1;\n").expect("it parses");
    assert_eq!(text, "const x = 1;\n");
    let again = format(&mut session, PathBuf::from("b.en"), text.as_bytes()).expect("it parses");
    assert_eq!(again, text);
    assert_eq!(session.render(&plain()), "");
}

#[test]
fn format_refuses_a_file_that_does_not_parse_and_the_next_file_starts_clean() {
    let mut session = Session::new();
    assert!(
        format(
            &mut session,
            PathBuf::from("bad.en"),
            b"const x = 1\nf();\n"
        )
        .is_err()
    );
    let text = format(&mut session, PathBuf::from("good.en"), b"f( );\n").expect("it parses");
    assert_eq!(text, "f();\n");
    let stderr = session.render(&plain());
    assert!(stderr.contains(" --> bad.en:1:12\n"), "{stderr}");
    assert!(!stderr.contains("good.en"), "{stderr}");
}

#[test]
fn format_takes_tests_in_a_test_part_only() {
    let mut session = Session::new();
    let source = b"test(\"t\", () => {});\n";
    assert!(format(&mut session, PathBuf::from("m.test.en"), source).is_ok());
    assert!(format(&mut session, PathBuf::from("m.en"), source).is_err());
}

#[test]
fn json_renders_one_object_per_diagnostic_and_notes_with_no_code() {
    let (mut session, start) = with_file("let x;\n");
    session
        .dcx
        .emit(Diagnostic::bare_note(Code::EN0909, "resolves"));
    session.dcx.emit(Diagnostic::new(
        Code::EN0601,
        "used after a move",
        span(start, 4, 5),
        "here",
    ));
    let json = session.render_json();
    let lines: Vec<&str> = json.lines().collect();
    assert_eq!(lines.len(), 2, "{json}");
    assert!(lines[0].contains("\"code\":null"), "{json}");
    assert!(lines[1].contains("\"code\":\"EN0601\""), "{json}");
    assert!(lines[1].contains("\"file\":\"a.en\""), "{json}");
    assert_eq!(session.render_json(), "", "rendering empties the buffer");
}
