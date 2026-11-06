//! Tool lookup, skip accounting, and `ENRANG_REQUIRE` (TESTING 20).

use std::ffi::OsStr;
use std::ffi::OsString;
use std::path::Path;

use enrang_testkit::{
    Harness, RunOptions, SkipLedger, TempDir, catch_panic, find_tool, golden, parse_require,
    require_matches, skip, tool,
};

use crate::support::{child, child_in, child_without, read_doc, run_harness};

/// The notice of section 20, exactly as the document prints it.
fn document_notices() -> Vec<String> {
    let doc = read_doc("TESTING.md");
    let section = doc
        .split("## 20. Skip notices")
        .nth(1)
        .expect("TESTING has section 20");
    let block = section
        .split("```text\n")
        .nth(1)
        .expect("section 20 has a block");
    let block = block.split("```").next().expect("the block closes");
    block.lines().map(str::to_owned).collect()
}

/// The three notes behind the document's lines.
fn document_ledger() -> SkipLedger {
    let ledger = SkipLedger::new();
    ledger.record("qemu-system-i386", 212, "not found");
    ledger.record("OVMF", 40, "not found");
    ledger.record_oracle("as", 2400, "not found");
    ledger
}

#[cfg(unix)]
fn make_executable(path: &Path) {
    use std::fs;
    use std::os::unix::fs::PermissionsExt;
    fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
}

#[cfg(not(unix))]
fn make_executable(_: &Path) {}

fn path_list(dirs: &[&Path]) -> OsString {
    std::env::join_paths(dirs).unwrap()
}

pub fn register(h: &mut Harness) {
    register_format(h);
    register_require(h);
    register_lookup(h);
    register_children(h);
}

fn register_format(h: &mut Harness) {
    h.case("skip::format::each_line_of_the_document", || {
        let mut produced = document_ledger().lines();
        let mut documented = document_notices();
        assert_eq!(documented.len(), 3, "{documented:?}");
        produced.sort();
        documented.sort();
        assert_eq!(produced, documented);
    });
    // Tool, tests, reason, oracle, and the exact line.
    let lines: &[(&str, usize, &str, bool, &str)] = &[
        (
            "qemu-system-i386",
            212,
            "not found",
            false,
            "SKIP qemu-system-i386 not found: 212 tests not run",
        ),
        (
            "OVMF",
            40,
            "not found",
            false,
            "SKIP OVMF not found: 40 tests not run",
        ),
        (
            "as",
            2400,
            "not found",
            true,
            "SKIP as not found: 2400 oracle tests not run",
        ),
        (
            "/mnt/c",
            7,
            "absent",
            false,
            "SKIP /mnt/c absent: 7 tests not run",
        ),
        (
            "objdump",
            1,
            "not found",
            true,
            "SKIP objdump not found: 1 oracle test not run",
        ),
        (
            "cc",
            1,
            "not found",
            false,
            "SKIP cc not found: 1 test not run",
        ),
        (
            "ld",
            2,
            "not found",
            true,
            "SKIP ld not found: 2 oracle tests not run",
        ),
        (
            "gcc",
            0,
            "not found",
            false,
            "SKIP gcc not found: 0 tests not run",
        ),
    ];
    for &(name, tests, reason, oracle, line) in lines {
        h.case(format!("skip::format::{name}"), move || {
            let ledger = SkipLedger::new();
            if oracle {
                ledger.record_oracle(name, tests, reason);
            } else {
                ledger.record(name, tests, reason);
            }
            assert_eq!(ledger.lines(), [line]);
            assert_eq!(ledger.total_tests(), tests);
        });
    }
    h.case("skip::ledger::starts_empty", || {
        let ledger = SkipLedger::new();
        assert_eq!(ledger.lines(), Vec::<String>::new());
        assert_eq!(ledger.total_tests(), 0);
    });
    h.case("skip::ledger::sums_one_tool_and_reason", || {
        let ledger = SkipLedger::new();
        ledger.record("as", 100, "not found");
        ledger.record("as", 23, "not found");
        assert_eq!(ledger.lines(), ["SKIP as not found: 123 tests not run"]);
        assert_eq!(ledger.total_tests(), 123);
    });
    h.case("skip::ledger::keeps_reasons_apart", || {
        let ledger = SkipLedger::new();
        ledger.record("as", 1, "not found");
        ledger.record("as", 2, "too old");
        assert_eq!(
            ledger.lines(),
            [
                "SKIP as not found: 1 test not run",
                "SKIP as too old: 2 tests not run"
            ]
        );
        assert_eq!(ledger.total_tests(), 3);
    });
    h.case("skip::ledger::keeps_oracle_tests_apart", || {
        let ledger = SkipLedger::new();
        ledger.record("as", 1, "not found");
        ledger.record_oracle("as", 2, "not found");
        assert_eq!(
            ledger.lines(),
            [
                "SKIP as not found: 1 test not run",
                "SKIP as not found: 2 oracle tests not run"
            ]
        );
    });
    h.case(
        "skip::ledger::order_does_not_depend_on_recording_order",
        || {
            let (one, other) = (SkipLedger::new(), SkipLedger::new());
            for name in ["qemu", "as", "OVMF", "gcc"] {
                one.record(name, 1, "not found");
            }
            for name in ["gcc", "OVMF", "as", "qemu"] {
                other.record(name, 1, "not found");
            }
            assert_eq!(one.lines(), other.lines());
        },
    );
    let refused: &[(&str, &str, &str)] = &[("no_tool", "", "not found"), ("no_reason", "as", "")];
    for &(name, tool_name, reason) in refused {
        h.case(format!("skip::ledger::refuses::{name}"), move || {
            let ledger = SkipLedger::new();
            assert!(catch_panic(|| ledger.record(tool_name, 1, reason)).is_some());
        });
    }
    h.case("skip::real_golden::summary", || {
        golden(
            "testkit",
            "skip_summary.txt",
            &(document_ledger().lines().join("\n") + "\n"),
        )
    });
}

fn register_require(h: &mut Harness) {
    let parsed: &[(Option<&str>, &[&str])] = &[
        (None, &[]),
        (Some(""), &[]),
        (Some(","), &[]),
        (Some("as"), &["as"]),
        (Some("qemu,as"), &["qemu", "as"]),
        (Some(" qemu , as "), &["qemu", "as"]),
        (Some("qemu,,as,"), &["qemu", "as"]),
    ];
    for &(value, names) in parsed {
        h.case(format!("skip::require::parse::{value:?}"), move || {
            assert_eq!(parse_require(value), names);
        });
    }
    let matching: &[(&str, &str, bool)] = &[
        ("as", "as", true),
        ("qemu", "qemu-system-i386", true),
        ("qemu", "qemu-system-x86_64", true),
        ("qemu-system-i386", "qemu-system-i386", true),
        ("OVMF", "OVMF", true),
        ("ovmf", "OVMF", true),
        ("QEMU", "qemu-system-i386", true),
        ("as", "asm", false),
        ("as", "gas", false),
        ("qemu", "qemu2", false),
        ("qemu-system-i386", "qemu", false),
        ("qemu-system", "qemu-system-i386", true),
        ("gcc", "as", false),
        ("", "as", false),
        ("speed", "speedy", false),
    ];
    for &(required, name, expected) in matching {
        h.case(
            format!("skip::require::matches::{required:?}_{name:?}"),
            move || {
                assert_eq!(require_matches(required, name), expected);
            },
        );
    }
    // Names of `ENRANG_REQUIRE`, and the number of the document's notices they fail.
    let failures: &[(&[&str], usize)] = &[
        (&[], 0),
        (&["gcc"], 0),
        (&["as"], 1),
        (&["qemu"], 1),
        (&["OVMF"], 1),
        (&["qemu", "as"], 2),
        (&["qemu", "as", "ovmf"], 3),
        (&["qemu", "gcc"], 1),
    ];
    for &(names, count) in failures {
        h.case(format!("skip::require::failures::{names:?}"), move || {
            let names: Vec<String> = names.iter().map(|&name| name.to_owned()).collect();
            assert_eq!(document_ledger().required_failures(&names).len(), count);
        });
    }
    h.case("skip::require::a_harness_run_fails_on_a_named_skip", || {
        let (report, output) = run_harness(
            |h| {
                let ledger = std::sync::Arc::new(document_ledger());
                h.ledger(ledger);
                h.case("a", || ());
            },
            &RunOptions {
                require: vec!["qemu".to_owned(), "as".to_owned()],
                ..RunOptions::default()
            },
        );
        assert!(!report.success());
        assert_eq!(report.required_skips.len(), 2);
        assert!(
            output.contains(
                "FAILED required by ENRANG_REQUIRE: SKIP qemu-system-i386 not found: 212 tests not run"
            ),
            "{output}"
        );
        assert!(
            output.contains("FAILED required by ENRANG_REQUIRE: SKIP as not found: 2400 oracle tests not run"),
            "{output}"
        );
    });
    h.case("skip::require::an_unnamed_skip_passes_a_run", || {
        let (report, output) = run_harness(
            |h| {
                let ledger = std::sync::Arc::new(document_ledger());
                h.ledger(ledger);
                h.case("a", || ());
            },
            &RunOptions::default(),
        );
        assert!(report.success(), "{output}");
        assert_eq!(report.tests_skipped, 2652);
        assert_eq!(output.matches("SKIP ").count(), 3, "{output}");
    });
    h.case("skip::require::a_present_tool_passes", || {
        let (report, _) = run_harness(
            |h| h.case("a", || ()),
            &RunOptions {
                require: vec!["as".to_owned()],
                ..RunOptions::default()
            },
        );
        assert!(report.success());
    });
}

fn register_lookup(h: &mut Harness) {
    h.case("tool::finds_a_real_tool_and_it_runs", || {
        let Some(found) = tool("sh") else {
            skip("sh", 1, "not found");
            return;
        };
        let status = found.command().args(["-c", "exit 7"]).status().unwrap();
        assert_eq!(status.code(), Some(7));
        assert!(found.path().ends_with("sh"));
    });
    h.case("tool::an_absent_tool_is_none", || {
        assert_eq!(tool("enrang-no-such-tool-anywhere"), None);
    });
    h.case("tool::find::an_executable_in_the_list", || {
        let dir = TempDir::new("tool");
        let file = dir.write("mytool", "#!/bin/sh\n");
        make_executable(&file);
        let found = find_tool("mytool", dir.path().as_os_str()).expect("it is on the list");
        assert_eq!(found.path(), file);
    });
    #[cfg(unix)]
    h.case("tool::find::a_file_that_cannot_run_does_not_count", || {
        let dir = TempDir::new("tool");
        dir.write("mytool", "text");
        assert_eq!(find_tool("mytool", dir.path().as_os_str()), None);
    });
    h.case("tool::find::a_directory_does_not_count", || {
        let dir = TempDir::new("tool");
        std::fs::create_dir(dir.join("mytool")).unwrap();
        assert_eq!(find_tool("mytool", dir.path().as_os_str()), None);
    });
    h.case("tool::find::the_first_directory_wins", || {
        let (first, second) = (TempDir::new("tool"), TempDir::new("tool"));
        let early = first.write("mytool", "#!/bin/sh\n");
        let late = second.write("mytool", "#!/bin/sh\n");
        make_executable(&early);
        make_executable(&late);
        let list = path_list(&[first.path(), second.path()]);
        assert_eq!(find_tool("mytool", &list).unwrap().path(), early);
    });
    #[cfg(unix)]
    h.case("tool::find::skips_a_non_executable_for_a_later_one", || {
        let (first, second) = (TempDir::new("tool"), TempDir::new("tool"));
        first.write("mytool", "text");
        let late = second.write("mytool", "#!/bin/sh\n");
        make_executable(&late);
        let list = path_list(&[first.path(), second.path()]);
        assert_eq!(find_tool("mytool", &list).unwrap().path(), late);
    });
    h.case("tool::find::an_empty_list_finds_nothing", || {
        assert_eq!(find_tool("sh", OsStr::new("")), None);
    });
    let refused = ["", "bin/sh", "/bin/sh", "./sh", "..\\sh"];
    for name in refused {
        h.case(
            format!("tool::find::only_a_bare_name::{name:?}"),
            move || {
                assert_eq!(find_tool(name, OsStr::new("/bin:/usr/bin")), None);
            },
        );
    }
}

fn register_children(h: &mut Harness) {
    const NOTICES: &str = "SKIP OVMF not found: 40 tests not run\n\
                           SKIP as not found: 2400 oracle tests not run\n\
                           SKIP qemu-system-i386 not found: 212 tests not run\n";
    h.case("skip::child::the_summary_passes_by_default", || {
        let output = child("skip_demo", &[], &[]);
        assert_eq!(output.code, Some(0), "{}", output.stdout);
        assert!(output.stdout.contains(NOTICES), "{}", output.stdout);
        assert!(
            output.stdout.contains("2652 tests skipped"),
            "{}",
            output.stdout
        );
    });
    // `ENRANG_REQUIRE`, status, and how many notices become failures.
    let rows: &[(&str, i32, usize)] = &[
        ("", 0, 0),
        ("gcc", 0, 0),
        ("as", 1, 1),
        ("qemu", 1, 1),
        ("qemu,as", 1, 2),
        ("qemu,as,ovmf", 1, 3),
        ("OVMF", 1, 1),
    ];
    for &(value, code, failures) in rows {
        h.case(format!("skip::child::require_{value:?}"), move || {
            let output = child("skip_demo", &[], &[("ENRANG_REQUIRE", value)]);
            assert_eq!(output.code, Some(code), "{}", output.stdout);
            assert_eq!(
                output
                    .stdout
                    .matches("FAILED required by ENRANG_REQUIRE")
                    .count(),
                failures,
                "{}",
                output.stdout
            );
            assert!(output.stdout.contains(NOTICES), "{}", output.stdout);
        });
    }
    h.case(
        "skip::child::a_filter_that_runs_the_case_still_summarises",
        || {
            let output = child("skip_demo", &["notes"], &[]);
            assert!(output.stdout.contains(NOTICES), "{}", output.stdout);
        },
    );
    h.case("skip::child::a_filtered_out_case_notes_nothing", || {
        let output = child("skip_demo", &["other"], &[("ENRANG_REQUIRE", "as")]);
        assert_eq!(output.code, Some(0), "{}", output.stdout);
        assert!(!output.stdout.contains("SKIP"), "{}", output.stdout);
    });
    h.case("skip::child::the_verdict_line_counts_one_test", || {
        let output = child("one_skip", &[], &[]);
        assert_eq!(output.code, Some(0), "{}", output.stdout);
        assert!(
            output
                .stdout
                .contains("SKIP gcc not found: 1 test not run\n"),
            "{}",
            output.stdout
        );
        assert!(
            output.stdout.ends_with("1 total; 1 test skipped\n"),
            "{}",
            output.stdout
        );
    });
    h.case("tool::child::found_through_the_real_path", || {
        if tool("sh").is_none() {
            skip("sh", 1, "not found");
            return;
        }
        let output = child("tool_probe", &[], &[]);
        assert_eq!(output.stdout, "sh=found\n");
    });
    h.case("tool::child::not_found_on_an_empty_path", || {
        let output = child("tool_probe", &[], &[("PATH", "")]);
        assert_eq!(output.stdout, "sh=absent\n");
    });
    h.case("tool::child::not_found_with_no_path_at_all", || {
        let output = child_without("tool_probe", &["PATH"]);
        assert_eq!(output.stdout, "sh=absent\n");
    });
    // A tool in the working directory, and a `PATH` of empty entries: POSIX would
    // read those as the working directory, and a test must not depend on where it
    // runs. The first row is the control, showing that the file is a usable tool.
    let working_directory: &[(&str, &str, &str)] = &[
        ("control", "<dir>", "sh=found\n"),
        ("empty_path", "", "sh=absent\n"),
        ("one_empty_entry", ":", "sh=absent\n"),
        (
            "empty_entry_first",
            ":/nonexistent-enrang-dir",
            "sh=absent\n",
        ),
        (
            "empty_entry_last",
            "/nonexistent-enrang-dir:",
            "sh=absent\n",
        ),
    ];
    for &(name, path, expected) in working_directory {
        h.case(
            format!("tool::child::the_working_directory::{name}"),
            move || {
                let dir = TempDir::new("tool");
                make_executable(&dir.write("sh", "#!/bin/sh\n"));
                let path = path.replace("<dir>", dir.path().to_str().unwrap());
                let output = child_in(dir.path(), "tool_probe", &[("PATH", &path)]);
                assert_eq!(output.stdout, expected);
            },
        );
    }
}
