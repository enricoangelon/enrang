//! Goldens: a mismatch must really fail, bless must really write and must refuse
//! under CI, and an orphan must really be found.

use std::fs;
use std::sync::Arc;

use enrang_testkit::{
    BlessMode, GoldenFailure, GoldenStore, Harness, Rng, RunOptions, TempDir, golden, line_diff,
    rng_for, scaled, workspace_root,
};

use crate::support::{child, run_harness};

const SUITE: &str = "demo";

/// A store over a fresh directory that already holds these golden files.
fn store_with(mode: BlessMode, goldens: &[(&str, &str)]) -> (TempDir, GoldenStore) {
    let dir = TempDir::new("golden");
    for (name, contents) in goldens {
        dir.write(&format!("{SUITE}/{name}"), contents);
    }
    let store = GoldenStore::new(dir.path(), mode);
    (dir, store)
}

fn on_disk(dir: &TempDir, name: &str) -> Option<String> {
    fs::read_to_string(dir.join(&format!("{SUITE}/{name}"))).ok()
}

/// Applies a diff to `expected`, relying only on the printed format.
fn apply_diff(expected: &str, diff: &str) -> String {
    let old: Vec<&str> = expected.split_inclusive('\n').collect();
    let mut out = String::new();
    let mut at = 0;
    for line in diff.lines() {
        if let Some(header) = line.strip_prefix("@@ expected line ") {
            let start: usize = header.split(',').next().unwrap().parse().unwrap();
            while at + 1 < start {
                out.push_str(old[at]);
                at += 1;
            }
        } else if let Some(text) = line.strip_prefix("  ") {
            assert_eq!(
                old[at].trim_end_matches('\n'),
                text,
                "a context line differs"
            );
            out.push_str(old[at]);
            at += 1;
        } else if let Some(text) = line.strip_prefix("- ") {
            assert_eq!(
                old[at].trim_end_matches('\n'),
                text,
                "a removed line differs"
            );
            at += 1;
        } else if let Some(text) = line.strip_prefix("+ ") {
            out.push_str(text);
            out.push('\n');
        } else {
            panic!("an unexpected diff line: {line:?}");
        }
    }
    for line in &old[at..] {
        out.push_str(line);
    }
    out
}

pub fn register(h: &mut Harness) {
    register_compare(h);
    register_bless(h);
    register_orphans(h);
    register_names(h);
    register_env(h);
    register_default_store(h);
    register_scratch(h);
    register_diff(h);
}

fn register_compare(h: &mut Harness) {
    let matching = [
        "",
        "a",
        "a\n",
        "a\nb\n",
        "  spaced  \n",
        "tab\there\n",
        "α→β\n",
        "\n\n\n",
    ];
    for (index, text) in matching.into_iter().enumerate() {
        h.case(format!("golden::match[{index}]"), move || {
            let (_dir, store) = store_with(BlessMode::Check, &[("g", text)]);
            assert_eq!(store.check(SUITE, "g", text), Ok(()));
        });
    }
    // On disk, actual, and the exact diff.
    let mismatches: &[(&str, &str, &str, &str)] = &[
        (
            "changed_line",
            "a\nb\nc\n",
            "a\nX\nc\n",
            "@@ expected line 1, actual line 1 @@\n  a\n- b\n+ X\n  c\n",
        ),
        (
            "added_line",
            "a\n",
            "a\nb\n",
            "@@ expected line 1, actual line 1 @@\n  a\n+ b\n",
        ),
        (
            "removed_line",
            "a\nb\n",
            "a\n",
            "@@ expected line 1, actual line 1 @@\n  a\n- b\n",
        ),
        (
            "lost_final_newline",
            "a\n",
            "a",
            "@@ expected line 1, actual line 1 @@\n- a\n+ a\n\\ no newline at end of file\n",
        ),
        (
            "gained_final_newline",
            "a",
            "a\n",
            "@@ expected line 1, actual line 1 @@\n- a\n\\ no newline at end of file\n+ a\n",
        ),
        (
            "line_ending",
            "a\n",
            "a\r\n",
            "@@ expected line 1, actual line 1 @@\n- a\n+ a\\r\n",
        ),
        (
            "carriage_return_on_disk",
            "a\r\n",
            "a\n",
            "@@ expected line 1, actual line 1 @@\n- a\\r\n+ a\n",
        ),
        (
            "trailing_space",
            "a\n",
            "a \n",
            "@@ expected line 1, actual line 1 @@\n- a\n+ a\u{b7}\n",
        ),
        (
            "tab_for_space",
            "a b\n",
            "a\tb\n",
            "@@ expected line 1, actual line 1 @@\n- a b\n+ a\\tb\n",
        ),
        (
            "from_empty",
            "",
            "a\n",
            "@@ expected line 1, actual line 1 @@\n+ a\n",
        ),
        (
            "to_empty",
            "a\n",
            "",
            "@@ expected line 1, actual line 1 @@\n- a\n",
        ),
        (
            "blank_line_added",
            "a\nb\n",
            "a\n\nb\n",
            "@@ expected line 1, actual line 1 @@\n  a\n+ \n  b\n",
        ),
    ];
    for &(name, disk, actual, diff) in mismatches {
        h.case(format!("golden::mismatch::{name}"), move || {
            let (dir, store) = store_with(BlessMode::Check, &[("g", disk)]);
            let failure = store.check(SUITE, "g", actual).expect_err("it must fail");
            assert_eq!(failure.failure, GoldenFailure::Mismatch);
            assert_eq!(failure.path, "tests/golden/demo/g");
            assert_eq!(failure.detail, diff);
            assert_eq!(
                on_disk(&dir, "g").as_deref(),
                Some(disk),
                "a check must not write"
            );
        });
    }
    h.case(
        "golden::mismatch::report_is_readable_and_names_the_way_out",
        || {
            let (_dir, store) = store_with(BlessMode::Check, &[("g", "old\n")]);
            let failure = store.check(SUITE, "g", "new\n").unwrap_err();
            assert_eq!(
                failure.to_string(),
                "golden mismatch: tests/golden/demo/g\n\
             @@ expected line 1, actual line 1 @@\n\
             - old\n\
             + new\n\
             rerun with ENRANG_BLESS=1 to accept the new output"
            );
        },
    );
    h.case("golden::mismatch::report_has_no_absolute_path", || {
        let (dir, store) = store_with(BlessMode::Check, &[("g", "old\n")]);
        let text = store.check(SUITE, "g", "new\n").unwrap_err().to_string();
        assert!(!text.contains(dir.path().to_str().unwrap()), "{text}");
    });
    h.case("golden::mismatch::fails_a_harness_case_and_the_run", || {
        let (_dir, store) = store_with(BlessMode::Check, &[("g", "old\n")]);
        let (report, output) = run_harness(
            move |h| h.case("compare", move || store.check(SUITE, "g", "new\n")),
            &RunOptions::default(),
        );
        assert_eq!(report.failed, ["compare"]);
        assert!(!report.success());
        assert!(
            output.contains("golden mismatch: tests/golden/demo/g"),
            "{output}"
        );
        assert!(output.contains("- old\n+ new\n"), "{output}");
    });
    h.case("golden::missing::fails_and_creates_nothing", || {
        let (dir, store) = store_with(BlessMode::Check, &[]);
        let failure = store.check(SUITE, "g", "text\n").unwrap_err();
        assert_eq!(failure.failure, GoldenFailure::Missing);
        assert_eq!(on_disk(&dir, "g"), None);
        let text = failure.to_string();
        assert!(
            text.starts_with("golden missing: tests/golden/demo/g"),
            "{text}"
        );
        assert!(text.contains("+ text"), "{text}");
    });
    h.case("golden::missing::of_empty_output_also_fails", || {
        let (_dir, store) = store_with(BlessMode::Check, &[]);
        let failure = store.check(SUITE, "g", "").unwrap_err();
        assert_eq!(failure.failure, GoldenFailure::Missing);
    });
    h.case("golden::a_directory_in_the_way_is_an_io_failure", || {
        let (dir, store) = store_with(BlessMode::Check, &[("g/inner", "x")]);
        let failure = store.check(SUITE, "g", "x").unwrap_err();
        assert_eq!(failure.failure, GoldenFailure::Io);
        assert!(!failure.to_string().contains(dir.path().to_str().unwrap()));
    });
    h.case("golden::non_utf8_on_disk_is_a_mismatch_not_a_crash", || {
        let (dir, store) = store_with(BlessMode::Check, &[]);
        fs::create_dir_all(dir.join(SUITE)).unwrap();
        fs::write(dir.join("demo/g"), [0xFF, 0xFE, b'\n']).unwrap();
        let failure = store.check(SUITE, "g", "text\n").unwrap_err();
        assert_eq!(failure.failure, GoldenFailure::Mismatch);
    });
}

fn register_bless(h: &mut Harness) {
    let modes: &[(Option<&str>, Option<&str>, BlessMode)] = &[
        (None, None, BlessMode::Check),
        (Some("1"), None, BlessMode::Bless),
        (Some("1"), Some("1"), BlessMode::Refuse),
        (Some("1"), Some("true"), BlessMode::Refuse),
        (Some("1"), Some("TRUE"), BlessMode::Refuse),
        (Some("1"), Some("yes"), BlessMode::Refuse),
        (Some("1"), Some("0"), BlessMode::Bless),
        (Some("1"), Some("false"), BlessMode::Bless),
        (Some("1"), Some("FALSE"), BlessMode::Bless),
        (Some("1"), Some(""), BlessMode::Bless),
        (Some("0"), None, BlessMode::Check),
        (Some("true"), None, BlessMode::Check),
        (Some(""), None, BlessMode::Check),
        (None, Some("1"), BlessMode::Check),
        (Some("0"), Some("1"), BlessMode::Check),
    ];
    for &(bless, ci, expected) in modes {
        h.case(
            format!("golden::mode::bless={bless:?}_ci={ci:?}"),
            move || {
                assert_eq!(BlessMode::from_values(bless, ci), expected);
            },
        );
    }
    h.case("golden::bless::rewrites_a_mismatch", || {
        let (dir, store) = store_with(BlessMode::Bless, &[("g", "old\n")]);
        assert_eq!(store.check(SUITE, "g", "new\n"), Ok(()));
        assert_eq!(on_disk(&dir, "g").as_deref(), Some("new\n"));
    });
    h.case(
        "golden::bless::creates_a_missing_golden_and_its_directories",
        || {
            let (dir, store) = store_with(BlessMode::Bless, &[]);
            assert_eq!(store.check(SUITE, "deep/er/g", "new\n"), Ok(()));
            assert_eq!(on_disk(&dir, "deep/er/g").as_deref(), Some("new\n"));
        },
    );
    h.case("golden::bless::leaves_a_matching_golden_untouched", || {
        let (dir, store) = store_with(BlessMode::Bless, &[("g", "same\n")]);
        let file = dir.join("demo/g");
        let before = fs::metadata(&file).unwrap().modified().unwrap();
        assert_eq!(store.check(SUITE, "g", "same\n"), Ok(()));
        assert_eq!(fs::metadata(&file).unwrap().modified().unwrap(), before);
    });
    h.case("golden::bless::then_a_check_passes", || {
        let (dir, blessing) = store_with(BlessMode::Bless, &[("g", "old\n")]);
        blessing.check(SUITE, "g", "new\n").unwrap();
        let checking = GoldenStore::new(dir.path(), BlessMode::Check);
        assert_eq!(checking.check(SUITE, "g", "new\n"), Ok(()));
        assert!(checking.check(SUITE, "g", "old\n").is_err());
    });
    h.case(
        "golden::bless::a_directory_in_the_way_is_an_io_failure",
        || {
            let (_dir, store) = store_with(BlessMode::Bless, &[("g/inner", "x")]);
            let failure = store.check(SUITE, "g", "x").unwrap_err();
            assert_eq!(failure.failure, GoldenFailure::Io);
        },
    );
    h.case("golden::bless::a_rewrite_is_reported_with_its_diff", || {
        let (_dir, store) = store_with(BlessMode::Bless, &[("g", "old\n")]);
        store.check(SUITE, "g", "new\n").unwrap();
        assert_eq!(
            store.take_blessed(),
            ["blessed tests/golden/demo/g\n@@ expected line 1, actual line 1 @@\n- old\n+ new\n"]
        );
        assert_eq!(
            store.take_blessed(),
            Vec::<String>::new(),
            "a report is taken once"
        );
    });
    h.case("golden::bless::reports_are_sorted_by_path", || {
        let (_dir, store) = store_with(BlessMode::Bless, &[]);
        for name in ["z", "a", "m"] {
            store.check(SUITE, name, "x\n").unwrap();
        }
        let reports = store.take_blessed();
        let firsts: Vec<&str> = reports.iter().map(|r| r.lines().next().unwrap()).collect();
        assert_eq!(
            firsts,
            [
                "blessed tests/golden/demo/a",
                "blessed tests/golden/demo/m",
                "blessed tests/golden/demo/z"
            ]
        );
    });
    h.case("golden::bless::a_matching_golden_reports_nothing", || {
        let (_dir, store) = store_with(BlessMode::Bless, &[("g", "same\n")]);
        store.check(SUITE, "g", "same\n").unwrap();
        assert_eq!(store.take_blessed(), Vec::<String>::new());
    });
    h.case("golden::check_mode_reports_no_blessing", || {
        let (_dir, store) = store_with(BlessMode::Check, &[("g", "old\n")]);
        store.check(SUITE, "g", "new\n").unwrap_err();
        assert_eq!(store.take_blessed(), Vec::<String>::new());
    });
    h.case("golden::bless::a_harness_prints_the_report", || {
        let (_dir, store) = store_with(BlessMode::Bless, &[("g", "old\n")]);
        let store = Arc::new(store);
        let in_case = Arc::clone(&store);
        let (report, output) = run_harness(
            move |h| {
                h.goldens_in(store, SUITE);
                h.case("compare", move || in_case.check(SUITE, "g", "new\n"));
            },
            &RunOptions::default(),
        );
        assert!(report.success(), "{output}");
        assert!(output.contains("blessed tests/golden/demo/g\n"), "{output}");
        assert!(output.contains("- old\n+ new\n"), "{output}");
    });
    let refused: &[(&str, &[(&str, &str)], &str, Option<&str>)] = &[
        ("mismatch", &[("g", "old\n")], "new\n", Some("old\n")),
        ("missing", &[], "new\n", None),
        ("matching", &[("g", "same\n")], "same\n", Some("same\n")),
    ];
    for &(name, goldens, actual, afterwards) in refused {
        h.case(format!("golden::refuse::{name}"), move || {
            let (dir, store) = store_with(BlessMode::Refuse, goldens);
            let failure = store.check(SUITE, "g", actual).unwrap_err();
            assert_eq!(failure.failure, GoldenFailure::BlessRefused);
            assert_eq!(on_disk(&dir, "g").as_deref(), afterwards);
            let text = failure.to_string();
            assert!(
                text.starts_with("bless refused under CI: tests/golden/demo/g"),
                "{text}"
            );
        });
    }
}

fn register_orphans(h: &mut Harness) {
    h.case("golden::orphan::an_unused_file_is_one", || {
        let (_dir, store) = store_with(BlessMode::Check, &[("used", "x"), ("forgotten", "y")]);
        store.check(SUITE, "used", "x").unwrap();
        assert_eq!(store.orphans(SUITE), ["tests/golden/demo/forgotten"]);
    });
    h.case("golden::orphan::all_used_means_none", || {
        let (_dir, store) = store_with(BlessMode::Check, &[("a", "x"), ("b", "y")]);
        store.check(SUITE, "a", "x").unwrap();
        store.check(SUITE, "b", "y").unwrap();
        assert_eq!(store.orphans(SUITE), Vec::<String>::new());
    });
    h.case("golden::orphan::a_mismatch_is_still_a_use", || {
        let (_dir, store) = store_with(BlessMode::Check, &[("a", "x")]);
        store.check(SUITE, "a", "other").unwrap_err();
        assert_eq!(store.orphans(SUITE), Vec::<String>::new());
    });
    h.case(
        "golden::orphan::found_in_nested_directories_and_sorted",
        || {
            let goldens = [
                ("z/deep/two", "x"),
                ("a/one", "x"),
                ("m", "x"),
                ("a/used", "x"),
            ];
            let (_dir, store) = store_with(BlessMode::Check, &goldens);
            store.check(SUITE, "a/used", "x").unwrap();
            assert_eq!(
                store.orphans(SUITE),
                [
                    "tests/golden/demo/a/one",
                    "tests/golden/demo/m",
                    "tests/golden/demo/z/deep/two"
                ]
            );
        },
    );
    h.case("golden::orphan::hidden_files_are_not_goldens", || {
        let (_dir, store) = store_with(BlessMode::Check, &[(".gitkeep", ""), ("a/.swp", "x")]);
        assert_eq!(store.orphans(SUITE), Vec::<String>::new());
    });
    h.case("golden::orphan::only_within_the_suite", || {
        let dir = TempDir::new("golden");
        dir.write("first/g", "x");
        dir.write("second/g", "x");
        let store = GoldenStore::new(dir.path(), BlessMode::Check);
        store.check("first", "g", "x").unwrap();
        assert_eq!(store.orphans("first"), Vec::<String>::new());
        assert_eq!(store.orphans("second"), ["tests/golden/second/g"]);
    });
    h.case("golden::orphan::a_suite_with_no_directory_has_none", || {
        let (_dir, store) = store_with(BlessMode::Check, &[]);
        assert_eq!(store.orphans("never_created"), Vec::<String>::new());
    });
    h.case("golden::orphan::survives_a_bless_run", || {
        let (dir, store) = store_with(BlessMode::Bless, &[("forgotten", "y")]);
        store.check(SUITE, "new", "x").unwrap();
        assert_eq!(store.orphans(SUITE), ["tests/golden/demo/forgotten"]);
        assert_eq!(
            on_disk(&dir, "forgotten").as_deref(),
            Some("y"),
            "bless deletes nothing"
        );
    });
    h.case("golden::orphan::a_refused_use_still_counts", || {
        let (_dir, store) = store_with(BlessMode::Refuse, &[("a", "x")]);
        store.check(SUITE, "a", "x").unwrap_err();
        assert_eq!(store.orphans(SUITE), Vec::<String>::new());
    });
    h.case("golden::orphan::fails_a_run_whose_cases_all_passed", || {
        let (_dir, store) = store_with(BlessMode::Check, &[("used", "x"), ("forgotten", "y")]);
        let store = Arc::new(store);
        let in_case = Arc::clone(&store);
        let (report, output) = run_harness(
            move |h| {
                h.goldens_in(store, SUITE);
                h.case("compare", move || in_case.check(SUITE, "used", "x"));
            },
            &RunOptions::default(),
        );
        assert_eq!(report.passed, 1);
        assert!(report.failed.is_empty());
        assert!(!report.success());
        assert_eq!(report.orphans, ["tests/golden/demo/forgotten"]);
        assert!(
            output
                .contains("FAILED orphaned golden: tests/golden/demo/forgotten is used by no case"),
            "{output}"
        );
        assert!(
            output
                .lines()
                .last()
                .unwrap()
                .starts_with("test result: FAILED."),
            "{output}"
        );
    });
    h.case("golden::orphan::a_clean_run_passes", || {
        let (_dir, store) = store_with(BlessMode::Check, &[("used", "x")]);
        let store = Arc::new(store);
        let in_case = Arc::clone(&store);
        let (report, _) = run_harness(
            move |h| {
                h.goldens_in(store, SUITE);
                h.case("compare", move || in_case.check(SUITE, "used", "x"));
            },
            &RunOptions::default(),
        );
        assert!(report.success());
        assert!(report.orphans.is_empty());
    });
    h.case("golden::orphan::a_filtered_run_cannot_judge", || {
        let (_dir, store) = store_with(BlessMode::Check, &[("used", "x")]);
        let store = Arc::new(store);
        let in_case = Arc::clone(&store);
        let (report, _) = run_harness(
            move |h| {
                h.goldens_in(store, SUITE);
                h.case("compare", move || in_case.check(SUITE, "used", "x"));
                h.case("other", || ());
            },
            &RunOptions {
                filters: vec!["other".to_owned()],
                ..RunOptions::default()
            },
        );
        assert!(report.success(), "{report:?}");
        assert!(report.orphans.is_empty());
    });
    h.case("golden::orphan::a_failing_run_cannot_judge", || {
        let (_dir, store) = store_with(BlessMode::Check, &[("never_reached", "x")]);
        let store = Arc::new(store);
        let (report, _) = run_harness(
            move |h| {
                h.goldens_in(store, SUITE);
                h.case("fails_before_its_golden", || -> () { panic!("early") });
            },
            &RunOptions::default(),
        );
        assert_eq!(report.failed, ["fails_before_its_golden"]);
        assert!(report.orphans.is_empty());
    });
}

fn register_names(h: &mut Harness) {
    let invalid: &[(&str, &str)] = &[
        ("", "g"),
        ("s", ""),
        ("..", "g"),
        ("s", ".."),
        ("s", "../g"),
        ("s", "a/../b"),
        ("s", ".hidden"),
        ("s", "a/.hidden"),
        (".s", "g"),
        ("s", "a//b"),
        ("s", "/abs"),
        ("s", "a/"),
        ("a/b", "g"),
        ("/abs", "g"),
        ("s", "a\\b"),
        ("s\\t", "g"),
    ];
    for &(suite, name) in invalid {
        h.case(
            format!("golden::invalid_name::{suite:?}/{name:?}"),
            move || {
                let dir = TempDir::new("golden");
                let store = GoldenStore::new(dir.join("root"), BlessMode::Bless);
                let failure = store.check(suite, name, "x").unwrap_err();
                assert_eq!(failure.failure, GoldenFailure::InvalidName);
                assert!(!dir.join("root").exists(), "nothing may be written");
                assert!(!dir.join("g").exists(), "nothing may escape the root");
            },
        );
    }
    let messages: &[(&str, &str, &str)] = &[
        ("s", "", "the name is empty"),
        ("s", "a//b", "the name has an empty path component"),
        ("", "g", "the suite has an empty path component"),
        ("s", ".hidden", "the name has a component starting with `.`"),
        ("a\\b", "g", "the suite has a path separator in a component"),
    ];
    for &(suite, name, message) in messages {
        h.case(
            format!("golden::invalid_name::says::{suite:?}/{name:?}"),
            move || {
                let dir = TempDir::new("golden");
                let store = GoldenStore::new(dir.path(), BlessMode::Check);
                let failure = store.check(suite, name, "x").unwrap_err();
                assert_eq!(failure.detail, message);
            },
        );
    }
    h.case("golden::a_name_may_hold_subdirectories", || {
        let (_dir, store) = store_with(BlessMode::Check, &[("a/b/c.txt", "x")]);
        assert_eq!(store.check(SUITE, "a/b/c.txt", "x"), Ok(()));
    });
}

fn register_env(h: &mut Harness) {
    let write_root = |contents: &str| {
        let dir = TempDir::new("golden-env");
        dir.write("s/out.txt", contents);
        dir
    };
    h.case(
        "golden::env::a_mismatch_exits_one_and_writes_nothing",
        move || {
            let dir = write_root("old\n");
            let root = dir.path().to_str().unwrap();
            let output = child("golden_env", &[], &[("ENRANG_TESTKIT_ROOT", root)]);
            assert_eq!(output.code, Some(1), "{}", output.stdout);
            assert!(
                output.stdout.contains("- old\n+ new\n"),
                "{}",
                output.stdout
            );
            assert_eq!(fs::read_to_string(dir.join("s/out.txt")).unwrap(), "old\n");
        },
    );
    h.case(
        "golden::env::bless_rewrites_and_prints_the_diff",
        move || {
            let dir = write_root("old\n");
            let root = dir.path().to_str().unwrap();
            let vars = [("ENRANG_TESTKIT_ROOT", root), ("ENRANG_BLESS", "1")];
            let output = child("golden_env", &[], &vars);
            assert_eq!(output.code, Some(0), "{}", output.stdout);
            assert!(
                output.stdout.contains("blessed tests/golden/s/out.txt"),
                "{}",
                output.stdout
            );
            assert!(
                output.stdout.contains("- old\n+ new\n"),
                "{}",
                output.stdout
            );
            assert_eq!(fs::read_to_string(dir.join("s/out.txt")).unwrap(), "new\n");
        },
    );
    let refusals = ["1", "true"];
    for ci in refusals {
        h.case(
            format!("golden::env::bless_under_ci_{ci}_is_refused"),
            move || {
                let dir = write_root("old\n");
                let root = dir.path().to_str().unwrap();
                let vars = [
                    ("ENRANG_TESTKIT_ROOT", root),
                    ("ENRANG_BLESS", "1"),
                    ("CI", ci),
                ];
                let output = child("golden_env", &[], &vars);
                assert_eq!(output.code, Some(1), "{}", output.stdout);
                assert!(
                    output.stdout.contains("bless refused under CI"),
                    "{}",
                    output.stdout
                );
                assert_eq!(fs::read_to_string(dir.join("s/out.txt")).unwrap(), "old\n");
            },
        );
    }
    h.case("golden::env::ci_alone_changes_nothing", move || {
        let dir = write_root("new\n");
        let root = dir.path().to_str().unwrap();
        let vars = [("ENRANG_TESTKIT_ROOT", root), ("CI", "1")];
        let output = child("golden_env", &[], &vars);
        assert_eq!(output.code, Some(0), "{}", output.stdout);
    });
    h.case("golden::env::an_orphan_exits_one", move || {
        let dir = write_root("new\n");
        dir.write("s/forgotten.txt", "x");
        let root = dir.path().to_str().unwrap();
        let output = child("golden_env", &[], &[("ENRANG_TESTKIT_ROOT", root)]);
        assert_eq!(output.code, Some(1), "{}", output.stdout);
        assert!(
            output
                .stdout
                .contains("orphaned golden: tests/golden/s/forgotten.txt"),
            "{}",
            output.stdout
        );
    });
    h.case("golden::env::golden_in_prints_what_it_blessed", move || {
        let dir = write_root("old\n");
        let root = dir.path().to_str().unwrap();
        let vars = [("ENRANG_TESTKIT_ROOT", root), ("ENRANG_BLESS", "1")];
        let output = child("golden_in_env", &[], &vars);
        assert_eq!(output.stdout, "true\n");
        assert!(
            output
                .stderr
                .starts_with("blessed tests/golden/s/out.txt\n"),
            "{}",
            output.stderr
        );
        assert!(
            output.stderr.contains("- old\n+ new\n"),
            "{}",
            output.stderr
        );
        assert_eq!(fs::read_to_string(dir.join("s/out.txt")).unwrap(), "new\n");
    });
    h.case(
        "golden::env::golden_in_is_silent_when_nothing_changed",
        move || {
            let dir = write_root("new\n");
            let root = dir.path().to_str().unwrap();
            let vars = [("ENRANG_TESTKIT_ROOT", root), ("ENRANG_BLESS", "1")];
            let output = child("golden_in_env", &[], &vars);
            assert_eq!(output.stdout, "true\n");
            assert_eq!(output.stderr, "");
        },
    );
    h.case(
        "golden::env::a_bless_run_does_not_excuse_an_orphan",
        move || {
            let dir = write_root("old\n");
            dir.write("s/forgotten.txt", "x");
            let root = dir.path().to_str().unwrap();
            let vars = [("ENRANG_TESTKIT_ROOT", root), ("ENRANG_BLESS", "1")];
            let output = child("golden_env", &[], &vars);
            assert_eq!(output.code, Some(1), "{}", output.stdout);
            assert_eq!(
                fs::read_to_string(dir.join("s/forgotten.txt")).unwrap(),
                "x"
            );
        },
    );
}

fn register_default_store(h: &mut Harness) {
    let real_golden = || workspace_root().join("tests/golden/testkit/skip_summary.txt");
    h.case("golden::default::lives_at_the_workspace_root", move || {
        assert!(workspace_root().join("docs/SPEC.md").is_file());
        assert!(real_golden().is_file());
    });
    h.case("golden::default::a_mismatch_fails_the_run", move || {
        let before = fs::read(real_golden()).unwrap();
        let output = child("default_store_mismatch", &[], &[]);
        assert_eq!(output.code, Some(1), "{}", output.stdout);
        assert!(
            output
                .stdout
                .contains("golden mismatch: tests/golden/testkit/skip_summary.txt"),
            "{}",
            output.stdout
        );
        assert_eq!(fs::read(real_golden()).unwrap(), before);
    });
    h.case("golden::default::bless_under_ci_is_refused", move || {
        let before = fs::read(real_golden()).unwrap();
        let vars = [("ENRANG_BLESS", "1"), ("CI", "1")];
        let output = child("default_store_mismatch", &[], &vars);
        assert_eq!(output.code, Some(1), "{}", output.stdout);
        assert!(
            output.stdout.contains("bless refused under CI"),
            "{}",
            output.stdout
        );
        assert_eq!(fs::read(real_golden()).unwrap(), before);
    });
    h.case("golden::default::every_unused_golden_is_an_orphan", || {
        let output = child("default_store_orphans", &[], &[]);
        assert_eq!(output.code, Some(1), "{}", output.stdout);
        for name in ["gate_report", "harness_output", "line_diff", "skip_summary"] {
            let line = format!("FAILED orphaned golden: tests/golden/testkit/{name}.txt");
            assert!(output.stdout.contains(&line), "{}", output.stdout);
        }
    });
}

fn register_scratch(h: &mut Harness) {
    h.case("temp::makes_an_empty_directory", || {
        let dir = TempDir::new("scratch");
        assert!(dir.path().is_dir());
        assert_eq!(fs::read_dir(dir.path()).unwrap().count(), 0);
    });
    h.case("temp::two_are_distinct", || {
        let (one, other) = (TempDir::new("scratch"), TempDir::new("scratch"));
        assert_ne!(one.path(), other.path());
    });
    h.case("temp::write_creates_parents_and_returns_the_path", || {
        let dir = TempDir::new("scratch");
        let file = dir.write("a/b/c.txt", "text");
        assert_eq!(file, dir.join("a/b/c.txt"));
        assert_eq!(fs::read_to_string(file).unwrap(), "text");
    });
    h.case(
        "temp::lives_under_the_temporary_directory_it_is_told",
        || {
            let under = TempDir::new("scratch");
            let tmpdir = under.path().to_str().unwrap();
            let output = child("temp_dir", &[], &[("TMPDIR", tmpdir)]);
            assert_eq!(output.code, Some(0), "{}", output.stderr);
            let printed = output.stdout.trim_end();
            assert!(
                printed.starts_with(&format!("{tmpdir}/enrang-testkit-probe-")),
                "{printed}"
            );
        },
    );
    h.case("temp::dropping_removes_everything", || {
        let dir = TempDir::new("scratch");
        let root = dir.path().to_path_buf();
        dir.write("a/b/c.txt", "text");
        drop(dir);
        assert!(!root.exists());
    });
}

fn register_diff(h: &mut Harness) {
    h.case("diff::equal_texts_have_no_diff", || {
        for text in ["", "a", "a\n", "a\nb\n", "\n"] {
            assert_eq!(line_diff(text, text), "");
        }
    });
    let numbered =
        |lines: std::ops::Range<u32>| -> String { lines.map(|n| format!("{n}\n")).collect() };
    // Replaces whole lines, where `str::replace` would also change `15` for `5`.
    let edit = |text: &str, edits: &[(&str, &str)]| -> String {
        text.lines()
            .map(|line| {
                let found = edits.iter().find(|(from, _)| *from == line);
                let replacement = found.map_or(line, |(_, to)| to);
                if replacement.is_empty() {
                    String::new()
                } else {
                    format!("{replacement}\n")
                }
            })
            .collect()
    };
    h.case("diff::context_is_three_lines", move || {
        let old = numbered(1..11);
        let new = edit(&old, &[("5", "five")]);
        assert_eq!(
            line_diff(&old, &new),
            "@@ expected line 2, actual line 2 @@\n  2\n  3\n  4\n- 5\n+ five\n  6\n  7\n  8\n"
        );
    });
    h.case(
        "diff::far_changes_make_two_hunks_with_true_line_numbers",
        move || {
            let old = numbered(1..31);
            let new = edit(&old, &[("5", "five"), ("25", "extra\n25")]);
            assert_eq!(
                line_diff(&old, &new),
                "@@ expected line 2, actual line 2 @@\n  2\n  3\n  4\n- 5\n+ five\n  6\n  7\n  8\n\
             @@ expected line 22, actual line 22 @@\n  22\n  23\n  24\n+ extra\n  25\n  26\n  27\n"
            );
        },
    );
    h.case("diff::near_changes_share_a_hunk", move || {
        let old = numbered(1..16);
        let new = edit(&old, &[("5", "five"), ("9", "nine")]);
        let diff = line_diff(&old, &new);
        assert_eq!(diff.matches("@@ expected").count(), 1, "{diff}");
    });
    // Between two changes, the unchanged lines and the hunks they leave. Six is what
    // both contexts show, so that the hunks would touch, and they merge.
    for (between, hunks) in [(5, 1), (6, 1), (7, 2), (8, 2)] {
        h.case(
            format!("diff::{between}_unchanged_lines_make_{hunks}_hunks"),
            move || {
                let middle: String = (0..between).map(|n| format!("{n}\n")).collect();
                let old = format!("a\n{middle}b\n");
                let new = format!("A\n{middle}B\n");
                let diff = line_diff(&old, &new);
                assert_eq!(diff.matches("@@ expected").count(), hunks, "{diff}");
            },
        );
    }
    h.case(
        "diff::lines_separated_by_more_than_both_contexts_split",
        move || {
            let old = numbered(1..21);
            let new = edit(&old, &[("5", "five"), ("13", "thirteen")]);
            let diff = line_diff(&old, &new);
            assert_eq!(diff.matches("@@ expected").count(), 2, "{diff}");
        },
    );
    h.case("diff::removal_comes_before_addition", || {
        assert_eq!(
            line_diff("a\n", "b\n"),
            "@@ expected line 1, actual line 1 @@\n- a\n+ b\n"
        );
    });
    h.case("diff::a_moved_line_shows_as_little_as_possible", || {
        assert_eq!(
            line_diff("a\nb\nc\nd\n", "b\nc\nd\na\n"),
            "@@ expected line 1, actual line 1 @@\n- a\n  b\n  c\n  d\n+ a\n"
        );
    });
    h.case("diff::start_of_file_insertion", move || {
        let old = numbered(1..10);
        let new = format!("zero\n{old}");
        assert_eq!(
            line_diff(&old, &new),
            "@@ expected line 1, actual line 1 @@\n+ zero\n  1\n  2\n  3\n"
        );
    });
    h.case("diff::end_of_file_removal", move || {
        let old = numbered(1..10);
        let new = numbered(1..9);
        assert_eq!(
            line_diff(&old, &new),
            "@@ expected line 6, actual line 6 @@\n  6\n  7\n  8\n- 9\n"
        );
    });
    let invisible: &[(&str, &str, &str)] = &[
        ("cr", "a\r\n", "- a\\r"),
        ("tab", "\ta\n", "- \\ta"),
        ("bell", "a\u{7}\n", "- a\\x07"),
        ("escape", "\u{1b}[0m\n", "- \\x1b[0m"),
        ("trailing_spaces", "a  \n", "- a\u{b7}\u{b7}"),
        ("only_spaces", "   \n", "- \u{b7}\u{b7}\u{b7}"),
        ("inner_spaces_stay", "a  b\n", "- a  b"),
        ("unicode_stays", "α → β\n", "- α → β"),
    ];
    for &(name, line, shown) in invisible {
        h.case(format!("diff::spells_out::{name}"), move || {
            let diff = line_diff(line, "");
            assert!(diff.contains(&format!("{shown}\n")), "{diff:?}");
        });
    }
    h.case("diff::large_inputs_fall_back_to_a_replacement", || {
        let old: String = (0..3000).map(|n| format!("old {n}\n")).collect();
        let new: String = (0..3000).map(|n| format!("new {n}\n")).collect();
        let diff = line_diff(&old, &new);
        assert_eq!(
            diff.lines().filter(|line| line.starts_with("- ")).count(),
            3000
        );
        assert_eq!(
            diff.lines().filter(|line| line.starts_with("+ ")).count(),
            3000
        );
    });
    h.case("diff::large_inputs_with_a_small_change_stay_small", || {
        let old: String = (0..20_000).map(|n| format!("line {n}\n")).collect();
        let new = old.replace("line 10000\n", "changed\n");
        let diff = line_diff(&old, &new);
        assert_eq!(diff.lines().count(), 9, "{diff}");
        assert!(
            diff.starts_with("@@ expected line 9998, actual line 9998 @@\n"),
            "{diff}"
        );
    });
    h.case(
        "diff::generated_texts_reconstruct_through_their_diff",
        || {
            let mut rng = rng_for("diff-reconstruct");
            for _ in 0..scaled(400) {
                let text = |rng: &mut enrang_testkit::Xoshiro256| -> String {
                    (0..rng.below(30))
                        .map(|_| format!("{}\n", rng.below(6)))
                        .collect()
                };
                let old = text(&mut rng);
                let new = text(&mut rng);
                let diff = line_diff(&old, &new);
                assert_eq!(diff.is_empty(), old == new, "{old:?} {new:?}");
                assert_eq!(apply_diff(&old, &diff), new, "{old:?} {new:?}\n{diff}");
            }
        },
    );
    h.case("diff::real_golden::sample", move || {
        let old = numbered(1..31);
        let new = edit(&old, &[("4", "four"), ("15", ""), ("25", "24.5\n25")]);
        golden("testkit", "line_diff.txt", &line_diff(&old, &new))
    });
}
