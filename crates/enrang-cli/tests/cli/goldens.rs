//! One golden per command, flag and message (TESTING 17 and 18).
//!
//! The table holds, by hand, each case's exit status and the first line it must
//! print. A golden can be blessed and these cannot, so blessing never changes which
//! outcome a command is expected to have.

use enrang_cli::{ALIASES, DEFERRED, LATER};
use enrang_diag::CURRENT_MILESTONE;
use enrang_testkit::{Harness, golden};

use crate::support::{RETIRED, SUITE, enrang, inproc, strings, transcript};

pub struct GoldenCase {
    pub name: String,
    pub args: Vec<String>,
    pub exit: i32,
    /// The first line printed, or empty when nothing is.
    pub head: String,
}

fn case(name: &str, args: &[&str], exit: i32, head: &str) -> GoldenCase {
    GoldenCase {
        name: format!("{name}.txt"),
        args: strings(args),
        exit,
        head: head.to_owned(),
    }
}

fn not_a_command(name: &str) -> String {
    format!("error[EN1302]: `{name}` is not an `enrang` command")
}

fn page_cases() -> Vec<GoldenCase> {
    let rows: &[(&str, &str)] = &[
        ("EN0001", "source is not valid UTF-8"),
        ("EN0101", "missing `;`"),
        ("EN0201", "`===` or `!==`: use `==` and `!=`"),
        ("EN0909", "unknown or rejected `--cpu`"),
        ("EN1001", "async functions"),
        ("EN1041", "`--multiboot`, `--coverage`"),
        ("EN1301", "deferred command"),
        ("EN1302", "unknown command"),
        ("EN1303", "unknown target"),
    ];
    rows.iter()
        .map(|(code, title)| {
            case(
                &format!("explain/page/{code}"),
                &["explain", code],
                0,
                &format!("{code}: {title}"),
            )
        })
        .collect()
}

fn title_cases() -> Vec<GoldenCase> {
    let rows: &[(&str, &str)] = &[
        (
            "EN0310",
            "no top-level statements or `main` on a hosted target",
        ),
        // Unreached codes only: M3's went to M4 and later ones before M3's pages
        // (M3 plan 0.4), as M2's did before M2's (M2 plan 0.4).
        ("EN0315", "module has a stale interface file and no source"),
        ("EN0414", "monomorphisation depth above 64"),
        ("EN0821", "second `@globalAllocator`"),
        ("EN0822", "allocator type lacks `GlobalAllocator`"),
        ("EN0902", "unknown mnemonic"),
        ("EN1101", "`expect` outside a test"),
        ("EN1108", "unknown matcher"),
        ("EN1211", "`@devMigrate` hook called from code"),
        ("T0005", "`test.panics` body did not panic as expected"),
        ("EN0809", "missing or invalid `@entry`"),
        ("EN0901", "instruction above the target CPU level"),
        ("EN1106", "`test.only` under `--ci`"),
        ("EN1201", "program cannot run in the VM: `asm` reachable"),
        ("EN1210", "reload refused: migration impossible, with path"),
        ("EN1212", "stale migration hook"),
        ("T0001", "value matcher found different values"),
        ("T0008", "native watchdog timeout"),
    ];
    rows.iter()
        .map(|(code, title)| {
            case(
                &format!("explain/title/{code}"),
                &["explain", code],
                0,
                &format!("{code}: {title}"),
            )
        })
        .collect()
}

fn explain_failure_cases() -> Vec<GoldenCase> {
    let unknown: &[(&str, &str, &str)] = &[
        ("EN9999", "EN9999", "is not a diagnostic code"),
        ("EN1300", "EN1300", "is not a diagnostic code"),
        ("short", "EN130", "is not a diagnostic code"),
        ("long", "EN13011", "is not a diagnostic code"),
        ("lowercase", "en1301", "is not a diagnostic code"),
        ("lowercase_test_code", "t0001", "is not a diagnostic code"),
        ("word", "frobnicate", "is not a diagnostic code"),
        ("empty", "", "is not a diagnostic code"),
        ("space", "EN 1301", "is not a diagnostic code"),
        (
            "retired",
            "EN0704",
            "is retired: R3's rule 3 with EN0710 and EN0712 covers what it named",
        ),
    ];
    let mut cases: Vec<GoldenCase> = unknown
        .iter()
        .map(|(file, code, tail)| {
            case(
                &format!("explain/unknown/{file}"),
                &["explain", code],
                2,
                &format!("error: `{code}` {tail}"),
            )
        })
        .collect();
    for (code, why) in RETIRED {
        if code == "EN0704" {
            continue;
        }
        cases.push(case(
            &format!("explain/unknown/retired/{code}"),
            &["explain", code],
            2,
            &format!("error: `{code}` is retired: {why}"),
        ));
    }
    cases.push(case(
        "explain/unknown/control_characters",
        &["explain", "a\x1b[31mb"],
        2,
        "error: `a\\u{1b}[31mb` is not a diagnostic code",
    ));
    cases.extend([
        case(
            "explain/usage/no_code",
            &["explain"],
            2,
            "error: `enrang explain` needs a code",
        ),
        case(
            "explain/usage/two_codes",
            &["explain", "EN1301", "EN1302"],
            2,
            "error: `enrang explain` takes one code",
        ),
        case(
            "explain/usage/help_and_code",
            &["explain", "--help", "EN1301"],
            2,
            "error: `enrang explain` takes one code",
        ),
        case(
            "explain/usage/unknown_flag",
            &["explain", "--bogus"],
            2,
            "error: `--bogus` is not a flag of `enrang explain`",
        ),
        case(
            "explain/usage/misspelt_flag",
            &["explain", "--hepl"],
            2,
            "error: `--hepl` is not a flag of `enrang explain`",
        ),
        case(
            "explain/help_long",
            &["explain", "--help"],
            0,
            "Print the page of a diagnostic code, or its title until the page arrives.",
        ),
        case(
            "explain/help_short",
            &["explain", "-h"],
            0,
            "Print the page of a diagnostic code, or its title until the page arrives.",
        ),
    ]);
    cases
}

fn targets_cases() -> Vec<GoldenCase> {
    let flag_error = |flag: &str| format!("error: `{flag}` is not a flag of `enrang targets`");
    let summary = "List targets, CPU levels and aliases; --evidence prints the support table.";
    let evidence = "Support evidence per CPU family. A class is printed only once it is reached.";
    vec![
        case("targets/list", &["targets"], 0, "Targets:"),
        case("targets/evidence", &["targets", "--evidence"], 0, evidence),
        case("targets/help_long", &["targets", "--help"], 0, summary),
        case("targets/help_short", &["targets", "-h"], 0, summary),
        case(
            "targets/usage/unknown_flag",
            &["targets", "--bogus"],
            2,
            &flag_error("--bogus"),
        ),
        case(
            "targets/usage/misspelt_evidence",
            &["targets", "--evidnce"],
            2,
            &flag_error("--evidnce"),
        ),
        case(
            "targets/usage/evidence_with_a_value",
            &["targets", "--evidence=yes"],
            2,
            &flag_error("--evidence=yes"),
        ),
        case(
            "targets/usage/misspelt_help",
            &["targets", "--hepl"],
            2,
            &flag_error("--hepl"),
        ),
        case(
            "targets/usage/argument",
            &["targets", "x86_64-linux"],
            2,
            &flag_error("x86_64-linux"),
        ),
        case(
            "targets/usage/two_flags",
            &["targets", "--evidence", "--evidence"],
            2,
            "error: `enrang targets` takes one flag at most",
        ),
        case(
            "targets/usage/flag_and_argument",
            &["targets", "--evidence", "x"],
            2,
            "error: `enrang targets` takes one flag at most",
        ),
    ]
}

fn command_table_cases() -> Vec<GoldenCase> {
    let mut cases = Vec::new();
    for name in DEFERRED {
        cases.push(case(
            &format!("deferred/{name}"),
            &[name],
            2,
            &format!("error[EN1301]: `enrang {name}` is not part of the prototype"),
        ));
    }
    for alias in ALIASES {
        cases.push(case(
            &format!("alias/{}", alias.name),
            &[alias.name],
            2,
            &not_a_command(alias.name),
        ));
    }
    for command in LATER {
        cases.push(case(
            &format!("later/{}", command.name),
            &[command.name],
            2,
            &format!(
                "error: `enrang {}` arrives with milestone {}",
                command.name, command.since
            ),
        ));
    }
    let with_arguments: &[(&str, &[&str], &str)] = &[
        (
            "deferred/with_arguments/doc_file",
            &["doc", "main.en"],
            "error[EN1301]: `enrang doc` is not part of the prototype",
        ),
        (
            "deferred/with_arguments/install_package",
            &["install", "left-pad"],
            "error[EN1301]: `enrang install` is not part of the prototype",
        ),
        (
            "deferred/with_arguments/bench_help",
            &["bench", "--help"],
            "error[EN1301]: `enrang bench` is not part of the prototype",
        ),
        (
            "alias/with_arguments/tsc_file",
            &["tsc", "main.en"],
            "error[EN1302]: `tsc` is not an `enrang` command",
        ),
        (
            "alias/with_arguments/start_help",
            &["start", "--help"],
            "error[EN1302]: `start` is not an `enrang` command",
        ),
        (
            "later/with_arguments/build_file",
            &["build", "main.en"],
            "error: `enrang build` arrives with milestone M5",
        ),
        (
            "later/with_arguments/build_help",
            &["build", "--help"],
            "error: `enrang build` arrives with milestone M5",
        ),
        (
            "later/with_arguments/run_vm",
            &["run", "--vm", "main.en"],
            "error: `enrang run` arrives with milestone M4",
        ),
        (
            "later/with_arguments/run_program_arguments",
            &["run", "main.en", "--", "--help"],
            "error: `enrang run` arrives with milestone M4",
        ),
        (
            "later/with_arguments/dev_file",
            &["dev", "main.en"],
            "error: `enrang dev` arrives with milestone M6",
        ),
        (
            "later/with_arguments/test_watch",
            &["test", "--watch"],
            "error: `enrang test` arrives with milestone M4",
        ),
    ];
    for (name, args, head) in with_arguments {
        cases.push(case(name, args, 2, head));
    }
    cases
}

/// `check`, `fmt` and `init` where they need no file and read empty standard input:
/// help, usage messages, `fmt` of nothing, and what `check` and `fmt` report before
/// they read any source (the phase 0 codes of M1). The transcripts that need files or
/// standard input are in `cli-project` (`project.rs`).
fn working_cases() -> Vec<GoldenCase> {
    let check_help = "Check a file's syntax, types and borrows.";
    let fmt_help = "Format files in the canonical style, or report those that would change.";
    let init_help = "Create a project without overwriting anything; M9 adds `--kernel`.";
    let not_a_flag =
        |flag: &str, command: &str| format!("error: `{flag}` is not a flag of `enrang {command}`");
    let not_found = |path: &str| format!("error[EN1305]: file not found: `{path}`");
    let dwarf = "error[EN1034]: DWARF output is not supported yet";
    let not_yet = "error[EN1041]: this flag is not supported yet";
    let rows: Vec<(&str, &[&str], i32, String)> =
        vec![
        (
            "check/help_long",
            &["check", "--help"],
            0,
            check_help.to_owned(),
        ),
        (
            "check/help_short",
            &["check", "-h"],
            0,
            check_help.to_owned(),
        ),
        (
            "check/usage/emit_unknown",
            &["check", "--emit=ast"],
            2,
            "error: `--emit=ast` is not a value `enrang check` takes".to_owned(),
        ),
        (
            "check/usage/emit_misspelt",
            &["check", "--emit=sumary", "main.en"],
            2,
            "error: `--emit=sumary` is not a value `enrang check` takes".to_owned(),
        ),
        (
            "check/usage/emit_empty",
            &["check", "--emit="],
            2,
            "error: `--emit` needs a value".to_owned(),
        ),
        (
            "check/usage/unknown_flag",
            &["check", "--bogus"],
            2,
            not_a_flag("--bogus", "check"),
        ),
        (
            "check/usage/misspelt_flag",
            &["check", "--taget=i386-linux", "main.en"],
            2,
            not_a_flag("--taget=i386-linux", "check"),
        ),
        (
            "check/usage/version",
            &["check", "--version"],
            2,
            not_a_flag("--version", "check"),
        ),
        (
            "check/usage/two_files",
            &["check", "a.en", "b.en"],
            2,
            "error: `enrang check` takes one file".to_owned(),
        ),
        (
            "check/usage/no_value",
            &["check", "--target"],
            2,
            "error: `--target` needs a value".to_owned(),
        ),
        (
            "check/usage/empty_value",
            &["check", "--cpu=", "main.en"],
            2,
            "error: `--cpu` needs a value".to_owned(),
        ),
        (
            "check/usage/bad_color",
            &["check", "--color=sometimes"],
            2,
            "error: `--color=sometimes` is not a value of `--color`".to_owned(),
        ),
        (
            "check/usage/misspelt_color",
            &["check", "--color=alway", "main.en"],
            2,
            "error: `--color=alway` is not a value of `--color`".to_owned(),
        ),
        (
            "check/usage/bad_error_format",
            &["check", "--error-format=xml"],
            2,
            "error: `--error-format=xml` is not a value of `--error-format`".to_owned(),
        ),
        (
            "check/usage/given_twice",
            &["check", "--cpu=i386", "--cpu=i486"],
            2,
            "error: `--cpu` is given twice".to_owned(),
        ),
        (
            "check/usage/deferred_given_twice",
            &["check", "--coverage", "--coverage"],
            2,
            "error: `--coverage` is given twice".to_owned(),
        ),
        (
            "check/usage/help_with_file",
            &["check", "--help", "main.en"],
            2,
            "error: `--help` takes no other arguments".to_owned(),
        ),
        (
            "check/usage/before_any_code",
            &[
                "check",
                "--coverage",
                "--target=bogus",
                "--bogus",
                "missing.en",
            ],
            2,
            not_a_flag("--bogus", "check"),
        ),
        (
            "check/no_file_no_manifest",
            &["check"],
            2,
            not_found("enrang.json"),
        ),
        (
            "check/missing",
            &["check", "missing.en"],
            2,
            not_found("missing.en"),
        ),
        ("check/empty_path", &["check", ""], 2, not_found("")),
        (
            "check/every_flag_error_before_the_file",
            &[
                "check",
                "--debug-info=dwarf",
                "--coverage",
                "--target=bogus",
                "missing.en",
            ],
            2,
            dwarf.to_owned(),
        ),
        (
            "check/alias_note_and_missing_file",
            &["check", "--target=i386-linux", "--cpu=k6", "missing.en"],
            2,
            "note: `k6` resolves to level `i586`".to_owned(),
        ),
        (
            "check/vm_target",
            &["check", "--target=vm64"],
            2,
            "error[EN1303]: unknown target `vm64`".to_owned(),
        ),
        (
            "check/cpu_native",
            &["check", "--cpu=native"],
            2,
            "error[EN0909]: `--cpu=native` is rejected".to_owned(),
        ),
        (
            "check/cpu_not_on_target",
            &["check", "--target=x86_64-linux", "--cpu=i686"],
            2,
            "error[EN0912]: level `i686` does not apply to target `x86_64-linux`".to_owned(),
        ),
        (
            "check/float_needs_level",
            &["check", "--target=i386-linux", "--float=sse2"],
            2,
            "error[EN0911]: `--float=sse2` needs level `sse2`, and this build is at level `i386`"
                .to_owned(),
        ),
        (
            "check/target_misspelt",
            &["check", "--target=i686-linux"],
            2,
            "error[EN1303]: unknown target `i686-linux`".to_owned(),
        ),
        (
            "check/target_windows_32",
            &["check", "--target=i386-windows"],
            2,
            "error[EN1031]: 32-bit Windows output is not supported yet".to_owned(),
        ),
        (
            "check/float_misspelt",
            &["check", "--float=sse"],
            2,
            "error[EN1304]: `--float=sse` is not a float strategy".to_owned(),
        ),
        (
            "check/debug_info",
            &["check", "--debug-info=dwarf"],
            2,
            dwarf.to_owned(),
        ),
        ("check/coverage", &["check", "--coverage"], 2, not_yet.to_owned()),
        (
            "check/multiboot",
            &["check", "--multiboot"],
            2,
            not_yet.to_owned(),
        ),
        ("fmt/help_long", &["fmt", "--help"], 0, fmt_help.to_owned()),
        ("fmt/help_short", &["fmt", "-h"], 0, fmt_help.to_owned()),
        ("fmt/empty_stdin", &["fmt"], 0, String::new()),
        ("fmt/empty_stdin_dash", &["fmt", "-"], 0, String::new()),
        (
            "fmt/check_empty_stdin",
            &["fmt", "--check"],
            0,
            String::new(),
        ),
        (
            "fmt/check_empty_stdin_dash",
            &["fmt", "-", "--check"],
            0,
            String::new(),
        ),
        ("fmt/missing", &["fmt", "missing.en"], 2, not_found("missing.en")),
        ("fmt/empty_path", &["fmt", ""], 2, not_found("")),
        (
            "fmt/check_missing",
            &["fmt", "--check", "a.en", "b"],
            2,
            not_found("a.en"),
        ),
        (
            "fmt/usage/unknown_flag",
            &["fmt", "--bogus"],
            2,
            not_a_flag("--bogus", "fmt"),
        ),
        (
            "fmt/usage/misspelt_check",
            &["fmt", "--chek", "src"],
            2,
            not_a_flag("--chek", "fmt"),
        ),
        (
            "fmt/usage/common_flag",
            &["fmt", "--color=never"],
            2,
            not_a_flag("--color=never", "fmt"),
        ),
        (
            "fmt/usage/check_twice",
            &["fmt", "--check", "--check"],
            2,
            "error: `--check` is given twice".to_owned(),
        ),
        (
            "fmt/usage/stdin_and_a_path",
            &["fmt", "-", "main.en"],
            2,
            "error: `-` is standard input, and takes no other path".to_owned(),
        ),
        (
            "fmt/usage/stdin_twice",
            &["fmt", "-", "-"],
            2,
            "error: `-` is standard input, and takes no other path".to_owned(),
        ),
        (
            "fmt/usage/help_with_path",
            &["fmt", "--help", "src"],
            2,
            "error: `--help` takes no other arguments".to_owned(),
        ),
        (
            "init/help_long",
            &["init", "--help"],
            0,
            init_help.to_owned(),
        ),
        ("init/help_short", &["init", "-h"], 0, init_help.to_owned()),
        (
            "init/kernel",
            &["init", "--kernel"],
            2,
            "error: `enrang init --kernel` arrives with milestone M9".to_owned(),
        ),
        (
            "init/kernel_with_name",
            &["init", "hello", "--kernel"],
            2,
            "error: `enrang init --kernel` arrives with milestone M9".to_owned(),
        ),
        (
            "init/usage/two_names",
            &["init", "a", "b"],
            2,
            "error: `enrang init` takes one name".to_owned(),
        ),
        (
            "init/usage/empty_name",
            &["init", ""],
            2,
            "error: the name of a project cannot be empty".to_owned(),
        ),
        (
            "init/usage/unknown_flag",
            &["init", "--bogus"],
            2,
            not_a_flag("--bogus", "init"),
        ),
        (
            "init/usage/misspelt_kernel",
            &["init", "--kernal"],
            2,
            not_a_flag("--kernal", "init"),
        ),
        (
            "init/usage/kernel_twice",
            &["init", "--kernel", "--kernel"],
            2,
            "error: `--kernel` is given twice".to_owned(),
        ),
        (
            "init/usage/help_with_name",
            &["init", "-h", "hello"],
            2,
            "error: `-h` takes no other arguments".to_owned(),
        ),
    ];
    rows.into_iter()
        .map(|(name, args, exit, head)| case(name, args, exit, &head))
        .collect()
}

fn unknown_cases() -> Vec<GoldenCase> {
    let names: &[(&str, &str)] = &[
        ("no_suggestion", "frobnicate"),
        ("help_word", "help"),
        ("version_word", "version"),
        ("empty", ""),
        ("space", "two words"),
        ("non_ascii", "bùild"),
        ("capitalised", "Build"),
        ("shouted", "BUILD"),
        ("typo/buidl", "buidl"),
        ("typo/rn", "rn"),
        ("typo/dv", "dv"),
        ("typo/tset", "tset"),
        ("typo/chekc", "chekc"),
        ("typo/explian", "explian"),
        ("typo/inti", "inti"),
        ("typo/targts", "targts"),
        ("typo/fmtt", "fmtt"),
        ("typo_of_deferred/lspp", "lspp"),
        ("typo_of_alias/tssc", "tssc"),
        ("flag/misspelt_help", "--hepl"),
        ("flag/misspelt_version", "--verison"),
        ("flag/help_with_a_value", "--help=1"),
        ("flag/unknown", "--bogus"),
        ("flag/single_letter", "-x"),
        ("flag/lowercase_version", "-v"),
        ("flag/dash", "-"),
        ("flag/double_dash", "--"),
        ("flag/not_top_level", "--evidence"),
        ("flag/of_a_later_command", "--color=always"),
    ];
    let mut cases: Vec<GoldenCase> = names
        .iter()
        .map(|(file, name)| {
            let head = if name.starts_with('-') {
                format!("error: `{name}` is not a flag of `enrang`")
            } else {
                not_a_command(name)
            };
            case(&format!("unknown/{file}"), &[name], 2, &head)
        })
        .collect();
    cases.push(case(
        "unknown/control_characters",
        &["a\x1b[31mb"],
        2,
        &not_a_command("a\\u{1b}[31mb"),
    ));
    cases
}

fn top_level_cases() -> Vec<GoldenCase> {
    let help_head = format!("The Enrang command line, milestone {CURRENT_MILESTONE}.");
    let version_head = format!(
        "enrang {} (milestone {CURRENT_MILESTONE})",
        env!("CARGO_PKG_VERSION")
    );
    let usage_of = |flag: &str| format!("error: `{flag}` takes no arguments");
    vec![
        case("top/help_long", &["--help"], 0, &help_head),
        case("top/help_short", &["-h"], 0, &help_head),
        case("top/version_long", &["--version"], 0, &version_head),
        case("top/version_short", &["-V"], 0, &version_head),
        case("top/no_arguments", &[], 2, "error: no command given"),
        case(
            "top/usage/help_with_argument",
            &["--help", "explain"],
            2,
            &usage_of("--help"),
        ),
        case(
            "top/usage/short_help_with_argument",
            &["-h", "x"],
            2,
            &usage_of("-h"),
        ),
        case(
            "top/usage/version_with_argument",
            &["--version", "x"],
            2,
            &usage_of("--version"),
        ),
        case(
            "top/usage/short_version_with_flag",
            &["-V", "--help"],
            2,
            &usage_of("-V"),
        ),
    ]
}

/// Every golden case of the suite.
pub fn table() -> Vec<GoldenCase> {
    let mut cases = top_level_cases();
    cases.extend(page_cases());
    cases.extend(title_cases());
    cases.extend(explain_failure_cases());
    cases.extend(targets_cases());
    cases.extend(working_cases());
    cases.extend(command_table_cases());
    cases.extend(unknown_cases());
    cases
}

pub fn register(h: &mut Harness) {
    for GoldenCase {
        name,
        args,
        exit,
        head,
    } in table()
    {
        let case_name = format!("golden/{name}");
        h.case(case_name, move || {
            let ran = enrang(&args);
            assert_eq!(ran.code, exit, "exit status of {args:?}: {ran:?}");
            let (printed, silent) = if exit == 0 {
                (&ran.stdout, &ran.stderr)
            } else {
                (&ran.stderr, &ran.stdout)
            };
            if head.is_empty() {
                assert_eq!(printed, "", "{args:?}");
            } else {
                assert_eq!(printed.lines().next(), Some(head.as_str()), "{args:?}");
            }
            assert_eq!(silent, "", "the other stream of {args:?}");
            let words: Vec<&str> = args.iter().map(String::as_str).collect();
            let in_process = inproc(&words);
            assert_eq!(in_process.stdout, ran.stdout, "{args:?} in-process");
            assert_eq!(in_process.stderr, ran.stderr, "{args:?} in-process");
            assert_eq!(i32::from(in_process.code), ran.code, "{args:?} in-process");
            golden(SUITE, &name, &transcript(&args, &ran))
        });
    }
}
