//! One golden per command, flag and message (TESTING 17 and 18).
//!
//! The table holds, by hand, each case's exit status and the first line it must
//! print. A golden can be blessed and these cannot, so blessing never changes which
//! outcome a command is expected to have.

use enrang_cli::{ALIASES, DEFERRED, LATER, run};
use enrang_testkit::{Harness, golden};

use crate::support::{SUITE, enrang, strings, transcript};

pub struct GoldenCase {
    pub name: String,
    pub args: Vec<String>,
    pub exit: i32,
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
    vec![
        case(
            "explain/page/EN1301",
            &["explain", "EN1301"],
            0,
            "EN1301: deferred command",
        ),
        case(
            "explain/page/EN1302",
            &["explain", "EN1302"],
            0,
            "EN1302: unknown command",
        ),
    ]
}

fn title_cases() -> Vec<GoldenCase> {
    let rows: &[(&str, &str)] = &[
        ("EN0001", "source is not valid UTF-8"),
        ("EN0101", "missing `;`"),
        ("EN0201", "`===` or `!==`: use `==` and `!=`"),
        ("EN0301", "unresolved name"),
        ("EN0310", "no `main` on a hosted target"),
        ("EN0401", "mismatched types"),
        ("EN0430", "integer division truncates"),
        ("EN0601", "use after move"),
        ("EN0710", "returning a reference to local data"),
        ("EN0809", "missing or invalid `@entry`"),
        ("EN0901", "instruction above the target CPU level"),
        ("EN0909", "unknown or rejected `--cpu`"),
        ("EN1001", "async functions"),
        ("EN1041", "`--multiboot`, `--coverage`"),
        ("EN1106", "`test.only` under `--ci`"),
        ("EN1201", "program cannot run in the VM: `asm` reachable"),
        ("EN1210", "reload refused: migration impossible, with path"),
        ("EN1303", "unknown target"),
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
            "is retired: R3's rule 4 with EN0710 and EN0712 covers what it named",
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
            "deferred/with_arguments/fmt_file",
            &["fmt", "main.en"],
            "error[EN1301]: `enrang fmt` is not part of the prototype",
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
        (
            "later/with_arguments/check_file",
            &["check", "main.en"],
            "error: `enrang check` arrives with milestone M1",
        ),
        (
            "later/with_arguments/check_version",
            &["check", "--version"],
            "error: `enrang check` arrives with milestone M1",
        ),
        (
            "later/with_arguments/init_name",
            &["init", "hello"],
            "error: `enrang init` arrives with milestone M1",
        ),
        (
            "later/with_arguments/init_kernel",
            &["init", "--kernel"],
            "error: `enrang init` arrives with milestone M1",
        ),
    ];
    for (name, args, head) in with_arguments {
        cases.push(case(name, args, 2, head));
    }
    cases
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
        ("typo_of_deferred/fmtt", "fmtt"),
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
    let help_head = "The Enrang command line, milestone M0.";
    let version_head = format!(
        "enrang {} (milestone M0, no compiler yet)",
        env!("CARGO_PKG_VERSION")
    );
    let usage_of = |flag: &str| format!("error: `{flag}` takes no arguments");
    vec![
        case("top/help_long", &["--help"], 0, help_head),
        case("top/help_short", &["-h"], 0, help_head),
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
            assert_eq!(printed.lines().next(), Some(head.as_str()), "{args:?}");
            assert_eq!(silent, "", "the other stream of {args:?}");
            let in_process = run(&args, false);
            assert_eq!(in_process.stdout, ran.stdout, "{args:?} in-process");
            assert_eq!(in_process.stderr, ran.stderr, "{args:?} in-process");
            assert_eq!(i32::from(in_process.code), ran.code, "{args:?} in-process");
            golden(SUITE, &name, &transcript(&args, &ran))
        });
    }
}
