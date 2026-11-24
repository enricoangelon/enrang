//! TESTING 23's case counts. A milestone's row asks for a number of cases; each suite
//! that holds that milestone's cases checks its own share of them as a case of its
//! own (`M1_SHARE` in the `main.rs` of the syntax and CLI suites, `M2_SHARE` in those
//! of the sema, hir, layout, rtlib, CLI and diag suites). This module reads the
//! shares from those sources, since it cannot run the suites, and checks that they
//! add up to the count TESTING 23 gives, so a share lowered to let a suite pass fails
//! here.
//!
//! M3's row asks for 4,000 more cases, half of them negative with fixed siblings (M3
//! plan f.9). Its suites are the four that M3 created, mir, borrowck, mirbuild and
//! the driver's pipeline, every case of which is M3's, the CLI's fixtures of M3's
//! codes, the diag suite's cases of their explain pages, and the meta suite's cases
//! of the M3 gates. A share is checked as M2's are once its suite declares it, and
//! from the bump that closes M3 every suite must declare one and the shares must add
//! up, as must every firing fixture of an M3 code have its near-miss sibling of the
//! same name, which is the "half negative with fixed siblings"; before the bump a
//! share not yet declared, and a sibling not yet written, are no failure. The hir and
//! sema suites hold M3 cases too, from M3's first stage, but their M2 shares count
//! every case they register, so an M3 share there would count those cases twice:
//! they hold none of M3's (a choice; M3 plan f.9 forecast 30 each).

use std::collections::BTreeSet;

use enrang_diag::{CURRENT_MILESTONE, Code, Milestone};
use enrang_testkit::{FixtureStatus, Harness, workspace_root};

use crate::covers::{Line, bump_problems, gate_lines, row_cells, stem};
use crate::gating::{Run, fake_fixture, fixture_status};
use crate::support::{Fixture, Place, fixtures, milestone_in, read, run_cached};

/// The suites that hold M1's cases, by the `main.rs` that declares each one's share.
const M1_SUITES: [&str; 2] = [
    "crates/enrang-syntax/tests/syntax/main.rs",
    "crates/enrang-cli/tests/cli/main.rs",
];

/// The suites that hold M2's cases (M2 plan g.8): the four suites M2 created, every
/// case of which is M2's, the CLI suite's fixtures of M2's codes, and the diag
/// suite's cases of their explain pages.
const M2_SUITES: [&str; 6] = [
    "crates/enrang-sema/tests/sema/main.rs",
    "crates/enrang-hir/tests/hir/main.rs",
    "crates/enrang-layout/tests/layout/main.rs",
    "crates/enrang-rtlib/tests/rtlib/main.rs",
    "crates/enrang-cli/tests/cli/main.rs",
    "crates/enrang-diag/tests/diag/main.rs",
];

/// The suites that hold M3's cases (M3 plan f.9), by the `main.rs` that declares
/// each one's share.
const M3_SUITES: [&str; 7] = [
    "crates/enrang-mir/tests/mir/main.rs",
    "crates/enrang-borrowck/tests/borrowck/main.rs",
    "crates/enrang-mirbuild/tests/mirbuild/main.rs",
    "crates/enrang-driver/tests/pipeline/main.rs",
    "crates/enrang-cli/tests/cli/main.rs",
    "crates/enrang-diag/tests/diag/main.rs",
    "crates/enrang-suite/tests/meta/main.rs",
];

/// How each of M3's suites counts, in the order of [`M3_SUITES`].
const M3_COUNTING: [Counting; 7] = [
    Counting::All,
    Counting::All,
    Counting::All,
    Counting::All,
    Counting::Filtered("compile/"),
    Counting::Filtered("explain/"),
    Counting::Prefixed,
];

/// How a suite counts a milestone's cases: every case it registers, the cases its
/// `is_mN` keeps, those of the codes due at the milestone under the prefix named,
/// or the cases whose names open with one of its `MN_PREFIXES`.
#[derive(Copy, Clone, Debug)]
enum Counting {
    All,
    Filtered(&'static str),
    Prefixed,
}

/// How each of M2's suites counts, in the order of [`M2_SUITES`].
const M2_COUNTING: [Counting; 6] = [
    Counting::All,
    Counting::All,
    Counting::All,
    Counting::All,
    Counting::Filtered("compile/"),
    Counting::Filtered("explain/"),
];

/// The M2 share case as each suite writes it, whole: a case that asserts anything
/// weaker than `m2 >= M2_SHARE` differs from it.
const M2_SHARE_CASE: &str = "    h.case(
        \"count/this suite holds its share of M2's cases\",
        move || {
            assert!(m2 >= M2_SHARE, \"{m2} cases, short of {M2_SHARE}\");
        },
    );
";

/// The `is_m2` of a suite that counts the cases under `prefix`, whole.
fn is_m2_text(prefix: &str) -> String {
    is_text(Milestone::M2, prefix)
}

/// The `is_mN` of a suite that counts `milestone`'s cases under `prefix`, whole.
fn is_text(milestone: Milestone, prefix: &str) -> String {
    let lower = format!("{milestone}").to_lowercase();
    format!(
        "fn is_{lower}(name: &str) -> bool {{
    name.strip_prefix(\"{prefix}\")
        .and_then(|rest| rest.split_once('/'))
        .and_then(|(code, _)| Code::from_name(code))
        .is_some_and(|code| code.since() == Milestone::{milestone})
}}
"
    )
}

/// The `is_mN` of a suite that counts the cases whose names open with one of its
/// `MN_PREFIXES`, whole.
fn is_prefixed_text(milestone: Milestone) -> String {
    let lower = format!("{milestone}").to_lowercase();
    format!(
        "fn is_{lower}(name: &str) -> bool {{
    {milestone}_PREFIXES.iter().any(|prefix| name.starts_with(prefix))
}}
"
    )
}

/// The share case of `milestone` as each suite writes it, whole.
fn share_case_text(milestone: Milestone) -> String {
    let lower = format!("{milestone}").to_lowercase();
    format!(
        "    h.case(
        \"count/this suite holds its share of {milestone}'s cases\",
        move || {{
            assert!({lower} >= {milestone}_SHARE, \"{{{lower}}} cases, short of {{{milestone}_SHARE}}\");
        }},
    );
"
    )
}

/// What is wrong with how `source`, an M2 suite's `main.rs`, counts its share: it
/// must hold [`M2_SHARE_CASE`] word for word, after the count `counting` gives,
/// `let m2 = h.len();` right before the case, or the count of `is_m2` with no use
/// of `m2` between it and the case and `is_m2` itself word for word. So a count
/// set by hand, a count of every case where only the M2 ones count, or a weakened
/// assertion fails here, though the numbers still add up.
fn share_block(source: &str, counting: Counting) -> Result<(), String> {
    share_block_for(source, Milestone::M2, counting)
}

/// [`share_block`] for `milestone`'s share: its case, count and `is_mN` as M2's are
/// with `mN` and `MN_SHARE` in place of `m2` and `M2_SHARE`; a suite counting by
/// prefixes holds `is_mN` over a non-empty `MN_PREFIXES`.
fn share_block_for(source: &str, milestone: Milestone, counting: Counting) -> Result<(), String> {
    let lower = format!("{milestone}").to_lowercase();
    let case = source.find(&share_case_text(milestone)).ok_or_else(|| {
        format!("the {milestone} share case is not `assert!({lower} >= {milestone}_SHARE, ..)` word for word")
    })?;
    let filtered =
        format!("    let {lower} = h.names().filter(|name| is_{lower}(name)).count();\n");
    match counting {
        Counting::All => {
            let count = format!("    let {lower} = h.len();\n");
            if !source[..case].ends_with(&count) {
                return Err(format!(
                    "`{}` is not right before the share case",
                    count.trim()
                ));
            }
        }
        Counting::Filtered(_) | Counting::Prefixed => {
            let at = source[..case]
                .rfind(&filtered)
                .ok_or_else(|| format!("no `{}`", filtered.trim()))?;
            if source[at + filtered.len()..case].contains(&lower) {
                return Err(format!(
                    "`{lower}` is used between its count and the share case"
                ));
            }
            let wanted = match counting {
                Counting::Filtered(prefix) => is_text(milestone, prefix),
                _ => is_prefixed_text(milestone),
            };
            if !source.contains(&wanted) {
                return Err(format!("`is_{lower}` is not, word for word:\n{wanted}"));
            }
            if matches!(counting, Counting::Prefixed) {
                let head = format!("const {milestone}_PREFIXES: [&str; ");
                let count = source
                    .split(head.as_str())
                    .nth(1)
                    .and_then(|rest| rest.split(']').next())
                    .and_then(|n| n.parse::<usize>().ok());
                if !count.is_some_and(|n| n > 0) {
                    return Err(format!("no non-empty `{head}..]`"));
                }
            }
        }
    }
    Ok(())
}

/// The suites that hold `milestone`'s cases.
fn suites(milestone: Milestone) -> &'static [&'static str] {
    match milestone {
        Milestone::M1 => &M1_SUITES,
        Milestone::M2 => &M2_SUITES,
        Milestone::M3 => &M3_SUITES,
        other => panic!("no suite holds a share of {other}'s cases yet"),
    }
}

/// The case each of a milestone's suites registers to check its share.
fn share_case(milestone: Milestone) -> String {
    format!("\"count/this suite holds its share of {milestone}'s cases\"")
}

/// The assertion of that case: `assert!(m2 >= M2_SHARE`.
fn share_assertion(milestone: Milestone) -> String {
    let lower = format!("{milestone}").to_lowercase();
    format!("assert!({lower} >= {milestone}_SHARE")
}

/// The number a gate item such as `2,500 cases` or `4,000 more cases` starts with.
pub fn leading_count(item: &str) -> Option<usize> {
    let number = item.trim().split(' ').next()?;
    if number.is_empty() || !number.bytes().all(|b| b.is_ascii_digit() || b == b',') {
        return None;
    }
    number.replace(',', "").parse().ok()
}

/// The count of cases TESTING 23's row for `milestone` asks for: its first item.
fn count_in_testing_23(milestone: Milestone) -> usize {
    let testing = read("docs/TESTING.md");
    let row = testing
        .lines()
        .skip_while(|line| *line != "| M | Gate |")
        .map(row_cells)
        .find(|row| {
            row.first()
                .and_then(|cell| milestone_in(cell))
                .is_some_and(|m| m == milestone)
        })
        .unwrap_or_else(|| panic!("TESTING 23 has no row for {milestone}"));
    let first = row[1].split(';').next().expect("an item");
    leading_count(first).unwrap_or_else(|| panic!("{first:?} is no count of cases"))
}

/// The share a suite's source declares for `milestone`:
/// `pub const M1_SHARE: usize = 1_800;`.
pub fn declared_share(source: &str, milestone: Milestone) -> Option<usize> {
    let head = format!("pub const {milestone}_SHARE: usize = ");
    let rest = source.split(head.as_str()).nth(1)?;
    let number = rest.split(';').next()?;
    if !number.bytes().all(|b| b.is_ascii_digit() || b == b'_') {
        return None;
    }
    number.replace('_', "").parse().ok()
}

/// The shares of `milestone`'s suites, each checked to be declared and asserted by
/// its suite's share case; panics on a suite that does not.
fn shares(milestone: Milestone) -> Vec<(&'static str, usize)> {
    suites(milestone)
        .iter()
        .map(|path| {
            let source = read(path);
            let share = declared_share(&source, milestone)
                .unwrap_or_else(|| panic!("{path} declares no `{milestone}_SHARE`"));
            assert!(
                source.contains(&share_case(milestone)),
                "{path} never checks its share of {milestone}'s cases"
            );
            assert!(
                source.contains(&share_assertion(milestone)),
                "{path} checks no count against its share of {milestone}'s cases"
            );
            (*path, share)
        })
        .collect()
}

/// What is wrong with M3's shares at `current`, each suite's source read by `read`:
/// a share a suite declares must be counted as [`share_block_for`] says, whatever
/// the milestone; from M3 on, every suite of [`M3_SUITES`] must declare one, they
/// must add up to TESTING 23's count, `wanted`, and the CLI's M1 count must leave
/// out M3's fixtures as it leaves out M2's.
fn m3_share_problems(
    current: Milestone,
    read: &dyn Fn(&str) -> String,
    wanted: usize,
) -> Vec<String> {
    let reached = current >= Milestone::M3;
    let mut problems = Vec::new();
    let mut total = 0;
    for (path, counting) in M3_SUITES.iter().zip(M3_COUNTING) {
        let source = read(path);
        match declared_share(&source, Milestone::M3) {
            Some(share) => {
                total += share;
                if let Err(error) = share_block_for(&source, Milestone::M3, counting) {
                    problems.push(format!("{path}: {error}"));
                }
            }
            None if reached => problems.push(format!("{path} declares no `M3_SHARE`")),
            None => {}
        }
    }
    if reached && total < wanted {
        problems.push(format!(
            "the shares of M3 add up to {total}, short of {wanted}"
        ));
    }
    let cli = read("crates/enrang-cli/tests/cli/main.rs");
    let counts_m3 = cli.contains("fn is_m3(");
    if (reached || counts_m3) && !cli.contains("&& !is_m3(name)") {
        problems.push("the CLI's M1 count takes M3's fixtures".to_owned());
    }
    problems
}

/// The compile fixtures that are firing fixtures of a code due at `milestone`, by
/// their directory.
fn firing_of(fixtures: &[Fixture], milestone: Milestone) -> Vec<&Fixture> {
    fixtures
        .iter()
        .filter(|fixture| !fixture.near_miss)
        .filter(|fixture| {
            Code::from_name(&fixture.code).is_some_and(|code| code.since() == milestone)
        })
        .collect()
}

/// One line per firing fixture of an M3 code: its near-miss sibling, of the same
/// name in the same directory, exists and passes.
fn sibling_lines(fixtures: &[Fixture], run: &Run<'_>) -> Vec<Line> {
    let near: BTreeSet<&str> = fixtures
        .iter()
        .filter(|fixture| fixture.near_miss)
        .map(|fixture| fixture.path.as_str())
        .collect();
    firing_of(fixtures, Milestone::M3)
        .into_iter()
        .map(|fixture| {
            let sibling = format!(
                "{}/{}.pass.en",
                fixture.path.rsplit_once('/').map_or("", |(dir, _)| dir),
                stem(fixture)
            );
            let status = match fixtures.iter().find(|other| other.path == sibling) {
                Some(other) if near.contains(other.path.as_str()) => fixture_status(other, run),
                _ => FixtureStatus::Missing,
            };
            Line {
                id: format!("sibling of {}", fixture.path),
                since: Milestone::M3,
                status,
            }
        })
        .collect()
}

fn read_or_empty(path: &str) -> String {
    std::fs::read_to_string(workspace_root().join(path)).unwrap_or_default()
}

pub fn register(h: &mut Harness) {
    h.case("counts/TESTING 23 asks M3 for 4,000 more cases", || {
        assert_eq!(count_in_testing_23(Milestone::M3), 4_000);
    });
    h.case(
        "counts/M3: the shares of M3's suites add up to TESTING 23's count once M3 is reached",
        || {
            let problems = m3_share_problems(
                CURRENT_MILESTONE,
                &read_or_empty,
                count_in_testing_23(Milestone::M3),
            );
            assert_eq!(problems, Vec::<String>::new());
        },
    );
    h.case(
        "counts/M3: at the bump every M3 suite must declare and count its share",
        || {
            // The bump that closes M3, simulated on the real sources: each suite that
            // declares no share yet is a problem then, and none before.
            let wanted = count_in_testing_23(Milestone::M3);
            let at_bump = m3_share_problems(Milestone::M3, &read_or_empty, wanted);
            for path in M3_SUITES {
                let declared = declared_share(&read_or_empty(path), Milestone::M3).is_some();
                let missing = format!("{path} declares no `M3_SHARE`");
                assert_eq!(at_bump.contains(&missing), !declared, "{path}: {at_bump:?}");
            }
            let total: usize = M3_SUITES
                .iter()
                .filter_map(|path| declared_share(&read_or_empty(path), Milestone::M3))
                .sum();
            let short = at_bump
                .iter()
                .any(|problem| problem.starts_with("the shares of M3"));
            assert_eq!(short, total < wanted, "{at_bump:?}");
        },
    );
    h.case(
        "counts/M3: every firing fixture of an M3 code has its fixed sibling",
        || {
            let report = gate_lines(&sibling_lines(&fixtures(), &run_cached), CURRENT_MILESTONE);
            assert!(report.is_clean(), "\n{report}");
        },
    );
    h.case(
        "counts/M3: before the bump no sibling is due, and at the bump every one is",
        || {
            let lines = sibling_lines(&fixtures(), &run_cached);
            assert_eq!(gate_lines(&lines, Milestone::M2).enforced, 0);
            for current in [CURRENT_MILESTONE, Milestone::M3] {
                let problems = bump_problems(&lines, current);
                assert!(problems.is_empty(), "{current}: {problems:?}");
            }
        },
    );
    h.case("counts/M3: a missing sibling is early before the bump and a gap at it", || {
        let fixtures = [
            fake_fixture("tests/compile/EN0601/a.fail.en", "x //~ EN0601\n"),
            fake_fixture("tests/compile/EN0601/a.pass.en", "y\n"),
            fake_fixture("tests/compile/EN0601/b.fail.en", "x //~ EN0601\n"),
            fake_fixture("tests/compile/EN0706/b.pass.en", "y\n"),
            fake_fixture("tests/compile/EN0706/c.fail.en", "x //~ EN0706\n"),
            fake_fixture("tests/compile/EN0706/c.pass.en", "y\n"),
            fake_fixture("tests/compile/EN0401/d.fail.en", "x //~ EN0401\n"),
        ];
        let cli = crate::gating::FakeCli::new([])
            .breaking("check tests/compile/EN0706/c.pass.en", 1, "");
        let run = |place: &Place, args: &[String]| cli.run(place, args);
        let lines = sibling_lines(&fixtures, &run);
        // `b`'s sibling stands in another directory, `c`'s fails, and `d` is M2's.
        assert_eq!(
            gate_lines(&lines, Milestone::M3).to_string(),
            "gap: sibling of tests/compile/EN0601/b.fail.en has no fixture (since M3, current M3)\n\
             gap: sibling of tests/compile/EN0706/c.fail.en has a failing fixture (since M3, current M3)\n"
        );
        let before = gate_lines(&lines, Milestone::M2);
        assert!(before.is_clean(), "{before}");
        assert_eq!((before.enforced, before.deferred), (0, 3));
    });
    h.case("counts/M3: a share counted another way fails, and the bump needs them all", || {
        let all = format!("pub const M3_SHARE: usize = 4_000;\nfn main() {{\n    let m3 = h.len();\n{}}}\n", share_case_text(Milestone::M3));
        assert_eq!(share_block_for(&all, Milestone::M3, Counting::All), Ok(()));
        let prefixed = format!(
            "const M3_PREFIXES: [&str; 1] = [\"x/\"];\n{}fn main() {{\n    let m3 = h.names().filter(|name| is_m3(name)).count();\n{}}}\n",
            is_prefixed_text(Milestone::M3),
            share_case_text(Milestone::M3)
        );
        assert_eq!(share_block_for(&prefixed, Milestone::M3, Counting::Prefixed), Ok(()));
        let empty = prefixed.replace("[&str; 1] = [\"x/\"]", "[&str; 0] = []");
        assert!(share_block_for(&empty, Milestone::M3, Counting::Prefixed).is_err());
        let filtered = format!(
            "{}fn main() {{\n    let m3 = h.names().filter(|name| is_m3(name)).count();\n{}}}\n",
            is_text(Milestone::M3, "compile/"),
            share_case_text(Milestone::M3)
        );
        assert_eq!(share_block_for(&filtered, Milestone::M3, Counting::Filtered("compile/")), Ok(()));
        let m2_filter = filtered.replace("== Milestone::M3", "== Milestone::M2");
        assert!(share_block_for(&m2_filter, Milestone::M3, Counting::Filtered("compile/")).is_err());
        let weak = all.replace("m3 >= M3_SHARE,", "m3 >= M3_SHARE || m3 > 0,");
        assert!(share_block_for(&weak, Milestone::M3, Counting::All).is_err());
        // M2's text is the one M2's suites hold.
        assert_eq!(share_case_text(Milestone::M2), M2_SHARE_CASE);
        // Fake sources: before M3 a share not declared is no problem, at M3 it is,
        // and so are shares that fall short and a CLI that counts M3's fixtures for M1.
        let source = |path: &str| -> String {
            if path.ends_with("mir/main.rs") {
                all.replace("4_000", "3_000")
            } else if path.ends_with("cli/main.rs") {
                "fn is_m1(name: &str) -> bool { x(name) && !is_m2(name) }\nfn is_m3(".to_owned()
            } else {
                String::new()
            }
        };
        assert_eq!(
            m3_share_problems(Milestone::M2, &source, 4_000),
            ["the CLI's M1 count takes M3's fixtures"]
        );
        let at_bump = m3_share_problems(Milestone::M3, &source, 4_000);
        assert_eq!(at_bump.len(), 6 + 2, "{at_bump:?}");
        assert!(at_bump.contains(&"the shares of M3 add up to 3000, short of 4000".to_owned()));
        assert!(!at_bump.iter().any(|p| p.starts_with("crates/enrang-mir/")), "{at_bump:?}");
    });
    h.case("counts/TESTING 23 asks M1 for 2,500 cases", || {
        assert_eq!(count_in_testing_23(Milestone::M1), 2_500);
    });
    h.case("counts/TESTING 23 asks M2 for 2,500 more cases", || {
        assert_eq!(count_in_testing_23(Milestone::M2), 2_500);
    });
    for milestone in [Milestone::M1, Milestone::M2, Milestone::M3] {
        h.case(
            format!("counts/the shares of {milestone}'s suites add up to TESTING 23's count"),
            move || {
                let total: usize = shares(milestone).iter().map(|(_, share)| share).sum();
                let wanted = count_in_testing_23(milestone);
                assert!(
                    total >= wanted,
                    "the shares of {milestone} add up to {total}, short of {wanted}"
                );
            },
        );
    }
    h.case(
        "counts/M2's shares are those its suites declare (M2 plan g.8, as built)",
        || {
            // The plan forecast sema 1,900, hir 150, layout 150, rtlib 50 and the CLI's
            // fixtures 250. The suites hold what the stages built: fewer sema and rtlib
            // cases, more fixtures, and the pages of every M2 code, so the shares are
            // set from them, each a floor its own suite checks, and still add up.
            let found: Vec<(&str, usize)> = shares(Milestone::M2);
            let wanted = [
                ("crates/enrang-sema/tests/sema/main.rs", 1_500),
                ("crates/enrang-hir/tests/hir/main.rs", 150),
                ("crates/enrang-layout/tests/layout/main.rs", 150),
                ("crates/enrang-rtlib/tests/rtlib/main.rs", 20),
                ("crates/enrang-cli/tests/cli/main.rs", 500),
                ("crates/enrang-diag/tests/diag/main.rs", 300),
            ];
            assert_eq!(found, wanted);
        },
    );
    h.case(
        "counts/M3's shares are those its suites declare (M3 plan f.9, as built)",
        || {
            // The plan forecast mir 400, borrowck 900, mirbuild 50, the pipeline 750,
            // the CLI's fixtures 1,700, diag 60, hir and sema 30 each, and meta 80.
            // The suites hold what the stages built: fewer mir and mirbuild cases, far
            // more borrowck and pipeline ones, and none counted again in hir or sema,
            // whose M2 shares count every case they hold. Each share is a floor its own
            // suite checks, set from them at the close of stage 5, and they add up to
            // half again TESTING 23's 4,000, so a lowered one is caught here, not by
            // the sum.
            assert!(Milestone::M3 <= CURRENT_MILESTONE, "M3's shares are due");
            let found: Vec<(&str, usize)> = shares(Milestone::M3);
            let wanted = [
                ("crates/enrang-mir/tests/mir/main.rs", 215),
                ("crates/enrang-borrowck/tests/borrowck/main.rs", 1_450),
                ("crates/enrang-mirbuild/tests/mirbuild/main.rs", 3),
                ("crates/enrang-driver/tests/pipeline/main.rs", 2_750),
                ("crates/enrang-cli/tests/cli/main.rs", 1_390),
                ("crates/enrang-diag/tests/diag/main.rs", 85),
                ("crates/enrang-suite/tests/meta/main.rs", 85),
            ];
            assert_eq!(found, wanted);
            let total: usize = wanted.iter().map(|(_, share)| share).sum();
            assert_eq!(total, 5_978);
            assert!(total >= count_in_testing_23(Milestone::M3));
        },
    );
    h.case(
        "counts/each M3 suite counts its M3 cases as its share case says",
        || {
            for (path, counting) in M3_SUITES.iter().zip(M3_COUNTING) {
                if let Err(error) = share_block_for(&read(path), Milestone::M3, counting) {
                    panic!("{path}: {error}");
                }
            }
            // The meta suite's own M3 cases are those of its four prefixes, as
            // dod.md documents them: dropping one would leave the count at its
            // share and the share case green (gate mutant G08).
            let meta = read("crates/enrang-suite/tests/meta/main.rs");
            assert!(
                meta.contains(
                    "const M3_PREFIXES: [&str; 4] = [\"covers/M3\", \"row/M3\", \"counts/M3\", \"disagreements/\"];"
                ),
                "the meta suite's M3 prefixes changed"
            );
        },
    );
    h.case(
        "counts/each M2 suite counts its M2 cases as its share case says",
        || {
            for (path, counting) in M2_SUITES.iter().zip(M2_COUNTING) {
                if let Err(error) = share_block(&read(path), counting) {
                    panic!("{path}: {error}");
                }
            }
        },
    );
    h.case("counts/a share counted another way fails", || {
        let all = |count: &str, case: &str| format!("fn main() {{\n{count}{case}    h.run()\n}}\n");
        let filtered = |count: &str, between: &str, prefix: &str| {
            format!(
                "{}fn main() {{\n{count}{between}{M2_SHARE_CASE}}}\n",
                is_m2_text(prefix)
            )
        };
        let len = "    let m2 = h.len();\n";
        let names = "    let m2 = h.names().filter(|name| is_m2(name)).count();\n";
        assert_eq!(share_block(&all(len, M2_SHARE_CASE), Counting::All), Ok(()));
        // A count set by hand (hir, m04), every case counted for diag (m05), and an
        // assertion that always holds (layout, m31).
        let by_hand = all("    let m2 = usize::MAX;\n", M2_SHARE_CASE);
        assert!(share_block(&by_hand, Counting::All).is_err());
        let every = filtered(len, "", "explain/");
        assert!(share_block(&every, Counting::Filtered("explain/")).is_err());
        let weak = M2_SHARE_CASE.replace("m2 >= M2_SHARE,", "m2 >= M2_SHARE || m2 > 0,");
        assert!(share_block(&all(len, &weak), Counting::All).is_err());
        assert_eq!(
            share_block(
                &filtered(names, "    let x = 1;\n", "explain/"),
                Counting::Filtered("explain/")
            ),
            Ok(())
        );
        // `m2` changed between its count and the case, `is_m2` counting another
        // milestone's codes, and a count that is not right before the case.
        let changed = filtered(names, "    let m2 = m2 + 9;\n", "explain/");
        assert!(share_block(&changed, Counting::Filtered("explain/")).is_err());
        let other = filtered(names, "", "explain/").replace("== Milestone::M2", "<= Milestone::M2");
        assert!(share_block(&other, Counting::Filtered("explain/")).is_err());
        let early = all(len, &format!("    let m2 = 0;\n{M2_SHARE_CASE}"));
        assert!(share_block(&early, Counting::All).is_err());
    });
    h.case("counts/a suite holds a share of no milestone twice", || {
        // The CLI suite holds shares of M1, M2 and M3: a fixture of an M2 or an M3
        // code must count for its own milestone alone, which its `is_m1` says. The
        // diag suite holds shares of M2 and M3, the pages of each one's codes, which
        // its `is_m2` and `is_m3` keep apart by `since`.
        let cli = read("crates/enrang-cli/tests/cli/main.rs");
        assert!(
            cli.contains("&& !is_m2(name)"),
            "the CLI's M1 count takes M2's fixtures"
        );
        assert!(
            cli.contains("&& !is_m3(name)"),
            "the CLI's M1 count takes M3's fixtures"
        );
        let diag = read("crates/enrang-diag/tests/diag/main.rs");
        for milestone in [Milestone::M2, Milestone::M3] {
            assert!(
                diag.contains(&is_text(milestone, "explain/")),
                "diag counts {milestone}'s pages by another rule"
            );
        }
    });
    let counts: &[(&str, Option<usize>)] = &[
        ("2,500 cases", Some(2_500)),
        ("2,500 more cases", Some(2_500)),
        ("4,000 more cases, half negative", Some(4_000)),
        ("300 corpus programs", Some(300)),
        ("Testkit self-tests", None),
        ("", None),
        ("2.500 cases", None),
    ];
    for (item, expected) in counts {
        let (item, expected) = (*item, *expected);
        h.case(format!("counts/the count of {item:?}"), move || {
            assert_eq!(leading_count(item), expected);
        });
    }
    let shares: &[(&str, Milestone, Option<usize>)] = &[
        (
            "pub const M1_SHARE: usize = 1_800;\n",
            Milestone::M1,
            Some(1_800),
        ),
        ("pub const M1_SHARE: usize = 7;", Milestone::M1, Some(7)),
        ("const M1_SHARE: usize = 7;", Milestone::M1, None),
        (
            "pub const M1_SHARE: usize = 1_000 + 800;",
            Milestone::M1,
            None,
        ),
        ("pub const M1_SHARE: usize = ;", Milestone::M1, None),
        (
            "pub const M2_SHARE: usize = 1_500;\n",
            Milestone::M2,
            Some(1_500),
        ),
        ("pub const M1_SHARE: usize = 1_500;\n", Milestone::M2, None),
        ("pub const M2_SHARE: usize = 1_500;\n", Milestone::M1, None),
    ];
    for (source, milestone, expected) in shares {
        let (source, milestone, expected) = (*source, *milestone, *expected);
        h.case(
            format!("counts/the {milestone} share of {source:?}"),
            move || {
                assert_eq!(declared_share(source, milestone), expected);
            },
        );
    }
    h.case("counts/each share case names its milestone", || {
        assert_eq!(
            share_case(Milestone::M2),
            "\"count/this suite holds its share of M2's cases\""
        );
        assert_eq!(share_assertion(Milestone::M2), "assert!(m2 >= M2_SHARE");
        assert_eq!(share_assertion(Milestone::M1), "assert!(m1 >= M1_SHARE");
        assert_eq!(
            share_case(Milestone::M3),
            "\"count/this suite holds its share of M3's cases\""
        );
        assert_eq!(share_assertion(Milestone::M3), "assert!(m3 >= M3_SHARE");
    });
}
