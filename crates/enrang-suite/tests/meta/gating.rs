//! `since` gating over the code registry (TESTING 18).
//!
//! A row at or below the current milestone needs a firing fixture and an explain
//! page with a transcript. A later row must not have a fixture that claims to pass.
//! A firing fixture is a golden transcript whose stderr opens with the code and
//! which a live run reproduces, so the evidence is the command line itself, not a
//! list someone keeps. The real registry and the fake ones go through one function.

use std::collections::{BTreeMap, BTreeSet};

use enrang_diag::{CURRENT_MILESTONE, Code, Milestone, explain};
use enrang_testkit::{FixtureStatus, GateReport, GateRow, Harness, gate};

use crate::support::{
    Golden, Ran, fired_codes, golden_args, parse_command, run_cli, stderr_of, transcripts,
};

/// A row of a registry, real or fake.
#[derive(Copy, Clone, Debug)]
pub struct Row<'a> {
    pub name: &'a str,
    pub since: Milestone,
}

/// Where a registry's evidence comes from.
pub struct Sources<'a> {
    pub goldens: &'a [Golden],
    /// The failing section of a code's explain page.
    pub page: &'a dyn Fn(&str) -> Option<String>,
    /// The command line, given its arguments.
    pub run: &'a dyn Fn(&[String]) -> Ran,
}

fn live_body(golden: &Golden, run: &dyn Fn(&[String]) -> Ran) -> Result<String, String> {
    golden_args(golden).map(|args| run(&args).body())
}

/// The best status of each code some transcript fires: passing if a live run
/// reproduces the transcript, failing if none does.
fn firing_fixtures(sources: &Sources<'_>) -> BTreeMap<String, FixtureStatus> {
    let mut fired = BTreeMap::new();
    for golden in sources.goldens {
        let live = live_body(golden, sources.run);
        let claimed = golden.text.split_once('\n').map(|(_, body)| body);
        let reproduced = matches!((&live, claimed), (Ok(live), Some(body)) if live == body);
        for code in fired_codes(stderr_of(&golden.text)) {
            let status = fired.entry(code).or_insert(FixtureStatus::Failing);
            if reproduced {
                *status = FixtureStatus::Passing;
            }
        }
    }
    fired
}

/// A page's evidence: its failing section must be a transcript of a real command
/// that fires the code, with exactly this stderr.
fn page_status(code: &str, sources: &Sources<'_>) -> FixtureStatus {
    let Some(failing) = (sources.page)(code) else {
        return FixtureStatus::Missing;
    };
    let (command, expected) = failing.split_once('\n').unwrap_or((&failing, ""));
    let Ok(args) = parse_command(command) else {
        return FixtureStatus::Failing;
    };
    let live = (sources.run)(&args);
    let fires = fired_codes(&live.stderr).contains(code);
    if fires && live.stderr.strip_suffix('\n') == Some(expected) {
        FixtureStatus::Passing
    } else {
        FixtureStatus::Failing
    }
}

/// Gates a registry. Each row has a `fires` line, and a reached row has a `page` line
/// too. A page may arrive early, so a later row's page claims nothing. A transcript
/// firing a code that no row has is an orphan.
pub fn gate_registry(rows: &[Row<'_>], sources: &Sources<'_>, current: Milestone) -> GateReport {
    let fired = firing_fixtures(sources);
    let mut lines: Vec<(String, Milestone, FixtureStatus)> = Vec::new();
    for row in rows {
        let status = fired
            .get(row.name)
            .copied()
            .unwrap_or(FixtureStatus::Missing);
        lines.push((format!("{} fires", row.name), row.since, status));
        if row.since <= current {
            let page = page_status(row.name, sources);
            lines.push((format!("{} page", row.name), row.since, page));
        }
    }
    let gate_rows: Vec<GateRow<'_, Milestone>> = lines
        .iter()
        .map(|(id, since, fixture)| GateRow {
            id,
            since: *since,
            fixture: *fixture,
        })
        .collect();
    let mut report = gate(&gate_rows, &current);
    let known: BTreeSet<&str> = rows.iter().map(|row| row.name).collect();
    report.orphans = fired
        .keys()
        .filter(|code| !known.contains(code.as_str()))
        .cloned()
        .collect();
    report
}

fn real_rows() -> Vec<Row<'static>> {
    Code::ALL
        .iter()
        .map(|code| Row {
            name: code.name(),
            since: code.since(),
        })
        .collect()
}

fn real_page(name: &str) -> Option<String> {
    Code::from_name(name)
        .and_then(explain)
        .map(|page| page.failing.to_owned())
}

fn real_report(goldens: &[Golden]) -> GateReport {
    let sources = Sources {
        goldens,
        page: &real_page,
        run: &run_cli,
    };
    gate_registry(&real_rows(), &sources, CURRENT_MILESTONE)
}

/// A fake command line: a table from a joined command to its stderr.
struct FakeCli(BTreeMap<&'static str, &'static str>);

impl FakeCli {
    fn run(&self, args: &[String]) -> Ran {
        let stderr = self.0.get(args.join(" ").as_str()).copied().unwrap_or("");
        Ran {
            stdout: String::new(),
            stderr: stderr.to_owned(),
            code: 2,
        }
    }
}

fn fake_golden(command: &str, stderr: &str) -> Golden {
    Golden {
        name: format!("{command}.txt"),
        text: format!("$ enrang {command}\n[exit 2]\n[stdout]\n[stderr]\n{stderr}"),
    }
}

fn fake_error(code: &str) -> String {
    format!("error[{code}]: fake\n")
}

fn fake_transcript(command: &str, code: &str) -> String {
    format!("$ enrang {command}\nerror[{code}]: fake")
}

/// A registry with one row of every kind that matters.
fn full_fake(current: Milestone) -> GateReport {
    let cli = FakeCli(BTreeMap::from([
        ("clean", "error[EN9001]: fake\n"),
        ("no-golden", "error[EN9002]: fake\n"),
        ("no-page", "error[EN9003]: fake\n"),
        ("drifted", "error[EN9004]: now different\n"),
        ("prose", "error[EN9005]: fake\n"),
        ("stale-page", "error[EN9006]: fake\n"),
        ("early", "error[EN9007]: fake\n"),
        ("page-only", "error[EN9009]: fake\n"),
        ("unregistered", "error[EN9999]: fake\n"),
    ]));
    let goldens = [
        fake_golden("clean", &fake_error("EN9001")),
        fake_golden("no-page", &fake_error("EN9003")),
        fake_golden("drifted", &fake_error("EN9004")),
        fake_golden("prose", &fake_error("EN9005")),
        fake_golden("stale-page", &fake_error("EN9006")),
        fake_golden("early", &fake_error("EN9007")),
        fake_golden("unregistered", &fake_error("EN9999")),
    ];
    let rows = [
        Row {
            name: "EN9001",
            since: Milestone::M0,
        },
        Row {
            name: "EN9002",
            since: Milestone::M0,
        },
        Row {
            name: "EN9003",
            since: Milestone::M0,
        },
        Row {
            name: "EN9004",
            since: Milestone::M0,
        },
        Row {
            name: "EN9005",
            since: Milestone::M0,
        },
        Row {
            name: "EN9006",
            since: Milestone::M0,
        },
        Row {
            name: "EN9007",
            since: Milestone::M1,
        },
        Row {
            name: "EN9008",
            since: Milestone::M1,
        },
        Row {
            name: "EN9009",
            since: Milestone::M2,
        },
    ];
    let page = |name: &str| match name {
        "EN9001" => Some(fake_transcript("clean", "EN9001")),
        "EN9002" => Some(fake_transcript("no-golden", "EN9002")),
        "EN9004" => Some("$ enrang drifted\nerror[EN9004]: now different".to_owned()),
        "EN9005" => Some("This page has prose where a transcript belongs.".to_owned()),
        "EN9006" => Some("$ enrang stale-page\nerror[EN9006]: an old message".to_owned()),
        "EN9007" => Some(fake_transcript("early", "EN9007")),
        "EN9008" => Some(fake_transcript("unwritten", "EN9008")),
        "EN9009" => Some(fake_transcript("page-only", "EN9009")),
        _ => None,
    };
    let sources = Sources {
        goldens: &goldens,
        page: &page,
        run: &|args| cli.run(args),
    };
    gate_registry(&rows, &sources, current)
}

pub fn register(h: &mut Harness) {
    h.case(
        "gating/the real registry passes at the current milestone",
        || {
            let report = real_report(&transcripts());
            assert!(report.is_clean(), "\n{report}");
        },
    );
    h.case(
        "gating/the real gate enforces what it should and no less",
        || {
            let report = real_report(&transcripts());
            let reached = Code::ALL.iter().filter(|code| code.reached()).count();
            assert!(reached >= 2, "only {reached} rows have reached");
            assert_eq!(report.enforced, 2 * reached, "a fires and a page line each");
            assert_eq!(report.deferred, Code::ALL.len() - reached);
            assert_eq!(report.current, format!("{CURRENT_MILESTONE:?}"));
        },
    );
    h.case(
        "gating/every reached row has a transcript that fires it",
        || {
            let goldens = transcripts();
            let mut fired: BTreeSet<String> = BTreeSet::new();
            for golden in &goldens {
                fired.extend(fired_codes(stderr_of(&golden.text)));
            }
            for code in Code::ALL.iter().filter(|code| code.reached()) {
                assert!(fired.contains(code.name()), "{code}");
            }
            for code in Code::ALL.iter().filter(|code| !code.reached()) {
                assert!(
                    !fired.contains(code.name()),
                    "{code} fires before its milestone"
                );
            }
        },
    );
    h.case(
        "gating/removing the transcripts of a reached row opens a gap",
        || {
            let without: Vec<Golden> = transcripts()
                .into_iter()
                .filter(|golden| !fired_codes(stderr_of(&golden.text)).contains("EN1301"))
                .collect();
            let report = real_report(&without);
            let gaps: Vec<&str> = report.gaps.iter().map(|gap| gap.id.as_str()).collect();
            assert_eq!(gaps, ["EN1301 fires"]);
            assert_eq!(report.gaps[0].fixture, FixtureStatus::Missing);
        },
    );
    h.case(
        "gating/a transcript of a later row is reported as stale",
        || {
            let mut goldens = transcripts();
            goldens.push(Golden {
                name: "invented.txt".to_owned(),
                text: "$ enrang --version\n[exit 0]\n[stdout]\n[stderr]\nerror[EN1303]: invented\n"
                    .to_owned(),
            });
            let report = real_report(&goldens);
            // The live run does not reproduce it, so it is failing rather than passing,
            // and a failing fixture of a later row claims nothing. The golden's own test
            // fails it. Reproduced, it is stale, as the fake registry shows.
            assert!(report.is_clean(), "{report}");

            let cli = FakeCli(BTreeMap::from([("target", "error[EN1303]: invented\n")]));
            let goldens = [fake_golden("target", "error[EN1303]: invented\n")];
            let page = |_: &str| None;
            let sources = Sources {
                goldens: &goldens,
                page: &page,
                run: &|args| cli.run(args),
            };
            let report = gate_registry(&real_rows(), &sources, CURRENT_MILESTONE);
            let stale: Vec<&str> = report.stale.iter().map(|row| row.id.as_str()).collect();
            assert_eq!(stale, ["EN1303 fires"]);
        },
    );
    h.case("gating/a fake registry with a gap and a stale row reports both", || {
        let cli = FakeCli(BTreeMap::from([("early", "error[EN9002]: fake\n")]));
        let goldens = [fake_golden("early", "error[EN9002]: fake\n")];
        let rows = [
            Row { name: "EN9001", since: Milestone::M0 },
            Row { name: "EN9002", since: Milestone::M1 },
        ];
        let page = |_: &str| None;
        let sources = Sources {
            goldens: &goldens,
            page: &page,
            run: &|args| cli.run(args),
        };
        let report = gate_registry(&rows, &sources, Milestone::M0);
        assert!(!report.is_clean());
        assert_eq!(
            report.to_string(),
            "gap: EN9001 fires has no fixture (since M0, current M0)\n\
             gap: EN9001 page has no fixture (since M0, current M0)\n\
             stale: EN9002 fires claims a passing fixture before its milestone (since M1, current M0)\n"
        );
        assert_eq!(report.enforced, 2);
        assert_eq!(report.deferred, 1);
    });
    h.case("gating/a fake registry reports each kind of row exactly", || {
        let report = full_fake(Milestone::M0);
        assert_eq!(
            report.to_string(),
            "gap: EN9002 fires has no fixture (since M0, current M0)\n\
             gap: EN9003 page has no fixture (since M0, current M0)\n\
             gap: EN9004 fires has a failing fixture (since M0, current M0)\n\
             gap: EN9005 page has a failing fixture (since M0, current M0)\n\
             gap: EN9006 page has a failing fixture (since M0, current M0)\n\
             stale: EN9007 fires claims a passing fixture before its milestone (since M1, current M0)\n\
             orphan: `covers: EN9999` names no row\n"
        );
    });
    h.case("gating/a fake registry's clean rows report nothing", || {
        let report = full_fake(Milestone::M0);
        let text = report.to_string();
        assert!(!text.contains("EN9001"), "{text}");
        assert!(!text.contains("EN9008"), "{text}");
        assert!(!text.contains("EN9009"), "{text}");
    });
    h.case(
        "gating/bumping the milestone turns a later row into a gap",
        || {
            let report = full_fake(Milestone::M1);
            let text = report.to_string();
            assert!(!text.contains("stale: EN9007"), "{text}");
            assert!(!text.contains("EN9007 fires"), "{text}");
            assert!(
                text.contains("gap: EN9008 fires has no fixture (since M1, current M1)"),
                "{text}"
            );
            assert!(
                text.contains("gap: EN9008 page has a failing fixture"),
                "{text}"
            );
        },
    );
    h.case("gating/a clean fake registry passes", || {
        let cli = FakeCli(BTreeMap::from([("clean", "error[EN9001]: fake\n")]));
        let goldens = [fake_golden("clean", "error[EN9001]: fake\n")];
        let rows = [
            Row {
                name: "EN9001",
                since: Milestone::M0,
            },
            Row {
                name: "EN9002",
                since: Milestone::M1,
            },
        ];
        let page = |name: &str| (name == "EN9001").then(|| fake_transcript("clean", "EN9001"));
        let sources = Sources {
            goldens: &goldens,
            page: &page,
            run: &|args| cli.run(args),
        };
        let report = gate_registry(&rows, &sources, Milestone::M0);
        assert!(report.is_clean(), "{report}");
        assert_eq!(report.enforced, 2);
        assert_eq!(report.deferred, 1);
    });
    h.case("gating/a page must fire its own code", || {
        let cli = FakeCli(BTreeMap::from([("other", "error[EN9002]: fake\n")]));
        let page = |_: &str| Some("$ enrang other\nerror[EN9002]: fake".to_owned());
        let goldens: [Golden; 0] = [];
        let sources = Sources {
            goldens: &goldens,
            page: &page,
            run: &|args| cli.run(args),
        };
        assert_eq!(page_status("EN9001", &sources), FixtureStatus::Failing);
        assert_eq!(page_status("EN9002", &sources), FixtureStatus::Passing);
    });
    h.case(
        "gating/every reached page's transcript is the real output",
        || {
            for code in Code::ALL.iter().filter(|code| code.reached()) {
                let page = explain(*code).expect("a reached row has a page");
                let (command, expected) = page.failing.split_once('\n').expect("a transcript");
                let args = parse_command(command).expect("a command");
                let live = run_cli(&args);
                assert_eq!(live.stderr, format!("{expected}\n"), "{code}");
                assert_eq!(live.stdout, "", "{code}");
                assert_eq!(live.code, 2, "{code}");
            }
        },
    );
    h.case(
        "gating/the fixture kind of each reached row can run today",
        || {
            for code in Code::ALL.iter().filter(|code| code.reached()) {
                assert_eq!(code.fixture().to_string(), "Cli", "{code}");
            }
        },
    );
    let fired_rows: &[(&str, &[&str])] = &[
        ("error[EN1301]: head\n", &["EN1301"]),
        ("warning[EN0430]: head\n", &["EN0430"]),
        ("fail[T0001]: head\n", &["T0001"]),
        (
            "error[EN1301]: a\n\nerror[EN1302]: b\n",
            &["EN1301", "EN1302"],
        ),
        ("error: aborting due to 1 previous error\n", &[]),
        ("    error[EN1301]: indented\n", &[]),
        ("note: error[EN1301]: inside\n", &[]),
        ("error[EN1301] no colon\n", &[]),
        ("", &[]),
    ];
    for (stderr, expected) in fired_rows {
        let (stderr, expected) = (*stderr, *expected);
        h.case(format!("gating/fired codes of {stderr:?}"), move || {
            let fired: Vec<String> = fired_codes(stderr).into_iter().collect();
            assert_eq!(fired, expected);
        });
    }
    let command_rows: &[(&str, Option<&[&str]>)] = &[
        ("$ enrang", Some(&[])),
        ("$ enrang fmt", Some(&["fmt"])),
        ("$ enrang tsc main.en", Some(&["tsc", "main.en"])),
        ("$ enrang ''", Some(&[""])),
        ("$ enrang 'two words' x", Some(&["two words", "x"])),
        ("$ enrang $'a\\x1b[31mb'", Some(&["a\x1b[31mb"])),
        ("$ enrang 'unclosed", None),
        ("$ enrang $'\\q'", None),
        ("$ enrang $'\\x1'", None),
        ("$ other", None),
        ("enrang fmt", None),
        ("", None),
    ];
    for (line, expected) in command_rows {
        let (line, expected) = (*line, *expected);
        h.case(format!("gating/parses the command {line:?}"), move || {
            let parsed = parse_command(line).ok();
            let wanted =
                expected.map(|args| args.iter().map(|a| (*a).to_owned()).collect::<Vec<_>>());
            assert_eq!(parsed, wanted);
        });
    }
}
