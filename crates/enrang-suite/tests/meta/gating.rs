//! `since` gating over the code registry (TESTING 18).
//!
//! A row at or below the current milestone needs the evidence of its fixture kind. A
//! `Cli` row (and, until their runners exist, the other kinds) needs a firing
//! transcript and an explain page whose failing transcript is the real output. A
//! `Compile` row needs a firing fixture, a passing near-miss and an explain page whose
//! examples compile (M1 plan 0.2 and d.6):
//!
//! - a firing fixture, `<name>.fail.en` in the code's directory of `tests/compile/`,
//!   is one whose run through `enrang check` reports exactly the (line, code) pairs
//!   its `//~` anchors name;
//! - a near-miss, `<name>.pass.en` in the code's directory, passes `check`;
//! - the page's failing source, run through `check`, fires the code and no other,
//!   and its fixed source passes `check`.
//!
//! A firing transcript is a golden whose stderr opens a line with the code and which
//! a live run reproduces, in the place its directory says (`support::gate_transcripts`).
//! The evidence is always a command that runs, never a list someone keeps.
//!
//! A later row must not have evidence that passes: any passing fixture or transcript
//! makes it stale, whatever its kind. Rows of the milestone being built are the
//! exception: their work lands before the commit that closes that milestone, so they
//! are early, not stale. The real registry and the fake ones go through one function.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use enrang_diag::{CURRENT_MILESTONE, Code, FixtureKind, Milestone, explain};
use enrang_testkit::{
    FixtureStatus, GateReport, GateRow, Harness, compare, fixture_header, gate_building, reported,
};

use crate::support::{
    Fixture, Golden, PROJECT_TRANSCRIPTS, Place, Ran, being_built, fired_codes, fixtures,
    gate_transcripts, golden_args, goldens_in, milestone_in, parse_command, run_cached, run_cli_at,
    stderr_of,
};

/// The rows reached at `milestone` whose fixture kind the gate cannot run yet. It runs
/// `Compile` fixtures and `Cli` transcripts; a `Reload` or `TestRun` row needs a firing
/// scenario of its own kind (TESTING 18), which the bump that reaches the first such
/// row must teach the gate, and this list is what trips until then.
fn unrunnable(milestone: Milestone) -> Vec<Code> {
    Code::ALL
        .iter()
        .copied()
        .filter(|code| code.since() <= milestone)
        .filter(|code| !matches!(code.fixture(), FixtureKind::Cli | FixtureKind::Compile))
        .collect()
}

/// A row of a registry, real or fake.
#[derive(Copy, Clone, Debug)]
pub struct Row<'a> {
    pub name: &'a str,
    pub since: Milestone,
    pub fixture: FixtureKind,
}

/// An explain page's examples: source for a `Compile` code, transcripts otherwise.
#[derive(Clone, Debug)]
pub struct Page {
    pub failing: String,
    pub fixed: String,
}

/// The command line, in a place, given its arguments: the real one or a fake.
pub type Run<'a> = dyn Fn(&Place, &[String]) -> Ran + 'a;

/// Where a registry's evidence comes from.
pub struct Sources<'a> {
    /// Transcripts, each with the place it runs in.
    pub goldens: &'a [(Golden, Place)],
    /// The anchored compile fixtures.
    pub fixtures: &'a [Fixture],
    /// A code's explain page.
    pub page: &'a dyn Fn(&str) -> Option<Page>,
    /// The command line, in a place, given its arguments.
    pub run: &'a Run<'a>,
}

/// The file an explain page's source is checked as: a module, not a test part.
const PAGE_FILE: &str = "page.en";

/// The line that opens each file of a page whose example needs several files, as an
/// import does: `// file: main.en`.
const FILE_MARK: &str = "// file: ";

fn live_body(golden: &Golden, place: &Place, sources: &Sources<'_>) -> Result<String, String> {
    golden_args(golden).map(|args| (sources.run)(place, &args).body())
}

/// The best status of each code some transcript fires: passing if a live run
/// reproduces the transcript, failing if none does.
fn firing_transcripts(sources: &Sources<'_>) -> BTreeMap<String, FixtureStatus> {
    let mut fired = BTreeMap::new();
    for (golden, place) in sources.goldens {
        let live = live_body(golden, place, sources);
        let claimed = golden.text.split_once('\n').map(|(_, body)| body);
        let reproduced = matches!((&live, claimed), (Ok(live), Some(body)) if live == body);
        let status = if reproduced {
            FixtureStatus::Passing
        } else {
            FixtureStatus::Failing
        };
        for code in fired_codes(stderr_of(&golden.text)) {
            let best = fired.entry(code).or_insert(FixtureStatus::Failing);
            *best = best.best(status);
        }
    }
    fired
}

/// `enrang check` on a fixture, from the workspace root, as the CLI fixture runner
/// runs it: `check --target=<name> <path>` when the fixture's first line is
/// `//! target: <name>`, `check <path>` when it names no target, and nothing at all
/// when that header is broken, so such a fixture never passes.
pub fn check_fixture(fixture: &Fixture, run: &Run<'_>) -> Option<Ran> {
    let args = fixture.check_args()?;
    Some(run(&Place::Root, &args))
}

/// Whether a firing fixture's run reports exactly what its anchors name, exits 1 if
/// it reported an error and 0 if not, and prints nothing on stdout.
pub fn fixture_fires(fixture: &Fixture, run: &Run<'_>) -> bool {
    let Ok(anchors) = &fixture.anchors else {
        return false;
    };
    if anchors.is_empty() {
        return false;
    }
    let Some(ran) = check_fixture(fixture, run) else {
        return false;
    };
    let status = i32::from(ran.stderr.lines().any(|line| line.starts_with("error[")));
    ran.stdout.is_empty() && ran.code == status && compare(anchors, &reported(&ran.stderr)).is_ok()
}

/// Whether a near-miss has no anchor and passes `check` with nothing on either
/// stream.
pub fn near_miss_passes(fixture: &Fixture, run: &Run<'_>) -> bool {
    let unanchored = matches!(&fixture.anchors, Ok(anchors) if anchors.is_empty());
    unanchored
        && check_fixture(fixture, run)
            .is_some_and(|ran| (ran.code, ran.stdout.as_str(), ran.stderr.as_str()) == (0, "", ""))
}

/// Whether a fixture does what its kind says: a firing fixture fires as anchored,
/// a near-miss passes.
pub fn fixture_status(fixture: &Fixture, run: &Run<'_>) -> FixtureStatus {
    let passes = if fixture.near_miss {
        near_miss_passes(fixture, run)
    } else {
        fixture_fires(fixture, run)
    };
    if passes {
        FixtureStatus::Passing
    } else {
        FixtureStatus::Failing
    }
}

/// The best status of each code the firing fixtures anchor. A fixture whose anchors
/// cannot be read counts as failing for the code of its directory.
fn firing_fixtures(sources: &Sources<'_>) -> BTreeMap<String, FixtureStatus> {
    let mut fired = BTreeMap::new();
    for fixture in sources.fixtures.iter().filter(|fixture| !fixture.near_miss) {
        let status = if fixture_fires(fixture, sources.run) {
            FixtureStatus::Passing
        } else {
            FixtureStatus::Failing
        };
        let codes: BTreeSet<String> = match &fixture.anchors {
            Ok(anchors) if !anchors.is_empty() => {
                anchors.iter().map(|anchor| anchor.code.clone()).collect()
            }
            _ => BTreeSet::from([fixture.code.clone()]),
        };
        for code in codes {
            let best = fired.entry(code).or_insert(FixtureStatus::Failing);
            *best = best.best(status);
        }
    }
    fired
}

/// The best status of each directory's near-misses: passing if one has no anchor and
/// passes `check` with nothing on either stream.
fn near_misses(sources: &Sources<'_>) -> BTreeMap<String, FixtureStatus> {
    let mut found = BTreeMap::new();
    for fixture in sources.fixtures.iter().filter(|fixture| fixture.near_miss) {
        let status = fixture_status(fixture, sources.run);
        let best = found
            .entry(fixture.code.clone())
            .or_insert(FixtureStatus::Failing);
        *best = best.best(status);
    }
    found
}

/// The bytes of the file a page's source stands for: its text and a final newline.
/// EN0001's failing example is printed as the text it was meant to be, and its file
/// holds that text in Latin-1, as the syntax suite's page test reads it.
pub fn page_source(code: &str, text: &str, failing: bool) -> Vec<u8> {
    let text = format!("{text}\n");
    if failing && code == "EN0001" {
        text.chars()
            .map(|c| u8::try_from(u32::from(c)).unwrap_or(b'?'))
            .collect()
    } else {
        text.into_bytes()
    }
}

/// The files a page's source stands for, the one `check` runs on first. A source whose
/// first line is `// file: <name>` holds several files, each opened by such a line, as
/// an example of an import needs; any other source is `page.en` alone.
pub fn page_files(code: &str, text: &str, failing: bool) -> Vec<(String, Vec<u8>)> {
    if !text.starts_with(FILE_MARK) {
        return vec![(PAGE_FILE.to_owned(), page_source(code, text, failing))];
    }
    let mut files: Vec<(String, String)> = Vec::new();
    for line in text.lines() {
        if let Some(name) = line.strip_prefix(FILE_MARK) {
            files.push((name.to_owned(), String::new()));
        } else if let Some((_, body)) = files.last_mut() {
            body.push_str(line);
            body.push('\n');
        }
    }
    files
        .into_iter()
        .map(|(name, body)| (name, format!("{}\n", body.trim_matches('\n')).into_bytes()))
        .collect()
}

/// `enrang check` on a page's source, in a directory of its own files, run on the first
/// of them as its header asks, as a compile fixture's is: for the target it names,
/// `//! target: <name>` (M2 plan g.4: an example of a rule only one target has, such
/// as an `@interrupt` handler's, runs there), and as a library module for
/// `//! library` (G50: EN0439's rule exists only in library code). `None` when that
/// header is broken.
fn check_page(code: &str, text: &str, failing: bool, sources: &Sources<'_>) -> Option<Ran> {
    let files = page_files(code, text, failing);
    let header = fixture_header(&String::from_utf8_lossy(&files[0].1)).ok()?;
    let mut args = vec!["check".to_owned()];
    args.extend(header.check_flags());
    args.push(files[0].0.clone());
    Some((sources.run)(&Place::Files(files), &args))
}

/// A page's evidence. For a `Compile` row its failing source must fire the code and
/// nothing else, with an empty stdout, exiting 1 for an error and 0 for a warning, as
/// a firing fixture does, and its fixed source must pass `check`. For any other row its
/// failing section must be a transcript of a real command, run in a fresh project,
/// that fires the code with exactly this stderr.
fn page_status(row: &Row<'_>, sources: &Sources<'_>) -> FixtureStatus {
    let Some(page) = (sources.page)(row.name) else {
        return FixtureStatus::Missing;
    };
    let passing = if row.fixture == FixtureKind::Compile {
        let (Some(failing), Some(fixed)) = (
            check_page(row.name, &page.failing, true, sources),
            check_page(row.name, &page.fixed, false, sources),
        ) else {
            return FixtureStatus::Failing;
        };
        // A warning fires in a program that compiles (TESTING 7, 18), so `check` exits
        // 0 on its page, and 1 on an error's.
        let errors = failing
            .stderr
            .lines()
            .any(|line| line.starts_with("error["));
        let fires = failing.code == i32::from(errors)
            && failing.stdout.is_empty()
            && fired_codes(&failing.stderr) == BTreeSet::from([row.name.to_owned()]);
        let compiles = (fixed.code, fixed.stdout.as_str(), fixed.stderr.as_str()) == (0, "", "");
        fires && compiles
    } else {
        let (command, expected) = page.failing.split_once('\n').unwrap_or((&page.failing, ""));
        let Ok(args) = parse_command(command) else {
            return FixtureStatus::Failing;
        };
        let live = (sources.run)(&Place::Initialised, &args);
        fired_codes(&live.stderr).contains(row.name)
            && live.stderr.strip_suffix('\n') == Some(expected)
    };
    if passing {
        FixtureStatus::Passing
    } else {
        FixtureStatus::Failing
    }
}

/// Gates a registry. Each row has a `fires` line; a reached row has a `page` line,
/// and a reached `Compile` row a `near-miss` line, too. A reached row's `fires` line
/// takes only the evidence of its kind; a later row's takes any evidence, since any
/// of it claims the code fires. A page or a near-miss may arrive early, so a later
/// row's claims nothing. A transcript or fixture firing a code that no row has, or a
/// fixture directory named after one, is an orphan.
pub fn gate_registry(rows: &[Row<'_>], sources: &Sources<'_>, current: Milestone) -> GateReport {
    let transcripts = firing_transcripts(sources);
    let anchored = firing_fixtures(sources);
    let near = near_misses(sources);
    let status_in = |map: &BTreeMap<String, FixtureStatus>, name: &str| {
        map.get(name).copied().unwrap_or(FixtureStatus::Missing)
    };
    let mut lines: Vec<(String, Milestone, FixtureStatus)> = Vec::new();
    for row in rows {
        let (own, other) = if row.fixture == FixtureKind::Compile {
            (
                status_in(&anchored, row.name),
                status_in(&transcripts, row.name),
            )
        } else {
            (
                status_in(&transcripts, row.name),
                status_in(&anchored, row.name),
            )
        };
        let reached = row.since <= current;
        let fires = if reached { own } else { own.best(other) };
        lines.push((format!("{} fires", row.name), row.since, fires));
        if reached {
            if row.fixture == FixtureKind::Compile {
                let near_miss = status_in(&near, row.name);
                lines.push((format!("{} near-miss", row.name), row.since, near_miss));
            }
            let page = page_status(row, sources);
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
    let mut report = gate_building(&gate_rows, &current, &being_built(current));
    let known: BTreeSet<&str> = rows.iter().map(|row| row.name).collect();
    let claimed: BTreeSet<&String> = transcripts
        .keys()
        .chain(anchored.keys())
        .chain(near.keys())
        .chain(sources.fixtures.iter().map(|fixture| &fixture.code))
        .collect();
    report.orphans = claimed
        .into_iter()
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
            fixture: code.fixture(),
        })
        .collect()
}

fn real_page(name: &str) -> Option<Page> {
    Code::from_name(name).and_then(explain).map(|page| Page {
        failing: page.failing.to_owned(),
        fixed: page.fixed.to_owned(),
    })
}

/// The real registry over the real evidence, at `milestone`.
pub fn real_report_at(goldens: &[(Golden, Place)], milestone: Milestone) -> GateReport {
    let fixtures = fixtures();
    let sources = Sources {
        goldens,
        fixtures: &fixtures,
        page: &real_page,
        run: &run_cached,
    };
    gate_registry(&real_rows(), &sources, milestone)
}

fn real_report(goldens: &[(Golden, Place)]) -> GateReport {
    real_report_at(goldens, CURRENT_MILESTONE)
}

/// How many gate lines a registry has at `milestone`: a `fires` line each, a `page`
/// line for each reached row and a `near-miss` line for each reached `Compile` row.
fn enforced_lines(milestone: Milestone) -> usize {
    Code::ALL
        .iter()
        .filter(|code| code.since() <= milestone)
        .map(|code| match code.fixture() {
            FixtureKind::Compile => 3,
            _ => 2,
        })
        .sum()
}

/// A fake command line: a table from a joined command, or from the text of the one
/// file of a directory it runs in, to its stderr. A `check` exits 1 when it printed
/// an error and 0 when not; any other command exits 2, as the fake transcripts say.
/// A key may instead be given its own exit status and stdout, for a run that breaks
/// those rules.
pub struct FakeCli {
    stderr: BTreeMap<String, String>,
    broken: BTreeMap<String, (i32, String)>,
}

impl FakeCli {
    pub fn new<'a>(table: impl IntoIterator<Item = (&'a str, &'a str)>) -> FakeCli {
        FakeCli {
            stderr: table
                .into_iter()
                .map(|(key, stderr)| (key.to_owned(), stderr.to_owned()))
                .collect(),
            broken: BTreeMap::new(),
        }
    }

    /// The run of `key` exits `code` and prints `stdout`, whatever its stderr.
    pub fn breaking(mut self, key: &str, code: i32, stdout: &str) -> FakeCli {
        self.broken
            .insert(key.to_owned(), (code, stdout.to_owned()));
        self
    }

    pub fn run(&self, place: &Place, args: &[String]) -> Ran {
        let key = match place {
            Place::Files(files) => String::from_utf8_lossy(&files[0].1).trim_end().to_owned(),
            _ => args.join(" "),
        };
        let stderr = self.stderr.get(&key).cloned().unwrap_or_default();
        if let Some((code, stdout)) = self.broken.get(&key) {
            return Ran {
                stdout: stdout.clone(),
                stderr,
                code: *code,
            };
        }
        let checking =
            matches!(place, Place::Files(_)) || args.first().is_some_and(|a| a == "check");
        let code = if !checking {
            2
        } else {
            i32::from(stderr.contains("error["))
        };
        Ran {
            stdout: String::new(),
            stderr,
            code,
        }
    }
}

fn fake_golden(command: &str, stderr: &str) -> (Golden, Place) {
    let golden = Golden {
        name: format!("{command}.txt"),
        text: format!("$ enrang {command}\n[exit 2]\n[stdout]\n[stderr]\n{stderr}"),
    };
    (golden, Place::Suite)
}

fn fake_error(code: &str) -> String {
    format!("error[{code}]: fake\n")
}

fn fake_transcript(command: &str, code: &str) -> Page {
    Page {
        failing: format!("$ enrang {command}\nerror[{code}]: fake"),
        fixed: String::new(),
    }
}

fn fake_row(name: &'static str, since: Milestone) -> Row<'static> {
    Row {
        name,
        since,
        fixture: FixtureKind::Cli,
    }
}

fn fake_compile_row(name: &'static str, since: Milestone) -> Row<'static> {
    Row {
        name,
        since,
        fixture: FixtureKind::Compile,
    }
}

/// A fake fixture, with its anchors read from `text`.
pub fn fake_fixture(path: &str, text: &str) -> Fixture {
    let name = path.trim_start_matches("tests/compile/");
    Fixture {
        path: path.to_owned(),
        code: name.split('/').next().unwrap_or("").to_owned(),
        near_miss: path.ends_with(".pass.en"),
        anchors: enrang_testkit::anchors(text),
        target: enrang_testkit::fixture_header(text),
    }
}

/// A registry with one row of every kind of transcript evidence that matters.
fn full_fake(current: Milestone) -> GateReport {
    let cli = FakeCli::new([
        ("clean", "error[EN9001]: fake\n"),
        ("no-golden", "error[EN9002]: fake\n"),
        ("no-page", "error[EN9003]: fake\n"),
        ("drifted", "error[EN9004]: now different\n"),
        ("prose", "error[EN9005]: fake\n"),
        ("stale-page", "error[EN9006]: fake\n"),
        ("later", "error[EN9007]: fake\n"),
        ("page-only", "error[EN9009]: fake\n"),
        ("next", "error[EN9010]: fake\n"),
        ("unregistered", "error[EN9999]: fake\n"),
    ]);
    let goldens = [
        fake_golden("clean", &fake_error("EN9001")),
        fake_golden("no-page", &fake_error("EN9003")),
        fake_golden("drifted", &fake_error("EN9004")),
        fake_golden("prose", &fake_error("EN9005")),
        fake_golden("stale-page", &fake_error("EN9006")),
        fake_golden("later", &fake_error("EN9007")),
        fake_golden("next", &fake_error("EN9010")),
        fake_golden("unregistered", &fake_error("EN9999")),
    ];
    let rows = [
        fake_row("EN9001", Milestone::M0),
        fake_row("EN9002", Milestone::M0),
        fake_row("EN9003", Milestone::M0),
        fake_row("EN9004", Milestone::M0),
        fake_row("EN9005", Milestone::M0),
        fake_row("EN9006", Milestone::M0),
        fake_row("EN9007", Milestone::M2),
        fake_row("EN9008", Milestone::M1),
        fake_row("EN9009", Milestone::M2),
        fake_row("EN9010", Milestone::M1),
    ];
    let page = |name: &str| match name {
        "EN9001" => Some(fake_transcript("clean", "EN9001")),
        "EN9002" => Some(fake_transcript("no-golden", "EN9002")),
        "EN9004" => Some(Page {
            failing: "$ enrang drifted\nerror[EN9004]: now different".to_owned(),
            fixed: String::new(),
        }),
        "EN9005" => Some(Page {
            failing: "This page has prose where a transcript belongs.".to_owned(),
            fixed: String::new(),
        }),
        "EN9006" => Some(Page {
            failing: "$ enrang stale-page\nerror[EN9006]: an old message".to_owned(),
            fixed: String::new(),
        }),
        "EN9007" => Some(fake_transcript("later", "EN9007")),
        "EN9008" => Some(fake_transcript("unwritten", "EN9008")),
        "EN9009" => Some(fake_transcript("page-only", "EN9009")),
        "EN9010" => Some(fake_transcript("next", "EN9010")),
        _ => None,
    };
    let sources = Sources {
        goldens: &goldens,
        fixtures: &[],
        page: &page,
        run: &|place, args| cli.run(place, args),
    };
    gate_registry(&rows, &sources, current)
}

/// A registry of `Compile` rows, with every kind of fixture evidence that matters.
fn compile_fake(current: Milestone) -> GateReport {
    let cli = FakeCli::new([
        (
            "check tests/compile/EN9101/fires.fail.en",
            "error[EN9101]: fake\n --> tests/compile/EN9101/fires.fail.en:1:1\n",
        ),
        ("check tests/compile/EN9101/near.pass.en", ""),
        (
            "check tests/compile/EN9102/wrong_line.fail.en",
            "error[EN9102]: fake\n --> tests/compile/EN9102/wrong_line.fail.en:2:1\n",
        ),
        (
            "check tests/compile/EN9102/noisy.pass.en",
            "error[EN9102]: fake\n --> tests/compile/EN9102/noisy.pass.en:1:1\n",
        ),
        (
            "check tests/compile/EN9103/fires.fail.en",
            "error[EN9103]: fake\n --> tests/compile/EN9103/fires.fail.en:1:1\n",
        ),
        (
            "check tests/compile/EN9104/fires.fail.en",
            "error[EN9104]: fake\n --> tests/compile/EN9104/fires.fail.en:1:1\n",
        ),
        (
            "check tests/compile/EN9105/also.fail.en",
            "error[EN9105]: fake\n --> tests/compile/EN9105/also.fail.en:1:1\n\nerror[EN9106]: fake\n --> tests/compile/EN9105/also.fail.en:1:5\n",
        ),
        (
            "check tests/compile/EN9109/fires.fail.en",
            "error[EN9109]: fake\n --> tests/compile/EN9109/fires.fail.en:1:1\n",
        ),
        ("later-compile", "error[EN9108]: fake\n"),
        ("bad 9101", "error[EN9101]: fake\n --> page.en:1:1\n"),
        ("bad 9102", "error[EN9102]: fake\n --> page.en:1:1\n"),
        ("good 9102", "error[EN9102]: fake\n --> page.en:1:1\n"),
        (
            "bad 9105",
            "error[EN9105]: fake\n --> page.en:1:1\n\nerror[EN9106]: fake\n --> page.en:1:3\n",
        ),
    ]);
    let fixtures = [
        fake_fixture("tests/compile/EN9101/fires.fail.en", "x //~ EN9101\n"),
        fake_fixture("tests/compile/EN9101/near.pass.en", "y\n"),
        fake_fixture("tests/compile/EN9102/wrong_line.fail.en", "x //~ EN9102\n"),
        fake_fixture("tests/compile/EN9102/noisy.pass.en", "y\n"),
        fake_fixture("tests/compile/EN9103/fires.fail.en", "x //~ EN9103\n"),
        fake_fixture("tests/compile/EN9104/fires.fail.en", "x //~ EN9104\n"),
        fake_fixture(
            "tests/compile/EN9105/also.fail.en",
            "x //~ EN9105 //~ EN9106\n",
        ),
        fake_fixture("tests/compile/EN9105/near.pass.en", "y\n"),
        fake_fixture("tests/compile/EN9107/bad.fail.en", "x //~ en9107\n"),
        fake_fixture("tests/compile/EN9998/fires.fail.en", "x //~ EN9998\n"),
        fake_fixture("tests/compile/EN9109/fires.fail.en", "x //~ EN9109\n"),
    ];
    let rows = [
        fake_compile_row("EN9101", Milestone::M0),
        fake_compile_row("EN9102", Milestone::M0),
        fake_compile_row("EN9103", Milestone::M1),
        fake_compile_row("EN9104", Milestone::M2),
        fake_compile_row("EN9105", Milestone::M0),
        fake_compile_row("EN9106", Milestone::M0),
        fake_compile_row("EN9107", Milestone::M0),
        fake_compile_row("EN9108", Milestone::M2),
        fake_row("EN9109", Milestone::M2),
    ];
    let page = |name: &str| {
        let number = name.trim_start_matches("EN");
        Some(Page {
            failing: format!("bad {number}"),
            fixed: format!("good {number}"),
        })
    };
    // A later row is stale on any passing evidence, of its own kind or not.
    let goldens = [fake_golden("later-compile", &fake_error("EN9108"))];
    let sources = Sources {
        goldens: &goldens,
        fixtures: &fixtures,
        page: &page,
        run: &|place, args| cli.run(place, args),
    };
    gate_registry(&rows, &sources, current)
}

/// A registry whose evidence breaks each rule of how the gate counts it: a reached
/// row's `fires` line takes only evidence of its own kind, a firing fixture's run
/// must exit as its errors say and print nothing on stdout, and a near-miss must
/// have no anchor and print nothing on either stream. EN9201 keeps every rule, so
/// the fake fails only what breaks one.
fn rules_fake(current: Milestone) -> GateReport {
    let fires =
        |code: &str| format!("error[{code}]: fake\n --> tests/compile/{code}/fires.fail.en:1:1\n");
    let page = |code: &str| format!("error[{code}]: fake\n --> page.en:1:1\n");
    let mut table: Vec<(String, String)> = Vec::new();
    for code in ["EN9201", "EN9202", "EN9204", "EN9205", "EN9206", "EN9207"] {
        let number = code.trim_start_matches("EN");
        table.push((format!("bad {number}"), page(code)));
        if code != "EN9202" {
            table.push((
                format!("check tests/compile/{code}/fires.fail.en"),
                fires(code),
            ));
        }
    }
    table.push(("by-transcript".to_owned(), fake_error("EN9202")));
    table.push((
        "check tests/compile/EN9203/fires.fail.en".to_owned(),
        fires("EN9203"),
    ));
    table.push(("cli-page".to_owned(), fake_error("EN9203")));
    table.push((
        "check tests/compile/EN9207/near.pass.en".to_owned(),
        "warning[EN9207]: fake\n --> tests/compile/EN9207/near.pass.en:1:1\n".to_owned(),
    ));
    let cli = FakeCli::new(
        table
            .iter()
            .map(|(key, stderr)| (key.as_str(), stderr.as_str())),
    )
    .breaking("check tests/compile/EN9204/fires.fail.en", 0, "")
    .breaking("check tests/compile/EN9205/fires.fail.en", 1, "noise\n");
    let mut fixtures = Vec::new();
    for code in ["EN9201", "EN9203", "EN9204", "EN9205", "EN9206", "EN9207"] {
        fixtures.push(fake_fixture(
            &format!("tests/compile/{code}/fires.fail.en"),
            &format!("x //~ {code}\n"),
        ));
    }
    for code in ["EN9201", "EN9202", "EN9204", "EN9205", "EN9207"] {
        fixtures.push(fake_fixture(
            &format!("tests/compile/{code}/near.pass.en"),
            "y\n",
        ));
    }
    fixtures.push(fake_fixture(
        "tests/compile/EN9206/near.pass.en",
        "y //~ EN9206\n",
    ));
    let rows = [
        fake_compile_row("EN9201", Milestone::M0),
        fake_compile_row("EN9202", Milestone::M0),
        fake_row("EN9203", Milestone::M0),
        fake_compile_row("EN9204", Milestone::M0),
        fake_compile_row("EN9205", Milestone::M0),
        fake_compile_row("EN9206", Milestone::M0),
        fake_compile_row("EN9207", Milestone::M0),
    ];
    let page = |name: &str| {
        if name == "EN9203" {
            return Some(fake_transcript("cli-page", "EN9203"));
        }
        let number = name.trim_start_matches("EN");
        Some(Page {
            failing: format!("bad {number}"),
            fixed: format!("good {number}"),
        })
    };
    let goldens = [fake_golden("by-transcript", &fake_error("EN9202"))];
    let sources = Sources {
        goldens: &goldens,
        fixtures: &fixtures,
        page: &page,
        run: &|place, args| cli.run(place, args),
    };
    gate_registry(&rows, &sources, current)
}

pub fn register(h: &mut Harness) {
    h.case(
        "gating/the real registry passes at the current milestone",
        || {
            let report = real_report(&gate_transcripts());
            assert!(report.is_clean(), "\n{report}");
        },
    );
    h.case(
        "gating/the real registry passes at M1, so closing M1 needs only the bump",
        || {
            let report = real_report_at(&gate_transcripts(), Milestone::M1);
            assert!(report.gaps.is_empty(), "\n{report}");
            // M1 built M2, so evidence that lands early for a row due after M2, up to
            // the milestone being built now (M3 plan 0.5), reads as stale from M1.
            // That says nothing about closing M1; any other stale row does.
            let building = being_built(CURRENT_MILESTONE);
            let after_m1 = being_built(Milestone::M1);
            let stale: Vec<&str> = (report.stale.iter())
                .filter(|finding| {
                    !milestone_in(&finding.since)
                        .is_some_and(|since| since > after_m1 && since <= building)
                })
                .map(|finding| finding.id.as_str())
                .collect();
            assert_eq!(stale, Vec::<&str>::new(), "\n{report}");
            assert!(report.duplicates.is_empty(), "\n{report}");
            assert!(report.orphans.is_empty(), "\n{report}");
            assert_eq!(report.enforced, enforced_lines(Milestone::M1));
            let reached = Code::ALL
                .iter()
                .filter(|code| code.since() <= Milestone::M1)
                .count();
            assert_eq!(report.deferred, Code::ALL.len() - reached);
            assert_eq!(report.current, "M1");
        },
    );
    h.case(
        "gating/the real registry passes at M2: every M2 code has a fixture, a near-miss and a page",
        || {
            // TESTING 23's M2 row, "every `since(M2)` code": each of the 117 rows is a
            // `Compile` row, so each has three lines, all of them enforced at M2.
            let report = real_report_at(&gate_transcripts(), Milestone::M2);
            assert!(report.gaps.is_empty(), "\n{report}");
            assert!(report.is_clean(), "\n{report}");
            assert_eq!(report.enforced, enforced_lines(Milestone::M2));
            let m2: Vec<Code> = Code::ALL
                .iter()
                .copied()
                .filter(|code| code.since() == Milestone::M2)
                .collect();
            assert_eq!(m2.len(), 117);
            assert!(m2.iter().all(|code| code.fixture() == FixtureKind::Compile));
            assert_eq!(
                enforced_lines(Milestone::M2) - enforced_lines(Milestone::M1),
                3 * m2.len()
            );
            let reached = Code::ALL
                .iter()
                .filter(|code| code.since() <= Milestone::M2)
                .count();
            assert_eq!(report.deferred, Code::ALL.len() - reached);
            assert_eq!(report.current, "M2");
            assert!(Milestone::M2 <= CURRENT_MILESTONE, "M2's rows are enforced");
        },
    );
    h.case(
        "gating/removing the fixtures or the page of an M2 row opens a gap at M2",
        || {
            let goldens = gate_transcripts();
            let without: Vec<Fixture> = fixtures()
                .into_iter()
                .filter(|fixture| fixture.code != "EN0402")
                .collect();
            let page = |name: &str| (name != "EN0402").then(|| real_page(name)).flatten();
            for (fixtures, page, wanted) in [
                (
                    without.clone(),
                    &real_page as &dyn Fn(&str) -> Option<Page>,
                    vec!["EN0402 fires", "EN0402 near-miss"],
                ),
                (fixtures(), &page, vec!["EN0402 page"]),
            ] {
                let sources = Sources {
                    goldens: &goldens,
                    fixtures: &fixtures,
                    page,
                    run: &run_cached,
                };
                let report = gate_registry(&real_rows(), &sources, Milestone::M2);
                let gaps: Vec<&str> = report.gaps.iter().map(|gap| gap.id.as_str()).collect();
                assert_eq!(gaps, wanted);
                // Before the bump the same loss was no gap: M2's rows were early.
                let report = gate_registry(&real_rows(), &sources, Milestone::M1);
                assert!(report.gaps.is_empty(), "\n{report}");
            }
        },
    );
    h.case(
        "gating/the real registry passes at M3: every M3 code has a fixture, a near-miss and a page",
        || {
            // TESTING 23's M3 row, "every `since(M3)` code": each of the 29 rows is a
            // `Compile` row, so each has three lines, all of them enforced at M3.
            let report = real_report_at(&gate_transcripts(), Milestone::M3);
            assert!(report.gaps.is_empty(), "\n{report}");
            assert!(report.is_clean(), "\n{report}");
            assert_eq!(report.enforced, enforced_lines(Milestone::M3));
            let m3: Vec<Code> = Code::ALL
                .iter()
                .copied()
                .filter(|code| code.since() == Milestone::M3)
                .collect();
            assert_eq!(m3.len(), 29);
            assert!(m3.iter().all(|code| code.fixture() == FixtureKind::Compile));
            assert_eq!(
                enforced_lines(Milestone::M3) - enforced_lines(Milestone::M2),
                3 * m3.len()
            );
            let reached = Code::ALL
                .iter()
                .filter(|code| code.since() <= Milestone::M3)
                .count();
            assert_eq!(report.deferred, Code::ALL.len() - reached);
            assert_eq!(report.current, "M3");
            assert!(Milestone::M3 <= CURRENT_MILESTONE, "M3's rows are enforced");
        },
    );
    h.case(
        "gating/removing the fixtures or the page of an M3 row opens a gap at M3",
        || {
            // EN0618's fixtures are all in its own directory, so leaving that out
            // leaves nothing that fires it or misses it narrowly.
            let goldens = gate_transcripts();
            let without: Vec<Fixture> = fixtures()
                .into_iter()
                .filter(|fixture| fixture.code != "EN0618")
                .collect();
            assert!(without.iter().all(|fixture| {
                fixture
                    .anchors
                    .as_ref()
                    .map_or(true, |anchors| anchors.iter().all(|a| a.code != "EN0618"))
            }));
            let page = |name: &str| (name != "EN0618").then(|| real_page(name)).flatten();
            for (fixtures, page, wanted) in [
                (
                    without.clone(),
                    &real_page as &dyn Fn(&str) -> Option<Page>,
                    vec!["EN0618 fires", "EN0618 near-miss"],
                ),
                (fixtures(), &page, vec!["EN0618 page"]),
            ] {
                let sources = Sources {
                    goldens: &goldens,
                    fixtures: &fixtures,
                    page,
                    run: &run_cached,
                };
                let report = gate_registry(&real_rows(), &sources, Milestone::M3);
                let gaps: Vec<&str> = report.gaps.iter().map(|gap| gap.id.as_str()).collect();
                assert_eq!(gaps, wanted);
                // Before the bump the same loss was no gap: M3's rows were early.
                let report = gate_registry(&real_rows(), &sources, Milestone::M2);
                assert!(report.gaps.is_empty(), "\n{report}");
            }
        },
    );
    h.case(
        "gating/the real gate enforces what it should and no less",
        || {
            let report = real_report(&gate_transcripts());
            let reached = Code::ALL.iter().filter(|code| code.reached()).count();
            assert!(reached >= 2, "only {reached} rows have reached");
            assert_eq!(report.enforced, enforced_lines(CURRENT_MILESTONE));
            assert_eq!(report.deferred, Code::ALL.len() - reached);
            assert_eq!(report.current, format!("{CURRENT_MILESTONE:?}"));
            let next = being_built(CURRENT_MILESTONE);
            for row in &report.early {
                assert!(row.since == format!("{next:?}"), "{row:?}");
            }
        },
    );
    h.case(
        "gating/every reached row has firing evidence of its kind",
        || {
            let mut fired: BTreeSet<String> = BTreeSet::new();
            for (golden, _) in &gate_transcripts() {
                fired.extend(fired_codes(stderr_of(&golden.text)));
            }
            let mut anchored: BTreeSet<String> = BTreeSet::new();
            for fixture in fixtures() {
                if let Ok(anchors) = &fixture.anchors {
                    anchored.extend(anchors.iter().map(|anchor| anchor.code.clone()));
                }
            }
            for code in Code::ALL.iter().filter(|code| code.reached()) {
                let evidence = match code.fixture() {
                    FixtureKind::Compile => &anchored,
                    _ => &fired,
                };
                assert!(evidence.contains(code.name()), "{code}");
            }
        },
    );
    h.case(
        "gating/nothing fires a row after the milestone being built",
        || {
            let next = being_built(CURRENT_MILESTONE);
            let mut fired: BTreeSet<String> = BTreeSet::new();
            for (golden, _) in &gate_transcripts() {
                fired.extend(fired_codes(stderr_of(&golden.text)));
            }
            for golden in goldens_in(PROJECT_TRANSCRIPTS) {
                fired.extend(fired_codes(stderr_of(&golden.text)));
            }
            for fixture in fixtures() {
                if let Ok(anchors) = &fixture.anchors {
                    fired.extend(anchors.iter().map(|anchor| anchor.code.clone()));
                }
            }
            for code in Code::ALL.iter().filter(|code| code.since() > next) {
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
            let without: Vec<(Golden, Place)> = gate_transcripts()
                .into_iter()
                .filter(|(golden, _)| !fired_codes(stderr_of(&golden.text)).contains("EN1301"))
                .collect();
            let report = real_report(&without);
            let gaps: Vec<&str> = report.gaps.iter().map(|gap| gap.id.as_str()).collect();
            assert_eq!(gaps, ["EN1301 fires"]);
            assert_eq!(report.gaps[0].fixture, FixtureStatus::Missing);
        },
    );
    h.case(
        "gating/removing the fixtures of an M1 row opens a gap at M1",
        || {
            let fixtures: Vec<Fixture> = fixtures()
                .into_iter()
                .filter(|fixture| fixture.code != "EN0201")
                .collect();
            let goldens = gate_transcripts();
            let sources = Sources {
                goldens: &goldens,
                fixtures: &fixtures,
                page: &real_page,
                run: &run_cached,
            };
            let report = gate_registry(&real_rows(), &sources, Milestone::M1);
            let gaps: Vec<&str> = report.gaps.iter().map(|gap| gap.id.as_str()).collect();
            assert_eq!(gaps, ["EN0201 fires", "EN0201 near-miss"]);
        },
    );
    h.case(
        "gating/a transcript of a later row is reported as stale",
        || {
            let mut goldens = gate_transcripts();
            goldens.push((
                Golden {
                    name: "invented.txt".to_owned(),
                    text: "$ enrang --version\n[exit 0]\n[stdout]\n[stderr]\nerror[EN1306]: invented\n"
                        .to_owned(),
                },
                Place::Suite,
            ));
            let report = real_report(&goldens);
            // The live run does not reproduce it, so it is failing rather than passing,
            // and a failing fixture of a later row claims nothing. The golden's own test
            // fails it. Reproduced, it is stale, as the fake command line shows.
            assert!(report.is_clean(), "{report}");

            let next = being_built(CURRENT_MILESTONE);
            let later = Code::ALL
                .iter()
                .find(|code| code.fixture() == FixtureKind::Cli && code.since() > next)
                .expect("a command-line row after the milestone being built");
            let stderr = format!("error[{later}]: invented\n");
            let cli = FakeCli::new([("target", stderr.as_str())]);
            let goldens = [fake_golden("target", &stderr)];
            let page = |_: &str| None;
            let sources = Sources {
                goldens: &goldens,
                fixtures: &[],
                page: &page,
                run: &|place, args| cli.run(place, args),
            };
            let report = gate_registry(&real_rows(), &sources, CURRENT_MILESTONE);
            let stale: Vec<&str> = report.stale.iter().map(|row| row.id.as_str()).collect();
            assert_eq!(stale, [format!("{later} fires")]);
        },
    );
    h.case("gating/a fake registry with a gap and a stale row reports both", || {
        let cli = FakeCli::new([("early", "error[EN9002]: fake\n")]);
        let goldens = [fake_golden("early", "error[EN9002]: fake\n")];
        let rows = [fake_row("EN9001", Milestone::M0), fake_row("EN9002", Milestone::M2)];
        let page = |_: &str| None;
        let sources = Sources {
            goldens: &goldens,
            fixtures: &[],
            page: &page,
            run: &|place, args| cli.run(place, args),
        };
        let report = gate_registry(&rows, &sources, Milestone::M0);
        assert!(!report.is_clean());
        assert_eq!(
            report.to_string(),
            "gap: EN9001 fires has no fixture (since M0, current M0)\n\
             gap: EN9001 page has no fixture (since M0, current M0)\n\
             stale: EN9002 fires claims a passing fixture before its milestone (since M2, current M0)\n"
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
             stale: EN9007 fires claims a passing fixture before its milestone (since M2, current M0)\n\
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
        "gating/a row of the milestone being built may pass early",
        || {
            let report = full_fake(Milestone::M0);
            let early: Vec<&str> = report.early.iter().map(|row| row.id.as_str()).collect();
            assert_eq!(early, ["EN9010 fires"]);
            assert!(!report.to_string().contains("EN9010"));
        },
    );
    h.case(
        "gating/bumping the milestone turns a later row into a gap",
        || {
            let report = full_fake(Milestone::M1);
            let text = report.to_string();
            assert!(!text.contains("stale: EN9007"), "{text}");
            assert!(!text.contains("EN9007 fires"), "{text}");
            assert!(!text.contains("EN9010"), "{text}");
            assert!(
                text.contains("gap: EN9008 fires has no fixture (since M1, current M1)"),
                "{text}"
            );
            assert!(
                text.contains("gap: EN9008 page has a failing fixture"),
                "{text}"
            );
            let early: Vec<&str> = report.early.iter().map(|row| row.id.as_str()).collect();
            assert_eq!(early, ["EN9007 fires"]);
        },
    );
    h.case("gating/a clean fake registry passes", || {
        let cli = FakeCli::new([("clean", "error[EN9001]: fake\n")]);
        let goldens = [fake_golden("clean", "error[EN9001]: fake\n")];
        let rows = [
            fake_row("EN9001", Milestone::M0),
            fake_row("EN9002", Milestone::M1),
        ];
        let page = |name: &str| (name == "EN9001").then(|| fake_transcript("clean", "EN9001"));
        let sources = Sources {
            goldens: &goldens,
            fixtures: &[],
            page: &page,
            run: &|place, args| cli.run(place, args),
        };
        let report = gate_registry(&rows, &sources, Milestone::M0);
        assert!(report.is_clean(), "{report}");
        assert_eq!(report.enforced, 2);
        assert_eq!(report.deferred, 1);
    });
    h.case(
        "gating/a firing fixture exits 1 only for an error: a warning's exits 0",
        || {
            // EF-06's EN0828 and EN0314, EN0430, EN0453, EN0459, EN0503 are warnings:
            // their firing fixtures exit 0 with the warning on stderr.
            let path = "tests/compile/EN9430/w.fail.en";
            let fixture = fake_fixture(path, "x //~ EN9430\n");
            let stderr = format!("warning[EN9430]: fake\n --> {path}:1:1\n");
            let key = format!("check {path}");
            let quiet = FakeCli::new([(key.as_str(), stderr.as_str())]);
            assert!(fixture_fires(&fixture, &|place, args| quiet.run(place, args)));
            let loud = FakeCli::new([(key.as_str(), stderr.as_str())]).breaking(&key, 1, "");
            assert!(!fixture_fires(&fixture, &|place, args| loud.run(place, args)));
            // An error exits 1, and 0 is wrong for it.
            let path = "tests/compile/EN9401/e.fail.en";
            let fixture = fake_fixture(path, "x //~ EN9401\n");
            let stderr = format!("error[EN9401]: fake\n --> {path}:1:1\n");
            let key = format!("check {path}");
            let fires = FakeCli::new([(key.as_str(), stderr.as_str())]);
            assert!(fixture_fires(&fixture, &|place, args| fires.run(place, args)));
            let silent = FakeCli::new([(key.as_str(), stderr.as_str())]).breaking(&key, 0, "");
            assert!(!fixture_fires(&fixture, &|place, args| silent.run(place, args)));
        },
    );
    h.case("gating/a firing fixture with no anchor never fires", || {
        // A `.fail.en` that anchors nothing shows nothing, even when its run is clean.
        let path = "tests/compile/EN9401/u.fail.en";
        let fixture = fake_fixture(path, "x\n");
        assert_eq!(fixture.anchors, Ok(Vec::new()));
        let cli = FakeCli::new([(format!("check {path}").as_str(), "")]);
        assert!(!fixture_fires(&fixture, &|place, args| cli.run(place, args)));
        assert_eq!(
            fixture_status(&fixture, &|place, args| cli.run(place, args)),
            FixtureStatus::Failing
        );
    });
    h.case("gating/a page must fire its own code", || {
        let cli = FakeCli::new([("other", "error[EN9002]: fake\n")]);
        let page = |_: &str| {
            Some(Page {
                failing: "$ enrang other\nerror[EN9002]: fake".to_owned(),
                fixed: String::new(),
            })
        };
        let sources = Sources {
            goldens: &[],
            fixtures: &[],
            page: &page,
            run: &|place, args| cli.run(place, args),
        };
        let row = |name| fake_row(name, Milestone::M0);
        assert_eq!(
            page_status(&row("EN9001"), &sources),
            FixtureStatus::Failing
        );
        assert_eq!(
            page_status(&row("EN9002"), &sources),
            FixtureStatus::Passing
        );
    });
    h.case("gating/a fake registry of compile rows reports each kind of evidence", || {
        let report = compile_fake(Milestone::M0);
        assert_eq!(
            report.to_string(),
            "gap: EN9102 fires has a failing fixture (since M0, current M0)\n\
             gap: EN9102 near-miss has a failing fixture (since M0, current M0)\n\
             gap: EN9102 page has a failing fixture (since M0, current M0)\n\
             gap: EN9105 page has a failing fixture (since M0, current M0)\n\
             gap: EN9106 near-miss has no fixture (since M0, current M0)\n\
             gap: EN9106 page has a failing fixture (since M0, current M0)\n\
             gap: EN9107 fires has a failing fixture (since M0, current M0)\n\
             gap: EN9107 near-miss has no fixture (since M0, current M0)\n\
             gap: EN9107 page has a failing fixture (since M0, current M0)\n\
             stale: EN9104 fires claims a passing fixture before its milestone (since M2, current M0)\n\
             stale: EN9108 fires claims a passing fixture before its milestone (since M2, current M0)\n\
             stale: EN9109 fires claims a passing fixture before its milestone (since M2, current M0)\n\
             orphan: `covers: EN9998` names no row\n"
        );
        let early: Vec<&str> = report.early.iter().map(|row| row.id.as_str()).collect();
        assert_eq!(early, ["EN9103 fires"]);
        assert_eq!(report.enforced, 5 * 3);
        assert_eq!(report.deferred, 4);
    });
    h.case(
        "gating/evidence counts only as its kind and as a process should run",
        || {
            let report = rules_fake(Milestone::M0);
            assert_eq!(
                report.to_string(),
                "gap: EN9202 fires has no fixture (since M0, current M0)\n\
                 gap: EN9203 fires has no fixture (since M0, current M0)\n\
                 gap: EN9204 fires has a failing fixture (since M0, current M0)\n\
                 gap: EN9205 fires has a failing fixture (since M0, current M0)\n\
                 gap: EN9206 near-miss has a failing fixture (since M0, current M0)\n\
                 gap: EN9207 near-miss has a failing fixture (since M0, current M0)\n"
            );
            assert_eq!(report.enforced, 6 * 3 + 2);
        },
    );
    h.case(
        "gating/a fixture naming its target is checked for that target, as the CLI runs it",
        || {
            // The CLI fixture runner (`crates/enrang-cli/tests/cli/compile.rs`) runs
            // `check --target=<name> <path>` for a first line `//! target: <name>`, and
            // fails a fixture whose header is broken; the gate must count it alike.
            let dir = "tests/compile/EN9301";
            let owned = |args: &[&str]| args.iter().map(|a| (*a).to_owned()).collect::<Vec<_>>();
            let targeted = fake_fixture(
                &format!("{dir}/c17.fail.en"),
                "//! target: i386-none\nx //~ EN9301\n",
            );
            assert_eq!(
                targeted.check_args(),
                Some(owned(&[
                    "check",
                    "--target=i386-none",
                    "tests/compile/EN9301/c17.fail.en"
                ]))
            );
            let plain = fake_fixture(&format!("{dir}/plain.fail.en"), "x //~ EN9301\n");
            assert_eq!(
                plain.check_args(),
                Some(owned(&["check", "tests/compile/EN9301/plain.fail.en"]))
            );
            let near = fake_fixture(&format!("{dir}/c17.pass.en"), "//! target: i386-none\ny\n");
            // The header must be the first line and name a target.
            let late = fake_fixture(
                &format!("{dir}/late.fail.en"),
                "x //~ EN9301\n//! target: i386-none\n",
            );
            let empty = fake_fixture(
                &format!("{dir}/empty.fail.en"),
                "//! target:\nx //~ EN9301\n",
            );
            assert_eq!(late.check_args(), None);
            assert_eq!(empty.check_args(), None);
            // Fires only for its target: run for the host's, it reports nothing.
            let untargeted = fake_fixture(
                &format!("{dir}/untargeted.fail.en"),
                "//! target: i386-none\nx //~ EN9301\n",
            );
            let fires = |name: &str, line: usize| {
                format!("error[EN9301]: fake\n --> {dir}/{name}:{line}:1\n")
            };
            let table = [
                (
                    format!("check --target=i386-none {dir}/c17.fail.en"),
                    fires("c17.fail.en", 2),
                ),
                (format!("check {dir}/c17.fail.en"), String::new()),
                (
                    format!("check {dir}/plain.fail.en"),
                    fires("plain.fail.en", 1),
                ),
                (
                    format!("check --target=i386-none {dir}/c17.pass.en"),
                    String::new(),
                ),
                (
                    format!("check {dir}/late.fail.en"),
                    fires("late.fail.en", 1),
                ),
                (
                    format!("check --target=i386-none {dir}/late.fail.en"),
                    fires("late.fail.en", 1),
                ),
                (
                    format!("check {dir}/empty.fail.en"),
                    fires("empty.fail.en", 2),
                ),
                (
                    format!("check {dir}/untargeted.fail.en"),
                    fires("untargeted.fail.en", 2),
                ),
                (
                    "bad 9301".to_owned(),
                    "error[EN9301]: fake\n --> page.en:1:1\n".to_owned(),
                ),
            ];
            let cli = FakeCli::new(
                table
                    .iter()
                    .map(|(key, stderr)| (key.as_str(), stderr.as_str())),
            )
            // A run for the wrong target would print an error here.
            .breaking(&format!("check {dir}/c17.pass.en"), 1, "");
            let run = |place: &Place, args: &[String]| cli.run(place, args);
            assert_eq!(fixture_status(&targeted, &run), FixtureStatus::Passing);
            assert_eq!(fixture_status(&plain, &run), FixtureStatus::Passing);
            assert_eq!(fixture_status(&near, &run), FixtureStatus::Passing);
            assert_eq!(fixture_status(&late, &run), FixtureStatus::Failing);
            assert_eq!(fixture_status(&empty, &run), FixtureStatus::Failing);
            assert_eq!(fixture_status(&untargeted, &run), FixtureStatus::Failing);

            let page = |_: &str| {
                Some(Page {
                    failing: "bad 9301".to_owned(),
                    fixed: "good 9301".to_owned(),
                })
            };
            let gated = |fixtures: &[Fixture]| {
                let sources = Sources {
                    goldens: &[],
                    fixtures,
                    page: &page,
                    run: &run,
                };
                let row = fake_compile_row("EN9301", Milestone::M0);
                gate_registry(&[row], &sources, Milestone::M0).to_string()
            };
            assert_eq!(gated(&[targeted, near.clone()]), "");
            assert_eq!(
                gated(&[untargeted, late, empty, near]),
                "gap: EN9301 fires has a failing fixture (since M0, current M0)\n"
            );
        },
    );
    h.case("gating/later rows take evidence of any kind", || {
        // The same evidence at M0 for rows of M2: each `fires` line that any
        // passing evidence backs is stale, whatever its kind.
        let report = rules_fake(Milestone::M0);
        assert!(report.stale.is_empty(), "{report}");
        let fake = |name: &'static str| Row {
            name,
            since: Milestone::M2,
            fixture: if name == "EN9203" {
                FixtureKind::Cli
            } else {
                FixtureKind::Compile
            },
        };
        let cli = FakeCli::new([
            ("by-transcript", "error[EN9202]: fake\n"),
            (
                "check tests/compile/EN9203/fires.fail.en",
                "error[EN9203]: fake\n --> tests/compile/EN9203/fires.fail.en:1:1\n",
            ),
        ]);
        let goldens = [fake_golden("by-transcript", &fake_error("EN9202"))];
        let fixtures = [fake_fixture(
            "tests/compile/EN9203/fires.fail.en",
            "x //~ EN9203\n",
        )];
        let page = |_: &str| None;
        let sources = Sources {
            goldens: &goldens,
            fixtures: &fixtures,
            page: &page,
            run: &|place, args| cli.run(place, args),
        };
        let report = gate_registry(&[fake("EN9202"), fake("EN9203")], &sources, Milestone::M0);
        let stale: Vec<&str> = report.stale.iter().map(|row| row.id.as_str()).collect();
        assert_eq!(stale, ["EN9202 fires", "EN9203 fires"]);
    });
    h.case("gating/a compile row's page needs both examples to work", || {
        let cli = FakeCli::new([
            ("fires", "error[EN9101]: fake\n --> page.en:1:1\n"),
            ("fires too", "error[EN9101]: fake\n --> page.en:1:1\n"),
            (
                "fires more",
                "error[EN9101]: fake\n --> page.en:1:1\n\nerror[EN9102]: fake\n --> page.en:2:1\n",
            ),
            ("warns", "warning[EN9101]: fake\n --> page.en:1:1\n"),
            ("warns failing", "warning[EN9101]: fake\n --> page.en:1:1\n"),
        ]);
        let cli = cli.breaking("warns failing", 1, "");
        let row = fake_compile_row("EN9101", Milestone::M0);
        let status = |failing: &str, fixed: &str| {
            let page = |_: &str| {
                Some(Page {
                    failing: failing.to_owned(),
                    fixed: fixed.to_owned(),
                })
            };
            let sources = Sources {
                goldens: &[],
                fixtures: &[],
                page: &page,
                run: &|place, args| cli.run(place, args),
            };
            page_status(&row, &sources)
        };
        assert_eq!(status("fires", "passes"), FixtureStatus::Passing);
        assert_eq!(status("silent", "passes"), FixtureStatus::Failing);
        assert_eq!(status("fires more", "passes"), FixtureStatus::Failing);
        assert_eq!(status("fires", "fires too"), FixtureStatus::Failing);
        // A warning's page fires it in a program that compiles, exit status 0.
        assert_eq!(status("warns", "passes"), FixtureStatus::Passing);
        assert_eq!(status("warns failing", "passes"), FixtureStatus::Failing);
    });
    h.case(
        "gating/a page of several files runs `check` on the first, beside the rest",
        || {
            let failing = "// file: main.en\nimport { H } from \"./user\";\n\n// file: user.en\nprivate class H {}";
            assert_eq!(
                page_files("EN9101", failing, true),
                [
                    (
                        "main.en".to_owned(),
                        b"import { H } from \"./user\";\n".to_vec()
                    ),
                    ("user.en".to_owned(), b"private class H {}\n".to_vec()),
                ]
            );
            assert_eq!(
                page_files("EN9101", "x", false),
                [("page.en".to_owned(), b"x\n".to_vec())]
            );
            let seen = RefCell::new(Vec::new());
            let page = |_: &str| {
                Some(Page {
                    failing: failing.to_owned(),
                    fixed: "x".to_owned(),
                })
            };
            let run = |place: &Place, args: &[String]| {
                let Place::Files(files) = place else {
                    panic!("a page runs in a directory of its own files")
                };
                let names: Vec<&str> = files.iter().map(|(name, _)| name.as_str()).collect();
                seen.borrow_mut()
                    .push(format!("{} in {}", args.join(" "), names.join(" ")));
                let stderr = if names.len() == 2 {
                    "error[EN9101]: fake\n --> main.en:1:10\n"
                } else {
                    ""
                };
                Ran {
                    stdout: String::new(),
                    stderr: stderr.to_owned(),
                    code: i32::from(!stderr.is_empty()),
                }
            };
            let sources = Sources {
                goldens: &[],
                fixtures: &[],
                page: &page,
                run: &run,
            };
            let row = fake_compile_row("EN9101", Milestone::M0);
            assert_eq!(page_status(&row, &sources), FixtureStatus::Passing);
            assert_eq!(
                *seen.borrow(),
                ["check main.en in main.en user.en", "check page.en in page.en"]
            );
        },
    );
    h.case("gating/a warning's page fires it in a program that compiles", || {
        let warns = "warning[EN9101]: fake\n --> page.en:1:1\n";
        let cli = FakeCli::new([
            ("warns", warns),
            ("warns but exits 1", warns),
            ("warns with stdout", warns),
            (
                "warns and fails",
                "warning[EN9101]: fake\n --> page.en:1:1\n\nerror[EN9102]: fake\n --> page.en:2:1\n",
            ),
        ])
        .breaking("warns but exits 1", 1, "")
        .breaking("warns with stdout", 0, "noise\n");
        let row = fake_compile_row("EN9101", Milestone::M0);
        let status = |failing: &str| {
            let page = |_: &str| {
                Some(Page {
                    failing: failing.to_owned(),
                    fixed: "passes".to_owned(),
                })
            };
            let sources = Sources {
                goldens: &[],
                fixtures: &[],
                page: &page,
                run: &|place, args| cli.run(place, args),
            };
            page_status(&row, &sources)
        };
        assert_eq!(status("warns"), FixtureStatus::Passing);
        assert_eq!(status("warns but exits 1"), FixtureStatus::Failing);
        assert_eq!(status("warns with stdout"), FixtureStatus::Failing);
        assert_eq!(status("warns and fails"), FixtureStatus::Failing);
    });
    h.case(
        "gating/a compile page runs for the target its first line names, and a warning exits 0",
        || {
            let row = fake_compile_row("EN9101", Milestone::M0);
            // Fires only for `i386-none`, where a fixed example passes too; warns with
            // exit 0 on `warns`; anything else reports another code.
            let run = |place: &Place, args: &[String]| {
                let Place::Files(files) = place else {
                    panic!("a page runs alone in a directory");
                };
                let text = String::from_utf8_lossy(&files[0].1).into_owned();
                let freestanding = args.iter().any(|arg| arg == "--target=i386-none");
                let (stderr, code) = if text.contains("warns") {
                    ("warning[EN9101]: fake\n --> page.en:1:1\n", 0)
                } else if freestanding && text.contains("fires") {
                    ("error[EN9101]: fake\n --> page.en:2:1\n", 1)
                } else if freestanding && text.contains("passes") {
                    ("", 0)
                } else {
                    ("error[EN9102]: fake\n --> page.en:2:1\n", 1)
                };
                Ran {
                    stdout: String::new(),
                    stderr: stderr.to_owned(),
                    code,
                }
            };
            let status = |failing: &str, fixed: &str| {
                let page = |_: &str| {
                    Some(Page {
                        failing: failing.to_owned(),
                        fixed: fixed.to_owned(),
                    })
                };
                let sources = Sources {
                    goldens: &[],
                    fixtures: &[],
                    page: &page,
                    run: &run,
                };
                page_status(&row, &sources)
            };
            let header = "//! target: i386-none\n";
            let fires = format!("{header}fires");
            let passes = format!("{header}passes");
            assert_eq!(status(&fires, &passes), FixtureStatus::Passing);
            assert_eq!(status("fires", &passes), FixtureStatus::Failing);
            assert_eq!(status(&fires, "passes"), FixtureStatus::Failing);
            assert_eq!(
                status(&fires, "//! target:\npasses"),
                FixtureStatus::Failing
            );
            // A broken header fails the page even where any target would do.
            assert_eq!(
                status("//! target:\nwarns", &passes),
                FixtureStatus::Failing
            );
            assert_eq!(
                status(&format!("{header}warns"), &passes),
                FixtureStatus::Passing
            );
            // A page of several files takes its target from its first file.
            let several = format!("// file: main.en\n{header}fires\n// file: other.en\nx");
            assert_eq!(status(&several, &passes), FixtureStatus::Passing);
        },
    );
    h.case("gating/EN0001's failing page source is Latin-1", || {
        assert_eq!(page_source("EN0001", "caf\u{e9}", true), b"caf\xe9\n");
        assert_eq!(
            page_source("EN0001", "caf\u{e9}", false),
            "caf\u{e9}\n".as_bytes()
        );
        assert_eq!(
            page_source("EN0201", "caf\u{e9}", true),
            "caf\u{e9}\n".as_bytes()
        );
    });
    h.case(
        "gating/every reached page's transcript is the real output",
        || {
            for code in Code::ALL.iter().filter(|code| code.reached()) {
                let page = explain(*code).expect("a reached row has a page");
                if code.fixture() == FixtureKind::Compile {
                    continue;
                }
                let (command, expected) = page.failing.split_once('\n').expect("a transcript");
                let args = parse_command(command).expect("a command");
                let live = run_cli_at(&Place::Initialised, &args);
                assert_eq!(live.stderr, format!("{expected}\n"), "{code}");
                assert_eq!(live.stdout, "", "{code}");
                assert_eq!(live.code, 2, "{code}");
            }
        },
    );
    h.case("gating/every M1 page's examples work as a process", || {
        let fixtures = fixtures();
        let goldens: [(Golden, Place); 0] = [];
        let sources = Sources {
            goldens: &goldens,
            fixtures: &fixtures,
            page: &real_page,
            run: &run_cached,
        };
        for row in real_rows().iter().filter(|row| row.since <= Milestone::M1) {
            assert_eq!(
                page_status(row, &sources),
                FixtureStatus::Passing,
                "{}",
                row.name
            );
        }
    });
    h.case(
        "gating/every page of the milestone being built that has arrived works as a process",
        || {
            // Pages may land before the bump (M2 plan 0.4), when no `page` line gates
            // them yet; they must work already.
            let fixtures = fixtures();
            let goldens: [(Golden, Place); 0] = [];
            let sources = Sources {
                goldens: &goldens,
                fixtures: &fixtures,
                page: &real_page,
                run: &run_cached,
            };
            let building = being_built(CURRENT_MILESTONE);
            let early = real_rows()
                .into_iter()
                .filter(|row| building > CURRENT_MILESTONE && row.since == building)
                .filter(|row| real_page(row.name).is_some());
            let mut checked = 0;
            for row in early {
                assert_eq!(
                    page_status(&row, &sources),
                    FixtureStatus::Passing,
                    "{}",
                    row.name
                );
                checked += 1;
            }
            // Every arrived page of the milestone being built, counted on its own.
            let arrived = Code::ALL
                .iter()
                .filter(|code| building > CURRENT_MILESTONE && code.since() == building)
                .filter(|code| explain(**code).is_some())
                .count();
            assert_eq!(checked, arrived);
        },
    );
    h.case(
        "gating/the fixture kind of each reached row can run today",
        || {
            assert_eq!(unrunnable(CURRENT_MILESTONE), Vec::<Code>::new());
        },
    );
    h.case(
        "gating/the bump that reaches the first TestRun rows must teach the gate their kind",
        || {
            // At M4 `enrang test` arrives, and with it the first `TestRun` rows, whose
            // evidence TESTING 18 says is a firing scenario of that kind, not a
            // transcript. Until the gate runs them, this trips on that bump.
            let tripped = unrunnable(Milestone::M4);
            assert!(tripped.contains(&Code::EN1106), "{tripped:?}");
            assert!(
                tripped
                    .iter()
                    .all(|code| code.fixture() == FixtureKind::TestRun),
                "{tripped:?}"
            );
            assert_eq!(unrunnable(Milestone::M3), Vec::<Code>::new());
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
