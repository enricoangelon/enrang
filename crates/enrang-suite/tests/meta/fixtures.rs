//! The anchored compile fixtures of `tests/compile/` as files (TESTING 7 and 18, M1
//! plan d.6), and the deferred features of SPEC 16, each of which needs a fixture
//! producing exactly its message head (TESTING 18). `gating.rs` runs the fixtures as
//! the evidence of each `Compile` row; this module keeps their layout honest, so a
//! misnamed file cannot drop out of that evidence unseen.

use std::collections::BTreeSet;

use enrang_diag::{CURRENT_MILESTONE, Code, FixtureKind, Milestone};
use enrang_testkit::{Harness, reported, workspace_root};

use crate::support::{
    FIXTURES, Place, cells, directories, files_under, fixtures, gate_transcripts, read, run_cached,
    stderr_of,
};

/// SPEC 16's table: each code and its message head.
pub fn deferred_heads() -> Vec<(String, String)> {
    let spec = read("docs/SPEC.md");
    let start = spec.find("\n## 16. Deferred features\n").expect("SPEC 16");
    let section = &spec[start + 1..];
    let end = section[3..]
        .find("\n## ")
        .map_or(section.len(), |at| at + 3);
    section[..end]
        .lines()
        .filter(|line| line.starts_with("| EN"))
        .map(|line| {
            let row = cells(&line.replace("\\|", "\u{0}"));
            let message = row[2].replace('\u{0}', "|");
            // EN1006's cell goes on, after the head, to say what its note names.
            let head = message.split(": ").next().unwrap_or(&message).to_owned();
            (row[0].clone(), head)
        })
        .collect()
}

/// The deferred features due by `milestone` whose fixture does not produce exactly
/// their message head: a firing fixture of a `Compile` code, run through `check`,
/// or a gate transcript of any other code.
fn heads_not_shown(milestone: Milestone) -> Vec<String> {
    let fixtures = fixtures();
    let transcripts = gate_transcripts();
    let mut missing = Vec::new();
    for (name, head) in deferred_heads() {
        let code = Code::from_name(&name).unwrap_or_else(|| panic!("{name} is no row"));
        if code.since() > milestone {
            continue;
        }
        let shown = if code.fixture() == FixtureKind::Compile {
            fixtures
                .iter()
                .filter(|fixture| fixture.code == name && !fixture.near_miss)
                .any(|fixture| {
                    let Some(args) = fixture.check_args() else {
                        return false;
                    };
                    let ran = run_cached(&Place::Root, &args);
                    reported(&ran.stderr)
                        .iter()
                        .any(|diag| diag.code == name && diag.message == head)
                })
        } else {
            let line = format!("error[{name}]: {head}");
            transcripts
                .iter()
                .any(|(golden, _)| stderr_of(&golden.text).lines().any(|l| l == line))
        };
        if !shown {
            missing.push(format!("{name}: {head}"));
        }
    }
    missing
}

pub fn register(h: &mut Harness) {
    h.case(
        "fixtures/every directory names a compile code of the registry",
        || {
            let names = directories(&workspace_root().join(FIXTURES));
            assert!(!names.is_empty(), "no fixture directory");
            for name in names {
                let code = Code::from_name(&name).unwrap_or_else(|| panic!("{name} is no code"));
                assert_eq!(code.fixture(), FixtureKind::Compile, "{name}");
            }
        },
    );
    h.case(
        "fixtures/every file is a firing fixture or a near-miss, one level down",
        || {
            for name in files_under(&workspace_root().join(FIXTURES)) {
                let parts: Vec<&str> = name.split('/').collect();
                assert_eq!(parts.len(), 2, "{name} is not <CODE>/<file>");
                // Neither suffix ends in `.test.en`, so no fixture is a test part.
                assert!(
                    parts[1].ends_with(".fail.en") || parts[1].ends_with(".pass.en"),
                    "{name} is neither <name>.fail.en nor <name>.pass.en"
                );
            }
        },
    );
    h.case(
        "fixtures/fmt skips every firing fixture, so no anchor can move",
        || {
            // A firing fixture that `fmt` read would not parse, or would be re-laid,
            // and either shows: errors on stderr, or its path on stdout.
            let args = vec!["fmt".to_owned(), "--check".to_owned(), FIXTURES.to_owned()];
            let ran = run_cached(&Place::Root, &args);
            assert!(ran.code == 0 || ran.code == 1, "{ran:?}");
            assert_eq!(ran.stderr, "", "fmt read a firing fixture");
            assert!(!ran.stdout.contains(".fail.en"), "{}", ran.stdout);
        },
    );
    h.case(
        "fixtures/a firing fixture anchors its own code, and a near-miss nothing",
        || {
            for fixture in fixtures() {
                let anchors = fixture
                    .anchors
                    .as_ref()
                    .unwrap_or_else(|error| panic!("{}: {error}", fixture.path));
                if fixture.near_miss {
                    assert!(
                        anchors.is_empty(),
                        "the near-miss {} has anchors",
                        fixture.path
                    );
                } else {
                    assert!(
                        anchors.iter().any(|anchor| anchor.code == fixture.code),
                        "{} anchors no {}",
                        fixture.path,
                        fixture.code
                    );
                }
            }
        },
    );
    h.case(
        "fixtures/every directory has a firing fixture and a near-miss",
        || {
            let all = fixtures();
            let codes: BTreeSet<&str> = all.iter().map(|fixture| fixture.code.as_str()).collect();
            for code in codes {
                let mine = || all.iter().filter(move |fixture| fixture.code == code);
                assert!(mine().any(|f| !f.near_miss), "{code} has no firing fixture");
                assert!(mine().any(|f| f.near_miss), "{code} has no near-miss");
            }
        },
    );
    h.case("fixtures/SPEC 16's table is read whole", || {
        let heads = deferred_heads();
        assert_eq!(heads.len(), 38);
        assert_eq!(
            heads[0],
            (
                "EN1001".to_owned(),
                "async functions are not supported yet".to_owned()
            )
        );
        let power = heads
            .iter()
            .find(|(code, _)| code == "EN1022")
            .expect("EN1022");
        assert_eq!(power.1, "the `**` operator is not supported yet");
        let by_value = heads
            .iter()
            .find(|(code, _)| code == "EN1006")
            .expect("EN1006");
        assert_eq!(
            by_value.1,
            "an interface type by value outside a parameter is not supported yet"
        );
    });
    h.case(
        "fixtures/each reached deferred feature gives exactly its message head",
        || {
            assert_eq!(heads_not_shown(CURRENT_MILESTONE), Vec::<String>::new());
        },
    );
    h.case(
        "fixtures/each deferred feature due at M1 gives exactly its message head",
        || {
            assert_eq!(heads_not_shown(Milestone::M1), Vec::<String>::new());
            let due = deferred_heads()
                .iter()
                .filter(|(name, _)| {
                    Code::from_name(name).is_some_and(|code| code.since() <= Milestone::M1)
                })
                .count();
            assert_eq!(due, 21);
        },
    );
    h.case(
        "fixtures/each deferred feature due at M2 gives exactly its message head",
        || {
            // Every row of SPEC 16 is due by M2: the 17 phase 2 heads join M1's 21.
            assert_eq!(heads_not_shown(Milestone::M2), Vec::<String>::new());
            let due: Vec<String> = deferred_heads()
                .into_iter()
                .filter(|(name, _)| {
                    Code::from_name(name).is_some_and(|code| code.since() == Milestone::M2)
                })
                .map(|(name, _)| name)
                .collect();
            assert_eq!(due.len(), 17, "{due:?}");
            assert_eq!(deferred_heads().len(), 21 + 17);
            assert!(Milestone::M2 <= CURRENT_MILESTONE, "M2's heads are due");
        },
    );
}
