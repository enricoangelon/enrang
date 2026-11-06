//! Milestone gating with a fake registry, as TESTING 23 asks at M0.

use enrang_testkit::{
    FixtureStatus::{self, Failing, Missing, Passing},
    GateFinding, GateRow, Harness, RunOptions, gate, gate_covers, golden, parse_covers, row_ids,
};

use crate::support::{read_doc, run_harness};

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
enum Milestone {
    M0,
    M1,
    M2,
    M3,
    M4,
    M5,
    M6,
    M9,
    M10,
}
use Milestone::*;

fn row<M>(id: &'static str, since: M, fixture: FixtureStatus) -> GateRow<'static, M> {
    GateRow { id, since, fixture }
}

fn ids(findings: &[GateFinding]) -> Vec<&str> {
    findings.iter().map(|finding| finding.id.as_str()).collect()
}

/// The registry in the shape of ARCHITECTURE 2.2, partway through the project.
fn registry() -> Vec<GateRow<'static, Milestone>> {
    vec![
        row("EN0101", M1, Passing),
        row("EN0430", M2, Passing),
        row("EN0601", M3, Missing),
        row("EN0414", M4, Missing),
        row("T0001", M4, Failing),
        row("EN1215", M6, Missing),
    ]
}

pub fn register(h: &mut Harness) {
    // since, current, status, and the verdict: enforced, gap, stale.
    let verdicts: &[(Milestone, Milestone, FixtureStatus, bool, bool, bool)] = &[
        (M0, M0, Missing, true, true, false),
        (M0, M0, Failing, true, true, false),
        (M0, M0, Passing, true, false, false),
        (M1, M0, Missing, false, false, false),
        (M1, M0, Failing, false, false, false),
        (M1, M0, Passing, false, false, true),
        (M0, M1, Missing, true, true, false),
        (M0, M1, Failing, true, true, false),
        (M0, M1, Passing, true, false, false),
        (M3, M3, Missing, true, true, false),
        (M3, M3, Passing, true, false, false),
        (M3, M4, Missing, true, true, false),
        (M4, M3, Missing, false, false, false),
        (M4, M3, Passing, false, false, true),
        (M10, M9, Failing, false, false, false),
        (M10, M9, Passing, false, false, true),
        (M10, M10, Failing, true, true, false),
        (M10, M10, Passing, true, false, false),
        (M0, M10, Missing, true, true, false),
        (M10, M0, Passing, false, false, true),
    ];
    for &(since, current, status, enforced, is_gap, is_stale) in verdicts {
        h.case(
            format!("gating::verdict::since_{since:?}_current_{current:?}_{status:?}"),
            move || {
                let report = gate(&[row("X", since, status)], &current);
                assert_eq!(report.enforced, usize::from(enforced));
                assert_eq!(report.deferred, usize::from(!enforced));
                assert_eq!(report.gaps.len(), usize::from(is_gap), "{report}");
                assert_eq!(report.stale.len(), usize::from(is_stale), "{report}");
                assert_eq!(report.is_clean(), !is_gap && !is_stale);
            },
        );
    }

    // Each current milestone over the same registry.
    let by_current: &[(Milestone, &[&str], &[&str], usize, usize)] = &[
        (M0, &[], &["EN0101", "EN0430"], 0, 6),
        (M1, &[], &["EN0430"], 1, 5),
        (M2, &[], &[], 2, 4),
        (M3, &["EN0601"], &[], 3, 3),
        (M4, &["EN0601", "EN0414", "T0001"], &[], 5, 1),
        (M5, &["EN0601", "EN0414", "T0001"], &[], 5, 1),
        (M6, &["EN0601", "EN0414", "T0001", "EN1215"], &[], 6, 0),
        (M10, &["EN0601", "EN0414", "T0001", "EN1215"], &[], 6, 0),
    ];
    for &(current, gaps, stale, enforced, deferred) in by_current {
        h.case(
            format!("gating::fake_registry::at_{current:?}"),
            move || {
                let report = gate(&registry(), &current);
                assert_eq!(ids(&report.gaps), gaps, "{report}");
                assert_eq!(ids(&report.stale), stale, "{report}");
                assert_eq!((report.enforced, report.deferred), (enforced, deferred));
                assert_eq!(report.current, format!("{current:?}"));
            },
        );
    }

    h.case("gating::a_stale_since_is_reported_with_its_milestone", || {
        let report = gate(&[row("EN1215", M6, Passing)], &M4);
        assert_eq!(
            report.stale,
            [GateFinding {
                id: "EN1215".to_owned(),
                since: "M6".to_owned(),
                fixture: Passing,
            }]
        );
        assert!(!report.is_clean());
        assert_eq!(
            report.to_string(),
            "stale: EN1215 claims a passing fixture before its milestone (since M6, current M4)\n"
        );
    });
    h.case("gating::a_gap_is_reported_with_its_milestone", || {
        let report = gate(
            &[row("EN0601", M3, Missing), row("T0001", M3, Failing)],
            &M3,
        );
        assert_eq!(
            report.to_string(),
            "gap: EN0601 has no fixture (since M3, current M3)\n\
             gap: T0001 has a failing fixture (since M3, current M3)\n"
        );
    });
    h.case("gating::findings_keep_the_order_of_the_rows", || {
        let rows = [
            row("z", M0, Missing),
            row("a", M0, Missing),
            row("m", M0, Missing),
        ];
        assert_eq!(ids(&gate(&rows, &M0).gaps), ["z", "a", "m"]);
    });
    h.case("gating::a_clean_report_prints_nothing", || {
        let report = gate(&[row("a", M0, Passing), row("b", M1, Missing)], &M0);
        assert!(report.is_clean());
        assert_eq!(report.to_string(), "");
        assert!(report.into_result().is_ok());
    });
    h.case("gating::no_rows_is_clean", || {
        let report = gate::<Milestone>(&[], &M5);
        assert!(report.is_clean());
        assert_eq!((report.enforced, report.deferred), (0, 0));
    });
    h.case("gating::a_repeated_id_is_reported_once", || {
        let rows = [
            row("a", M0, Passing),
            row("b", M0, Passing),
            row("a", M0, Passing),
            row("a", M0, Passing),
        ];
        let report = gate(&rows, &M0);
        assert_eq!(report.duplicates, ["a"]);
        assert!(!report.is_clean());
    });
    h.case("gating::any_ordered_milestone_type_works", || {
        let numeric = [row("a", 3u8, Missing), row("b", 5u8, Passing)];
        let report = gate(&numeric, &4u8);
        assert_eq!(ids(&report.gaps), ["a"]);
        assert_eq!(ids(&report.stale), ["b"]);
        assert_eq!(report.gaps[0].since, "3");
    });
    h.case("gating::into_result_carries_a_failing_report", || {
        let error = gate(&[row("a", M0, Missing)], &M0)
            .into_result()
            .unwrap_err();
        assert_eq!(ids(&error.gaps), ["a"]);
    });
    h.case("gating::a_failing_report_fails_a_harness_case", || {
        let (report, output) = run_harness(
            |h| h.case("gate", || gate(&[row("a", M1, Passing)], &M0).into_result()),
            &RunOptions::default(),
        );
        assert_eq!(report.failed, ["gate"]);
        assert!(
            output.contains("stale: a claims a passing fixture"),
            "{output}"
        );
    });
    h.case("gating::real_golden::report", || {
        let rows = [
            row("EN0601", M3, Missing),
            row("T0001", M3, Failing),
            row("EN1215", M6, Passing),
            row("EN0601", M3, Missing),
        ];
        let covers = ["MIG-99".to_owned()];
        let mut report = gate(&rows, &M3);
        report.orphans = gate_covers(&[("MIG-01", M6)], &covers, &M3).orphans;
        golden("testkit", "gate_report.txt", &report.to_string())
    });
    register_covers(h);
}

fn register_covers(h: &mut Harness) {
    let rows = || [("MIG-01", M6), ("MIG-02", M6), ("C01", M2), ("H01", M3)];
    // Claims, current, gaps, stale, orphans.
    let table: &[(&[&str], Milestone, &[&str], &[&str], &[&str])] = &[
        (&[], M0, &[], &[], &[]),
        (&[], M2, &["C01"], &[], &[]),
        (&["C01"], M2, &[], &[], &[]),
        (&["C01", "H01"], M2, &[], &["H01"], &[]),
        (&["C01", "H01"], M3, &[], &[], &[]),
        (&["C01"], M6, &["MIG-01", "MIG-02", "H01"], &[], &[]),
        (&["MIG-01", "MIG-02", "C01", "H01"], M6, &[], &[], &[]),
        (&["MIG-01"], M0, &[], &["MIG-01"], &[]),
        (&["MIG-99"], M0, &[], &[], &["MIG-99"]),
        (
            &["MIG-99", "ADV-1"],
            M10,
            &["MIG-01", "MIG-02", "C01", "H01"],
            &[],
            &["ADV-1", "MIG-99"],
        ),
        (&["C01", "C01"], M2, &[], &[], &[]),
    ];
    for (index, &(claims, current, gaps, stale, orphans)) in table.iter().enumerate() {
        h.case(format!("gating::covers[{index}]"), move || {
            let claims: Vec<String> = claims.iter().map(|&id| id.to_owned()).collect();
            let report = gate_covers(&rows(), &claims, &current);
            assert_eq!(ids(&report.gaps), gaps, "{report}");
            assert_eq!(ids(&report.stale), stale, "{report}");
            assert_eq!(report.orphans, orphans, "{report}");
        });
    }
    h.case("gating::covers::an_orphan_is_reported_in_words", || {
        let report = gate_covers(&[("MIG-01", M6)], &["MIG-99".to_owned()], &M0);
        assert_eq!(
            report.to_string(),
            "orphan: `covers: MIG-99` names no row\n"
        );
        assert!(!report.is_clean());
    });
    h.case("gating::covers::over_the_real_c_rows", || {
        let spec = read_doc("SPEC.md");
        let found = row_ids(&spec, "C").expect("SPEC 4.5 parses");
        let rows: Vec<(&str, Milestone)> = found.iter().map(|row| (row.id.as_str(), M2)).collect();
        assert!(gate_covers(&rows, &[], &M1).is_clean());
        assert_eq!(gate_covers(&rows, &[], &M2).gaps.len(), 17);
        let fixture = "//! covers: C01\n//! covers: C02, C03\nfunction main(): void {}\n";
        let report = gate_covers(&rows, &parse_covers(fixture), &M2);
        assert_eq!(report.gaps.len(), 14);
        assert!(!ids(&report.gaps).contains(&"C02"));
    });
}
