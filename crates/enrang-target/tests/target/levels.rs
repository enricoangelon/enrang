//! Every level against every feature, checked against SPEC 10.1 and the complete
//! sets of ARCHITECTURE 8.2.

use std::collections::BTreeSet;

use enrang_target::{Arch, CpuLevel, Feature, FeatureSet};
use enrang_testkit::Harness;

use crate::support::{
    arch_level_set, arch_levels, backticked, feature, level, section, spec_levels,
};

const ARCHES: [(&str, Arch); 3] = [
    ("i386", Arch::I386),
    ("x86_64", Arch::X86_64),
    ("mir", Arch::Mir),
];

/// The arch whose ladder holds `level`.
fn home_arch(level: CpuLevel) -> Arch {
    if level == CpuLevel::X86_64 {
        Arch::X86_64
    } else {
        Arch::I386
    }
}

/// What SPEC 10.1 says of `feature` at `level`: `None` where it does not say.
///
/// The rows from `i386` to `sse2` are exhaustive lists of what code may assume, so
/// a public feature none of them has added is a no. The internal tags are not
/// SPEC's vocabulary, and `sse` at level `sse2` comes from ARCHITECTURE 7.14. The
/// `x86-64` row states only some features in each direction.
fn spec_says(target: CpuLevel, feature: Feature) -> Option<bool> {
    let rows = spec_levels();
    let at = rows
        .iter()
        .position(|(name, _)| name == target.name())
        .expect("a SPEC row for the level");
    if !rows[at].1.cumulative && !rows[at].1.denies.is_empty() && at > 0 {
        let row = &rows[at].1;
        return if row.adds.contains(&feature) {
            Some(true)
        } else if row.denies.contains(&feature) {
            Some(false)
        } else {
            None
        };
    }
    if rows[..=at]
        .iter()
        .any(|(_, row)| row.adds.contains(&feature))
    {
        return Some(true);
    }
    if matches!(feature, Feature::Ud2 | Feature::Ia32) {
        return None;
    }
    if feature == Feature::Sse && target == CpuLevel::Sse2 {
        return None;
    }
    Some(false)
}

pub fn register(h: &mut Harness) {
    names(h);
    matrix(h);
    spec_rows(h);
    per_arch(h);
    lowest_with(h);
    shape(h);
}

fn names(h: &mut Harness) {
    h.case("level/ALL is SPEC 10.1's rungs, in its order", || {
        let code: Vec<&str> = CpuLevel::ALL.iter().map(|l| l.name()).collect();
        let doc: Vec<&str> = spec_levels().iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(code, doc);
    });
    h.case(
        "level/ALL is ARCHITECTURE 8.2's rungs, in its order",
        || {
            let code: Vec<&str> = CpuLevel::ALL.iter().map(|l| l.name()).collect();
            let doc: Vec<&str> = arch_levels().iter().map(|(n, _)| n.as_str()).collect();
            assert_eq!(code, doc);
        },
    );
    for level in CpuLevel::ALL {
        h.case(format!("level/name/{}", level.name()), move || {
            assert_eq!(CpuLevel::from_name(level.name()), Some(level));
        });
    }
    for name in [
        "", "I386", "i786", "i386 ", "x86_64", "x8664", "amd64", "pentium", "k6", "core2", "native",
    ] {
        h.case(format!("level/not a level/`{name}`"), move || {
            assert_eq!(CpuLevel::from_name(name), None);
        });
    }
    h.case("level/the ladder orders by rung", || {
        let mut sorted = CpuLevel::ALL;
        sorted.sort();
        assert_eq!(sorted, CpuLevel::ALL);
        assert!(CpuLevel::Sse2 > CpuLevel::I686);
    });
}

/// The heart of the table: 6 levels by 28 features.
fn matrix(h: &mut Harness) {
    for level in CpuLevel::ALL {
        for &feature in Feature::ALL {
            let name = format!("level/{}/{}", level.name(), feature.name());
            h.case(name, move || {
                let actual = level.features(home_arch(level)).contains(feature);
                if let Some(says) = spec_says(level, feature) {
                    assert_eq!(actual, says, "against SPEC 10.1");
                }
                let arch = arch_level_set(level).contains(feature.name());
                assert_eq!(actual, arch, "against ARCHITECTURE 8.2");
            });
        }
    }
    for level in CpuLevel::ALL {
        h.case(format!("level/{}/set is 8.2's", level.name()), move || {
            let code: BTreeSet<String> = level
                .features(home_arch(level))
                .iter()
                .map(|f| f.name().to_owned())
                .collect();
            assert_eq!(&code, arch_level_set(level));
        });
    }
}

/// SPEC's words and 8.2's names, row by row, so neither can drift from the other.
fn spec_rows(h: &mut Harness) {
    for (at, (name, row)) in spec_levels().iter().enumerate() {
        let (name, row) = (name.clone(), row.clone());
        h.case(format!("level/spec row/{name}"), move || {
            let this = level(&name);
            let set = this.features(home_arch(this));
            for feature in &row.adds {
                assert!(
                    set.contains(*feature),
                    "SPEC says it may assume {feature:?}"
                );
            }
            for feature in &row.denies {
                assert!(!set.contains(*feature), "SPEC says not {feature:?}");
            }
            if row.cumulative {
                let below = CpuLevel::ALL[at - 1];
                let added: BTreeSet<Feature> = below
                    .features(home_arch(below))
                    .missing(set)
                    .iter()
                    .collect();
                // What a rung adds beyond SPEC's words is only the tags SPEC does
                // not use: `ud2`, and `sse` under `sse2` (ARCHITECTURE 7.14).
                let extra: Vec<&Feature> = added.difference(&row.adds).collect();
                let allowed: &[Feature] = match this {
                    CpuLevel::I686 => &[Feature::Ud2],
                    CpuLevel::Sse2 => &[Feature::Sse],
                    _ => &[],
                };
                for feature in &extra {
                    assert!(allowed.contains(feature), "{feature:?} is not in SPEC");
                }
                assert_eq!(extra.len(), allowed.len(), "{extra:?} against {allowed:?}");
            }
        });
    }
    h.case("level/the i386 row denies what it must", || {
        let denied = &spec_levels()[0].1.denies;
        for name in [
            "fpu", "sse", "cpuid", "cr4", "cmov", "bswap", "cmpxchg", "xadd", "rdtsc", "nopl",
        ] {
            assert!(denied.contains(&feature(name)), "`{name}` was not read");
        }
    });
    h.case(
        "level/the x86-64 row rules out the post-baseline forms",
        || {
            let denied = &spec_levels()[5].1.denies;
            for name in ["popcnt", "sse3", "ssse3", "sse4.1", "sse4.2"] {
                assert!(denied.contains(&feature(name)), "`{name}` was not read");
            }
            let set = CpuLevel::X86_64.features(Arch::X86_64);
            assert!(set.contains(Feature::Lm));
            assert!(set.contains(Feature::Nopl));
        },
    );
    h.case("level/only level x86-64 has nopl, lm, fpu and pae", || {
        for name in ["nopl", "lm", "fpu", "pae"] {
            for level in CpuLevel::ALL {
                assert_eq!(
                    arch_level_set(level).contains(name),
                    level == CpuLevel::X86_64,
                    "{level:?} {name}"
                );
            }
        }
    });
    h.case(
        "level/no rung has MMX, 3DNow!, NX or anything past SSE2",
        || {
            let never = [
                "mmx", "3dnow", "nx", "sse3", "ssse3", "sse4.1", "sse4.2", "popcnt",
            ];
            for level in CpuLevel::ALL {
                let set = level.features(home_arch(level));
                for name in never {
                    assert!(!set.contains(feature(name)), "{level:?} has {name}");
                }
            }
        },
    );
    h.case("level/the floor is only ia32", || {
        let set = CpuLevel::I386.features(Arch::I386);
        assert_eq!(set, FeatureSet::of(&[Feature::Ia32]));
    });
}

/// `features(arch)` on each architecture.
fn per_arch(h: &mut Harness) {
    for level in CpuLevel::ALL {
        for (arch_name, arch) in ARCHES {
            h.case(
                format!("level/{}/on {arch_name}", level.name()),
                move || {
                    let applies = arch == Arch::Mir || arch == home_arch(level);
                    let set = level.features(arch);
                    if applies {
                        let names: BTreeSet<String> =
                            set.iter().map(|f| f.name().to_owned()).collect();
                        assert_eq!(&names, arch_level_set(level));
                    } else {
                        assert!(set.is_empty(), "a level that does not apply gave {set}");
                    }
                },
            );
        }
    }
    let ladders: [(&str, Arch, &[CpuLevel]); 3] = [
        (
            "i386",
            Arch::I386,
            &[
                CpuLevel::I386,
                CpuLevel::I486,
                CpuLevel::I586,
                CpuLevel::I686,
                CpuLevel::Sse2,
            ],
        ),
        ("x86_64", Arch::X86_64, &[CpuLevel::X86_64]),
        ("mir", Arch::Mir, &[]),
    ];
    for (name, arch, want) in ladders {
        h.case(format!("level/ladder of {name}"), move || {
            assert_eq!(CpuLevel::for_arch(arch), want);
        });
    }
}

fn lowest_with(h: &mut Harness) {
    // Derived from the table: the first rung of the arch's ladder with the feature.
    for &feature in Feature::ALL {
        for (arch_name, arch) in ARCHES {
            let name = format!("lowest/{}/{arch_name}", feature.name());
            h.case(name, move || {
                let want = CpuLevel::for_arch(arch)
                    .iter()
                    .copied()
                    .find(|level| arch_level_set(*level).contains(feature.name()));
                assert_eq!(CpuLevel::lowest_with(feature, arch), want);
            });
        }
    }
    // Stated by hand, so the rule above cannot share a mistake with the code.
    let facts: &[(&str, Arch, Option<CpuLevel>)] = &[
        ("ia32", Arch::I386, Some(CpuLevel::I386)),
        ("bswap", Arch::I386, Some(CpuLevel::I486)),
        ("cmpxchg", Arch::I386, Some(CpuLevel::I486)),
        ("xadd", Arch::I386, Some(CpuLevel::I486)),
        ("invlpg", Arch::I386, Some(CpuLevel::I486)),
        ("cpuid", Arch::I386, Some(CpuLevel::I586)),
        ("cmpxchg8b", Arch::I386, Some(CpuLevel::I586)),
        ("rdtsc", Arch::I386, Some(CpuLevel::I586)),
        ("msr", Arch::I386, Some(CpuLevel::I586)),
        ("cr4", Arch::I386, Some(CpuLevel::I586)),
        ("cmov", Arch::I386, Some(CpuLevel::I686)),
        ("fcomi", Arch::I386, Some(CpuLevel::I686)),
        ("ud2", Arch::I386, Some(CpuLevel::I686)),
        ("sse", Arch::I386, Some(CpuLevel::Sse2)),
        ("sse2", Arch::I386, Some(CpuLevel::Sse2)),
        ("fxsave", Arch::I386, Some(CpuLevel::Sse2)),
        ("fpu", Arch::I386, None),
        ("nopl", Arch::I386, None),
        ("lm", Arch::I386, None),
        ("pae", Arch::I386, None),
        ("mmx", Arch::I386, None),
        ("3dnow", Arch::I386, None),
        ("popcnt", Arch::I386, None),
        ("ia32", Arch::X86_64, Some(CpuLevel::X86_64)),
        ("cmov", Arch::X86_64, Some(CpuLevel::X86_64)),
        ("fpu", Arch::X86_64, Some(CpuLevel::X86_64)),
        ("lm", Arch::X86_64, Some(CpuLevel::X86_64)),
        ("mmx", Arch::X86_64, None),
        ("popcnt", Arch::X86_64, None),
        ("sse3", Arch::X86_64, None),
        ("ia32", Arch::Mir, None),
        ("sse2", Arch::Mir, None),
    ];
    for &(name, arch, want) in facts {
        h.case(format!("lowest/fact/{name} on {arch:?}"), move || {
            assert_eq!(CpuLevel::lowest_with(feature(name), arch), want);
        });
    }
    h.case("lowest/G15's `bswap` needs `i486`", || {
        let golden = section(
            "SPEC.md",
            "### G15 Inline assembly above the target CPU level",
        );
        let line = golden
            .lines()
            .find(|line| line.contains("needs level"))
            .expect("the label of G15");
        let named = backticked(line)
            .into_iter()
            .find(|piece| piece.starts_with('i'))
            .expect("a level in the label");
        assert_eq!(
            CpuLevel::lowest_with(Feature::Bswap, Arch::I386).map(CpuLevel::name),
            Some(named)
        );
    });
}

/// The rungs form a chain, even though the chips do not (see `chips`).
fn shape(h: &mut Harness) {
    for pair in CpuLevel::ALL.windows(2) {
        let (low, high) = (pair[0], pair[1]);
        let name = format!("level/{} is below {}", low.name(), high.name());
        h.case(name, move || {
            let (lo, hi) = (low.features(Arch::Mir), high.features(Arch::Mir));
            assert!(hi.contains_all(lo), "{high:?} lost {}", hi.missing(lo));
            assert!(!lo.contains_all(hi), "{high:?} adds nothing");
        });
    }
    h.case(
        "level/i686 has CMOV and lacks MMX; nothing below has CMOV",
        || {
            assert!(CpuLevel::I686.features(Arch::I386).contains(Feature::Cmov));
            assert!(!CpuLevel::I686.features(Arch::I386).contains(Feature::Mmx));
            assert!(!CpuLevel::I586.features(Arch::I386).contains(Feature::Cmov));
        },
    );
}
