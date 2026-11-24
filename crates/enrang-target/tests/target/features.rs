//! `define_features!` against ARCHITECTURE 7.14, `cpu.has` against SPEC 10.3, and
//! the laws of `FeatureSet`.

use enrang_target::{CpuLevel, Feature, FeatureSet};
use enrang_testkit::{Harness, Rng, Xoshiro256, rng_for, scaled};

use crate::support::{backticked, features, line_starting, section};

/// A row of the `define_features!` block in ARCHITECTURE 7.14.
#[derive(Clone)]
struct DocRow {
    variant: String,
    name: String,
    internal: bool,
}

fn doc_rows() -> Vec<DocRow> {
    let text = section("ARCHITECTURE.md", "### 7.14 Level enforcement");
    let (_, rest) = text.split_once("define_features! {").expect("the block");
    let (body, _) = rest.split_once("\n}").expect("the end of the block");
    let mut rows = Vec::new();
    for line in body.lines() {
        let (code, comment) = line.split_once("//").unwrap_or((line, ""));
        for item in code.split(',').map(str::trim).filter(|i| !i.is_empty()) {
            let (variant, name) = item.split_once(' ').expect("`Variant \"name\"`");
            rows.push(DocRow {
                variant: variant.to_owned(),
                name: name.trim_matches('"').to_owned(),
                internal: comment.contains("not queryable through cpu.has"),
            });
        }
    }
    rows
}

/// The names `cpu.has` takes, from SPEC 10.3.
fn cpu_has_names() -> Vec<&'static str> {
    let line = line_starting(
        section("SPEC.md", "### 10.3 Run-time detection"),
        "- `cpu.has(feature: &string): bool`",
    );
    let list = backticked(line)
        .into_iter()
        .find(|piece| piece.starts_with("fpu "))
        .expect("the feature list");
    list.split_whitespace().collect()
}

pub fn register(h: &mut Harness) {
    rows(h);
    cpu_has(h);
    sets(h);
    laws(h);
}

fn rows(h: &mut Harness) {
    let doc = doc_rows();
    h.case(
        "features/the block has 28 rows, two of them internal",
        || {
            let doc = doc_rows();
            assert_eq!(doc.len(), 28);
            let internal: Vec<&str> = doc
                .iter()
                .filter(|row| row.internal)
                .map(|row| row.name.as_str())
                .collect();
            assert_eq!(internal, ["ud2", "ia32"]);
        },
    );
    h.case("features/ALL has exactly the rows, in order", || {
        let doc: Vec<String> = doc_rows().into_iter().map(|row| row.name).collect();
        let code: Vec<&str> = Feature::ALL.iter().map(|f| f.name()).collect();
        assert_eq!(code, doc);
    });
    for (index, row) in doc.into_iter().enumerate() {
        h.case(format!("features/row/{}", row.name), move || {
            let found = Feature::from_name(&row.name)
                .unwrap_or_else(|| panic!("`{}` is not a feature", row.name));
            assert_eq!(format!("{found:?}"), row.variant);
            assert_eq!(found.name(), row.name);
            assert_eq!(found.queryable(), !row.internal);
            assert_eq!(Feature::ALL[index], found, "its place in ALL");
        });
    }
    for name in [
        "",
        " fpu",
        "fpu ",
        "FPU",
        "sse4",
        "sse41",
        "3DNow",
        "cmpxchg16b",
        "lahf",
        "avx",
        "x87",
    ] {
        h.case(format!("features/not a feature/`{name}`"), move || {
            assert_eq!(Feature::from_name(name), None);
            assert_eq!(Feature::from_cpu_has(name), None);
        });
    }
}

fn cpu_has(h: &mut Harness) {
    h.case("features/QUERYABLE is SPEC 10.3's list, in order", || {
        let names: Vec<&str> = Feature::QUERYABLE.iter().map(|f| f.name()).collect();
        assert_eq!(names, cpu_has_names());
    });
    for name in cpu_has_names() {
        h.case(format!("features/cpu.has answers/{name}"), move || {
            let found = Feature::from_cpu_has(name)
                .unwrap_or_else(|| panic!("`cpu.has(\"{name}\")` is refused"));
            assert_eq!(found.name(), name);
            assert!(found.queryable());
        });
    }
    for (name, tag) in [("ud2", Feature::Ud2), ("ia32", Feature::Ia32)] {
        h.case(format!("features/cpu.has refuses/{name}"), move || {
            assert_eq!(Feature::from_cpu_has(name), None);
            assert!(!cpu_has_names().contains(&name), "SPEC lists `{name}`");
            assert!(!tag.queryable());
            assert_eq!(Feature::from_name(name), Some(tag), "still a tag");
        });
    }
}

/// `sets[..]`: `(have, need, contains_all, missing)` by feature name.
type SetRow = (
    &'static str,
    &'static [&'static str],
    &'static [&'static str],
    bool,
    &'static [&'static str],
);

const SET_ROWS: &[SetRow] = &[
    ("empty against empty", &[], &[], true, &[]),
    ("empty needs nothing", &["cmov"], &[], true, &[]),
    ("nothing has a need", &[], &["cmov"], false, &["cmov"]),
    ("equal", &["cmov", "mmx"], &["cmov", "mmx"], true, &[]),
    ("superset", &["cmov", "mmx"], &["mmx"], true, &[]),
    ("subset", &["mmx"], &["cmov", "mmx"], false, &["cmov"]),
    ("disjoint", &["mmx"], &["cmov"], false, &["cmov"]),
    (
        "overlap lists only what is lacking",
        &["ia32", "mmx"],
        &["ia32", "cmov", "sse2"],
        false,
        &["cmov", "sse2"],
    ),
    (
        "the highest and lowest bits",
        &["fpu"],
        &["ia32"],
        false,
        &["ia32"],
    ),
    ("the same reversed", &["ia32"], &["fpu"], false, &["fpu"]),
];

fn sets(h: &mut Harness) {
    for &(name, have, need, holds, missing) in SET_ROWS {
        h.case(format!("set/{name}"), move || {
            let (have, need) = (features(have), features(need));
            assert_eq!(have.contains_all(need), holds, "contains_all");
            assert_eq!(have.missing(need), features(missing), "missing");
        });
    }
    for &feature in Feature::ALL {
        h.case(format!("set/singleton/{}", feature.name()), move || {
            let set = FeatureSet::of(&[feature]);
            assert_eq!(set.iter().collect::<Vec<_>>(), [feature]);
            assert!(set.contains(feature));
            for &other in Feature::ALL {
                assert_eq!(set.contains(other), other == feature, "{other:?}");
            }
            assert_eq!(set.to_string(), feature.name());
        });
    }
    h.case("set/empty", || {
        assert!(FeatureSet::EMPTY.is_empty());
        assert_eq!(FeatureSet::EMPTY, FeatureSet::default());
        assert_eq!(FeatureSet::EMPTY.iter().count(), 0);
        assert_eq!(FeatureSet::EMPTY.to_string(), "");
        assert!(!FeatureSet::of(&[Feature::Fpu]).is_empty());
    });
    h.case("set/of ignores repeats and order", || {
        let a = FeatureSet::of(&[Feature::Cmov, Feature::Mmx, Feature::Cmov]);
        let b = FeatureSet::of(&[Feature::Mmx, Feature::Cmov]);
        assert_eq!(a, b);
    });
    h.case("set/union", || {
        let a = features(&["cmov", "mmx"]);
        let b = features(&["mmx", "sse2"]);
        assert_eq!(a.union(b), features(&["cmov", "mmx", "sse2"]));
        assert_eq!(a.union(FeatureSet::EMPTY), a);
    });
    h.case("set/prints in row order, not insertion order", || {
        let set = FeatureSet::of(&[Feature::Ia32, Feature::Sse41, Feature::Fpu]);
        assert_eq!(set.to_string(), "fpu sse4.1 ia32");
        assert_eq!(format!("{set:?}"), "FeatureSet(fpu sse4.1 ia32)");
    });
    h.case("set/every pair of singletons", || {
        for &a in Feature::ALL {
            for &b in Feature::ALL {
                let (sa, sb) = (FeatureSet::of(&[a]), FeatureSet::of(&[b]));
                assert_eq!(sa.contains_all(sb), a == b, "{a:?} {b:?}");
                let lacking = if a == b { FeatureSet::EMPTY } else { sb };
                assert_eq!(sa.missing(sb), lacking, "{a:?} {b:?}");
            }
        }
    });
    h.case("set/every level has ia32", || {
        for level in CpuLevel::ALL {
            assert!(
                level
                    .features(enrang_target::Arch::Mir)
                    .contains(Feature::Ia32),
                "{level:?}"
            );
        }
    });
}

fn random_set(rng: &mut Xoshiro256) -> FeatureSet {
    let picked: Vec<Feature> = Feature::ALL
        .iter()
        .copied()
        .filter(|_| rng.below(2) == 0)
        .collect();
    FeatureSet::of(&picked)
}

fn laws(h: &mut Harness) {
    h.case("set/laws on random sets", || {
        let mut rng = rng_for("target/set laws");
        let mut saw_contained = false;
        let mut saw_missing = false;
        for _ in 0..scaled(4000) {
            let a = random_set(&mut rng);
            // One draw in four is built to be contained, or `contains_all` would
            // almost never hold on a random pair and that side would go untested.
            let b = if rng.below(4) == 0 {
                let picked: Vec<Feature> = a.iter().filter(|_| rng.below(2) == 0).collect();
                FeatureSet::of(&picked)
            } else {
                random_set(&mut rng)
            };
            let missing = a.missing(b);
            assert_eq!(a.contains_all(b), missing.is_empty(), "{a} / {b}");
            saw_contained |= missing.is_empty();
            saw_missing |= !missing.is_empty();
            assert!(b.contains_all(missing), "missing is part of what was asked");
            assert!(a.union(missing).contains_all(b), "adding it is enough");
            for feature in missing.iter() {
                assert!(!a.contains(feature), "{feature:?} was not lacking");
            }
            let round: Vec<Feature> = a.iter().collect();
            assert_eq!(FeatureSet::of(&round), a);
            assert_eq!(a.union(b), b.union(a));
        }
        assert!(saw_contained && saw_missing, "both outcomes were reached");
    });
}
