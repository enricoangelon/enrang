//! The ISA is not a line. Reads the chip matrix of ARCHITECTURE 8.1 into feature
//! sets and shows that SPEC 10.1's alias table follows from it: each alias sits at
//! the highest rung every chip it names can run.

use std::collections::BTreeMap;
use std::sync::OnceLock;

use enrang_target::{Arch, CPU_ALIASES, CpuAlias, CpuLevel, Feature, FeatureSet, LongMode};
use enrang_testkit::Harness;

use crate::support::{cpu, feature, features, line_starting, section, spec};

/// A row of the matrix: the flag of each of the 23 columns.
struct Chip {
    flags: Vec<char>,
}

struct Matrix {
    /// The feature of each column.
    columns: Vec<Feature>,
    chips: BTreeMap<String, Chip>,
}

impl Matrix {
    fn chip(&self, name: &str) -> &Chip {
        self.chips
            .get(name)
            .unwrap_or_else(|| panic!("no row `{name}` in the 8.1 matrix"))
    }

    /// The features a chip surely has. `~` varies by model or stepping, `?` is
    /// unverified and `o` is an external option, so none of them can be assumed.
    fn has(&self, name: &str) -> FeatureSet {
        let chip = self.chip(name);
        let present: Vec<Feature> = self
            .columns
            .iter()
            .zip(&chip.flags)
            .filter(|(_, flag)| **flag == 'Y')
            .map(|(feature, _)| *feature)
            .collect();
        FeatureSet::of(&present)
    }

    fn flag(&self, name: &str, feature: Feature) -> char {
        let column = self
            .columns
            .iter()
            .position(|f| *f == feature)
            .unwrap_or_else(|| panic!("no column for {feature:?}"));
        self.chip(name).flags[column]
    }

    /// `level`, reduced to what the matrix has columns for.
    fn testable(&self, level: CpuLevel) -> FeatureSet {
        let kept: Vec<Feature> = level
            .features(Arch::Mir)
            .iter()
            .filter(|feature| self.columns.contains(feature))
            .collect();
        FeatureSet::of(&kept)
    }

    fn runs(&self, chip: &str, level: CpuLevel) -> bool {
        self.has(chip).contains_all(self.testable(level))
    }
}

fn matrix() -> &'static Matrix {
    static MATRIX: OnceLock<Matrix> = OnceLock::new();
    MATRIX.get_or_init(|| {
        let text = section("ARCHITECTURE.md", "### 8.1 Feature matrix");

        let columns_line = line_starting(text, "Columns: ");
        let columns: Vec<Feature> = columns_line["Columns: ".len()..]
            .trim_end_matches('.')
            .split(", ")
            .enumerate()
            .map(|(index, column)| {
                let (number, word) = column.split_once(' ').expect("`1 FPU`");
                assert_eq!(number.parse::<usize>(), Ok(index + 1), "`{column}`");
                match word {
                    "3DNow!" => Feature::Amd3dnow,
                    "x86-64" => Feature::Lm,
                    other => feature(&other.to_ascii_lowercase()),
                }
            })
            .collect();
        assert_eq!(columns.len(), 23);

        let (_, rest) = text.split_once("```text\n").expect("the matrix");
        let (body, _) = rest.split_once("```").expect("the end of the matrix");
        let mut chips = BTreeMap::new();
        for line in body.lines().skip(1) {
            let tokens: Vec<&str> = line.split_whitespace().collect();
            let groups = &tokens[tokens.len() - 5..];
            let lengths: Vec<usize> = groups.iter().map(|group| group.len()).collect();
            assert_eq!(lengths, [5, 5, 5, 5, 3], "the columns of `{line}`");
            let flags: Vec<char> = groups.concat().chars().collect();
            for flag in &flags {
                assert!("Y.o~?".contains(*flag), "`{flag}` in `{line}`");
            }
            let label = line[..line.len() - groups.join(" ").len()]
                .trim()
                .to_owned();
            chips.insert(label, Chip { flags });
        }
        assert_eq!(chips.len(), 25, "the 8.1 matrix has 25 rows");
        Matrix { columns, chips }
    })
}

const I486_ROWS: &[&str] = &[
    "i486 SX; Am486 SX",
    "i486 DX,DX2; Am486 DX,DX2",
    "i486 DX4; Am486DX4; Am5x86",
];

/// The matrix rows each alias of SPEC 10.1 names, the one thing here not read from
/// a document, because the documents name the same chips differently.
const ALIAS_CHIPS: &[(&str, &[&str])] = &[
    ("386", &["i386 DX,SX; Am386 DX,SX"]),
    ("am386", &["i386 DX,SX; Am386 DX,SX"]),
    ("486", I486_ROWS),
    ("am486", I486_ROWS),
    ("am5x86", &["i486 DX4; Am486DX4; Am5x86"]),
    ("pentium", &["Pentium P5,P54C; K5", "Pentium MMX; K6"]),
    ("k5", &["Pentium P5,P54C; K5"]),
    ("k6", &["Pentium MMX; K6"]),
    ("k6-2", &["K6-2, K6-III"]),
    ("k6-3", &["K6-2, K6-III"]),
    ("pentiumpro", &["Pentium Pro"]),
    ("p2", &["Pentium II"]),
    ("p3", &["Pentium III"]),
    (
        "k7",
        &["K7 model 1", "K7 model 2-4, Duron", "K7 XP, MP, Morgan"],
    ),
    ("athlon-xp", &["K7 XP, MP, Morgan"]),
    (
        "p4",
        &["Willamette, Northwood", "Prescott", "Smithfield-Presler"],
    ),
    ("pentium-m", &["Pentium M"]),
    ("core-duo", &["Core Solo/Duo"]),
    (
        "atom",
        &["Bonnell Z5xx, N2xx", "Bonnell 64-bit", "Silvermont+ Atom"],
    ),
    ("core2", &["Core 2 65 nm", "Core 2 45 nm incl. Q8400"]),
    ("q8400", &["Core 2 45 nm incl. Q8400"]),
];

fn chips_of(alias: &str) -> &'static [&'static str] {
    ALIAS_CHIPS
        .iter()
        .find(|(name, _)| *name == alias)
        .unwrap_or_else(|| panic!("no chips for `{alias}`"))
        .1
}

pub fn register(h: &mut Harness) {
    not_a_line(h);
    per_alias(h);
    per_chip(h);
}

fn not_a_line(h: &mut Harness) {
    h.case("isa/K6 has MMX and lacks CMOV", || {
        let k6 = matrix().has("Pentium MMX; K6");
        assert!(k6.contains(Feature::Mmx));
        assert!(!k6.contains(Feature::Cmov));
    });
    h.case("isa/Pentium Pro has CMOV and lacks MMX", || {
        let pro = matrix().has("Pentium Pro");
        assert!(pro.contains(Feature::Cmov));
        assert!(!pro.contains(Feature::Mmx));
    });
    h.case(
        "isa/neither of K6 and Pentium Pro contains the other",
        || {
            let k6 = matrix().has("Pentium MMX; K6");
            let pro = matrix().has("Pentium Pro");
            assert!(!k6.contains_all(pro));
            assert!(!pro.contains_all(k6));
            assert!(k6.missing(pro).contains(Feature::Cmov));
            assert!(pro.missing(k6).contains(Feature::Mmx));
        },
    );
    h.case("isa/ARCHITECTURE 7.14 states the same two chips", || {
        let text = section("ARCHITECTURE.md", "### 7.14 Level enforcement");
        assert!(text.contains("K6 has MMX and lacks CMOV"), "{text}");
        assert!(
            text.contains("Pentium Pro has CMOV and lacks MMX"),
            "{text}"
        );
    });
    h.case(
        "isa/K6's alias stays at i586: i686 needs CMOV and FCOMI",
        || {
            let matrix = matrix();
            let chip = "Pentium MMX; K6";
            assert!(matrix.runs(chip, CpuLevel::I586));
            assert!(!matrix.runs(chip, CpuLevel::I686));
            let lacking = matrix.has(chip).missing(matrix.testable(CpuLevel::I686));
            assert_eq!(lacking, features(&["cmov", "fcomi"]));

            let built = spec("i386-linux", &cpu("k6"));
            assert_eq!(built.cpu, CpuLevel::I586);
            assert!(
                !built.allowed.contains(Feature::Cmov),
                "K6 would fault on it"
            );
        },
    );
    h.case("isa/K6-2 has 3DNow!, and it buys no higher rung", || {
        let matrix = matrix();
        let chip = "K6-2, K6-III";
        assert!(matrix.has(chip).contains(Feature::Amd3dnow));
        assert!(!matrix.runs(chip, CpuLevel::I686));
        assert_eq!(
            CpuAlias::find("k6-2").map(|a| a.level32),
            Some(CpuLevel::I586)
        );
    });
    h.case(
        "isa/Pentium III has SSE without SSE2, so it stays at i686",
        || {
            let matrix = matrix();
            let chip = "Pentium III";
            assert!(matrix.has(chip).contains(Feature::Sse));
            assert!(!matrix.has(chip).contains(Feature::Sse2));
            assert!(matrix.runs(chip, CpuLevel::I686));
            assert!(!matrix.runs(chip, CpuLevel::Sse2));
        },
    );
    h.case(
        "isa/K7 XP has SSE and 3DNow!, not SSE2, so it stays at i686",
        || {
            let matrix = matrix();
            let chip = "K7 XP, MP, Morgan";
            assert!(matrix.has(chip).contains_all(features(&["sse", "3dnow"])));
            assert!(!matrix.runs(chip, CpuLevel::Sse2));
            assert_eq!(
                CpuAlias::find("athlon-xp").map(|a| a.level32),
                Some(CpuLevel::I686)
            );
        },
    );
    h.case("isa/an i386 has neither BSWAP nor a sure FPU", || {
        let matrix = matrix();
        let chip = "i386 DX,SX; Am386 DX,SX";
        assert!(!matrix.runs(chip, CpuLevel::I486));
        assert_eq!(matrix.flag(chip, Feature::Fpu), 'o', "an external option");
        assert!(!matrix.has(chip).contains(Feature::Fpu));
    });
    h.case("isa/the matrix's rows are not totally ordered", || {
        let matrix = matrix();
        let incomparable = matrix.chips.keys().any(|a| {
            matrix.chips.keys().any(|b| {
                !matrix.has(a).contains_all(matrix.has(b))
                    && !matrix.has(b).contains_all(matrix.has(a))
            })
        });
        assert!(incomparable, "a line would need every pair comparable");
    });
    h.case(
        "isa/every alias has chips and every chip row is reached",
        || {
            assert_eq!(ALIAS_CHIPS.len(), CPU_ALIASES.len());
            for alias in CPU_ALIASES {
                for chip in chips_of(alias.name) {
                    assert!(matrix().chips.contains_key(*chip), "`{chip}`");
                }
            }
        },
    );
}

fn per_alias(h: &mut Harness) {
    for alias in CPU_ALIASES {
        let name = alias.name;
        h.case(
            format!("chips/{name}/sits at the highest rung"),
            move || {
                let matrix = matrix();
                let chips = chips_of(name);
                let highest = CpuLevel::for_arch(Arch::I386)
                    .iter()
                    .copied()
                    .filter(|level| chips.iter().all(|chip| matrix.runs(chip, *level)))
                    .max()
                    .expect("every chip runs the floor");
                assert_eq!(CpuAlias::find(name).unwrap().level32, highest);
            },
        );
        // Level `sse2` is the top of the 32-bit ladder, so it has no next rung.
        if alias.level32 != CpuLevel::Sse2 {
            let next = CpuLevel::ALL[CpuLevel::ALL
                .iter()
                .position(|l| *l == alias.level32)
                .unwrap()
                + 1];
            h.case(
                format!("chips/{name}/the next rung is out of reach"),
                move || {
                    let matrix = matrix();
                    let chips = chips_of(name);
                    assert!(
                        chips.iter().any(|chip| !matrix.runs(chip, next)),
                        "{chips:?} all run {next:?}"
                    );
                },
            );
        }
        h.case(format!("chips/{name}/long mode"), move || {
            let matrix = matrix();
            let flags: Vec<char> = chips_of(name)
                .iter()
                .map(|chip| matrix.flag(chip, Feature::Lm))
                .collect();
            let want = if flags.iter().all(|flag| *flag == 'Y') {
                LongMode::All
            } else if flags.iter().any(|flag| *flag != '.') {
                LongMode::SomeModels
            } else {
                LongMode::None
            };
            assert_eq!(CpuAlias::find(name).unwrap().long_mode, want, "{flags:?}");
        });
    }
}

fn per_chip(h: &mut Harness) {
    // Every model with long mode can run the x86-64 rung: that is what makes the
    // alias on a 64-bit target honest for the models it covers.
    for chip in matrix().chips.keys() {
        let chip = chip.clone();
        h.case(format!("chips/row/{chip}"), move || {
            let matrix = matrix();
            let long_mode = matrix.has(&chip).contains(Feature::Lm);
            assert_eq!(
                matrix.runs(&chip, CpuLevel::X86_64),
                long_mode,
                "lacking {}",
                matrix.has(&chip).missing(matrix.testable(CpuLevel::X86_64))
            );
        });
    }
}
