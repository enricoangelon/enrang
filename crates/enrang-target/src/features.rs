//! CPU features and sets of them (ARCHITECTURE 7.14).

use std::fmt;

/// Generates [`Feature`] from one row per feature. The rows before the semicolon
/// are what `cpu.has` can name; the rows after it are tags for the encoder only.
macro_rules! define_features {
    (
        $($public:ident $public_name:literal,)*
        ;
        $($internal:ident $internal_name:literal,)*
    ) => {
        /// Something an instruction form may need that not every listed chip has.
        #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
        pub enum Feature {
            $($public,)*
            $($internal,)*
        }

        impl Feature {
            /// Every feature, in the order of its row.
            pub const ALL: &'static [Feature] = &[
                $(Feature::$public,)*
                $(Feature::$internal,)*
            ];

            /// The features `cpu.has` can name, in the order SPEC 10.3 lists them.
            pub const QUERYABLE: &'static [Feature] = &[$(Feature::$public,)*];

            /// The feature's spelling in `cpu.has`, `@requires` and diagnostics.
            pub const fn name(self) -> &'static str {
                match self {
                    $(Feature::$public => $public_name,)*
                    $(Feature::$internal => $internal_name,)*
                }
            }
        }
    };
}

define_features! {
    Fpu "fpu", Cpuid "cpuid", Bswap "bswap", Cmpxchg "cmpxchg", Xadd "xadd", Cmpxchg8b "cmpxchg8b",
    Rdtsc "rdtsc", Msr "msr", Cr4 "cr4", Cmov "cmov", Fcomi "fcomi", Mmx "mmx", Amd3dnow "3dnow",
    Sse "sse", Sse2 "sse2", Sse3 "sse3", Ssse3 "ssse3", Sse41 "sse4.1", Sse42 "sse4.2", Popcnt "popcnt",
    Fxsave "fxsave", Nopl "nopl", Pae "pae", Nx "nx", Lm "lm", Invlpg "invlpg",
    ;
    Ud2 "ud2",      // internal tag, P6 and up
    Ia32 "ia32",    // internal tag on every form outside the 8086 subset
}

const _: () = assert!(Feature::ALL.len() <= u32::BITS as usize);

impl Feature {
    /// The feature spelled `name`, internal tags included.
    pub fn from_name(name: &str) -> Option<Feature> {
        Feature::ALL.iter().copied().find(|f| f.name() == name)
    }

    /// The feature `cpu.has(name)` asks about. An internal tag is not one (EN0908).
    pub fn from_cpu_has(name: &str) -> Option<Feature> {
        Feature::QUERYABLE
            .iter()
            .copied()
            .find(|f| f.name() == name)
    }

    /// Whether `cpu.has` can name this feature.
    pub fn queryable(self) -> bool {
        Feature::QUERYABLE.contains(&self)
    }

    const fn bit(self) -> u32 {
        1 << self as u32
    }
}

/// A set of features. Levels are sets rather than points on a line because the ISA
/// is not a line: K6 has MMX and lacks CMOV, Pentium Pro has CMOV and lacks MMX.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Default)]
pub struct FeatureSet(u32);

impl FeatureSet {
    pub const EMPTY: FeatureSet = FeatureSet(0);

    pub const fn of(features: &[Feature]) -> FeatureSet {
        let mut bits = 0;
        let mut i = 0;
        while i < features.len() {
            bits |= features[i].bit();
            i += 1;
        }
        FeatureSet(bits)
    }

    pub const fn union(self, other: FeatureSet) -> FeatureSet {
        FeatureSet(self.0 | other.0)
    }

    pub const fn contains(self, feature: Feature) -> bool {
        self.0 & feature.bit() != 0
    }

    /// Whether every feature of `other` is in this set: `allowed.contains_all(form)`.
    pub const fn contains_all(self, other: FeatureSet) -> bool {
        other.0 & !self.0 == 0
    }

    /// The features of `other` this set lacks: `allowed.missing(form)` is what a
    /// form needs beyond the level, and is empty exactly when `contains_all` holds.
    pub const fn missing(self, other: FeatureSet) -> FeatureSet {
        FeatureSet(other.0 & !self.0)
    }

    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// The set's features, in the order of their rows.
    pub fn iter(self) -> impl Iterator<Item = Feature> {
        Feature::ALL
            .iter()
            .copied()
            .filter(move |&f| self.contains(f))
    }
}

/// The names, separated by spaces.
impl fmt::Display for FeatureSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (index, feature) in self.iter().enumerate() {
            if index > 0 {
                f.write_str(" ")?;
            }
            f.write_str(feature.name())?;
        }
        Ok(())
    }
}

impl fmt::Debug for FeatureSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FeatureSet({self})")
    }
}
