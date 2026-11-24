//! The `--cpu` ladder and its chip-name aliases (SPEC 10.1, ARCHITECTURE 8.2).

use crate::features::Feature::*;
use crate::features::{Feature, FeatureSet};
use crate::spec::Arch;

/// A rung of the ladder. The order is the ladder's.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum CpuLevel {
    I386,
    I486,
    I586,
    I686,
    Sse2,
    X86_64,
}

const I386_SET: FeatureSet = FeatureSet::of(&[Ia32]);
const I486_SET: FeatureSet = I386_SET.union(FeatureSet::of(&[Bswap, Cmpxchg, Xadd, Invlpg]));
const I586_SET: FeatureSet = I486_SET.union(FeatureSet::of(&[Cpuid, Cmpxchg8b, Rdtsc, Msr, Cr4]));
const I686_SET: FeatureSet = I586_SET.union(FeatureSet::of(&[Cmov, Fcomi, Ud2]));
const SSE2_SET: FeatureSet = I686_SET.union(FeatureSet::of(&[Sse, Sse2, Fxsave]));
const X86_64_SET: FeatureSet = FeatureSet::of(&[
    Ia32, Cpuid, Cmpxchg8b, Cmpxchg, Xadd, Bswap, Rdtsc, Msr, Cmov, Fcomi, Fpu, Ud2, Sse, Sse2,
    Fxsave, Nopl, Lm, Invlpg, Cr4, Pae,
]);

impl CpuLevel {
    /// Every rung, lowest first.
    pub const ALL: [CpuLevel; 6] = [
        CpuLevel::I386,
        CpuLevel::I486,
        CpuLevel::I586,
        CpuLevel::I686,
        CpuLevel::Sse2,
        CpuLevel::X86_64,
    ];

    /// The level's spelling in `--cpu`.
    pub const fn name(self) -> &'static str {
        match self {
            CpuLevel::I386 => "i386",
            CpuLevel::I486 => "i486",
            CpuLevel::I586 => "i586",
            CpuLevel::I686 => "i686",
            CpuLevel::Sse2 => "sse2",
            CpuLevel::X86_64 => "x86-64",
        }
    }

    /// The level spelled `name`. An alias is not a level: see [`CpuAlias::find`].
    pub fn from_name(name: &str) -> Option<CpuLevel> {
        CpuLevel::ALL.into_iter().find(|l| l.name() == name)
    }

    /// The rungs `--cpu` can ask for on `arch`, lowest first. The VM has none.
    pub const fn for_arch(arch: Arch) -> &'static [CpuLevel] {
        match arch {
            Arch::I386 => &[
                CpuLevel::I386,
                CpuLevel::I486,
                CpuLevel::I586,
                CpuLevel::I686,
                CpuLevel::Sse2,
            ],
            Arch::X86_64 => &[CpuLevel::X86_64],
            Arch::Mir => &[],
        }
    }

    pub(crate) const fn table_set(self) -> FeatureSet {
        match self {
            CpuLevel::I386 => I386_SET,
            CpuLevel::I486 => I486_SET,
            CpuLevel::I586 => I586_SET,
            CpuLevel::I686 => I686_SET,
            CpuLevel::Sse2 => SSE2_SET,
            CpuLevel::X86_64 => X86_64_SET,
        }
    }

    /// What code at this level may assume on `arch`. A level that does not apply
    /// to `arch` provides nothing, so such a pairing can never widen an allowed set.
    /// A VM row carries the level of its native twin, so on `Mir` every level keeps
    /// its table entry.
    pub fn features(self, arch: Arch) -> FeatureSet {
        if arch == Arch::Mir || CpuLevel::for_arch(arch).contains(&self) {
            self.table_set()
        } else {
            FeatureSet::EMPTY
        }
    }

    /// The lowest rung of `arch` providing `feature`, which EN0901 names. `None`
    /// when no rung has it, as for MMX, or when `arch` has no rungs.
    pub fn lowest_with(feature: Feature, arch: Arch) -> Option<CpuLevel> {
        CpuLevel::for_arch(arch)
            .iter()
            .copied()
            .find(|level| level.features(arch).contains(feature))
    }
}

/// How the chips behind an alias relate to long mode.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum LongMode {
    /// None has it: on `x86_64-*` the alias is EN0912.
    None,
    /// Only some models have it: on `x86_64-*` the note says so.
    SomeModels,
    /// All have it.
    All,
}

/// A chip name `--cpu` accepts in place of a level. It prints a note.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct CpuAlias {
    pub name: &'static str,
    /// The rung on a 32-bit target.
    pub level32: CpuLevel,
    pub long_mode: LongMode,
}

const fn alias(name: &'static str, level32: CpuLevel, long_mode: LongMode) -> CpuAlias {
    CpuAlias {
        name,
        level32,
        long_mode,
    }
}

/// Every alias of SPEC 10.1, in its order.
pub const CPU_ALIASES: &[CpuAlias] = &[
    alias("386", CpuLevel::I386, LongMode::None),
    alias("am386", CpuLevel::I386, LongMode::None),
    alias("486", CpuLevel::I486, LongMode::None),
    alias("am486", CpuLevel::I486, LongMode::None),
    alias("am5x86", CpuLevel::I486, LongMode::None),
    alias("pentium", CpuLevel::I586, LongMode::None),
    alias("k5", CpuLevel::I586, LongMode::None),
    alias("k6", CpuLevel::I586, LongMode::None),
    alias("k6-2", CpuLevel::I586, LongMode::None),
    alias("k6-3", CpuLevel::I586, LongMode::None),
    alias("pentiumpro", CpuLevel::I686, LongMode::None),
    alias("p2", CpuLevel::I686, LongMode::None),
    alias("p3", CpuLevel::I686, LongMode::None),
    alias("k7", CpuLevel::I686, LongMode::None),
    alias("athlon-xp", CpuLevel::I686, LongMode::None),
    alias("p4", CpuLevel::Sse2, LongMode::SomeModels),
    alias("pentium-m", CpuLevel::Sse2, LongMode::None),
    alias("core-duo", CpuLevel::Sse2, LongMode::None),
    alias("atom", CpuLevel::Sse2, LongMode::SomeModels),
    alias("core2", CpuLevel::Sse2, LongMode::All),
    alias("q8400", CpuLevel::Sse2, LongMode::All),
];

impl CpuAlias {
    pub fn find(name: &str) -> Option<&'static CpuAlias> {
        CPU_ALIASES.iter().find(|alias| alias.name == name)
    }

    /// The rung this alias resolves to on `arch`, if any: `None` on the VM, and on
    /// `x86_64` for chips with no long mode.
    pub const fn level_on(&self, arch: Arch) -> Option<CpuLevel> {
        match (arch, self.long_mode) {
            (Arch::I386, _) => Some(self.level32),
            (Arch::X86_64, LongMode::SomeModels | LongMode::All) => Some(CpuLevel::X86_64),
            (Arch::X86_64, LongMode::None) | (Arch::Mir, _) => None,
        }
    }
}
