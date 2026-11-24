//! `enrang targets [--evidence]` (ARCHITECTURE 11).

use enrang_diag::{CURRENT_MILESTONE, did_you_mean, shown};
use enrang_target::{
    Arch, CPU_ALIASES, CpuAlias, CpuLevel, FeatureSet, LongMode, OsLayer, OutputFormat, TargetOpts,
    TargetSpec, all_targets, resolve,
};

use crate::commands::{LATER, TARGETS};
use crate::evidence;
use crate::outcome::Outcome;
use crate::report::complaint;
use crate::table::table;

const USAGE: &str = "enrang targets [--evidence]";

pub(crate) fn command(args: &[String]) -> Outcome {
    match args {
        [] => Outcome::print(listing()),
        [flag] if flag == "--evidence" => Outcome::print(evidence::text()),
        [flag] if flag == "--help" || flag == "-h" => Outcome::print(help()),
        [other] => {
            let suggestion = did_you_mean(other, &["--evidence", "--help"]);
            let help = suggestion.map(|flag| format!("did you mean `{flag}`?"));
            complaint(
                &format!("`{}` is not a flag of `enrang targets`", shown(other)),
                help.as_deref(),
                Some(USAGE),
            )
        }
        [..] => complaint("`enrang targets` takes one flag at most", None, Some(USAGE)),
    }
}

fn help() -> String {
    format!("{}.\n\nUsage: {USAGE}\n", TARGETS.summary)
}

fn listing() -> String {
    format!(
        "Targets:\n\n{}\nCPU levels, the values --cpu will take:\n\n{}\nCPU aliases, which --cpu will accept in place of a level:\n\n{}\n{}",
        table(&target_rows()),
        table(&level_rows()),
        table(&alias_rows()),
        closing(),
    )
}

/// What the tables are worth today: nothing can be built for a target until `build`
/// arrives.
fn closing() -> String {
    match LATER.iter().find(|command| command.name == "build") {
        Some(build) => format!(
            "These are design tables. This is milestone {CURRENT_MILESTONE}, and `enrang build` arrives with milestone {},\nso nothing can be built for any target yet.\n",
            build.since
        ),
        None => "These are design tables.\n".to_owned(),
    }
}

fn row(cells: &[&str]) -> Vec<String> {
    cells.iter().map(|cell| (*cell).to_owned()).collect()
}

fn target_rows() -> Vec<Vec<String>> {
    let mut rows = vec![row(&[
        "target",
        "code",
        "pointer",
        "default --cpu",
        "float",
        "output",
        "os",
    ])];
    for name in all_targets() {
        let (spec, _) = resolve(name, &TargetOpts::default())
            .expect("every listed target resolves with no flags");
        let code = match spec.arch {
            Arch::I386 => "i386",
            Arch::X86_64 => "x86-64",
            Arch::Mir => "vm",
        };
        rows.push(row(&[
            name,
            code,
            &format!("{} bytes", spec.layout.ptr_bytes),
            default_level(&spec),
            spec.float.name(),
            output_name(spec.format),
            os_name(spec.os),
        ]));
    }
    rows
}

/// A VM row carries the level of its native twin, but `--cpu` means nothing there.
fn default_level(spec: &TargetSpec) -> &'static str {
    if CpuLevel::for_arch(spec.arch).is_empty() {
        "none"
    } else {
        spec.cpu.name()
    }
}

fn output_name(format: OutputFormat) -> &'static str {
    match format {
        OutputFormat::Elf64 => "elf64",
        OutputFormat::Elf32 => "elf32",
        OutputFormat::Pe { .. } => "pe32+",
        OutputFormat::Flat => "flat",
        OutputFormat::BiosImage(_) => "image",
        OutputFormat::None => "none",
    }
}

fn os_name(os: OsLayer) -> &'static str {
    match os {
        OsLayer::LinuxX64 => "linux",
        OsLayer::LinuxInt80 => "linux, int 0x80",
        OsLayer::Win64Imports => "windows",
        OsLayer::None => "none",
        OsLayer::Uefi => "uefi",
        OsLayer::Vm => "vm",
    }
}

/// The names in `set`, without the encoder's internal tags.
fn queryable_names(set: FeatureSet) -> Vec<&'static str> {
    set.iter()
        .filter(|feature| feature.queryable())
        .map(|feature| feature.name())
        .collect()
}

fn level_rows() -> Vec<Vec<String>> {
    let mut rows = vec![row(&["level", "targets", "code may assume"])];
    for arch in [Arch::I386, Arch::X86_64] {
        let targets = match arch {
            Arch::I386 => "i386-*",
            _ => "x86_64-*",
        };
        let mut below = FeatureSet::EMPTY;
        for level in CpuLevel::for_arch(arch) {
            let features = level.features(arch);
            let added = queryable_names(below.missing(features)).join(" ");
            let assume = if added.is_empty() {
                "80386 integer only".to_owned()
            } else if below == FeatureSet::EMPTY {
                added
            } else {
                format!("+ {added}")
            };
            rows.push(row(&[level.name(), targets, &assume]));
            below = features;
        }
    }
    rows
}

fn alias_rows() -> Vec<Vec<String>> {
    let mut rows = vec![row(&["alias", "on i386-*", "on x86_64-*"])];
    for alias in CPU_ALIASES {
        rows.push(row(&[
            alias.name,
            alias.level32.name(),
            &long_mode_cell(alias),
        ]));
    }
    rows
}

fn long_mode_cell(alias: &CpuAlias) -> String {
    let level = alias.level_on(Arch::X86_64);
    match (alias.long_mode, level) {
        (LongMode::All, Some(level)) => level.name().to_owned(),
        (LongMode::SomeModels, Some(level)) => format!("{}, 64-bit models only", level.name()),
        _ => "EN0912, no long mode".to_owned(),
    }
}
