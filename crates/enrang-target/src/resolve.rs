//! From a target name and the command line's flags to a [`TargetSpec`].

use enrang_diag::{Code, Diagnostic, Help, did_you_mean};

use crate::features::Feature;
use crate::level::{CPU_ALIASES, CpuAlias, CpuLevel, LongMode};
use crate::presets::{
    FOREIGN_WIN64, PE_FILE_ALIGN, PE_SECTION_ALIGN, SUBSYSTEM_EFI, limit_reserve, preset,
};
use crate::spec::{
    Arch, FloatStrategy, ImageKind, OsLayer, OutputFormat, TargetSpec, TargetUsize, TraceLevel,
};

const TARGETS: &[&str] = &[
    "x86_64-linux",
    "x86_64-windows",
    "i386-linux",
    "i386-none",
    "x86_64-none",
    "vm64",
    "vm32",
];

/// What `--target=` takes (ARCHITECTURE 11). The VM rows are chosen by `run --vm
/// --layout=`, so no message offers them.
const NATIVE_TARGETS: &[&str] = &[
    "x86_64-linux",
    "x86_64-windows",
    "i386-linux",
    "i386-none",
    "x86_64-none",
];

/// What `--float=` takes (ARCHITECTURE 11).
const FLOATS: &[&str] = &["soft", "sse2", "x87"];
const FORMATS: &[&str] = &["elf", "pe", "flat", "efi"];
const IMAGES: &[&str] = &["floppy", "hdd"];
const TRACES: &[&str] = &["full", "fn", "none"];

/// Every target, in the order of the table in ARCHITECTURE 2.7.
pub fn all_targets() -> &'static [&'static str] {
    TARGETS
}

/// The target of the machine running the compiler, which only ever runs on a
/// modern x86-64 machine: `enrang run` builds for this.
pub fn host_target() -> &'static str {
    if cfg!(windows) {
        "x86_64-windows"
    } else {
        "x86_64-linux"
    }
}

/// The flags that shape a target, as written on the command line.
#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub struct TargetOpts {
    pub cpu: Option<String>,
    pub float: Option<String>,
    pub format: Option<String>,
    pub image: Option<String>,
    pub base: Option<u64>,
    pub trace: Option<String>,
    pub stack_size: Option<u64>,
}

/// Resolves a target, and returns it with any notes to print: one naming the level
/// when `--cpu` was an alias, and none otherwise.
///
/// The first problem found is the error, in the order target, `--cpu`, `--float`,
/// `--format`, `--image`, `--base`, `--stack-size`, `--trace`.
pub fn resolve(name: &str, opts: &TargetOpts) -> Result<(TargetSpec, Vec<Diagnostic>), Diagnostic> {
    let mut spec = preset(name).ok_or_else(|| unknown_target(name))?;

    let mut alias = None;
    let mut notes = Vec::new();
    if let Some(cpu) = opts.cpu.as_deref() {
        let level = resolve_cpu(cpu, &spec)?;
        spec.cpu = level;
        spec.allowed = level.features(spec.arch);
        alias = CpuAlias::find(cpu);
        if let Some(alias) = alias {
            notes.push(alias_note(alias, level));
        }
    }

    spec.float = resolve_float(opts.float.as_deref(), &spec, alias)?;
    if spec.stack.limit_check {
        spec.stack.limit_reserve = limit_reserve(spec.float);
    }

    if spec.arch == Arch::Mir {
        reject_vm_flags(&spec, opts)?;
    } else {
        apply_format(opts, &mut spec)?;
        apply_image(opts, &mut spec)?;
        apply_base(opts, &mut spec)?;
        apply_stack_size(opts, &mut spec)?;
        apply_trace(opts, &mut spec)?;
    }
    Ok((spec, notes))
}

/// `a`, `b` and `c`.
fn code_list(names: &[&str]) -> String {
    let mut list = String::new();
    for (index, name) in names.iter().enumerate() {
        if index > 0 {
            list.push_str(if index + 1 == names.len() {
                " and "
            } else {
                ", "
            });
        }
        list.push('`');
        list.push_str(name);
        list.push('`');
    }
    list
}

/// A help offering the candidate closest to `written`, spelled by `shape`. A
/// candidate differing only in case beats any other at the same distance: `I386`
/// means `i386`, not `386`.
fn with_suggestion(
    diag: Diagnostic,
    written: &str,
    candidates: &[&str],
    shape: impl Fn(&str) -> String,
) -> Diagnostic {
    let same_but_case = candidates
        .iter()
        .find(|candidate| candidate.eq_ignore_ascii_case(written))
        .copied();
    match same_but_case.or_else(|| did_you_mean(written, candidates)) {
        Some(found) => diag.with_help(Help::text(format!("did you mean `{}`?", shape(found)))),
        None => diag,
    }
}

/// A flag's value that is not one of `values`.
fn unknown_value(flag: &str, value: &str, kind: &str, values: &[&str]) -> Diagnostic {
    let diag = flag_error(
        format!("`{flag}={value}` is not {kind}"),
        format!("the values of `{flag}` are {}", code_list(values)),
    );
    with_suggestion(diag, value, values, |found| format!("{flag}={found}"))
}

/// An invalid flag or combination of flags, on any target.
fn flag_error(message: impl Into<String>, note: impl Into<String>) -> Diagnostic {
    Diagnostic::spanless(Code::EN1304, message).note(note)
}

fn unknown_target(name: &str) -> Diagnostic {
    if name == "i386-windows" {
        return Diagnostic::spanless(Code::EN1031, "32-bit Windows output is not supported yet")
            .note("Windows output is 64-bit only; nothing has been built for 32-bit Windows")
            .with_help(Help::text(
                "`x86_64-windows`; `i386-linux` for 32-bit testing",
            ));
    }
    let diag = Diagnostic::spanless(Code::EN1303, format!("unknown target `{name}`"))
        .note(format!("targets are {}", code_list(NATIVE_TARGETS)));
    with_suggestion(diag, name, NATIVE_TARGETS, str::to_owned)
}

/// The levels and aliases `--cpu` can name on `arch`.
fn cpu_candidates(arch: Arch) -> Vec<&'static str> {
    let levels = CpuLevel::for_arch(arch).iter().map(|level| level.name());
    let aliases = CPU_ALIASES
        .iter()
        .filter(|alias| alias.level_on(arch).is_some())
        .map(|alias| alias.name);
    levels.chain(aliases).collect()
}

fn resolve_cpu(cpu: &str, spec: &TargetSpec) -> Result<CpuLevel, Diagnostic> {
    if spec.arch == Arch::Mir {
        let name = spec.name;
        return Err(Diagnostic::spanless(
            Code::EN0912,
            format!("`--cpu={cpu}` does not apply to target `{name}`"),
        )
        .note(format!(
            "the VM interprets MIR, so target `{name}` has no CPU level"
        )));
    }
    if cpu == "native" {
        return Err(Diagnostic::spanless(Code::EN0909, "`--cpu=native` is rejected")
            .note("the host is never the target: output runs on the chips it was built for, not on the machine building it")
            .with_help(Help::text("name a level or a chip; `enrang targets` lists them")));
    }
    let alias = CpuAlias::find(cpu);
    let named = alias
        .map(|alias| alias.level32)
        .or(CpuLevel::from_name(cpu));
    let Some(named) = named else {
        return Err(unknown_cpu(cpu, spec));
    };
    let applies = match alias {
        Some(alias) => alias.level_on(spec.arch),
        None => CpuLevel::for_arch(spec.arch)
            .contains(&named)
            .then_some(named),
    };
    applies.ok_or_else(|| level_does_not_apply(cpu, named, alias.is_some(), spec))
}

fn unknown_cpu(cpu: &str, spec: &TargetSpec) -> Diagnostic {
    let levels: Vec<&str> = CpuLevel::for_arch(spec.arch)
        .iter()
        .map(|level| level.name())
        .collect();
    let note = if levels.is_empty() {
        format!("target `{}` has no CPU levels", spec.name)
    } else {
        format!(
            "levels on target `{}`: {}; `enrang targets` lists chip names too",
            spec.name,
            code_list(&levels)
        )
    };
    let diag =
        Diagnostic::spanless(Code::EN0909, format!("`--cpu={cpu}` is not a CPU level")).note(note);
    with_suggestion(diag, cpu, &cpu_candidates(spec.arch), |found| {
        format!("--cpu={found}")
    })
}

/// A real level or alias on a target it does not apply to (EN0912).
fn level_does_not_apply(
    cpu: &str,
    named: CpuLevel,
    is_alias: bool,
    spec: &TargetSpec,
) -> Diagnostic {
    let name = spec.name;
    let head = if is_alias {
        format!("`--cpu={cpu}` does not apply to target `{name}`")
    } else {
        format!("level `{cpu}` does not apply to target `{name}`")
    };
    let diag = Diagnostic::spanless(Code::EN0912, head);
    match spec.arch {
        Arch::Mir => unreachable!("`resolve_cpu` refuses every `--cpu` on a VM row first"),
        Arch::I386 => diag
            .note("level `x86-64` assumes long mode, and `i386-*` output runs in 32-bit mode")
            .with_help(Help::text(
                "`--cpu=sse2` is the highest level on `i386-*`; `--target=x86_64-linux` builds 64-bit output",
            )),
        Arch::X86_64 => {
            let target32 = if spec.is_freestanding() {
                "i386-none"
            } else {
                "i386-linux"
            };
            let build32 = format!("`--target={target32}` builds 32-bit output");
            if is_alias {
                diag.note(format!(
                    "`{cpu}` resolves to the 32-bit level `{}`, because those chips have no long mode",
                    named.name()
                ))
                .with_help(Help::text(build32))
            } else {
                diag.note("level `x86-64` is the only level on `x86_64-*`")
                    .with_help(Help::text(format!("`--cpu=x86-64`; {build32}")))
            }
        }
    }
}

fn alias_note(alias: &CpuAlias, level: CpuLevel) -> Diagnostic {
    let resolved = format!("`{}` resolves to level `{}`", alias.name, level.name());
    let text = if level == CpuLevel::X86_64 && alias.long_mode == LongMode::SomeModels {
        format!("{resolved}; this covers only its 64-bit models")
    } else {
        resolved
    };
    Diagnostic::bare_note(Code::EN0909, text)
}

fn resolve_float(
    float: Option<&str>,
    spec: &TargetSpec,
    alias: Option<&CpuAlias>,
) -> Result<FloatStrategy, Diagnostic> {
    let Some(float) = float else {
        return Ok(default_float(spec));
    };
    match float {
        "soft" | "x87" if spec.arch == Arch::X86_64 => Err(only_sse2_on_x86_64(float, spec)),
        "sse2" | "x87" if spec.arch == Arch::Mir => Err(not_in_the_vm(float, spec)),
        "soft" => Ok(FloatStrategy::Soft),
        "x87" => Ok(FloatStrategy::X87),
        "sse2" if spec.allowed.contains(Feature::Sse2) => Ok(FloatStrategy::Sse2),
        "sse2" => Err(float_needs_level(spec, alias)),
        other => Err(unknown_value("--float", other, "a float strategy", FLOATS)),
    }
}

/// The row's default, except that on `i386-*` the level picks it (SPEC 9.3 and 10,
/// ARCHITECTURE 2.7): `soft` at `i386` and `i486`, whose chips may have no FPU,
/// `x87` at `i586` and `i686`, and `sse2` at `sse2`.
fn default_float(spec: &TargetSpec) -> FloatStrategy {
    if spec.arch != Arch::I386 {
        return spec.float;
    }
    match spec.cpu {
        CpuLevel::I586 | CpuLevel::I686 => FloatStrategy::X87,
        CpuLevel::Sse2 => FloatStrategy::Sse2,
        _ => spec.float,
    }
}

/// SSE2 is part of the x86-64 baseline, so a software or x87 path there would be
/// another lowering with no chip that needs it (SPEC 9.3).
fn only_sse2_on_x86_64(float: &str, spec: &TargetSpec) -> Diagnostic {
    Diagnostic::spanless(
        Code::EN0911,
        format!("`--float={float}` does not apply to target `{}`", spec.name),
    )
    .note("every x86-64 CPU has SSE2, so `sse2` is the only float strategy on `x86_64-*`")
}

/// The VM's only float modes are the host's floats and `soft` (DEV_RUNTIME 2).
fn not_in_the_vm(float: &str, spec: &TargetSpec) -> Diagnostic {
    Diagnostic::spanless(
        Code::EN0911,
        format!("`--float={float}` does not apply to target `{}`", spec.name),
    )
    .note("the VM runs floats on the host, or under `--float=soft` through the soft-float library")
}

fn float_needs_level(spec: &TargetSpec, alias: Option<&CpuAlias>) -> Diagnostic {
    let needed = CpuLevel::lowest_with(Feature::Sse2, spec.arch).map_or("?", CpuLevel::name);
    let current = spec.cpu.name();
    let diag = Diagnostic::spanless(
        Code::EN0911,
        format!("`--float=sse2` needs level `{needed}`, and this build is at level `{current}`"),
    );
    let diag = match alias {
        Some(alias) => diag.note(format!("`{}` resolves to level `{current}`", alias.name)),
        None => diag,
    };
    diag.with_help(Help::text(format!("build for it: `--cpu={needed}`")))
        .with_help(Help::text(
            "or `--float=soft`, which works at every level and is bit-identical",
        ))
}

/// Native output's flags mean nothing to a VM row, which writes no file.
fn reject_vm_flags(spec: &TargetSpec, opts: &TargetOpts) -> Result<(), Diagnostic> {
    let given = [
        (opts.format.is_some(), "--format"),
        (opts.image.is_some(), "--image"),
        (opts.base.is_some(), "--base"),
        (opts.stack_size.is_some(), "--stack-size"),
        (opts.trace.is_some(), "--trace"),
    ];
    match given.into_iter().find(|(is_given, _)| *is_given) {
        Some((_, flag)) => Err(flag_error(
            format!("`{flag}` does not apply to target `{}`", spec.name),
            "the VM interprets MIR and writes no output file",
        )),
        None => Ok(()),
    }
}

fn apply_format(opts: &TargetOpts, spec: &mut TargetSpec) -> Result<(), Diagnostic> {
    let Some(format) = opts.format.as_deref() else {
        return Ok(());
    };
    if !FORMATS.contains(&format) {
        return Err(unknown_value(
            "--format",
            format,
            "an output format",
            FORMATS,
        ));
    }
    let freestanding = spec.is_freestanding();
    let fits = match format {
        "elf" => matches!(spec.format, OutputFormat::Elf32 | OutputFormat::Elf64),
        "pe" => matches!(spec.os, OsLayer::Win64Imports),
        "flat" => freestanding,
        _ => freestanding && spec.arch == Arch::X86_64,
    };
    if !fits {
        let builds: &[&str] = match spec.os {
            OsLayer::LinuxX64 | OsLayer::LinuxInt80 => &["elf"],
            OsLayer::Win64Imports => &["pe"],
            _ if spec.arch == Arch::X86_64 => &["flat", "efi"],
            _ => &["flat"],
        };
        return Err(flag_error(
            format!("`--format={format}` does not fit target `{}`", spec.name),
            format!("target `{}` builds {}", spec.name, code_list(builds)),
        ));
    }
    if format == "efi" {
        spec.format = OutputFormat::Pe {
            subsystem: SUBSYSTEM_EFI,
        };
        spec.os = OsLayer::Uefi;
        spec.foreign = FOREIGN_WIN64;
        // A PE image whatever the row's own output is (ARCHITECTURE 9.4).
        spec.image.section_align = PE_SECTION_ALIGN;
        spec.image.file_align = PE_FILE_ALIGN;
    }
    Ok(())
}

fn apply_image(opts: &TargetOpts, spec: &mut TargetSpec) -> Result<(), Diagnostic> {
    let Some(image) = opts.image.as_deref() else {
        return Ok(());
    };
    let kind = match image {
        "floppy" => ImageKind::Floppy144,
        "hdd" => ImageKind::Hdd,
        other => return Err(unknown_value("--image", other, "an image kind", IMAGES)),
    };
    if opts.format.is_some() {
        return Err(flag_error(
            "`--image` and `--format` cannot be combined",
            "`--image` already says what to write: a bootable disk image",
        ));
    }
    if !spec.is_freestanding() {
        return Err(flag_error(
            format!("`--image={image}` does not fit target `{}`", spec.name),
            "a bootable image needs a freestanding target: `i386-none` or `x86_64-none`",
        ));
    }
    spec.format = OutputFormat::BiosImage(kind);
    Ok(())
}

fn apply_base(opts: &TargetOpts, spec: &mut TargetSpec) -> Result<(), Diagnostic> {
    let Some(base) = opts.base else {
        return Ok(());
    };
    if !matches!(spec.format, OutputFormat::Flat | OutputFormat::BiosImage(_)) {
        return Err(flag_error(
            format!("`--base` does not fit target `{}`", spec.name),
            "only flat output and BIOS images take a link base",
        ));
    }
    let Some(TargetUsize(base)) = TargetUsize::checked(base, spec) else {
        return Err(flag_error(
            format!("`--base={base:#x}` does not fit target `{}`", spec.name),
            format!(
                "addresses on this target end at {:#x}",
                spec.layout.usize_max()
            ),
        ));
    };
    spec.image.base = base;
    Ok(())
}

fn apply_stack_size(opts: &TargetOpts, spec: &mut TargetSpec) -> Result<(), Diagnostic> {
    let Some(size) = opts.stack_size else {
        return Ok(());
    };
    if !spec.is_freestanding() && spec.os != OsLayer::Win64Imports {
        return Err(flag_error(
            format!("`--stack-size` does not fit target `{}`", spec.name),
            "it sets the freestanding stack or the PE reserve, and on Linux the OS sizes the stack",
        ));
    }
    if size == 0 || size > spec.layout.isize_max() {
        return Err(flag_error(
            format!("`--stack-size={size}` does not fit target `{}`", spec.name),
            format!(
                "a stack is at least 1 byte and at most {} bytes on this target",
                spec.layout.isize_max()
            ),
        ));
    }
    spec.stack.size = size;
    Ok(())
}

fn apply_trace(opts: &TargetOpts, spec: &mut TargetSpec) -> Result<(), Diagnostic> {
    let Some(trace) = opts.trace.as_deref() else {
        return Ok(());
    };
    spec.trace = match trace {
        "full" => TraceLevel::Full,
        "fn" => TraceLevel::Fn,
        "none" => TraceLevel::None,
        other => return Err(unknown_value("--trace", other, "a trace level", TRACES)),
    };
    Ok(())
}
