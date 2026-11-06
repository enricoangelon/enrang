//! What holds for every call of `resolve`: the whole cross product of target, level
//! and float strategy, then random flags at every boundary.

use enrang_diag::{Code, Diagnostic, Phase, Severity};
use enrang_target::{
    Arch, CPU_ALIASES, CpuAlias, CpuLevel, Feature, FloatStrategy, TargetOpts, TargetSpec,
    TargetUsize, resolve,
};
use enrang_testkit::{Harness, Rng, Xoshiro256, rng_for, scaled};

use crate::support::{TARGETS, arch_of, opts_with, render};

/// Every `--cpu` value worth trying: none, each level, each alias, and two refusals.
fn cpu_values() -> Vec<Option<String>> {
    let mut values = vec![None];
    values.extend(CpuLevel::ALL.iter().map(|l| Some(l.name().to_owned())));
    values.extend(CPU_ALIASES.iter().map(|a| Some(a.name.to_owned())));
    values.push(Some("native".to_owned()));
    values.push(Some("bogus".to_owned()));
    values
}

const FLOATS: [Option<&str>; 5] = [None, Some("soft"), Some("sse2"), Some("x87"), Some("bogus")];

/// What the spec says the code must be.
fn expected_code(target: &str, cpu: Option<&str>, float: Option<&str>) -> Option<Code> {
    let arch = arch_of(target);
    let mut level = match arch {
        Arch::I386 => CpuLevel::I386,
        Arch::X86_64 | Arch::Mir => CpuLevel::X86_64,
    };
    if let Some(cpu) = cpu {
        if arch == Arch::Mir {
            return Some(Code::EN0912);
        }
        if cpu == "native" || cpu == "bogus" {
            return Some(Code::EN0909);
        }
        level = match CpuAlias::find(cpu) {
            Some(alias) => match alias.level_on(arch) {
                Some(level) => level,
                None => return Some(Code::EN0912),
            },
            None => {
                let named = CpuLevel::from_name(cpu).expect("a level");
                if !CpuLevel::for_arch(arch).contains(&named) {
                    return Some(Code::EN0912);
                }
                named
            }
        };
    }
    match float {
        None => None,
        Some("soft") if arch == Arch::X86_64 => Some(Code::EN0911),
        Some("soft") => None,
        Some("x87") => Some(Code::EN1020),
        Some("sse2") => match arch {
            Arch::Mir => Some(Code::EN0911),
            _ if level >= CpuLevel::Sse2 => None,
            _ => Some(Code::EN0911),
        },
        Some(_) => Some(Code::EN1304),
    }
}

fn check_spec(target: &str, built: &TargetSpec, cpu: Option<&str>, float: Option<&str>) {
    assert_eq!(built.name, target);
    assert_eq!(built.arch, arch_of(target));
    assert_eq!(built.allowed, built.cpu.features(built.arch));
    assert!(built.allowed.contains_all(built.floor));
    assert!(built.allowed.contains(Feature::Ia32));
    assert_ne!(built.float, FloatStrategy::X87);
    if built.float == FloatStrategy::Sse2 {
        assert!(
            built.allowed.contains(Feature::Sse2),
            "SSE2 code above the level"
        );
    }
    if built.arch != Arch::Mir {
        assert!(CpuLevel::for_arch(built.arch).contains(&built.cpu));
        assert_ne!(
            built.float,
            FloatStrategy::Host,
            "the host float is VM-only"
        );
    }
    if float == Some("soft") {
        assert_eq!(built.float, FloatStrategy::Soft);
    }
    if cpu.is_none() {
        let floor = match built.arch {
            Arch::I386 => CpuLevel::I386,
            Arch::X86_64 => CpuLevel::X86_64,
            Arch::Mir => built.cpu,
        };
        assert_eq!(built.cpu, floor, "SPEC 10.1's default");
    }
}

fn check_note(printed: &[Diagnostic], built: &TargetSpec, cpu: Option<&str>) {
    match cpu.and_then(CpuAlias::find) {
        Some(alias) => {
            assert_eq!(printed.len(), 1);
            let note = &printed[0];
            assert_eq!(note.severity, Severity::Note);
            let rendered = render(printed);
            assert!(rendered.contains(alias.name), "{rendered}");
            assert!(rendered.contains(built.cpu.name()), "{rendered}");
            assert!(
                !rendered.contains("aborting"),
                "a note aborts nothing: {rendered}"
            );
        }
        None => assert!(printed.is_empty(), "{printed:?}"),
    }
}

/// SPEC 13.1's conventions, on any error `resolve` can return.
fn check_error(diag: &Diagnostic) {
    assert_eq!(diag.severity, Severity::Error);
    assert_eq!(diag.code.phase(), Phase::CommandLine, "{}", diag.code);
    assert!(diag.primary.span.is_dummy(), "no source was read yet");
    assert!(diag.secondary.is_empty());
    let first = diag.message.chars().next().expect("a message");
    assert!(
        first == '`' || first.is_ascii_lowercase() || first.is_ascii_digit(),
        "`{}` should start lower-case or with a code span",
        diag.message
    );
    assert!(
        !diag.message.ends_with('.'),
        "no final period: {}",
        diag.message
    );
    assert!(!diag.message.contains('\n'), "{}", diag.message);
    for help in &diag.helps {
        assert!(
            !help.message.contains('\n'),
            "a help is one line: {}",
            help.message
        );
    }
    let rendered = render(std::slice::from_ref(diag));
    assert!(
        rendered.starts_with(&format!("error[{}]: ", diag.code)),
        "{rendered}"
    );
    assert!(
        rendered.contains("aborting due to 1 previous error"),
        "{rendered}"
    );
}

pub fn register(h: &mut Harness) {
    cross_product(h);
    random(h);
}

fn cross_product(h: &mut Harness) {
    for target in TARGETS {
        h.case(format!("product/{target}"), move || {
            let mut built = 0;
            let mut refused = 0;
            for cpu in cpu_values() {
                for float in FLOATS {
                    let opts = opts_with(cpu.as_deref(), float);
                    let want = expected_code(target, cpu.as_deref(), float);
                    match resolve(target, &opts) {
                        Ok((spec, printed)) => {
                            assert_eq!(want, None, "{opts:?}");
                            check_spec(target, &spec, cpu.as_deref(), float);
                            check_note(&printed, &spec, cpu.as_deref());
                            built += 1;
                        }
                        Err(diag) => {
                            assert_eq!(Some(diag.code), want, "{opts:?}: {}", diag.message);
                            check_error(&diag);
                            refused += 1;
                        }
                    }
                }
            }
            assert!(refused > 0, "this product reaches refusals");
            assert!(built > 0, "and successes");
        });
    }
}

fn pick(rng: &mut Xoshiro256, values: &[&str]) -> Option<String> {
    // One draw in three leaves the flag off, so successes stay common.
    if rng.below(3) == 0 {
        return None;
    }
    Some(values[rng.below(values.len() as u64) as usize].to_owned())
}

fn random_opts(rng: &mut Xoshiro256) -> TargetOpts {
    let mut cpus: Vec<&str> = CpuLevel::ALL.iter().map(|l| l.name()).collect();
    cpus.extend(CPU_ALIASES.iter().map(|a| a.name));
    cpus.extend(["native", "", "x86_64", "I386", "k8"]);
    TargetOpts {
        cpu: pick(rng, &cpus),
        float: pick(rng, &["soft", "sse2", "x87", "host", ""]),
        format: pick(rng, &["elf", "pe", "flat", "efi", "coff", ""]),
        image: pick(rng, &["floppy", "hdd", "cdrom", ""]),
        base: if rng.below(2) == 0 {
            None
        } else {
            Some(rng.edge_u64())
        },
        trace: pick(rng, &["full", "fn", "none", "all", ""]),
        stack_size: if rng.below(2) == 0 {
            None
        } else {
            Some(rng.edge_u64())
        },
    }
}

fn random(h: &mut Harness) {
    h.case(
        "random/any flags give a spec that holds, or one clean error",
        || {
            let mut rng = rng_for("target/random flags");
            let mut built = 0;
            let mut refused = 0;
            for _ in 0..scaled(20_000) {
                let target = TARGETS[rng.below(TARGETS.len() as u64) as usize];
                let opts = random_opts(&mut rng);
                let first = resolve(target, &opts);
                assert_eq!(first, resolve(target, &opts), "deterministic: {opts:?}");
                match first {
                    Ok((spec, printed)) => {
                        check_spec(target, &spec, opts.cpu.as_deref(), opts.float.as_deref());
                        check_note(&printed, &spec, opts.cpu.as_deref());
                        assert!(
                            TargetUsize::checked(spec.image.base, &spec).is_some(),
                            "the base fits: {opts:?}"
                        );
                        assert!(spec.stack.size <= spec.layout.isize_max(), "{opts:?}");
                        built += 1;
                    }
                    Err(diag) => {
                        check_error(&diag);
                        refused += 1;
                    }
                }
            }
            assert!(built > 100, "only {built} successes");
            assert!(refused > 100, "only {refused} refusals");
        },
    );
    h.case("random/resolve reads no ambient state", || {
        // The same flags in another order of calls, with others in between.
        let mut rng = rng_for("target/order");
        let opts: Vec<TargetOpts> = (0..64).map(|_| random_opts(&mut rng)).collect();
        let forward: Vec<_> = opts.iter().map(|o| resolve("i386-none", o)).collect();
        let backward: Vec<_> = opts.iter().rev().map(|o| resolve("i386-none", o)).collect();
        let reversed: Vec<_> = backward.into_iter().rev().collect();
        assert_eq!(forward, reversed);
    });
}
