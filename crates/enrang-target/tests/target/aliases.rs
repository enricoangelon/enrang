//! Every alias of SPEC 10.1 on every target, with its note.

use enrang_diag::{Code, Severity};
use enrang_target::{
    Arch, CPU_ALIASES, CpuAlias, CpuLevel, FloatStrategy, LongMode, TargetOpts, resolve,
};
use enrang_testkit::Harness;

use crate::support::{
    I386_TARGETS, SpecAlias, SpecOn64, TARGETS, VM_TARGETS, X86_64_TARGETS, cpu, default_float,
    err, level, ok, render, says, spec_aliases,
};

/// Asserts that the one note of a resolve names `alias` and `level`, and the exact
/// bytes it renders to.
fn check_note(target: &str, alias: &str, level_name: &str, some_models: bool) {
    let (_, printed) = ok(target, &cpu(alias));
    assert_eq!(printed.len(), 1, "one note: {printed:?}");
    let note = &printed[0];
    assert_eq!(note.severity, Severity::Note, "SPEC 10.1: it prints a note");
    assert!(!note.severity.fails(), "a note never stops a build");
    assert_eq!(note.code, Code::EN0909);
    assert!(
        note.primary.span.is_dummy(),
        "a command-line note has no place"
    );
    assert!(note.helps.is_empty());
    assert!(note.entries.is_empty());

    let suffix = if some_models {
        "; this covers only its 64-bit models"
    } else {
        ""
    };
    let line = format!("`{alias}` resolves to level `{level_name}`{suffix}");
    assert_eq!(note.message, line);
    assert_eq!(render(&printed), format!("note: {line}\n"));
}

pub fn register(h: &mut Harness) {
    table(h);
    for alias in spec_aliases() {
        on_32_bit(h, alias);
        on_64_bit(h, alias);
        on_vm(h, alias);
    }
    levels_print_nothing(h);
    wording(h);
}

fn table(h: &mut Harness) {
    h.case(
        "alias/CPU_ALIASES is SPEC 10.1's list, in its order",
        || {
            let code: Vec<(&str, &str)> = CPU_ALIASES
                .iter()
                .map(|alias| (alias.name, alias.level32.name()))
                .collect();
            let doc: Vec<(&str, &str)> = spec_aliases()
                .iter()
                .map(|alias| (alias.name.as_str(), alias.level32.as_str()))
                .collect();
            assert_eq!(code, doc);
        },
    );
    h.case("alias/SPEC names two of each 64-bit class", || {
        let count = |class| spec_aliases().iter().filter(|a| a.on_64 == class).count();
        assert_eq!(count(SpecOn64::Whole), 2);
        assert_eq!(count(SpecOn64::SomeModels), 2);
        assert_eq!(count(SpecOn64::NoLongMode), 2);
        assert_eq!(count(SpecOn64::Family), 15);
    });
    h.case("alias/names are unique and no alias is a level", || {
        for (index, alias) in CPU_ALIASES.iter().enumerate() {
            assert_eq!(CpuLevel::from_name(alias.name), None, "{}", alias.name);
            assert!(
                CPU_ALIASES[index + 1..]
                    .iter()
                    .all(|o| o.name != alias.name),
                "{} twice",
                alias.name
            );
        }
    });
    for name in ["", "K6", "k6 ", "k8", "core", "pentium4", "native", "i386"] {
        h.case(format!("alias/not an alias/`{name}`"), move || {
            assert_eq!(CpuAlias::find(name), None);
        });
    }
    for alias in CPU_ALIASES {
        let name = alias.name;
        h.case(format!("alias/{name}/level_on"), move || {
            let alias = CpuAlias::find(name).unwrap();
            assert_eq!(alias.level_on(Arch::I386), Some(alias.level32));
            assert_eq!(alias.level_on(Arch::Mir), None);
            let on_64 = match alias.long_mode {
                LongMode::None => None,
                LongMode::SomeModels | LongMode::All => Some(CpuLevel::X86_64),
            };
            assert_eq!(alias.level_on(Arch::X86_64), on_64);
        });
    }
}

fn on_32_bit(h: &mut Harness, alias: &SpecAlias) {
    for target in I386_TARGETS {
        let name = alias.name.clone();
        let want = alias.level32.clone();
        h.case(format!("alias/{name}/on {target}"), move || {
            let (built, _) = ok(target, &cpu(&name));
            let rung = level(&want);
            assert_eq!(built.cpu, rung);
            assert_eq!(built.allowed, rung.features(Arch::I386));
            let float = match rung {
                CpuLevel::Sse2 => FloatStrategy::Sse2,
                CpuLevel::I586 | CpuLevel::I686 => FloatStrategy::X87,
                _ => FloatStrategy::Soft,
            };
            assert_eq!(built.float, float, "the default float follows the rung");
            assert_eq!(built.float, default_float(Arch::I386, rung));
            check_note(target, &name, &want, false);
        });
    }
}

fn on_64_bit(h: &mut Harness, alias: &SpecAlias) {
    for target in X86_64_TARGETS {
        let name = alias.name.clone();
        let want = alias.level32.clone();
        let class = alias.on_64;
        h.case(format!("alias/{name}/on {target}"), move || match class {
            SpecOn64::Whole | SpecOn64::SomeModels => {
                let (built, _) = ok(target, &cpu(&name));
                assert_eq!(built.cpu, CpuLevel::X86_64);
                assert_eq!(built.allowed, CpuLevel::X86_64.features(Arch::X86_64));
                assert_eq!(built.float, FloatStrategy::Sse2);
                check_note(target, &name, "x86-64", class == SpecOn64::SomeModels);
            }
            SpecOn64::NoLongMode | SpecOn64::Family => {
                let diag = err(target, &cpu(&name));
                assert_eq!(diag.code, Code::EN0912);
                assert_eq!(
                    diag.message,
                    format!("`--cpu={name}` does not apply to target `{target}`")
                );
                says(&diag, &[&format!("32-bit level `{want}`"), "no long mode"]);
                assert_eq!(diag.helps.len(), 1, "the 32-bit target to use");
            }
        });
    }
}

fn on_vm(h: &mut Harness, alias: &SpecAlias) {
    for target in VM_TARGETS {
        let name = alias.name.clone();
        h.case(format!("alias/{name}/on {target}"), move || {
            let diag = err(target, &cpu(&name));
            assert_eq!(diag.code, Code::EN0912);
            says(&diag, &["no CPU level", target]);
        });
    }
}

fn levels_print_nothing(h: &mut Harness) {
    const LOW: &[&str] = &I386_TARGETS;
    const HIGH: &[&str] = &X86_64_TARGETS;
    let rungs = [
        ("i386", LOW),
        ("i486", LOW),
        ("i586", LOW),
        ("i686", LOW),
        ("sse2", LOW),
        ("x86-64", HIGH),
    ];
    for (name, targets) in rungs {
        for &target in targets {
            h.case(
                format!("alias/level {name} on {target} has no note"),
                move || {
                    let (built, printed) = ok(target, &cpu(name));
                    assert!(printed.is_empty(), "{printed:?}");
                    assert_eq!(built.cpu, level(name));
                },
            );
        }
    }
    for target in TARGETS {
        h.case(
            format!("alias/no --cpu on {target} has no note"),
            move || {
                let (_, printed) = ok(target, &TargetOpts::default());
                assert!(printed.is_empty(), "{printed:?}");
            },
        );
    }
}

fn wording(h: &mut Harness) {
    h.case("alias/a failing compile does not count the note", || {
        let (_, mut printed) = ok("x86_64-linux", &cpu("q8400"));
        printed.push(err("nope", &TargetOpts::default()));
        let text = render(&printed);
        assert!(
            text.ends_with("error: aborting due to 1 previous error\n"),
            "{text}"
        );
    });
    h.case("alias/the 64-bit note appears only when it is true", || {
        for alias in CPU_ALIASES {
            let Ok((_, printed)) = resolve("x86_64-linux", &cpu(alias.name)) else {
                assert_eq!(alias.long_mode, LongMode::None, "{}", alias.name);
                continue;
            };
            let text = render(&printed);
            assert_eq!(
                text.contains("64-bit models"),
                alias.long_mode == LongMode::SomeModels,
                "{text}"
            );
        }
    });
    h.case("alias/a 32-bit target never mentions 64-bit models", || {
        for alias in CPU_ALIASES {
            let (_, printed) = ok("i386-linux", &cpu(alias.name));
            let text = render(&printed);
            assert!(!text.contains("64-bit"), "{text}");
        }
    });
    h.case("alias/an alias and its level build the same", || {
        for alias in CPU_ALIASES {
            let by_alias = ok("i386-none", &cpu(alias.name)).0;
            let by_level = ok("i386-none", &cpu(alias.level32.name())).0;
            assert_eq!(by_alias, by_level, "{}", alias.name);
        }
    });
    for (target, chip) in [
        ("x86_64-linux", "i386-linux"),
        ("x86_64-windows", "i386-linux"),
        ("x86_64-none", "i386-none"),
    ] {
        h.case(
            format!("alias/EN0912 on {target} points to {chip}"),
            move || {
                let diag = err(target, &cpu("k6"));
                says(&diag, &[&format!("--target={chip}")]);
                assert_eq!(
                    ok(chip, &cpu("k6")).0.cpu,
                    CpuLevel::I586,
                    "and that builds"
                );
            },
        );
    }
}
