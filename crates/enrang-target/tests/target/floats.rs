//! Float strategy: its defaults, what `--float` may ask for, and the stack reserve
//! that follows from it.

use enrang_diag::Code;
use enrang_target::{CPU_ALIASES, CpuLevel, FloatStrategy, TargetOpts, resolve};
use enrang_testkit::Harness;

use crate::support::{
    I386_TARGETS, TARGETS, VM_TARGETS, X86_64_TARGETS, cpu, default_spec, float, opts_with,
    section, spec,
};

pub fn register(h: &mut Harness) {
    the_rule(h);
    defaults(h);
    soft_is_always_legal(h);
    sse2(h);
    reserve(h);
}

fn the_rule(h: &mut Harness) {
    h.case("float/ARCHITECTURE 2.7 still states this rule", || {
        let text = section("ARCHITECTURE.md", "### 2.7 TargetSpec");
        let rule = "On `i386-*` the default float is `soft`, except that `--cpu=sse2` defaults to `sse2`. `--float=soft` is legal on every `i386-*` and VM row and is EN0911 on native `x86_64-*`, which has only `sse2`; `--float=sse2` below level `sse2` is EN0911; `--float=x87` is EN1020; `i386-windows` is EN1031.";
        assert!(text.contains(rule), "the rule has changed");
    });
    h.case(
        "float/SPEC 9.3 still says `sse2` is the only native x86-64 strategy",
        || {
            let text = section("SPEC.md", "### 9.3 Floating point");
            let rule =
                "default and only strategy on native `x86_64-*`, where `--float=soft` is EN0911";
            assert!(text.contains(rule), "the rule has changed");
        },
    );
    h.case("float/SPEC 16 still gives the help the code prints", || {
        let text = section("SPEC.md", "## 16. Deferred features");
        let help = "`--float=soft` works at every level of `i386-*` and is bit-identical";
        assert!(text.contains(help), "the rule has changed");
    });
    for (strategy, name) in [
        (FloatStrategy::Soft, "soft"),
        (FloatStrategy::Sse2, "sse2"),
        (FloatStrategy::X87, "x87"),
        (FloatStrategy::Host, "host"),
    ] {
        h.case(format!("float/name/{name}"), move || {
            assert_eq!(strategy.name(), name);
        });
    }
}

fn defaults(h: &mut Harness) {
    for (rung, want) in [
        ("i386", FloatStrategy::Soft),
        ("i486", FloatStrategy::Soft),
        ("i586", FloatStrategy::Soft),
        ("i686", FloatStrategy::Soft),
        ("sse2", FloatStrategy::Sse2),
    ] {
        for target in I386_TARGETS {
            h.case(format!("float/default/{rung} on {target}"), move || {
                assert_eq!(spec(target, &cpu(rung)).float, want);
            });
        }
    }
    for target in I386_TARGETS {
        h.case(format!("float/default/no --cpu on {target}"), move || {
            assert_eq!(default_spec(target).float, FloatStrategy::Soft);
        });
    }
    for target in X86_64_TARGETS {
        h.case(format!("float/default/no --cpu on {target}"), move || {
            assert_eq!(default_spec(target).float, FloatStrategy::Sse2);
        });
        h.case(format!("float/default/x86-64 on {target}"), move || {
            assert_eq!(spec(target, &cpu("x86-64")).float, FloatStrategy::Sse2);
        });
    }
    for target in VM_TARGETS {
        h.case(format!("float/default/{target} is the host's"), move || {
            assert_eq!(default_spec(target).float, FloatStrategy::Host);
        });
    }
    h.case("float/default/an alias at sse2 defaults to sse2", || {
        for alias in CPU_ALIASES {
            let want = if alias.level32 == CpuLevel::Sse2 {
                FloatStrategy::Sse2
            } else {
                FloatStrategy::Soft
            };
            assert_eq!(
                spec("i386-linux", &cpu(alias.name)).float,
                want,
                "{}",
                alias.name
            );
        }
    });
}

fn soft_is_always_legal(h: &mut Harness) {
    for target in TARGETS {
        h.case(format!("float/soft/{target} with no --cpu"), move || {
            if target.starts_with("x86_64-") {
                let diag = resolve(target, &float("soft")).expect_err("only sse2 there");
                assert_eq!(diag.code, Code::EN0911);
            } else {
                assert_eq!(spec(target, &float("soft")).float, FloatStrategy::Soft);
            }
        });
    }
    for rung in ["i386", "i486", "i586", "i686", "sse2"] {
        for target in I386_TARGETS {
            h.case(format!("float/soft/{rung} on {target}"), move || {
                let built = spec(target, &opts_with(Some(rung), Some("soft")));
                assert_eq!(built.float, FloatStrategy::Soft);
                assert_eq!(built.cpu.name(), rung, "the level is unchanged");
            });
        }
    }
    for target in X86_64_TARGETS {
        h.case(format!("float/soft/refused on {target}"), move || {
            let opts = opts_with(Some("x86-64"), Some("soft"));
            let diag = resolve(target, &opts).expect_err("x86-64 has one float strategy");
            assert_eq!(diag.code, Code::EN0911);
            assert_eq!(
                diag.message,
                format!("`--float=soft` does not apply to target `{target}`")
            );
        });
    }
    h.case("float/soft/every alias that builds", || {
        for alias in CPU_ALIASES {
            let built = spec("i386-none", &opts_with(Some(alias.name), Some("soft")));
            assert_eq!(built.float, FloatStrategy::Soft, "{}", alias.name);
        }
    });
    h.case(
        "float/soft/at level sse2 keeps sse2 in the allowed set",
        || {
            // TESTING's `l32-sse2s` cell: the level still folds `cpu.has("sse2")`.
            let built = spec("i386-linux", &opts_with(Some("sse2"), Some("soft")));
            assert!(built.allowed.contains(enrang_target::Feature::Sse2));
        },
    );
}

fn sse2(h: &mut Harness) {
    for target in I386_TARGETS {
        h.case(format!("float/sse2/at level sse2 on {target}"), move || {
            let built = spec(target, &opts_with(Some("sse2"), Some("sse2")));
            assert_eq!(built.float, FloatStrategy::Sse2);
        });
        for chip in ["p4", "pentium-m", "core-duo", "atom", "core2", "q8400"] {
            h.case(format!("float/sse2/{chip} on {target}"), move || {
                let built = spec(target, &opts_with(Some(chip), Some("sse2")));
                assert_eq!(built.float, FloatStrategy::Sse2);
            });
        }
    }
    for target in X86_64_TARGETS {
        h.case(format!("float/sse2/on {target}"), move || {
            assert_eq!(spec(target, &float("sse2")).float, FloatStrategy::Sse2);
        });
    }
}

/// `__stack_limit`'s reserve (ARCHITECTURE 7.5, 7.15).
fn reserve(h: &mut Harness) {
    h.case("reserve/ARCHITECTURE 7.5 still says 2 KB and 3 KB", || {
        let text = section("ARCHITECTURE.md", "### 7.5 Frames");
        assert!(
            text.contains("a fixed reserve: 2 KB under `soft`, 3 KB under `sse2`"),
            "the reserve has changed"
        );
    });
    h.case(
        "reserve/ARCHITECTURE 7.15 still says x86-64 always saves",
        || {
            let text = section("ARCHITECTURE.md", "### 7.15 Interrupt stubs");
            assert!(text.contains("x86-64 uses the 16-byte IDT and always `fxsave`s"));
        },
    );
    let rows: &[(&str, Option<&str>, Option<&str>, u32)] = &[
        ("i386-none", None, None, 2048),
        ("i386-none", Some("i686"), None, 2048),
        ("i386-none", Some("sse2"), None, 3072),
        ("i386-none", Some("sse2"), Some("sse2"), 3072),
        ("i386-none", Some("sse2"), Some("soft"), 2048),
        ("i386-none", None, Some("soft"), 2048),
        ("i386-none", Some("q8400"), None, 3072),
        ("i386-none", Some("q8400"), Some("soft"), 2048),
        ("x86_64-none", None, None, 3072),
        ("x86_64-none", None, Some("sse2"), 3072),
        // No limit check, so nothing to reserve.
        ("i386-linux", None, None, 0),
        ("i386-linux", Some("sse2"), None, 0),
        ("x86_64-linux", None, None, 0),
        ("x86_64-windows", None, None, 0),
        ("vm64", None, None, 0),
        ("vm32", None, Some("soft"), 0),
    ];
    for &(target, level, strategy, want) in rows {
        let name = format!("reserve/{target} cpu={level:?} float={strategy:?}");
        h.case(name, move || {
            let built = spec(target, &opts_with(level, strategy));
            assert_eq!(built.stack.limit_reserve, want);
            assert_eq!(built.stack.limit_check, want != 0);
        });
    }
    h.case(
        "reserve/the flags do not disturb the other stack fields",
        || {
            let plain = spec("i386-none", &TargetOpts::default()).stack;
            let raised = spec("i386-none", &cpu("sse2")).stack;
            assert_eq!(plain.size, raised.size);
            assert_eq!(plain.probe_interval, raised.probe_interval);
            assert_eq!(plain.limit_check, raised.limit_check);
            assert_ne!(plain.limit_reserve, raised.limit_reserve);
        },
    );
}
