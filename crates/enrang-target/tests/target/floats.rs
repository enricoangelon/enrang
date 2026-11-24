//! Float strategy: its defaults, what `--float` may ask for, and the stack reserve
//! that follows from it.

use enrang_diag::Code;
use enrang_target::{Arch, CPU_ALIASES, CpuLevel, FloatStrategy, TargetOpts, resolve};
use enrang_testkit::Harness;

use crate::support::{
    I386_TARGETS, TARGETS, VM_TARGETS, X86_64_TARGETS, backticked, cpu, default_float,
    default_spec, doc, float, level, line_starting, ok, opts_with, section, spec,
    spec_default_floats, table,
};

pub fn register(h: &mut Harness) {
    the_rule(h);
    the_documents(h);
    defaults(h);
    soft_is_always_legal(h);
    sse2(h);
    x87(h);
    reserve(h);
}

fn the_rule(h: &mut Harness) {
    h.case("float/ARCHITECTURE 2.7 still states this rule", || {
        let text = section("ARCHITECTURE.md", "### 2.7 TargetSpec");
        let rule = "On `i386-*` the default float follows the level: `soft` at `i386` and `i486`, `x87` at `i586` and `i686`, and `sse2` at `sse2`. `--float=soft` is legal on every `i386-*` and VM row and is EN0911 on native `x86_64-*`, which has only `sse2`; `--float=sse2` below level `sse2` is EN0911; `--float=x87` is legal at every level of `i386-*` and is EN0911 on native `x86_64-*`; `i386-windows` is EN1031. `--float=sse2` and `--float=x87` on a VM row are EN0911 too.";
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
    // EN1020 refused `--float=x87` and is retired; SPEC 9.3 now states where the
    // strategy applies, and the code follows it.
    h.case("float/SPEC 9.3 still says where x87 applies", || {
        let text = section("SPEC.md", "### 9.3 Floating point");
        for rule in [
            "`x87` (the FPU; the default at `i586` and `i686`, and `--float=x87` opts in at `i386`, `i486` and `sse2`; on native `x86_64-*` it is EN0911, as `--float=soft` is)",
            "On VM rows `--float=x87` is EN0911, as `--float=sse2` is.",
        ] {
            assert!(text.contains(rule), "the rule has changed: {rule}");
        }
    });
    h.case("float/EN1020 is retired, and SPEC 13.2 says why", || {
        assert_eq!(Code::from_name("EN1020"), None, "codes are never reused");
        let text = section("SPEC.md", "### 13.2 Catalog");
        let why = "EN1020 (`--float=x87` is accepted; it is the default at `i586` and `i686`)";
        assert!(text.contains(why), "the reason has changed");
        assert_eq!(spec("i386-linux", &float("x87")).float, FloatStrategy::X87);
    });
    h.case(
        "float/ARCHITECTURE 11 lists the values `--float` takes",
        || {
            let flags = table(
                section("ARCHITECTURE.md", "## 11. Driver and CLI"),
                &["Flag", "Values"],
            );
            let cell = &flags.row("`--float=`")[1];
            let named: Vec<&str> = cell.split('`').skip(1).step_by(2).collect();
            assert_eq!(named, ["soft", "sse2", "x87"]);
            // Each is a value somewhere: the error for an unknown one lists them all.
            for name in &named {
                let built = ok("i386-linux", &opts_with(Some("sse2"), Some(name))).0;
                assert_eq!(built.float.name(), *name);
            }
            let diag = resolve("i386-linux", &float("bogus")).expect_err("not a value");
            assert_eq!(diag.code, Code::EN1304);
            let list = "the values of `--float` are `soft`, `sse2` and `x87`";
            assert_eq!(crate::support::notes(&diag), [list]);
        },
    );
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

/// The `i386-*` levels at which `resolve` makes `strategy` the default, read back
/// from `resolve` itself on every `i386-*` row.
fn resolved_defaults(strategy: FloatStrategy) -> Vec<CpuLevel> {
    CpuLevel::for_arch(Arch::I386)
        .iter()
        .copied()
        .filter(|rung| {
            let floats: Vec<FloatStrategy> = I386_TARGETS
                .iter()
                .map(|target| spec(target, &cpu(rung.name())).float)
                .collect();
            assert!(
                floats.iter().all(|float| *float == floats[0]),
                "the `i386-*` rows disagree at {}: {floats:?}",
                rung.name()
            );
            floats[0] == strategy
        })
        .collect()
}

/// The `i386-*` levels at which `--float=<strategy>` builds on every `i386-*` row
/// although it is not the default there: where the strategy is an opt-in.
fn resolved_opt_ins(strategy: FloatStrategy) -> Vec<CpuLevel> {
    let defaults = resolved_defaults(strategy);
    CpuLevel::for_arch(Arch::I386)
        .iter()
        .copied()
        .filter(|rung| !defaults.contains(rung))
        .filter(|rung| {
            I386_TARGETS.iter().all(|target| {
                let opts = opts_with(Some(rung.name()), Some(strategy.name()));
                matches!(resolve(target, &opts), Ok((built, _)) if built.float == strategy)
            })
        })
        .collect()
}

/// The levels listed at the start of `text`, as in "`i386` and `i486`" or "level
/// `sse2`": backticked level names joined by `, `, ` and ` or `, and `. The list
/// ends at the first word or backticked name that is not part of it.
fn listed_levels(text: &str) -> Vec<CpuLevel> {
    let mut rest = ["levels ", "level "]
        .iter()
        .find_map(|word| text.strip_prefix(word))
        .unwrap_or(text);
    let mut found = Vec::new();
    while let Some((name, after)) = rest
        .strip_prefix('`')
        .and_then(|quoted| quoted.split_once('`'))
    {
        let Some(rung) = CpuLevel::from_name(name) else {
            break;
        };
        found.push(rung);
        match [", and ", " and ", ", "]
            .iter()
            .find_map(|joint| after.strip_prefix(joint))
        {
            Some(next) => rest = next,
            None => break,
        }
    }
    found
}

/// What follows the first `words` in `text`.
fn following<'a>(text: &'a str, words: &str) -> &'a str {
    text.split_once(words)
        .unwrap_or_else(|| panic!("`{words}` is not in: {text}"))
        .1
}

/// The text inside the parentheses that follow `` `name` `` in `text`.
fn parenthesised_after<'a>(text: &'a str, name: &str) -> &'a str {
    let head = format!("`{name}` (");
    let start = text
        .find(&head)
        .unwrap_or_else(|| panic!("`{head}` is not in: {text}"))
        + head.len();
    let mut depth = 1;
    for (at, c) in text[start..].char_indices() {
        match c {
            '(' => depth += 1,
            ')' if depth == 1 => return &text[start..start + at],
            ')' => depth -= 1,
            _ => {}
        }
    }
    panic!("`{head}` never closes");
}

fn names(levels: &[CpuLevel]) -> Vec<&'static str> {
    levels.iter().map(|rung| rung.name()).collect()
}

const STRATEGIES: [FloatStrategy; 3] =
    [FloatStrategy::Soft, FloatStrategy::X87, FloatStrategy::Sse2];

/// Each sentence and table row the documents give a strategy's default levels, or
/// the levels where it is an opt-in, against what `resolve` does.
fn the_documents(h: &mut Harness) {
    h.case(
        "float/docs/the level reader reads the lists it must",
        || {
            let rows: [(&str, &[&str]); 7] = [
                ("`i386` and `i486`, because", &["i386", "i486"]),
                ("`i386`, `i486` and `sse2`; on", &["i386", "i486", "sse2"]),
                ("`i586`, `i686`, and `--float=x87` opts", &["i586", "i686"]),
                ("level `sse2`, and the default", &["sse2"]),
                ("`i686`", &["i686"]),
                ("`x86_64-*`", &[]),
                ("every level", &[]),
            ];
            for (text, want) in rows {
                assert_eq!(names(&listed_levels(text)), want, "{text}");
            }
            assert_eq!(
                names(&resolved_defaults(FloatStrategy::X87)),
                ["i586", "i686"]
            );
            assert_eq!(
                names(&resolved_opt_ins(FloatStrategy::X87)),
                ["i386", "i486", "sse2"]
            );
        },
    );
    h.case(
        "float/docs/SPEC 9.3 gives each strategy the levels `resolve` does",
        || {
            let text = section("SPEC.md", "### 9.3 Floating point");
            let strategies = line_starting(text, "**Strategies.**");
            for strategy in STRATEGIES {
                let name = strategy.name();
                let clause = parenthesised_after(strategies, name);
                let defaults = listed_levels(following(clause, "the default at "));
                assert_eq!(
                    names(&defaults),
                    names(&resolved_defaults(strategy)),
                    "`{name}`: {clause}"
                );
                let opt_in = clause.split_once("opts in at ");
                assert!(
                    opt_in.is_some() || strategy != FloatStrategy::X87,
                    "SPEC 9.3 names no `x87` opt-in: {clause}"
                );
                if let Some((_, rest)) = opt_in {
                    assert_eq!(
                        names(&listed_levels(rest)),
                        names(&resolved_opt_ins(strategy)),
                        "`{name}`: {clause}"
                    );
                }
            }
        },
    );
    h.case(
        "float/docs/ARCHITECTURE 7.10 gives each strategy the levels `resolve` does",
        || {
            let text = section("ARCHITECTURE.md", "### 7.10 Floats");
            let decision = line_starting(text, "**Decision:");
            let rule = following(decision, "On `i386-*` the default follows the level: ");
            for strategy in STRATEGIES {
                let name = strategy.name();
                let defaults = listed_levels(following(rule, &format!("`{name}` at ")));
                assert_eq!(
                    names(&defaults),
                    names(&resolved_defaults(strategy)),
                    "`{name}`: {rule}"
                );
            }
            let opt_ins = listed_levels(following(decision, "`--float=x87` opts in at "));
            assert_eq!(
                names(&opt_ins),
                names(&resolved_opt_ins(FloatStrategy::X87)),
                "{decision}"
            );
            let strategies = table(text, &["Strategy", "Where", "Implementation"]);
            for strategy in STRATEGIES {
                let name = strategy.name();
                let cell = strategies.get(&format!("`{name}`"), "Where");
                let defaults = listed_levels(following(cell, "`i386-*` at "));
                assert_eq!(
                    names(&defaults),
                    names(&resolved_defaults(strategy)),
                    "`{name}`: {cell}"
                );
                let opt_in = cell.split_once("opt-in at ");
                assert!(
                    opt_in.is_some() || strategy != FloatStrategy::X87,
                    "the `x87` row names no opt-in: {cell}"
                );
                if let Some((_, rest)) = opt_in {
                    assert_eq!(
                        names(&listed_levels(rest)),
                        names(&resolved_opt_ins(strategy)),
                        "`{name}`: {cell}"
                    );
                }
                if cell.contains("Default and only on `x86_64-*`") {
                    for target in X86_64_TARGETS {
                        assert_eq!(default_spec(target).float, strategy, "{target}: {cell}");
                    }
                }
            }
        },
    );
    h.case(
        "float/docs/ARCHITECTURE 8.2 names each level's default float",
        || {
            let ladder = table(
                section("ARCHITECTURE.md", "### 8.2 The `--cpu` ladder"),
                &[
                    "Level",
                    "`FeatureSet`",
                    "Codegen uses",
                    "Startup check (floor code)",
                ],
            );
            let mut named = Vec::new();
            for row in &ladder.rows {
                let rung = level(backticked(&row[0])[0]);
                let cell = row[2].to_lowercase();
                let Some((_, rest)) = cell.split_once("float strategy `") else {
                    continue;
                };
                let stated = rest.split('`').next().expect("a strategy");
                let target = if rung == CpuLevel::X86_64 {
                    X86_64_TARGETS[0]
                } else {
                    I386_TARGETS[0]
                };
                let resolved = spec(target, &cpu(rung.name())).float;
                assert_eq!(
                    stated,
                    resolved.name(),
                    "{} on {target}: {}",
                    row[0],
                    row[2]
                );
                named.push(rung);
            }
            // Every rung whose default differs from the floor's says which it is.
            let floor = spec(I386_TARGETS[0], &cpu("i386")).float;
            for rung in CpuLevel::for_arch(Arch::I386) {
                if spec(I386_TARGETS[0], &cpu(rung.name())).float != floor {
                    assert!(
                        named.contains(rung),
                        "`{}` names no float strategy",
                        rung.name()
                    );
                }
            }
        },
    );
    h.case(
        "float/docs/DEV_RUNTIME 2.3 names the float modes the VM refuses",
        || {
            let bullet = line_starting(doc("DEV_RUNTIME.md"), "- **Floats.**");
            let sentence = bullet
                .split(". ")
                .find(|sentence| sentence.contains("EN0911"))
                .unwrap_or_else(|| panic!("no sentence names EN0911: {bullet}"));
            let refused: Vec<&str> = backticked(sentence)
                .into_iter()
                .filter_map(|flag| flag.strip_prefix("--float="))
                .collect();
            assert!(!refused.is_empty(), "{sentence}");
            for target in VM_TARGETS {
                for value in ["soft", "sse2", "x87"] {
                    let result = resolve(target, &float(value));
                    let is_refused = matches!(&result, Err(diag) if diag.code == Code::EN0911);
                    assert_eq!(
                        is_refused,
                        refused.contains(&value),
                        "{target} --float={value}: {sentence}"
                    );
                    assert!(
                        is_refused || result.is_ok(),
                        "{target} --float={value}: {result:?}"
                    );
                }
            }
        },
    );
}

fn defaults(h: &mut Harness) {
    let rows = [
        ("i386", FloatStrategy::Soft),
        ("i486", FloatStrategy::Soft),
        ("i586", FloatStrategy::X87),
        ("i686", FloatStrategy::X87),
        ("sse2", FloatStrategy::Sse2),
    ];
    for (rung, want) in rows {
        for target in I386_TARGETS {
            h.case(format!("float/default/{rung} on {target}"), move || {
                assert_eq!(spec(target, &cpu(rung)).float, want);
                assert_eq!(default_float(Arch::I386, level(rung)), want);
            });
        }
    }
    h.case("float/default/SPEC 10.1 states the rows above", move || {
        let stated = spec_default_floats();
        let names: Vec<&str> = stated
            .iter()
            .map(|(strategy, _)| strategy.as_str())
            .collect();
        assert_eq!(names, ["soft", "x87", "sse2"], "{stated:?}");
        let mut levels = Vec::new();
        for (strategy, named) in &stated {
            for name in named {
                let rung = level(name);
                let arch = if rung == CpuLevel::X86_64 {
                    Arch::X86_64
                } else {
                    Arch::I386
                };
                assert_eq!(default_float(arch, rung).name(), strategy, "{name}");
                levels.push(rung);
            }
        }
        levels.sort();
        let mut all = CpuLevel::ALL.to_vec();
        all.sort();
        assert_eq!(levels, all, "every level once");
        for (rung, want) in rows {
            let (strategy, _) = stated
                .iter()
                .find(|(_, named)| named.iter().any(|name| name == rung))
                .expect("a stated level");
            assert_eq!(strategy, want.name(), "{rung}");
        }
    });
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
    h.case("float/default/an alias defaults as its rung does", || {
        for alias in CPU_ALIASES {
            let want = match alias.level32 {
                CpuLevel::Sse2 => FloatStrategy::Sse2,
                CpuLevel::I586 | CpuLevel::I686 => FloatStrategy::X87,
                _ => FloatStrategy::Soft,
            };
            assert_eq!(
                spec("i386-linux", &cpu(alias.name)).float,
                want,
                "{}",
                alias.name
            );
        }
    });
    h.case("float/default/only i586 and i686 default to x87", || {
        for target in TARGETS {
            let built = default_spec(target);
            for rung in CpuLevel::for_arch(built.arch) {
                let float = spec(target, &cpu(rung.name())).float;
                let x87 =
                    built.arch == Arch::I386 && matches!(rung, CpuLevel::I586 | CpuLevel::I686);
                assert_eq!(
                    float == FloatStrategy::X87,
                    x87,
                    "{target} at {}",
                    rung.name()
                );
            }
            assert_ne!(built.float, FloatStrategy::X87, "{target} with no --cpu");
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

/// `--float=x87` is legal at every level of `i386-*` (SPEC 9.3, ARCHITECTURE 2.7).
fn x87(h: &mut Harness) {
    for target in TARGETS {
        h.case(format!("float/x87/{target} with no --cpu"), move || {
            if target.starts_with("i386-") {
                let built = spec(target, &float("x87"));
                assert_eq!(built.float, FloatStrategy::X87);
                assert_eq!(built.cpu, CpuLevel::I386, "an opt-in at the floor");
            } else {
                let diag = resolve(target, &float("x87")).expect_err("not an i386 row");
                assert_eq!(diag.code, Code::EN0911);
            }
        });
    }
    for rung in ["i386", "i486", "i586", "i686", "sse2"] {
        for target in I386_TARGETS {
            h.case(format!("float/x87/{rung} on {target}"), move || {
                let built = spec(target, &opts_with(Some(rung), Some("x87")));
                assert_eq!(built.float, FloatStrategy::X87);
                assert_eq!(built.cpu.name(), rung, "the level is unchanged");
                assert_eq!(
                    built.allowed,
                    level(rung).features(Arch::I386),
                    "no level's set gains `fpu` (ARCHITECTURE 7.14)"
                );
            });
        }
    }
    h.case("float/x87/every alias that builds on 32 bits", || {
        for alias in CPU_ALIASES {
            let (built, printed) = ok("i386-none", &opts_with(Some(alias.name), Some("x87")));
            assert_eq!(built.float, FloatStrategy::X87, "{}", alias.name);
            assert_eq!(built.cpu, alias.level32, "{}", alias.name);
            assert_eq!(printed.len(), 1, "the alias is still named: {}", alias.name);
        }
    });
    h.case(
        "float/x87/at level sse2 keeps sse2 in the allowed set",
        || {
            // SPEC 9.3: `--float=x87` opts in at `sse2` too; the level still folds
            // `cpu.has("sse2")`.
            let built = spec("i386-linux", &opts_with(Some("sse2"), Some("x87")));
            assert!(built.allowed.contains(enrang_target::Feature::Sse2));
        },
    );
}

/// `__stack_limit`'s reserve (ARCHITECTURE 7.5, 7.15).
fn reserve(h: &mut Harness) {
    h.case("reserve/ARCHITECTURE 7.5 still says 2 KB and 3 KB", || {
        let text = section("ARCHITECTURE.md", "### 7.5 Frames");
        assert!(
            text.contains("a fixed reserve: 2 KB under `soft`, 3 KB under `sse2` and `x87`"),
            "the reserve has changed"
        );
        assert!(
            text.contains("the 512-byte `fxsave` with its alignment or the 108-byte `fnsave`"),
            "what the reserve covers has changed"
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
        ("i386-none", Some("i486"), None, 2048),
        ("i386-none", Some("i586"), None, 3072),
        ("i386-none", Some("i686"), None, 3072),
        ("i386-none", Some("i686"), Some("soft"), 2048),
        ("i386-none", None, Some("x87"), 3072),
        ("i386-none", Some("k6"), None, 3072),
        ("i386-none", Some("sse2"), Some("x87"), 3072),
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
        ("i386-linux", Some("i686"), None, 0),
        ("i386-linux", None, Some("x87"), 0),
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
