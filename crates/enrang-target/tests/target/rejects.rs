//! Every rejected combination of target, `--cpu` and `--float`, with its code.

use enrang_diag::{Code, EntryKind, Owner, Phase, Severity};
use enrang_target::{CpuLevel, FloatStrategy, TargetOpts, resolve};
use enrang_testkit::Harness;

use crate::support::{
    I386_TARGETS, NATIVE_TARGETS, TARGETS, VM_TARGETS, X86_64_TARGETS, cpu, err, float, notes, ok,
    opts_with, render, says, section, spec, table,
};

/// A row of SPEC 16: the normative message and help of a deferred feature.
fn deferred(code: &str) -> (String, String) {
    let rows = table(
        section("SPEC.md", "## 16. Deferred features"),
        &["Code", "Feature seen", "Message", "Help"],
    );
    let row = rows.row(code);
    (row[2].clone(), row[3].clone())
}

pub fn register(h: &mut Harness) {
    registry(h);
    unknown_targets(h);
    windows_32(h);
    native(h);
    unknown_levels(h);
    levels_that_do_not_apply(h);
    floats(h);
    precedence(h);
    rendered(h);
    typed_values_reach_no_terminal(h);
    spec_sentences(h);
}

fn registry(h: &mut Harness) {
    for code in [
        Code::EN0909,
        Code::EN0911,
        Code::EN0912,
        Code::EN1020,
        Code::EN1031,
        Code::EN1303,
    ] {
        h.case(
            format!("reject/{code} is target's, on the command line"),
            move || {
                assert_eq!(code.owner(), Owner::Target);
                assert_eq!(code.phase(), Phase::CommandLine);
                assert_eq!(code.severity(), Severity::Error);
            },
        );
    }
}

fn unknown_targets(h: &mut Harness) {
    // What was typed, and the target a did-you-mean offers, if any.
    let rows: &[(&str, Option<&str>)] = &[
        ("", None),
        ("linux", None),
        ("x86_64", None),
        ("wasm32", None),
        ("aarch64-linux", None),
        ("native", None),
        ("x86_64-linuxx", Some("x86_64-linux")),
        ("x86_64-linx", Some("x86_64-linux")),
        ("x86-64-linux", Some("x86_64-linux")),
        ("X86_64-LINUX", Some("x86_64-linux")),
        ("x86_64-windws", Some("x86_64-windows")),
        ("x86_64-nonee", Some("x86_64-none")),
        ("i386-linu", Some("i386-linux")),
        ("i386-nonee", Some("i386-none")),
        ("i486-linux", Some("i386-linux")),
        ("i686-none", Some("i386-none")),
        ("vm16", None),
        // The VM rows are chosen by `run --vm --layout=`, so nothing offers them.
        ("vm6", None),
        ("vm33", None),
        ("vm65", None),
        ("VM64", None),
        ("x86_64-win32", Some("x86_64-linux")),
        ("i386-windows ", None),
        ("I386-windows", None),
    ];
    for &(name, suggestion) in rows {
        h.case(format!("reject/EN1303/`{name}`"), move || {
            let diag = err(name, &TargetOpts::default());
            assert_eq!(diag.code, Code::EN1303, "{}", diag.message);
            assert_eq!(diag.message, format!("unknown target `{name}`"));
            assert!(diag.primary.span.is_dummy());
            match suggestion {
                Some(target) => {
                    assert_eq!(diag.helps.len(), 1);
                    assert_eq!(diag.helps[0].message, format!("did you mean `{target}`?"));
                    assert!(resolve(target, &TargetOpts::default()).is_ok());
                }
                None => assert!(diag.helps.is_empty(), "{:?}", diag.helps),
            }
            let listed = notes(&diag);
            assert_eq!(listed.len(), 1);
            for target in NATIVE_TARGETS {
                assert!(listed[0].contains(&format!("`{target}`")), "{}", listed[0]);
            }
            for target in VM_TARGETS {
                assert!(!listed[0].contains(target), "{}", listed[0]);
            }
        });
    }
}

fn windows_32(h: &mut Harness) {
    let (message, help) = deferred("EN1031");
    let spec16 = message.clone();
    h.case("reject/EN1031/SPEC 16's message and help", move || {
        let diag = err("i386-windows", &TargetOpts::default());
        assert_eq!(diag.code, Code::EN1031);
        assert_eq!(diag.message, message);
        assert_eq!(diag.helps.len(), 1, "one help");
        assert_eq!(diag.helps[0].message, help);
        assert_eq!(diag.entries.len(), 1, "one note with the reason");
        assert_eq!(diag.entries[0].kind, EntryKind::Note);
    });
    // Whatever else the command line says, the target is reported first.
    let opts: [(&str, TargetOpts); 5] = [
        ("--cpu=i386", cpu("i386")),
        ("--cpu=native", cpu("native")),
        ("--float=x87", float("x87")),
        (
            "--cpu=sse2 --float=sse2",
            opts_with(Some("sse2"), Some("sse2")),
        ),
        (
            "--format=pe",
            TargetOpts {
                format: Some("pe".to_owned()),
                ..TargetOpts::default()
            },
        ),
    ];
    for (name, opts) in opts {
        let want = spec16.clone();
        h.case(format!("reject/EN1031/with {name}"), move || {
            let diag = err("i386-windows", &opts);
            assert_eq!(diag.code, Code::EN1031);
            assert_eq!(diag.message, want);
        });
    }
    h.case("reject/EN1031/the help's targets exist", || {
        assert!(resolve("x86_64-windows", &TargetOpts::default()).is_ok());
        assert!(resolve("i386-linux", &TargetOpts::default()).is_ok());
    });
}

fn native(h: &mut Harness) {
    for target in VM_TARGETS {
        h.case(format!("reject/EN0912/native on {target}"), move || {
            let diag = err(target, &cpu("native"));
            assert_eq!(diag.code, Code::EN0912);
            assert_eq!(
                diag.message,
                format!("`--cpu=native` does not apply to target `{target}`")
            );
        });
    }
    for target in NATIVE_TARGETS {
        h.case(format!("reject/EN0909/native on {target}"), move || {
            let diag = err(target, &cpu("native"));
            assert_eq!(diag.code, Code::EN0909);
            assert_eq!(diag.severity, Severity::Error);
            assert_eq!(diag.message, "`--cpu=native` is rejected");
            says(&diag, &["the host is never the target"]);
        });
    }
}

fn unknown_levels(h: &mut Harness) {
    // What was typed, and the `--cpu` a did-you-mean offers on each ladder.
    let rows: &[(&str, Option<&str>, Option<&str>)] = &[
        ("", None, None),
        ("bogus", None, None),
        ("avx2", None, None),
        ("x86_64", None, Some("x86-64")),
        ("x8664", None, Some("x86-64")),
        ("X86-64", None, Some("x86-64")),
        ("Pentium", Some("pentium"), None),
        ("CORE2", Some("core2"), Some("core2")),
        ("i386 ", Some("i386"), None),
        ("I386", Some("i386"), None),
        ("i786", Some("i386"), None),
        ("sse3", Some("sse2"), None),
        ("K6", Some("k6"), None),
        ("k8", Some("k5"), None),
        ("pentium3", Some("pentium"), None),
        ("pentiumm", Some("pentium"), None),
        ("core2duo", Some("core-duo"), None),
        ("core3", Some("core2"), Some("core2")),
        ("q8401", Some("q8400"), Some("q8400")),
        ("NATIVE", None, None),
        ("nativ", None, None),
    ];
    for &(name, on32, on64) in rows {
        for target in I386_TARGETS {
            h.case(format!("reject/EN0909/`{name}` on {target}"), move || {
                check_unknown(target, name, on32);
            });
        }
        for target in X86_64_TARGETS {
            h.case(format!("reject/EN0909/`{name}` on {target}"), move || {
                check_unknown(target, name, on64);
            });
        }
        for target in VM_TARGETS {
            h.case(format!("reject/EN0912/`{name}` on {target}"), move || {
                let diag = err(target, &cpu(name));
                assert_eq!(diag.code, Code::EN0912, "any `--cpu` on a VM row");
                says(&diag, &["has no CPU level"]);
                assert!(diag.helps.is_empty(), "the VM has nothing to suggest");
            });
        }
    }
}

fn check_unknown(target: &str, name: &str, suggestion: Option<&str>) {
    let diag = err(target, &cpu(name));
    assert_eq!(diag.code, Code::EN0909);
    assert_eq!(diag.message, format!("`--cpu={name}` is not a CPU level"));
    assert!(diag.primary.span.is_dummy());
    match suggestion {
        Some(wanted) => {
            assert_eq!(diag.helps.len(), 1);
            let help = format!("did you mean `--cpu={wanted}`?");
            assert_eq!(diag.helps[0].message, help);
            assert!(
                ok(target, &cpu(wanted)).0.allowed.iter().count() > 0,
                "{wanted}"
            );
        }
        None => assert!(diag.helps.is_empty(), "{:?}", diag.helps),
    }
}

fn levels_that_do_not_apply(h: &mut Harness) {
    for rung in ["i386", "i486", "i586", "i686", "sse2"] {
        for target in X86_64_TARGETS {
            h.case(format!("reject/EN0912/{rung} on {target}"), move || {
                let diag = err(target, &cpu(rung));
                assert_eq!(diag.code, Code::EN0912);
                assert_eq!(
                    diag.message,
                    format!("level `{rung}` does not apply to target `{target}`")
                );
                says(&diag, &["`--cpu=x86-64`", "--target=i386-"]);
                assert_eq!(ok(target, &cpu("x86-64")).0.cpu, CpuLevel::X86_64);
            });
        }
    }
    for target in I386_TARGETS {
        h.case(format!("reject/EN0912/x86-64 on {target}"), move || {
            let diag = err(target, &cpu("x86-64"));
            assert_eq!(diag.code, Code::EN0912);
            assert_eq!(
                diag.message,
                format!("level `x86-64` does not apply to target `{target}`")
            );
            says(
                &diag,
                &["long mode", "`--cpu=sse2`", "--target=x86_64-linux"],
            );
        });
    }
    for rung in CpuLevel::ALL {
        for target in VM_TARGETS {
            let name = rung.name();
            h.case(format!("reject/EN0912/{name} on {target}"), move || {
                let diag = err(target, &cpu(name));
                assert_eq!(diag.code, Code::EN0912);
                says(&diag, &[target, "no CPU level"]);
            });
        }
    }
    for chip in ["pentium-m", "core-duo"] {
        for target in X86_64_TARGETS {
            h.case(
                format!("reject/EN0912/SPEC's {chip} on {target}"),
                move || {
                    let diag = err(target, &cpu(chip));
                    assert_eq!(diag.code, Code::EN0912);
                    says(&diag, &[chip, target, "no long mode"]);
                },
            );
        }
        for target in I386_TARGETS {
            h.case(
                format!("reject/EN0912/{chip} is fine on {target}"),
                move || {
                    assert_eq!(ok(target, &cpu(chip)).0.cpu, CpuLevel::Sse2);
                },
            );
        }
    }
}

fn floats(h: &mut Harness) {
    let (message, help) = deferred("EN1020");
    for target in TARGETS {
        let (message, help) = (message.clone(), help.clone());
        h.case(format!("reject/EN1020/{target}"), move || {
            let diag = err(target, &float("x87"));
            assert_eq!(diag.code, Code::EN1020);
            assert_eq!(diag.message, message);
            assert_eq!(diag.helps.len(), 1);
            assert_eq!(diag.helps[0].message, help);
            assert_eq!(notes(&diag).len(), 1, "one note with the reason");
        });
    }
    for rung in ["i386", "i486", "i586", "i686", "sse2"] {
        for target in I386_TARGETS {
            let opts = opts_with(Some(rung), Some("x87"));
            h.case(format!("reject/EN1020/{rung} on {target}"), move || {
                assert_eq!(err(target, &opts).code, Code::EN1020);
            });
        }
    }
    for rung in ["i386", "i486", "i586", "i686"] {
        for target in I386_TARGETS {
            h.case(format!("reject/EN0911/{rung} on {target}"), move || {
                let diag = err(target, &opts_with(Some(rung), Some("sse2")));
                assert_eq!(diag.code, Code::EN0911);
                assert_eq!(
                    diag.message,
                    format!(
                        "`--float=sse2` needs level `sse2`, and this build is at level `{rung}`"
                    )
                );
                let helps: Vec<&str> = diag.helps.iter().map(|h| h.message.as_str()).collect();
                assert_eq!(helps.len(), 2, "{helps:?}");
                assert!(helps[0].contains("`--cpu=sse2`"), "{helps:?}");
                assert!(helps[1].contains("`--float=soft`"), "{helps:?}");
            });
        }
    }
    for target in I386_TARGETS {
        h.case(
            format!("reject/EN0911/the default level on {target}"),
            move || {
                let diag = err(target, &float("sse2"));
                assert_eq!(diag.code, Code::EN0911);
                says(&diag, &["level `i386`"]);
            },
        );
        h.case(
            format!("reject/EN0911/the helps work on {target}"),
            move || {
                let fixed = opts_with(Some("sse2"), Some("sse2"));
                assert_eq!(spec(target, &fixed).float, FloatStrategy::Sse2);
                let fixed = opts_with(Some("i386"), Some("soft"));
                assert_eq!(spec(target, &fixed).float, FloatStrategy::Soft);
            },
        );
    }
    // An alias below `sse2`: the error names the rung it resolved to, and the alias.
    let aliased = [
        ("386", "i386"),
        ("486", "i486"),
        ("k6", "i586"),
        ("p3", "i686"),
        ("athlon-xp", "i686"),
    ];
    for (alias, rung) in aliased {
        for target in I386_TARGETS {
            h.case(
                format!("reject/EN0911/alias {alias} on {target}"),
                move || {
                    let diag = err(target, &opts_with(Some(alias), Some("sse2")));
                    assert_eq!(diag.code, Code::EN0911);
                    let wanted = format!("`{alias}` resolves to level `{rung}`");
                    assert_eq!(notes(&diag), [wanted.as_str()]);
                    says(&diag, &[&format!("at level `{rung}`")]);
                },
            );
        }
    }
    // Spellings that are no strategy at all.
    let bad = [
        ("", None),
        ("hard", None),
        ("avx", None),
        ("host", None),
        ("SOFT", Some("soft")),
        ("sof", Some("soft")),
        ("sse", Some("sse2")),
        // `x87` is refused whatever the target, so no suggestion leads to it.
        ("x86", None),
        ("x8", None),
        ("x88", None),
        ("X87", None),
    ];
    for (name, suggestion) in bad {
        for target in TARGETS {
            h.case(
                format!("reject/EN1304/--float=`{name}` on {target}"),
                move || {
                    let diag = err(target, &float(name));
                    assert_eq!(diag.code, Code::EN1304);
                    assert_eq!(
                        diag.message,
                        format!("`--float={name}` is not a float strategy")
                    );
                    assert_eq!(
                        notes(&diag),
                        ["the values of `--float` are `soft` and `sse2`"]
                    );
                    match suggestion {
                        Some(found) => {
                            let help = format!("did you mean `--float={found}`?");
                            assert_eq!(diag.helps[0].message, help);
                        }
                        None => assert!(diag.helps.is_empty(), "{:?}", diag.helps),
                    }
                },
            );
        }
    }
    for target in VM_TARGETS {
        h.case(
            format!("reject/EN0911/--float=sse2 on {target}"),
            move || {
                let diag = err(target, &float("sse2"));
                assert_eq!(diag.code, Code::EN0911);
                says(&diag, &[target, "--float=soft"]);
            },
        );
    }
}

/// The order in `resolve`'s contract, shown by flags that are wrong together.
fn precedence(h: &mut Harness) {
    let bad = |field: &str, value: &str| {
        let mut opts = TargetOpts::default();
        match field {
            "cpu" => opts.cpu = Some(value.to_owned()),
            "float" => opts.float = Some(value.to_owned()),
            "format" => opts.format = Some(value.to_owned()),
            "image" => opts.image = Some(value.to_owned()),
            "trace" => opts.trace = Some(value.to_owned()),
            other => panic!("no field {other}"),
        }
        opts
    };
    let cpu_and_float = TargetOpts {
        float: Some("x87".to_owned()),
        ..bad("cpu", "native")
    };
    let everything_else = TargetOpts {
        format: Some("coff".to_owned()),
        image: Some("cdrom".to_owned()),
        trace: Some("all".to_owned()),
        base: Some(u64::MAX),
        stack_size: Some(0),
        ..TargetOpts::default()
    };
    let rows: Vec<(&str, &str, TargetOpts, Code, &str)> = vec![
        (
            "the VM names --format before --image",
            "vm64",
            TargetOpts {
                format: Some("elf".to_owned()),
                image: Some("floppy".to_owned()),
                ..TargetOpts::default()
            },
            Code::EN1304,
            "`--format` does not apply to target `vm64`",
        ),
        (
            "the VM names --image before --base",
            "vm32",
            TargetOpts {
                image: Some("floppy".to_owned()),
                base: Some(1),
                ..TargetOpts::default()
            },
            Code::EN1304,
            "`--image` does not apply to target `vm32`",
        ),
        (
            "the VM names --base before --stack-size",
            "vm64",
            TargetOpts {
                base: Some(1),
                stack_size: Some(1),
                ..TargetOpts::default()
            },
            Code::EN1304,
            "`--base` does not apply to target `vm64`",
        ),
        (
            "the VM names --stack-size before --trace",
            "vm32",
            TargetOpts {
                stack_size: Some(1),
                trace: Some("fn".to_owned()),
                ..TargetOpts::default()
            },
            Code::EN1304,
            "`--stack-size` does not apply to target `vm32`",
        ),
        (
            "target beats cpu",
            "nope",
            cpu_and_float.clone(),
            Code::EN1303,
            "unknown target",
        ),
        (
            "cpu beats float",
            "i386-linux",
            cpu_and_float,
            Code::EN0909,
            "native",
        ),
        (
            "cpu's reach beats float",
            "x86_64-linux",
            TargetOpts {
                float: Some("x87".to_owned()),
                ..bad("cpu", "i686")
            },
            Code::EN0912,
            "i686",
        ),
        (
            "float beats format",
            "i386-linux",
            TargetOpts {
                format: Some("coff".to_owned()),
                ..bad("float", "x87")
            },
            Code::EN1020,
            "x87",
        ),
        (
            "EN0911 beats format",
            "i386-linux",
            TargetOpts {
                format: Some("coff".to_owned()),
                ..bad("float", "sse2")
            },
            Code::EN0911,
            "sse2",
        ),
        (
            "format comes first of the rest",
            "i386-none",
            everything_else.clone(),
            Code::EN1304,
            "--format=coff",
        ),
        (
            "image follows format",
            "i386-none",
            TargetOpts {
                format: None,
                ..everything_else.clone()
            },
            Code::EN1304,
            "--image=cdrom",
        ),
        (
            "base follows image",
            "i386-none",
            TargetOpts {
                format: None,
                image: None,
                ..everything_else.clone()
            },
            Code::EN1304,
            "--base",
        ),
        (
            "stack size follows base",
            "i386-none",
            TargetOpts {
                format: None,
                image: None,
                base: None,
                ..everything_else.clone()
            },
            Code::EN1304,
            "--stack-size=0",
        ),
        (
            "trace is last",
            "i386-none",
            TargetOpts {
                format: None,
                image: None,
                base: None,
                stack_size: None,
                ..everything_else.clone()
            },
            Code::EN1304,
            "--trace=all",
        ),
    ];
    for (name, target, opts, code, word) in rows {
        h.case(format!("reject/first problem wins/{name}"), move || {
            let diag = err(target, &opts);
            assert_eq!(diag.code, code, "{}", diag.message);
            assert!(diag.message.contains(word), "{}", diag.message);
        });
    }
    h.case(
        "reject/an error beats the note it would have printed",
        || {
            // The result is an error alone, so the alias is told inside it.
            let opts = opts_with(Some("k6"), Some("x87"));
            assert_eq!(err("i386-linux", &opts).code, Code::EN1020);
        },
    );
    for target in NATIVE_TARGETS {
        h.case(
            format!("reject/the float flag has a default on {target}"),
            move || {
                let (built, printed) = ok(target, &TargetOpts::default());
                assert!(printed.is_empty());
                assert!(matches!(
                    built.float,
                    FloatStrategy::Soft | FloatStrategy::Sse2
                ));
            },
        );
    }
}

/// The whole of what a reader sees, byte for byte, one of each kind of refusal.
fn rendered(h: &mut Harness) {
    let summary = "\nerror: aborting due to 1 previous error\n";
    let rows: &[(&str, &str, TargetOpts, &[&str])] = &[
        (
            "native",
            "i386-linux",
            cpu("native"),
            &[
                "error[EN0909]: `--cpu=native` is rejected",
                "  = note: the host is never the target: output runs on the chips it was built for, not on the machine building it",
                "help: name a level or a chip; `enrang targets` lists them",
                "  = explain: run `enrang explain EN0909`",
            ],
        ),
        (
            "an unknown level",
            "i386-linux",
            cpu("pentiun"),
            &[
                "error[EN0909]: `--cpu=pentiun` is not a CPU level",
                "  = note: levels on target `i386-linux`: `i386`, `i486`, `i586`, `i686` and `sse2`; `enrang targets` lists chip names too",
                "help: did you mean `--cpu=pentium`?",
                "  = explain: run `enrang explain EN0909`",
            ],
        ),
        (
            "an i386-family level on x86_64-*",
            "x86_64-linux",
            cpu("i686"),
            &[
                "error[EN0912]: level `i686` does not apply to target `x86_64-linux`",
                "  = note: level `x86-64` is the only level on `x86_64-*`",
                "help: `--cpu=x86-64`; `--target=i386-linux` builds 32-bit output",
                "  = explain: run `enrang explain EN0912`",
            ],
        ),
        (
            "a chip with no long mode",
            "x86_64-none",
            cpu("pentium-m"),
            &[
                "error[EN0912]: `--cpu=pentium-m` does not apply to target `x86_64-none`",
                "  = note: `pentium-m` resolves to the 32-bit level `sse2`, because those chips have no long mode",
                "help: `--target=i386-none` builds 32-bit output",
                "  = explain: run `enrang explain EN0912`",
            ],
        ),
        (
            "sse2 below its level",
            "i386-linux",
            opts_with(Some("k6"), Some("sse2")),
            &[
                "error[EN0911]: `--float=sse2` needs level `sse2`, and this build is at level `i586`",
                "  = note: `k6` resolves to level `i586`",
                "help: build for it: `--cpu=sse2`",
                "help: or `--float=soft`, which works at every level and is bit-identical",
                "  = explain: run `enrang explain EN0911`",
            ],
        ),
        (
            "x87",
            "x86_64-linux",
            float("x87"),
            &[
                "error[EN1020]: the x87 float strategy is not supported yet",
                "  = note: x87 is deferred: it may not ship until it passes the bit vectors `soft` and `sse2` pass",
                "help: `--float=soft` works at every level of `i386-*` and is bit-identical",
                "  = explain: run `enrang explain EN1020`",
            ],
        ),
        (
            "i386-windows",
            "i386-windows",
            TargetOpts::default(),
            &[
                "error[EN1031]: 32-bit Windows output is not supported yet",
                "  = note: Windows output is 64-bit only; nothing has been built for 32-bit Windows",
                "help: `x86_64-windows`; `i386-linux` for 32-bit testing",
                "  = explain: run `enrang explain EN1031`",
            ],
        ),
        (
            "an unknown target",
            "x86_64-linxu",
            TargetOpts::default(),
            &[
                "error[EN1303]: unknown target `x86_64-linxu`",
                "  = note: targets are `x86_64-linux`, `x86_64-windows`, `i386-linux`, `i386-none` and `x86_64-none`",
                "help: did you mean `x86_64-linux`?",
                "  = explain: run `enrang explain EN1303`",
            ],
        ),
    ];
    for (name, target, opts, lines) in rows.iter().cloned() {
        h.case(format!("reject/rendered/{name}"), move || {
            let mut want = lines.join("\n");
            want.push('\n');
            want.push_str(summary);
            assert_eq!(render(&[err(target, &opts)]), want);
        });
    }
}

/// A flag's value goes into a message as the user wrote it, and what reaches the
/// terminal is the renderer's business: nothing typed can act on it (SPEC 13.1).
fn typed_values_reach_no_terminal(h: &mut Harness) {
    let typed = "\x1b[2J";
    let escaped = "\\u{1b}[2J";
    let bad = |field: &str| match field {
        "cpu" => cpu(typed),
        "float" => float(typed),
        "format" => TargetOpts {
            format: Some(typed.to_owned()),
            ..TargetOpts::default()
        },
        "image" => TargetOpts {
            image: Some(typed.to_owned()),
            ..TargetOpts::default()
        },
        _ => TargetOpts {
            trace: Some(typed.to_owned()),
            ..TargetOpts::default()
        },
    };
    for (field, head) in [
        ("cpu", "error[EN0909]: `--cpu=<v>` is not a CPU level"),
        (
            "float",
            "error[EN1304]: `--float=<v>` is not a float strategy",
        ),
        (
            "format",
            "error[EN1304]: `--format=<v>` is not an output format",
        ),
        ("image", "error[EN1304]: `--image=<v>` is not an image kind"),
        ("trace", "error[EN1304]: `--trace=<v>` is not a trace level"),
    ] {
        h.case(format!("reject/a typed --{field} is escaped"), move || {
            let text = render(&[err("i386-none", &bad(field))]);
            assert!(!text.contains('\x1b'), "{text:?}");
            assert_eq!(
                text.lines().next(),
                Some(head.replace("<v>", escaped).as_str())
            );
        });
    }
    h.case("reject/a typed target is escaped", move || {
        let text = render(&[err(typed, &TargetOpts::default())]);
        assert!(!text.contains('\x1b'), "{text:?}");
        let head = format!("error[EN1303]: unknown target `{escaped}`");
        assert_eq!(text.lines().next(), Some(head.as_str()));
    });
}

/// The sentences of SPEC 10.1 this file turns into behaviour.
fn spec_sentences(h: &mut Harness) {
    for sentence in [
        "Default: `i386` on `i386-*`, `x86-64` on `x86_64-*`.",
        "`pentium-m` and `core-duo` are EN0912, because those chips have no long mode.",
        "`native` is rejected (EN0909): the host is never the target.",
        "An `i386`-family level on an `x86_64-*` target is EN0912.",
    ] {
        h.case(
            format!("reject/SPEC 10.1 still says/{sentence}"),
            move || {
                let text = section("SPEC.md", "### 10.1 The option");
                assert!(text.contains(sentence), "the rule has changed");
            },
        );
    }
}
