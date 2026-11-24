//! The output flags: `--format`, `--image`, `--base`, `--stack-size` and `--trace`
//! (ARCHITECTURE 11), each against every target.

use enrang_diag::{Code, Diagnostic};
use enrang_target::{
    ForeignKind, ImageKind, OsLayer, OutputFormat, Reg, TargetOpts, TargetSpec, TraceLevel, Xmm,
};
use enrang_testkit::Harness;

use crate::support::{
    NATIVE_TARGETS, TARGETS, VM_TARGETS, default_spec, err, says, section, spec, table,
};

fn format_flag(value: &str) -> TargetOpts {
    TargetOpts {
        format: Some(value.to_owned()),
        ..TargetOpts::default()
    }
}

fn image_flag(value: &str) -> TargetOpts {
    TargetOpts {
        image: Some(value.to_owned()),
        ..TargetOpts::default()
    }
}

fn base_flag(value: u64) -> TargetOpts {
    TargetOpts {
        base: Some(value),
        ..TargetOpts::default()
    }
}

fn stack_flag(value: u64) -> TargetOpts {
    TargetOpts {
        stack_size: Some(value),
        ..TargetOpts::default()
    }
}

fn trace_flag(value: &str) -> TargetOpts {
    TargetOpts {
        trace: Some(value.to_owned()),
        ..TargetOpts::default()
    }
}

fn is_flag_error(diag: &Diagnostic) {
    assert_eq!(diag.code, Code::EN1304, "{}", diag.message);
    assert_eq!(diag.entries.len(), 1, "one note says why");
}

pub fn register(h: &mut Harness) {
    flag_values(h);
    formats(h);
    images(h);
    bases(h);
    stacks(h);
    traces(h);
    vm_rows(h);
}

fn flag_values(h: &mut Harness) {
    let flags = table(
        section("ARCHITECTURE.md", "## 11. Driver and CLI"),
        &["Flag", "Values", "Notes"],
    );
    let listed = |flag: &str| -> Vec<String> {
        flags.row(flag)[1]
            .split('`')
            .skip(1)
            .step_by(2)
            .map(str::to_owned)
            .collect()
    };
    let formats = listed("`--format=`");
    let images = listed("`--image=`");
    let traces = listed("`--trace=`");
    h.case(
        "output/the document lists the values the suite tests",
        move || {
            assert_eq!(formats, ["elf", "pe", "flat", "efi"]);
            assert_eq!(images, ["floppy", "hdd"]);
            assert_eq!(traces, ["full", "fn", "none"]);
        },
    );
}

const PE_CUI: OutputFormat = OutputFormat::Pe { subsystem: 3 };
const PE_EFI: OutputFormat = OutputFormat::Pe { subsystem: 10 };

fn formats(h: &mut Harness) {
    // `Some(format)` when the flag fits the target, from the table in 2.7.
    let rows: &[(&str, [Option<OutputFormat>; 4])] = &[
        (
            "x86_64-linux",
            [Some(OutputFormat::Elf64), None, None, None],
        ),
        ("x86_64-windows", [None, Some(PE_CUI), None, None]),
        ("i386-linux", [Some(OutputFormat::Elf32), None, None, None]),
        ("i386-none", [None, None, Some(OutputFormat::Flat), None]),
        (
            "x86_64-none",
            [None, None, Some(OutputFormat::Flat), Some(PE_EFI)],
        ),
    ];
    for &(target, row) in rows {
        for (flag, want) in ["elf", "pe", "flat", "efi"].into_iter().zip(row) {
            h.case(format!("format/{flag} on {target}"), move || match want {
                Some(format) => assert_eq!(spec(target, &format_flag(flag)).format, format),
                None => {
                    let diag = err(target, &format_flag(flag));
                    is_flag_error(&diag);
                    assert_eq!(
                        diag.message,
                        format!("`--format={flag}` does not fit target `{target}`")
                    );
                    says(&diag, &[target, "builds"]);
                }
            });
        }
    }
    // Target, `--format`, and the image: base, page, section and file alignment.
    // ARCHITECTURE 9.4 fixes the two alignments of a PE image, EFI or not. Its
    // `ImageBase` of 0x140000000 disagrees with the `x86_64-none` row of 2.7 for EFI:
    // this keeps the row's until the documents settle it.
    let images: &[(&str, Option<&str>, (u64, u32, u32, u32))] = &[
        ("x86_64-none", None, (0x10_0000, 0x1000, 1, 1)),
        ("x86_64-none", Some("flat"), (0x10_0000, 0x1000, 1, 1)),
        (
            "x86_64-none",
            Some("efi"),
            (0x10_0000, 0x1000, 0x1000, 0x200),
        ),
        (
            "x86_64-windows",
            None,
            (0x1_4000_0000, 0x1000, 0x1000, 0x200),
        ),
        (
            "x86_64-windows",
            Some("pe"),
            (0x1_4000_0000, 0x1000, 0x1000, 0x200),
        ),
        ("i386-none", Some("flat"), (0x1_0000, 0x1000, 1, 1)),
    ];
    for &(target, format, (base, page, section_align, file_align)) in images {
        h.case(
            format!("format/image of {target} under {format:?}"),
            move || {
                let opts = format.map_or_else(TargetOpts::default, format_flag);
                let image = spec(target, &opts).image;
                assert_eq!(
                    (
                        image.base,
                        image.page_size,
                        image.section_align,
                        image.file_align
                    ),
                    (base, page, section_align, file_align)
                );
            },
        );
    }
    h.case(
        "format/efi changes the OS layer and the foreign ABI",
        || {
            let built = spec("x86_64-none", &format_flag("efi"));
            assert_eq!(built.os, OsLayer::Uefi);
            assert_eq!(built.foreign.kind, ForeignKind::Win64);
            assert_eq!(built.foreign.shadow_bytes, 32);
            assert_eq!(built.foreign.extra_saved, [Reg::Si, Reg::Di]);
            assert_eq!(
                built.foreign.extra_saved_xmm,
                [
                    Xmm::Xmm6,
                    Xmm::Xmm7,
                    Xmm::Xmm8,
                    Xmm::Xmm9,
                    Xmm::Xmm10,
                    Xmm::Xmm11,
                    Xmm::Xmm12,
                    Xmm::Xmm13,
                    Xmm::Xmm14,
                    Xmm::Xmm15,
                ]
            );
            assert!(built.is_freestanding(), "UEFI is still freestanding");
            assert!(!built.alloc_default, "`alloc` stays optional under UEFI");
        },
    );
    h.case("format/flat keeps the default OS layer", || {
        let built = spec("x86_64-none", &format_flag("flat"));
        assert_eq!(built, default_spec("x86_64-none"));
    });
    for &target in &NATIVE_TARGETS {
        h.case(
            format!("format/the default on {target} is one it accepts"),
            move || {
                let default = default_spec(target);
                let same = match default.format {
                    OutputFormat::Elf64 | OutputFormat::Elf32 => spec(target, &format_flag("elf")),
                    OutputFormat::Pe { .. } => spec(target, &format_flag("pe")),
                    OutputFormat::Flat => spec(target, &format_flag("flat")),
                    other => panic!("{other:?}"),
                };
                assert_eq!(same, default);
            },
        );
    }
    let bad = [
        ("", None),
        ("coff", None),
        ("ELF", Some("elf")),
        ("elf64", None),
        ("elf3", Some("elf")),
        ("pe32", None),
        ("pe3", Some("pe")),
        ("flatt", Some("flat")),
        ("efii", Some("efi")),
    ];
    for (name, suggestion) in bad {
        for target in NATIVE_TARGETS {
            h.case(format!("format/`{name}` on {target}"), move || {
                let diag = err(target, &format_flag(name));
                is_flag_error(&diag);
                assert_eq!(
                    diag.message,
                    format!("`--format={name}` is not an output format")
                );
                check_suggestion(&diag, "--format", suggestion);
            });
        }
    }
}

fn check_suggestion(diag: &Diagnostic, flag: &str, suggestion: Option<&str>) {
    match suggestion {
        Some(found) => {
            assert_eq!(diag.helps.len(), 1, "{:?}", diag.helps);
            assert_eq!(
                diag.helps[0].message,
                format!("did you mean `{flag}={found}`?")
            );
        }
        None => assert!(diag.helps.is_empty(), "{:?}", diag.helps),
    }
}

fn images(h: &mut Harness) {
    let kinds = [("floppy", ImageKind::Floppy144), ("hdd", ImageKind::Hdd)];
    for (flag, kind) in kinds {
        for target in ["i386-none", "x86_64-none"] {
            h.case(format!("image/{flag} on {target}"), move || {
                let built = spec(target, &image_flag(flag));
                assert_eq!(built.format, OutputFormat::BiosImage(kind));
                assert_eq!(built.image.base, default_spec(target).image.base);
            });
        }
        for target in ["x86_64-linux", "x86_64-windows", "i386-linux"] {
            h.case(format!("image/{flag} on hosted {target}"), move || {
                let diag = err(target, &image_flag(flag));
                is_flag_error(&diag);
                says(&diag, &["freestanding", "i386-none"]);
            });
        }
    }
    for (name, suggestion) in [
        ("", None),
        ("cdrom", None),
        ("HDD", Some("hdd")),
        ("hd", Some("hdd")),
        ("floppie", Some("floppy")),
    ] {
        for target in ["i386-none", "x86_64-none", "i386-linux"] {
            h.case(format!("image/`{name}` on {target}"), move || {
                let diag = err(target, &image_flag(name));
                is_flag_error(&diag);
                assert_eq!(
                    diag.message,
                    format!("`--image={name}` is not an image kind")
                );
                check_suggestion(&diag, "--image", suggestion);
            });
        }
    }
    for format in ["flat", "efi", "elf", "pe"] {
        h.case(format!("image/hdd with --format={format}"), move || {
            let opts = TargetOpts {
                format: Some(format.to_owned()),
                image: Some("hdd".to_owned()),
                ..TargetOpts::default()
            };
            let target = if format == "flat" || format == "efi" {
                "x86_64-none"
            } else if format == "elf" {
                "i386-linux"
            } else {
                "x86_64-windows"
            };
            let diag = err(target, &opts);
            is_flag_error(&diag);
            assert_eq!(diag.message, "`--image` and `--format` cannot be combined");
        });
    }
}

fn with_base(format: Option<&str>, image: Option<&str>, base: u64) -> TargetOpts {
    TargetOpts {
        format: format.map(str::to_owned),
        image: image.map(str::to_owned),
        base: Some(base),
        ..TargetOpts::default()
    }
}

fn bases(h: &mut Harness) {
    // What SPEC and TESTING build with a base, and the boundary of the address space.
    let accepted: &[(&str, Option<&str>, Option<&str>, u64)] = &[
        ("i386-none", None, None, 0x10_0000),
        ("i386-none", Some("flat"), None, 0x7C00),
        ("i386-none", None, Some("hdd"), 0x10_0000),
        ("i386-none", None, Some("floppy"), 0x2_0000),
        ("i386-none", Some("flat"), None, 0),
        ("i386-none", Some("flat"), None, 0xFFFF_FFFF),
        ("x86_64-none", None, None, 0x20_0000),
        ("x86_64-none", None, Some("hdd"), 0x20_0000),
        ("x86_64-none", Some("flat"), None, 0x1_0000_0000),
        ("x86_64-none", Some("flat"), None, u64::MAX),
    ];
    for &(target, format, image, base) in accepted {
        let name = format!("base/{base:#x} on {target} format={format:?} image={image:?}");
        h.case(name, move || {
            let built = spec(target, &with_base(format, image, base));
            assert_eq!(built.image.base, base);
        });
    }
    for base in [0x1_0000_0000, 0x1_0000_0001, u64::MAX] {
        for image in [None, Some("hdd")] {
            h.case(
                format!("base/{base:#x} image={image:?} is past i386-none"),
                move || {
                    let diag = err("i386-none", &with_base(None, image, base));
                    is_flag_error(&diag);
                    says(&diag, &[&format!("{base:#x}"), "i386-none", "0xffffffff"]);
                },
            );
        }
    }
    for target in ["x86_64-linux", "x86_64-windows", "i386-linux"] {
        h.case(
            format!("base/hosted {target} links where it links"),
            move || {
                let diag = err(target, &base_flag(0x20_0000));
                is_flag_error(&diag);
                says(&diag, &[target, "flat output and BIOS images"]);
            },
        );
    }
    h.case("base/efi takes no base", || {
        let diag = err("x86_64-none", &with_base(Some("efi"), None, 0x20_0000));
        is_flag_error(&diag);
    });
    h.case("base/only the base changes", || {
        let built = spec("i386-none", &base_flag(0x10_0000));
        let mut expected = default_spec("i386-none");
        expected.image.base = 0x10_0000;
        assert_eq!(built, expected);
    });
}

fn stacks(h: &mut Harness) {
    let accepted: &[(&str, u64)] = &[
        ("i386-none", 1),
        ("i386-none", 1_048_576),
        ("i386-none", 0x7FFF_FFFF),
        ("x86_64-none", 1_048_576),
        ("x86_64-none", 0x8000_0000),
        ("x86_64-none", i64::MAX as u64),
        ("x86_64-windows", 1_048_576),
        ("x86_64-windows", 0x8000_0000),
    ];
    for &(target, size) in accepted {
        h.case(format!("stack/{size} on {target}"), move || {
            assert_eq!(spec(target, &stack_flag(size)).stack.size, size);
        });
    }
    let refused: &[(&str, u64)] = &[
        ("i386-none", 0),
        ("i386-none", 0x8000_0000),
        ("i386-none", 0xFFFF_FFFF),
        ("i386-none", 0x1_0000_0000),
        ("i386-none", u64::MAX),
        ("x86_64-none", 0),
        ("x86_64-none", i64::MAX as u64 + 1),
        ("x86_64-windows", 0),
        ("x86_64-windows", u64::MAX),
    ];
    for &(target, size) in refused {
        h.case(
            format!("stack/{size} is out of range on {target}"),
            move || {
                let diag = err(target, &stack_flag(size));
                is_flag_error(&diag);
                assert_eq!(
                    diag.message,
                    format!("`--stack-size={size}` does not fit target `{target}`")
                );
            },
        );
    }
    for target in ["x86_64-linux", "i386-linux"] {
        h.case(
            format!("stack/the OS sizes the stack on {target}"),
            move || {
                let diag = err(target, &stack_flag(1_048_576));
                is_flag_error(&diag);
                says(&diag, &["--stack-size", target, "Linux"]);
            },
        );
    }
    h.case(
        "stack/efi keeps the flag, since it is a freestanding stack",
        || {
            let opts = TargetOpts {
                format: Some("efi".to_owned()),
                stack_size: Some(65536),
                ..TargetOpts::default()
            };
            assert_eq!(spec("x86_64-none", &opts).stack.size, 65536);
        },
    );
    h.case("stack/only the size changes", || {
        let built: TargetSpec = spec("i386-none", &stack_flag(32768));
        let mut expected = default_spec("i386-none");
        expected.stack.size = 32768;
        assert_eq!(built, expected);
    });
}

fn traces(h: &mut Harness) {
    let levels = [
        ("full", TraceLevel::Full),
        ("fn", TraceLevel::Fn),
        ("none", TraceLevel::None),
    ];
    for (flag, level) in levels {
        for target in NATIVE_TARGETS {
            h.case(format!("trace/{flag} on {target}"), move || {
                assert_eq!(spec(target, &trace_flag(flag)).trace, level);
            });
        }
    }
    for (name, suggestion) in [
        ("", None),
        ("all", None),
        ("FULL", Some("full")),
        ("ful", Some("full")),
        ("f", Some("fn")),
        ("non", Some("none")),
    ] {
        h.case(format!("trace/`{name}`"), move || {
            let diag = err("x86_64-linux", &trace_flag(name));
            is_flag_error(&diag);
            assert_eq!(
                diag.message,
                format!("`--trace={name}` is not a trace level")
            );
            check_suggestion(&diag, "--trace", suggestion);
        });
    }
    for target in TARGETS {
        h.case(
            format!("trace/the default on {target} is full"),
            move || {
                assert_eq!(default_spec(target).trace, TraceLevel::Full);
            },
        );
    }
}

fn vm_rows(h: &mut Harness) {
    let flags: [(&str, TargetOpts); 6] = [
        ("--format", format_flag("flat")),
        ("--image", image_flag("hdd")),
        ("--base", base_flag(0x1000)),
        ("--stack-size", stack_flag(4096)),
        ("--trace", trace_flag("none")),
        (
            "--format",
            TargetOpts {
                format: Some("elf".to_owned()),
                trace: Some("none".to_owned()),
                ..TargetOpts::default()
            },
        ),
    ];
    for (index, (flag, opts)) in flags.into_iter().enumerate() {
        for target in VM_TARGETS {
            let opts = opts.clone();
            h.case(format!("vm/{index} {flag} on {target}"), move || {
                let diag = err(target, &opts);
                is_flag_error(&diag);
                assert_eq!(
                    diag.message,
                    format!("`{flag}` does not apply to target `{target}`")
                );
                says(&diag, &["writes no output file"]);
            });
        }
    }
}
