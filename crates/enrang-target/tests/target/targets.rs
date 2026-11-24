//! The target table of ARCHITECTURE 2.7, the rows' other fields, and the commands
//! and test cells the documents build.

use enrang_target::{
    Addressing, Arch, CodeMode, CpuLevel, FloatStrategy, ForeignKind, OsLayer, OutputFormat,
    PanicPolicy, TargetOpts, TargetSpec, all_targets, host_target, resolve,
};
use enrang_testkit::Harness;

use crate::support::{TARGETS, Table, default_spec, doc, level, number, ok, section, spec, table};

fn target_table() -> Table {
    table(
        section("ARCHITECTURE.md", "### 2.7 TargetSpec"),
        &[
            "Target",
            "P",
            "Default `--cpu`",
            "Default float",
            "Format",
            "Base",
            "OS layer",
        ],
    )
}

fn unquoted(cell: &str) -> &str {
    cell.trim_matches('`')
}

pub fn register(h: &mut Harness) {
    names(h);
    table_columns(h);
    other_fields(h);
    vm_twins(h);
    pe_parameters(h);
    documented_commands(h);
    test_cells(h);
}

fn names(h: &mut Harness) {
    h.case(
        "target/all_targets is the table's first column, in order",
        || {
            let table = target_table();
            let doc: Vec<&str> = table.rows.iter().map(|row| unquoted(&row[0])).collect();
            assert_eq!(all_targets(), doc);
        },
    );
    h.case("target/no name twice", || {
        let names = all_targets();
        for (index, name) in names.iter().enumerate() {
            assert!(!names[index + 1..].contains(name), "{name}");
        }
    });
    for target in TARGETS {
        h.case(
            format!("target/{target} resolves under its own name"),
            move || {
                assert_eq!(default_spec(target).name, target);
            },
        );
    }
    h.case("target/the host is a hosted 64-bit target", || {
        let host = host_target();
        assert!(all_targets().contains(&host), "{host}");
        let built = default_spec(host);
        assert_eq!(built.arch, Arch::X86_64);
        assert!(!built.is_freestanding());
    });
    h.case("target/the host follows the compiler's own OS", || {
        let want = if cfg!(windows) {
            "x86_64-windows"
        } else {
            "x86_64-linux"
        };
        assert_eq!(host_target(), want);
    });
    h.case("target/the flag's list is the native rows", || {
        let flags = table(
            section("ARCHITECTURE.md", "## 11. Driver and CLI"),
            &["Flag", "Values"],
        );
        let cell = &flags.row("`--target=`")[1];
        let named: Vec<&str> = cell.split('`').skip(1).step_by(2).collect();
        let native: Vec<&str> = all_targets()
            .iter()
            .copied()
            .filter(|name| default_spec(name).arch != Arch::Mir)
            .collect();
        assert_eq!(named, native);
    });
}

/// Each column of the table, each row, read from the document.
fn table_columns(h: &mut Harness) {
    let table = target_table();
    for row in &table.rows {
        let target = unquoted(&row[0]).to_owned();
        let cells = row.clone();

        let (name, want) = (target.clone(), number(&cells[1]));
        h.case(format!("table/{target}/P"), move || {
            assert_eq!(u64::from(default_spec(&name).layout.ptr_bytes), want);
        });

        let (name, want) = (target.clone(), cells[2].clone());
        h.case(format!("table/{target}/default cpu"), move || {
            let built = default_spec(&name);
            if want == "n/a" {
                assert_eq!(built.arch, Arch::Mir, "only the VM has no `--cpu`");
                let flagged = resolve(&name, &crate::support::cpu(built.cpu.name()));
                assert!(flagged.is_err(), "the VM refuses any `--cpu`");
            } else {
                assert_eq!(built.cpu, level(unquoted(&want)));
            }
        });

        let (name, want) = (target.clone(), cells[3].clone());
        h.case(format!("table/{target}/default float"), move || {
            let built = default_spec(&name);
            if want == "host or `--float=soft`" {
                assert_eq!(built.float, FloatStrategy::Host);
                let soft = spec(&name, &crate::support::float("soft"));
                assert_eq!(soft.float, FloatStrategy::Soft);
            } else {
                assert_eq!(built.float.name(), unquoted(&want));
            }
        });

        let (name, want) = (target.clone(), cells[4].clone());
        h.case(format!("table/{target}/format"), move || {
            let default = match want.as_str() {
                "ELF64 ET_EXEC" => OutputFormat::Elf64,
                "ELF32 ET_EXEC" => OutputFormat::Elf32,
                "PE32+ CUI" => OutputFormat::Pe { subsystem: 3 },
                "flat or BIOS image" | "flat, BIOS image, or PE32+ EFI" => OutputFormat::Flat,
                "none" => OutputFormat::None,
                other => panic!("a format the suite cannot read: `{other}`"),
            };
            assert_eq!(default_spec(&name).format, default);
        });

        let (name, want) = (target.clone(), cells[5].clone());
        h.case(format!("table/{target}/base"), move || {
            let base = if want == "n/a" {
                0
            } else {
                number(unquoted(&want))
            };
            assert_eq!(default_spec(&name).image.base, base);
        });

        let (name, want) = (target.clone(), cells[6].clone());
        h.case(format!("table/{target}/os layer"), move || {
            let os = match want.as_str() {
                "raw `syscall`" => OsLayer::LinuxX64,
                "`kernel32.dll` imports" => OsLayer::Win64Imports,
                "`int 0x80`" => OsLayer::LinuxInt80,
                "none" | "none or UEFI" => OsLayer::None,
                "`os/vm`" => OsLayer::Vm,
                other => panic!("an OS layer the suite cannot read: `{other}`"),
            };
            assert_eq!(default_spec(&name).os, os);
        });
    }
    h.case("table/P is 4 on i386-*, 8 on x86_64-* (SPEC 11)", || {
        let text = section("SPEC.md", "## 11. Runtime data layout");
        assert!(text.contains("`P` (4 on `i386-*`, 8 on `x86_64-*`)"));
        for target in ["i386-linux", "i386-none"] {
            assert_eq!(default_spec(target).layout.ptr_bytes, 4);
        }
        for target in ["x86_64-linux", "x86_64-windows", "x86_64-none"] {
            assert_eq!(default_spec(target).layout.ptr_bytes, 8);
        }
    });
    h.case(
        "table/freestanding bases are what SPEC 7.8 and ARCHITECTURE 9.5 say",
        || {
            let text = section("ARCHITECTURE.md", "### 9.5 Flat");
            assert!(text.contains(
                "Default base is `0x10000` on `i386-none` and `0x100000` on `x86_64-none`"
            ));
            assert_eq!(default_spec("i386-none").image.base, 0x10000);
            assert_eq!(default_spec("x86_64-none").image.base, 0x100000);
        },
    );
}

/// One row: the fields the table in 2.7 has no column for. The documents state them
/// in prose, so the suite states them again here rather than read prose.
struct Row {
    target: &'static str,
    arch: Arch,
    mode: CodeMode,
    addressing: Addressing,
    alloc_default: bool,
    panic: PanicPolicy,
    foreign: ForeignKind,
    shadow: u32,
    freestanding: bool,
    stack_size: u64,
    probe: Option<u32>,
    page: u32,
    section_align: u32,
    file_align: u32,
    floor: CpuLevel,
}

const ROWS: &[Row] = &[
    Row {
        target: "x86_64-linux",
        arch: Arch::X86_64,
        mode: CodeMode::M64,
        addressing: Addressing::RipRelative,
        alloc_default: true,
        panic: PanicPolicy::Exit(101),
        foreign: ForeignKind::SysV,
        shadow: 0,
        freestanding: false,
        stack_size: 0,
        probe: Some(0x1000),
        page: 0x1000,
        section_align: 1,
        file_align: 1,
        floor: CpuLevel::X86_64,
    },
    Row {
        target: "x86_64-windows",
        arch: Arch::X86_64,
        mode: CodeMode::M64,
        addressing: Addressing::RipRelative,
        alloc_default: true,
        panic: PanicPolicy::Exit(101),
        foreign: ForeignKind::Win64,
        shadow: 32,
        freestanding: false,
        stack_size: 8 * 1024 * 1024,
        probe: Some(0x1000),
        page: 0x1000,
        section_align: 0x1000,
        file_align: 0x200,
        floor: CpuLevel::X86_64,
    },
    Row {
        target: "i386-linux",
        arch: Arch::I386,
        mode: CodeMode::M32,
        addressing: Addressing::Absolute32,
        alloc_default: true,
        panic: PanicPolicy::Exit(101),
        foreign: ForeignKind::None,
        shadow: 0,
        freestanding: false,
        stack_size: 0,
        probe: Some(0x1000),
        page: 0x1000,
        section_align: 1,
        file_align: 1,
        floor: CpuLevel::I386,
    },
    Row {
        target: "i386-none",
        arch: Arch::I386,
        mode: CodeMode::M32,
        addressing: Addressing::Absolute32,
        alloc_default: false,
        panic: PanicPolicy::UserHandler,
        foreign: ForeignKind::None,
        shadow: 0,
        freestanding: true,
        stack_size: 16 * 1024,
        probe: None,
        page: 0x1000,
        section_align: 1,
        file_align: 1,
        floor: CpuLevel::I386,
    },
    Row {
        target: "x86_64-none",
        arch: Arch::X86_64,
        mode: CodeMode::M64,
        addressing: Addressing::RipRelative,
        alloc_default: false,
        panic: PanicPolicy::UserHandler,
        foreign: ForeignKind::None,
        shadow: 0,
        freestanding: true,
        stack_size: 16 * 1024,
        probe: None,
        page: 0x1000,
        section_align: 1,
        file_align: 1,
        floor: CpuLevel::X86_64,
    },
    Row {
        target: "vm64",
        arch: Arch::Mir,
        mode: CodeMode::M64,
        addressing: Addressing::RipRelative,
        alloc_default: true,
        panic: PanicPolicy::VmPause,
        foreign: ForeignKind::None,
        shadow: 0,
        freestanding: false,
        stack_size: 0,
        probe: None,
        page: 0,
        section_align: 0,
        file_align: 0,
        floor: CpuLevel::X86_64,
    },
    Row {
        target: "vm32",
        arch: Arch::Mir,
        mode: CodeMode::M32,
        addressing: Addressing::Absolute32,
        alloc_default: true,
        panic: PanicPolicy::VmPause,
        foreign: ForeignKind::None,
        shadow: 0,
        freestanding: false,
        stack_size: 0,
        probe: None,
        page: 0,
        section_align: 0,
        file_align: 0,
        floor: CpuLevel::I386,
    },
];

fn field_case(
    h: &mut Harness,
    target: &'static str,
    field: &str,
    check: impl FnOnce(&TargetSpec) + Send + 'static,
) {
    h.case(format!("row/{target}/{field}"), move || {
        check(&default_spec(target));
    });
}

fn other_fields(h: &mut Harness) {
    for row in ROWS {
        let t = row.target;
        let arch = row.arch;
        field_case(h, t, "arch", move |s| assert_eq!(s.arch, arch));
        let mode = row.mode;
        field_case(h, t, "code mode", move |s| assert_eq!(s.code_mode, mode));
        let addressing = row.addressing;
        field_case(h, t, "addressing", move |s| {
            assert_eq!(s.addressing, addressing)
        });
        let alloc = row.alloc_default;
        field_case(h, t, "alloc default", move |s| {
            assert_eq!(s.alloc_default, alloc)
        });
        let panic = row.panic;
        field_case(h, t, "panic", move |s| assert_eq!(s.panic, panic));
        let foreign = row.foreign;
        field_case(h, t, "foreign kind", move |s| {
            assert_eq!(s.foreign.kind, foreign)
        });
        let shadow = row.shadow;
        field_case(h, t, "shadow", move |s| {
            assert_eq!(s.foreign.shadow_bytes, shadow)
        });
        let freestanding = row.freestanding;
        field_case(h, t, "freestanding", move |s| {
            assert_eq!(s.is_freestanding(), freestanding)
        });
        let stack = row.stack_size;
        field_case(h, t, "stack size", move |s| assert_eq!(s.stack.size, stack));
        let probe = row.probe;
        field_case(h, t, "probe interval", move |s| {
            assert_eq!(s.stack.probe_interval, probe)
        });
        field_case(h, t, "limit check", move |s| {
            assert_eq!(s.stack.limit_check, freestanding)
        });
        let page = row.page;
        field_case(h, t, "page size", move |s| {
            assert_eq!(s.image.page_size, page)
        });
        let section_align = row.section_align;
        field_case(h, t, "section align", move |s| {
            assert_eq!(s.image.section_align, section_align)
        });
        let file_align = row.file_align;
        field_case(h, t, "file align", move |s| {
            assert_eq!(s.image.file_align, file_align)
        });
        let floor = row.floor;
        field_case(h, t, "floor", move |s| {
            assert_eq!(s.floor, floor.features(s.arch));
            assert!(
                s.allowed.contains_all(s.floor),
                "the floor is below the level"
            );
            assert_eq!(s.allowed, s.cpu.features(s.arch));
        });
    }
    h.case("row/every target has a row", || {
        let rows: Vec<&str> = ROWS.iter().map(|row| row.target).collect();
        assert_eq!(rows, TARGETS);
    });
    h.case("row/no row's own default is the x87 strategy", || {
        // Each row's default `--cpu` sits below the levels that default to x87.
        for target in TARGETS {
            assert_ne!(default_spec(target).float, FloatStrategy::X87);
        }
    });
    h.case(
        "row/x87 is the default at i586 and i686 on i386-* only",
        || {
            for target in TARGETS {
                let built = default_spec(target);
                for rung in CpuLevel::for_arch(built.arch) {
                    let float = spec(target, &crate::support::cpu(rung.name())).float;
                    assert_eq!(
                        float,
                        crate::support::default_float(built.arch, *rung),
                        "{target} at {}",
                        rung.name()
                    );
                    let x87 = matches!(rung, CpuLevel::I586 | CpuLevel::I686);
                    assert_eq!(float == FloatStrategy::X87, x87, "{target}");
                }
            }
        },
    );
    h.case("row/the freestanding stack is ARCHITECTURE 9.6's", || {
        let text = section("ARCHITECTURE.md", "### 9.6 BIOS images");
        assert!(text.contains("default stack 16 KB in `.bss.stack`"));
    });
    h.case("row/hosted panics exit 101, as SPEC 9.1 says", || {
        let text = section("SPEC.md", "### 9.1 Panics");
        assert!(text.contains("exits with status 101"));
        assert!(text.contains("Freestanding: calls `@panicHandler`"));
    });
    h.case("row/the level does not move the floor", || {
        let high = spec("i386-linux", &crate::support::cpu("sse2"));
        assert_eq!(high.floor, default_spec("i386-linux").floor);
        assert_ne!(high.allowed, high.floor);
    });
}

fn vm_twins(h: &mut Harness) {
    h.case("vm/DEV_RUNTIME names the twins", || {
        let text = section("DEV_RUNTIME.md", "## 2. The VM");
        assert!(text.contains(
            "`vm64` borrows the `x86_64-linux` layout and is the dev default; `vm32` borrows `i386-linux`"
        ));
    });
    for (vm, twin) in [("vm64", "x86_64-linux"), ("vm32", "i386-linux")] {
        h.case(format!("vm/{vm} keeps the layout of {twin}"), move || {
            assert_eq!(default_spec(vm).layout, default_spec(twin).layout);
        });
        h.case(format!("vm/{vm} keeps the level of {twin}"), move || {
            let (vm, twin) = (default_spec(vm), default_spec(twin));
            assert_eq!(vm.cpu, twin.cpu);
            assert_eq!(vm.allowed, twin.allowed);
            assert_eq!(vm.floor, twin.floor);
            assert_eq!(vm.code_mode, twin.code_mode);
        });
        h.case(
            format!("vm/{vm} has no image, format or registers"),
            move || {
                let vm = default_spec(vm);
                assert_eq!(vm.format, OutputFormat::None);
                assert_eq!(vm.os, OsLayer::Vm);
                assert_eq!(vm.image.base, 0);
                assert!(vm.cc.int_args.is_empty());
                assert!(vm.cc.scratch.is_empty());
                assert!(vm.cc.xmm_alloc.is_empty());
            },
        );
        h.case(format!("vm/{vm} takes --float=soft"), move || {
            let soft = spec(vm, &crate::support::float("soft"));
            assert_eq!(soft.float, FloatStrategy::Soft);
            assert_eq!(soft.layout, default_spec(twin).layout);
        });
    }
}

/// ARCHITECTURE 9.4's values for the PE row.
fn pe_parameters(h: &mut Harness) {
    let optional = table(
        section("ARCHITECTURE.md", "### 9.4 PE32+ (`x86_64-windows`, EFI)"),
        &["Opt off", "Field", "Value"],
    );
    let aligns = optional.get("32, 36", "Value").to_owned();
    h.case("pe/section and file alignment", move || {
        let quoted: Vec<&str> = aligns.split('`').skip(1).step_by(2).collect();
        assert_eq!(quoted.len(), 2, "{aligns}");
        let image = default_spec("x86_64-windows").image;
        assert_eq!(u64::from(image.section_align), number(quoted[0]));
        assert_eq!(u64::from(image.file_align), number(quoted[1]));
    });
    let base = optional.get("24", "Value").to_owned();
    h.case("pe/image base", move || {
        let quoted: Vec<&str> = base.split('`').skip(1).step_by(2).collect();
        assert_eq!(default_spec("x86_64-windows").image.base, number(quoted[0]));
    });
    let subsystem = optional.get("68", "Value").to_owned();
    h.case("pe/subsystem", move || {
        assert_eq!(subsystem, "3 CUI; 10 EFI application");
        assert_eq!(
            default_spec("x86_64-windows").format,
            OutputFormat::Pe { subsystem: 3 }
        );
        let efi = TargetOpts {
            format: Some("efi".to_owned()),
            ..TargetOpts::default()
        };
        assert_eq!(
            spec("x86_64-none", &efi).format,
            OutputFormat::Pe { subsystem: 10 }
        );
    });
    let reserve = optional.get("72, 80", "Value").to_owned();
    h.case("pe/stack reserve", move || {
        assert!(reserve.contains("default 8 MiB"), "{reserve}");
        assert_eq!(default_spec("x86_64-windows").stack.size, 8 << 20);
    });
}

/// Turns `--flag=value` words into options. `None` for a word it does not know, so
/// a document that starts using a new flag fails here until the suite reads it.
fn parse_flags(words: &[&str]) -> (Option<String>, TargetOpts) {
    let mut target = None;
    let mut opts = TargetOpts::default();
    for word in words {
        let (flag, value) = word
            .split_once('=')
            .unwrap_or_else(|| panic!("`{word}` is not `--flag=value`"));
        let owned = Some(value.to_owned());
        match flag {
            "--target" => target = owned,
            "--cpu" => opts.cpu = owned,
            "--float" => opts.float = owned,
            "--format" => opts.format = owned,
            "--image" => opts.image = owned,
            "--base" => opts.base = Some(number(value)),
            "--stack-size" => opts.stack_size = Some(number(value)),
            "--trace" => opts.trace = owned,
            other => panic!("a flag the suite cannot read: `{other}`"),
        }
    }
    (target, opts)
}

/// Every concrete `enrang build` the case markers of SPEC.md run, plus the
/// documented kernel builds: a document's command must resolve.
fn documented_commands(h: &mut Harness) {
    let spec_md = doc("SPEC.md");
    let mut commands: Vec<String> = spec_md
        .lines()
        .filter_map(|line| line.strip_prefix("<!-- case: "))
        .filter_map(|line| line.split_once("cmd=\"").map(|(_, rest)| rest))
        .filter_map(|rest| rest.split_once('"').map(|(cmd, _)| cmd.to_owned()))
        .filter(|cmd| cmd.contains("--target="))
        .collect();
    assert!(commands.len() >= 4, "only {commands:?}");
    commands.dedup();
    for cmd in commands {
        h.case(format!("command/{cmd}"), move || {
            let words: Vec<&str> = cmd
                .split_whitespace()
                .filter(|word| word.starts_with("--"))
                .collect();
            let (target, opts) = parse_flags(&words);
            ok(&target.expect("a --target"), &opts);
        });
    }
    let more: &[&[&str]] = &[
        // SPEC 7.5's raw boot sector and TESTING 19's corpus test.
        &["--target=i386-none", "--format=flat", "--base=0x7C00"],
        // TESTING 19.
        &["--target=i386-none", "--base=0x100000"],
        // TESTING 14's freestanding cells.
        &["--target=i386-none", "--stack-size=1048576"],
        // TESTING 20's owner checklist and ARCHITECTURE 9.7.
        &["--target=x86_64-none", "--image=hdd"],
        &["--target=x86_64-none", "--format=efi"],
        &["--target=i386-none", "--image=floppy"],
    ];
    for words in more {
        let name = words.join(" ");
        let words = words.to_vec();
        h.case(format!("command/{name}"), move || {
            let (target, opts) = parse_flags(&words);
            ok(&target.expect("a --target"), &opts);
        });
    }
}

/// Every cell of TESTING's matrix resolves to what its row says.
fn test_cells(h: &mut Harness) {
    let cells = table(
        section(
            "TESTING.md",
            "## 12. Conformance corpus and implementation matrix",
        ),
        &[
            "Cell",
            "Target",
            "`--cpu`",
            "Float",
            "Runs on this machine",
            "From",
        ],
    );
    assert_eq!(cells.rows.len(), 18, "the matrix's cells");
    // The cells that ask for `soft` where their level defaults to another strategy,
    // so their float is not what the level gives with no flag (SPEC 10.1, TESTING 12).
    const NOT_THE_DEFAULT: [&str; 4] = ["vm32-soft", "l32-i586", "l32-i686", "l32-sse2s"];
    let names: Vec<String> = cells
        .rows
        .iter()
        .map(|row| unquoted(&row[0]).to_owned())
        .collect();
    h.case(
        "cell/the cells that set their float are in the matrix",
        move || {
            for cell in NOT_THE_DEFAULT {
                assert!(names.iter().any(|name| name == cell), "{cell}");
            }
        },
    );
    for row in cells.rows {
        let cell = unquoted(&row[0]).to_owned();
        let target_cell = row[1].clone();
        let level_cell = unquoted(&row[2]).to_owned();
        let float_cell = unquoted(&row[3]).to_owned();
        h.case(format!("cell/{cell}"), move || {
            let (target, mut opts) = if target_cell == "VM" {
                let name = if cell.starts_with("vm64") {
                    "vm64"
                } else {
                    "vm32"
                };
                (name.to_owned(), TargetOpts::default())
            } else {
                // `i386-none`, with a shim, or `x86_64-none --format=efi`.
                let quoted: Vec<&str> = target_cell.split('`').skip(1).step_by(2).collect();
                let mut words = quoted[0].split_whitespace();
                let target = words.next().expect("a target").to_owned();
                let flags: Vec<String> = words.map(|word| word.to_owned()).collect();
                let flags: Vec<&str> = flags.iter().map(String::as_str).collect();
                (target, parse_flags(&flags).1)
            };
            if !level_cell.is_empty() {
                opts.cpu = Some(level_cell.clone());
            }
            if float_cell != "host" {
                opts.float = Some(float_cell.clone());
            }
            let built = spec(&target, &opts);
            assert_eq!(built.float.name(), float_cell);
            if !level_cell.is_empty() {
                assert_eq!(built.cpu.name(), level_cell);
            }
            // Dropping the float flag must give the same default, except for the
            // cells that ask for `soft` where the level defaults to something else.
            opts.float = None;
            let by_default = spec(&target, &opts).float.name();
            if NOT_THE_DEFAULT.contains(&cell.as_str()) {
                assert_ne!(
                    by_default, float_cell,
                    "the cell's float is set, not the default"
                );
                assert_eq!(
                    float_cell, "soft",
                    "a cell only ever overrides the default with `soft`"
                );
            } else {
                assert_eq!(by_default, float_cell, "the cell's float is the default");
            }
        });
    }
}
