//! `Reg`, `Xmm` and the register tables of ARCHITECTURE 7.4 and 7.6.

use std::collections::BTreeSet;

use enrang_target::{Arch, CallConv, CodeMode, ForeignKind, Reg, Xmm};
use enrang_testkit::Harness;

use crate::support::{Table, VM_TARGETS, backticked, default_spec, line_starting, section, table};

const I386_ROWS: [&str; 2] = ["i386-linux", "i386-none"];
const X86_64_ROWS: [&str; 3] = ["x86_64-linux", "x86_64-windows", "x86_64-none"];

/// (target, column of the document's tables, code mode)
fn native() -> Vec<(&'static str, &'static str, CodeMode)> {
    let mut rows = Vec::new();
    for target in I386_ROWS {
        rows.push((target, "i386", CodeMode::M32));
    }
    for target in X86_64_ROWS {
        rows.push((target, "x86-64", CodeMode::M64));
    }
    rows
}

/// The register names in a cell: the backticked words, with `` `a`-`b` `` and
/// `a-b` ranges expanded by their trailing numbers. `none` has no backticks.
fn names_in(cell: &str) -> Vec<String> {
    let joined = cell.replace("`-`", "-");
    let mut names = Vec::new();
    for piece in backticked(&joined) {
        for word in piece.split_whitespace() {
            match word.split_once('-') {
                Some((low, high)) => {
                    let split = low
                        .find(|c: char| c.is_ascii_digit())
                        .unwrap_or_else(|| panic!("`{word}` is not a range"));
                    let (prefix, first) = low.split_at(split);
                    let first: u32 = first.parse().expect("the low end of a range");
                    let last: u32 = high
                        .trim_start_matches(prefix)
                        .parse()
                        .unwrap_or_else(|_| panic!("the high end of `{word}`"));
                    assert!(first < last, "`{word}` is empty");
                    names.extend((first..=last).map(|n| format!("{prefix}{n}")));
                }
                None => names.push(word.to_owned()),
            }
        }
    }
    names
}

/// The name of each of `regs` in `mode`, failing on any `mode` cannot name.
fn reg_names(regs: &[Reg], mode: CodeMode) -> Vec<String> {
    regs.iter()
        .map(|reg| {
            reg.name(mode)
                .unwrap_or_else(|| panic!("{reg:?} does not exist in {mode:?}"))
                .to_owned()
        })
        .collect()
}

fn xmm_names(regs: &[Xmm]) -> Vec<String> {
    regs.iter().map(|reg| reg.name().to_owned()).collect()
}

fn sorted(names: Vec<String>) -> BTreeSet<String> {
    let set: BTreeSet<String> = names.iter().cloned().collect();
    assert_eq!(set.len(), names.len(), "a name twice in {names:?}");
    set
}

fn roles() -> Table {
    table(
        section("ARCHITECTURE.md", "### 7.4 Register strategy"),
        &["Role", "i386", "x86-64"],
    )
}

fn conventions() -> Table {
    table(
        section("ARCHITECTURE.md", "### 7.6 Calling conventions"),
        &["", "i386", "x86-64"],
    )
}

fn cc(target: &str) -> CallConv {
    default_spec(target).cc
}

pub fn register(h: &mut Harness) {
    numbering(h);
    role_table(h);
    convention_table(h);
    win64(h);
    invariants(h);
    vm(h);
}

fn numbering(h: &mut Harness) {
    let gprs = [
        (Reg::Ax, 0, "eax", "rax"),
        (Reg::Cx, 1, "ecx", "rcx"),
        (Reg::Dx, 2, "edx", "rdx"),
        (Reg::Bx, 3, "ebx", "rbx"),
        (Reg::Sp, 4, "esp", "rsp"),
        (Reg::Bp, 5, "ebp", "rbp"),
        (Reg::Si, 6, "esi", "rsi"),
        (Reg::Di, 7, "edi", "rdi"),
    ];
    for (reg, number, name32, name64) in gprs {
        h.case(format!("reg/{name64}"), move || {
            assert_eq!(reg.number(), number);
            assert_eq!(reg.name(CodeMode::M32), Some(name32));
            assert_eq!(reg.name(CodeMode::M64), Some(name64));
            assert!(Reg::for_mode(CodeMode::M32).contains(&reg));
            assert!(Reg::for_mode(CodeMode::M64).contains(&reg));
        });
    }
    let extended = [
        (Reg::R8, 8, "r8"),
        (Reg::R9, 9, "r9"),
        (Reg::R10, 10, "r10"),
        (Reg::R11, 11, "r11"),
        (Reg::R12, 12, "r12"),
        (Reg::R13, 13, "r13"),
        (Reg::R14, 14, "r14"),
        (Reg::R15, 15, "r15"),
    ];
    for (reg, number, name) in extended {
        h.case(format!("reg/{name}"), move || {
            assert_eq!(reg.number(), number);
            assert_eq!(reg.name(CodeMode::M64), Some(name));
            assert_eq!(reg.name(CodeMode::M32), None, "not in 32-bit code");
            assert!(!Reg::for_mode(CodeMode::M32).contains(&reg));
            assert!(Reg::for_mode(CodeMode::M64).contains(&reg));
        });
    }
    h.case("reg/ALL is in number order", || {
        for (index, reg) in Reg::ALL.iter().enumerate() {
            assert_eq!(usize::from(reg.number()), index);
        }
    });
    for (index, xmm) in Xmm::ALL.into_iter().enumerate() {
        h.case(format!("xmm/{index}"), move || {
            assert_eq!(usize::from(xmm.number()), index);
            assert_eq!(xmm.name(), format!("xmm{index}"));
            assert_eq!(Xmm::for_mode(CodeMode::M32).contains(&xmm), index < 8);
            assert!(Xmm::for_mode(CodeMode::M64).contains(&xmm));
        });
    }
}

/// The table of 7.4, each role on each native target.
fn role_table(h: &mut Harness) {
    for (target, column, mode) in native() {
        let role = |name: &str| names_in(roles().get(name, column));
        type Read = fn(&CallConv, CodeMode) -> Vec<String>;
        let cases: Vec<(&str, Vec<String>, Read)> = vec![
            ("scratch", role("Scratch, never allocated"), |c, m| {
                reg_names(c.scratch, m)
            }),
            (
                "allocatable, callee-saved",
                role("Allocatable, callee-saved"),
                |c, m| reg_names(c.alloc_callee, m),
            ),
            (
                "allocatable, caller-saved",
                role("Allocatable, caller-saved"),
                |c, m| reg_names(c.alloc_caller, m),
            ),
            ("xmm allocatable", role("XMM allocatable"), |c, _| {
                xmm_names(c.xmm_alloc)
            }),
            ("xmm scratch", role("XMM scratch"), |c, _| {
                xmm_names(c.xmm_scratch)
            }),
        ];
        for (name, want, read) in cases {
            // In the document's order, so that no list is reordered unnoticed: the
            // allocators of M5 will walk them.
            h.case(format!("roles/{target}/{name}"), move || {
                assert_eq!(read(&cc(target), mode), want);
            });
        }
        let fixed = role("Fixed");
        h.case(
            format!("roles/{target}/fixed is every other register"),
            move || {
                let cc = cc(target);
                let used: BTreeSet<Reg> = cc
                    .scratch
                    .iter()
                    .chain(cc.alloc_callee)
                    .chain(cc.alloc_caller)
                    .copied()
                    .collect();
                let rest: Vec<Reg> = Reg::for_mode(mode)
                    .iter()
                    .copied()
                    .filter(|reg| !used.contains(reg))
                    .collect();
                assert_eq!(sorted(reg_names(&rest, mode)), sorted(fixed));
            },
        );
    }
    h.case("roles/the cell reader expands ranges and `none`", || {
        assert_eq!(names_in("`r12`-`r15`"), ["r12", "r13", "r14", "r15"]);
        assert_eq!(names_in("`rbx rbp r12-r15`").len(), 6);
        assert_eq!(
            names_in("`xmm0`-`xmm2`, `xmm7`"),
            ["xmm0", "xmm1", "xmm2", "xmm7"]
        );
        assert!(names_in("none").is_empty());
    });
}

/// The table of 7.6, each row on each native target.
fn convention_table(h: &mut Harness) {
    for (target, column, mode) in native() {
        let cell = |name: &str| conventions().get(name, column).to_owned();

        let args = cell("Int args");
        h.case(format!("cc/{target}/int args"), move || {
            // The stack has no backticks, and the order matters here.
            assert_eq!(reg_names(cc(target).int_args, mode), names_in(&args));
        });
        let args = cell("Float args");
        h.case(format!("cc/{target}/float args"), move || {
            assert_eq!(xmm_names(cc(target).float_args), names_in(&args));
        });
        let saved = cell("Callee-saved");
        h.case(format!("cc/{target}/callee-saved"), move || {
            let actual = reg_names(cc(target).callee_saved, mode);
            assert_eq!(sorted(actual), sorted(names_in(&saved)));
        });
        let returns = cell("Returns");
        h.case(format!("cc/{target}/int return"), move || {
            // `edx:eax` is high then low; `int_ret` is low then high.
            let quoted = backticked(&returns);
            let pair = quoted.iter().find(|piece| piece.contains(':'));
            let want: Vec<String> = match pair {
                Some(pair) => {
                    let (high, low) = pair.split_once(':').unwrap();
                    vec![low.to_owned(), high.to_owned()]
                }
                None => vec![quoted[0].to_owned()],
            };
            assert_eq!(reg_names(cc(target).int_ret, mode), want);
        });
        let cleanup = cell("Cleanup");
        h.case(format!("cc/{target}/cleanup"), move || {
            let callee = cleanup.starts_with("Callee");
            assert!(callee || cleanup.starts_with("Caller"), "{cleanup}");
            assert_eq!(cc(target).stack_args_callee_pops, callee);
        });
    }
    h.case("cc/SPEC 11 states the same x86-64 registers", || {
        let line = line_starting(
            section("SPEC.md", "## 11. Runtime data layout"),
            "**Calling conventions**",
        );
        assert!(line.contains("i386 pushes all arguments right to left and the callee pops"));
        let quoted = backticked(line);
        let ints: Vec<&str> = quoted[0].split(", ").collect();
        let spelled = reg_names(cc("x86_64-linux").int_args, CodeMode::M64);
        assert_eq!(spelled, ints);
        assert_eq!(quoted[1], "xmm0-7");
        assert_eq!(cc("x86_64-linux").float_args.len(), 8);
        assert!(cc("i386-linux").stack_args_callee_pops);
    });
    h.case(
        "cc/no target uses a red zone, so no field records one",
        || {
            let line = line_starting(
                section("SPEC.md", "## 11. Runtime data layout"),
                "**Calling conventions**",
            );
            assert!(line.contains("No target uses a red zone"), "{line}");
        },
    );
}

fn win64(h: &mut Harness) {
    h.case("win64/the shadow space is 7.6's", || {
        let line = line_starting(
            section("ARCHITECTURE.md", "### 7.6 Calling conventions"),
            "- **Win64:**",
        );
        assert!(line.contains("32 bytes of shadow space"), "{line}");
        assert_eq!(default_spec("x86_64-windows").foreign.shadow_bytes, 32);
    });
    h.case("win64/extra saved registers are 7.6's", || {
        let line = line_starting(
            section("ARCHITECTURE.md", "### 7.6 Calling conventions"),
            "- **`@abi(\"win64\")` entry functions**",
        );
        let mut named: Vec<&str> = backticked(line);
        named.retain(|piece| !piece.starts_with('@') && !piece.starts_with("xmm"));
        let saved = default_spec("x86_64-windows").foreign.extra_saved;
        assert_eq!(reg_names(saved, CodeMode::M64), named);
    });
    h.case(
        "win64/the internal set is a subset of the platform's",
        || {
            // RBX, RBP, RDI, RSI, RSP, R12-R15 by the platform ABI.
            let platform = [
                Reg::Bx,
                Reg::Bp,
                Reg::Di,
                Reg::Si,
                Reg::Sp,
                Reg::R12,
                Reg::R13,
                Reg::R14,
                Reg::R15,
            ];
            for reg in cc("x86_64-windows").callee_saved {
                assert!(platform.contains(reg), "{reg:?}");
            }
        },
    );
    h.case(
        "win64/extra saved fills exactly the gap to the platform's set",
        || {
            let spec = default_spec("x86_64-windows");
            let platform: BTreeSet<Reg> = [
                Reg::Bx,
                Reg::Bp,
                Reg::Di,
                Reg::Si,
                Reg::R12,
                Reg::R13,
                Reg::R14,
                Reg::R15,
            ]
            .into();
            let ours: BTreeSet<Reg> = spec
                .cc
                .callee_saved
                .iter()
                .chain(spec.foreign.extra_saved)
                .copied()
                .collect();
            assert_eq!(ours, platform);
        },
    );
    h.case("win64/SysV needs no extra saves", || {
        let spec = default_spec("x86_64-linux");
        assert_eq!(spec.foreign.kind, ForeignKind::SysV);
        assert!(spec.foreign.extra_saved.is_empty());
        assert!(spec.foreign.extra_saved_xmm.is_empty());
        assert_eq!(spec.foreign.shadow_bytes, 0);
        // RBX, RBP, R12-R15 by the platform ABI, exactly the internal set.
        let platform: BTreeSet<Reg> =
            [Reg::Bx, Reg::Bp, Reg::R12, Reg::R13, Reg::R14, Reg::R15].into();
        let ours: BTreeSet<Reg> = spec.cc.callee_saved.iter().copied().collect();
        assert_eq!(ours, platform);
    });
}

fn disjoint<T: Ord + std::fmt::Debug + Copy>(a: &[T], b: &[T]) {
    let a: BTreeSet<T> = a.iter().copied().collect();
    let b: BTreeSet<T> = b.iter().copied().collect();
    let shared: Vec<&T> = a.intersection(&b).collect();
    assert!(shared.is_empty(), "shared: {shared:?}");
}

fn no_repeats<T: Ord + std::fmt::Debug + Copy>(list: &[T]) {
    let set: BTreeSet<T> = list.iter().copied().collect();
    assert_eq!(set.len(), list.len(), "repeats in {list:?}");
}

/// What a register allocator relies on, on every native target.
fn invariants(h: &mut Harness) {
    type Check = fn(&CallConv, CodeMode);
    let checks: &[(&str, Check)] = &[
        (
            "scratch and callee-saved allocatable do not overlap",
            |c, _| {
                disjoint(c.scratch, c.alloc_callee);
            },
        ),
        (
            "scratch and caller-saved allocatable do not overlap",
            |c, _| {
                disjoint(c.scratch, c.alloc_caller);
            },
        ),
        ("the two allocatable sets do not overlap", |c, _| {
            disjoint(c.alloc_callee, c.alloc_caller);
        }),
        ("xmm scratch and allocatable do not overlap", |c, _| {
            disjoint(c.xmm_alloc, c.xmm_scratch);
        }),
        (
            "the stack and frame pointers are never allocated or scratch",
            |c, _| {
                for reg in c.scratch.iter().chain(c.alloc_callee).chain(c.alloc_caller) {
                    assert!(!matches!(reg, Reg::Sp | Reg::Bp), "{reg:?}");
                }
            },
        ),
        (
            "the stack and frame pointers carry no arguments or returns",
            |c, _| {
                for reg in c.int_args.iter().chain(c.int_ret) {
                    assert!(!matches!(reg, Reg::Sp | Reg::Bp), "{reg:?}");
                }
            },
        ),
        ("callee-saved allocatable is callee-saved", |c, _| {
            for reg in c.alloc_callee {
                assert!(c.callee_saved.contains(reg), "{reg:?}");
            }
        }),
        ("caller-saved allocatable is not callee-saved", |c, _| {
            disjoint(c.alloc_caller, c.callee_saved);
        }),
        ("scratch is not callee-saved", |c, _| {
            disjoint(c.scratch, c.callee_saved);
        }),
        (
            "callee-saved is the allocatable set plus the frame pointer",
            |c, _| {
                let mut want: BTreeSet<Reg> = c.alloc_callee.iter().copied().collect();
                want.insert(Reg::Bp);
                let have: BTreeSet<Reg> = c.callee_saved.iter().copied().collect();
                assert_eq!(have, want);
            },
        ),
        ("no list repeats a register", |c, _| {
            no_repeats(c.int_args);
            no_repeats(c.int_ret);
            no_repeats(c.callee_saved);
            no_repeats(c.scratch);
            no_repeats(c.alloc_callee);
            no_repeats(c.alloc_caller);
            no_repeats(c.float_args);
            no_repeats(c.xmm_alloc);
            no_repeats(c.xmm_scratch);
        }),
        ("every register exists in the mode", |c, m| {
            let all = c
                .int_args
                .iter()
                .chain(c.int_ret)
                .chain(c.callee_saved)
                .chain(c.scratch)
                .chain(c.alloc_callee)
                .chain(c.alloc_caller);
            for reg in all {
                assert!(Reg::for_mode(m).contains(reg), "{reg:?} in {m:?}");
            }
            for xmm in c.float_args.iter().chain(c.xmm_alloc).chain(c.xmm_scratch) {
                assert!(Xmm::for_mode(m).contains(xmm), "{xmm:?} in {m:?}");
            }
        }),
        ("every register has one role", |c, m| {
            let count = c.scratch.len() + c.alloc_callee.len() + c.alloc_caller.len() + 2;
            assert_eq!(count, Reg::for_mode(m).len());
            let xmm = c.xmm_alloc.len() + c.xmm_scratch.len();
            assert_eq!(xmm, Xmm::for_mode(m).len());
        }),
        (
            "mul, div and shifts have their registers in scratch",
            |c, _| {
                for reg in [Reg::Ax, Reg::Dx, Reg::Cx] {
                    assert!(c.scratch.contains(&reg), "{reg:?}");
                }
            },
        ),
        (
            "the return is in scratch, so it is never live in an allocated register",
            |c, _| {
                for reg in c.int_ret {
                    assert!(c.scratch.contains(reg), "{reg:?}");
                }
            },
        ),
    ];
    for (target, _, mode) in native() {
        for &(name, check) in checks {
            h.case(format!("regs/{target}/{name}"), move || {
                check(&cc(target), mode);
            });
        }
    }
    // The negative control: the disjointness check above can fail.
    h.case("regs/the overlap check catches an overlap", || {
        let caught = enrang_testkit::catch_panic(|| disjoint(&[Reg::Ax, Reg::Si], &[Reg::Si]));
        assert!(caught.is_some(), "an overlap went unnoticed");
    });
    h.case(
        "regs/i386 and x86-64 differ where the document says",
        || {
            assert_eq!(cc("i386-linux").scratch.len(), 3);
            assert_eq!(cc("x86_64-linux").scratch.len(), 5);
            assert!(cc("i386-linux").alloc_caller.is_empty());
            assert!(cc("i386-linux").int_args.is_empty());
            assert_eq!(default_spec("i386-linux").arch, Arch::I386);
        },
    );
    for pair in [I386_ROWS.as_slice(), X86_64_ROWS.as_slice()] {
        let first = pair[0];
        for &target in &pair[1..] {
            h.case(
                format!("regs/{target} has {first}'s convention"),
                move || {
                    // ARCHITECTURE 7.6: one per architecture, independent of OS.
                    assert_eq!(cc(target), cc(first));
                },
            );
        }
    }
}

fn vm(h: &mut Harness) {
    for target in VM_TARGETS {
        h.case(format!("regs/{target} names no register"), move || {
            let c = cc(target);
            assert!(c.int_args.is_empty() && c.int_ret.is_empty());
            assert!(c.callee_saved.is_empty() && c.scratch.is_empty());
            assert!(c.alloc_callee.is_empty() && c.alloc_caller.is_empty());
            assert!(c.float_args.is_empty());
            assert!(c.xmm_alloc.is_empty() && c.xmm_scratch.is_empty());
        });
    }
}
