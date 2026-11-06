//! The target rows of ARCHITECTURE 2.7, before any flag is applied.

use crate::level::CpuLevel;
use crate::regs::Reg::*;
use crate::regs::Xmm::*;
use crate::spec::{
    Addressing, Arch, CallConv, CodeMode, DataLayout, FloatStrategy, ForeignAbi, ForeignKind,
    ImageParams, OsLayer, OutputFormat, PanicPolicy, StackPolicy, TargetSpec, TraceLevel,
};

const PAGE: u32 = 0x1000;

/// Hosted exit status of a panic (SPEC 9.1).
const PANIC_STATUS: i32 = 101;

/// `SectionAlignment` and `FileAlignment` of every PE image (ARCHITECTURE 9.4).
pub(crate) const PE_SECTION_ALIGN: u32 = PAGE;
pub(crate) const PE_FILE_ALIGN: u32 = 0x200;

/// The PE subsystem of a console program and of an EFI application.
const SUBSYSTEM_CUI: u16 = 3;
pub(crate) const SUBSYSTEM_EFI: u16 = 10;

const LAYOUT_32: DataLayout = DataLayout {
    ptr_bytes: 4,
    i64_align: 4,
    f64_align: 4,
    frame_align: 4,
};

const LAYOUT_64: DataLayout = DataLayout {
    ptr_bytes: 8,
    i64_align: 8,
    f64_align: 8,
    frame_align: 16,
};

const CC_I386: CallConv = CallConv {
    int_args: &[],
    float_args: &[],
    int_ret: &[Ax, Dx],
    callee_saved: &[Bx, Si, Di, Bp],
    scratch: &[Ax, Cx, Dx],
    alloc_callee: &[Bx, Si, Di],
    alloc_caller: &[],
    xmm_alloc: &[Xmm0, Xmm1, Xmm2, Xmm3, Xmm4, Xmm5],
    xmm_scratch: &[Xmm6, Xmm7],
    stack_args_callee_pops: true,
};

const CC_X86_64: CallConv = CallConv {
    int_args: &[Di, Si, Dx, Cx, R8, R9],
    float_args: &[Xmm0, Xmm1, Xmm2, Xmm3, Xmm4, Xmm5, Xmm6, Xmm7],
    int_ret: &[Ax],
    callee_saved: &[Bx, Bp, R12, R13, R14, R15],
    scratch: &[Ax, Cx, Dx, R10, R11],
    alloc_callee: &[Bx, R12, R13, R14, R15],
    alloc_caller: &[Si, Di, R8, R9],
    xmm_alloc: &[
        Xmm0, Xmm1, Xmm2, Xmm3, Xmm4, Xmm5, Xmm6, Xmm7, Xmm8, Xmm9, Xmm10, Xmm11, Xmm12, Xmm13,
    ],
    xmm_scratch: &[Xmm14, Xmm15],
    stack_args_callee_pops: false,
};

const CC_VM: CallConv = CallConv {
    int_args: &[],
    float_args: &[],
    int_ret: &[],
    callee_saved: &[],
    scratch: &[],
    alloc_callee: &[],
    alloc_caller: &[],
    xmm_alloc: &[],
    xmm_scratch: &[],
    stack_args_callee_pops: false,
};

const FOREIGN_NONE: ForeignAbi = ForeignAbi {
    kind: ForeignKind::None,
    shadow_bytes: 0,
    extra_saved: &[],
    extra_saved_xmm: &[],
};

const FOREIGN_SYSV: ForeignAbi = ForeignAbi {
    kind: ForeignKind::SysV,
    shadow_bytes: 0,
    extra_saved: &[],
    extra_saved_xmm: &[],
};

pub(crate) const FOREIGN_WIN64: ForeignAbi = ForeignAbi {
    kind: ForeignKind::Win64,
    shadow_bytes: 32,
    extra_saved: &[Si, Di],
    extra_saved_xmm: &[
        Xmm6, Xmm7, Xmm8, Xmm9, Xmm10, Xmm11, Xmm12, Xmm13, Xmm14, Xmm15,
    ],
};

const STACK_HOSTED: StackPolicy = StackPolicy {
    size: 0,
    probe_interval: Some(PAGE),
    limit_check: false,
    limit_reserve: 0,
};

/// The PE reserve (ARCHITECTURE 9.4).
const STACK_PE: StackPolicy = StackPolicy {
    size: 8 * 1024 * 1024,
    ..STACK_HOSTED
};

const STACK_VM: StackPolicy = StackPolicy {
    size: 0,
    probe_interval: None,
    limit_check: false,
    limit_reserve: 0,
};

/// `limit_reserve` follows the float strategy, so `resolve` sets it.
const STACK_FREESTANDING: StackPolicy = StackPolicy {
    size: 16 * 1024,
    probe_interval: None,
    limit_check: true,
    limit_reserve: 0,
};

/// What `__stack_limit` keeps free on a freestanding target: 2 KB under `soft`,
/// 3 KB under `sse2`, where an interrupt stub saves 512 bytes of `fxsave` state
/// (ARCHITECTURE 7.5, 7.15).
pub(crate) fn limit_reserve(float: FloatStrategy) -> u32 {
    match float {
        FloatStrategy::Soft => 2 * 1024,
        _ => 3 * 1024,
    }
}

/// Sections pack at their own alignment: the ELF and flat writers add no padding.
fn packed_image(base: u64) -> ImageParams {
    ImageParams {
        base,
        page_size: PAGE,
        section_align: 1,
        file_align: 1,
    }
}

fn i386(name: &'static str, os: OsLayer, format: OutputFormat, base: u64) -> TargetSpec {
    let floor = CpuLevel::I386.table_set();
    TargetSpec {
        name,
        arch: Arch::I386,
        code_mode: CodeMode::M32,
        layout: LAYOUT_32,
        cpu: CpuLevel::I386,
        allowed: floor,
        floor,
        float: FloatStrategy::Soft,
        cc: CC_I386,
        foreign: FOREIGN_NONE,
        os,
        alloc_default: true,
        format,
        addressing: Addressing::Absolute32,
        image: packed_image(base),
        stack: STACK_HOSTED,
        panic: PanicPolicy::Exit(PANIC_STATUS),
        trace: TraceLevel::Full,
    }
}

fn x86_64(name: &'static str, os: OsLayer, format: OutputFormat, base: u64) -> TargetSpec {
    let floor = CpuLevel::X86_64.table_set();
    TargetSpec {
        name,
        arch: Arch::X86_64,
        code_mode: CodeMode::M64,
        layout: LAYOUT_64,
        cpu: CpuLevel::X86_64,
        allowed: floor,
        floor,
        float: FloatStrategy::Sse2,
        cc: CC_X86_64,
        foreign: FOREIGN_NONE,
        os,
        alloc_default: true,
        format,
        addressing: Addressing::RipRelative,
        image: packed_image(base),
        stack: STACK_HOSTED,
        panic: PanicPolicy::Exit(PANIC_STATUS),
        trace: TraceLevel::Full,
    }
}

/// The fields `i386-none` and `x86_64-none` share.
fn freestanding(spec: TargetSpec) -> TargetSpec {
    TargetSpec {
        alloc_default: false,
        stack: STACK_FREESTANDING,
        panic: PanicPolicy::UserHandler,
        ..spec
    }
}

/// A VM row keeps the layout, level and addressing of its native twin. It has no
/// registers and no image.
fn vm(twin: TargetSpec) -> TargetSpec {
    TargetSpec {
        arch: Arch::Mir,
        float: FloatStrategy::Host,
        cc: CC_VM,
        image: ImageParams {
            base: 0,
            page_size: 0,
            section_align: 0,
            file_align: 0,
        },
        stack: STACK_VM,
        panic: PanicPolicy::VmPause,
        ..twin
    }
}

/// The row of `name`, for exactly the names `all_targets` lists.
pub(crate) fn preset(name: &str) -> Option<TargetSpec> {
    let spec = match name {
        "x86_64-linux" => TargetSpec {
            foreign: FOREIGN_SYSV,
            ..x86_64(
                "x86_64-linux",
                OsLayer::LinuxX64,
                OutputFormat::Elf64,
                0x40_0000,
            )
        },
        "x86_64-windows" => {
            let format = OutputFormat::Pe {
                subsystem: SUBSYSTEM_CUI,
            };
            let base = 0x1_4000_0000;
            TargetSpec {
                foreign: FOREIGN_WIN64,
                image: ImageParams {
                    base,
                    page_size: PAGE,
                    section_align: PE_SECTION_ALIGN,
                    file_align: PE_FILE_ALIGN,
                },
                stack: STACK_PE,
                ..x86_64("x86_64-windows", OsLayer::Win64Imports, format, base)
            }
        }
        "i386-linux" => i386(
            "i386-linux",
            OsLayer::LinuxInt80,
            OutputFormat::Elf32,
            0x0804_8000,
        ),
        "i386-none" => freestanding(i386(
            "i386-none",
            OsLayer::None,
            OutputFormat::Flat,
            0x1_0000,
        )),
        "x86_64-none" => freestanding(x86_64(
            "x86_64-none",
            OsLayer::None,
            OutputFormat::Flat,
            0x10_0000,
        )),
        "vm64" => vm(x86_64("vm64", OsLayer::Vm, OutputFormat::None, 0)),
        "vm32" => vm(i386("vm32", OsLayer::Vm, OutputFormat::None, 0)),
        _ => return None,
    };
    Some(spec)
}
