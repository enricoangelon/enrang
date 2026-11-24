//! `TargetSpec` and the types it is made of (ARCHITECTURE 2.7).

use crate::features::FeatureSet;
use crate::level::CpuLevel;
use crate::regs::{Reg, Xmm};

/// A target-sized quantity. Compiler-side sizes and addresses are `u64`, and this
/// checks them against the spec: no compiler code assumes a 64-bit `usize`.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct TargetUsize(pub u64);

impl TargetUsize {
    /// `v`, if it is a value of the target's `usize`.
    pub fn checked(v: u64, spec: &TargetSpec) -> Option<TargetUsize> {
        (v <= spec.layout.usize_max()).then_some(TargetUsize(v))
    }
}

/// What the code is compiled to. `Mir` is the VM.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Arch {
    I386,
    X86_64,
    Mir,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum CodeMode {
    M32,
    M64,
}

/// What SPEC 11 leaves to the target. The rest of its table follows from these.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct DataLayout {
    /// `P`: the size and alignment of pointers, `usize` and `isize`.
    pub ptr_bytes: u32,
    pub i64_align: u32,
    pub f64_align: u32,
    /// What the stack is kept aligned to at a call.
    pub frame_align: u32,
}

impl DataLayout {
    /// The target's `usize.MAX`.
    pub const fn usize_max(self) -> u64 {
        u64::MAX >> (u64::BITS - self.ptr_bytes * 8)
    }

    /// The target's `isize.MAX`, the largest size of a type or static (SPEC 11).
    pub const fn isize_max(self) -> u64 {
        self.usize_max() >> 1
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum FloatStrategy {
    Soft,
    Sse2,
    /// The FPU: the default at `i586` and `i686` on `i386-*`, and `--float=x87` at
    /// any level there (SPEC 9.3). Code generation for it arrives in M8.
    X87,
    /// Rust's floats, in the VM only.
    Host,
}

impl FloatStrategy {
    pub const fn name(self) -> &'static str {
        match self {
            FloatStrategy::Soft => "soft",
            FloatStrategy::Sse2 => "sse2",
            FloatStrategy::X87 => "x87",
            FloatStrategy::Host => "host",
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum OsLayer {
    LinuxX64,
    LinuxInt80,
    Win64Imports,
    None,
    Uefi,
    Vm,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum OutputFormat {
    Elf64,
    Elf32,
    Pe { subsystem: u16 },
    Flat,
    BiosImage(ImageKind),
    None,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum ImageKind {
    Floppy144,
    Hdd,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Addressing {
    RipRelative,
    Absolute32,
}

/// The internal calling convention and register roles (ARCHITECTURE 7.4, 7.6). A
/// register in no list is fixed: the stack and frame pointers. VM rows have no
/// registers, so every list there is empty.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct CallConv {
    /// In order. Empty when integer arguments go on the stack.
    pub int_args: &'static [Reg],
    /// In order. Empty when float arguments go on the stack.
    pub float_args: &'static [Xmm],
    /// The low word first.
    pub int_ret: &'static [Reg],
    pub callee_saved: &'static [Reg],
    /// Never allocated: what `mul`, `div` and shifts need, and what spills go through.
    pub scratch: &'static [Reg],
    pub alloc_callee: &'static [Reg],
    pub alloc_caller: &'static [Reg],
    pub xmm_alloc: &'static [Xmm],
    pub xmm_scratch: &'static [Xmm],
    pub stack_args_callee_pops: bool,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum ForeignKind {
    None,
    SysV,
    Win64,
}

/// The ABI of foreign code on this target.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct ForeignAbi {
    pub kind: ForeignKind,
    pub shadow_bytes: u32,
    /// General registers an entry function must save beyond the internal
    /// callee-saved set.
    pub extra_saved: &'static [Reg],
    /// XMM registers such a function must save (ARCHITECTURE 7.6).
    pub extra_saved_xmm: &'static [Xmm],
}

/// Where an image goes. `section_align` and `file_align` are floors applied by the
/// writer: 1 means sections pack at their own alignment, and segments are placed
/// by the page rule of ARCHITECTURE 9.2. A VM row has no image: all are zero.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct ImageParams {
    pub base: u64,
    pub page_size: u32,
    pub section_align: u32,
    pub file_align: u32,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct StackPolicy {
    /// Bytes: the freestanding stack or the PE reserve. 0 when the OS or the VM
    /// sizes the stack.
    pub size: u64,
    /// Frames this large are probed, one page per step, on hosted targets.
    pub probe_interval: Option<u32>,
    pub limit_check: bool,
    /// What the `__stack_limit` check keeps free for panic printing and interrupts.
    pub limit_reserve: u32,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum PanicPolicy {
    Exit(i32),
    UserHandler,
    VmPause,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum TraceLevel {
    Full,
    Fn,
    None,
}

/// Everything the compiler knows about a target, once `--cpu` and the other flags
/// have been applied. No field for a red zone, because no target uses one, and none
/// for atomics, because availability follows from `allowed`.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct TargetSpec {
    pub name: &'static str,
    pub arch: Arch,
    pub code_mode: CodeMode,
    pub layout: DataLayout,
    /// The level code is built at. A VM row has no `--cpu` and carries its twin's.
    pub cpu: CpuLevel,
    /// What code outside the floor island may use.
    pub allowed: FeatureSet,
    /// What the floor island may use, whatever `--cpu` says (ARCHITECTURE 8.4).
    pub floor: FeatureSet,
    pub float: FloatStrategy,
    pub cc: CallConv,
    pub foreign: ForeignAbi,
    pub os: OsLayer,
    /// Whether the target has an allocator without a `@globalAllocator`.
    pub alloc_default: bool,
    pub format: OutputFormat,
    pub addressing: Addressing,
    pub image: ImageParams,
    pub stack: StackPolicy,
    pub panic: PanicPolicy,
    pub trace: TraceLevel,
}

impl TargetSpec {
    /// Whether no OS runs below the program, which then needs `@entry` and, once a
    /// panic can happen, a `@panicHandler`.
    pub const fn is_freestanding(&self) -> bool {
        matches!(self.os, OsLayer::None | OsLayer::Uefi)
    }
}
