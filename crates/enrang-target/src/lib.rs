//! Target tables: CPU features and levels, register roles, data layout and the
//! target presets (SPEC 10 and 11, ARCHITECTURE 2.7, 7.4, 7.6, 7.14 and 8).
//!
//! The driver calls [`resolve`] with a target name and the command line's flags and
//! gets back the [`TargetSpec`] every later phase reads, with any notes to print:
//!
//! ```
//! use enrang_target::{CpuLevel, FloatStrategy, TargetOpts, resolve};
//!
//! let opts = TargetOpts { cpu: Some("q8400".to_owned()), ..TargetOpts::default() };
//! let (spec, notes) = resolve("i386-linux", &opts).unwrap();
//! assert_eq!(spec.cpu, CpuLevel::Sse2);
//! assert_eq!(spec.float, FloatStrategy::Sse2);
//! assert_eq!(notes.len(), 1);
//! ```
//!
//! **No compiler code assumes a 64-bit `usize`.** Sizes and addresses are `u64`, and
//! [`TargetUsize`] and [`DataLayout`] say what fits the target.

#![forbid(unsafe_code)]

mod features;
mod level;
mod presets;
mod regs;
mod resolve;
mod spec;

pub use features::{Feature, FeatureSet};
pub use level::{CPU_ALIASES, CpuAlias, CpuLevel, LongMode};
pub use regs::{Reg, Xmm};
pub use resolve::{TargetOpts, all_targets, host_target, resolve};
pub use spec::{
    Addressing, Arch, CallConv, CodeMode, DataLayout, FloatStrategy, ForeignAbi, ForeignKind,
    ImageKind, ImageParams, OsLayer, OutputFormat, PanicPolicy, StackPolicy, TargetSpec,
    TargetUsize, TraceLevel,
};
