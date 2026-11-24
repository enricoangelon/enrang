//! Physical registers, as later crates name them.

use crate::spec::CodeMode;

/// Declares a register enum in hardware-number order, with `ALL` and `number`.
macro_rules! registers {
    ($(#[$doc:meta])* $name:ident: $($reg:ident)*) => {
        $(#[$doc])*
        #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
        pub enum $name { $($reg,)* }

        impl $name {
            /// Every register, by hardware number.
            pub const ALL: [$name; 16] = [$($name::$reg,)*];

            /// The hardware number, as encoded in ModRM with REX.
            pub const fn number(self) -> u8 {
                self as u8
            }

            /// The registers `mode` can name.
            pub fn for_mode(mode: CodeMode) -> &'static [$name] {
                match mode {
                    CodeMode::M32 => &$name::ALL[..8],
                    CodeMode::M64 => &$name::ALL,
                }
            }
        }
    };
}

registers! {
    /// A general register. The width comes from the instruction: `Reg::Ax` is `eax`
    /// in 32-bit code and `rax` in 64-bit code.
    Reg: Ax Cx Dx Bx Sp Bp Si Di R8 R9 R10 R11 R12 R13 R14 R15
}

registers! {
    /// An SSE register.
    Xmm: Xmm0 Xmm1 Xmm2 Xmm3 Xmm4 Xmm5 Xmm6 Xmm7 Xmm8 Xmm9 Xmm10 Xmm11 Xmm12 Xmm13 Xmm14 Xmm15
}

const NAMES_32: [&str; 8] = ["eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi"];
const NAMES_64: [&str; 16] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
    "r14", "r15",
];
const XMM_NAMES: [&str; 16] = [
    "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10",
    "xmm11", "xmm12", "xmm13", "xmm14", "xmm15",
];

impl Reg {
    /// The full-width name in `mode`, or `None` if `mode` cannot name this register.
    pub fn name(self, mode: CodeMode) -> Option<&'static str> {
        let names: &[&'static str] = match mode {
            CodeMode::M32 => &NAMES_32,
            CodeMode::M64 => &NAMES_64,
        };
        names.get(usize::from(self.number())).copied()
    }
}

impl Xmm {
    pub fn name(self) -> &'static str {
        XMM_NAMES[usize::from(self.number())]
    }
}
