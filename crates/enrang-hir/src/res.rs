//! What a name resolves to (A:886: `Res::Local`, `Res::Def`, `Res::PrimType`,
//! `Res::Namespace`, plus the variants ARCHITECTURE leaves silent).

use crate::ids::{DefId, LocalId, ModuleId, ParamId, TopVar};
use crate::ty::{FloatTy, IntTy};

/// A primitive type name: `bool i8 .. u64 isize usize int f32 f64 void never
/// string`; `int` is `Int(I32)`, `string` is `Str`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum PrimTy {
    Bool,
    Int(IntTy),
    Float(FloatTy),
    Void,
    Never,
    Str,
}

impl PrimTy {
    /// The primitive a type name spells, if any.
    pub fn from_name(name: &str) -> Option<PrimTy> {
        Some(match name {
            "bool" => PrimTy::Bool,
            "int" | "i32" => PrimTy::Int(IntTy::I32),
            "i8" => PrimTy::Int(IntTy::I8),
            "i16" => PrimTy::Int(IntTy::I16),
            "i64" => PrimTy::Int(IntTy::I64),
            "u8" => PrimTy::Int(IntTy::U8),
            "u16" => PrimTy::Int(IntTy::U16),
            "u32" => PrimTy::Int(IntTy::U32),
            "u64" => PrimTy::Int(IntTy::U64),
            "isize" => PrimTy::Int(IntTy::Isize),
            "usize" => PrimTy::Int(IntTy::Usize),
            "f32" => PrimTy::Float(FloatTy::F32),
            "f64" => PrimTy::Float(FloatTy::F64),
            "void" => PrimTy::Void,
            "never" => PrimTy::Never,
            "string" => PrimTy::Str,
            _ => return None,
        })
    }

    /// Every primitive type name, in SPEC 4.6's order.
    pub const NAMES: [&'static str; 17] = [
        "bool", "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "isize", "usize", "int",
        "f32", "f64", "void", "never", "string",
    ];
}

/// A compiler form reached by name (SPEC 6's table, S:1177-1191). `mem.forget` and
/// `cpu.has` are forms reached through the namespaces `core/mem` and `core/cpu`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum FormName {
    Console,
    Panic,
    Err,
    Assert,
    Unreachable,
    Dispose,
    WriteTo,
    SizeOf,
    AlignOf,
    OffsetOf,
}

impl FormName {
    pub const ALL: [FormName; 10] = [
        FormName::Console,
        FormName::Panic,
        FormName::Err,
        FormName::Assert,
        FormName::Unreachable,
        FormName::Dispose,
        FormName::WriteTo,
        FormName::SizeOf,
        FormName::AlignOf,
        FormName::OffsetOf,
    ];

    /// The name a program writes.
    pub fn name(self) -> &'static str {
        match self {
            FormName::Console => "console",
            FormName::Panic => "panic",
            FormName::Err => "Err",
            FormName::Assert => "assert",
            FormName::Unreachable => "unreachable",
            FormName::Dispose => "dispose",
            FormName::WriteTo => "writeTo",
            FormName::SizeOf => "sizeOf",
            FormName::AlignOf => "alignOf",
            FormName::OffsetOf => "offsetOf",
        }
    }

    pub fn from_name(name: &str) -> Option<FormName> {
        FormName::ALL.iter().copied().find(|f| f.name() == name)
    }
}

/// What a name resolves to.
#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Res {
    Local(LocalId),
    Def(DefId),
    /// An overload set: one or more functions of one name.
    Fns(Vec<DefId>),
    PrimType(PrimTy),
    TyParam(ParamId),
    /// `Self` inside an interface (SPEC 4.4).
    SelfTy,
    /// A module: a user folder or `import * as n`, legal only left of `.`.
    Namespace(ModuleId),
    Form(FormName),
    /// A top-level variable seen from a local function: a hidden argument (N13).
    TopVar(TopVar),
    /// Nothing: the name is unresolved, and the resolver has reported it.
    Err,
}
