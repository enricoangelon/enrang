//! The typed HIR: definitions, the `Ty` interner, signatures, typed bodies, `Tcx`,
//! the lang-item and intrinsic tables (ARCHITECTURE 1, 2.4, 3).
//!
//! This is a contract crate (ARCHITECTURE 1 "Parallel work rules"): sema writes
//! it, and mirbuild, borrowck, mono and the VM read it, so it changes only through
//! its owner. ARCHITECTURE 2.4 is kept with its names and fields; what it names
//! without defining is defined here, and the additions a SPEC rule forces carry
//! the departure numbers of the M2 plan (D1-D16), each documented where it sits:
//!
//! - D1: every `Expr` has an `ExprId`, a body stores its narrowing facts and
//!   records, and `NarrowedPayload` names its fact ([`narrow`]).
//! - D2: `TyKind` holds only ids and is `Copy`; `Tcx::kind` returns it by value.
//! - D3: `ConstTree` holds aggregate constants.
//! - D4: `FieldDef` gains `has_default`, `declared_in`, `span`, `optional`.
//! - D5: implicit type parameters stand for interface- and object-typed parameters.
//! - D6: `Body.param_defaults` and `FieldInits`.
//! - D7: `Arm.value_spans`.
//! - D8: `Callee::Super` and `Callee::SuperCtor`.
//! - D9: `ExprKind::Destructure`; D11: `ExprKind::NullLit`.
//! - D12: `FormKind::{Clone, Fmt, Equals}` for members the compiler synthesises.
//! - D13: `Shape.optional`, the fields a literal may leave out.
//! - D14: `ParamSig.fn_names` and `FnSig.ret_fn_names`, the parameter names of a
//!   written function type, kept outside the type.
//! - D15: `Callee::BoundMember.found`, the member chosen on the bound.
//! - D16: `Adjust::FnToHandler` for C17.
//! - D17: `Pat::Place`, a destructuring assignment's part that is not a local.
//!
//! M3 adds what phase 3 reads and M2 did not record (M3 plan 0.3, K1-K8):
//! `Store::read_set_only` (K1), `Contract::moves_or_writes` (K2), three `Reason`s
//! (K3), [`ConvKind`] (K4), `VariantIdx::NULL` and `PRESENT` (K5),
//! `CheckedProgram::satisfactions` (K6), `CheckedProgram::hidden_args` and
//! `top_vars` (K7), and `FieldInits::this_spans` (K8).
//!
//! Determinism: nothing here iterates a hash map, and ids, which follow load and
//! interning order, never order output; output is sorted by [`ItemPath`].

#![forbid(unsafe_code)]

mod adt;
mod body;
mod consts;
mod contract;
mod def;
mod display;
mod ids;
mod intrinsic;
mod lang;
mod member;
pub mod narrow;
mod path;
mod predicates;
mod program;
mod res;
mod sig;
mod tcx;
mod ty;

pub use adt::{
    AdtDecl, AdtDef, AdtKind, ClassDef, ClassModifier, EnumDef, EnumValues, FieldDef, IfaceDef,
    VariantDef, VariantValue,
};
pub use body::{
    Adjust, Arm, ArmBody, ArmValue, ArrayPart, ArrowBody, ArrowBodyKind, BinOp, BindingMode, Block,
    Body, BodyOwner, Callee, Capture, CastKind, ConvKind, ErrForm, ExpectArg, ExpectForm, Expr,
    ExprKind, FieldInits, ForSource, FormKind, HirAsm, LocalDecl, LocalKind, LogOp, OptChain,
    OptMember, Pat, SpreadKind, Stmt, StmtKind, TplPart, TryKind, UnOp, is_path_place,
};
pub use consts::{ConstTree, ConstValue, FnRef, StringTable};
pub use contract::{ClassContract, Contract, Perm, Reason, ResultPerm, RetSources, Store};
pub use def::{AliasDef, Attrs, DefData, DefFlags, DefKind, ModuleInfo, Repr, Vis};
pub use enrang_target::{Feature, FeatureSet};
pub use ids::{
    AdtId, ArrowId, BoundId, DefId, ExprId, FactId, FieldIdx, FnSigId, GenericsId, HostCallId,
    InferVar, LocalId, LoopId, ModuleId, ParamId, ShapeId, StringId, TopVar, TyList, VariantIdx,
};
pub use intrinsic::{AluOp, IntrinsicKind, IntrinsicName};
pub use lang::{LangItem, LangLayer};
pub use member::{FoundMethod, MemberKind, MemberRef};
pub use narrow::{Fact, FactInfo, FactPath, NarrowRecord, PathStep, RecordKind};
pub use path::{CTOR_SEGMENT, DTOR_SEGMENT, ItemPath, ModulePath};
pub use predicates::{is_slot_type, is_value_type};
pub use program::{CheckedProgram, Entry, SatisfactionRecord, TestItem, TestItemKind, TopVarInfo};
pub use res::{FormName, PrimTy, Res};
pub use sig::{
    Bound, FnDecl, FnSig, Generics, Implicit, Mark, OncePerType, ParamEnv, ParamSig, Receiver,
    TyParamDef, TyParamFacts,
};
pub use tcx::{CommonTypes, ExtendDef, LayoutMemo, Tcx};
pub use ty::{Abi, ClosureSig, FloatTy, FnPtrSig, IntTy, Shape, Ty, TyKind};
