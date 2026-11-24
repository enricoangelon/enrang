//! The MIR of ARCHITECTURE 2.5 as Rust types (M3 plan b.1-b.3).
//!
//! ARCHITECTURE 2.5 is kept with its names and fields. What it names without
//! defining is defined here, and the additions the M3 plan forces carry its
//! departure numbers, each documented where it sits: D18 (`BodyOwner::Test`), D19
//! (`Callee::Form`), D20 (`Callee::NamedFill`, `Callee::ImplicitCtor`), D22
//! (`AggregateKind::Repeat`), D24 (an arrow's parent as a HIR owner, `ClosureFn`,
//! `Rvalue::ArrowFn`), D25 (a constant carries its type) and D26 (`PhaseMeta`).
//! Two more are this crate's own: a constant is a [`ConstKind`], since plan d.12
//! makes a literal view a static numbered per body (`Body::literals`) before any
//! static of it has a `DefId`; and a narrowing fact is rooted at a MIR local
//! ([`MirFact`]), since borrowck compares it with MIR places.

use std::collections::BTreeMap;

use enrang_base::{IdVec, Span, Symbol};
use enrang_hir::{
    self as hir, Abi, AdtId, ArrowId, CastKind, ConstTree, ConstValue, ConvKind, DefId, Fact,
    FactId, FieldIdx, FnRef, HostCallId, IntrinsicKind, ItemPath, LoopId, ModuleId, PathStep,
    RecordKind, ShapeId, Ty, TyList, VariantIdx,
};

use crate::ids::{BlockId, Local, Point, ProjId, RegionId};
use crate::proj::ProjTable;

/// How far a body has come (A:452).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum MirPhase {
    Built,
    Elaborated,
    Mono,
}

/// Whose code a body is (A:467). D18: `Test`, a test item's body, which `check`
/// runs phase 3 on and which is never stored. D24: an arrow's parent is a HIR
/// owner, since an arrow of the statements or of a test has no parent `DefId`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum BodyOwner {
    Fn(DefId),
    Arrow(hir::BodyOwner, ArrowId),
    Statements(ModuleId),
    Test(DefId),
    Shim(ShimKind),
}

/// The glue and adapter bodies of ARCHITECTURE 2.6 (A:615-624). M3 builds none.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum ShimKind {
    DropGlue(Ty),
    CloneGlue(Ty),
    EqGlue(Ty),
    ShowGlue(Ty),
    DisplayGlue(Ty),
    FnAsClosure(FnRef),
    StringForm(FnRef),
    StringFormEnv { from: Ty, to: Ty },
    NamedFill(Ty),
}

/// One module's bodies, keyed for lookup; output walks them in owner `ItemPath`
/// order (ARCHITECTURE 1).
pub type Bodies = BTreeMap<BodyOwner, Body>;

/// A function's control-flow graph (A:455-464).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Body {
    pub owner: BodyOwner,
    pub phase: MirPhase,
    pub arg_count: u32,
    pub locals: IdVec<Local, LocalDecl>,
    pub blocks: IdVec<BlockId, Block>,
    /// An arrow body's environment fields, in environment order.
    pub captures: Vec<Capture>,
    /// Elaborated only: each drop flag and the move path it guards (A:605).
    pub drop_flags: Vec<(Local, MovePathKey)>,
    pub span: Span,
    /// The names of the fields and cases of every ADT the body names, for
    /// `remap_ids` ([`BodyNames::collect`]).
    pub names: BodyNames,
    pub unsafe_regions: IdVec<RegionId, UnsafeRegion>,
    /// The body's interned projection lists (A:472 interns them; per body here, so
    /// a body clones and prints alone).
    pub projs: ProjTable,
    /// Elaborated only: the constant literal views made static (plan d.12), each
    /// reached as `static_addr(literal#k)`.
    pub literals: Vec<LiteralStatic>,
    pub meta: PhaseMeta,
}

impl Body {
    /// An empty `Built` body with only its return slot, of type `ret`.
    pub fn new(owner: BodyOwner, ret: Ty, span: Span) -> Body {
        let mut locals = IdVec::new();
        locals.push(LocalDecl::new(ret, LocalKind::Return, span));
        Body {
            owner,
            phase: MirPhase::Built,
            arg_count: 0,
            locals,
            blocks: IdVec::new(),
            captures: Vec::new(),
            drop_flags: Vec::new(),
            span,
            names: BodyNames::default(),
            unsafe_regions: IdVec::new(),
            projs: ProjTable::new(),
            literals: Vec::new(),
            meta: PhaseMeta::default(),
        }
    }

    /// The return type: `_0`'s.
    pub fn ret_ty(&self) -> Ty {
        self.locals[Local::RETURN].ty
    }

    /// The arguments `_1.._arg_count`.
    pub fn args(&self) -> impl Iterator<Item = Local> {
        (1..=self.arg_count).map(Local)
    }

    /// The statement at `p`, or `None` at a terminator.
    pub fn stmt_at(&self, p: Point) -> Option<&Statement> {
        self.blocks[p.block].stmts.get(p.index as usize)
    }

    /// The terminator's point of `b`.
    pub fn terminator_point(&self, b: BlockId) -> Point {
        Point::new(b, self.blocks[b].stmts.len())
    }
}

/// One `unsafe` region: an `unsafe { }` block, an `asm`, or the whole body of an
/// `unsafe function` or `@naked` function (A:465-466).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnsafeRegion {
    pub kind: UnsafeKind,
    pub parent: Option<RegionId>,
    pub span: Span,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum UnsafeKind {
    Block,
    Asm,
    WholeBody,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum LocalKind {
    Return,
    Arg,
    User,
    Temp,
    DropFlag,
    HiddenLoop(LoopRole),
    ClosureEnv,
}

/// The hidden locals of a `for...of`, printed `#i`, `#n`, `#src`, `#iter`, `#cur`,
/// `#end` (A:469).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum LoopRole {
    Index,
    Length,
    Source,
    IntoIter,
    RangeCursor,
    RangeEnd,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalDecl {
    pub ty: Ty,
    pub mutable: bool,
    pub name: Option<Symbol>,
    pub span: Span,
    pub kind: LocalKind,
}

impl LocalDecl {
    /// An unnamed, immutable local.
    pub fn new(ty: Ty, kind: LocalKind, span: Span) -> LocalDecl {
        LocalDecl {
            ty,
            mutable: false,
            name: None,
            span,
            kind,
        }
    }
}

/// One environment field of an arrow body (A:461 names it): `&T` for a captured
/// path or reference, `&F` for a captured closure parameter `F` (A:971).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Capture {
    pub name: Symbol,
    pub ty: Ty,
    pub kind: CaptureKind,
    pub span: Span,
}

/// A:971's three lowerings of a capture.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum CaptureKind {
    Path,
    ThroughRef,
    ClosureParam,
}

/// A move path: a local, then fields and case fields (A:987's grammar).
#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct MovePathKey {
    pub local: Local,
    pub steps: Vec<MoveStep>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum MoveStep {
    Field(FieldIdx),
    VariantField(VariantIdx, FieldIdx),
}

/// The field and case names of the ADTs a body names, keyed by stable path, never
/// by `AdtId` (A:462).
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct BodyNames {
    pub adts: BTreeMap<ItemPath, AdtNames>,
}

/// One ADT's names: a class's flattened fields, an enum's cases with their fields,
/// and each case's tag as a `Switch` on its discriminant sees it.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct AdtNames {
    pub fields: Vec<Symbol>,
    pub variants: Vec<(Symbol, Vec<Symbol>)>,
    pub tags: Vec<u128>,
}

/// A constant literal view made static at elaboration (plan d.12): its type and
/// value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiteralStatic {
    pub ty: Ty,
    pub value: ConstTree,
}

/// What phase 3 reads and the CFG alone cannot show (plan D26): mirbuild writes it,
/// the text form prints it, so a `.mir` fixture needs no front end.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct PhaseMeta {
    /// One per `for...of` over a path or a once-evaluated source, in `LoopId` order.
    pub loops: Vec<ForOfLoop>,
    /// The body's narrowing facts, rooted at MIR locals.
    pub facts: IdVec<FactId, MirFact>,
    pub records: Vec<MirRecord>,
    /// Each `CheckTag` a narrowed payload was lowered to.
    pub narrowed_uses: Vec<(FactId, Point)>,
    /// The block entered when the fact's test holds.
    pub fact_tests: Vec<(FactId, BlockId)>,
    /// Each `Move` that is an assignment's kept value (A:942, EN0621).
    pub assign_values: Vec<Point>,
    /// The hidden `isize` of supplied parameters (A:937), if any.
    pub defaults_count: Option<Local>,
}

/// A `for...of` loop (A:949-964): its blocks, the bind point (the element's
/// `Ref [for-of-element]`), the source and the binding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForOfLoop {
    pub id: LoopId,
    pub preheader: BlockId,
    pub head: BlockId,
    pub bind: Point,
    pub source: LoopSource,
    pub binding: Local,
    /// The source expression's.
    pub span: Span,
}

/// A loop's source: a path, or the `HiddenLoop(Source)` local of a once-evaluated
/// one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LoopSource {
    Path(Place),
    Once(Local),
}

/// A narrowing fact (HIR's `FactInfo`, D1) with its path rooted at a MIR local.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MirFact {
    pub root: Local,
    pub steps: Vec<PathStep>,
    pub fact: Fact,
    pub span: Span,
}

/// A HIR narrowing record mapped to MIR (plan c.20): the statement that made the
/// reference and the local it went into.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MirRecord {
    pub fact: FactId,
    pub at: Point,
    pub slot: Local,
    pub kind: RecordKind,
    pub span: Span,
}

// ---------------------------------------------------------------------------------
// Places, operands, rvalues.

/// A local and an interned projection list (A:472); a root is always a local.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct Place {
    pub local: Local,
    pub proj: ProjId,
}

impl Place {
    /// The local itself.
    pub fn local(local: Local) -> Place {
        Place {
            local,
            proj: ProjId::EMPTY,
        }
    }

    /// Whether the place is its local, with no projection.
    pub fn is_local(self) -> bool {
        self.proj == ProjId::EMPTY
    }
}

impl From<Local> for Place {
    fn from(local: Local) -> Place {
        Place::local(local)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Proj {
    Field(FieldIdx),
    Deref,
    Variant(VariantIdx),
    Index(Local),
    ConstIndex(u64),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Const(Box<Constant>),
}

impl Operand {
    /// A constant value of type `ty`.
    pub fn constant(value: ConstValue, ty: Ty) -> Operand {
        Operand::Const(Box::new(Constant {
            kind: ConstKind::Value(value),
            ty,
        }))
    }

    /// The place copied or moved, if any.
    pub fn place(&self) -> Option<Place> {
        match self {
            Operand::Copy(p) | Operand::Move(p) => Some(*p),
            Operand::Const(_) => None,
        }
    }
}

/// A constant with its type (D25: A:474's `Const(ConstValue)` has none, and a
/// `string` or `&string` text, or a function address, needs one).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constant {
    pub kind: ConstKind,
    pub ty: Ty,
}

/// A constant's value: a HIR constant, or the address of a literal view made static
/// at elaboration, `Body::literals[k]` (plan d.12, `static_addr(literal#k)`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstKind {
    Value(ConstValue),
    LiteralAddr(u32),
}

/// Why a loan was made (A:476-479).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum BorrowOrigin {
    Explicit,
    AutoBorrow,
    Reborrow,
    Destructure,
    ForOfElement,
    ForOfHidden,
    ClosureCapture,
    HiddenArg,
    TempArg,
    CompoundTarget,
    LiteralView,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum DropOrigin {
    Scope,
    Assign,
}

/// The whole-object event a `CheckClass` guards (A:481-484).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum ClassOp {
    Unbox,
    Assign,
    CopyOut,
    MoveThis(Symbol),
    Replace,
    Swap,
    Clone,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum ClassHolder {
    Box,
    Ref,
}

/// Wrapping arithmetic and comparisons (comparisons yield `bool`). `Div` and `Rem`
/// are on floats only, IEEE division and `fmod` (S:1520); on integers they are
/// `Checked`, which panics on a zero divisor (S:1492).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Shl,
    Shr,
    Ushr,
    BitAnd,
    BitOr,
    BitXor,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl BinOp {
    pub fn is_comparison(self) -> bool {
        matches!(
            self,
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
        )
    }
}

/// The operations that panic on overflow, a zero divisor or a shift out of range
/// (SPEC 9.2).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum CheckedOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Shl,
    Shr,
    Ushr,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum UnOp {
    Not,
    BitNot,
    /// Wrapping; on floats only.
    Neg,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Rvalue {
    Use(Operand),
    /// Every loan site; phase 3 decides shared or exclusive (N4).
    Ref {
        place: Place,
        origin: BorrowOrigin,
    },
    /// A raw pointer, no loan.
    AddrOf(Place),
    Binary(BinOp, Operand, Operand),
    Checked(CheckedOp, Operand, Operand),
    Unary(UnOp, Operand),
    CheckedNeg(Operand),
    Cast(CastKind, Operand, Ty),
    /// The target type is the destination's (A:493).
    Convert(ConvKind, Operand),
    Aggregate(AggregateKind, Vec<Operand>),
    Discriminant(Place),
    /// `isize`.
    Len(Place),
    /// D24: `func` names an arrow, or a definition through the `FnAsClosure` shim
    /// (the env holds a local function's hidden arguments, else nothing), or is
    /// the `fn` value the env holds as its one field (C12 on an `fn` value).
    ClosureValue {
        func: ClosureFn,
        env: Place,
    },
    ClosureReborrow(Place),
    /// D24: a non-capturing arrow as an `fn` value.
    ArrowFn(ArrowId),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum ClosureFn {
    Arrow(ArrowId),
    Named(FnRef),
    /// The `fn` value in the env's field 0, called with the closure's arguments.
    FnValue,
}

/// What an `Aggregate` builds (A:495 names it).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AggregateKind {
    /// `T[N]` of N operands; the element type.
    Fixed(Ty),
    /// D22: `[x; n]`, one operand.
    Repeat(u64),
    Tuple,
    /// A class's fields in `FieldIdx` order, or an enum case's.
    Adt {
        adt: AdtId,
        variant: Option<VariantIdx>,
        args: TyList,
    },
    /// Operands in shape order.
    Object(ShapeId),
    /// `T | null` holding its one operand.
    Present,
    /// `null` of the destination's nullable type.
    Null,
    /// Operands in `Body::captures` order.
    ClosureEnv,
}

// ---------------------------------------------------------------------------------
// Statements, calls, terminators.

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Statement {
    pub kind: StatementKind,
    pub span: Span,
    /// The innermost `unsafe` region it lies in (A:560).
    pub region: Option<RegionId>,
}

impl Statement {
    pub fn new(kind: StatementKind, span: Span) -> Statement {
        Statement {
            kind,
            span,
            region: None,
        }
    }
}

/// Generates [`StatementKind`] and `StatementKind::ALL_NAMES`, for the
/// traceability meta-test (A:501).
macro_rules! define_mir_statements {
    ($($(#[$doc:meta])* $name:ident $({ $($field:ident : $fty:ty),* $(,)? })? $(( $($tty:ty),* ))?,)*) => {
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub enum StatementKind {
            $($(#[$doc])* $name $({ $($field: $fty),* })? $(( $($tty),* ))?,)*
        }

        impl StatementKind {
            /// Every statement kind's name, in declaration order.
            pub const ALL_NAMES: &'static [&'static str] = &[$(stringify!($name),)*];

            /// This statement's kind name.
            pub fn name(&self) -> &'static str {
                match self {
                    $(StatementKind::$name { .. } => stringify!($name),)*
                }
            }
        }
    };
}

define_mir_statements! {
    Assign { dest: Place, value: Rvalue },
    /// Panics; the address is computed afterwards (O6).
    CheckBounds { index: Operand, len: Operand },
    /// In the run of checks before the projection, same block.
    CheckTag { place: Place, variant: VariantIdx },
    /// Panics unless the object is exactly the place's class.
    CheckClass { place: Place, op: ClassOp, via: ClassHolder },
    /// Writes `class`'s method table into the object's hidden pointer.
    SetTable { place: Place, class: Ty },
    /// A field initialiser's or default's store in a constructor of a class that
    /// can be extended, or in an implicit constructor.
    FieldInit { field: Place, value: Operand },
    StorageLive(Local),
    StorageDead(Local),
    /// `Built` only.
    Drop(Place, DropOrigin),
    /// `Elaborated`: run the type's glue.
    DropGlue(Place),
    Intrinsic { kind: IntrinsicKind, args: Vec<Operand>, dest: Option<Place> },
    Asm(Box<AsmStmt>),
    /// Legal only in `os/vm`.
    HostCall { id: HostCallId, args: Vec<Operand>, dest: Option<Place> },
    Nop,
}

/// An `asm` with its operands lowered (HIR's `HirAsm`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AsmStmt {
    pub template: Symbol,
    pub ins: Vec<(Symbol, Operand)>,
    pub outs: Vec<(Symbol, Option<Place>)>,
    pub clobbers: Vec<Symbol>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Callee {
    Fn(FnRef),
    FnPtr(Operand),
    ClosureLocal(Local),
    Foreign(ForeignRef),
    /// Through a method table (A:513-523); `table` is a copy of the receiver
    /// operand (plan b.4).
    Virtual {
        method: FnRef,
        table: Operand,
    },
    /// D19: a compiler form whose library body arrives at M4.
    Form(FormCall),
    /// D19: a form whose arguments include a template, flattened into its parts
    /// (A:976): `parts` holds how many operands each written argument gave, so a
    /// printing form runs one `fmt` per argument with a space between and a
    /// template's parts with none (A:977); `form log[1, 3](...)` in the text form.
    FormParts {
        form: FormCall,
        parts: Vec<u32>,
    },
    /// D20: the `NamedFill` shim of a named form; one argument, `addr_of(dest)`.
    NamedFill {
        class: Ty,
        left_out: Vec<FieldIdx>,
    },
    /// D20: the implicit constructor a `super()` reaches over a base chain with no
    /// constructor; one argument, `addr_of(dest)`.
    ImplicitCtor {
        class: Ty,
    },
}

/// A foreign function and its convention (A:524 names it).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct ForeignRef {
    pub def: DefId,
    pub abi: Abi,
}

impl Callee {
    /// The form a `Form` or `FormParts` callee calls.
    pub fn form(&self) -> Option<FormCall> {
        match self {
            Callee::Form(f) | Callee::FormParts { form: f, .. } => Some(*f),
            _ => None,
        }
    }
}

/// D19's forms. Contract: every reference parameter Read but `Append`'s first and
/// `WriteTo`'s first, the `Formatter` it writes (Write, S:1203); no sources, no
/// stores; a `void`, `string`, `Failure` or `never` result.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum FormCall {
    Log,
    Error,
    WriteTo,
    Panic,
    Template,
    ToString,
    Assert,
    Unreachable,
    FailureText,
    FailureMove,
    FailureCopy,
    IntoFailure,
    Concat,
    Append,
    Expect { matcher: Symbol, negated: bool },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    pub stmts: Vec<Statement>,
    pub term: Terminator,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Terminator {
    pub kind: TerminatorKind,
    pub span: Span,
    pub region: Option<RegionId>,
}

impl Terminator {
    pub fn new(kind: TerminatorKind, span: Span) -> Terminator {
        Terminator {
            kind,
            span,
            region: None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TerminatorKind {
    Goto(BlockId),
    /// On a `bool`: arms `[0: else]`, `otherwise: then` (plan b.4).
    Switch {
        value: Operand,
        arms: Vec<(u128, BlockId)>,
        otherwise: Option<BlockId>,
    },
    /// `next: None`: the callee returns `never`.
    Call {
        callee: Callee,
        args: Vec<Operand>,
        dest: Place,
        next: Option<BlockId>,
    },
    Return,
    Unreachable,
}

impl TerminatorKind {
    /// The successors, `Switch` arms in order then `otherwise`, a `Call`'s `next`.
    pub fn successors(&self) -> Vec<BlockId> {
        match self {
            TerminatorKind::Goto(b) => vec![*b],
            TerminatorKind::Switch {
                arms, otherwise, ..
            } => arms
                .iter()
                .map(|&(_, b)| b)
                .chain(otherwise.iter().copied())
                .collect(),
            TerminatorKind::Call { next, .. } => next.iter().copied().collect(),
            TerminatorKind::Return | TerminatorKind::Unreachable => Vec::new(),
        }
    }

    /// The successors, mutable, in the same order.
    pub fn successors_mut(&mut self) -> Vec<&mut BlockId> {
        match self {
            TerminatorKind::Goto(b) => vec![b],
            TerminatorKind::Switch {
                arms, otherwise, ..
            } => arms
                .iter_mut()
                .map(|(_, b)| b)
                .chain(otherwise.iter_mut())
                .collect(),
            TerminatorKind::Call { next, .. } => next.iter_mut().collect(),
            TerminatorKind::Return | TerminatorKind::Unreachable => Vec::new(),
        }
    }
}
