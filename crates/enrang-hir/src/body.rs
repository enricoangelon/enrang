//! Typed bodies (ARCHITECTURE 2.4, A:339-426), kept field for field; the additions
//! a SPEC rule forces are marked with the plan's departure numbers.
//!
//! Every coercion a body applies is an [`Adjust`] on the expression it applies to,
//! recorded at the coercion site and nowhere else (A:888), so MIR building reads
//! only these. Borrow modes are phase 3's: nothing here says whether a borrow reads
//! or writes. Bodies are generic: `T` stays `Param`. An expression typing rejected
//! is `ExprKind::Never` of type `Error`, so a body can always be built, and no body
//! with an error leaves phase 2, which then stops (SPEC 13.1).

use enrang_base::{IdVec, Span, Symbol};
pub use enrang_syntax::ast::{BinOp, LogOp, UnOp};
use enrang_target::Feature;

use crate::consts::{ConstValue, FnRef};
use crate::ids::{
    AdtId, ArrowId, DefId, ExprId, FactId, FieldIdx, FnSigId, HostCallId, LocalId, LoopId,
    ModuleId, ParamId, ShapeId, StringId, TopVar, TyList, VariantIdx,
};
use crate::intrinsic::IntrinsicKind;
use crate::narrow::{FactInfo, NarrowRecord};
use crate::sig::Mark;
use crate::tcx::Tcx;
use crate::ty::{Ty, TyKind};

/// What owns a body. ARCHITECTURE's `Body.owner` is a `DefId`; a program's
/// top-level statements have none, so this names them by module.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum BodyOwner {
    /// A function, method, constructor, destructor or local function.
    Fn(DefId),
    /// A program's top-level statements.
    Statements(ModuleId),
    /// A constant's initialiser, an `unsafe let`'s, or a static `assert`.
    Const(DefId),
    /// A test item's body, typed as an arrow.
    Test(DefId),
}

/// A typed body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Body {
    pub owner: BodyOwner,
    pub params: Vec<LocalId>,
    pub locals: IdVec<LocalId, LocalDecl>,
    pub root: Block,
    pub arrows: IdVec<ArrowId, ArrowBody>,
    pub ret: Ty,
    /// D6: a parameter's default runs as the body's first statements (SPEC 4.14).
    pub param_defaults: Vec<(LocalId, Expr)>,
    /// D1: the narrowing facts typing used (A:898).
    pub facts: IdVec<FactId, FactInfo>,
    /// D1: the references phase 3 checks against the facts (A:1250).
    pub records: Vec<NarrowRecord>,
    /// D1: `ExprId`s are `0..expr_count`.
    pub expr_count: u32,
    pub span: Span,
}

impl Body {
    /// A body with no parameter, local or statement.
    pub fn empty(owner: BodyOwner, ret: Ty, span: Span) -> Body {
        Body {
            owner,
            params: Vec::new(),
            locals: IdVec::new(),
            root: Block {
                stmts: Vec::new(),
                span,
            },
            arrows: IdVec::new(),
            ret,
            param_defaults: Vec::new(),
            facts: IdVec::new(),
            records: Vec::new(),
            expr_count: 0,
            span,
        }
    }
}

/// A local of a body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalDecl {
    pub name: Option<Symbol>,
    pub ty: Ty,
    pub mutable: bool,
    pub kind: LocalKind,
    pub span: Span,
}

/// Where a local comes from. ARCHITECTURE names locals without kinds.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum LocalKind {
    This,
    Param(Mark),
    User,
    ForBinding,
    PatBinding,
    /// A program's top-level variable, in the statements body.
    TopVar(TopVar),
    /// A local function's hidden argument (N13).
    Hidden(TopVar),
    /// A parameter of an arrow.
    Arrow(ArrowId),
}

/// An arrow function of a body. ARCHITECTURE names it without fields.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArrowBody {
    pub params: Vec<LocalId>,
    pub body: ArrowBodyKind,
    pub ret: Ty,
    pub sig: FnSigId,
    pub captures: Vec<Capture>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArrowBodyKind {
    Expr(Expr),
    Block(Block),
}

/// An outer local an arrow uses; its mode is decided in phase 3 (A:920).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Capture {
    pub local: LocalId,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StmtKind {
    /// No `init`: the type's default (SPEC O3), or unassigned if it has none.
    Let {
        local: LocalId,
        init: Option<Expr>,
    },
    Destructure {
        pat: Pat,
        mode: BindingMode,
        init: Expr,
    },
    If {
        cond: Expr,
        then_: Block,
        else_: Option<Block>,
    },
    While {
        id: LoopId,
        cond: Expr,
        body: Block,
    },
    DoWhile {
        id: LoopId,
        body: Block,
        cond: Expr,
    },
    For {
        id: LoopId,
        init: Option<Box<Stmt>>,
        cond: Option<Expr>,
        step: Option<Box<Stmt>>,
        body: Block,
    },
    ForOf {
        id: LoopId,
        pat: Pat,
        source: ForSource,
        body: Block,
    },
    Return(Option<Expr>),
    Break(LoopId),
    Continue(LoopId),
    Block(Block),
    Unsafe(Block),
    Expr(Expr),
    Expect(ExpectForm),
}

/// SPEC 5.6, set by the source: a reference gives references; an owned value copies
/// or moves each part.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum BindingMode {
    Ref,
    Owned,
}

/// A classified `for...of` source (ARCHITECTURE 2.4's seven rules; sema alone
/// classifies).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForSource {
    /// A borrowed path of array type with an empty `adjust`; read or write is phase
    /// 3's.
    Path {
        place: Expr,
    },
    /// `Ref`: a borrowed place or a reference rvalue; `Owned`: the loop takes it.
    Once {
        value: Expr,
        mode: BindingMode,
    },
    Range {
        lo: Expr,
        hi: Expr,
    },
}

/// A destructuring pattern; it nests, and arms bind nothing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pat {
    Bind(LocalId),
    Object(Vec<(FieldIdx, Pat)>),
    Tuple(Vec<Pat>),
    /// D17: a destructuring assignment's part that is a place other than a local
    /// (`[this.a, this.b] = [this.b, this.a];`, SPEC 3.4), stored into; never in a
    /// declaration. ARCHITECTURE's `Pat` binds only locals.
    Place(Box<Expr>),
}

impl Pat {
    /// The places of a destructuring assignment's parts ([`Pat::Place`]), in order.
    pub fn places(&self) -> Vec<&Expr> {
        let mut out = Vec::new();
        self.collect_places(&mut out);
        out
    }

    fn collect_places<'p>(&'p self, out: &mut Vec<&'p Expr>) {
        match self {
            Pat::Bind(_) => {}
            Pat::Object(fields) => fields.iter().for_each(|(_, p)| p.collect_places(out)),
            Pat::Tuple(parts) => parts.iter().for_each(|p| p.collect_places(out)),
            Pat::Place(e) => out.push(e),
        }
    }

    /// [`Pat::places`], mutably.
    pub fn places_mut(&mut self) -> Vec<&mut Expr> {
        let mut out = Vec::new();
        self.collect_places_mut(&mut out);
        out
    }

    fn collect_places_mut<'p>(&'p mut self, out: &mut Vec<&'p mut Expr>) {
        match self {
            Pat::Bind(_) => {}
            Pat::Object(fields) => fields
                .iter_mut()
                .for_each(|(_, p)| p.collect_places_mut(out)),
            Pat::Tuple(parts) => parts.iter_mut().for_each(|p| p.collect_places_mut(out)),
            Pat::Place(e) => out.push(e),
        }
    }
}

/// One arm of a `match`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arm {
    /// Empty for `default`.
    pub values: Vec<ArmValue>,
    pub guard: Option<Expr>,
    pub body: ArmBody,
    pub span: Span,
    /// D7: one span per value, where EN0503 points (SPEC 6).
    pub value_spans: Vec<Span>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArmValue {
    Const(ConstValue),
    Null,
    /// A case; `Ok` and `Err` too.
    Case(VariantIdx),
    /// Half-open, `lo..hi`, its ends compared by value (`ConstValue::cmp_numeric`),
    /// never by the derived `Ord`, which puts `-10` above `0`.
    Range(ConstValue, ConstValue),
    /// A condition under `match (true)`.
    Cond(Expr),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArmBody {
    Expr(Expr),
    Block(Block),
    Return(Option<Expr>),
    Break(LoopId),
    Continue(LoopId),
}

/// What a call calls.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Callee {
    Fn(FnRef),
    /// A member of a bounded type parameter, resolved per instance by mono.
    /// D15: `found` is the member typing chose on the bound (an interface member or
    /// a bounding class's method), which `member` alone cannot say when the bound
    /// has overloads of that name; mono finds the instance's member of the same
    /// exact shape (SPEC 4.4).
    BoundMember {
        param: ParamId,
        member: Symbol,
        found: DefId,
        args: TyList,
    },
    FnPtr(Box<Expr>),
    /// A closure parameter, narrowed when nullable, or a local holding an arrow.
    Closure(LocalId),
    Foreign(DefId),
    Intrinsic(IntrinsicKind, TyList),
    HostCall(HostCallId),
    /// SPEC 6's compiler forms, `Err(ErrForm)` among them.
    Form(FormKind),
    /// D8: `super.m()`, never through the method table (SPEC 4.3).
    Super(FnRef),
    /// D8: `super(...)`; `ctor: None` is the base's implicit constructor (SPEC 4.3).
    SuperCtor {
        adt: AdtId,
        args: TyList,
        ctor: Option<DefId>,
    },
}

/// A compiler form (SPEC 6's table). ARCHITECTURE names `FormKind` without listing
/// it.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum FormKind {
    ConsoleLog,
    ConsoleError,
    ToString,
    Panic,
    Err(ErrForm),
    Assert,
    Unreachable,
    Dispose,
    MemForget,
    WriteTo,
    SizeOf(Ty),
    AlignOf(Ty),
    OffsetOf(Ty, FieldIdx),
    CpuHas(Feature),
    /// D12: `clone` of a Clone type with no written `clone` (A:761 `CloneGlue`).
    Clone,
    /// D12: `fmt` of a class or enum with no written `fmt` (A:607 `DisplayGlue`).
    Fmt,
    /// D12: `equals` of an `implements Eq` class with no written body (SPEC 4.4).
    Equals,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TplPart {
    Text(StringId),
    Hole(Expr),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TryKind {
    Result,
    /// `?` into `Result<T>` from another error type keeps its text.
    ResultIntoFailure,
    Nullable,
}

/// How `Err(x)` makes its `E` (SPEC 6), decided in typing (A:373-380).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ErrForm {
    /// `x` is already an `E`.
    Value,
    /// A fixed text or template at `Failure`, or a fixed text at a literal-union `E`.
    Text,
    /// A `string` value at `Failure`, moved in with no copy.
    TextMove,
    /// An operand of type `&string`, copied at `Failure`.
    TextCopy,
    /// An error of another type at `Result<T>` keeps its text, as `?` does.
    IntoFailure,
}

/// The conversions of C18, C21 and C22 on a reference or a `Box` that MIR keeps as
/// `Rvalue::Convert` (A:386, A:493; M3 plan K4): the operand's loans and marks carry
/// over. ARCHITECTURE names the type without defining it; these are its `Adjust`
/// steps.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum ConvKind {
    FixedToSlice,
    ArrayToSlice,
    Upcast,
    BoxToInterface,
    RefToInterface,
}

impl ConvKind {
    /// The conversion an `Adjust` step makes, if it is one.
    pub fn of_adjust(a: Adjust) -> Option<ConvKind> {
        match a {
            Adjust::FixedToSlice => Some(ConvKind::FixedToSlice),
            Adjust::ArrayToSlice => Some(ConvKind::ArrayToSlice),
            Adjust::Upcast => Some(ConvKind::Upcast),
            Adjust::BoxToInterface => Some(ConvKind::BoxToInterface),
            Adjust::RefToInterface => Some(ConvKind::RefToInterface),
            _ => None,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum CastKind {
    IntToInt,
    IntToFloat,
    FloatToFloat,
    FloatToInt,
    EnumToInt,
    BoolToInt,
    UsizeToRaw,
    RawToUsize,
    RefToRaw,
    RawToRaw,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OptChain {
    pub base: Expr,
    pub member: OptMember,
    pub void_result: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OptMember {
    Field(FieldIdx),
    Call { callee: Callee, args: Vec<Expr> },
}

/// A typed expression. `id` (D1) is unique within its body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    pub id: ExprId,
    pub ty: Ty,
    pub span: Span,
    pub kind: ExprKind,
    pub adjust: Vec<Adjust>,
}

impl Expr {
    /// An expression with no adjust.
    pub fn new(id: ExprId, ty: Ty, span: Span, kind: ExprKind) -> Expr {
        Expr {
            id,
            ty,
            span,
            kind,
            adjust: Vec::new(),
        }
    }
}

/// SPEC 4.5's coercions made explicit (A:385-402); MIR building reads only these.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Adjust {
    AutoBorrow,
    Reborrow,
    ReadThrough,
    ReadThroughNullable,
    WrapNull,
    WrapNullRef,
    /// `return v` in a `Result` function (C19).
    WrapOk,
    BoxDeref,
    NeverToAny,
    LiteralDescriptor,
    FnToPtr,
    FnToUnsafePtr,
    ArrowToClosure,
    ClosureReborrow,
    /// C18: `&T[N]` to `&Slice<T>`, its address and static length (SPEC 11).
    FixedToSlice,
    /// C18: a whole `&T[]` to `&Slice<T>`, the array's `ptr` and `len`.
    ArrayToSlice,
    /// C21: `&D` or `Box<D>` to `&A` or `Box<A>`.
    Upcast,
    /// C22: `Box<I>` adds the class's table for `I` (ARCHITECTURE 7.7).
    BoxToInterface,
    /// C22: an `&C` becomes a two-word `&I` anywhere but at a non-null `&I`
    /// parameter, adding the table as `BoxToInterface` does.
    RefToInterface,
    /// D16, C17: the name of an `@interrupt` function becomes an
    /// `InterruptHandler`, which holds the address of the handler's entry stub
    /// (SPEC 4.5 C17, 7.7). ARCHITECTURE's list has no step for C17, and MIR building
    /// reads only these.
    FnToHandler,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprKind {
    // Places.
    Local(LocalId),
    Static(DefId),
    Field(Box<Expr>, FieldIdx),
    Deref(Box<Expr>),
    Index(Box<Expr>, Box<Expr>),
    /// `CheckTag` and the payload: `Present` for a non-null fact, the case inside its
    /// arm; D1: the fact that typed it.
    NarrowedPayload(Box<Expr>, VariantIdx, FactId),
    // Values.
    Const(ConstValue),
    Template(Vec<TplPart>),
    ArrayLit(Vec<Expr>),
    Repeat(Box<Expr>, u64),
    TupleLit(Vec<Expr>),
    /// An array literal with a spread; `ArrayLit` has none.
    ArrayBuild {
        elem: Ty,
        parts: Vec<ArrayPart>,
    },
    /// `new C { ... }`, or `{ ... }` at a class type.
    NewNamed {
        adt: AdtId,
        args: TyList,
        fields: Vec<(FieldIdx, Expr)>,
        default_from: Vec<FieldIdx>,
    },
    /// An anonymous object, fields in shape order; `eval` lists the indices of
    /// the values written in the literal in the order they are written, which is
    /// the order they are evaluated in (O6), the others following in shape order.
    ObjectLit {
        shape: ShapeId,
        fields: Vec<Expr>,
        eval: Vec<u32>,
    },
    /// An enum case, fields in declaration order; `eval` as for `ObjectLit`.
    VariantLit {
        adt: AdtId,
        variant: VariantIdx,
        args: TyList,
        fields: Vec<Expr>,
        eval: Vec<u32>,
    },
    New {
        ctor: DefId,
        args: TyList,
        values: Vec<Expr>,
    },
    /// O6 takes the receiver's auto-borrow last.
    Call {
        callee: Callee,
        receiver: Option<Box<Expr>>,
        args: Vec<Expr>,
    },
    Unary(UnOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Logical(LogOp, Box<Expr>, Box<Expr>),
    Coalesce(Box<Expr>, Box<Expr>),
    OptionalChain(Box<OptChain>),
    Ternary(Box<Expr>, Box<Expr>, Box<Expr>),
    Cast(Box<Expr>, CastKind),
    Borrow(Box<Expr>),
    AddrOf(Box<Expr>),
    /// A compound assignment's `op` is its `AssignOp` as a `BinOp` (`Add` for `+=`).
    Assign {
        op: Option<BinOp>,
        target: Box<Expr>,
        value: Box<Expr>,
    },
    IncDec {
        target: Box<Expr>,
        inc: bool,
        prefix: bool,
    },
    Match {
        subject: Box<Expr>,
        arms: Vec<Arm>,
    },
    Try(Box<Expr>, TryKind),
    NonNull(Box<Expr>),
    Arrow(ArrowId),
    Asm(Box<HirAsm>),
    VoidOp(Box<Expr>),
    /// An expression typing rejected, or one that never produces a value.
    Never,
    /// D9: `[a, b] = [b, a];` as an expression (SPEC 3.5).
    Destructure {
        pat: Pat,
        value: Box<Expr>,
    },
    /// D11: `null`, typed at the expected `T | null`; ARCHITECTURE has no form for it.
    NullLit,
}

/// One part of an `ArrayBuild`; a spread operand carries its borrow adjust, which
/// only reads.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArrayPart {
    Item(Expr),
    Spread(Expr, SpreadKind),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SpreadKind {
    Array,
    Fixed(u64),
    Slice,
}

/// An `asm` expression: template and operands typed only (silent in ARCHITECTURE).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirAsm {
    pub template: Symbol,
    pub ins: Vec<(Symbol, Expr)>,
    pub outs: Vec<(Symbol, Option<Expr>)>,
    pub clobbers: Vec<Symbol>,
    pub span: Span,
}

/// `expect(actual).not.matcher(args)`, typed at M2 and lowered at M4.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExpectForm {
    pub actual: Expr,
    pub negated: bool,
    pub matcher: Symbol,
    pub args: Vec<ExpectArg>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExpectArg {
    Expr(Expr),
    Arm(ArmValue),
}

/// D6: a class's field initialisers and override defaults, typed once per class
/// (SPEC 4.3).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldInits {
    pub adt: AdtId,
    pub inits: Vec<(FieldIdx, Expr)>,
    /// Each `this` written in an initialiser or override default, which typing
    /// types as an error with no report: phase 3 reports EN0610 at each (A:998;
    /// M3 plan K8). In source order.
    pub this_spans: Vec<Span>,
}

/// A place reached only through locals, fields, narrowed payloads and dereferences
/// of references and boxes (A:424-426): a `Local` (`this` is a local), `Field(b)` or
/// `NarrowedPayload(b, ..)` with `b` a path, or `Deref(b)` with `b` a path of type
/// `Ref` or `Boxed`. Everything else is false: `Index`, `Static`, `Call`, a raw
/// `Deref`.
///
/// ARCHITECTURE writes `is_path_place(e: &Expr)`, but telling a reference's `Deref`
/// from a raw one needs the operand's kind, so this takes the `Tcx`.
pub fn is_path_place(tcx: &Tcx, e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Local(_) => true,
        ExprKind::Field(base, _) | ExprKind::NarrowedPayload(base, _, _) => {
            is_path_place(tcx, base)
        }
        ExprKind::Deref(base) => {
            matches!(tcx.kind(base.ty), TyKind::Ref(_) | TyKind::Boxed(_))
                && is_path_place(tcx, base)
        }
        _ => false,
    }
}
