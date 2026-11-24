//! Typing bodies (plan d.5-d.12; A:888, SPEC 4.5-4.8, 6): bidirectional per body,
//! with union-find inference, the coercion table as `Adjust` chains, member lookup,
//! calls, overloads and generics, narrowing, destructuring, `Result` forms, closures
//! and interface types.
//!
//! [`check_body`] builds a [`FnCtxt`] and types one body into a `hir::Body`. The
//! methods of `FnCtxt` are the seams of plan h.2, each in its owner stage's file:
//! `expr.rs`, `stmt.rs`, `coerce.rs`, `ops.rs`, `cast.rs`, `literal.rs`, `infer.rs`
//! (3A); `path.rs`, `member.rs`, `call.rs` (3B); `overload.rs`, `generic.rs`,
//! `construct.rs`, `forms.rs` (4A); `narrow.rs`, `forof.rs`, `pattern.rs` (4B);
//! `result.rs`, `closure.rs`, `iface.rs` (4C).
//!
//! A body is typed in one walk (`check_expr`, `check_block`), every expression
//! synthesised and then, at a coercion site, passed to `coerce`, the only place that
//! pushes `Adjust`s (A:888). Inference variables unify across the whole body; at its
//! end ([`FnCtxt::finish`]) the defaults apply, the deferred checks run in the order
//! they were pushed (literal fit EN0411, spread elements EN0438, the integer-only
//! and signed uses of an operand that was still a variable, EN0403, EN0405, EN0420,
//! and casts whose operand was one, EN0404), and every type of
//! the body is rewritten with its variables resolved, so a finished `hir::Body` holds
//! no `Infer`.
//!
//! What a body is: a function's, method's, constructor's or destructor's block, with
//! `this` and the parameters as its first locals, each parameter default typed at its
//! parameter (D6, `param_defaults`), a destructuring parameter bound by a
//! `Destructure` at the start, and a constructor's parameter properties stored by a
//! synthesised `this.f = p` before the written body (S:583); a program's top-level
//! statements, with `args: string[]` declared first and each top-level variable a
//! `LocalKind::TopVar` (S:1143), returning `i32`, since `return 3;` there sets the
//! exit code (plan choice); a constant's, `unsafe let`'s or static assert's
//! initialiser, coerced to its annotation, an unannotated constant taking the
//! initialiser's type (S:756), typed on demand when a body typed before it reads it
//! ([`const_ty`]); and a test body, typed as an arrow whose annotation
//! must be `void` or `Result<void, E>` (S:536, EN0401).

pub(crate) mod call;
pub(crate) mod cast;
pub(crate) mod closure;
pub(crate) mod coerce;
pub(crate) mod construct;
pub(crate) mod expr;
pub(crate) mod forms;
pub(crate) mod forof;
pub(crate) mod generic;
pub(crate) mod iface;
pub(crate) mod infer;
pub(crate) mod literal;
pub(crate) mod member;
pub(crate) mod narrow;
pub(crate) mod ops;
pub(crate) mod overload;
pub(crate) mod path;
pub(crate) mod pattern;
pub(crate) mod result;
pub(crate) mod stmt;

use std::collections::{BTreeMap, BTreeSet};

use enrang_base::{BytePos, IdVec, Span, Symbol, intern};
use enrang_diag::{Code, Diagnostic};
use enrang_hir::{
    self as hir, AdtKind, ArrowBody, ArrowId, BodyOwner, ConstValue, DefKind, ExprId, ExprKind,
    FactId, FactInfo, LangItem, LocalDecl, LocalId, LocalKind, LoopId, NarrowRecord, ParamEnv,
    Receiver, TopVar, Ty, TyKind,
};
use enrang_syntax::ast;

use crate::cx::Sema;
use crate::lower::{BodyAst, ItemAstKind};
use crate::resolve::ScopeAt;
use crate::resolve::scope::ScopeStack;

/// What the context expects of an expression (plan d.5).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Expect {
    /// Nothing: the expression's own type stands.
    None,
    /// A hint that guides inference, with no coercion.
    Has(Ty),
    /// A coercion site of SPEC 4.5 (S:656).
    Coerce(Ty, Site),
}

impl Expect {
    /// The expected type, if any.
    pub fn ty(self) -> Option<Ty> {
        match self {
            Expect::None => None,
            Expect::Has(t) | Expect::Coerce(t, _) => Some(t),
        }
    }
}

/// The coercion sites of S:656.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Site {
    Arg,
    Init,
    Field,
    Assign,
    Return,
    Element,
    Branch,
}

/// The result a `return` targets: the function's, or the innermost arrow's (plan
/// d.5, d.12).
#[allow(dead_code)] // `origin` is 4C's (C19).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) struct RetCtx {
    pub ty: Ty,
    pub origin: RetOrigin,
}

/// Where a result type comes from, which decides whether C19 wraps a returned
/// value in `Ok` (A:920: never in an inferred result).
#[allow(dead_code)] // `Expected` and `Body` are 4C's.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum RetOrigin {
    /// Written in the signature or on the arrow: C19 applies.
    Written,
    /// The expected closure type's: C19 applies.
    Expected,
    /// Decided by the body, an arrow with neither: no C19, and `ty` is an
    /// inference variable.
    Body,
}

/// An arrow being typed (4C): its result replaces the function's while its body is
/// typed, and its first local tells its own locals from the captured ones.
#[allow(dead_code)] // `first_local` and `captures` are 4C's.
#[derive(Clone, Debug)]
pub(crate) struct ArrowFrame {
    pub ret: RetCtx,
    /// Locals from this one on are the arrow's; an older one it uses is a capture.
    pub first_local: LocalId,
    pub captures: Vec<hir::Capture>,
    /// The `?` that decided the result of an arrow whose body decides it, before
    /// any return did (T:902's secondary).
    pub try_fixed: Option<Span>,
}

/// A number literal, kept for its fit check once its variable resolves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Literal {
    /// The value, with a `-` written directly before it folded in (S:728).
    Int { value: u128, negative: bool },
    /// The text, parsed once at the final width.
    Float(Symbol),
}

/// A check that waits for the end of inference, run in order after defaults
/// (plan d.5, d.9).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Deferred {
    /// The literal must fit its final type (EN0411, d.6).
    LiteralFit {
        expr: ExprId,
        span: Span,
        ty: Ty,
        literal: Literal,
    },
    /// A spread's element type must be `Clone` (EN0438, A:890, S:815).
    SpreadClone { span: Span, elem: Ty },
    /// A call's type arguments, in the order of `Tcx::all_params` of the callee's
    /// generics, against their written and inferred bounds and the callee's `where`
    /// clause (EN0419, EN0805, EN0438 for a spread's `extendCloned`; EN0703, EN1006,
    /// EN0701 for the arguments themselves; A:888, S:323).
    Bounds {
        span: Span,
        callee: hir::DefId,
        args: Vec<Ty>,
    },
    /// An operand an integer-only operator, an index or `-` met while it was still
    /// an `Int` variable, which a later use may make a float (S:726) or an unsigned
    /// integer: checked once it has its final type (`ops.rs`), so the outcome never
    /// depends on the order of the statements.
    NumUse { span: Span, ty: Ty, need: NumNeed },
    /// A cast whose operand still held a variable: its kind is chosen after
    /// defaulting, and EN0404 when the table has no row for the final type (S:703).
    Cast {
        span: Span,
        value: Span,
        from: Ty,
        to: Ty,
    },
}

/// What a [`Deferred::NumUse`] operand must be.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum NumNeed {
    /// An integer, for this bitwise or shift operator (EN0403).
    Integer(&'static str),
    /// An integer, as an index (EN0405).
    Index,
    /// A signed number, for `-` (EN0420).
    Signed,
}

/// A call being typed, for the messages of a coercion at one of its arguments
/// (EN0612 names the callee, G17).
#[derive(Clone, Debug)]
pub(crate) struct CallFrame {
    /// The callee's name as written (`bump`, `push` for `xs.push`).
    pub callee: Option<Symbol>,
    /// The callee expression, which an argument's help may name.
    pub callee_span: Span,
    /// Each argument's span.
    pub args: Vec<Span>,
    /// Whether the call itself reported an error that covers its arguments (EN0423,
    /// EN0451, a callee that could not be typed): then an arrow argument typed
    /// with no expected type is not EN0409 as well.
    pub reported: bool,
}

/// The state of typing one body.
pub(crate) struct FnCtxt<'s, 'a> {
    pub sema: &'s mut Sema<'a>,
    pub owner: BodyOwner,
    /// Where names in the body resolve, below its locals.
    pub at: ScopeAt,
    pub locals: IdVec<LocalId, LocalDecl>,
    pub params: Vec<LocalId>,
    pub arrows: IdVec<ArrowId, ArrowBody>,
    pub infer: infer::InferTable,
    pub scopes: ScopeStack,
    pub flow: narrow::FlowState,
    /// The states at each loop's `break`s and `continue`s (4B).
    pub jumps: narrow::Jumps,
    pub facts: IdVec<FactId, FactInfo>,
    pub records: Vec<NarrowRecord>,
    pub loops: Vec<LoopId>,
    pub next_loop: u32,
    pub next_expr: u32,
    /// The body's result; an arrow's is on `arrow_stack` (`ret_ctx`).
    pub ret: RetCtx,
    /// The arrows being typed, innermost last.
    pub arrow_stack: Vec<ArrowFrame>,
    /// The checks that wait for the end of inference.
    pub deferred: Vec<Deferred>,
    pub unsafe_depth: u32,
    /// The bounds a `where` clause adds in this body.
    pub env: ParamEnv,
    /// The body's name as messages give it (`area`), for EN0427.
    pub name: Option<Symbol>,
    /// The span of the written result type, for EN0401's secondary at a `return`.
    pub ret_span: Option<Span>,
    /// While an annotated initialiser is typed: its span and the annotation's.
    pub init_annotation: Option<(Span, Span)>,
    /// While a local's initialiser is typed: the local's name, which EN0440's help
    /// names.
    pub init_name: Option<Symbol>,
    /// The calls being typed, innermost last.
    pub calls: Vec<CallFrame>,
    /// Whether the end of what has been typed so far can be reached (EN0427).
    pub reachable: bool,
    /// The loops some `break` leaves.
    pub broken: BTreeSet<LoopId>,
    /// The loops some `continue` targets, whose condition a `continue` reaches.
    pub continued: BTreeSet<LoopId>,
    /// A label written before the loop about to be entered.
    pub pending_label: Option<Symbol>,
    /// The loops that carry a label, innermost last.
    pub labelled: Vec<LoopId>,
    /// How many blocks deep the statement being typed is.
    pub depth: u32,
    /// Parameter defaults (D6).
    pub param_defaults: Vec<(LocalId, hir::Expr)>,
    /// The constant of each number literal at its final type, filled by the fit
    /// checks and written into the body by `resolve_body`.
    pub literal_values: BTreeMap<ExprId, ConstValue>,
    /// Integer divisions to check once the defaults apply (EN0430).
    pub int_divisions: Vec<ops::IntDivision>,
    /// The arrow each local was initialised with, for EN1007's capture (S:966).
    pub local_arrows: BTreeMap<LocalId, hir::ArrowId>,
    /// Each `this` of a field initialiser, typed as an error with no report, for
    /// phase 3's EN0610 (`FieldInits::this_spans`, M3 plan K8). A probe that
    /// typing rolls back may leave a span, which the committed way types again, so
    /// the reader sorts and dedupes.
    pub this_spans: Vec<Span>,
    /// The number literals standing as `match` arm values, held as `ArmValue::Cond`
    /// until `resolve_body` makes each a `Const` at its final type.
    pub arm_literals: BTreeSet<ExprId>,
    /// The ranges standing as `match` arm values, each an `ArmValue::Cond` holding a
    /// `TupleLit` of its ends until `resolve_body` makes it a `Range`.
    pub arm_ranges: BTreeSet<ExprId>,
    /// While an object pattern's field is looked up: the pattern's other field
    /// names, which "did you mean" does not offer (`{ x, w }` never suggests `x`).
    pub taken_names: Vec<Symbol>,
    /// How the value of the expression being typed is used: whether a `null` in
    /// its place would still check, so EN0303 offers its `?.` fix-it only where it
    /// gives code that compiles. `check_expr` sets it from its expected type, a
    /// parenthesised expression keeps its enclosing one's, and a receiver of `.`
    /// needs a value (`check_operand`), since `?.` never short-circuits (S:607).
    pub value_use: ValueUse,
    /// Set right before a `check_expr` call whose expression keeps the use already
    /// in `value_use`; that call clears it.
    pub inherit_use: bool,
}

/// Whether a `null` may stand where a value is used (`FnCtxt::value_use`).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum ValueUse {
    /// No expected type, or one that admits `null` and a reference: a statement's
    /// value, an unannotated initialiser, a `&T | null` site.
    Any,
    /// A `T | null` site with a by-value `T`: `?.m()` gives the method's value or
    /// `null`, but `?.f` a `&F | null`, which fits only when `F` is Copy (C08).
    Copied,
    /// A site whose type is no nullable, an operand of arithmetic or an ordering,
    /// or a condition.
    NonNull,
}

impl<'s, 'a> FnCtxt<'s, 'a> {
    pub fn new(sema: &'s mut Sema<'a>, owner: BodyOwner, at: ScopeAt, ret: Ty) -> FnCtxt<'s, 'a> {
        FnCtxt {
            sema,
            owner,
            at,
            locals: IdVec::new(),
            params: Vec::new(),
            arrows: IdVec::new(),
            infer: infer::InferTable::default(),
            scopes: ScopeStack::default(),
            flow: narrow::FlowState::default(),
            jumps: narrow::Jumps::default(),
            facts: IdVec::new(),
            records: Vec::new(),
            loops: Vec::new(),
            next_loop: 0,
            next_expr: 0,
            ret: RetCtx {
                ty: ret,
                origin: RetOrigin::Written,
            },
            arrow_stack: Vec::new(),
            deferred: Vec::new(),
            unsafe_depth: 0,
            env: ParamEnv::empty(),
            name: None,
            ret_span: None,
            init_annotation: None,
            init_name: None,
            calls: Vec::new(),
            reachable: true,
            broken: BTreeSet::new(),
            continued: BTreeSet::new(),
            pending_label: None,
            labelled: Vec::new(),
            depth: 0,
            param_defaults: Vec::new(),
            literal_values: BTreeMap::new(),
            taken_names: Vec::new(),
            int_divisions: Vec::new(),
            local_arrows: BTreeMap::new(),
            this_spans: Vec::new(),
            arm_literals: BTreeSet::new(),
            arm_ranges: BTreeSet::new(),
            value_use: ValueUse::Any,
            inherit_use: false,
        }
    }

    /// The use `ex` gives a value: `NonNull` when its type is known and admits no
    /// `null` (a variable, `Error` and `void` admit anything).
    pub(crate) fn use_of(&self, ex: Expect) -> ValueUse {
        let Some(t) = ex.ty() else {
            return ValueUse::Any;
        };
        match self.sema.tcx.kind(self.shallow(t)) {
            TyKind::Nullable(payload) => match self.sema.tcx.kind(self.shallow(payload)) {
                TyKind::Ref(_) | TyKind::Infer(_) | TyKind::Error => ValueUse::Any,
                _ => ValueUse::Copied,
            },
            TyKind::Infer(_) | TyKind::Error | TyKind::Void => ValueUse::Any,
            _ => ValueUse::NonNull,
        }
    }

    /// `e` typed as an operand that needs a value, never `null`: of arithmetic or
    /// an ordering (`a.zip?.length() > 0` would not check).
    pub(crate) fn check_value(&mut self, e: &ast::Expr, ex: Expect) -> hir::Expr {
        let saved = self.value_use;
        self.value_use = ValueUse::NonNull;
        self.inherit_use = true;
        let typed = self.check_expr(e, ex);
        self.value_use = saved;
        typed
    }

    /// The result a `return` here targets: the innermost arrow's, else the body's.
    pub fn ret_ctx(&self) -> RetCtx {
        self.arrow_stack.last().map_or(self.ret, |frame| frame.ret)
    }

    pub fn error_ty(&self) -> Ty {
        self.sema.tcx.common().error
    }

    /// A fresh expression id.
    pub fn next_id(&mut self) -> ExprId {
        let id = ExprId(self.next_expr);
        self.next_expr += 1;
        id
    }

    /// An expression of `ty` with no adjust.
    pub fn mk_expr(&mut self, ty: Ty, span: Span, kind: ExprKind) -> hir::Expr {
        let id = self.next_id();
        hir::Expr::new(id, ty, span, kind)
    }

    /// The placeholder of an expression typing rejected, or that no stage types
    /// yet: `Never` of type `Error`, which absorbs every later check.
    pub fn error_expr(&mut self, span: Span) -> hir::Expr {
        let error = self.error_ty();
        self.mk_expr(error, span, ExprKind::Never)
    }

    /// Declares a local in the innermost block.
    pub fn declare(
        &mut self,
        name: Option<Symbol>,
        ty: Ty,
        mutable: bool,
        kind: LocalKind,
        span: Span,
    ) -> LocalId {
        let local = self.locals.push(LocalDecl {
            name,
            ty,
            mutable,
            kind,
            span,
        });
        if let Some(name) = name {
            self.scopes.declare(name, local);
        }
        local
    }

    /// A fresh loop id, pushed as the innermost loop; a label written before the
    /// loop names it.
    pub fn enter_loop(&mut self) -> LoopId {
        let id = LoopId(self.next_loop);
        self.next_loop += 1;
        self.loops.push(id);
        if let Some(label) = self.pending_label.take() {
            self.scopes.push_label(label, id);
            self.labelled.push(id);
        }
        id
    }

    pub fn exit_loop(&mut self) {
        if let Some(id) = self.loops.pop()
            && self.labelled.last() == Some(&id)
        {
            self.labelled.pop();
            self.scopes.pop_label();
        }
    }

    /// The written type `t` at this body's scope, each class or enum instance in it
    /// checked against its parameters' bounds as a declaration's types are (EN0419
    /// at `t`).
    pub fn lower_ty(&mut self, t: &ast::TypeExpr) -> Ty {
        let ty = self.lower_ty_unchecked(t);
        generic::check_written(self.sema, t.span, ty, &self.env);
        ty
    }

    /// [`Self::lower_ty`] without the bound check, for a construction's class or
    /// enum, whose instance the construction checks itself (one diagnostic per
    /// mistake).
    pub fn lower_ty_unchecked(&mut self, t: &ast::TypeExpr) -> Ty {
        let saved = self.shadow_lengths(t);
        let ty = crate::lower::types::lower_ty(self.sema, self.at, t);
        self.sema.consts.shadowing = saved;
        ty
    }

    /// The written type `t` of a parameter (an arrow's), where a closure type may
    /// stand at the top (S:367), checked as [`Self::lower_ty`] checks.
    pub fn lower_param_ty(&mut self, t: &ast::TypeExpr) -> Ty {
        let saved = self.shadow_lengths(t);
        let ty = crate::lower::types::lower_param_ty(self.sema, self.at, t);
        self.sema.consts.shadowing = saved;
        generic::check_written(self.sema, t.span, ty, &self.env);
        ty
    }

    /// [`Self::lower_param_ty`] for an arrow's parameter, where no closure type
    /// stands (closures do not nest, EN0705).
    pub(crate) fn lower_arrow_param_ty(&mut self, t: &ast::TypeExpr) -> Ty {
        let saved = self.shadow_lengths(t);
        let ty = crate::lower::types::lower_arrow_param_ty(self.sema, self.at, t);
        self.sema.consts.shadowing = saved;
        generic::check_written(self.sema, t.span, ty, &self.env);
        ty
    }

    /// Tells const eval which names in `t`'s lengths are locals here, which hide
    /// any constant of their name (S:756); returns what to restore.
    fn shadow_lengths(&mut self, t: &ast::TypeExpr) -> Vec<enrang_base::Symbol> {
        let mut names = Vec::new();
        length_idents(t, &mut names);
        self.shadow_names(names)
    }

    /// [`Self::shadow_lengths`] for the identifiers `names` of a length.
    pub(crate) fn shadow_names(
        &mut self,
        names: Vec<enrang_base::Symbol>,
    ) -> Vec<enrang_base::Symbol> {
        let locals: Vec<enrang_base::Symbol> = names
            .into_iter()
            .filter(|&n| self.scopes.lookup(n).is_some())
            .collect();
        let mut shadowing = self.sema.consts.shadowing.clone();
        shadowing.extend(locals);
        std::mem::replace(&mut self.sema.consts.shadowing, shadowing)
    }

    /// The source text under `span`.
    pub fn snippet(&self, span: Span) -> String {
        if span.is_dummy() {
            return String::new();
        }
        self.sema.tcx.map().text(span).to_owned()
    }

    /// Whether `t` is `Error` or holds it.
    pub fn is_error(&self, t: Ty) -> bool {
        let t = self.resolve(t);
        self.sema.tcx.references_error(t)
    }

    /// Ends the body: defaults, deferred checks in order, then every type resolved.
    pub(crate) fn finish(mut self, root: hir::Block, span: Span) -> hir::Body {
        self.apply_defaults();
        self.check_int_divisions();
        for d in std::mem::take(&mut self.deferred) {
            match d {
                Deferred::LiteralFit {
                    expr,
                    span,
                    ty,
                    literal,
                } => self.check_literal_fit(expr, span, ty, &literal),
                Deferred::SpreadClone { span, elem } => self.check_spread_clone(span, elem),
                Deferred::NumUse { span, ty, need } => self.check_num_use(span, ty, need),
                Deferred::Cast {
                    span,
                    value,
                    from,
                    to,
                } => self.check_deferred_cast(span, value, from, to),
                Deferred::Bounds { span, callee, args } => {
                    self.check_deferred_bounds(span, callee, &args)
                }
            }
        }
        let mut body = hir::Body {
            owner: self.owner,
            params: std::mem::take(&mut self.params),
            locals: std::mem::take(&mut self.locals),
            root,
            arrows: std::mem::take(&mut self.arrows),
            ret: self.ret.ty,
            param_defaults: std::mem::take(&mut self.param_defaults),
            facts: std::mem::take(&mut self.facts),
            records: std::mem::take(&mut self.records),
            expr_count: self.next_expr,
            span,
        };
        self.resolve_body(&mut body);
        body
    }
}

/// A parameter's AST: a function's or method's, or a constructor's.
#[derive(Copy, Clone)]
enum ParamAst<'a> {
    Plain(&'a ast::Param),
    Ctor(&'a ast::CtorParam),
}

impl ParamAst<'_> {
    fn default(&self) -> Option<&ast::Expr> {
        match self {
            ParamAst::Plain(p) => p.default.as_ref(),
            ParamAst::Ctor(p) => p.default.as_ref(),
        }
    }

    fn pattern(&self) -> Option<&ast::Binding> {
        match self {
            ParamAst::Plain(p) => match &p.binding {
                ast::Binding::Name(_) => None,
                pattern => Some(pattern),
            },
            ParamAst::Ctor(_) => None,
        }
    }

    fn name_span(&self) -> Span {
        match self {
            ParamAst::Plain(p) => match &p.binding {
                ast::Binding::Name(n) => n.span,
                _ => p.span,
            },
            ParamAst::Ctor(p) => p.name.span,
        }
    }
}

/// Types the body of `owner` (plan d.5).
pub(crate) fn check_body(sema: &mut Sema, owner: BodyOwner) -> hir::Body {
    let common = *sema.tcx.common();
    let at = sema
        .decls
        .scope_of(owner)
        .unwrap_or_else(|| ScopeAt::module(sema.module_id(sema.program.entry), false));
    let ast = sema.decls.body_ast(owner);
    let span = match owner {
        BodyOwner::Statements(m) => sema.program.modules[sema.res.index(m)].ast.span,
        BodyOwner::Fn(def) | BodyOwner::Const(def) | BodyOwner::Test(def) => sema.tcx.def(def).span,
    };
    let ret = match owner {
        BodyOwner::Fn(def) => sema.tcx.sig_opt(def).map_or(common.error, |s| s.ret),
        BodyOwner::Const(def) => sema.tcx.item_ty(def).unwrap_or(common.error),
        BodyOwner::Statements(_) => common.i32,
        BodyOwner::Test(_) => common.void,
    };
    // An unannotated constant is being typed until its body is done, so a read of
    // it from its own initialiser, through others or not, is a cycle (`const_ty`).
    let unannotated = match owner {
        BodyOwner::Const(def) => sema.tcx.item_ty(def).is_none(),
        _ => false,
    };
    if let (true, BodyOwner::Const(def)) = (unannotated, owner) {
        sema.typing_consts.push(def);
    }
    let mut fcx = FnCtxt::new(sema, owner, at, ret);
    fcx.scopes.push();
    let root = match (owner, ast) {
        (BodyOwner::Fn(def), Some(ast)) => fcx.check_fn(def, ast, span),
        (BodyOwner::Statements(module), Some(BodyAst::Statements(stmts))) => {
            fcx.declare_args(module);
            fcx.check_stmts(stmts, span)
        }
        (BodyOwner::Const(def), Some(BodyAst::Const(e))) => fcx.check_const(def, e),
        (BodyOwner::Test(_), Some(BodyAst::Test(arrow))) => fcx.check_test(arrow),
        _ => hir::Block {
            stmts: Vec::new(),
            span,
        },
    };
    let body = fcx.finish(root, span);
    if unannotated {
        sema.typing_consts.pop();
    }
    if let BodyOwner::Const(def) = owner
        && sema.tcx.item_ty(def).is_none()
        && sema.tcx.def(def).kind == DefKind::Const
        && let Some(hir::Stmt {
            kind: hir::StmtKind::Expr(value),
            ..
        }) = body.root.stmts.first()
    {
        sema.tcx.set_item_ty(def, value.ty);
    }
    body
}

/// The type of constant `def` where a body reads it: its annotation's, or the type
/// of its initialiser (S:756), which, for an unannotated constant whose turn has not
/// come, is typed here, its body kept for that turn (`Sema::early_consts`). A read
/// of an unannotated constant from its own initialiser, directly or through others,
/// is EN0412 `` constant cycle: `A` uses `B`, which uses `A` `` at the first constant
/// of the cycle in source order, as const eval words it, and the read is `Error`.
/// `None` for what is no constant.
pub(crate) fn const_ty(sema: &mut Sema, def: hir::DefId) -> Option<Ty> {
    if let Some(ty) = sema.tcx.item_ty(def) {
        return Some(ty);
    }
    if sema.tcx.def(def).kind != DefKind::Const {
        return None;
    }
    let error = sema.tcx.common().error;
    if let Some(start) = sema.typing_consts.iter().position(|&d| d == def) {
        let members = sema.typing_consts[start..].to_vec();
        if let Some(diag) = crate::consteval::cycle(sema.tcx, &members).diagnostic() {
            sema.emit(diag.clone());
        }
        return Some(error);
    }
    if sema.bodies.contains_key(&def)
        || sema.early_consts.contains_key(&def)
        || sema.decls.body_ast(BodyOwner::Const(def)).is_none()
    {
        // Typed already, which set its type, or with no initialiser to type.
        return Some(error);
    }
    let body = check_body(sema, BodyOwner::Const(def));
    sema.early_consts.insert(def, body);
    Some(sema.tcx.item_ty(def).unwrap_or(error))
}

impl FnCtxt<'_, '_> {
    /// A function's, method's, constructor's or destructor's body.
    fn check_fn(&mut self, def: hir::DefId, ast: BodyAst<'_>, span: Span) -> hir::Block {
        self.name = self.sema.tcx.def(def).name();
        if let Some(sig) = self.sema.tcx.sig_opt(def) {
            self.env = ParamEnv {
                bounds: sig.where_bounds.clone(),
            };
        }
        let (params, block, ret) = match ast {
            BodyAst::Function(f) => (
                f.params.iter().map(ParamAst::Plain).collect(),
                Some(&f.body),
                f.ret.as_ref(),
            ),
            BodyAst::Method(m) => (
                m.params.iter().map(ParamAst::Plain).collect(),
                m.body.as_ref(),
                m.ret.as_ref(),
            ),
            BodyAst::Ctor(c) => (
                c.params.iter().map(ParamAst::Ctor).collect(),
                Some(&c.body),
                None,
            ),
            BodyAst::Dtor(d) => (Vec::new(), Some(&d.body), None),
            BodyAst::Statements(_) | BodyAst::Const(_) | BodyAst::Test(_) => {
                (Vec::new(), None, None)
            }
        };
        self.ret_span = ret.map(|r| r.ty.span);
        let mut prologue = self.declare_params(def, &params);
        let Some(block) = block else {
            return hir::Block {
                stmts: prologue,
                span,
            };
        };
        let mut checked = self.check_block(block);
        if self.reachable {
            self.check_fall_off(block.span);
        }
        prologue.append(&mut checked.stmts);
        checked.stmts = prologue;
        checked
    }

    /// EN0427 when a body that must return a value can end (S:1137); falling off a
    /// `Result<void, E>` body is `return Ok();` (S:677).
    fn check_fall_off(&mut self, block: Span) {
        let ret = self.resolve(self.ret.ty);
        let tcx = &*self.sema.tcx;
        let returns_nothing = match tcx.kind(ret) {
            TyKind::Void | TyKind::Error => true,
            TyKind::Adt(adt, args) if tcx.is_lang_adt(adt, LangItem::Result) => tcx
                .list(args)
                .first()
                .is_some_and(|&ok| tcx.kind(ok) == TyKind::Void),
            _ => tcx.references_error(ret),
        };
        if returns_nothing {
            return;
        }
        let close = Span {
            lo: BytePos(block.hi.0.saturating_sub(1)),
            hi: block.hi,
        };
        let name = self
            .name
            .map_or_else(|| "this function".to_owned(), |n| format!("`{n}`"));
        let ty = self.ty_str(ret);
        let mut diag = Diagnostic::new(
            Code::EN0427,
            format!(
                "{name} may end without returning {}",
                crate::classes::sig::a_ty(&ty)
            ),
            close,
            format!("the end of the body is reached without a `return`"),
        );
        if let Some(ret_span) = self.ret_span {
            diag = diag.with_secondary(ret_span, format!("`{ty}` is required by the return type"));
        }
        self.sema.emit(diag);
    }

    /// `this` (for a method with a receiver, a constructor or a destructor) and the
    /// parameters, as the body's first locals; returns the statements that run before
    /// the written body: a destructuring parameter's `Destructure` and a constructor's
    /// parameter properties. Each default is typed at its parameter (D6).
    fn declare_params(&mut self, def: hir::DefId, asts: &[ParamAst<'_>]) -> Vec<hir::Stmt> {
        let Some(sig) = self.sema.tcx.sig_opt(def).cloned() else {
            return Vec::new();
        };
        let data = self.sema.tcx.def(def).clone();
        let has_this = match data.kind {
            DefKind::Ctor | DefKind::Dtor => true,
            DefKind::Method => !matches!(sig.receiver, Some(Receiver::Static) | None),
            _ => false,
        };
        let mut this = None;
        if has_this {
            let this_ty = self.this_ty(data.parent);
            let local = self.declare(
                Some(intern("this")),
                this_ty,
                false,
                LocalKind::This,
                data.span,
            );
            self.params.push(local);
            this = Some(local);
        }
        let mut locals = Vec::new();
        for (i, p) in sig.params.iter().enumerate() {
            let ast = asts.get(i);
            let pattern = ast.and_then(ParamAst::pattern);
            let name = if pattern.is_some() {
                None
            } else {
                Some(p.name)
            };
            let span = ast.map_or(p.span, ParamAst::name_span);
            let local = self.declare(name, p.ty, false, LocalKind::Param(p.mark), span);
            self.params.push(local);
            locals.push(local);
        }
        let mut prologue = Vec::new();
        for (i, ast) in asts.iter().enumerate() {
            let (Some(&local), Some(p)) = (locals.get(i), sig.params.get(i)) else {
                continue;
            };
            if let Some(default) = ast.default() {
                let value = self.check_expr(default, Expect::Coerce(p.ty, Site::Arg));
                self.param_defaults.push((local, value));
            } else if p.has_default {
                // `x?: T` is `x: T | null = null` (S:829): its default is explicit,
                // so a call that leaves it out finds `null` there (A:937).
                let value = self.mk_expr(p.ty, ast.name_span(), ExprKind::NullLit);
                self.param_defaults.push((local, value));
            }
            if let Some(pattern) = ast.pattern() {
                let span = ast.name_span();
                let init = self.mk_expr(p.ty, span, ExprKind::Local(local));
                let (pat, mode) = self.check_destructure(pattern, init.clone());
                prologue.push(hir::Stmt {
                    kind: hir::StmtKind::Destructure { pat, mode, init },
                    span,
                });
            }
            if let ParamAst::Ctor(c) = ast
                && c.property.is_some()
                && let Some(this) = this
                && let Some(stmt) = self.store_property(this, local, c)
            {
                prologue.push(stmt);
            }
        }
        prologue
    }

    /// `this.f = p` for a constructor's parameter property (S:583).
    fn store_property(
        &mut self,
        this: LocalId,
        param: LocalId,
        c: &ast::CtorParam,
    ) -> Option<hir::Stmt> {
        let this_ty = self.locals[this].ty;
        let TyKind::Ref(class_ty) = self.sema.tcx.kind(this_ty) else {
            return None;
        };
        let TyKind::Adt(adt, args) = self.sema.tcx.kind(class_ty) else {
            return None;
        };
        let class = self.sema.tcx.adt(adt).as_class()?;
        let (field, _) = class.field_named(c.name.name)?;
        let field_ty = self.sema.tcx.field_ty(adt, None, field, args);
        let span = c.span;
        let this_e = self.mk_expr(this_ty, span, ExprKind::Local(this));
        // `this` is a reference: the field is reached through a `Deref`, as a
        // member's base is (plan d.8).
        let base = self.mk_expr(class_ty, span, ExprKind::Deref(Box::new(this_e)));
        let target = self.mk_expr(field_ty, span, ExprKind::Field(Box::new(base), field));
        let param_ty = self.locals[param].ty;
        let value = self.mk_expr(param_ty, span, ExprKind::Local(param));
        let value = self.coerce(value, field_ty, Site::Field);
        let assign = self.mk_expr(
            field_ty,
            span,
            ExprKind::Assign {
                op: None,
                target: Box::new(target),
                value: Box::new(value),
            },
        );
        Some(hir::Stmt {
            kind: hir::StmtKind::Expr(assign),
            span,
        })
    }

    /// The type of `this` in a member of `parent`: a reference to the class or enum
    /// at its own parameters; an `extend` block's pattern; `Self` in an interface.
    fn this_ty(&self, parent: Option<hir::DefId>) -> Ty {
        let tcx = &*self.sema.tcx;
        let Some(parent) = parent else {
            return tcx.common().error;
        };
        let inner = match tcx.adt_of(parent) {
            Some(adt) => match tcx.adt(adt).as_interface() {
                Some(iface) => tcx.mk_param(iface.self_param),
                None => tcx.adt_identity(adt),
            },
            None => tcx
                .extends()
                .iter()
                .find(|e| e.def == parent)
                .map_or(tcx.common().error, |e| e.ty),
        };
        match tcx.kind(inner) {
            TyKind::Error => inner,
            _ => tcx.mk_ref(inner),
        }
    }

    /// `args: string[]`, the first top-level variable of a program's statements
    /// (S:1143; plan choice: `TopVar(0)`).
    fn declare_args(&mut self, module: hir::ModuleId) {
        if self.sema.res.toplevel.module != Some(module) {
            return;
        }
        let str_ty = self.sema.tcx.common().str;
        let ty = self.sema.tcx.mk_array(str_ty);
        self.declare(
            Some(intern("args")),
            ty,
            false,
            LocalKind::TopVar(TopVar(0)),
            Span::DUMMY,
        );
    }

    /// The top-level variable a declaration of `name` at `span` among a program's
    /// statements is.
    pub(crate) fn top_var(&self, name: Symbol, span: Span) -> Option<TopVar> {
        if !matches!(self.owner, BodyOwner::Statements(_)) || self.depth != 1 {
            return None;
        }
        self.sema
            .res
            .toplevel
            .vars
            .iter()
            .position(|v| v.name == name && v.span == span)
            .map(|i| TopVar(i as u32))
    }

    /// A constant's, `unsafe let`'s or static assert's initialiser.
    fn check_const(&mut self, def: hir::DefId, e: &ast::Expr) -> hir::Block {
        let kind = self.sema.tcx.def(def).kind;
        let value = match kind {
            DefKind::StaticAssert => self.check_cond(e),
            _ => match self.sema.tcx.item_ty(def) {
                Some(ty) => {
                    let annotation = self.annotation_of(def);
                    let saved = self.init_annotation.take();
                    self.init_annotation = annotation.map(|a| (e.span, a));
                    let value = self.check_expr(e, Expect::Coerce(ty, Site::Init));
                    self.init_annotation = saved;
                    value
                }
                None => self.check_expr(e, Expect::None),
            },
        };
        hir::Block {
            stmts: vec![hir::Stmt {
                span: e.span,
                kind: hir::StmtKind::Expr(value),
            }],
            span: e.span,
        }
    }

    /// The span of a constant's or static's written type.
    fn annotation_of(&self, def: hir::DefId) -> Option<Span> {
        self.sema
            .decls
            .items
            .iter()
            .find(|item| item.def == def)
            .and_then(|item| match &item.kind {
                ItemAstKind::Const(c) => c.ty.as_ref().map(|t| t.span),
                ItemAstKind::Static(u) => Some(u.ty.span),
                _ => None,
            })
    }

    /// A test body, typed as an arrow: its annotation must be `void` or
    /// `Result<void, E>` (S:536, EN0401; plan d.17).
    fn check_test(&mut self, arrow: &ast::ArrowFn) -> hir::Block {
        if let Some(ret) = &arrow.ret {
            let ty = self.lower_ty(&ret.ty);
            if self.test_result_ok(ty) {
                self.ret.ty = ty;
                self.ret_span = Some(ret.ty.span);
            } else {
                let shown = self.ty_str(ty);
                self.sema.emit(Diagnostic::new(
                    Code::EN0401,
                    format!("a test returns `void` or `Result<void, E>`, not `{shown}`"),
                    ret.ty.span,
                    format!("this is `{shown}`"),
                ));
                self.ret.ty = self.error_ty();
            }
        }
        for p in &arrow.params {
            let ty = match &p.ty {
                Some(t) => self.lower_param_ty(t),
                None => self.error_ty(),
            };
            let local = self.declare(
                Some(p.name.name),
                ty,
                false,
                LocalKind::Param(if p.is_let {
                    hir::Mark::Let
                } else {
                    hir::Mark::None
                }),
                p.name.span,
            );
            self.params.push(local);
        }
        match &arrow.body {
            ast::ArrowBody::Block(block) => self.check_block(block),
            ast::ArrowBody::Expr(e) => {
                let value = self.check_expr(e, Expect::None);
                hir::Block {
                    stmts: vec![hir::Stmt {
                        span: e.span,
                        kind: hir::StmtKind::Expr(value),
                    }],
                    span: e.span,
                }
            }
        }
    }

    /// Whether `ty` is `void` or `Result<void, E>`, or an error.
    fn test_result_ok(&self, ty: Ty) -> bool {
        let tcx = &*self.sema.tcx;
        match tcx.kind(ty) {
            TyKind::Void | TyKind::Error => true,
            TyKind::Adt(adt, args) => {
                tcx.is_lang_adt(adt, LangItem::Result)
                    && tcx
                        .list(args)
                        .first()
                        .is_some_and(|&ok| tcx.kind(ok) == TyKind::Void)
            }
            _ => false,
        }
    }

    /// Whether `ty` (resolved) is an enum written as a string-literal union.
    pub(crate) fn str_union_of(&self, ty: Ty) -> Option<hir::AdtId> {
        let tcx = &*self.sema.tcx;
        match tcx.kind(self.shallow(ty)) {
            TyKind::Adt(adt, _) => match &tcx.adt(adt).kind {
                AdtKind::Enum(e) if e.str_union => Some(adt),
                _ => None,
            },
            _ => None,
        }
    }
}

/// The identifiers the array lengths written anywhere in `t` read.
fn length_idents(t: &ast::TypeExpr, out: &mut Vec<enrang_base::Symbol>) {
    match &t.kind {
        ast::TypeExprKind::Fixed(elem, len) => {
            out.extend(crate::consteval::idents_of(len));
            length_idents(elem, out);
        }
        ast::TypeExprKind::Named { args, .. } => args.iter().for_each(|a| length_idents(a, out)),
        ast::TypeExprKind::Nullable(inner)
        | ast::TypeExprKind::Ref(inner)
        | ast::TypeExprKind::Raw(inner)
        | ast::TypeExprKind::ReadonlyRef(inner)
        | ast::TypeExprKind::Array(inner)
        | ast::TypeExprKind::Paren(inner) => length_idents(inner, out),
        ast::TypeExprKind::Tuple(parts) | ast::TypeExprKind::Union(parts) => {
            parts.iter().for_each(|p| length_idents(p, out))
        }
        ast::TypeExprKind::FnPtr(f) => {
            f.params.iter().for_each(|p| length_idents(&p.ty, out));
            length_idents(&f.ret.ty, out);
        }
        ast::TypeExprKind::Closure(c) => {
            c.params.iter().for_each(|p| length_idents(&p.ty, out));
            length_idents(&c.ret, out);
        }
        ast::TypeExprKind::Object(fields) => {
            fields.iter().for_each(|(_, _, f)| length_idents(f, out))
        }
        ast::TypeExprKind::StrUnion(_)
        | ast::TypeExprKind::Void
        | ast::TypeExprKind::Never
        | ast::TypeExprKind::NullLit
        | ast::TypeExprKind::Error => {}
    }
}
