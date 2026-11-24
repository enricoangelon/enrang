//! Constant evaluation (plan d.14; SPEC 4.9, S:754-758; ARCHITECTURE 4 "Const eval",
//! A:918): a small interpreter over typed HIR (owner 2E), and its integration with
//! typing (owner 4F: `check_items`, `eval_len`).
//!
//! A constant expression is built from literals, `null` among them, other constants,
//! arithmetic with checked overflow at the target's widths (`isize` and `usize` from
//! its `DataLayout`), comparisons, `!`, `&&` and `||`, `sizeOf`, `alignOf` and
//! `offsetOf` through `enrang-layout`, numeric `as` and `usize` to raw pointer `as`,
//! and fixed-array, tuple, object, class (`new C { ... }`) and case literals of those;
//! `&` of a bracket literal of those is a constant literal view
//! (`ConstTree::View`), and a string literal at `&string` is a constant (S:756).
//!
//! Every failure is EN0412, `constant evaluation failed: ...`: an operation that
//! would panic at run time, labelled with the message that panic prints (SPEC 9.1);
//! a part that is not constant, named, with a label saying what it is; a spread, at
//! its `...`, with the note `a spread allocates at run time`; `sizeOf`, `alignOf` or
//! `offsetOf` of a borrowing class or tuple, with SPEC 4.9's note; a cycle, `constant
//! cycle: ...`, at the first constant of the cycle in source order. A call is EN1032
//! with SPEC 16's message, note and help.
//!
//! Each root is checked in three steps: its shape (every part constant, so a call or
//! a non-constant part is reported even in an operand that `&&` or `||` skips), then
//! the constants it reads, each evaluated on demand and memoised, on an explicit
//! stack, so a long chain of constants never deepens the Rust stack and the stack
//! itself gives the cycle; then its value, `&&` and `||` skipping as at run time. A
//! constant that reads a failed one fails with the same diagnostic, which `DiagCtx`
//! keeps once (it keeps the first per code and primary span).
//!
//! The contexts (4F, plan d.14): `check_items`, run after declarations are lowered
//! and before bodies are typed, computes enum case values (with `@repr`'s fit,
//! S:1288), every top-level `const` and `unsafe let` value (kept with
//! `Tcx::set_const`, so a `match` arm naming a constant gets its value), and every
//! top-level `assert` outside a program's statements (EN0415); `eval_len` gives a
//! `T[N]` length or a `RepeatLit` count; `check_statement_asserts` evaluates the
//! constant `assert`s among a program's statements once they are typed. A spread in
//! any of these is reported at its `...` before the expression is typed (S:756,
//! A:890). An expression is typed alone, as a body of its own, then evaluated; a
//! length's type may be any integer type, a literal defaulting to `usize`
//! (**choice**). Lengths written in declarations are evaluated while declarations
//! are lowered, when a class may still lack its fields and an enum its computed
//! values: see `eval_len`.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use enrang_base::{BytePos, Span, Symbol};
use enrang_diag::{Code, Diagnostic, Help};
use enrang_hir::{
    Adjust, AdtId, AdtKind, ArrayPart, BinOp, Block, Body, BodyOwner, Callee, CastKind, ConstTree,
    ConstValue, DefId, DefKind, EnumValues, Expr, ExprKind, FieldIdx, FloatTy, FormKind, LogOp,
    OptMember, Repr, Res, Stmt, StmtKind, Tcx, Ty, TyKind, TyList, UnOp, VariantIdx, VariantValue,
};
use enrang_layout::{LayoutCx, LayoutError, layout_of};
use enrang_syntax::ast;

use crate::cx::Sema;
use crate::lower::types::lower_ty;
use crate::lower::{BodyAst, ItemAst, ItemAstKind};
use crate::resolve::ScopeAt;
use crate::resolve::scope::lookup_value;
use crate::resolve::suggest::deferred_code;
use crate::typeck::{self, Deferred, Expect, FnCtxt};

/// The most values one evaluation may build, counting every node of the trees it
/// makes or copies (**choice**: the docs set no limit, and `[0; 4000000000]` must
/// fail rather than exhaust memory).
pub const MAX_VALUES: u64 = 1 << 20;

/// The longest expression text a message quotes; a longer one, or one that spans
/// lines, is `this expression` (**choice**).
const QUOTE_MAX: usize = 40;

/// What const eval keeps between roots: each constant evaluated so far with its
/// result, the first result kept; and, for the contexts that reach it from typing
/// (4F), what has been prepared, the constants being typed for an evaluation, and
/// the lengths evaluated while declarations were lowered, checked again once they
/// are complete.
#[derive(Clone, Debug, Default)]
pub struct ConstState {
    /// The names of the locals in scope where a body writes the length being
    /// evaluated, which hide constants of their names (S:756: a local is never a
    /// constant); set by typing around the lengths it lowers.
    pub(crate) shadowing: Vec<Symbol>,
    values: BTreeMap<DefId, Result<ConstTree, ConstError>>,
    /// Lay out with a cache of the evaluation's own, never the `Tcx`'s memo: while
    /// declarations are lowered a class may still lack its fields, and the memo
    /// keeps the first layout it is given.
    fresh_layouts: bool,
    /// Every constant's and static's scope and written type are in place, and every
    /// initialiser holding a spread is reported.
    prepared: bool,
    /// The constants and statics whose scope and written type are in place.
    ensured: BTreeSet<DefId>,
    /// Those whose written type is being lowered.
    ensuring: BTreeSet<DefId>,
    /// The constants typed for an evaluation, outermost first: one met again closes
    /// a cycle.
    typing: Vec<DefId>,
    /// The lengths evaluated while declarations were lowered.
    lengths: Vec<LengthSite>,
    /// The enum cases whose value is written as an expression that is no literal,
    /// not computed yet: a cast reading one, or a case after one, has no value.
    pending_cases: BTreeSet<(AdtId, VariantIdx)>,
    /// The enum cases whose computed value failed, which was reported.
    failed_cases: BTreeSet<(AdtId, VariantIdx)>,
    /// The enums whose values are computed and checked, or being so.
    checked_enums: BTreeSet<AdtId>,
    /// A layout cycle was reported while the length being evaluated was: that
    /// length is not evaluated again (one mistake, one diagnostic).
    cycle_reported: bool,
    /// The enum case whose written value is being computed: a read of it, or of a
    /// case after it, closes a cycle.
    computing: Option<(AdtId, VariantIdx)>,
}

/// A `T[N]` length or `RepeatLit` count evaluated while declarations were lowered:
/// where it resolves, its text, and the value it got (`None`: deferred).
#[derive(Clone, Debug)]
struct LengthSite {
    at: ScopeAt,
    expr: ast::Expr,
    value: Option<u64>,
}

/// Why an expression has no constant value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstError {
    /// The diagnostic to report: EN0412, or EN1032 for a call.
    Fail(Box<Diagnostic>),
    /// Nothing more to say: the expression holds an error typing already reported,
    /// or a constant it reads has no typed initialiser because its declaration
    /// failed.
    Reported,
}

impl ConstError {
    /// The diagnostic to report, if there is one.
    pub fn diagnostic(&self) -> Option<&Diagnostic> {
        match self {
            ConstError::Fail(diag) => Some(diag),
            ConstError::Reported => None,
        }
    }

    /// The error of a spread whose `...` is at `dots`, for typing to report at the
    /// token before any expected type is compared (S:756, A:890).
    pub fn spread(tcx: &Tcx, dots: Span) -> ConstError {
        fail(
            Diagnostic::new(
                Code::EN0412,
                format!(
                    "constant evaluation failed: {} is not constant",
                    quote(tcx, dots)
                ),
                dots,
                "this spread",
            )
            .note("a spread allocates at run time"),
        )
    }
}

/// Where const eval finds the typed initialiser of a constant it reads: a
/// `BodyOwner::Const` body whose root block holds the initialiser as its one
/// expression statement, as typing builds it.
pub trait ConstBodies {
    /// The body of the constant `def`, or `None` when it has none, as for a
    /// constant whose declaration failed.
    fn const_body(&mut self, def: DefId) -> Option<Arc<Body>>;
}

impl ConstBodies for BTreeMap<DefId, Arc<Body>> {
    fn const_body(&mut self, def: DefId) -> Option<Arc<Body>> {
        self.get(&def).cloned()
    }
}

/// No bodies: constants are read from `Tcx::const_value` alone.
struct NoBodies;

impl ConstBodies for NoBodies {
    fn const_body(&mut self, _def: DefId) -> Option<Arc<Body>> {
        None
    }
}

impl ConstState {
    pub fn new() -> ConstState {
        ConstState::default()
    }

    /// The value of the constant `def`: its value in `tcx` when one is stored there,
    /// else its initialiser from `bodies`, evaluated once and memoised.
    pub fn value_of(
        &mut self,
        tcx: &Tcx,
        bodies: &mut dyn ConstBodies,
        def: DefId,
    ) -> Result<ConstTree, ConstError> {
        if let Some(value) = tcx.const_value(def) {
            return Ok(value.clone());
        }
        if !self.values.contains_key(&def) {
            self.run(tcx, bodies, def);
        }
        self.values
            .get(&def)
            .cloned()
            .unwrap_or(Err(ConstError::Reported))
    }

    /// The value of `e`, an expression of `body` that must be constant: an enum
    /// value, a length, an assert's condition, an initialiser.
    pub fn eval(
        &mut self,
        tcx: &Tcx,
        bodies: &mut dyn ConstBodies,
        body: &Body,
        e: &Expr,
    ) -> Result<ConstTree, ConstError> {
        for dep in scan(tcx, body, e, self.fresh_layouts)? {
            self.value_of(tcx, bodies, dep)?;
        }
        Interp::new(tcx, self).eval(e)
    }

    /// The result kept for the constant `def`, if it was evaluated.
    pub fn result(&self, def: DefId) -> Option<&Result<ConstTree, ConstError>> {
        self.values.get(&def)
    }

    /// Evaluates `root` and every constant it needs, depth first on an explicit
    /// stack; a constant met again while it is on the stack closes a cycle.
    fn run(&mut self, tcx: &Tcx, bodies: &mut dyn ConstBodies, root: DefId) {
        let mut stack: Vec<Frame> = Vec::new();
        // The constants on the stack, for a membership test that stays cheap on a
        // long chain.
        let mut active: BTreeSet<DefId> = BTreeSet::new();
        if let Some(frame) = self.start(tcx, bodies, root) {
            active.insert(root);
            stack.push(frame);
        }
        while let Some(top) = stack.len().checked_sub(1) {
            let Some(&dep) = stack[top].deps.get(stack[top].next) else {
                let frame = stack.pop().expect("a frame");
                active.remove(&frame.def);
                let result = match initializer(&frame.body) {
                    Some(init) => Interp::new(tcx, self).eval(init),
                    None => Err(ConstError::Reported),
                };
                self.values.insert(frame.def, result);
                continue;
            };
            let failure = match self.resolved(tcx, dep) {
                Some(Ok(())) => {
                    stack[top].next += 1;
                    continue;
                }
                Some(Err(err)) => err,
                None if active.contains(&dep) => {
                    let at = stack
                        .iter()
                        .position(|frame| frame.def == dep)
                        .expect("an active constant is on the stack");
                    let members: Vec<DefId> = stack[at..].iter().map(|f| f.def).collect();
                    cycle(tcx, &members)
                }
                None => {
                    if let Some(frame) = self.start(tcx, bodies, dep) {
                        active.insert(dep);
                        stack.push(frame);
                    }
                    continue;
                }
            };
            let frame = stack.pop().expect("a frame");
            active.remove(&frame.def);
            self.values.insert(frame.def, Err(failure));
        }
    }

    /// Checks the shape of `def`'s initialiser: its frame, with the constants it
    /// reads, or `None` once why it has no value is recorded.
    fn start(&mut self, tcx: &Tcx, bodies: &mut dyn ConstBodies, def: DefId) -> Option<Frame> {
        let Some(body) = bodies.const_body(def) else {
            self.values.insert(def, Err(ConstError::Reported));
            return None;
        };
        let scanned = match initializer(&body) {
            Some(init) => scan(tcx, &body, init, self.fresh_layouts),
            None => Err(ConstError::Reported),
        };
        match scanned {
            Ok(deps) => Some(Frame {
                def,
                body,
                deps,
                next: 0,
            }),
            Err(err) => {
                self.values.insert(def, Err(err));
                None
            }
        }
    }

    /// Whether `def` already has a result: `Ok` for a value, the error otherwise.
    fn resolved(&self, tcx: &Tcx, def: DefId) -> Option<Result<(), ConstError>> {
        if tcx.const_value(def).is_some() {
            return Some(Ok(()));
        }
        self.values
            .get(&def)
            .map(|result| result.as_ref().map(|_| ()).map_err(Clone::clone))
    }

    /// A constant's value for a read, once `run` or `eval` has evaluated it.
    fn read(&self, tcx: &Tcx, def: DefId) -> Result<ConstTree, ConstError> {
        if let Some(value) = tcx.const_value(def) {
            return Ok(value.clone());
        }
        self.values
            .get(&def)
            .cloned()
            .unwrap_or(Err(ConstError::Reported))
    }
}

/// A constant being evaluated: its body, the constants its initialiser reads in
/// evaluation order, and how many of them have a value.
struct Frame {
    def: DefId,
    body: Arc<Body>,
    deps: Vec<DefId>,
    next: usize,
}

/// The initialiser of a `BodyOwner::Const` body: its one expression statement.
fn initializer(body: &Body) -> Option<&Expr> {
    match body.root.stmts.as_slice() {
        [
            Stmt {
                kind: StmtKind::Expr(init),
                ..
            },
        ] => Some(init),
        _ => None,
    }
}

/// The value of `e` in `body`, other constants read from `tcx` alone (plan h.2's
/// seam).
#[allow(dead_code)] // A seam of plan h.2; the contexts below share `ConstState`.
pub(crate) fn eval(tcx: &Tcx, body: &Body, e: &Expr) -> Result<ConstTree, ConstError> {
    ConstState::new().eval(tcx, &mut NoBodies, body, e)
}

// ---------------------------------------------------------------------------------
// Contexts (4F): the places typing hands const eval an expression.

/// Evaluates every constant item of the user's modules, in declaration order (plan
/// d.1 step 5): first each enum's computed case values (S:591), with `@repr`'s fit
/// (S:1288), another enum's computed values that one reads computed first; then
/// each `const` initialiser, whose value `Tcx` keeps (`set_const`), a constant
/// whose type holds heap memory or a destructor being EN0412 (S:756); each `unsafe
/// let` initialiser (S:1351); and each top-level `assert` outside a program's
/// statements, EN0415 when it is `false` (A:918). Every body typed here waits in
/// `Sema::early_consts` for its own turn's passes. Last, the lengths evaluated
/// while declarations were lowered are evaluated again with every declaration
/// complete.
pub(crate) fn check_items(sema: &mut Sema) {
    prepare(sema);
    let items: Vec<ItemAst> = sema
        .decls
        .items
        .iter()
        .filter(|item| !sema.program.modules[sema.res.index(item.module)].library)
        .cloned()
        .collect();
    for item in &items {
        if let ItemAstKind::Enum(adt, decl, _) = &item.kind {
            pend_cases(sema, *adt, decl);
        }
    }
    for item in &items {
        if let ItemAstKind::Enum(adt, _, _) = &item.kind {
            ensure_enum(sema, *adt);
        }
    }
    let messages = assert_messages(sema);
    for item in &items {
        match &item.kind {
            ItemAstKind::Const(_) => constant(sema, item.def),
            ItemAstKind::Static(u) if u.value.is_some() => static_value(sema, item.def),
            ItemAstKind::StaticAssert => {
                let message = messages.get(&item.def).cloned().flatten();
                static_assert(sema, item.def, message);
            }
            _ => {}
        }
    }
    recheck_lengths(sema);
}

/// A fixed array's length or a repeat literal's count (SPEC 4.1 `T[N]`,
/// `RepeatLit`, both `ConstExpr`s, S:756): an integer literal that fits `usize` is
/// its own value; anything else is typed alone at `at` with `usize` as a hint, so a
/// literal is a `usize` and a constant keeps its own integer type, then evaluated.
/// `None` only after reporting why, so `lower` can return `Error` without a
/// diagnostic of its own; the report may come once declarations are complete
/// (`check_items`).
///
/// A spread is EN0412 at its `...` before anything is typed (S:756, A:890); `this`,
/// and inside a body a name that is no constant (a local), EN0412; a value that is
/// no integer EN0401; a negative one EN0412. A length above `isize.MAX` is left to
/// phase 4 (EN0435, S:1628). Inside a body, names resolve at the body's item scope,
/// and a name typing marks as a local in scope there (`ConstState::shadowing`) is
/// EN0412 `is a local variable` even when a constant has its name.
///
/// While declarations are lowered, a class may still lack its fields, a function
/// its signature and an enum its computed values. Then a length is evaluated only
/// when it and every constant it reads are built from literals, constants,
/// operators, `as`, the size forms (laid out with a cache of their own, never the
/// `Tcx`'s memo) and payload-free cases of enums, and kept to be evaluated again in
/// `check_items`; any other length is evaluated only there, and a length whose
/// value there differs from the one its type was given, or that had none, is
/// EN0412 `is not known where this type is written` (**choice**).
pub(crate) fn eval_len(sema: &mut Sema, at: ScopeAt, e: &ast::Expr) -> Option<u64> {
    // The locals this length's body has in scope: they hide constants here only,
    // never in what evaluating the length types.
    let shadowing = std::mem::take(&mut sema.consts.shadowing);
    let value = eval_len_in(sema, at, e, &shadowing);
    sema.consts.shadowing = shadowing;
    value
}

fn eval_len_in(sema: &mut Sema, at: ScopeAt, e: &ast::Expr, shadowing: &[Symbol]) -> Option<u64> {
    if let Some(n) = literal_len(sema, e) {
        return Some(n);
    }
    prepare(sema);
    if let Some(dots) = first_spread(e) {
        report(sema, ConstError::spread(sema.tcx, dots));
        return None;
    }
    if let Some(diag) = runtime_part(sema, at, e, shadowing) {
        sema.emit(diag);
        return None;
    }
    if sema.decls.lowered {
        return length_value(sema, at, e, false);
    }
    let value = if simple(sema, at, e, &mut BTreeSet::new()) {
        length_value(sema, at, e, true)
    } else {
        None
    };
    if std::mem::take(&mut sema.consts.cycle_reported) {
        // Reported as a cycle: the type holds `Error`, nothing more to check.
        return None;
    }
    sema.consts.lengths.push(LengthSite {
        at,
        expr: e.clone(),
        value,
    });
    value
}

/// The value of a length written as an integer literal, in parentheses or not,
/// that fits `usize`: the literal itself, with nothing to type. Any other length,
/// and a literal too large (EN0411 from typing), goes the long way.
fn literal_len(sema: &Sema, e: &ast::Expr) -> Option<u64> {
    match &e.kind {
        ast::ExprKind::Paren(inner) => literal_len(sema, inner),
        ast::ExprKind::Int { value, .. } => u64::try_from(*value)
            .ok()
            .filter(|&n| n <= sema.tcx.target().layout.usize_max()),
        _ => None,
    }
}

/// The top-level `assert`s among a program's statements whose condition is
/// constant: EN0415 when it is `false` (S:756, A:918); one whose condition is not
/// constant is checked at run time, and so is one that compares by calling
/// `equals`. Run once the statements are typed (`entry::check`).
pub(crate) fn check_statement_asserts(sema: &mut Sema) {
    let Some(body) = sema.statements.clone() else {
        return;
    };
    for stmt in &body.root.stmts {
        let StmtKind::Expr(Expr {
            kind:
                ExprKind::Call {
                    callee: Callee::Form(FormKind::Assert),
                    args,
                    ..
                },
            ..
        }) = &stmt.kind
        else {
            continue;
        };
        let Some(cond) = args.first() else {
            continue;
        };
        if sema.tcx.references_error(cond.ty) || scan(sema.tcx, &body, cond, false).is_err() {
            continue;
        }
        let message = match args.get(1).map(|m| &m.kind) {
            Some(ExprKind::Const(ConstValue::Str(id))) => Some(sema.tcx.str(*id).to_string()),
            _ => None,
        };
        match eval_in(sema, &body, cond, false) {
            Ok(ConstTree::Scalar(ConstValue::Bool(false))) => {
                sema.emit(assert_failed(cond.span, message.as_deref()));
            }
            Err(ConstError::Fail(diag)) if diag.code == Code::EN0412 => sema.emit(*diag),
            _ => {}
        }
    }
}

/// Reports what `err` holds.
fn report(sema: &mut Sema, err: ConstError) {
    if let ConstError::Fail(diag) = err {
        sema.emit(*diag);
    }
}

/// Once per run, before the first evaluation: every initialiser holding a spread
/// reported at its `...`, before anything compares it with an expected type (S:756,
/// A:890).
/// Such an initialiser is never typed: its body is left empty, which gives no value
/// and nothing more to report.
fn prepare(sema: &mut Sema) {
    if sema.consts.prepared {
        return;
    }
    sema.consts.prepared = true;
    // A constant's or static's scope and written type are put in place when a
    // length reads it (`simple_def`), never all at once: lowering every written
    // type here, while a class's fields are lowered, would lay out classes not
    // complete yet (fix-6).
    let items = sema.decls.items.clone();
    for item in &items {
        let init = match &item.kind {
            ItemAstKind::Const(c) => Some(&c.value),
            ItemAstKind::Static(u) => u.value.as_ref(),
            ItemAstKind::StaticAssert => match sema.decls.body_ast(BodyOwner::Const(item.def)) {
                Some(BodyAst::Const(cond)) => Some(cond),
                _ => None,
            },
            _ => None,
        };
        let Some(dots) = init.and_then(first_spread) else {
            continue;
        };
        report(sema, ConstError::spread(sema.tcx, dots));
        if !sema.bodies.contains_key(&item.def) && !sema.early_consts.contains_key(&item.def) {
            let error = sema.tcx.common().error;
            let ret = sema.tcx.item_ty(item.def).unwrap_or(error);
            let span = sema.tcx.def(item.def).span;
            let empty = Body::empty(BodyOwner::Const(item.def), ret, span);
            sema.early_consts.insert(item.def, empty);
        }
    }
}

/// The scope and written type of constant or static `item`, put in place while
/// declarations are lowered (`lower::consts_decl` repeats both later, to the same
/// effect). A constant's type written with a length that reads the constant itself
/// is left to that length's own report.
fn ensure_item(sema: &mut Sema, item: &ItemAst) {
    if sema.decls.lowered || sema.consts.ensured.contains(&item.def) {
        return;
    }
    sema.consts.ensured.insert(item.def);
    let at = ScopeAt {
        owner: Some(item.def),
        ..ScopeAt::module(item.module, item.test_part)
    };
    sema.decls.scopes.entry(item.def).or_insert(at);
    if sema.tcx.item_ty(item.def).is_some() {
        return;
    }
    let written = match &item.kind {
        ItemAstKind::Const(c) => c.ty.as_ref(),
        ItemAstKind::Static(u) => Some(&u.ty),
        _ => None,
    };
    if let Some(t) = written {
        sema.consts.ensuring.insert(item.def);
        let ty = lower_ty(sema, at, t);
        sema.consts.ensuring.remove(&item.def);
        sema.tcx.set_item_ty(item.def, ty);
    }
}

/// The collected declaration of `def`.
fn item_of<'a>(sema: &Sema<'a>, def: DefId) -> Option<ItemAst<'a>> {
    sema.decls
        .items
        .iter()
        .find(|item| item.def == def)
        .cloned()
}

/// Whether `e`, read while declarations are lowered, is built only from literals,
/// constants and statics, operators, `as`, the size forms and the constants of the
/// primitive types, through every constant it reads, so typing it needs no field,
/// signature or computed enum value. Puts each constant and static it reads in
/// place first.
fn simple(sema: &mut Sema, at: ScopeAt, e: &ast::Expr, visiting: &mut BTreeSet<DefId>) -> bool {
    match &e.kind {
        ast::ExprKind::Int { .. }
        | ast::ExprKind::Float(_)
        | ast::ExprKind::Str(_)
        | ast::ExprKind::RawTemplate(_)
        | ast::ExprKind::Bool(_)
        | ast::ExprKind::Null
        | ast::ExprKind::SizeForm(_) => true,
        ast::ExprKind::Paren(x) | ast::ExprKind::Unary(_, x) | ast::ExprKind::Cast(x, _) => {
            simple(sema, at, x, visiting)
        }
        ast::ExprKind::Binary(_, a, b) | ast::ExprKind::Logical(_, a, b) => {
            simple(sema, at, a, visiting) && simple(sema, at, b, visiting)
        }
        ast::ExprKind::Ternary(c, a, b) => {
            simple(sema, at, c, visiting)
                && simple(sema, at, a, visiting)
                && simple(sema, at, b, visiting)
        }
        ast::ExprKind::Member {
            base,
            name: member,
            optional: false,
        } => match &base.kind {
            ast::ExprKind::Ident(name) => {
                match lookup_value(
                    sema,
                    at,
                    ast::Ident {
                        name: *name,
                        span: base.span,
                    },
                ) {
                    Res::PrimType(_) => true,
                    // A constant of a namespace, as a name is (S:801).
                    Res::Namespace(m) => {
                        let index = sema.res.index(m);
                        match crate::resolve::scope::public_member(sema, index, member.name) {
                            Some(Res::Def(def)) => simple_def(sema, at, def, visiting),
                            _ => false,
                        }
                    }
                    Res::Def(def) => simple_case(sema, def, member.name, visiting),
                    _ => false,
                }
            }
            _ => false,
        },
        ast::ExprKind::Ident(name) => {
            let res = lookup_value(
                sema,
                at,
                ast::Ident {
                    name: *name,
                    span: e.span,
                },
            );
            match res {
                Res::Def(def) => simple_def(sema, at, def, visiting),
                Res::Fns(_) => false,
                _ => true,
            }
        }
        _ => false,
    }
}

/// [`simple`] for a name that resolved to `def`: a constant whose initialiser is
/// simple, or a static whose type is in place.
fn simple_def(sema: &mut Sema, at: ScopeAt, def: DefId, visiting: &mut BTreeSet<DefId>) -> bool {
    let Some(item) = item_of(sema, def) else {
        return true;
    };
    match &item.kind {
        ItemAstKind::Const(c) => {
            ensure_item(sema, &item);
            if sema.consts.ensuring.contains(&def) {
                return false;
            }
            if !visiting.insert(def) {
                return true;
            }
            let scope = sema.decls.scopes.get(&def).copied().unwrap_or(at);
            simple(sema, scope, &c.value, visiting)
        }
        ItemAstKind::Static(_) => {
            ensure_item(sema, &item);
            !sema.consts.ensuring.contains(&def)
        }
        _ => true,
    }
}

/// [`simple`] for `E.name`, `def` the type `E` names: a payload-free case of an
/// enum whose cases are named already (its header). A case whose value is
/// computed (`A = K`) is simple when every computed value of its enum is; those
/// are computed now, in source order, as before any value that reads them.
fn simple_case(sema: &mut Sema, def: DefId, name: Symbol, visiting: &mut BTreeSet<DefId>) -> bool {
    let Some(adt) = sema.tcx.adt_of(def) else {
        return false;
    };
    let Some(en) = sema.tcx.adt(adt).as_enum() else {
        return false;
    };
    let Some((_, case)) = en.variant_named(name) else {
        return false;
    };
    if !case.fields.is_empty() {
        return false;
    }
    if case.value.is_some()
        || en.values == EnumValues::Texts
        || sema.consts.checked_enums.contains(&adt)
    {
        return true;
    }
    let enum_def = sema.tcx.adt(adt).def;
    if !visiting.insert(enum_def) {
        return false;
    }
    let written: Vec<ast::Expr> = sema
        .decls
        .items
        .iter()
        .find_map(|item| match &item.kind {
            ItemAstKind::Enum(a, decl, _) if *a == adt => Some(
                decl.variants
                    .iter()
                    .filter_map(|v| match &v.payload {
                        ast::VariantPayload::Value(e) => Some(e.clone()),
                        _ => None,
                    })
                    .collect(),
            ),
            _ => None,
        })
        .unwrap_or_default();
    let Some(scope) = sema.decls.scopes.get(&enum_def).copied() else {
        return false;
    };
    // Computed values are stored once: none may read a layout, which may still be
    // incomplete here, unlike a length's own value, evaluated again later.
    if !written.iter().all(|e| simple(sema, scope, e, visiting)) {
        return false;
    }
    if written
        .iter()
        .any(|e| reads_layout(sema, scope, e, &mut BTreeSet::new()))
    {
        return false;
    }
    ensure_enum(sema, adt);
    true
}

/// Whether `e`, or a constant it reads, holds `sizeOf`, `alignOf` or `offsetOf`.
fn reads_layout(sema: &Sema, at: ScopeAt, e: &ast::Expr, visiting: &mut BTreeSet<DefId>) -> bool {
    let mut found = false;
    let mut consts = Vec::new();
    each_expr(e, &mut |x| match &x.kind {
        ast::ExprKind::SizeForm(_) => found = true,
        ast::ExprKind::Ident(name) => {
            let ident = ast::Ident {
                name: *name,
                span: x.span,
            };
            if let Res::Def(def) = lookup_value(sema, at, ident) {
                consts.push(def);
            }
        }
        _ => {}
    });
    if found {
        return true;
    }
    for def in consts {
        if !visiting.insert(def) {
            continue;
        }
        let Some(item) = item_of(sema, def) else {
            continue;
        };
        if let ItemAstKind::Const(c) = &item.kind {
            let scope = sema.decls.scopes.get(&def).copied().unwrap_or(at);
            if reads_layout(sema, scope, &c.value, visiting) {
                return true;
            }
        }
    }
    false
}

/// The value of a length typed and evaluated now: `fresh` while declarations are
/// lowered.
fn length_value(sema: &mut Sema, at: ScopeAt, e: &ast::Expr, fresh: bool) -> Option<u64> {
    let usize_ty = sema.tcx.common().usize;
    let pushed = push_owner(sema, at);
    let body = type_alone(sema, at, e, Some(usize_ty));
    let result = match initializer(&body) {
        Some(value) if !sema.tcx.references_error(value.ty) => {
            Some(eval_in(sema, &body, value, fresh))
        }
        _ => None,
    };
    if pushed {
        sema.consts.typing.pop();
    }
    let value = initializer(&body)?;
    match result? {
        Ok(ConstTree::Scalar(int @ ConstValue::Int(..))) => match int.as_i128(sema.tcx) {
            Some(n) if n >= 0 => u64::try_from(n).ok(),
            Some(n) => {
                sema.err(
                    Code::EN0412,
                    format!(
                        "constant evaluation failed: {} is negative",
                        quote(sema.tcx, value.span)
                    ),
                    value.span,
                    format!("this is {n}, and a length can't be negative"),
                );
                None
            }
            None => {
                not_usize(sema, value);
                None
            }
        },
        Ok(_) => {
            not_usize(sema, value);
            None
        }
        Err(err) => {
            report(sema, err);
            None
        }
    }
}

/// EN0401 for a length whose type is no integer.
fn not_usize(sema: &mut Sema, value: &Expr) {
    let shown = sema.tcx.ty_string(value.ty);
    sema.err(
        Code::EN0401,
        format!("mismatched types: expected `usize`, found `{shown}`"),
        value.span,
        format!("this is `{shown}`"),
    );
}

/// Pushes `at`'s constant, static or assert on the stack of the constants being
/// typed for an evaluation, when it is not on it: a length inside its initialiser
/// that reads it back closes a cycle.
fn push_owner(sema: &mut Sema, at: ScopeAt) -> bool {
    let Some(def) = at.owner else {
        return false;
    };
    let kind = sema.tcx.def(def).kind;
    if !matches!(
        kind,
        DefKind::Const | DefKind::Static | DefKind::StaticAssert
    ) || sema.consts.typing.contains(&def)
    {
        return false;
    }
    sema.consts.typing.push(def);
    true
}

/// The lengths evaluated while declarations were lowered, evaluated again now that
/// they are complete: one that was deferred, or whose value changes, is EN0412 at
/// the length, which the type already holds; one deferred and failing now with no
/// error reported anywhere is EN0412 too, so no length leaves phase 2 unexplained.
fn recheck_lengths(sema: &mut Sema) {
    let sites = std::mem::take(&mut sema.consts.lengths);
    let mut seen = BTreeSet::new();
    for site in sites {
        if !seen.insert((site.expr.span.lo, site.expr.span.hi)) {
            continue;
        }
        let now = length_value(sema, site.at, &site.expr, false);
        let unknown = match (site.value, now) {
            (Some(then), Some(now)) => then != now,
            (None, Some(_)) => true,
            (Some(_), None) => false,
            (None, None) => !sema.dcx.has_errors(),
        };
        if unknown {
            let span = site.expr.span;
            sema.emit(
                Diagnostic::new(
                    Code::EN0412,
                    format!(
                        "constant evaluation failed: {} is not known where this type is written",
                        quote(sema.tcx, span)
                    ),
                    span,
                    "a declaration's types are sized before the declarations this reads are complete",
                )
                .with_help(Help::text(
                    "write it with literals, constants, operators, `as` and `sizeOf` of types declared above",
                )),
            );
        }
    }
}

/// Types `e` alone at `at`, as a body of its own whose root holds it as its one
/// expression statement (the shape `initializer` reads), `hint` guiding a literal;
/// inference ends as at the end of any body (`typeck`'s `finish`, whose deferred
/// checks it runs; a call's bounds are left out, a call being EN1032 here anyway).
fn type_alone(sema: &mut Sema, at: ScopeAt, e: &ast::Expr, hint: Option<Ty>) -> Body {
    let common = *sema.tcx.common();
    let owner = match at.owner.or(sema.tcx.module(at.module).def) {
        Some(def) => BodyOwner::Const(def),
        None => BodyOwner::Statements(at.module),
    };
    let mut fcx = FnCtxt::new(sema, owner, at, hint.unwrap_or(common.void));
    fcx.scopes.push();
    let expect = match hint {
        Some(ty) => Expect::Has(ty),
        None => Expect::None,
    };
    let value = fcx.check_expr(e, expect);
    let root = Block {
        stmts: vec![Stmt {
            span: e.span,
            kind: StmtKind::Expr(value),
        }],
        span: e.span,
    };
    fcx.apply_defaults();
    fcx.check_int_divisions();
    for deferred in std::mem::take(&mut fcx.deferred) {
        match deferred {
            Deferred::LiteralFit {
                expr,
                span,
                ty,
                literal,
            } => fcx.check_literal_fit(expr, span, ty, &literal),
            Deferred::SpreadClone { span, elem } => fcx.check_spread_clone(span, elem),
            Deferred::NumUse { span, ty, need } => fcx.check_num_use(span, ty, need),
            Deferred::Cast {
                span,
                value,
                from,
                to,
            } => fcx.check_deferred_cast(span, value, from, to),
            _ => {}
        }
    }
    let mut body = Body {
        owner: fcx.owner,
        params: std::mem::take(&mut fcx.params),
        locals: std::mem::take(&mut fcx.locals),
        root,
        arrows: std::mem::take(&mut fcx.arrows),
        ret: fcx.ret.ty,
        param_defaults: std::mem::take(&mut fcx.param_defaults),
        facts: std::mem::take(&mut fcx.facts),
        records: std::mem::take(&mut fcx.records),
        expr_count: fcx.next_expr,
        span: e.span,
    };
    fcx.resolve_body(&mut body);
    body
}

/// The value of `e` of `body`: its shape, then the constants it reads typed and
/// evaluated, then its own value; `fresh` while declarations are lowered, with a
/// state of its own whose layouts skip the `Tcx`'s memo.
fn eval_in(sema: &mut Sema, body: &Body, e: &Expr, fresh: bool) -> Result<ConstTree, ConstError> {
    let deps = scan(sema.tcx, body, e, fresh)?;
    let mut bodies = typed_closure(sema, &deps, fresh)?;
    if fresh {
        // While declarations are lowered, every class a size form lays out gets its
        // fields first, whatever the order of the declarations; one whose fields are
        // being lowered closes a cycle through its own layout (S:756).
        let mut types = Vec::new();
        size_form_types(e, &mut types);
        for b in bodies.values() {
            crate::passes::walk::for_each_expr(b, &mut |x| size_form_types(x, &mut types));
        }
        for ty in types {
            if let Err(adt) = crate::lower::adts::ensure_fields(sema, ty) {
                sema.consts.cycle_reported = true;
                let class = sema.tcx.adt(adt).def;
                let err = match deps.first() {
                    Some(&c) => cycle(sema.tcx, &[c, class]),
                    None => fail(Diagnostic::new(
                        Code::EN0412,
                        format!(
                            "constant cycle: the layout of `{}` uses its own size",
                            sema.tcx.adt(adt).name
                        ),
                        e.span,
                        "this needs the layout of the class it is written in",
                    )),
                };
                return Err(err);
            }
        }
    }
    if !fresh && !sema.consts.pending_cases.is_empty() {
        // The enums whose computed values this reads through `as`, by source
        // position, computed first.
        let mut enums = Vec::new();
        enums_read(sema.tcx, e, &mut enums);
        for body in bodies.values() {
            if let Some(init) = initializer(body) {
                enums_read(sema.tcx, init, &mut enums);
            }
        }
        enums.sort_by_key(|&adt| sema.tcx.def(sema.tcx.adt(adt).def).name_span);
        enums.dedup();
        for adt in enums {
            ensure_enum(sema, adt);
        }
    }
    if fresh {
        let mut state = ConstState {
            fresh_layouts: true,
            ..ConstState::default()
        };
        state.eval(sema.tcx, &mut bodies, body, e)
    } else {
        sema.consts.eval(sema.tcx, &mut bodies, body, e)
    }
}

/// The types the size forms directly in `e` lay out.
fn size_form_types(e: &Expr, out: &mut Vec<Ty>) {
    if let ExprKind::Call {
        callee: Callee::Form(form),
        ..
    } = &e.kind
        && let Some((ty, _)) = size_form(*form)
    {
        out.push(ty);
    }
    match &e.kind {
        ExprKind::Unary(_, a) | ExprKind::Cast(a, _) | ExprKind::Borrow(a) => {
            size_form_types(a, out)
        }
        ExprKind::Binary(_, a, b) | ExprKind::Logical(_, a, b) => {
            size_form_types(a, out);
            size_form_types(b, out);
        }
        ExprKind::Repeat(a, _) => size_form_types(a, out),
        ExprKind::ArrayLit(items) | ExprKind::TupleLit(items) => {
            items.iter().for_each(|x| size_form_types(x, out))
        }
        _ => {}
    }
}

/// Each enum whose discriminant `e` reads, a payload-free case converted with `as`,
/// through the parts a constant expression may have.
fn enums_read(tcx: &Tcx, e: &Expr, out: &mut Vec<AdtId>) {
    match &e.kind {
        ExprKind::Cast(a, kind) => {
            if *kind == CastKind::EnumToInt
                && let TyKind::Adt(adt, _) = tcx.kind(peel_nullable(tcx, a.ty))
            {
                out.push(adt);
            }
            enums_read(tcx, a, out);
        }
        ExprKind::Unary(_, a) | ExprKind::Borrow(a) | ExprKind::Repeat(a, _) => {
            enums_read(tcx, a, out)
        }
        ExprKind::Binary(_, a, b) | ExprKind::Logical(_, a, b) => {
            enums_read(tcx, a, out);
            enums_read(tcx, b, out);
        }
        ExprKind::ArrayLit(items)
        | ExprKind::TupleLit(items)
        | ExprKind::ObjectLit { fields: items, .. }
        | ExprKind::VariantLit { fields: items, .. } => {
            for item in items {
                enums_read(tcx, item, out);
            }
        }
        ExprKind::NewNamed { fields, .. } => {
            for (_, value) in fields {
                enums_read(tcx, value, out);
            }
        }
        _ => {}
    }
}

/// The typed initialisers of `roots` and of every constant they read, through one
/// another, each typed now when its turn has not come (kept for that turn in
/// `Sema::early_consts`). A constant with a value already needs no body.
fn typed_closure(
    sema: &mut Sema,
    roots: &[DefId],
    fresh: bool,
) -> Result<BTreeMap<DefId, Arc<Body>>, ConstError> {
    let mut bodies = BTreeMap::new();
    let mut work: Vec<DefId> = roots.iter().rev().copied().collect();
    let mut seen = BTreeSet::new();
    while let Some(def) = work.pop() {
        if !seen.insert(def)
            || sema.tcx.def(def).kind != DefKind::Const
            || sema.tcx.const_value(def).is_some()
            || (!fresh && sema.consts.values.contains_key(&def))
        {
            continue;
        }
        let Some(body) = find_body(sema, def)? else {
            continue;
        };
        if let Some(init) = initializer(&body)
            && let Ok(deps) = scan(sema.tcx, &body, init, fresh)
        {
            work.extend(deps.into_iter().rev());
        }
        bodies.insert(def, body);
    }
    Ok(bodies)
}

/// The typed body of constant, static or assert `def`: the finished one, the one
/// typed before its turn, or one typed now. A constant met again while it is being
/// typed for an evaluation closes a cycle (EN0412); one typing is reading back
/// already reports its own cycle (`typeck::const_ty`).
fn find_body(sema: &mut Sema, def: DefId) -> Result<Option<Arc<Body>>, ConstError> {
    if let Some(body) = sema.bodies.get(&def) {
        return Ok(Some(Arc::clone(body)));
    }
    if let Some(body) = sema.early_consts.get(&def) {
        return Ok(Some(Arc::new(body.clone())));
    }
    if sema.decls.body_ast(BodyOwner::Const(def)).is_none() || sema.typing_consts.contains(&def) {
        return Ok(None);
    }
    if let Some(start) = sema.consts.typing.iter().position(|&d| d == def) {
        return Err(cycle(sema.tcx, &sema.consts.typing[start..]));
    }
    sema.consts.typing.push(def);
    let body = typeck::check_body(sema, BodyOwner::Const(def));
    sema.consts.typing.pop();
    sema.early_consts.insert(def, body.clone());
    Ok(Some(Arc::new(body)))
}

/// A constant item: its value, kept in `Tcx`; a type that holds heap memory or a
/// destructor is EN0412 (S:756: "`T` has no destructor and no heap; string
/// literals are allowed only as `&string`").
fn constant(sema: &mut Sema, def: DefId) {
    let mut bodies = match typed_closure(sema, &[def], false) {
        Ok(bodies) => bodies,
        Err(err) => return report(sema, err),
    };
    let result = sema.consts.value_of(sema.tcx, &mut bodies, def);
    match result {
        Ok(tree) => match held_part(sema.tcx, sema.tcx.item_ty(def), &mut BTreeSet::new()) {
            Some((part, why)) => {
                let shown = sema.tcx.ty_string(part);
                let mut diag = Diagnostic::new(
                    Code::EN0412,
                    format!(
                        "constant evaluation failed: a constant can't hold {}",
                        crate::classes::sig::a_ty(&shown)
                    ),
                    sema.tcx.def(def).name_span,
                    format!("`{shown}` {why}"),
                );
                if sema.tcx.kind(part) == TyKind::Str {
                    diag = diag.with_help(Help::text(
                        "a string literal is a constant as a `&string`: write the type `&string`",
                    ));
                }
                sema.emit(diag);
            }
            None => sema.tcx.set_const(def, tree),
        },
        Err(err) => report(sema, err),
    }
}

/// The first part of `ty` a constant may not hold: heap memory or a destructor.
/// What a reference points at is not part of the constant.
fn held_part(
    tcx: &Tcx,
    ty: Option<Ty>,
    visiting: &mut BTreeSet<AdtId>,
) -> Option<(Ty, &'static str)> {
    let ty = ty?;
    match tcx.kind(ty) {
        TyKind::Str | TyKind::Array(_) | TyKind::Boxed(_) => Some((ty, "owns heap memory")),
        TyKind::Fixed(inner, _) | TyKind::Nullable(inner) => held_part(tcx, Some(inner), visiting),
        TyKind::Tuple(parts) => tcx
            .list(parts)
            .iter()
            .find_map(|&part| held_part(tcx, Some(part), visiting)),
        TyKind::Object(shape) => tcx
            .shape(shape)
            .fields
            .iter()
            .find_map(|&(_, field)| held_part(tcx, Some(field), visiting)),
        TyKind::Adt(adt, args) => {
            if !visiting.insert(adt) {
                return None;
            }
            if tcx.adt(adt).as_class().is_some() && tcx.class_dtor(adt, args).is_some() {
                return Some((ty, "has a destructor"));
            }
            if tcx.adt(adt).as_class().is_none() && tcx.adt(adt).as_enum().is_none() {
                return None;
            }
            tcx.adt_field_tys(adt, args)
                .into_iter()
                .find_map(|field| held_part(tcx, Some(field), visiting))
        }
        _ => None,
    }
}

/// An `unsafe let` initialiser: a constant expression with no call (S:758,
/// S:1351); its value is kept in `Tcx`.
fn static_value(sema: &mut Sema, def: DefId) {
    let body = match find_body(sema, def) {
        Ok(Some(body)) => body,
        Ok(None) => return,
        Err(err) => return report(sema, err),
    };
    let Some(init) = initializer(&body) else {
        return;
    };
    match eval_in(sema, &body, init, false) {
        Ok(tree) => sema.tcx.set_const(def, tree),
        Err(err) => report(sema, err),
    }
}

/// A top-level `assert` outside a program's statements: EN0415 when its condition
/// is `false`, with its message (S:756, A:918).
fn static_assert(sema: &mut Sema, def: DefId, message: Option<String>) {
    let body = match find_body(sema, def) {
        Ok(Some(body)) => body,
        Ok(None) => return,
        Err(err) => return report(sema, err),
    };
    let Some(cond) = initializer(&body) else {
        return;
    };
    match eval_in(sema, &body, cond, false) {
        Ok(ConstTree::Scalar(ConstValue::Bool(false))) => {
            sema.emit(assert_failed(cond.span, message.as_deref()));
        }
        Ok(_) => {}
        Err(err) => report(sema, err),
    }
}

/// EN0415 at `cond` (**choice** of wording: the code's title, then the message).
fn assert_failed(cond: Span, message: Option<&str>) -> Diagnostic {
    let head = match message {
        Some(message) => format!("compile-time assert failed: {message}"),
        None => "compile-time assert failed".to_owned(),
    };
    Diagnostic::new(Code::EN0415, head, cond, "this is `false`")
}

/// The message of each top-level `assert` item, by its definition.
fn assert_messages(sema: &Sema) -> BTreeMap<DefId, Option<String>> {
    fn walk(sema: &Sema, items: &[ast::Item], out: &mut BTreeMap<DefId, Option<String>>) {
        for item in items {
            match &item.kind {
                ast::ItemKind::StaticAssert { message, .. } => {
                    if let Some(&def) = sema.res.item_defs.get(&item.id) {
                        out.insert(def, message.as_ref().map(|m| m.value.as_str().to_owned()));
                    }
                }
                ast::ItemKind::Describe(d) => walk(sema, &d.items, out),
                _ => {}
            }
        }
    }
    let mut out = BTreeMap::new();
    for module in &sema.program.modules {
        walk(sema, &module.ast.items, &mut out);
        if let Some(part) = &module.test_part {
            walk(sema, &part.ast.items, &mut out);
        }
    }
    out
}

/// Records the cases of enum `adt` whose value is written as an expression that is
/// no literal, which lowering left without a value, as pending.
fn pend_cases(sema: &mut Sema, adt: AdtId, decl: &ast::EnumDecl) {
    let Some(en) = sema.tcx.adt(adt).as_enum() else {
        return;
    };
    if en.values == EnumValues::Texts || en.str_union {
        return;
    }
    for (index, written) in decl.variants.iter().enumerate() {
        if matches!(written.payload, ast::VariantPayload::Value(_))
            && en.variants.get(index).is_some_and(|v| v.value.is_none())
        {
            sema.consts
                .pending_cases
                .insert((adt, VariantIdx(index as u32)));
        }
    }
}

/// Computes the case values of enum `adt` and checks their fit, once: at its turn,
/// or earlier, before a value that reads one of them through `as` is evaluated.
fn ensure_enum(sema: &mut Sema, adt: AdtId) {
    if sema.consts.checked_enums.contains(&adt) {
        return;
    }
    let found = sema.decls.items.iter().find_map(|item| match &item.kind {
        ItemAstKind::Enum(a, decl, _) if *a == adt => Some((item.clone(), *decl)),
        _ => None,
    });
    if let Some((item, decl)) = found {
        enum_values(sema, &item, adt, decl);
    }
}

/// An enum's case values (S:591): each one written as an expression that is no
/// literal is typed alone, at its `@repr`'s integer type as a hint, and evaluated;
/// a value of no integer type is EN0401. Under `@repr("u8"|"u16"|"u32")` every
/// value, written or following the one before, must fit, else EN0412 (S:1288).
/// Text enums have no numbers to check. Each computed value is stored as soon as
/// it is known, so a later case may read it; one that fails is recorded so, and a
/// read of it, or of a case after it, has no value and nothing more to report.
fn enum_values(sema: &mut Sema, item: &ItemAst, adt: AdtId, decl: &ast::EnumDecl) {
    sema.consts.checked_enums.insert(adt);
    let Some(en) = sema.tcx.adt(adt).as_enum().cloned() else {
        return;
    };
    if en.values == EnumValues::Texts || en.str_union {
        return;
    }
    let repr = match en.repr {
        Some(Repr::U8) => Some((sema.tcx.common().u8, 8, "u8")),
        Some(Repr::U16) => Some((sema.tcx.common().u16, 16, "u16")),
        Some(Repr::U32) => Some((sema.tcx.common().u32, 32, "u32")),
        _ => None,
    };
    let at = sema
        .decls
        .scopes
        .get(&item.def)
        .copied()
        .unwrap_or(ScopeAt::module(item.module, item.test_part));
    let mut next: Option<i128> = Some(0);
    for (index, written) in decl.variants.iter().enumerate() {
        let (value, span) = match &written.payload {
            ast::VariantPayload::Value(e) => match en.variants.get(index).and_then(|v| v.value) {
                Some(VariantValue::Int(v)) => (Some(v), e.span),
                Some(VariantValue::Text(_)) => return,
                None => {
                    let case = (adt, VariantIdx(index as u32));
                    let outer = sema.consts.computing.replace(case);
                    let value = case_value(sema, at, e, repr.map(|r| r.0));
                    sema.consts.computing = outer;
                    sema.consts.pending_cases.remove(&case);
                    match value {
                        Some(v) => {
                            if let AdtKind::Enum(e) = &mut sema.tcx.adt_mut(adt).kind
                                && let Some(variant) = e.variants.get_mut(index)
                            {
                                variant.value = Some(VariantValue::Int(v));
                            }
                        }
                        None => {
                            sema.consts.failed_cases.insert(case);
                        }
                    }
                    (value, e.span)
                }
            },
            ast::VariantPayload::Unit => (next, written.name.span),
            ast::VariantPayload::Fields(_) => return,
        };
        // Without `@repr` no range is checked: SPEC 11 numbers tags from 0
        // regardless of value, and also says a payload-free enum's tag is its
        // discriminant (doc defect, fix-6: reported, nothing refused).
        let mut failed = false;
        if let (Some(v), Some((_, bits, name))) = (value, repr) {
            let max = (1i128 << bits) - 1;
            if !(0..=max).contains(&v) {
                failed = true;
                let enum_name = decl.name.name;
                let message = match &written.payload {
                    ast::VariantPayload::Value(_) => format!(
                        "constant evaluation failed: {} does not fit `{name}`",
                        quote(sema.tcx, span)
                    ),
                    _ => format!(
                        "constant evaluation failed: `{}` would be {v}, which does not fit `{name}`",
                        written.name.name
                    ),
                };
                sema.err(
                    Code::EN0412,
                    message,
                    span,
                    format!("`{enum_name}` is `@repr(\"{name}\")`, which holds 0 to {max}"),
                );
            }
        }
        // The cases after a value that does not fit follow from it alone: not
        // checked again (one mistake, one diagnostic).
        next = match failed {
            true => None,
            false => value.and_then(|v| v.checked_add(1)),
        };
    }
}

/// A case value written as an expression that is no literal: its integer value, or
/// `None` once why is reported.
fn case_value(sema: &mut Sema, at: ScopeAt, e: &ast::Expr, hint: Option<Ty>) -> Option<i128> {
    if let Some(dots) = first_spread(e) {
        report(sema, ConstError::spread(sema.tcx, dots));
        return None;
    }
    if let Some(diag) = runtime_part(sema, at, e, &[]) {
        sema.emit(diag);
        return None;
    }
    let body = type_alone(sema, at, e, hint);
    let value = initializer(&body)?;
    if sema.tcx.references_error(value.ty) {
        return None;
    }
    match eval_in(sema, &body, value, false) {
        Ok(ConstTree::Scalar(int @ ConstValue::Int(..))) if int.as_i128(sema.tcx).is_some() => {
            int.as_i128(sema.tcx)
        }
        Ok(_) => {
            let shown = sema.tcx.ty_string(value.ty);
            sema.err(
                Code::EN0401,
                format!("mismatched types: expected an integer, found `{shown}`"),
                value.span,
                "a case's value is an integer, or else a string literal",
            );
            None
        }
        Err(err) => {
            report(sema, err);
            None
        }
    }
}

/// The `...` of the first spread in `e`, in source order.
fn first_spread(e: &ast::Expr) -> Option<Span> {
    let mut first: Option<Span> = None;
    each_expr(e, &mut |x| {
        if let ast::ExprKind::Array(elems) = &x.kind {
            for elem in elems {
                if let ast::ArrayElem::Spread { dots, .. } = elem
                    && first.is_none_or(|f| dots.lo < f.lo)
                {
                    first = Some(*dots);
                }
            }
        }
    });
    first
}

/// A part of `e` known only at run time that typing it alone could not name:
/// `this` or `super`, and, inside a body, a name that resolves to nothing outside
/// it and was not reported, so a local (EN0412, labelled as the interpreter labels
/// a local).
fn runtime_part(
    sema: &Sema,
    at: ScopeAt,
    e: &ast::Expr,
    shadowing: &[Symbol],
) -> Option<Diagnostic> {
    let mut found: Option<Diagnostic> = None;
    each_expr(e, &mut |x| {
        if found.is_some() {
            return;
        }
        match &x.kind {
            ast::ExprKind::This | ast::ExprKind::Super => {
                let word = if matches!(x.kind, ast::ExprKind::This) {
                    "this"
                } else {
                    "super"
                };
                found = Some(failed_diag(
                    x.span,
                    format!("`{word}` is not constant"),
                    "an object known only at run time",
                ));
            }
            ast::ExprKind::Ident(name) if sema.decls.lowered => {
                let ident = ast::Ident {
                    name: *name,
                    span: x.span,
                };
                let reported = sema.dcx.reported(Code::EN0301, x.span)
                    || sema.dcx.reported(Code::EN0313, x.span)
                    || sema.res.import_failed(at, *name)
                    || deferred_code(name.as_str()).is_some_and(|c| sema.dcx.reported(c, x.span));
                let local = shadowing.contains(name);
                if (local || matches!(lookup_value(sema, at, ident), Res::Err)) && !reported {
                    found = Some(failed_diag(
                        x.span,
                        format!("`{name}` is not constant"),
                        format!("`{name}` is a local variable"),
                    ));
                }
            }
            _ => {}
        }
    });
    found
}

/// The identifiers `e` reads, as [`each_expr`] reaches them.
pub(crate) fn idents_of(e: &ast::Expr) -> Vec<Symbol> {
    let mut out = Vec::new();
    each_expr(e, &mut |x| {
        if let ast::ExprKind::Ident(name) = &x.kind {
            out.push(*name);
        }
    });
    out
}

/// Each expression of `e`, outermost first, through every operand, never into an
/// arrow's body or a block.
fn each_expr<'e>(e: &'e ast::Expr, f: &mut dyn FnMut(&'e ast::Expr)) {
    f(e);
    match &e.kind {
        ast::ExprKind::Template(parts) => {
            for part in parts {
                if let ast::TplPart::Expr(x) = part {
                    each_expr(x, f);
                }
            }
        }
        ast::ExprKind::Array(elems) => {
            for elem in elems {
                match elem {
                    ast::ArrayElem::Item(x) | ast::ArrayElem::Spread { expr: x, .. } => {
                        each_expr(x, f)
                    }
                }
            }
        }
        ast::ExprKind::Repeat(a, b)
        | ast::ExprKind::Binary(_, a, b)
        | ast::ExprKind::Logical(_, a, b)
        | ast::ExprKind::Coalesce(a, b)
        | ast::ExprKind::Index(a, b)
        | ast::ExprKind::Assign {
            target: a,
            value: b,
            ..
        } => {
            each_expr(a, f);
            each_expr(b, f);
        }
        ast::ExprKind::Ternary(c, a, b) => {
            each_expr(c, f);
            each_expr(a, f);
            each_expr(b, f);
        }
        ast::ExprKind::New { init, .. } => match init {
            ast::NewInit::Args(args) => {
                for a in args {
                    each_expr(a, f);
                }
            }
            ast::NewInit::Fields(fields) => {
                for field in fields {
                    if let Some(v) = &field.value {
                        each_expr(v, f);
                    }
                }
            }
        },
        ast::ExprKind::CaseLit { fields, .. } | ast::ExprKind::ObjectLit(fields) => {
            for field in fields {
                if let Some(v) = &field.value {
                    each_expr(v, f);
                }
            }
        }
        ast::ExprKind::Match { subject, arms } => {
            each_expr(subject, f);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    each_expr(guard, f);
                }
                if let ast::ArmBody::Expr(x) = &arm.body {
                    each_expr(x, f);
                }
            }
        }
        ast::ExprKind::Asm(asm) => each_expr(&asm.template, f),
        ast::ExprKind::Paren(x)
        | ast::ExprKind::Unary(_, x)
        | ast::ExprKind::Borrow(x)
        | ast::ExprKind::Deref(x)
        | ast::ExprKind::VoidOp(x)
        | ast::ExprKind::Cast(x, _)
        | ast::ExprKind::Try(x)
        | ast::ExprKind::NonNull(x)
        | ast::ExprKind::Member { base: x, .. }
        | ast::ExprKind::IncDec { target: x, .. } => each_expr(x, f),
        ast::ExprKind::Call { callee, args, .. } => {
            each_expr(callee, f);
            for a in args {
                each_expr(a, f);
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------------
// Shape: every part constant, and the constants read.

/// Checks that every part of `e` is constant and returns the constants it reads,
/// each once, in evaluation order; `fresh` lays out without the `Tcx`'s memo.
fn scan(tcx: &Tcx, body: &Body, e: &Expr, fresh: bool) -> Result<Vec<DefId>, ConstError> {
    let mut scan = Scan {
        tcx,
        body,
        deps: Vec::new(),
        fresh,
    };
    scan.expr(e)?;
    Ok(scan.deps)
}

struct Scan<'a> {
    tcx: &'a Tcx,
    body: &'a Body,
    deps: Vec<DefId>,
    fresh: bool,
}

impl Scan<'_> {
    fn expr(&mut self, e: &Expr) -> Result<(), ConstError> {
        let tcx = self.tcx;
        if tcx.references_error(e.ty) {
            return Err(ConstError::Reported);
        }
        match &e.kind {
            ExprKind::Const(value) => match value {
                ConstValue::Int(..)
                | ConstValue::Float(..)
                | ConstValue::Bool(_)
                | ConstValue::Void
                | ConstValue::Str(_) => {}
                ConstValue::FnAddr(_) => {
                    return Err(not_constant(
                        tcx,
                        e,
                        "a function's address is not a constant",
                    ));
                }
                ConstValue::StaticAddr(_) | ConstValue::Overridden(_) => {
                    return Err(not_constant(tcx, e, NOT_CONSTANT));
                }
            },
            ExprKind::NullLit => {}
            ExprKind::Static(def) => {
                let data = tcx.def(*def);
                let name = data.name().map_or("?", |n| n.as_str());
                match data.kind {
                    DefKind::Const => {
                        if !self.deps.contains(def) {
                            self.deps.push(*def);
                        }
                    }
                    DefKind::Static => {
                        let label =
                            format!("`{name}` is an `unsafe let`, which can change at run time");
                        return Err(not_constant(tcx, e, label));
                    }
                    _ => return Err(not_constant(tcx, e, NOT_CONSTANT)),
                }
            }
            ExprKind::Local(local) => {
                let label = match self.body.locals.get(*local).and_then(|l| l.name) {
                    Some(name) => format!("`{name}` is a local variable"),
                    None => "this is a local variable".to_owned(),
                };
                return Err(not_constant(tcx, e, label));
            }
            ExprKind::ArrayLit(items) => {
                self.fixed(e)?;
                for item in items {
                    self.expr(item)?;
                }
            }
            ExprKind::Repeat(item, _) => {
                self.fixed(e)?;
                self.expr(item)?;
            }
            ExprKind::TupleLit(items)
            | ExprKind::ObjectLit { fields: items, .. }
            | ExprKind::VariantLit { fields: items, .. } => {
                for item in items {
                    self.expr(item)?;
                }
            }
            ExprKind::NewNamed {
                adt,
                args,
                fields,
                default_from,
            } => {
                for (_, value) in fields {
                    self.expr(value)?;
                }
                for &field in default_from {
                    field_default(tcx, e, *adt, *args, field)?;
                }
            }
            ExprKind::Unary(_, a) => self.expr(a)?,
            ExprKind::Binary(_, a, b) | ExprKind::Logical(_, a, b) => {
                self.expr(a)?;
                self.expr(b)?;
            }
            ExprKind::Cast(a, kind) => {
                self.expr(a)?;
                let numeric = matches!(
                    kind,
                    CastKind::IntToInt
                        | CastKind::IntToFloat
                        | CastKind::FloatToFloat
                        | CastKind::FloatToInt
                        | CastKind::EnumToInt
                        | CastKind::BoolToInt
                        | CastKind::UsizeToRaw
                );
                if !numeric {
                    return Err(not_constant(tcx, e, "this conversion is not constant"));
                }
            }
            ExprKind::Borrow(a) => {
                if !matches!(a.kind, ExprKind::ArrayLit(_) | ExprKind::Repeat(..)) {
                    return Err(not_constant(
                        tcx,
                        e,
                        "only `&` of a bracket literal is constant",
                    ));
                }
                self.expr(a)?;
            }
            ExprKind::Call {
                callee: Callee::Form(form),
                ..
            } if size_form(*form).is_some() => {
                let (ty, field) = size_form(*form).expect("a size form");
                layout_value(tcx, e, ty, *form, field, self.fresh)?;
            }
            ExprKind::Call { .. } => return Err(call(e, "this calls a function")),
            ExprKind::New { .. } => return Err(call(e, "this calls a constructor")),
            ExprKind::OptionalChain(chain) if matches!(chain.member, OptMember::Call { .. }) => {
                return Err(call(e, "this calls a function"));
            }
            ExprKind::ArrayBuild { parts, .. } => {
                let dots = parts
                    .iter()
                    .find_map(|part| match part {
                        ArrayPart::Spread(operand, _) => Some(dots_before(tcx, operand)),
                        ArrayPart::Item(_) => None,
                    })
                    .unwrap_or(e.span);
                return Err(ConstError::spread(tcx, dots));
            }
            ExprKind::Template(_) => {
                return Err(not_constant(
                    tcx,
                    e,
                    "a template builds a string at run time",
                ));
            }
            _ => return Err(not_constant(tcx, e, NOT_CONSTANT)),
        }
        for adjust in &e.adjust {
            if !constant_adjust(*adjust) {
                return Err(not_constant(tcx, e, "this conversion happens at run time"));
            }
        }
        Ok(())
    }

    /// A bracket literal must make a fixed array: a growable one allocates.
    fn fixed(&self, e: &Expr) -> Result<(), ConstError> {
        let ty = peel_nullable(self.tcx, e.ty);
        match self.tcx.kind(ty) {
            TyKind::Fixed(..) => Ok(()),
            _ => {
                let shown = self.tcx.ty_string(ty);
                let label = format!(
                    "{} allocates at run time",
                    crate::classes::sig::a_ty(&shown)
                );
                Err(not_constant(self.tcx, e, label))
            }
        }
    }
}

/// The label of a part that is not constant and needs no other word.
const NOT_CONSTANT: &str = "this is not a constant expression";

/// The adjusts a constant may carry: a wrap into `T | null`, and the two that change
/// only how a literal is passed (C13, C18).
fn constant_adjust(adjust: Adjust) -> bool {
    matches!(
        adjust,
        Adjust::WrapNull | Adjust::WrapNullRef | Adjust::LiteralDescriptor | Adjust::FixedToSlice
    )
}

/// The type and field of `sizeOf`, `alignOf` or `offsetOf`.
fn size_form(form: FormKind) -> Option<(Ty, Option<FieldIdx>)> {
    match form {
        FormKind::SizeOf(ty) | FormKind::AlignOf(ty) => Some((ty, None)),
        FormKind::OffsetOf(ty, field) => Some((ty, Some(field))),
        _ => None,
    }
}

/// The value of a size form through `enrang-layout`; `fresh` lays out with a
/// cache of its own instead of the `Tcx`'s memo.
fn layout_value(
    tcx: &Tcx,
    e: &Expr,
    ty: Ty,
    form: FormKind,
    field: Option<FieldIdx>,
    fresh: bool,
) -> Result<u64, ConstError> {
    let layout = if fresh {
        LayoutCx::new(tcx).layout_of(ty)
    } else {
        layout_of(tcx, ty)
    };
    let layout = layout.map_err(|err| layout_error(tcx, e, err))?;
    match (form, field) {
        (FormKind::AlignOf(_), _) => Ok(u64::from(layout.align)),
        (_, Some(field)) => layout
            .fields
            .get(field.0 as usize)
            .copied()
            .ok_or_else(|| not_constant(tcx, e, NOT_CONSTANT)),
        _ => Ok(layout.size),
    }
}

/// Why a size form has no constant value.
fn layout_error(tcx: &Tcx, e: &Expr, err: LayoutError) -> ConstError {
    let name = tcx.ty_string(err.ty());
    match err {
        LayoutError::DependsOnContracts { ty } => {
            let (label, note) = match tcx.kind(ty) {
                TyKind::Adt(..) => (
                    format!("`{name}` holds references"),
                    format!(
                        "the layout of `{name}` depends on what its methods do with its references"
                    ),
                ),
                TyKind::Tuple(_) => (
                    format!("`{name}` holds references"),
                    format!(
                        "the layout of `{name}` depends on what the code using it does with its \
                         references"
                    ),
                ),
                _ => (
                    format!("`{name}` is a reference whose form follows its permission"),
                    format!(
                        "the layout of `{name}` depends on what the code using it does with it"
                    ),
                ),
            };
            fail(not_constant_diag(tcx, e, label).note(note))
        }
        LayoutError::TooLarge { .. } => {
            not_constant(tcx, e, format!("`{name}` is larger than `isize.MAX` bytes"))
        }
        LayoutError::Unsized { .. } => {
            not_constant(tcx, e, format!("`{name}` has no size of its own"))
        }
        LayoutError::Generic { .. } => not_constant(
            tcx,
            e,
            format!("the layout of `{name}` depends on a type argument"),
        ),
        LayoutError::Recursive { .. } | LayoutError::ErrorType { .. } => ConstError::Reported,
    }
}

/// The default of a field a class literal leaves out (`default_from`): the field
/// type's default (S:582), with how many values it holds; `x?: T` is `T | null`
/// already, so its default is `null`. A field whose default is a written
/// initialiser, its own or an `override` in the class's chain, is not constant:
/// initialisers run at run time (S:756) and stay in the declaring module's code
/// (A:928).
fn field_default(
    tcx: &Tcx,
    e: &Expr,
    adt: AdtId,
    args: TyList,
    field: FieldIdx,
) -> Result<(Ty, u64), ConstError> {
    let Some(def) = tcx
        .adt(adt)
        .as_class()
        .and_then(|class| class.fields.get(field.0 as usize))
    else {
        return Err(ConstError::Reported);
    };
    let name = def.name;
    if overridden(tcx, adt, field) || (def.has_default && !def.optional) {
        let label = format!("`{name}` is left to its initialiser, which runs at run time");
        return Err(not_constant(tcx, e, label));
    }
    let ty = tcx.field_ty(adt, None, field, args);
    match default_size(tcx, ty) {
        Some(size) => Ok((ty, size)),
        None => Err(not_constant(
            tcx,
            e,
            format!("`{name}` has no constant default"),
        )),
    }
}

/// Whether a class of `adt`'s chain gives `field` a new default (`override`).
fn overridden(tcx: &Tcx, adt: AdtId, field: FieldIdx) -> bool {
    let mut at = Some(adt);
    while let Some(adt) = at {
        let Some(class) = tcx.adt(adt).as_class() else {
            return false;
        };
        if class.overrides.contains(&field) {
            return true;
        }
        at = class.base.and_then(|base| match tcx.kind(base) {
            TyKind::Adt(base, _) => Some(base),
            _ => None,
        });
    }
    false
}

/// The number of values in `ty`'s default, saturating, or `None` when it has none.
/// A default is a number's `0`, `bool`'s `false`, `null`, a raw pointer's address 0
/// (S:582, S:871), or a fixed array of defaults (**choice**: S:582 names no fixed
/// array, and a zero-filled one allocates nothing).
fn default_size(tcx: &Tcx, ty: Ty) -> Option<u64> {
    match tcx.kind(ty) {
        TyKind::Bool | TyKind::Int(_) | TyKind::Raw(_) | TyKind::Float(_) | TyKind::Nullable(_) => {
            Some(1)
        }
        TyKind::Fixed(elem, n) => {
            Some(default_size(tcx, elem)?.saturating_mul(n).saturating_add(1))
        }
        _ => None,
    }
}

/// `ty`'s default, once `default_size` said it has one and the values are paid.
fn build_default(tcx: &Tcx, ty: Ty) -> ConstTree {
    match tcx.kind(ty) {
        TyKind::Bool => ConstTree::Scalar(ConstValue::Bool(false)),
        TyKind::Float(_) => ConstTree::Scalar(ConstValue::Float(0, ty)),
        TyKind::Nullable(_) => ConstTree::Null,
        TyKind::Fixed(elem, n) => ConstTree::Array(vec![build_default(tcx, elem); n as usize]),
        _ => ConstTree::Scalar(ConstValue::Int(0, ty)),
    }
}

// ---------------------------------------------------------------------------------
// Value.

/// One root's evaluation, after its shape passed and the constants it reads have
/// values.
struct Interp<'a> {
    tcx: &'a Tcx,
    state: &'a ConstState,
    left: u64,
    ptr_bits: u32,
}

/// An integer type's signedness and width; a raw pointer is unsigned at `P`.
#[derive(Copy, Clone)]
struct IntInfo {
    signed: bool,
    bits: u32,
}

impl IntInfo {
    fn mask(self) -> u128 {
        (1u128 << self.bits) - 1
    }

    fn min(self) -> i128 {
        if self.signed {
            -(1i128 << (self.bits - 1))
        } else {
            0
        }
    }

    fn max(self) -> i128 {
        if self.signed {
            (1i128 << (self.bits - 1)) - 1
        } else {
            (1i128 << self.bits) - 1
        }
    }

    /// The value of two's-complement `bits` at this width.
    fn decode(self, bits: u128) -> i128 {
        let bits = bits & self.mask();
        if self.signed && bits >> (self.bits - 1) & 1 == 1 {
            (bits | !self.mask()) as i128
        } else {
            bits as i128
        }
    }

    /// The bits of `value`, when it fits.
    fn encode(self, value: i128) -> Option<u128> {
        (self.min()..=self.max())
            .contains(&value)
            .then(|| value as u128 & self.mask())
    }
}

impl<'a> Interp<'a> {
    fn new(tcx: &'a Tcx, state: &'a ConstState) -> Interp<'a> {
        Interp {
            tcx,
            state,
            left: MAX_VALUES,
            ptr_bits: u32::from(tcx.target().layout.ptr_bytes) * 8,
        }
    }

    fn eval(&mut self, e: &Expr) -> Result<ConstTree, ConstError> {
        let mut value = self.kind(e)?;
        for adjust in &e.adjust {
            value = match adjust {
                Adjust::WrapNull | Adjust::WrapNullRef => {
                    self.spend(e, 1)?;
                    ConstTree::Present(Box::new(value))
                }
                Adjust::LiteralDescriptor | Adjust::FixedToSlice => value,
                _ => {
                    return Err(not_constant(
                        self.tcx,
                        e,
                        "this conversion happens at run time",
                    ));
                }
            };
        }
        Ok(value)
    }

    /// Charges `n` values to the evaluation.
    fn spend(&mut self, e: &Expr, n: u64) -> Result<(), ConstError> {
        match self.left.checked_sub(n) {
            Some(left) => {
                self.left = left;
                Ok(())
            }
            None => Err(failed(
                e.span,
                format!("{} is too large to evaluate", quote(self.tcx, e.span)),
                format!("a constant holds at most {MAX_VALUES} values"),
            )),
        }
    }

    fn kind(&mut self, e: &Expr) -> Result<ConstTree, ConstError> {
        let tcx = self.tcx;
        match &e.kind {
            ExprKind::Const(value) => {
                self.spend(e, 1)?;
                Ok(ConstTree::Scalar(*value))
            }
            ExprKind::NullLit => {
                self.spend(e, 1)?;
                Ok(ConstTree::Null)
            }
            ExprKind::Static(def) => {
                let value = self.state.read(tcx, *def)?;
                self.spend(e, tree_size(&value))?;
                Ok(value)
            }
            ExprKind::ArrayLit(items) => {
                self.spend(e, 1)?;
                Ok(ConstTree::Array(self.list(items)?))
            }
            ExprKind::Repeat(item, n) => {
                // The item, already paid once, then its other copies and the array.
                let value = self.eval(item)?;
                let total = n
                    .saturating_sub(1)
                    .checked_mul(tree_size(&value))
                    .and_then(|t| t.checked_add(1))
                    .unwrap_or(u64::MAX);
                self.spend(e, total)?;
                Ok(ConstTree::Array(vec![value; *n as usize]))
            }
            ExprKind::TupleLit(items) => {
                self.spend(e, 1)?;
                Ok(ConstTree::Tuple(self.list(items)?))
            }
            ExprKind::ObjectLit { fields, .. } => {
                self.spend(e, 1)?;
                Ok(ConstTree::Object(self.list(fields)?))
            }
            ExprKind::VariantLit {
                adt,
                variant,
                fields,
                ..
            } => {
                self.spend(e, 1)?;
                Ok(ConstTree::Adt {
                    adt: *adt,
                    variant: Some(*variant),
                    fields: self.list(fields)?,
                })
            }
            ExprKind::NewNamed {
                adt,
                args,
                fields,
                default_from,
            } => self.new_named(e, *adt, *args, fields, default_from),
            ExprKind::Unary(op, a) => self.unary(e, *op, a),
            ExprKind::Binary(op, a, b) => self.binary(e, *op, a, b),
            ExprKind::Logical(op, a, b) => {
                let left = self.boolean(a)?;
                let value = match (op, left) {
                    (LogOp::And, false) => false,
                    (LogOp::Or, true) => true,
                    _ => self.boolean(b)?,
                };
                self.spend(e, 1)?;
                Ok(ConstTree::Scalar(ConstValue::Bool(value)))
            }
            ExprKind::Cast(a, kind) => self.cast(e, a, *kind),
            ExprKind::Borrow(a) => {
                let ConstTree::Array(items) = self.eval(a)? else {
                    return Err(not_constant(tcx, e, NOT_CONSTANT));
                };
                let elem = match tcx.kind(peel_nullable(tcx, a.ty)) {
                    TyKind::Fixed(elem, _) => elem,
                    _ => return Err(not_constant(tcx, e, NOT_CONSTANT)),
                };
                Ok(ConstTree::View { elem, items })
            }
            ExprKind::Call {
                callee: Callee::Form(form),
                ..
            } if size_form(*form).is_some() => {
                let (ty, field) = size_form(*form).expect("a size form");
                let value = layout_value(tcx, e, ty, *form, field, self.state.fresh_layouts)?;
                self.spend(e, 1)?;
                let usize_ty = tcx.common().usize;
                Ok(ConstTree::Scalar(ConstValue::Int(
                    u128::from(value),
                    usize_ty,
                )))
            }
            _ => Err(not_constant(tcx, e, NOT_CONSTANT)),
        }
    }

    fn list(&mut self, items: &[Expr]) -> Result<Vec<ConstTree>, ConstError> {
        items.iter().map(|item| self.eval(item)).collect()
    }

    fn boolean(&mut self, e: &Expr) -> Result<bool, ConstError> {
        match self.eval(e)? {
            ConstTree::Scalar(ConstValue::Bool(value)) => Ok(value),
            _ => Err(not_constant(self.tcx, e, NOT_CONSTANT)),
        }
    }

    /// `new C { ... }`: the named values in order, then the left-out fields'
    /// defaults, every field in `FieldIdx` order.
    fn new_named(
        &mut self,
        e: &Expr,
        adt: AdtId,
        args: TyList,
        fields: &[(FieldIdx, Expr)],
        default_from: &[FieldIdx],
    ) -> Result<ConstTree, ConstError> {
        let tcx = self.tcx;
        let Some(class) = tcx.adt(adt).as_class() else {
            return Err(ConstError::Reported);
        };
        let mut slots: Vec<Option<ConstTree>> = vec![None; class.fields.len()];
        self.spend(e, 1)?;
        for (field, value) in fields {
            let value = self.eval(value)?;
            match slots.get_mut(field.0 as usize) {
                Some(slot) => *slot = Some(value),
                None => return Err(ConstError::Reported),
            }
        }
        for &field in default_from {
            let (ty, size) = field_default(tcx, e, adt, args, field)?;
            self.spend(e, size)?;
            let value = build_default(tcx, ty);
            match slots.get_mut(field.0 as usize) {
                Some(slot) => *slot = Some(value),
                None => return Err(ConstError::Reported),
            }
        }
        let fields = slots
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .ok_or(ConstError::Reported)?;
        Ok(ConstTree::Adt {
            adt,
            variant: None,
            fields,
        })
    }

    /// An integer constant's value and width; a raw pointer's address.
    fn int(&self, value: ConstValue) -> Option<(i128, IntInfo, Ty)> {
        let ConstValue::Int(bits, ty) = value else {
            return None;
        };
        let info = self.int_info(ty)?;
        Some((info.decode(bits), info, ty))
    }

    fn int_info(&self, ty: Ty) -> Option<IntInfo> {
        match self.tcx.kind(ty) {
            TyKind::Int(int) => Some(IntInfo {
                signed: int.is_signed(),
                bits: int.bits(self.ptr_bits),
            }),
            TyKind::Raw(_) => Some(IntInfo {
                signed: false,
                bits: self.ptr_bits,
            }),
            _ => None,
        }
    }

    fn float_ty(&self, ty: Ty) -> Option<FloatTy> {
        match self.tcx.kind(ty) {
            TyKind::Float(float) => Some(float),
            _ => None,
        }
    }

    fn scalar(&mut self, e: &Expr, value: ConstValue) -> Result<ConstTree, ConstError> {
        self.spend(e, 1)?;
        Ok(ConstTree::Scalar(value))
    }

    fn unary(&mut self, e: &Expr, op: UnOp, a: &Expr) -> Result<ConstTree, ConstError> {
        let tcx = self.tcx;
        let ConstTree::Scalar(value) = self.eval(a)? else {
            return Err(not_constant(tcx, e, NOT_CONSTANT));
        };
        match (op, value) {
            (UnOp::Not, ConstValue::Bool(b)) => self.scalar(e, ConstValue::Bool(!b)),
            (UnOp::Neg, ConstValue::Float(bits, ty)) => {
                let sign = match self.float_ty(ty) {
                    Some(FloatTy::F32) => 1 << 31,
                    _ => 1 << 63,
                };
                self.scalar(e, ConstValue::Float(bits ^ sign, ty))
            }
            (UnOp::Neg, _) => {
                let Some((x, info, ty)) = self.int(value) else {
                    return Err(not_constant(tcx, e, NOT_CONSTANT));
                };
                match info.encode(-x) {
                    Some(bits) => self.scalar(e, ConstValue::Int(bits, ty)),
                    None => Err(overflow(tcx, e, ty, format!("integer overflow: neg {x}"))),
                }
            }
            (UnOp::BitNot, _) => {
                let Some((x, info, ty)) = self.int(value) else {
                    return Err(not_constant(tcx, e, NOT_CONSTANT));
                };
                let bits = !(x as u128) & info.mask();
                self.scalar(e, ConstValue::Int(bits, ty))
            }
            _ => Err(not_constant(tcx, e, NOT_CONSTANT)),
        }
    }

    fn binary(&mut self, e: &Expr, op: BinOp, a: &Expr, b: &Expr) -> Result<ConstTree, ConstError> {
        let x = self.eval(a)?;
        let y = self.eval(b)?;
        match op {
            BinOp::Eq | BinOp::Ne => {
                let equal = self.equal(e, &x, &y)?;
                self.scalar(e, ConstValue::Bool(equal == (op == BinOp::Eq)))
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let order = self.order(e, &x, &y)?;
                let holds = match op {
                    BinOp::Lt => order.is_some_and(|o| o.is_lt()),
                    BinOp::Le => order.is_some_and(|o| o.is_le()),
                    BinOp::Gt => order.is_some_and(|o| o.is_gt()),
                    _ => order.is_some_and(|o| o.is_ge()),
                };
                self.scalar(e, ConstValue::Bool(holds))
            }
            _ => match (x, y) {
                (ConstTree::Scalar(x), ConstTree::Scalar(y)) => self.arith(e, op, x, y),
                _ => Err(not_constant(self.tcx, e, NOT_CONSTANT)),
            },
        }
    }

    /// `==` (SPEC 4.6): numbers by value, integers of two types by their true
    /// values, `bool`, strings by text, payload-free enum cases, and nullables
    /// equal when both are null or both present with equal payloads. A class or a
    /// payload enum compares by calling `equals`: EN1032.
    fn equal(&self, e: &Expr, x: &ConstTree, y: &ConstTree) -> Result<bool, ConstError> {
        let tcx = self.tcx;
        match (x, y) {
            (ConstTree::Null, ConstTree::Null) => Ok(true),
            (ConstTree::Null, ConstTree::Present(_)) | (ConstTree::Present(_), ConstTree::Null) => {
                Ok(false)
            }
            (ConstTree::Present(x), ConstTree::Present(y)) => self.equal(e, x, y),
            (ConstTree::Scalar(a), ConstTree::Scalar(b)) => {
                if let (Some((x, ..)), Some((y, ..))) = (self.int(*a), self.int(*b)) {
                    return Ok(x == y);
                }
                match (*a, *b) {
                    (ConstValue::Float(x, xt), ConstValue::Float(y, _)) => {
                        Ok(match self.float_ty(xt) {
                            Some(FloatTy::F32) => {
                                f32::from_bits(x as u32) == f32::from_bits(y as u32)
                            }
                            _ => f64::from_bits(x) == f64::from_bits(y),
                        })
                    }
                    (ConstValue::Bool(x), ConstValue::Bool(y)) => Ok(x == y),
                    (ConstValue::Str(x), ConstValue::Str(y)) => Ok(tcx.str(x) == tcx.str(y)),
                    (ConstValue::Void, ConstValue::Void) => Ok(true),
                    _ => Err(not_constant(tcx, e, NOT_CONSTANT)),
                }
            }
            (
                ConstTree::Adt {
                    adt,
                    variant: Some(x),
                    ..
                },
                ConstTree::Adt {
                    variant: Some(y), ..
                },
            ) if tcx
                .adt(*adt)
                .as_enum()
                .is_some_and(|en| en.is_payload_free()) =>
            {
                Ok(x == y)
            }
            (ConstTree::Adt { .. }, ConstTree::Adt { .. }) => {
                Err(call(e, "this compares by calling `equals`"))
            }
            _ => Err(not_constant(tcx, e, NOT_CONSTANT)),
        }
    }

    /// `<` and its kin: numbers only, integers of two types by their true values; a
    /// NaN orders with nothing.
    fn order(
        &self,
        e: &Expr,
        x: &ConstTree,
        y: &ConstTree,
    ) -> Result<Option<std::cmp::Ordering>, ConstError> {
        let (ConstTree::Scalar(a), ConstTree::Scalar(b)) = (x, y) else {
            return Err(not_constant(self.tcx, e, NOT_CONSTANT));
        };
        if let (Some((x, ..)), Some((y, ..))) = (self.int(*a), self.int(*b)) {
            return Ok(Some(x.cmp(&y)));
        }
        match (*a, *b) {
            (ConstValue::Float(x, xt), ConstValue::Float(y, _)) => Ok(match self.float_ty(xt) {
                Some(FloatTy::F32) => {
                    f32::from_bits(x as u32).partial_cmp(&f32::from_bits(y as u32))
                }
                _ => f64::from_bits(x).partial_cmp(&f64::from_bits(y)),
            }),
            _ => Err(not_constant(self.tcx, e, NOT_CONSTANT)),
        }
    }

    /// Arithmetic, bitwise and shift operators (SPEC 4.6, 9.2): checked at the left
    /// operand's width, `/` truncating, `%` with the dividend's sign, `>>`
    /// arithmetic on signed types, a shift count of any integer type.
    fn arith(
        &mut self,
        e: &Expr,
        op: BinOp,
        a: ConstValue,
        b: ConstValue,
    ) -> Result<ConstTree, ConstError> {
        let tcx = self.tcx;
        if let (ConstValue::Float(x, ty), ConstValue::Float(y, _)) = (a, b) {
            return self.float_arith(e, op, x, y, ty);
        }
        let (Some((x, info, ty)), Some((y, ..))) = (self.int(a), self.int(b)) else {
            return Err(not_constant(tcx, e, NOT_CONSTANT));
        };
        // The label repeats the run-time panic (SPEC 9.1), `shown` its operator.
        let overflowed = |shown: BinOp| {
            let label = format!("integer overflow: {x} {} {y}", shown.as_str());
            overflow(tcx, e, ty, label)
        };
        let bits = match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                // Checked even in `i128`: two `u64` operands multiply past it.
                let result = match op {
                    BinOp::Add => x.checked_add(y),
                    BinOp::Sub => x.checked_sub(y),
                    _ => x.checked_mul(y),
                };
                result
                    .and_then(|r| info.encode(r))
                    .ok_or_else(|| overflowed(op))?
            }
            BinOp::Div | BinOp::Rem => {
                if y == 0 {
                    return Err(failed(
                        e.span,
                        format!("{} divides by zero", quote(tcx, e.span)),
                        "division by zero",
                    ));
                }
                // `MIN / -1` does not fit, and neither does `MIN % -1`, whose panic
                // SPEC 9.1's table also writes `integer overflow: MIN / -1`.
                let quotient = x / y;
                info.encode(quotient)
                    .ok_or_else(|| overflowed(BinOp::Div))?;
                let result = if op == BinOp::Div { quotient } else { x % y };
                info.encode(result).ok_or_else(|| overflowed(op))?
            }
            BinOp::Shl | BinOp::Shr => {
                if y < 0 || y >= i128::from(info.bits) {
                    return Err(failed(
                        e.span,
                        format!("{} shifts out of range", quote(tcx, e.span)),
                        format!("shift count {y} out of range for {} bits", info.bits),
                    ));
                }
                if op == BinOp::Shl {
                    ((x as u128) << y) & info.mask()
                } else {
                    (x >> y) as u128 & info.mask()
                }
            }
            BinOp::BitAnd => (x & y) as u128 & info.mask(),
            BinOp::BitOr => (x | y) as u128 & info.mask(),
            BinOp::BitXor => (x ^ y) as u128 & info.mask(),
            _ => return Err(not_constant(tcx, e, NOT_CONSTANT)),
        };
        self.scalar(e, ConstValue::Int(bits, ty))
    }

    /// Float arithmetic in the type's own precision; IEEE, never failing (SPEC 4.6).
    fn float_arith(
        &mut self,
        e: &Expr,
        op: BinOp,
        x: u64,
        y: u64,
        ty: Ty,
    ) -> Result<ConstTree, ConstError> {
        let bits = match self.float_ty(ty) {
            Some(FloatTy::F32) => {
                let (x, y) = (f32::from_bits(x as u32), f32::from_bits(y as u32));
                let result = match op {
                    BinOp::Add => x + y,
                    BinOp::Sub => x - y,
                    BinOp::Mul => x * y,
                    BinOp::Div => x / y,
                    BinOp::Rem => x % y,
                    _ => return Err(not_constant(self.tcx, e, NOT_CONSTANT)),
                };
                u64::from(result.to_bits())
            }
            _ => {
                let (x, y) = (f64::from_bits(x), f64::from_bits(y));
                let result = match op {
                    BinOp::Add => x + y,
                    BinOp::Sub => x - y,
                    BinOp::Mul => x * y,
                    BinOp::Div => x / y,
                    BinOp::Rem => x % y,
                    _ => return Err(not_constant(self.tcx, e, NOT_CONSTANT)),
                };
                result.to_bits()
            }
        };
        self.scalar(e, ConstValue::Float(bits, ty))
    }

    /// Numeric `as` and `usize` to raw pointer `as` (SPEC 4.6's table): int to int
    /// checked, to float rounding to nearest-even, float to float rounding,
    /// float to int truncating and checked, a payload-free enum's discriminant
    /// checked as int to int, `bool` to 0 or 1.
    fn cast(&mut self, e: &Expr, a: &Expr, kind: CastKind) -> Result<ConstTree, ConstError> {
        let tcx = self.tcx;
        // The cast's own type: an adjust's wrap may be part of `e.ty`, and no cast
        // makes a nullable.
        let target = peel_nullable(tcx, e.ty);
        let value = self.eval(a)?;
        let result = match (kind, value) {
            (CastKind::IntToInt | CastKind::UsizeToRaw, ConstTree::Scalar(v)) => {
                let x = self
                    .int(v)
                    .ok_or_else(|| not_constant(tcx, e, NOT_CONSTANT))?
                    .0;
                self.int_to(e, target, x, &x.to_string())?
            }
            (CastKind::IntToFloat, ConstTree::Scalar(v)) => {
                let x = self
                    .int(v)
                    .ok_or_else(|| not_constant(tcx, e, NOT_CONSTANT))?
                    .0;
                let bits = match self.float_ty(target) {
                    Some(FloatTy::F32) => u64::from((x as f32).to_bits()),
                    Some(FloatTy::F64) => (x as f64).to_bits(),
                    None => return Err(not_constant(tcx, e, NOT_CONSTANT)),
                };
                ConstValue::Float(bits, target)
            }
            (CastKind::FloatToFloat, ConstTree::Scalar(ConstValue::Float(bits, from))) => {
                let value = float_value(self.float_ty(from), bits);
                let bits = match self.float_ty(target) {
                    Some(FloatTy::F32) => u64::from((value as f32).to_bits()),
                    Some(FloatTy::F64) => value.to_bits(),
                    None => return Err(not_constant(tcx, e, NOT_CONSTANT)),
                };
                ConstValue::Float(bits, target)
            }
            (CastKind::FloatToInt, ConstTree::Scalar(ConstValue::Float(bits, from))) => {
                let from = self.float_ty(from);
                let shown = float_text(from, bits);
                let truncated = float_value(from, bits).trunc();
                if truncated.is_nan() {
                    return Err(out_of_range(tcx, e, target, &shown));
                }
                // Exact for every value that can fit, and saturating, so out of
                // range, for any other (an infinity included).
                self.int_to(e, target, truncated as i128, &shown)?
            }
            (
                CastKind::EnumToInt,
                ConstTree::Adt {
                    adt,
                    variant: Some(variant),
                    ..
                },
            ) => {
                if let Some(err) = self.unknown_case(e, adt, variant) {
                    return Err(err);
                }
                let Some(x) = discriminant(tcx, adt, variant) else {
                    return Err(not_constant(tcx, e, NOT_CONSTANT));
                };
                self.int_to(e, target, x, &x.to_string())?
            }
            (CastKind::BoolToInt, ConstTree::Scalar(ConstValue::Bool(b))) => {
                self.int_to(e, target, i128::from(b), if b { "true" } else { "false" })?
            }
            _ => return Err(not_constant(tcx, e, NOT_CONSTANT)),
        };
        self.scalar(e, result)
    }

    /// Why the discriminant of case `variant` of `adt` is not known: it, or a case
    /// before it that it follows with no value of its own between, has a computed
    /// value that failed (reported already), or one not computed yet, which a value
    /// of the enum's own, or a cycle through another enum, reads before its turn.
    fn unknown_case(&self, e: &Expr, adt: AdtId, variant: VariantIdx) -> Option<ConstError> {
        let def = self.tcx.adt(adt);
        let en = def.as_enum()?;
        for index in (0..=variant.0).rev() {
            let case = (adt, VariantIdx(index));
            if self.state.failed_cases.contains(&case) {
                return Some(ConstError::Reported);
            }
            if self.state.pending_cases.contains(&case) {
                let name = en
                    .variants
                    .get(index as usize)
                    .map_or("?".to_owned(), |v| v.name.to_string());
                // The case being computed reads itself, through a constant or the
                // cases that follow it (S:756: a cycle is EN0412).
                // That is a cycle only when the pending case reached is the one
                // being computed: the read case is it, or follows it with no value
                // of its own. A case with a value of its own is merely later.
                if let Some((computing, at)) = self.state.computing
                    && computing == adt
                    && at.0 == index
                {
                    let own = en
                        .variants
                        .get(at.0 as usize)
                        .map_or("?".to_owned(), |v| v.name.to_string());
                    let read = en
                        .variants
                        .get(variant.0 as usize)
                        .map_or("?".to_owned(), |v| v.name.to_string());
                    let enum_name = def.name;
                    let message = match at == variant {
                        true => format!("constant cycle: `{enum_name}.{own}` uses its own value"),
                        false => format!(
                            "constant cycle: `{enum_name}.{own}` uses `{enum_name}.{read}`, which uses `{enum_name}.{own}`"
                        ),
                    };
                    return Some(fail(Diagnostic::new(
                        Code::EN0412,
                        message,
                        e.span,
                        format!(
                            "this reads `{enum_name}.{read}` while `{enum_name}.{own}` is computed"
                        ),
                    )));
                }
                return Some(not_constant(
                    self.tcx,
                    e,
                    format!(
                        "the value of `{}.{name}` is not computed yet here",
                        def.name
                    ),
                ));
            }
            if en
                .variants
                .get(index as usize)
                .is_some_and(|v| v.value.is_some())
            {
                return None;
            }
        }
        None
    }

    /// `x` at the integer or raw pointer type `target`, when it fits.
    fn int_to(&self, e: &Expr, target: Ty, x: i128, shown: &str) -> Result<ConstValue, ConstError> {
        let Some(info) = self.int_info(target) else {
            return Err(not_constant(self.tcx, e, NOT_CONSTANT));
        };
        info.encode(x)
            .map(|bits| ConstValue::Int(bits, target))
            .ok_or_else(|| out_of_range(self.tcx, e, target, shown))
    }
}

/// A float constant's value, `f32` bits widened exactly.
fn float_value(fty: Option<FloatTy>, bits: u64) -> f64 {
    match fty {
        Some(FloatTy::F32) => f64::from(f32::from_bits(bits as u32)),
        _ => f64::from_bits(bits),
    }
}

/// A float constant as a message shows it, in its own precision.
fn float_text(fty: Option<FloatTy>, bits: u64) -> String {
    match fty {
        Some(FloatTy::F32) => format!("{:?}", f32::from_bits(bits as u32)),
        _ => format!("{:?}", f64::from_bits(bits)),
    }
}

/// A payload-free enum case's discriminant: its written integer, or the one after
/// the case before, from 0 (S:591); `None` for a payload or text enum.
fn discriminant(tcx: &Tcx, adt: AdtId, variant: VariantIdx) -> Option<i128> {
    let en = tcx.adt(adt).as_enum()?;
    if !en.is_payload_free() || en.values == EnumValues::Texts {
        return None;
    }
    let mut next: i128 = 0;
    for (index, case) in en.variants.iter().enumerate() {
        let value = match case.value {
            Some(VariantValue::Int(value)) => value,
            _ => next,
        };
        if index == variant.0 as usize {
            return Some(value);
        }
        next = value.checked_add(1)?;
    }
    None
}

/// The number of nodes in a tree.
fn tree_size(tree: &ConstTree) -> u64 {
    let sum = |items: &[ConstTree]| items.iter().map(tree_size).sum::<u64>();
    1 + match tree {
        ConstTree::Scalar(_) | ConstTree::Null => 0,
        ConstTree::Array(items)
        | ConstTree::Tuple(items)
        | ConstTree::Object(items)
        | ConstTree::Adt { fields: items, .. }
        | ConstTree::View { items, .. } => sum(items),
        ConstTree::Present(inner) => tree_size(inner),
    }
}

/// `ty` without its `| null` layers: a cast's or a literal's own type when the
/// expression's type includes the wrap of its adjust.
fn peel_nullable(tcx: &Tcx, mut ty: Ty) -> Ty {
    while let TyKind::Nullable(inner) = tcx.kind(ty) {
        ty = inner;
    }
    ty
}

// ---------------------------------------------------------------------------------
// Diagnostics.

fn fail(diag: Diagnostic) -> ConstError {
    ConstError::Fail(Box::new(diag))
}

/// `` `text` `` of a short one-line span, else `this expression`.
fn quote(tcx: &Tcx, span: Span) -> String {
    if !span.is_dummy() {
        let text = tcx.map().text(span);
        if !text.contains('\n') && text.chars().count() <= QUOTE_MAX {
            return format!("`{text}`");
        }
    }
    "this expression".to_owned()
}

/// EN0412, `constant evaluation failed: <what>`, at `span`.
fn failed_diag(span: Span, what: String, label: impl Into<String>) -> Diagnostic {
    Diagnostic::new(
        Code::EN0412,
        format!("constant evaluation failed: {what}"),
        span,
        label,
    )
}

fn failed(span: Span, what: String, label: impl Into<String>) -> ConstError {
    fail(failed_diag(span, what, label))
}

/// EN0412 naming the part `e` that is not constant.
fn not_constant_diag(tcx: &Tcx, e: &Expr, label: impl Into<String>) -> Diagnostic {
    failed_diag(
        e.span,
        format!("{} is not constant", quote(tcx, e.span)),
        label,
    )
}

fn not_constant(tcx: &Tcx, e: &Expr, label: impl Into<String>) -> ConstError {
    fail(not_constant_diag(tcx, e, label))
}

/// EN0412 for an operation at `ty` whose result does not fit; `label` is the
/// message the operation panics with at run time (SPEC 9.1).
fn overflow(tcx: &Tcx, e: &Expr, ty: Ty, label: String) -> ConstError {
    failed(
        e.span,
        format!("{} overflows `{}`", quote(tcx, e.span), tcx.ty_string(ty)),
        label,
    )
}

/// EN0412 for a conversion whose value does not fit `target`, labelled with the
/// panic's message, `conversion out of range: V as T` (SPEC 9.1).
fn out_of_range(tcx: &Tcx, e: &Expr, target: Ty, shown: &str) -> ConstError {
    let target = tcx.ty_string(target);
    failed(
        e.span,
        format!("{} is out of range for `{target}`", quote(tcx, e.span)),
        format!("conversion out of range: {shown} as {target}"),
    )
}

/// EN1032 at a call (SPEC 16: the message head, one note with the reason, the
/// table's help).
fn call(e: &Expr, label: &str) -> ConstError {
    fail(
        Diagnostic::new(
            Code::EN1032,
            "compile-time function calls are not supported yet",
            e.span,
            label,
        )
        .note(
            "a constant is computed while compiling, and the compiler does not run functions yet.",
        )
        .with_help(Help::text(
            "Use a literal expression, or initialise at startup",
        )),
    )
}

/// EN0412 for a cycle, at the first of its constants in source order, the cycle
/// read from there: `` constant cycle: `A` uses `B`, which uses `A` ``. `members`
/// are in the order each uses the next, the last using the first.
pub(crate) fn cycle(tcx: &Tcx, members: &[DefId]) -> ConstError {
    let first = (0..members.len())
        .min_by_key(|&i| {
            let data = tcx.def(members[i]);
            (data.name_span, data.path.to_string())
        })
        .unwrap_or(0);
    let order: Vec<DefId> = members[first..]
        .iter()
        .chain(&members[..first])
        .copied()
        .collect();
    let name = |def: DefId| tcx.def(def).name().map_or("?", |n| n.as_str());
    let names: Vec<&str> = order
        .iter()
        .chain(std::iter::once(&order[0]))
        .map(|&def| name(def))
        .collect();
    let mut message = format!("constant cycle: `{}` uses `{}`", names[0], names[1]);
    for next in &names[2..] {
        message.push_str(&format!(", which uses `{next}`"));
    }
    fail(Diagnostic::new(
        Code::EN0412,
        message,
        tcx.def(order[0]).name_span,
        format!("`{}` depends on its own value", name(order[0])),
    ))
}

/// The `...` before a spread operand: the three bytes ending where the text before
/// the operand ends, once trailing whitespace is skipped; the operand's own span
/// when the text has no `...` there.
fn dots_before(tcx: &Tcx, operand: &Expr) -> Span {
    let span = operand.span;
    if span.is_dummy() {
        return span;
    }
    let file = tcx.map().file_of(span.lo);
    let offset = (span.lo.0 - file.start.0) as usize;
    let before = file.text[..offset].trim_end();
    if before.ends_with("...") {
        let hi = file.start + before.len() as u32;
        return Span {
            lo: BytePos(hi.0 - 3),
            hi,
        };
    }
    span
}
