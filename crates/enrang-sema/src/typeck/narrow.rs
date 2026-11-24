//! Narrowing (plan d.10; SPEC 4.8; A:898-914; owner 4B): flow state inside
//! `check_expr`. A [`FlowState`] follows control flow; facts come from conditions
//! and arms and die only on a visible change (an assignment, a move of the path, a
//! direct write to it or a prefix), found by a prescan of loop bodies and arrow
//! arguments. Every other reference to a proper prefix of a fact's path, or to the
//! path at its nullable type, is recorded for phase 3 (`Body.records`, D1).
//!
//! A fact sits on the place whose type is the nullable or the enum: a path is a
//! local or `this`, then field steps, `Deref` through a reference or a `Box`, and
//! `Payload` into a narrowed nullable (`FactPath`), never an index, a tuple part, a
//! call, a static or a raw deref (S:739). Facts come from `p != null`, `p == null`
//! in the else branch, `!`, `&&`, `||`, an assignment tested in place
//! (`(line = readLine()) != null`, whose value is `line` read after the store), and
//! from `match` arms: the arm's case on the subject inside the arm and its guard,
//! and, after an unguarded `null` arm, the subject non-null in the later arms
//! (S:1133-1135). A test of a path that already holds the same fact keeps that fact
//! (plan choice), and branches join by intersection: a path keeps its fact when
//! every branch holds the same one, under the first branch's identity (A:898, plan
//! choice for the identity a narrowed use names, D1).
//!
//! Kills (S:742): a write kills the facts on its place and deeper, so writing a
//! narrowed payload's field (`n.x = 1`), or the payload itself (`p += 1`), keeps the
//! fact on `p`; `p = q` kills it. A move, a by-value use of a path that is not Copy
//! at a call argument, a binding or the right side of an assignment, kills the facts
//! on the path, or, for a payload, on the nullable it was read from. Calls and
//! borrows kill nothing: [`FnCtxt::record_ref`] records each reference a call
//! argument, a receiver, a copy, a binding, a capture or a hidden argument makes to
//! a proper prefix of a fact's path, or to the path at its nullable type, while a use
//! at the nullable type itself records nothing, and neither does passing a narrowed
//! path at a `&T` (A:898).
//!
//! A read of a path is typed through its facts ([`FnCtxt::narrow_read`],
//! `NarrowedPayload(place, Present, fact)`), except where the expected type is the
//! nullable type; an assignment's target, a null test, `!` and `??` take the path at
//! its declared type ([`FnCtxt::check_place`]); a member receiver also sees a case
//! fact, through one reference or `Box` ([`FnCtxt::narrowed`]).
//!
//! Before a loop's condition, before the arrow arguments of a call and before an
//! arrow's body, a prescan of the syntax kills the facts on every place it changes:
//! assignment, compound and `++`/`--` targets, writes through `*`, `asm` outputs and
//! moves of paths, nested arrows and spread operands included; a name the scanned
//! code declares itself is not the outer one. The states at each loop's `break`s and
//! `continue`s are kept ([`Jumps`]), so the state after a loop is its head's exit
//! joined with every `break` of it (A:908) and a `for` step or a `do` condition runs
//! in the join of the body's end and its `continue`s.

use std::collections::{BTreeMap, BTreeSet};

use enrang_base::{Idx, Span, Symbol, intern};
use enrang_diag::{Code, Diagnostic};
use enrang_hir::{
    self as hir, Adjust, BinOp, ExprKind, Fact, FactId, FactInfo, FactPath, LogOp, LoopId,
    NarrowRecord, Pat, PathStep, RecordKind, Ty, TyKind, UnOp, VariantIdx,
};
use enrang_syntax::ast;

use crate::typeck::{Expect, FnCtxt};

/// The case of a nullable that holds a value: `null` is case 0, a present value case
/// 1, as in the tag layout of SPEC 11.
pub(crate) const PRESENT: VariantIdx = VariantIdx::PRESENT;

/// The facts in force at a point: each path's fact.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct FlowState {
    pub facts: BTreeMap<FactPath, FactId>,
    /// Each fact killed on the way here, with the span of the change that killed it,
    /// which a later rejection of a use typed through it names.
    pub kills: BTreeMap<FactId, Span>,
}

/// The states at each loop's `break`s and `continue`s, by loop, until the loop ends.
#[derive(Clone, Debug, Default)]
pub(crate) struct Jumps {
    pub breaks: BTreeMap<LoopId, Vec<FlowState>>,
    pub continues: BTreeMap<LoopId, Vec<FlowState>>,
}

/// What a prescan looks through for the visible changes it kills facts on.
#[derive(Copy, Clone, Debug)]
pub(crate) enum Prescan<'e> {
    /// A loop body, before the loop's condition.
    Loop(&'e ast::Block),
    /// A `for...of` body, whose binding hides an outer name of its own.
    ForOf(&'e ast::Binding, &'e ast::Block),
    /// A call's arrow arguments, before their bodies.
    Arrows(&'e [ast::Expr]),
    /// An expression every turn of a loop runs: a `for` step, a loop's condition.
    Expr(&'e ast::Expr),
    /// An arrow's body, before it is typed (A:900).
    Arrow(&'e ast::ArrowFn),
}

/// A visible change a prescan found: a place written, or a path moved.
#[derive(Copy, Clone)]
struct Change<'e> {
    target: ChangeAt<'e>,
    moved: bool,
    /// A compound assignment or `++`/`--`, which writes a narrowed nullable's
    /// payload as typing does (plan choice, doc gap: S:744 kills as typing kills).
    payload: bool,
}

/// What a change writes: a place written as an expression, or a name an object
/// pattern's shorthand field assigns (`({ x } = p)`).
#[derive(Copy, Clone)]
enum ChangeAt<'e> {
    Expr(&'e ast::Expr),
    Name(ast::Ident),
}

/// The walk of a prescan: the changes found, and the names the scanned code
/// declares, which hide outer ones from there on.
#[derive(Default)]
struct Scan<'e> {
    changes: Vec<(Change<'e>, Vec<Symbol>)>,
    declared: Vec<Symbol>,
}

impl<'e> Scan<'e> {
    fn change(&mut self, target: &'e ast::Expr, moved: bool) {
        self.changes.push((
            Change {
                target: ChangeAt::Expr(target),
                moved,
                payload: false,
            },
            self.declared.clone(),
        ));
    }

    /// A compound assignment's or `++`/`--`'s target (see [`Change::payload`]).
    fn change_payload(&mut self, target: &'e ast::Expr) {
        self.changes.push((
            Change {
                target: ChangeAt::Expr(target),
                moved: false,
                payload: true,
            },
            self.declared.clone(),
        ));
    }

    fn binding(&mut self, b: &ast::Binding) {
        match b {
            ast::Binding::Name(name) => self.declared.push(name.name),
            ast::Binding::Object { fields, .. } => {
                for (name, sub) in fields {
                    match sub {
                        Some(sub) => self.binding(sub),
                        None => self.declared.push(name.name),
                    }
                }
            }
            ast::Binding::Tuple { elems, .. } => {
                for e in elems {
                    self.binding(e);
                }
            }
        }
    }

    fn block(&mut self, b: &'e ast::Block) {
        let mark = self.declared.len();
        for s in &b.stmts {
            self.stmt(s);
        }
        self.declared.truncate(mark);
    }

    fn stmt(&mut self, s: &'e ast::Stmt) {
        match &s.kind {
            ast::StmtKind::VarDecl(d) => self.var_decl(d),
            ast::StmtKind::If(i) => self.if_stmt(i),
            ast::StmtKind::While(w) | ast::StmtKind::DoWhile(w) => {
                self.expr(&w.cond);
                self.block(&w.body);
            }
            ast::StmtKind::For(f) => {
                let mark = self.declared.len();
                match &f.init {
                    Some(ast::ForInit::VarDecl(d)) => self.var_decl(d),
                    Some(ast::ForInit::Expr(e)) => self.expr(e),
                    None => {}
                }
                if let Some(c) = &f.cond {
                    self.expr(c);
                }
                if let Some(step) = &f.step {
                    self.expr(step);
                }
                self.block(&f.body);
                self.declared.truncate(mark);
            }
            ast::StmtKind::ForOf(f) => {
                match &f.source {
                    ast::ForOfSource::Range(lo, hi) => {
                        self.expr(lo);
                        self.expr(hi);
                    }
                    ast::ForOfSource::Expr(e) => self.value(e),
                }
                let mark = self.declared.len();
                self.binding(&f.binding);
                self.block(&f.body);
                self.declared.truncate(mark);
            }
            ast::StmtKind::Return(e) => {
                if let Some(e) = e {
                    self.expr(e);
                }
            }
            ast::StmtKind::Block(b) | ast::StmtKind::Unsafe(b) => self.block(b),
            ast::StmtKind::Labeled(_, inner) => self.stmt(inner),
            ast::StmtKind::Expr(e) => self.expr(e),
            ast::StmtKind::Expect(x) => {
                self.expr(&x.actual);
                for a in &x.args {
                    if let ast::MatcherArg::Expr(e) = a {
                        self.expr(e);
                    }
                }
            }
            ast::StmtKind::Assert { cond, .. } => self.expr(cond),
            ast::StmtKind::Break(_)
            | ast::StmtKind::Continue(_)
            | ast::StmtKind::LocalFn { .. } => {}
        }
    }

    fn var_decl(&mut self, d: &'e ast::VarDecl) {
        if let Some(init) = &d.init {
            self.value(init);
        }
        self.binding(&d.binding);
    }

    fn if_stmt(&mut self, i: &'e ast::IfStmt) {
        self.expr(&i.cond);
        self.block(&i.then_block);
        match &i.else_branch {
            Some(ast::ElseBranch::Block(b)) => self.block(b),
            Some(ast::ElseBranch::If(inner)) => self.if_stmt(inner),
            None => {}
        }
    }

    /// An expression whose value is taken: a path there moves.
    fn value(&mut self, e: &'e ast::Expr) {
        match &e.kind {
            ast::ExprKind::Paren(inner) => self.value(inner),
            ast::ExprKind::Ternary(c, a, b) => {
                self.expr(c);
                self.value(a);
                self.value(b);
            }
            ast::ExprKind::Ident(_)
            | ast::ExprKind::Member {
                optional: false, ..
            } => {
                self.change(e, true);
                self.expr(e);
            }
            _ => self.expr(e),
        }
    }

    fn arrow(&mut self, a: &'e ast::ArrowFn) {
        let mark = self.declared.len();
        self.declared.extend(a.params.iter().map(|p| p.name.name));
        match &a.body {
            ast::ArrowBody::Expr(e) => self.expr(e),
            ast::ArrowBody::Block(b) => self.block(b),
        }
        self.declared.truncate(mark);
    }

    fn expr(&mut self, e: &'e ast::Expr) {
        match &e.kind {
            ast::ExprKind::Int { .. }
            | ast::ExprKind::Float(_)
            | ast::ExprKind::Str(_)
            | ast::ExprKind::RawTemplate(_)
            | ast::ExprKind::Bool(_)
            | ast::ExprKind::Null
            | ast::ExprKind::Ident(_)
            | ast::ExprKind::This
            | ast::ExprKind::Super
            | ast::ExprKind::TypeMember { .. }
            | ast::ExprKind::SizeForm(_)
            | ast::ExprKind::Error => {}
            ast::ExprKind::Template(parts) => {
                for p in parts {
                    if let ast::TplPart::Expr(e) = p {
                        self.expr(e);
                    }
                }
            }
            ast::ExprKind::Paren(inner)
            | ast::ExprKind::Unary(_, inner)
            | ast::ExprKind::Borrow(inner)
            | ast::ExprKind::Deref(inner)
            | ast::ExprKind::VoidOp(inner)
            | ast::ExprKind::Cast(inner, _)
            | ast::ExprKind::Try(inner)
            | ast::ExprKind::NonNull(inner) => self.expr(inner),
            ast::ExprKind::Array(elems) => {
                for el in elems {
                    match el {
                        ast::ArrayElem::Item(x) => self.value(x),
                        ast::ArrayElem::Spread { expr, .. } => self.expr(expr),
                    }
                }
            }
            ast::ExprKind::Repeat(v, n) => {
                self.value(v);
                self.expr(n);
            }
            ast::ExprKind::New { init, .. } => match init {
                ast::NewInit::Args(args) => {
                    for a in args {
                        self.value(a);
                    }
                }
                ast::NewInit::Fields(fields) => self.fields(fields),
            },
            ast::ExprKind::CaseLit { fields, .. } | ast::ExprKind::ObjectLit(fields) => {
                self.fields(fields)
            }
            ast::ExprKind::Match { subject, arms } => {
                self.expr(subject);
                for arm in arms {
                    for v in &arm.values {
                        match v {
                            ast::ArmValue::Value(x) => self.expr(x),
                            ast::ArmValue::Range(a, b) => {
                                self.expr(a);
                                self.expr(b);
                            }
                            _ => {}
                        }
                    }
                    if let Some(g) = &arm.guard {
                        self.expr(g);
                    }
                    match &arm.body {
                        ast::ArmBody::Expr(x) => self.expr(x),
                        ast::ArmBody::Block(b) => self.block(b),
                        ast::ArmBody::Return(Some(x)) => self.expr(x),
                        _ => {}
                    }
                }
            }
            ast::ExprKind::Asm(asm) => {
                self.expr(&asm.template);
                for option in asm.options.iter().flatten() {
                    match &option.kind {
                        ast::AsmOptionKind::In(regs) => {
                            for r in regs {
                                if let Some(v) = &r.value {
                                    self.expr(v);
                                }
                            }
                        }
                        ast::AsmOptionKind::Out(regs) => {
                            for r in regs {
                                if let Some(v) = &r.value {
                                    self.change(v, false);
                                    self.expr(v);
                                }
                            }
                        }
                        ast::AsmOptionKind::Clobbers(_) => {}
                    }
                }
            }
            ast::ExprKind::Binary(_, a, b) | ast::ExprKind::Logical(_, a, b) => {
                self.expr(a);
                self.expr(b);
            }
            ast::ExprKind::Coalesce(a, b) => {
                self.value(a);
                self.expr(b);
            }
            ast::ExprKind::Ternary(c, a, b) => {
                self.expr(c);
                self.expr(a);
                self.expr(b);
            }
            ast::ExprKind::Assign { op, target, value } => match op {
                ast::AssignOp::Assign => {
                    self.assign_target(target);
                    self.value(value);
                }
                _ => {
                    self.change_payload(target);
                    self.expr(target);
                    self.expr(value);
                }
            },
            ast::ExprKind::IncDec { target, .. } => {
                self.change_payload(target);
                self.expr(target);
            }
            ast::ExprKind::Member { base, .. } => self.expr(base),
            ast::ExprKind::Index(base, index) => {
                self.expr(base);
                self.expr(index);
            }
            ast::ExprKind::Call { callee, args, .. } => {
                self.expr(callee);
                // A form's arguments are borrowed (A:966), anything else's taken.
                let form = matches!(&callee.kind, ast::ExprKind::Member { base, .. }
                    if matches!(base.kind, ast::ExprKind::Ident(n) if n.as_str() == "console"));
                for a in args {
                    match form {
                        true => self.expr(a),
                        false => self.value(a),
                    }
                }
            }
            ast::ExprKind::Arrow(a) => self.arrow(a),
        }
    }

    /// The arrows an argument passes (S:746): itself, parenthesised, or a branch of
    /// a ternary, `??` or `match` that is one.
    fn arrow_arg(&mut self, e: &'e ast::Expr) {
        match &e.kind {
            ast::ExprKind::Paren(inner) => self.arrow_arg(inner),
            ast::ExprKind::Arrow(a) => self.arrow(a),
            ast::ExprKind::Ternary(_, a, b) | ast::ExprKind::Coalesce(a, b) => {
                self.arrow_arg(a);
                self.arrow_arg(b);
            }
            ast::ExprKind::Match { arms, .. } => {
                for arm in arms {
                    if let ast::ArmBody::Expr(x) = &arm.body {
                        self.arrow_arg(x);
                    }
                }
            }
            _ => {}
        }
    }

    /// An assignment's target: each element of a destructuring target `[a, b]`,
    /// nested ones included, is changed (S:744), as a whole target is.
    fn assign_target(&mut self, target: &'e ast::Expr) {
        let mut inner = target;
        while let ast::ExprKind::Paren(e) = &inner.kind {
            inner = e;
        }
        match &inner.kind {
            ast::ExprKind::Array(elems) => {
                for elem in elems {
                    match elem {
                        ast::ArrayElem::Item(item) => self.assign_target(item),
                        ast::ArrayElem::Spread { expr, .. } => self.expr(expr),
                    }
                }
            }
            // An object pattern's targets: `{ x }` assigns `x`, `{ f: t }` the
            // target `t`, nested patterns included.
            ast::ExprKind::ObjectLit(fields) => {
                for f in fields {
                    match &f.value {
                        Some(v) => self.assign_target(v),
                        None => self.changes.push((
                            Change {
                                target: ChangeAt::Name(f.name),
                                moved: false,
                                payload: false,
                            },
                            self.declared.clone(),
                        )),
                    }
                }
            }
            _ => {
                self.change(target, false);
                self.expr(target);
            }
        }
    }

    fn fields(&mut self, fields: &'e [ast::FieldInit]) {
        for f in fields {
            match &f.value {
                Some(v) => self.value(v),
                None => {}
            }
        }
    }
}

/// Whether argument `e` passes an arrow, as [`Scan::arrow_arg`] finds them: then
/// the call prescans its arrow arguments (S:746).
pub(crate) fn holds_arrow(e: &ast::Expr) -> bool {
    match &e.kind {
        ast::ExprKind::Paren(inner) => holds_arrow(inner),
        ast::ExprKind::Arrow(_) => true,
        ast::ExprKind::Ternary(_, a, b) | ast::ExprKind::Coalesce(a, b) => {
            holds_arrow(a) || holds_arrow(b)
        }
        ast::ExprKind::Match { arms, .. } => arms
            .iter()
            .any(|arm| matches!(&arm.body, ast::ArmBody::Expr(x) if holds_arrow(x))),
        _ => false,
    }
}

impl FnCtxt<'_, '_> {
    // -----------------------------------------------------------------------------
    // Paths.

    /// The path of the place `e` is, its own adjusts aside.
    pub(crate) fn place_path(&self, e: &hir::Expr) -> Option<FactPath> {
        let tcx = &*self.sema.tcx;
        let mut path = match &e.kind {
            ExprKind::Local(l) => FactPath {
                root: *l,
                steps: Vec::new(),
            },
            ExprKind::Field(base, field) => {
                if matches!(
                    tcx.kind(self.shallow(self.adjusted_ty(base))),
                    TyKind::Tuple(_)
                ) {
                    // A tuple part is reached by an index (S:739).
                    return None;
                }
                let mut path = self.adjusted_path(base)?;
                path.steps.push(PathStep::Field(*field));
                path
            }
            ExprKind::Deref(base) => {
                match tcx.kind(self.shallow(self.adjusted_ty(base))) {
                    TyKind::Ref(_) | TyKind::Boxed(_) => {}
                    _ => return None,
                }
                let mut path = self.adjusted_path(base)?;
                path.steps.push(PathStep::Deref);
                path
            }
            ExprKind::NarrowedPayload(base, _, _) => {
                let mut path = self.adjusted_path(base)?;
                if matches!(
                    tcx.kind(self.shallow(self.adjusted_ty(base))),
                    TyKind::Nullable(_)
                ) {
                    path.steps.push(PathStep::Payload);
                }
                path
            }
            ExprKind::NonNull(base) => {
                if !matches!(
                    tcx.kind(self.shallow(self.adjusted_ty(base))),
                    TyKind::Nullable(_)
                ) {
                    return None;
                }
                let mut path = self.adjusted_path(base)?;
                path.steps.push(PathStep::Payload);
                path
            }
            _ => return None,
        };
        path.steps.shrink_to_fit();
        Some(path)
    }

    /// The path of the place `e` reaches once its `BoxDeref` adjusts apply; `None`
    /// when another adjust makes it a value first.
    pub(crate) fn adjusted_path(&self, e: &hir::Expr) -> Option<FactPath> {
        let mut path = self.place_path(e)?;
        for adjust in &e.adjust {
            match adjust {
                Adjust::BoxDeref => path.steps.push(PathStep::Deref),
                _ => return None,
            }
        }
        Some(path)
    }

    /// `e`'s type once its `BoxDeref` adjusts apply.
    fn adjusted_ty(&self, e: &hir::Expr) -> Ty {
        let mut t = e.ty;
        for adjust in &e.adjust {
            if *adjust != Adjust::BoxDeref {
                break;
            }
            if let TyKind::Boxed(inner) = self.sema.tcx.kind(self.shallow(t)) {
                t = inner;
            }
        }
        t
    }

    /// The place a fact on `e` sits on: `e`'s path, then one `Deref` for each
    /// reference or `Box` around the value, with the value's type.
    fn value_place(&self, e: &hir::Expr) -> Option<(FactPath, Ty)> {
        let mut path = self.adjusted_path(e)?;
        let mut t = self.shallow(self.adjusted_ty(e));
        // Every round strips one reference or `Box`; a type is finite, so this
        // ends without a depth cap (a cap would put the fact on a shallower place).
        loop {
            match self.sema.tcx.kind(t) {
                TyKind::Ref(inner) | TyKind::Boxed(inner) => {
                    path.steps.push(PathStep::Deref);
                    t = self.shallow(inner);
                }
                _ => break,
            }
        }
        Some((path, t))
    }

    /// Whether `t` is an enum, `Result` included.
    fn is_enum(&self, t: Ty) -> bool {
        let tcx = &*self.sema.tcx;
        match tcx.kind(t) {
            TyKind::Adt(adt, _) => tcx.adt(adt).as_enum().is_some(),
            _ => false,
        }
    }

    fn is_nullable(&self, t: Ty) -> bool {
        matches!(self.sema.tcx.kind(self.shallow(t)), TyKind::Nullable(_))
    }

    // -----------------------------------------------------------------------------
    // Facts.

    /// Adds `fact` on `path` to `state`, made by the test at `span`; a path already
    /// holding that fact keeps it. A condition's facts are read again once all of it
    /// is typed (`a && b` gives `b` the facts of `a`, then the whole its facts), and a
    /// test read again makes the same fact, which a change typed since, in `b`, has
    /// killed: then it gives none.
    fn add_fact(&mut self, state: &mut FlowState, path: FactPath, fact: Fact, span: Span) {
        if let Some(&id) = state.facts.get(&path)
            && self.facts[id].fact == fact
        {
            // Phase 3 counts the test as a new one of the fact it keeps (S:742).
            let info = &mut self.facts[id];
            if info.span != span && !info.retests.contains(&span) {
                info.retests.push(span);
            }
            return;
        }
        let made = self
            .facts
            .iter_enumerated()
            .find(|(_, f)| f.path == path && f.fact == fact && f.span == span)
            .map(|(id, _)| id);
        let id = match made {
            Some(id) if state.kills.contains_key(&id) => return,
            Some(id) => id,
            None => self.facts.push(FactInfo {
                path: path.clone(),
                fact,
                span,
                retests: Vec::new(),
            }),
        };
        state.facts.insert(path, id);
    }

    /// The fact in force on `path`, if it is `fact`'s kind (any case for a case).
    fn fact_at(&self, path: &FactPath, nonnull: bool) -> Option<(Fact, FactId)> {
        let &id = self.flow.facts.get(path)?;
        let fact = self.facts[id].fact;
        match (fact, nonnull) {
            (Fact::NonNull, true) | (Fact::Case(_), false) => Some((fact, id)),
            _ => None,
        }
    }

    /// Whether fact `id` is in force.
    fn holds(&self, id: FactId) -> bool {
        self.flow.facts.values().any(|&f| f == id)
    }

    /// Kills every fact on `prefix` and deeper but those in `keep`, naming `span` as
    /// the change.
    fn kill_under(&mut self, prefix: &FactPath, span: Span, keep: &BTreeSet<FactId>) {
        let doomed: Vec<(FactPath, FactId)> = self
            .flow
            .facts
            .iter()
            .filter(|(p, id)| {
                (*p == prefix || prefix.is_proper_prefix_of(p)) && !keep.contains(*id)
            })
            .map(|(p, id)| (p.clone(), *id))
            .collect();
        for (path, id) in doomed {
            self.flow.facts.remove(&path);
            self.flow.kills.insert(id, span);
        }
    }

    /// Kills every fact on `path` and deeper, naming `span` as the change.
    pub(crate) fn kill_path(&mut self, path: &FactPath, span: Span) {
        self.kill_under(path, span, &BTreeSet::new());
    }

    /// The facts the test `cond` gives when true and when false, from `base`.
    fn facts_of(&mut self, cond: &hir::Expr, base: FlowState) -> (FlowState, FlowState) {
        match &cond.kind {
            ExprKind::Unary(UnOp::Not, inner) => {
                let (t, f) = self.facts_of(inner, base);
                (f, t)
            }
            ExprKind::Logical(LogOp::And, a, b) => {
                let (ta, fa) = self.facts_of(a, base);
                let (tb, fb) = self.facts_of(b, ta);
                (tb, self.intersect(vec![fa, fb]))
            }
            ExprKind::Logical(LogOp::Or, a, b) => {
                let (ta, fa) = self.facts_of(a, base);
                let (tb, fb) = self.facts_of(b, fa);
                (self.intersect(vec![ta, tb]), fb)
            }
            ExprKind::Binary(op @ (BinOp::Eq | BinOp::Ne), a, b) => {
                let tested = match (&a.kind, &b.kind) {
                    (_, ExprKind::NullLit) => Some(&**a),
                    (ExprKind::NullLit, _) => Some(&**b),
                    _ => None,
                };
                let Some(path) = tested.and_then(|t| self.tested_path(t)) else {
                    return (base.clone(), base);
                };
                let mut with = base.clone();
                self.add_fact(&mut with, path, Fact::NonNull, cond.span);
                match op {
                    BinOp::Ne => (with, base),
                    _ => (base, with),
                }
            }
            _ => (base.clone(), base),
        }
    }

    /// The place a null test of `e` tests: `e`'s, or for an assignment tested in
    /// place its target's (S:741); `None` when it is no path of a nullable.
    fn tested_path(&self, e: &hir::Expr) -> Option<FactPath> {
        let place = match &e.kind {
            ExprKind::Assign {
                op: None, target, ..
            } => &**target,
            _ => e,
        };
        let (path, t) = self.value_place(place)?;
        matches!(self.sema.tcx.kind(t), TyKind::Nullable(_)).then_some(path)
    }

    // -----------------------------------------------------------------------------
    // The seams of plan h.2.

    /// The states after `cond` is true and after it is false (S:741).
    pub(crate) fn cond_facts(&mut self, cond: &hir::Expr) -> (FlowState, FlowState) {
        let base = self.flow.clone();
        self.facts_of(cond, base)
    }

    /// Kills the facts a write to `place` changes: those on its path and deeper
    /// (S:742).
    pub(crate) fn kill_write(&mut self, place: &hir::Expr) {
        if let Some(path) = self.adjusted_path(place) {
            self.kill_under(&path, place.span, &BTreeSet::new());
        }
    }

    /// Records each reference `e` makes, as `kind`, to a proper prefix of a fact's
    /// path or to the path at its nullable type (A:898); a call argument, binding or
    /// copy that takes a path that is not Copy moves it, which kills its facts.
    pub(crate) fn record_ref(&mut self, e: &hir::Expr, kind: RecordKind) {
        if matches!(kind, RecordKind::Capture | RecordKind::HiddenArg) {
            // The variable itself, at its declared type.
            if let ExprKind::Local(local) = e.kind {
                let facts: Vec<FactId> = self
                    .flow
                    .facts
                    .iter()
                    .filter(|(p, _)| p.root == local)
                    .map(|(_, id)| *id)
                    .collect();
                for fact in facts {
                    self.push_record(fact, e, kind);
                }
            }
            return;
        }
        match self.referenced(e, kind) {
            Some((path, nullable)) => self.record_against(&path, nullable, e, kind),
            None if kind != RecordKind::Receiver => self.kill_move(e),
            None => {}
        }
    }

    /// The items of an array or tuple literal, and the field values of a named
    /// form, case literal or object literal, go into the new value: each moves
    /// its path when it is not Copy, which kills its facts, or is recorded as a
    /// copy when it is a reference to one (S:742).
    pub(crate) fn moved_into(&mut self, lit: &hir::Expr) {
        let items: Vec<&hir::Expr> = match &lit.kind {
            ExprKind::ArrayLit(items) | ExprKind::TupleLit(items) => items.iter().collect(),
            ExprKind::ArrayBuild { parts, .. } => parts
                .iter()
                .filter_map(|p| match p {
                    hir::ArrayPart::Item(e) => Some(e),
                    hir::ArrayPart::Spread(..) => None,
                })
                .collect(),
            ExprKind::NewNamed { fields, .. } => fields.iter().map(|(_, e)| e).collect(),
            ExprKind::VariantLit { fields, .. } | ExprKind::ObjectLit { fields, .. } => {
                fields.iter().collect()
            }
            _ => Vec::new(),
        };
        let items: Vec<hir::Expr> = items.into_iter().cloned().collect();
        for item in &items {
            self.record_ref(item, RecordKind::Copy);
        }
    }

    /// `place` as its facts type it for a member lookup (`NarrowedPayload`): a
    /// non-null nullable as its payload, then an enum in a `match` arm as its case,
    /// through one reference or `Box` each.
    pub(crate) fn narrowed(&mut self, place: hir::Expr) -> hir::Expr {
        self.narrow_place(place, true)
    }

    /// Enters an arm whose case is `fact` for `subject`'s path; returns the state to
    /// restore after the arm. On a nullable subject a case arm also makes it
    /// non-null (S:1133).
    pub(crate) fn enter_arm(&mut self, subject: &hir::Expr, fact: Fact) -> FlowState {
        let saved = self.flow.clone();
        let Some((path, t)) = self.value_place(subject) else {
            return saved;
        };
        let mut state = std::mem::take(&mut self.flow);
        match (fact, self.sema.tcx.kind(t)) {
            (Fact::Case(case), TyKind::Nullable(inner)) => {
                self.add_fact(&mut state, path.clone(), Fact::NonNull, subject.span);
                let mut inner_path = path;
                inner_path.steps.push(PathStep::Payload);
                let mut inner = self.shallow(inner);
                while let TyKind::Ref(i) | TyKind::Boxed(i) = self.sema.tcx.kind(inner) {
                    inner_path.steps.push(PathStep::Deref);
                    inner = self.shallow(i);
                }
                if self.is_enum(inner) {
                    self.add_fact(&mut state, inner_path, Fact::Case(case), subject.span);
                }
            }
            (Fact::Case(case), _) if self.is_enum(t) => {
                self.add_fact(&mut state, path, Fact::Case(case), subject.span);
            }
            (Fact::NonNull, TyKind::Nullable(_)) => {
                self.add_fact(&mut state, path, Fact::NonNull, subject.span);
            }
            _ => {}
        }
        self.flow = state;
        saved
    }

    /// Kills, ahead of `ast`, the facts its visible changes change (A:900).
    pub(crate) fn prescan_kill(&mut self, ast: Prescan<'_>) {
        self.prescan_kill_except(ast, &BTreeSet::new());
    }

    /// Joins the states of branches that meet: a fact holds after only if it holds on
    /// every branch.
    pub(crate) fn join(&mut self, states: Vec<FlowState>) {
        if states.is_empty() {
            return;
        }
        self.flow = self.intersect(states);
    }

    /// The facts every state of `states` holds (A:898: `FactSet`s intersect by
    /// path and fact), each under the identity the first state gives it; the kills
    /// of any.
    pub(crate) fn intersect(&self, states: Vec<FlowState>) -> FlowState {
        let mut states = states.into_iter();
        let Some(mut joined) = states.next() else {
            return FlowState::default();
        };
        for state in states {
            joined.facts.retain(|path, id| {
                state
                    .facts
                    .get(path)
                    .is_some_and(|other| self.facts[*other].fact == self.facts[*id].fact)
            });
            for (id, span) in state.kills {
                joined.kills.entry(id).or_insert(span);
            }
        }
        joined
    }

    // -----------------------------------------------------------------------------
    // Reads.

    /// A path read as a value, typed through its facts (S:747): a nullable whose
    /// non-null fact holds is its payload, unless the expected type is itself a
    /// nullable, where the use records nothing (A:898).
    pub(crate) fn narrow_read(&mut self, e: hir::Expr, ex: Expect) -> hir::Expr {
        if let Some(t) = ex.ty()
            && self.is_nullable(t)
        {
            return e;
        }
        if !self.is_nullable(e.ty) {
            return e;
        }
        self.narrow_place(e, false)
    }

    /// `e` typed against `ex` (no coercion site) as the place it names, at its
    /// declared type: an assignment's target, a null test, `!`, `??`.
    pub(crate) fn check_place(&mut self, e: &ast::Expr, ex: Expect) -> hir::Expr {
        let typed = self.check_expr(e, ex);
        match typed.kind {
            ExprKind::NarrowedPayload(place, _, _) if typed.adjust.is_empty() => *place,
            _ => typed,
        }
    }

    fn narrow_place(&mut self, place: hir::Expr, receiver: bool) -> hir::Expr {
        let mut e = place;
        // Every round that does not return strips one `| null` or one reference
        // or `Box`, so this ends without a depth cap.
        loop {
            let Some(path) = self.adjusted_path(&e) else {
                return e;
            };
            let t = self.shallow(self.adjusted_ty(&e));
            match self.sema.tcx.kind(t) {
                TyKind::Nullable(inner) => match self.fact_at(&path, true) {
                    Some((_, id)) => {
                        let span = e.span;
                        let inner = self.shallow(inner);
                        e = self.mk_expr(
                            inner,
                            span,
                            ExprKind::NarrowedPayload(Box::new(e), PRESENT, id),
                        );
                    }
                    None => return e,
                },
                _ if !receiver => return e,
                TyKind::Ref(inner) | TyKind::Boxed(inner) => {
                    let mut deeper = path;
                    deeper.steps.push(PathStep::Deref);
                    let inner = self.shallow(inner);
                    let applies = match self.sema.tcx.kind(inner) {
                        TyKind::Nullable(_) => self.fact_at(&deeper, true).is_some(),
                        _ if self.is_enum(inner) => self.fact_at(&deeper, false).is_some(),
                        _ => false,
                    };
                    if !applies {
                        return e;
                    }
                    let span = e.span;
                    e = self.mk_expr(inner, span, ExprKind::Deref(Box::new(e)));
                }
                _ if self.is_enum(t) => {
                    return match self.fact_at(&path, false) {
                        Some((Fact::Case(case), id)) => {
                            let span = e.span;
                            self.mk_expr(t, span, ExprKind::NarrowedPayload(Box::new(e), case, id))
                        }
                        _ => e,
                    };
                }
                _ => return e,
            }
        }
    }

    /// A value read through the reference path `e` (`p: &(T | null)`) whose
    /// referent a fact narrows (`p != null` compares through it, S:684): the
    /// payload `T`, read as operators and C08 read through one reference (S:739).
    /// `e` itself otherwise.
    pub(crate) fn read_narrowed(&mut self, e: hir::Expr) -> hir::Expr {
        let Some(mut path) = self.adjusted_path(&e) else {
            return e;
        };
        let TyKind::Ref(inner) = self.sema.tcx.kind(self.shallow(self.adjusted_ty(&e))) else {
            return e;
        };
        let inner = self.shallow(inner);
        let TyKind::Nullable(payload) = self.sema.tcx.kind(inner) else {
            return e;
        };
        let payload = self.shallow(payload);
        let tcx = &*self.sema.tcx;
        if !(tcx.kind(payload) == TyKind::Str || tcx.is_copy(payload, &self.env)) {
            return e;
        }
        path.steps.push(PathStep::Deref);
        let Some((_, id)) = self.fact_at(&path, true) else {
            return e;
        };
        let span = e.span;
        let referent = self.mk_expr(inner, span, ExprKind::Deref(Box::new(e)));
        self.mk_expr(
            payload,
            span,
            ExprKind::NarrowedPayload(Box::new(referent), PRESENT, id),
        )
    }

    // -----------------------------------------------------------------------------
    // Records and moves.

    /// The place a reference that `e` makes or carries refers to, and whether it
    /// reaches that place at its nullable type; `None` when `e` is a value, copied
    /// or moved.
    fn referenced(&self, e: &hir::Expr, kind: RecordKind) -> Option<(FactPath, bool)> {
        let tcx = &*self.sema.tcx;
        if e.adjust
            .iter()
            .any(|a| matches!(a, Adjust::ReadThrough | Adjust::ReadThroughNullable))
        {
            return None;
        }
        if let ExprKind::Borrow(inner) = &e.kind {
            let path = self.adjusted_path(inner)?;
            return Some((path, self.is_nullable(self.adjusted_ty(inner))));
        }
        if let Some(at) = e.adjust.iter().position(|a| *a == Adjust::AutoBorrow) {
            let mut path = self.place_path(e)?;
            let mut t = self.shallow(e.ty);
            for adjust in &e.adjust[..at] {
                if *adjust != Adjust::BoxDeref {
                    return None;
                }
                path.steps.push(PathStep::Deref);
                if let TyKind::Boxed(inner) = tcx.kind(t) {
                    t = self.shallow(inner);
                }
            }
            return Some((path, self.is_nullable(t)));
        }
        let t = self.shallow(self.adjusted_ty(e));
        match tcx.kind(t) {
            TyKind::Ref(inner) => {
                let mut path = self.adjusted_path(e)?;
                path.steps.push(PathStep::Deref);
                Some((path, self.is_nullable(inner)))
            }
            TyKind::Nullable(inner) if matches!(tcx.kind(self.shallow(inner)), TyKind::Ref(_)) => {
                let TyKind::Ref(pointee) = tcx.kind(self.shallow(inner)) else {
                    return None;
                };
                let mut path = self.adjusted_path(e)?;
                path.steps.push(PathStep::Payload);
                path.steps.push(PathStep::Deref);
                Some((path, self.is_nullable(pointee)))
            }
            _ if kind == RecordKind::Receiver => {
                let path = self.adjusted_path(e)?;
                Some((path, self.is_nullable(t)))
            }
            _ => None,
        }
    }

    /// Records `e` against each fact whose path `path` is a proper prefix of, or is,
    /// when the reference reaches it at its nullable type or the fact is a case,
    /// which any reference to the enum itself may change (I6).
    fn record_against(&mut self, path: &FactPath, nullable: bool, e: &hir::Expr, kind: RecordKind) {
        let facts: Vec<FactId> = self
            .flow
            .facts
            .iter()
            .filter(|(p, id)| {
                path.is_proper_prefix_of(p)
                    || (*p == path && (nullable || matches!(self.facts[**id].fact, Fact::Case(_))))
            })
            .map(|(_, id)| *id)
            .collect();
        for fact in facts {
            self.push_record(fact, e, kind);
        }
    }

    fn push_record(&mut self, fact: FactId, e: &hir::Expr, kind: RecordKind) {
        let known = self
            .records
            .iter()
            .any(|r| r.fact == fact && r.expr == e.id && r.kind == kind);
        if !known {
            self.records.push(NarrowRecord {
                fact,
                expr: e.id,
                kind,
                span: e.span,
            });
        }
    }

    /// A by-value use of the path `e` that is not Copy moves it, killing the facts on
    /// it, or on the nullable whose payload it is (S:742).
    pub(crate) fn kill_move(&mut self, e: &hir::Expr) {
        let Some(mut path) = self.adjusted_path(e) else {
            return;
        };
        let t = self.resolve(self.adjusted_ty(e));
        let tcx = &*self.sema.tcx;
        if tcx.has_infer(t) || tcx.is_copy(t, &self.env) {
            return;
        }
        while path.steps.last() == Some(&PathStep::Payload) {
            path.steps.pop();
        }
        self.kill_under(&path, e.span, &BTreeSet::new());
    }

    // -----------------------------------------------------------------------------
    // Prescans.

    /// [`Self::prescan_kill`], sparing the facts in `keep` (a `for...of` loop's
    /// source facts, A:904).
    pub(crate) fn prescan_kill_except(&mut self, ast: Prescan<'_>, keep: &BTreeSet<FactId>) {
        let mut scan = Scan::default();
        match ast {
            Prescan::Loop(b) => scan.block(b),
            Prescan::ForOf(binding, b) => {
                scan.binding(binding);
                scan.block(b);
            }
            Prescan::Arrows(args) => {
                for a in args {
                    scan.arrow_arg(a);
                }
            }
            Prescan::Expr(e) => scan.expr(e),
            Prescan::Arrow(a) => scan.arrow(a),
        }
        for (change, declared) in scan.changes {
            let (found, span) = match change.target {
                ChangeAt::Expr(e) => (self.ast_path(e, &declared), e.span),
                ChangeAt::Name(name) => (self.name_path(name.name, &declared), name.span),
            };
            let Some((mut path, ty)) = found else {
                continue;
            };
            if change.payload && self.is_nullable(self.resolve(ty)) {
                path.steps.push(PathStep::Payload);
            }
            if change.moved {
                let t = self.resolve(ty);
                let tcx = &*self.sema.tcx;
                if tcx.has_infer(t) || tcx.is_copy(t, &self.env) {
                    continue;
                }
                while path.steps.last() == Some(&PathStep::Payload) {
                    path.steps.pop();
                }
            }
            self.kill_under(&path, span, keep);
        }
    }

    /// The path of the local `name` names, with its type; `None` when no local of
    /// that name is in scope, or the scanned code declares it.
    fn name_path(&self, name: Symbol, declared: &[Symbol]) -> Option<(FactPath, Ty)> {
        if declared.contains(&name) {
            return None;
        }
        let local = self.scopes.lookup(name)?;
        Some((
            FactPath {
                root: local,
                steps: Vec::new(),
            },
            self.locals[local].ty,
        ))
    }

    /// The path an AST place names, resolved through the types of the locals in
    /// scope here, with its type; `None` for what is no path, or names a local
    /// `declared` in the scanned code.
    fn ast_path(&self, e: &ast::Expr, declared: &[Symbol]) -> Option<(FactPath, Ty)> {
        let tcx = &*self.sema.tcx;
        let root = |name: Symbol| self.name_path(name, declared);
        match &e.kind {
            ast::ExprKind::Paren(inner) => self.ast_path(inner, declared),
            ast::ExprKind::Ident(name) => root(*name),
            ast::ExprKind::This => root(intern("this")),
            ast::ExprKind::Member {
                base,
                name,
                optional: false,
            } => {
                let (mut path, mut ty) = self.ast_path(base, declared)?;
                // Every round that does not return strips one reference, `Box`
                // or `| null`, so this ends without a depth cap.
                loop {
                    let t = self.shallow(ty);
                    match tcx.kind(t) {
                        TyKind::Ref(inner) | TyKind::Boxed(inner) => {
                            path.steps.push(PathStep::Deref);
                            ty = inner;
                        }
                        TyKind::Nullable(inner) => {
                            path.steps.push(PathStep::Payload);
                            ty = inner;
                        }
                        TyKind::Adt(adt, args) => {
                            let class = tcx.adt(adt).as_class()?;
                            let (field, _) = class.field_named(name.name)?;
                            path.steps.push(PathStep::Field(field));
                            return Some((path, tcx.field_ty(adt, None, field, args)));
                        }
                        TyKind::Object(shape) => {
                            let shape = tcx.shape(shape);
                            let i = shape.position(name.name)?;
                            path.steps.push(PathStep::Field(hir::FieldIdx::new(i)));
                            return Some((path, shape.fields[i].1));
                        }
                        _ => return None,
                    }
                }
            }
            ast::ExprKind::Deref(inner) => {
                let (mut path, ty) = self.ast_path(inner, declared)?;
                let mut t = self.shallow(ty);
                if let TyKind::Nullable(payload) = tcx.kind(t) {
                    path.steps.push(PathStep::Payload);
                    t = self.shallow(payload);
                }
                match tcx.kind(t) {
                    TyKind::Ref(pointee) | TyKind::Boxed(pointee) => {
                        path.steps.push(PathStep::Deref);
                        Some((path, pointee))
                    }
                    _ => None,
                }
            }
            ast::ExprKind::NonNull(inner) => {
                let (mut path, ty) = self.ast_path(inner, declared)?;
                match tcx.kind(self.shallow(ty)) {
                    TyKind::Nullable(payload) => {
                        path.steps.push(PathStep::Payload);
                        Some((path, payload))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    // -----------------------------------------------------------------------------
    // Loops, arms and arrows.

    /// Keeps the state at a `break` (or a `continue`) of loop `id`, when it is
    /// reached.
    pub(crate) fn record_jump(&mut self, id: LoopId, is_break: bool) {
        if !self.reachable {
            return;
        }
        let state = self.flow.clone();
        let map = match is_break {
            true => &mut self.jumps.breaks,
            false => &mut self.jumps.continues,
        };
        map.entry(id).or_default().push(state);
    }

    /// The state a `for` step or a `do` condition of loop `id` runs in: the join of
    /// the body's end, when reached, and every `continue` of the loop.
    pub(crate) fn back_edge(&mut self, id: LoopId) {
        let mut states = Vec::new();
        if self.reachable {
            states.push(self.flow.clone());
        }
        states.extend(self.jumps.continues.remove(&id).unwrap_or_default());
        self.join(states);
    }

    /// The state after loop `id`: its head's exit state, when the head can exit,
    /// joined with every `break` of the loop (A:908).
    pub(crate) fn loop_exit(&mut self, id: LoopId, head: Option<FlowState>) {
        let mut states: Vec<FlowState> = head.into_iter().collect();
        states.extend(self.jumps.breaks.remove(&id).unwrap_or_default());
        self.jumps.continues.remove(&id);
        self.join(states);
    }

    /// After an unguarded `null` arm, the later arms see the subject without `null`
    /// (S:1135): its non-null fact joins the current state.
    pub(crate) fn null_arm(&mut self, subject: &hir::Expr) {
        let Some((path, t)) = self.value_place(subject) else {
            return;
        };
        if matches!(self.sema.tcx.kind(t), TyKind::Nullable(_)) {
            let mut state = std::mem::take(&mut self.flow);
            self.add_fact(&mut state, path, Fact::NonNull, subject.span);
            self.flow = state;
        }
    }

    /// Before an arrow's body: kills, for the body only, the facts on the places it
    /// changes, since it may run at any later point (S:746); returns the state to
    /// restore once it is typed.
    pub(crate) fn enter_arrow(&mut self, a: &ast::ArrowFn) -> FlowState {
        let saved = self.flow.clone();
        self.prescan_kill(Prescan::Arrow(a));
        saved
    }

    /// After an arrow: the state before it, and a `Capture` record for each local it
    /// captures, made at the arrow.
    pub(crate) fn exit_arrow(&mut self, saved: FlowState, typed: &hir::Expr) {
        self.flow = saved;
        let ExprKind::Arrow(id) = typed.kind else {
            return;
        };
        let Some(arrow) = self.arrows.get(id) else {
            return;
        };
        let captures: Vec<hir::Capture> = arrow.captures.clone();
        for capture in captures {
            let ty = self.locals[capture.local].ty;
            let at = hir::Expr::new(typed.id, ty, capture.span, ExprKind::Local(capture.local));
            self.record_ref(&at, RecordKind::Capture);
        }
    }

    /// Marks every local `pat` binds as `let` when `mutable`.
    pub(crate) fn set_pattern_mutable(&mut self, pat: &Pat, mutable: bool) {
        if !mutable {
            return;
        }
        match pat {
            Pat::Bind(local) => self.locals[*local].mutable = true,
            Pat::Object(fields) => {
                for (_, p) in fields {
                    self.set_pattern_mutable(p, mutable);
                }
            }
            Pat::Tuple(parts) => {
                for p in parts {
                    self.set_pattern_mutable(p, mutable);
                }
            }
            Pat::Place(_) => {}
        }
    }

    // -----------------------------------------------------------------------------
    // Uses after a kill (O6).

    /// A call's receiver, typed through facts before its arguments, used after them
    /// (A:898): EN0401 with a note naming the argument when one killed a fact it was
    /// typed through.
    pub(crate) fn recheck_receiver(&mut self, narrowed: &hir::Expr) {
        let args: Vec<Span> = self
            .calls
            .last()
            .map(|c| c.args.clone())
            .unwrap_or_default();
        self.recheck(narrowed, &args, "argument");
    }

    /// An assignment's place, typed through facts before its right side `rhs` and
    /// stored after it (O6): EN0401 with a note when the right side killed one.
    pub(crate) fn recheck_place(&mut self, place: &hir::Expr, rhs: Span) {
        self.recheck(place, &[rhs], "right-hand side");
    }

    fn recheck(&mut self, e: &hir::Expr, by: &[Span], what: &str) {
        let mut at = e;
        loop {
            match &at.kind {
                ExprKind::NarrowedPayload(inner, variant, id) => {
                    if !self.holds(*id) {
                        self.report_lost(at, inner, *variant, *id, by, what);
                        return;
                    }
                    at = inner;
                }
                ExprKind::Field(inner, _) | ExprKind::Deref(inner) | ExprKind::NonNull(inner) => {
                    at = inner;
                }
                _ => return,
            }
        }
    }

    /// EN0401 at `inner`, typed as `narrowed` through fact `id`, which a change in
    /// one of `by` killed.
    fn report_lost(
        &mut self,
        narrowed: &hir::Expr,
        inner: &hir::Expr,
        variant: VariantIdx,
        id: FactId,
        by: &[Span],
        what: &str,
    ) {
        let found = self.ty_str(inner.ty);
        let expected = match self.facts[id].fact {
            Fact::NonNull => self.ty_str(narrowed.ty),
            Fact::Case(_) => {
                let tcx = &*self.sema.tcx;
                let case = match tcx.kind(self.shallow(narrowed.ty)) {
                    TyKind::Adt(adt, _) => tcx
                        .adt(adt)
                        .as_enum()
                        .and_then(|e| e.variants.get(variant.0 as usize))
                        .map(|v| v.name.to_string()),
                    _ => None,
                };
                match case {
                    Some(case) => format!("{found}.{case}"),
                    None => found.clone(),
                }
            }
        };
        let place = self.snippet(inner.span);
        let mut diag = Diagnostic::new(
            Code::EN0401,
            format!("mismatched types: expected `{expected}`, found `{found}`"),
            inner.span,
            format!("this is `{found}` here"),
        );
        let kill = self.flow.kills.get(&id).copied();
        if let Some(kill) = kill
            && let Some(by) = by.iter().find(|s| s.lo <= kill.lo && kill.hi <= s.hi)
        {
            diag = diag.note(format!(
                "the {what} `{}` changes `{place}` before this use",
                self.snippet(*by)
            ));
        }
        self.sema.emit(diag);
    }
}
