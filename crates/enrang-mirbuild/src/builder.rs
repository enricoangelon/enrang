//! The body under construction and its CFG helpers (M3 plan c.1, g.2): locals from
//! HIR locals, a local function's hidden arguments (K7), the supplied-count
//! argument (A:937), temporaries, blocks, the cursor and its `unsafe` region, and
//! the expression points narrowing records map to (c.20).

use std::collections::BTreeMap;

use enrang_base::{BytePos, Span, intern};
use enrang_diag::{DiagCtx, Diagnostic};
use enrang_hir::{self as hir, ExprId, FactId, ParamEnv, PathStep, TopVar, Ty, TyKind};
use enrang_mir::{
    Block, BlockId, Body, BodyNames, BodyOwner, Local, LocalDecl, LocalKind, MirFact, MirRecord,
    Operand, Place, Point, Proj, RegionId, Rvalue, Statement, StatementKind, Terminator,
    TerminatorKind, UnsafeKind, UnsafeRegion,
};

use crate::BuildCx;
use crate::scope::{Entry, ExitTarget, Scope, ScopeKind};

/// One body being built.
pub struct Builder<'a> {
    pub cx: &'a BuildCx<'a>,
    pub hir: &'a hir::Body,
    pub body: Body,
    pub locals: BTreeMap<hir::LocalId, Local>,
    /// The block statements go into; `None` after a terminator.
    pub cursor: Option<BlockId>,
    pub scopes: Vec<Scope>,
    /// Where each expression a narrowing record names was lowered (plan c.20).
    pub expr_points: BTreeMap<ExprId, Point>,
    pub diags: Vec<Diagnostic>,
    /// The innermost `unsafe` region new statements lie in (A:560).
    pub region: Option<RegionId>,
    /// The bounds in force: the owner's `where` clause.
    pub env: ParamEnv,
    /// A local function's hidden arguments, by top-level variable (K7).
    pub hidden: BTreeMap<TopVar, Local>,
    /// The fact each narrowed case projection was made from (c.4, c.20).
    pub facts_of: BTreeMap<Place, FactId>,
    /// The points of hidden-argument records, by index in the HIR's records.
    pub record_points: BTreeMap<usize, Point>,
    /// The payload place of an optional call's base, already evaluated and
    /// narrowed, by the base's expression: its receiver's `!` reads it (c.7).
    pub payloads: BTreeMap<ExprId, Place>,
    /// The exact-class check the borrow that is argument expression `ExprId`
    /// makes on its object, a `mem.replace` or `mem.swap` argument's (A:943).
    pub borrow_check: Option<(enrang_mir::ClassOp, ExprId)>,
    /// The destructured expression of the declaration being bound: its
    /// `Binding` records go on the reference bindings that reach their facts
    /// (S:744, c.20).
    pub destructure: Option<ExprId>,
    /// The temporaries that have had a value: a temporary is created when it first
    /// gets one, which is when its scope entry takes its place (S 5.7 D2).
    pub valued: std::collections::BTreeSet<Local>,
}

impl<'a> Builder<'a> {
    /// A builder for `hir` (plan c.1): `_0`, its parameters (`this` first), a local
    /// function's hidden arguments, then `#supplied` when a parameter has a default.
    pub fn new(cx: &'a BuildCx<'a>, hir: &'a hir::Body) -> Builder<'a> {
        let tcx = cx.tcx;
        let (owner, def) = match hir.owner {
            hir::BodyOwner::Fn(d) => (BodyOwner::Fn(d), Some(d)),
            hir::BodyOwner::Statements(m) => (BodyOwner::Statements(m), None),
            hir::BodyOwner::Test(d) | hir::BodyOwner::Const(d) => (BodyOwner::Test(d), None),
        };
        let sig = def.and_then(|d| tcx.sig_opt(d));
        let mut b = Builder {
            cx,
            hir,
            body: Body::new(owner, hir.ret, hir.span),
            locals: BTreeMap::new(),
            cursor: None,
            scopes: Vec::new(),
            expr_points: BTreeMap::new(),
            diags: Vec::new(),
            region: None,
            env: ParamEnv {
                bounds: sig.map(|s| s.where_bounds.clone()).unwrap_or_default(),
            },
            hidden: BTreeMap::new(),
            facts_of: BTreeMap::new(),
            record_points: BTreeMap::new(),
            payloads: BTreeMap::new(),
            borrow_check: None,
            destructure: None,
            valued: std::collections::BTreeSet::new(),
        };
        // The statements' `args` (SPEC 7) holds its value from the entry on, as
        // a parameter does: their one argument.
        let args = hir.locals.iter_enumerated().find_map(|(l, d)| {
            (d.kind == hir::LocalKind::TopVar(TopVar(0)) && d.span.is_dummy()).then_some(l)
        });
        for &p in hir.params.iter().chain(&args) {
            let l = b.declare(p, LocalKind::Arg);
            b.locals.insert(p, l);
        }
        let vars = def.and_then(|d| cx.program.hidden_args.get(&d));
        for &v in vars.into_iter().flatten() {
            let info = &cx.program.top_vars[v.0 as usize];
            let ty = match tcx.kind(info.ty) {
                TyKind::Ref(_) => info.ty,
                TyKind::Nullable(t) if matches!(tcx.kind(t), TyKind::Ref(_)) => info.ty,
                _ => tcx.mk_ref(info.ty),
            };
            let l = b.new_local(ty, LocalKind::Arg, Some(info.name), info.span);
            b.hidden.insert(v, l);
        }
        if sig.is_some_and(|s| s.params.iter().any(|p| p.has_default)) {
            let isize = tcx.common().isize;
            let l = b.new_local(isize, LocalKind::Arg, Some(intern("#supplied")), hir.span);
            b.body.meta.defaults_count = Some(l);
        }
        b.body.arg_count = b.body.locals.len() as u32 - 1;
        let unsafe_body =
            def.is_some_and(|d| sig.is_some_and(|s| s.unsafety) || tcx.def(d).attrs.naked);
        if unsafe_body {
            b.region = Some(b.body.unsafe_regions.push(UnsafeRegion {
                kind: UnsafeKind::WholeBody,
                parent: None,
                span: hir.span,
            }));
        }
        let entry = b.new_block();
        b.switch_to(entry);
        b
    }

    /// Builds `hir`: the prologue (a constructor's, parameter defaults), the body,
    /// the exits, then the narrowing facts and records.
    pub fn build(cx: &'a BuildCx<'a>, hir: &'a hir::Body, dcx: &mut DiagCtx) -> Body {
        let mut b = Builder::new(cx, hir);
        let end = closing(hir.root.span);
        b.open(ScopeKind::Body, end);
        // A `move` method owns its object: what the body leaves of `*this` is
        // dropped at every exit, after the other parameters (A:638, S:605).
        let by_move = |d| cx.tcx.sig_opt(d).map(|s| s.receiver) == Some(Some(hir::Receiver::Move));
        if let hir::BodyOwner::Fn(d) = hir.owner
            && by_move(d)
        {
            let this = b.body.place(Local(1), &[Proj::Deref]);
            if cx.tcx.needs_drop(b.place_ty(this)) {
                b.schedule_drop(this);
            }
        }
        let params: Vec<Local> = (b.locals.iter())
            .filter(|(p, l)| {
                b.hir.locals[**p].kind != hir::LocalKind::This && l.0 <= b.body.arg_count
            })
            .map(|(_, &l)| l)
            .collect();
        for l in params {
            if cx.tcx.needs_drop(b.body.locals[l].ty) {
                b.schedule_drop(l.into());
            }
        }
        b.prologue();
        b.lower_block(&hir.root);
        if b.cursor.is_some() {
            b.fall_off_end(end);
        }
        b.scopes.clear();
        b.finish();
        for d in b.diags.drain(..) {
            dcx.emit(d);
        }
        b.body
    }

    /// Falling off the end: `Ok {}` in a `Result<void, E>` body (A:946), then the
    /// exits of every scope and `return`.
    fn fall_off_end(&mut self, end: Span) {
        self.return_void_ok(end);
        self.exit(ExitTarget::Return, end);
    }

    /// `_0 = Result::Ok {}` when the body returns `Result<void, E>` (A:946), as
    /// falling off its end or `return;` makes it; nothing otherwise.
    pub(crate) fn return_void_ok(&mut self, span: Span) {
        if let Some(ok) = self.void_ok() {
            self.assign(Place::local(Local::RETURN), ok, span);
        }
    }

    /// `Result::Ok {}` when the body returns `Result<void, E>`.
    pub(crate) fn void_ok(&self) -> Option<Rvalue> {
        let tcx = self.cx.tcx;
        let ret = self.body.ret_ty();
        let TyKind::Adt(adt, args) = tcx.kind(ret) else {
            return None;
        };
        let ok = tcx.is_lang_adt(adt, hir::LangItem::Result)
            && tcx
                .list(args)
                .first()
                .is_some_and(|&t| tcx.kind(t) == TyKind::Void);
        ok.then(|| {
            let void = Operand::constant(hir::ConstValue::Void, tcx.common().void);
            Rvalue::Aggregate(
                enrang_mir::AggregateKind::Adt {
                    adt,
                    variant: Some(hir::VariantIdx::OK),
                    args,
                },
                vec![void],
            )
        })
    }

    /// The facts rooted at MIR locals, the records at their points (plan c.20), the
    /// names of the ADTs the body names.
    pub fn finish(&mut self) {
        for f in self.hir.facts.iter() {
            let place = self.local_place(f.path.root);
            let mut steps: Vec<PathStep> = self
                .body
                .projs(place)
                .iter()
                .map(|x| match x {
                    Proj::Field(f) => PathStep::Field(*f),
                    _ => PathStep::Deref,
                })
                .collect();
            steps.extend(f.path.steps.iter().copied());
            self.body.meta.facts.push(MirFact {
                root: place.local,
                steps,
                fact: f.fact,
                span: f.span,
            });
        }
        for (i, r) in self.hir.records.iter().enumerate() {
            // A capture's record is made at its environment field (c.16, c.20).
            if r.kind == hir::RecordKind::Capture {
                continue;
            }
            let at = self.record_points.get(&i).or(self.expr_points.get(&r.expr));
            let Some(&at) = at else {
                continue;
            };
            let slot = match self.body.stmt_at(at).map(|s| &s.kind) {
                Some(StatementKind::Assign { dest, .. }) => dest.local,
                _ => continue,
            };
            self.body.meta.records.push(MirRecord {
                fact: r.fact,
                at,
                slot,
                kind: r.kind,
                span: r.span,
            });
        }
        self.body.names = BodyNames::collect(self.cx.tcx, &self.body);
    }

    fn declare(&mut self, l: hir::LocalId, kind: LocalKind) -> Local {
        let decl = &self.hir.locals[l];
        let m = self.new_local(decl.ty, kind, decl.name, decl.span);
        self.body.locals[m].mutable = decl.mutable;
        m
    }

    pub(crate) fn new_local(
        &mut self,
        ty: Ty,
        kind: LocalKind,
        name: Option<enrang_base::Symbol>,
        span: Span,
    ) -> Local {
        let mut decl = LocalDecl::new(ty, kind, span);
        decl.name = name;
        self.body.locals.push(decl)
    }

    /// A temporary; one whose type needs a drop is registered in the innermost
    /// scope, which runs its `Drop` and `StorageDead` at its exits (c.3).
    pub fn new_temp(&mut self, ty: Ty, span: Span) -> Local {
        let t = self
            .body
            .locals
            .push(LocalDecl::new(ty, LocalKind::Temp, span));
        if self.cx.tcx.needs_drop(ty) {
            self.scope_local(t);
        }
        t
    }

    pub fn push(&mut self, kind: StatementKind, span: Span) {
        if let Some(b) = self.cursor {
            if let StatementKind::Assign { dest, .. }
            | StatementKind::Intrinsic {
                dest: Some(dest), ..
            }
            | StatementKind::HostCall {
                dest: Some(dest), ..
            } = &kind
            {
                self.created(*dest);
            }
            let mut st = Statement::new(kind, span);
            st.region = self.region;
            self.body.blocks[b].stmts.push(st);
        }
    }

    pub fn assign(&mut self, dest: Place, value: Rvalue, span: Span) {
        self.push(StatementKind::Assign { dest, value }, span);
    }

    pub fn terminate(&mut self, kind: TerminatorKind, span: Span) {
        if let TerminatorKind::Call { dest, .. } = &kind
            && self.cursor.is_some()
        {
            self.created(*dest);
        }
        if let Some(b) = self.cursor.take() {
            let mut t = Terminator::new(kind, span);
            t.region = self.region;
            self.body.blocks[b].term = t;
        }
    }

    /// D2 ends temporaries in reverse creation order, and a temporary is created
    /// when it first gets its value, not where it is declared: the first write of a
    /// whole temporary moves its entry to the end of its scope's, so `mk`'s result
    /// in `show(&mk(&("a" + "b")))`, declared before its argument's temporaries but
    /// filled after them, ends first (S 5.7). A temporary built in place, by `new`
    /// or a named form, is created when its construction finishes.
    pub(crate) fn created(&mut self, dest: Place) {
        if !dest.is_local()
            || self.body.locals[dest.local].kind != LocalKind::Temp
            || !self.valued.insert(dest.local)
        {
            return;
        }
        let entry = Entry::Local(dest.local);
        for scope in self.scopes.iter_mut().rev() {
            if let Some(i) = scope.entries.iter().position(|e| *e == entry) {
                let e = scope.entries.remove(i);
                scope.entries.push(e);
                return;
            }
        }
    }

    pub fn new_block(&mut self) -> BlockId {
        self.body.blocks.push(Block {
            stmts: Vec::new(),
            term: Terminator::new(TerminatorKind::Unreachable, Span::DUMMY),
        })
    }

    pub fn switch_to(&mut self, b: BlockId) {
        self.cursor = Some(b);
    }

    /// `goto target` from the cursor, if any.
    pub(crate) fn goto(&mut self, target: BlockId, span: Span) {
        self.terminate(TerminatorKind::Goto(target), span);
    }

    /// The place `e` names, its adjust chain applied, with its guard run emitted
    /// directly before the next statement (plan c.4): a caller that projects it
    /// further, or uses it later, emits the run of the place it uses with
    /// [`Builder::guard`].
    pub fn as_place(&mut self, e: &hir::Expr) -> Place {
        let p = self.adjusted_place(e);
        self.guard(p, e.span);
        p
    }

    /// `e` as an operand (plan c.5, c.6; `expr.rs`, `adjust.rs`).
    pub fn as_operand(&mut self, e: &hir::Expr) -> Operand {
        self.operand_of(e)
    }

    /// Evaluates `e` into `dest` (plan c.5; `expr.rs`).
    pub fn expr_into(&mut self, e: &hir::Expr, dest: Place) {
        self.lower_into(e, dest);
    }

    /// Lowers a block in a scope of its own (plan c.3, c.9; `stmt.rs`).
    pub fn lower_block(&mut self, b: &hir::Block) {
        self.open(ScopeKind::Block, closing(b.span));
        self.lower_stmts(b);
        self.pop_scope();
    }

    pub fn push_scope(&mut self, kind: ScopeKind) {
        self.open(kind, Span::DUMMY);
    }

    /// Opens a scope whose fall-through exit carries `end`.
    pub(crate) fn open(&mut self, kind: ScopeKind, end: Span) {
        self.scopes.push(Scope {
            kind,
            entries: Vec::new(),
            end,
        });
    }

    /// Closes the innermost scope, running its drops and storage ends in reverse
    /// creation order on the fall-through path (plan c.3).
    pub fn pop_scope(&mut self) {
        if let Some(scope) = self.scopes.pop() {
            self.run_exits(&scope.entries, scope.end);
        }
    }

    /// Schedules `Drop(place)` at the innermost scope's exits: a parameter, or
    /// a `move` method's object. A temporary needs none: [`Builder::new_temp`]
    /// registers it, and its scope ends it.
    pub fn schedule_drop(&mut self, place: Place) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.entries.push(Entry::Drop(place));
        }
    }

    /// Leaves for `target`, running the drops of every scope crossed (plan c.3;
    /// `scope.rs`).
    pub fn exit_to(&mut self, target: ExitTarget, span: Span) {
        self.exit(target, span);
    }

    /// Records the point an expression a narrowing record names was lowered at:
    /// the next statement.
    pub fn record_point(&mut self, expr: ExprId) {
        if let Some(b) = self.cursor {
            let p = Point::new(b, self.body.blocks[b].stmts.len());
            self.expr_points.insert(expr, p);
        }
    }

    /// For a narrowing record made at expression `id`: the statement of the current
    /// block that last assigned `dest`, the reference the record names (c.20).
    pub(crate) fn note(&mut self, id: ExprId, dest: Local) {
        if !self.hir.records.iter().any(|r| r.expr == id) {
            return;
        }
        if let Some(at) = self.last_assign(dest) {
            self.expr_points.insert(id, at);
        }
    }

    /// The point of the current block's last whole-local assignment to `dest`.
    pub(crate) fn last_assign(&self, dest: Local) -> Option<Point> {
        let b = self.cursor?;
        let i = self.body.blocks[b].stmts.iter().rposition(|s| {
            matches!(&s.kind, StatementKind::Assign { dest: d, .. } if *d == Place::local(dest))
        })?;
        Some(Point::new(b, i))
    }

    /// The MIR local of a HIR local, declared at first use (plan c.1). A hidden
    /// local of a local function is its hidden argument (K7), which holds `&v`
    /// for an owned variable: its value's place is [`Builder::local_place`].
    pub fn local(&mut self, l: hir::LocalId) -> Local {
        if let Some(&m) = self.locals.get(&l) {
            return m;
        }
        let m = match self.hir.locals[l].kind {
            hir::LocalKind::Hidden(v) if self.hidden.contains_key(&v) => self.hidden[&v],
            _ => self.declare(l, LocalKind::User),
        };
        self.locals.insert(l, m);
        m
    }

    /// The place of a HIR local's value: `*_k` for an owned variable reached
    /// through a hidden argument (c.17), the local itself otherwise.
    pub(crate) fn local_place(&mut self, l: hir::LocalId) -> Place {
        if let Some(p) = self.captured_place(l) {
            return p;
        }
        let m = self.local(l);
        let hidden_ref = matches!(self.hir.locals[l].kind, hir::LocalKind::Hidden(_))
            && self.body.locals[m].ty != self.hir.locals[l].ty;
        match hidden_ref {
            true => self.body.place(m, &[Proj::Deref]),
            false => Place::local(m),
        }
    }

    /// A `Block` region nested in the current one, for an `unsafe { }` or `asm`.
    pub(crate) fn new_region(&mut self, kind: UnsafeKind, span: Span) -> RegionId {
        self.body.unsafe_regions.push(UnsafeRegion {
            kind,
            parent: self.region,
            span,
        })
    }

    pub(crate) fn place_ty(&self, p: Place) -> Ty {
        self.body
            .place_ty(self.cx.tcx, p)
            .map_or(self.cx.tcx.common().error, |t| t.ty)
    }

    pub(crate) fn is_copy(&self, t: Ty) -> bool {
        self.cx.tcx.is_copy(t, &self.env)
    }
}

/// The span of a block's closing brace (plan c.1).
pub(crate) fn closing(span: Span) -> Span {
    if span.is_dummy() || span.is_empty() {
        return span;
    }
    Span {
        lo: BytePos(span.hi.0 - 1),
        hi: span.hi,
    }
}
