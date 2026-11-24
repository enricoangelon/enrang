//! Statements (M3 plan c.9): `let` with its default (A:938), conditions and loops
//! with their temporary scopes (D2), `return`, `break`, `continue`, blocks and
//! `unsafe` regions. A statement after a `return`, `break` or `continue` is not
//! built: no path reaches it.

use enrang_hir::{self as hir, ConstValue, StmtKind as S, TyKind};
use enrang_mir::{
    AggregateKind, BlockId, IntrinsicKind, Local, Operand, Place, Rvalue, StatementKind, UnsafeKind,
};

use crate::builder::{Builder, closing};

/// No block: a fact that holds on neither edge.
pub(crate) const NONE: BlockId = BlockId(u32::MAX);
use crate::scope::{ExitTarget, ScopeKind};

impl Builder<'_> {
    /// Lowers a block's statements, in the scope the caller opened.
    pub(crate) fn lower_stmts(&mut self, b: &hir::Block) {
        for s in &b.stmts {
            if self.cursor.is_none() {
                return;
            }
            self.lower_stmt(s);
        }
    }

    pub(crate) fn lower_stmt(&mut self, s: &hir::Stmt) {
        let span = s.span;
        match &s.kind {
            S::Let { local, init } => {
                let l = self.local(*local);
                self.push(StatementKind::StorageLive(l), span);
                self.scope_local(l);
                match init {
                    Some(e) => self.in_temps(span, |b| {
                        b.lower_into(e, l.into());
                        b.note(e.id, l);
                    }),
                    None => self.in_temps(span, |b| b.default_into(l, span)),
                }
            }
            S::Destructure { pat, mode, init } => {
                self.in_temps(span, |b| crate::lower_destructure(b, pat, *mode, init));
                // The bindings live to the end of the enclosing block (c.15).
                let mut bound = Vec::new();
                crate::pattern::binds(pat, &mut bound);
                for l in bound {
                    let m = self.local(l);
                    self.scope_local(m);
                }
            }
            S::If { cond, then_, else_ } => {
                let (t, join) = (self.new_block(), self.new_block());
                let e = match else_ {
                    Some(_) => self.new_block(),
                    None => join,
                };
                self.cond_to(cond, t, e);
                self.switch_to(t);
                self.lower_block(then_);
                self.goto(join, closing(then_.span));
                if let Some(b) = else_ {
                    self.switch_to(e);
                    self.lower_block(b);
                    self.goto(join, closing(b.span));
                }
                self.switch_to(join);
            }
            S::While { id, cond, body } => {
                let (head, body_bb, exit) = (self.new_block(), self.new_block(), self.new_block());
                self.goto(head, span);
                self.switch_to(head);
                self.cond_to(cond, body_bb, exit);
                self.switch_to(body_bb);
                self.loop_body(*id, head, exit, body);
                self.switch_to(exit);
            }
            S::DoWhile { id, body, cond } => {
                let (body_bb, test, exit) = (self.new_block(), self.new_block(), self.new_block());
                self.goto(body_bb, span);
                self.switch_to(body_bb);
                self.loop_body(*id, test, exit, body);
                self.switch_to(test);
                self.cond_to(cond, body_bb, exit);
                self.switch_to(exit);
            }
            S::For {
                id,
                init,
                cond,
                step,
                body,
            } => {
                self.open(ScopeKind::Block, span);
                if let Some(init) = init {
                    self.lower_stmt(init);
                }
                let (head, body_bb) = (self.new_block(), self.new_block());
                let (step_bb, exit) = (self.new_block(), self.new_block());
                self.goto(head, span);
                self.switch_to(head);
                match cond {
                    Some(c) => self.cond_to(c, body_bb, exit),
                    None => self.goto(body_bb, span),
                }
                self.switch_to(body_bb);
                self.loop_body(*id, step_bb, exit, body);
                self.switch_to(step_bb);
                if let Some(step) = step {
                    self.lower_stmt(step);
                }
                self.goto(head, span);
                self.switch_to(exit);
                self.pop_scope();
            }
            S::ForOf {
                id,
                pat,
                source,
                body,
            } => self.in_temps(span, |b| {
                crate::lower_for_of(b, *id, pat, source, body, span)
            }),
            S::Return(e) => {
                self.open(ScopeKind::Statement, span);
                let ret = Place::local(Local::RETURN);
                match e {
                    Some(e) => self.lower_into(e, ret),
                    None => {
                        if let Some(ok) = self.void_ok() {
                            self.assign(ret, ok, span);
                        }
                    }
                }
                self.exit(ExitTarget::Return, span);
                self.scopes.pop();
            }
            S::Break(l) => self.exit(ExitTarget::Break(*l), span),
            S::Continue(l) => self.exit(ExitTarget::Continue(*l), span),
            S::Block(b) => self.lower_block(b),
            S::Unsafe(b) => {
                let outer = self.region;
                self.region = Some(self.new_region(UnsafeKind::Block, b.span));
                self.lower_block(b);
                self.region = outer;
            }
            S::Expr(e) => self.in_temps(span, |b| b.expr_stmt(e)),
            S::Expect(f) => self.in_temps(span, |b| crate::lower_expect(b, f)),
        }
    }

    /// A loop body in its loop scope: `continue` goes to `next`, `break` to
    /// `exit`; the fall-through goes to `next`.
    fn loop_body(&mut self, id: hir::LoopId, next: BlockId, exit: BlockId, body: &hir::Block) {
        self.open(
            ScopeKind::Loop {
                id,
                head: next,
                exit,
            },
            closing(body.span),
        );
        self.lower_block(body);
        self.pop_scope();
        self.goto(next, closing(body.span));
    }

    /// A condition in its temporary scope, switching to `then_` when it holds and
    /// `else_` when it fails (b.4); a condition that is a narrowing fact's test
    /// records `then_` (c.20).
    ///
    /// A retest's block is its own: the switch goes to a fresh block that goes on
    /// to the target, since an `if` with no `else` fails into its join, which the
    /// then-branch reaches too, and there the retest's fact must not hold (S:742).
    pub(crate) fn cond_to(&mut self, c: &hir::Expr, then_: BlockId, else_: BlockId) {
        let bool_ty = self.cx.tcx.common().bool;
        let t = self.new_temp(bool_ty, c.span);
        self.in_temps(c.span, |b| b.lower_into(c, t.into()));
        if !self.retests_in(c) {
            self.switch_bool(Operand::Move(t.into()), then_, else_, c.span);
            self.fact_tests(c, then_, else_);
            return;
        }
        let (own_then, own_else) = (self.new_block(), self.new_block());
        self.switch_bool(Operand::Move(t.into()), own_then, own_else, c.span);
        for (own, target) in [(own_then, then_), (own_else, else_)] {
            self.switch_to(own);
            self.goto(target, c.span);
        }
        self.cursor = None;
        self.fact_tests(c, own_then, own_else);
    }

    /// Whether `c`, or a condition [`Builder::fact_tests`] reads in it, retests a
    /// fact: a test of a path that already held it (`FactInfo::retests`).
    fn retests_in(&self, c: &hir::Expr) -> bool {
        use hir::ExprKind as K;
        match &c.kind {
            K::Logical(_, a, b) => self.retests_in(a) || self.retests_in(b),
            K::Unary(hir::UnOp::Not, x) => self.retests_in(x),
            _ => self.hir.facts.iter().any(|f| f.retests.contains(&c.span)),
        }
    }

    /// The narrowing facts `c` tests (c.20, linked by span): a `!= null` test's
    /// holds in `then_`, an `== null` test's in `else_`, `NONE` for neither; a
    /// right operand of `&&` or `||` by their truth tables (the left one's
    /// block is its operator's, `Builder::logical`), through `!`.
    ///
    /// The left operand's tests hold there too when the right operand makes no
    /// reference a narrowing records, since only a record invalidates a fact
    /// (N2): a retest in `p != null && q` keeps `p` non-null in the branch, which
    /// the value-lowered `&&` would otherwise join with the path where it failed.
    pub(crate) fn fact_tests(&mut self, c: &hir::Expr, then_: BlockId, else_: BlockId) {
        use hir::ExprKind as K;
        let quiet = |b: &hir::Expr| {
            !(self.hir.records.iter()).any(|r| b.span.lo <= r.span.lo && r.span.hi <= b.span.hi)
        };
        match &c.kind {
            K::Logical(hir::LogOp::And, a, b) => {
                if quiet(b) {
                    self.fact_tests(a, then_, NONE);
                }
                self.fact_tests(b, then_, NONE)
            }
            K::Logical(hir::LogOp::Or, a, b) => {
                if quiet(b) {
                    self.fact_tests(a, NONE, else_);
                }
                self.fact_tests(b, NONE, else_)
            }
            K::Unary(hir::UnOp::Not, x) => self.fact_tests(x, else_, then_),
            _ => {
                let at = match &c.kind {
                    K::Binary(hir::BinOp::Eq, ..) => else_,
                    _ => then_,
                };
                for (id, f) in self.hir.facts.iter_enumerated() {
                    if (f.span == c.span || f.retests.contains(&c.span)) && at != NONE {
                        self.body.meta.fact_tests.push((id, at));
                    }
                }
            }
        }
    }

    /// An expression statement: an assignment stores, anything else is evaluated
    /// into a temporary dropped at the statement's end.
    fn expr_stmt(&mut self, e: &hir::Expr) {
        match &e.kind {
            hir::ExprKind::Assign { .. } | hir::ExprKind::IncDec { .. } if e.adjust.is_empty() => {
                self.lower_assign(e, false);
            }
            _ => self.discard(e),
        }
    }

    /// `let l: T;` (A:938, S:871): `T`'s default when it has one, else nothing.
    pub(crate) fn default_into(&mut self, l: Local, span: enrang_base::Span) {
        let ty = self.body.locals[l].ty;
        if let TyKind::Array(t) = self.cx.tcx.kind(ty) {
            self.intrinsic(IntrinsicKind::AllocArray(t), Vec::new(), l.into(), span);
        } else if let Some(rv) = self.default_rv(ty, span) {
            self.assign(l.into(), rv, span);
        }
    }

    /// A type's default as an operand: a constant as it is, anything else in a
    /// temporary.
    pub(crate) fn default_op(&mut self, ty: hir::Ty, span: enrang_base::Span) -> Option<Operand> {
        Some(match self.default_rv(ty, span)? {
            Rvalue::Use(op) => op,
            rv => self.use_val(crate::expr::Val::Rv(rv), ty, span),
        })
    }

    /// A type's default (S:871): zero numbers and raw pointers, `false`, `""`,
    /// `[]`, `null`, `void`, and fixed arrays, tuples and objects of defaults.
    pub(crate) fn default_rv(&mut self, ty: hir::Ty, span: enrang_base::Span) -> Option<Rvalue> {
        let tcx = self.cx.tcx;
        let c = |v| Some(Rvalue::Use(Operand::constant(v, ty)));
        let parts = |b: &mut Self, tys: Vec<hir::Ty>| -> Option<Vec<Operand>> {
            tys.into_iter().map(|t| b.default_op(t, span)).collect()
        };
        match tcx.kind(ty) {
            TyKind::Int(_) => c(ConstValue::Int(0, ty)),
            TyKind::Float(_) => c(ConstValue::Float(0, ty)),
            TyKind::Bool => c(ConstValue::Bool(false)),
            TyKind::Void => c(ConstValue::Void),
            TyKind::Str => c(ConstValue::Str(tcx.intern_str(""))),
            TyKind::Nullable(_) => Some(Rvalue::Aggregate(AggregateKind::Null, Vec::new())),
            TyKind::Raw(_) => {
                let usize_ = tcx.common().usize;
                let zero = Operand::constant(ConstValue::Int(0, usize_), usize_);
                Some(Rvalue::Cast(hir::CastKind::UsizeToRaw, zero, ty))
            }
            TyKind::Array(t) => {
                let d = self.new_temp(ty, span);
                self.intrinsic(IntrinsicKind::AllocArray(t), Vec::new(), d.into(), span);
                Some(Rvalue::Use(Operand::Move(d.into())))
            }
            TyKind::Fixed(e, n) => {
                let op = parts(self, vec![e])?;
                Some(Rvalue::Aggregate(AggregateKind::Repeat(n), op))
            }
            TyKind::Tuple(l) => {
                let ops = parts(self, tcx.list(l).to_vec())?;
                Some(Rvalue::Aggregate(AggregateKind::Tuple, ops))
            }
            TyKind::Object(shape) => {
                let tys = tcx.shape(shape).fields.iter().map(|f| f.1).collect();
                let ops = parts(self, tys)?;
                Some(Rvalue::Aggregate(AggregateKind::Object(shape), ops))
            }
            _ => None,
        }
    }
}
