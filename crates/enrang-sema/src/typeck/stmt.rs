//! Statements (plan c.4, d.5; owner 3A): blocks and their scopes, declarations,
//! conditions (EN0203, S:1131), loops and their labels, `return`, `break`,
//! `continue`, `unsafe` blocks, `expect` (plan d.17), a top-level `assert`, and the
//! reachability that missing return (EN0427, `mod.rs`) reads: a `return`, `break`,
//! `continue`, a `never`-typed expression statement, `panic(...)` and
//! `unreachable()` end it; an `if` reaches its end when a branch does; a
//! `while (true)`, `for (;;)` or `do ... while (true)` only when a `break` leaves it;
//! a `do ... while (c)` when a `break` leaves it or its condition is reached, at the
//! end of its body or by a `continue`; and no loop after code that cannot be
//! reached.
//!
//! A local's type is its annotation, else its initialiser's, else a variable a later
//! use decides (`let q;`, EN0410 if none does, S:733). A tuple pattern gives its
//! right side an expected tuple type of fresh variables (S:735); the pattern itself
//! is 4B's (`check_destructure`). The seams into narrowing (`cond_facts`, `join`,
//! `prescan_kill`), `for...of` (`check_for_of`) and results (`check_return`,
//! `check_unused`) are called where the plan puts them; after an `if` the states of
//! the branches that reach its end join, so an early `return` in one branch leaves
//! the other's facts (S:741).

use enrang_base::{Span, Symbol};
use enrang_diag::{Code, Diagnostic, Help};
use enrang_hir::{
    self as hir, Callee, ConstValue, ExprKind, FormKind, LocalKind, RecordKind, StmtKind, Ty,
    TyKind,
};
use enrang_syntax::ast;

use crate::typeck::expr::strip_parens;
use crate::typeck::infer::VarKind;
use crate::typeck::narrow::Prescan;
use crate::typeck::{Expect, FnCtxt, Site};

impl FnCtxt<'_, '_> {
    /// A block in a scope of its own.
    pub(crate) fn check_block(&mut self, b: &ast::Block) -> hir::Block {
        self.check_stmts(&b.stmts, b.span)
    }

    /// Statements in a scope of their own.
    pub(crate) fn check_stmts(&mut self, stmts: &[ast::Stmt], span: Span) -> hir::Block {
        self.scopes.push();
        self.depth += 1;
        let stmts = stmts.iter().filter_map(|s| self.check_stmt(s)).collect();
        self.depth -= 1;
        self.scopes.pop();
        hir::Block { stmts, span }
    }

    /// A condition: a `bool` (EN0203, S:1131).
    pub(crate) fn check_cond(&mut self, e: &ast::Expr) -> hir::Expr {
        let bool_ty = self.sema.tcx.common().bool;
        let mut value = self.check_expr(e, Expect::Has(bool_ty));
        let t = self.shallow(value.ty);
        if self.is_error(t) || matches!(self.sema.tcx.kind(t), TyKind::Bool | TyKind::Never) {
            return value;
        }
        if self.var_kind(t) == Some(VarKind::Any) && self.unify(t, bool_ty) {
            return value;
        }
        let shown = self.ty_str(t);
        let text = self.snippet(e.span);
        let help = match self
            .sema
            .tcx
            .kind(super::infer::display_in(self.sema.tcx, &self.infer, t))
        {
            TyKind::Int(_) | TyKind::Float(_) => Some(format!("compare it: `{text} != 0`")),
            TyKind::Nullable(_) => Some(format!("test it: `{text} != null`")),
            // A condition reads no reference (plan choice; doc gap): the `bool` is
            // read through it.
            TyKind::Ref(inner) if self.sema.tcx.kind(self.shallow(inner)) == TyKind::Bool => {
                Some(format!("read the `bool` it points at: `*{text}`"))
            }
            _ => None,
        };
        let mut diag = Diagnostic::new(
            Code::EN0203,
            format!("a condition must be `bool`, found `{shown}`"),
            e.span,
            format!("this is `{shown}`"),
        );
        if let Some(help) = help {
            diag = diag.with_help(Help::text(help));
        }
        self.sema.emit(diag);
        // A nullable written as a condition is TypeScript's truthiness test, and the
        // help already reads it as `x != null`: recover as that test, so the fact
        // it makes narrows `x` and `if (user) { user.name }` is one error, not two
        // (one mistake, one diagnostic). Truthiness itself never narrows (S:741).
        if matches!(self.sema.tcx.kind(t), TyKind::Nullable(_)) {
            let null = self.mk_expr(t, e.span, ExprKind::NullLit);
            return self.mk_expr(
                bool_ty,
                e.span,
                ExprKind::Binary(ast::BinOp::Ne, Box::new(value), Box::new(null)),
            );
        }
        value.ty = self.error_ty();
        value
    }

    fn stmt(kind: StmtKind, span: Span) -> Option<hir::Stmt> {
        Some(hir::Stmt { kind, span })
    }

    /// One statement; `None` for what is not one in HIR (a local function).
    fn check_stmt(&mut self, s: &ast::Stmt) -> Option<hir::Stmt> {
        let kind = match &s.kind {
            ast::StmtKind::VarDecl(decl) => self.check_var_decl(decl),
            ast::StmtKind::If(i) => self.check_if(i),
            ast::StmtKind::While(w) => {
                let before = self.reachable;
                self.prescan_kill(Prescan::Loop(&w.body));
                self.prescan_kill(Prescan::Expr(&w.cond));
                let cond = self.check_cond(&w.cond);
                let (when_true, when_false) = self.cond_facts(&cond);
                let id = self.enter_loop();
                self.flow = when_true;
                let body = self.check_block(&w.body);
                self.exit_loop();
                let endless = is_true(&w.cond);
                self.loop_exit(id, (!endless).then_some(when_false));
                self.reachable = before && (!endless || self.broken.contains(&id));
                StmtKind::While { id, cond, body }
            }
            ast::StmtKind::DoWhile(w) => {
                let before = self.reachable;
                self.prescan_kill(Prescan::Loop(&w.body));
                self.prescan_kill(Prescan::Expr(&w.cond));
                let id = self.enter_loop();
                let body = self.check_block(&w.body);
                // The condition runs when the body ends or a `continue` jumps to it.
                let cond_reached = self.reachable || self.continued.contains(&id);
                self.back_edge(id);
                self.exit_loop();
                self.reachable = true;
                let cond = self.check_cond(&w.cond);
                let (_, when_false) = self.cond_facts(&cond);
                let endless = is_true(&w.cond);
                self.loop_exit(id, (cond_reached && !endless).then_some(when_false));
                self.reachable =
                    before && ((cond_reached && !endless) || self.broken.contains(&id));
                StmtKind::DoWhile { id, body, cond }
            }
            ast::StmtKind::For(f) => self.check_for(f),
            ast::StmtKind::ForOf(f) => {
                let before = self.reachable;
                let kind = self.check_for_of(f);
                self.reachable = before;
                kind
            }
            ast::StmtKind::Return(e) => {
                let kind = self.check_return(e.as_ref(), s.span);
                self.reachable = false;
                kind
            }
            ast::StmtKind::Break(label) => {
                let id = self.jump_target(label.as_ref());
                self.broken.insert(id);
                self.record_jump(id, true);
                self.reachable = false;
                StmtKind::Break(id)
            }
            ast::StmtKind::Continue(label) => {
                let id = self.jump_target(label.as_ref());
                self.continued.insert(id);
                self.record_jump(id, false);
                self.reachable = false;
                StmtKind::Continue(id)
            }
            ast::StmtKind::Block(b) => StmtKind::Block(self.check_block(b)),
            ast::StmtKind::Unsafe(b) => {
                self.unsafe_depth += 1;
                let block = self.check_block(b);
                self.unsafe_depth -= 1;
                StmtKind::Unsafe(block)
            }
            ast::StmtKind::Labeled(label, inner) => {
                self.pending_label = Some(label.name);
                let stmt = self.check_stmt(inner);
                self.pending_label = None;
                return stmt;
            }
            ast::StmtKind::Expr(e) => {
                let value = match &strip_parens(e).kind {
                    ast::ExprKind::Match { subject, arms } => {
                        let typed = self.check_match(subject, arms, e.span, Expect::None, true);
                        // A statement `match` drops each expression arm's value, as
                        // an expression statement does (S:1142, plan choice).
                        if let ExprKind::Match { arms, .. } = &typed.kind {
                            for arm in arms {
                                if let hir::ArmBody::Expr(v) = &arm.body {
                                    self.check_unused(v);
                                }
                            }
                        }
                        typed
                    }
                    _ => self.check_expr(e, Expect::None),
                };
                if ends_flow(self, &value) {
                    self.reachable = false;
                }
                self.check_unused(&value);
                StmtKind::Expr(value)
            }
            ast::StmtKind::LocalFn { .. } => return None,
            ast::StmtKind::Expect(x) => self.check_expect(x),
            ast::StmtKind::Assert { cond, message } => {
                let cond = self.check_cond(cond);
                let mut args = vec![cond];
                if let Some(message) = message {
                    let id = self.sema.tcx.intern_str(message.value.as_str());
                    let str_ty = self.sema.tcx.common().str;
                    let mut text =
                        self.mk_expr(str_ty, message.span, ExprKind::Const(ConstValue::Str(id)));
                    text.adjust.push(hir::Adjust::LiteralDescriptor);
                    args.push(text);
                }
                let void = self.sema.tcx.common().void;
                StmtKind::Expr(self.mk_expr(
                    void,
                    s.span,
                    ExprKind::Call {
                        callee: Callee::Form(FormKind::Assert),
                        receiver: None,
                        args,
                    },
                ))
            }
        };
        Self::stmt(kind, s.span)
    }

    /// `for (init; cond; step) body`.
    fn check_for(&mut self, f: &ast::ForStmt) -> StmtKind {
        let before = self.reachable;
        self.scopes.push();
        self.depth += 1;
        let init = f.init.as_ref().map(|init| {
            let kind = match init {
                ast::ForInit::VarDecl(decl) => self.check_var_decl(decl),
                ast::ForInit::Expr(e) => StmtKind::Expr(self.check_expr(e, Expect::None)),
            };
            Box::new(hir::Stmt { kind, span: f.span })
        });
        self.prescan_kill(Prescan::Loop(&f.body));
        for e in [&f.cond, &f.step].into_iter().flatten() {
            self.prescan_kill(Prescan::Expr(e));
        }
        let cond = f.cond.as_ref().map(|c| self.check_cond(c));
        let (when_true, when_false) = match &cond {
            Some(c) => self.cond_facts(c),
            None => (self.flow.clone(), self.flow.clone()),
        };
        let id = self.enter_loop();
        self.flow = when_true;
        let body = self.check_block(&f.body);
        // The step runs after the body's end and after each `continue`.
        self.back_edge(id);
        let step = f.step.as_ref().map(|e| {
            let e = self.check_expr(e, Expect::None);
            Box::new(hir::Stmt {
                span: e.span,
                kind: StmtKind::Expr(e),
            })
        });
        self.exit_loop();
        self.depth -= 1;
        self.scopes.pop();
        let endless = f.cond.as_ref().is_none_or(is_true);
        self.loop_exit(id, (!endless).then_some(when_false));
        self.reachable = before && (!endless || self.broken.contains(&id));
        StmtKind::For {
            id,
            init,
            cond,
            step,
            body,
        }
    }

    /// `let`/`const`: a local, or a destructuring (4B's pattern).
    pub(crate) fn check_var_decl(&mut self, decl: &ast::VarDecl) -> StmtKind {
        let mut annotated = decl.ty.as_ref().map(|t| (self.lower_ty(t), t.span));
        // A named local's annotation that a position rule rejects is `Error` here,
        // so it reports once (positions; plan d.15).
        if let (ast::Binding::Name(_), Some(t), Some((ty, span))) =
            (&decl.binding, &decl.ty, annotated)
            && !self.sema.tcx.module(self.at.module).library
            && !self.sema.tcx.references_error(ty)
            && crate::passes::positions::rejects_local_annotation(self.sema, ty, t)
        {
            annotated = Some((self.error_ty(), span));
        }
        match &decl.binding {
            ast::Binding::Name(name) => {
                let expect = annotated.map_or(Expect::None, |(t, _)| Expect::Coerce(t, Site::Init));
                let saved = self.init_annotation.take();
                let saved_name = self.init_name.replace(name.name);
                if let (Some((_, annotation)), Some(init)) = (annotated, &decl.init) {
                    self.init_annotation = Some((init.span, annotation));
                }
                let init = decl.init.as_ref().map(|e| self.check_expr(e, expect));
                self.init_annotation = saved;
                self.init_name = saved_name;
                if let Some(init) = &init {
                    self.record_ref(init, RecordKind::Binding);
                }
                let ty = match (annotated, &init) {
                    (Some((t, _)), _) => t,
                    (None, Some(init)) => self.shallow(init.ty),
                    (None, None) => {
                        self.new_var(VarKind::Any, name.span, format!("`{}`", name.name))
                    }
                };
                if annotated.is_none()
                    && let TyKind::Infer(v) = self.sema.tcx.kind(self.shallow(ty))
                {
                    self.infer.locals.push((v, name.span));
                }
                let kind = self
                    .top_var(name.name, name.span)
                    .map_or(LocalKind::User, LocalKind::TopVar);
                let local = self.declare(Some(name.name), ty, decl.mutable, kind, name.span);
                if let Some(ExprKind::Arrow(id)) = init.as_ref().map(|e| &e.kind) {
                    self.local_arrows.insert(local, *id);
                }
                StmtKind::Let { local, init }
            }
            binding => {
                let expect = match (annotated, binding) {
                    (Some((t, _)), _) => Expect::Coerce(t, Site::Init),
                    (None, ast::Binding::Tuple { .. }) => Expect::Has(self.pattern_ty(binding)),
                    (None, _) => Expect::None,
                };
                let init = match &decl.init {
                    Some(e) => self.check_expr(e, expect),
                    None => self.error_expr(decl.span),
                };
                if let (Expect::Has(pattern), None) = (expect, annotated) {
                    let init_ty = init.ty;
                    self.unify(pattern, init_ty);
                }
                let (pat, mode) = self.check_destructure(binding, init.clone());
                self.set_pattern_mutable(&pat, decl.mutable);
                StmtKind::Destructure { pat, mode, init }
            }
        }
    }

    /// The expected type a tuple pattern gives its right side: a tuple of fresh
    /// variables, nested as the pattern is (S:735).
    fn pattern_ty(&mut self, b: &ast::Binding) -> Ty {
        match b {
            ast::Binding::Tuple { elems, .. } => {
                let parts: Vec<Ty> = elems.iter().map(|e| self.pattern_ty(e)).collect();
                self.sema.tcx.mk_tuple(&parts)
            }
            ast::Binding::Name(_) | ast::Binding::Object { .. } => {
                let var = self.infer.fresh(VarKind::Any);
                self.sema.tcx.intern_ty(TyKind::Infer(var))
            }
        }
    }

    fn check_if(&mut self, i: &ast::IfStmt) -> StmtKind {
        let cond = self.check_cond(&i.cond);
        let (when_true, when_false) = self.cond_facts(&cond);
        let before = self.reachable;
        self.flow = when_true;
        let then_ = self.check_block(&i.then_block);
        let then_reaches = self.reachable;
        let after_then = std::mem::replace(&mut self.flow, when_false);
        self.reachable = before;
        let else_ = i.else_branch.as_ref().map(|e| match e {
            ast::ElseBranch::Block(b) => self.check_block(b),
            ast::ElseBranch::If(inner) => {
                let kind = self.check_if(inner);
                hir::Block {
                    stmts: vec![hir::Stmt {
                        kind,
                        span: inner.span,
                    }],
                    span: inner.span,
                }
            }
        });
        let else_reaches = self.reachable;
        let after_else = std::mem::take(&mut self.flow);
        let mut states = Vec::new();
        if then_reaches {
            states.push(after_then.clone());
        }
        if else_reaches {
            states.push(after_else.clone());
        }
        if states.is_empty() {
            states = vec![after_then, after_else];
        }
        self.join(states);
        self.reachable = then_reaches || else_reaches;
        StmtKind::If { cond, then_, else_ }
    }

    /// `expect(a).m(args)` (plan d.17): `a` with no expected type; each argument
    /// against `a`'s type with one `&` and one `| null` peeled, a `toMatchPattern`
    /// argument as an arm value. Matcher names are M4's.
    fn check_expect(&mut self, x: &ast::ExpectStmt) -> StmtKind {
        let actual = self.check_expect_actual(&x.actual);
        let mut hint = self.shallow(actual.ty);
        if let TyKind::Ref(inner) = self.sema.tcx.kind(hint) {
            hint = self.shallow(inner);
        }
        if let TyKind::Nullable(inner) = self.sema.tcx.kind(hint) {
            hint = self.shallow(inner);
        }
        let expect = if self.is_error(hint) {
            Expect::None
        } else {
            Expect::Has(hint)
        };
        let compares = matches!(
            x.matcher.name.as_str(),
            "toBe"
                | "toBeGreaterThan"
                | "toBeGreaterThanOrEqual"
                | "toBeLessThan"
                | "toBeLessThanOrEqual"
        );
        let args = x
            .args
            .iter()
            .enumerate()
            .map(|(i, a)| match a {
                ast::MatcherArg::Expr(e) => {
                    let arg = self.check_expr(e, expect);
                    if compares && i == 0 {
                        self.compare_matcher_arg(x.matcher.name, &actual, &arg);
                    }
                    hir::ExpectArg::Expr(arg)
                }
                ast::MatcherArg::Arm(v) => hir::ExpectArg::Arm(self.expect_arm(v, &actual)),
            })
            .collect();
        StmtKind::Expect(hir::ExpectForm {
            actual,
            negated: x.negated,
            matcher: x.matcher.name,
            args,
            span: x.span,
        })
    }

    fn check_expect_actual(&mut self, e: &ast::Expr) -> hir::Expr {
        self.check_expr(e, Expect::None)
    }

    /// EN0401 when the value `toBe` or an order matcher compares the actual with
    /// has another type: `expect(a).toBe(b)` lowers to `__eq<T>(&a, &b)` (SPEC
    /// 12.2), one `T` for both. References and `| null` are peeled from both sides
    /// first, as matchers peel the actual, so only the types under them must
    /// agree; an order matcher compares two integer types by value, as `<` does.
    fn compare_matcher_arg(&mut self, matcher: Symbol, actual: &hir::Expr, arg: &hir::Expr) {
        let peel = |me: &Self, mut t: Ty| {
            loop {
                t = me.shallow(t);
                match me.sema.tcx.kind(t) {
                    TyKind::Ref(inner) | TyKind::Nullable(inner) => t = inner,
                    _ => break,
                }
            }
            t
        };
        let (want, have) = (peel(self, actual.ty), peel(self, arg.ty));
        if self.is_error(want) || self.is_error(have) || matches!(arg.kind, ExprKind::NullLit) {
            return;
        }
        let int = |me: &Self, t: Ty| {
            matches!(me.sema.tcx.kind(t), TyKind::Int(_)) || me.var_kind(t) == Some(VarKind::Int)
        };
        if matcher.as_str() != "toBe" && int(self, want) && int(self, have) {
            return;
        }
        if self.unify(want, have) {
            return;
        }
        let (sw, sh) = (self.ty_str(want), self.ty_str(have));
        self.sema.emit(
            Diagnostic::new(
                Code::EN0401,
                format!("mismatched types: expected `{sw}`, found `{sh}`"),
                arg.span,
                format!("this is `{sh}`"),
            )
            .with_secondary(
                actual.span,
                format!("`{matcher}` compares it with this `{sw}`"),
            ),
        );
    }
}

/// Whether `e` is the literal `true`.
fn is_true(e: &ast::Expr) -> bool {
    matches!(strip_parens(e).kind, ast::ExprKind::Bool(true))
}

/// Whether an expression statement ends reachability: `never`-typed, or a
/// `panic(...)` or `unreachable()` form (plan d.5).
fn ends_flow(fcx: &FnCtxt<'_, '_>, e: &hir::Expr) -> bool {
    fcx.sema.tcx.kind(fcx.shallow(e.ty)) == TyKind::Never
        || matches!(
            e.kind,
            ExprKind::Call {
                callee: Callee::Form(FormKind::Panic | FormKind::Unreachable),
                ..
            }
        )
}
