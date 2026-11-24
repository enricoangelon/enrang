//! A program's top-level variables and local functions, and the names written in
//! bodies (plan d.3; SPEC 5.5, S:981, S:1143, A:886, N13).
//!
//! The top-level `let` and `const` declarations among the entry's statements are its
//! top-level variables, in declaration order (`TopVar`), after `args: string[]`,
//! which is declared before the first statement (S:1143; plan choice, `TopVar(0)`).
//! They are locals of the statements body. A local function sees those declared
//! above it, judged on the names its own body writes (A:886); its hidden arguments
//! are the top-level variables it uses plus those of every local function it names,
//! a least fixed point over the local call graph, so `relay()`, which writes no
//! variable but calls `grow()`, lends what `grow` uses. Nothing else sees a
//! top-level variable: a use in a class body, an item function, a constant, or a
//! local function declared above the variable is EN0313; and a local function with
//! hidden arguments named anywhere but the statements and other local functions is
//! EN0313 too, since nothing there can evaluate them. A `.test.en` part sees neither
//! (S:1720), so there such names are simply not found (EN0301, plan choice).
//!
//! Finding which top-level variables a body uses means resolving the names it
//! writes, which is the body-local part of resolution (A:886): this pass walks every
//! body of every user module with its own block scopes, as typing will (an inner
//! block may shadow, a same-block redeclaration is EN0307, a declaration is visible
//! after it), and reports the names that resolve to nothing (EN0301 with "did you
//! mean", or a SPEC 16 code) and the local names declared twice (EN0307). Typing
//! reports the same diagnostics at the same places, which the diagnostic context
//! keeps once.

use std::collections::{BTreeMap, BTreeSet};

use enrang_base::{Span, Symbol, intern};
use enrang_diag::{Code, Diagnostic, Help};
use enrang_hir::{BodyOwner, DefId, DefKind, ModuleId, Res, TopVar};
use enrang_syntax::ast::{self, Ident};

use crate::cx::Sema;
use crate::lower::{BodyAst, ItemAstKind};
use crate::resolve::ScopeAt;
use crate::resolve::scope::lookup_value;
use crate::resolve::suggest::{NameKind, unresolved_with};

/// One top-level variable.
#[derive(Clone, Debug)]
pub(crate) struct TopVarDef {
    pub name: Symbol,
    /// The name as declared; `DUMMY` for `args`.
    pub span: Span,
    /// Its place: 0 for `args`, else its statement's index plus one.
    pub order: usize,
}

/// The top-level variables of the entry's statements and each local function's
/// hidden arguments.
#[derive(Clone, Debug, Default)]
pub(crate) struct TopLevel {
    /// The entry module, when it has top-level statements.
    pub module: Option<ModuleId>,
    /// Each top-level variable, in declaration order (`TopVar` indexes it).
    pub vars: Vec<TopVarDef>,
    /// Each local function's place among the statements (its statement's index
    /// plus one).
    pub local_fns: BTreeMap<DefId, usize>,
    /// Each local function's hidden arguments, in `TopVar` order.
    pub hidden: BTreeMap<DefId, Vec<TopVar>>,
}

impl TopLevel {
    fn var(&self, v: TopVar) -> &TopVarDef {
        &self.vars[v.0 as usize]
    }
}

/// The hidden arguments of local function `f`, in `TopVar` order.
pub(crate) fn hidden_args<'s>(sema: &'s Sema, f: DefId) -> &'s [TopVar] {
    sema.res
        .toplevel
        .hidden
        .get(&f)
        .map(Vec::as_slice)
        .unwrap_or(&[])
}

/// The local function whose body `at` is, with its place among the statements.
fn local_fn_at(sema: &Sema, at: ScopeAt) -> Option<(DefId, usize)> {
    let owner = at.owner?;
    sema.res
        .toplevel
        .local_fns
        .get(&owner)
        .map(|&order| (owner, order))
}

/// The top-level variable `name` that code at `at` sees below its locals: `args` in
/// the statements, and in a local function a variable declared above it.
pub(crate) fn visible_var(sema: &Sema, at: ScopeAt, name: Symbol) -> Option<TopVar> {
    let top = &sema.res.toplevel;
    if top.module != Some(at.module) || at.test_part {
        return None;
    }
    if at.statements {
        return (name.as_str() == "args" && !top.vars.is_empty()).then_some(TopVar(0));
    }
    let (_, order) = local_fn_at(sema, at)?;
    top.vars
        .iter()
        .enumerate()
        .rev()
        .find(|(_, v)| v.name == name && v.order < order)
        .map(|(i, _)| TopVar(i as u32))
}

/// The top-level variables a local function at `at` sees, nearest first, `args`
/// left out: candidates for "did you mean".
pub(crate) fn visible_vars(sema: &Sema, at: ScopeAt) -> Vec<(Symbol, Span)> {
    let top = &sema.res.toplevel;
    if top.module != Some(at.module) || at.test_part || at.statements {
        return Vec::new();
    }
    let Some((_, order)) = local_fn_at(sema, at) else {
        return Vec::new();
    };
    top.vars
        .iter()
        .rev()
        .filter(|v| v.order < order && v.order > 0)
        .map(|v| (v.name, v.span))
        .collect()
}

/// How a message names the code at `at`: its class, the type of its member, or the
/// function or constant itself.
fn viewer(sema: &Sema, at: ScopeAt) -> String {
    let tcx = &*sema.tcx;
    if let Some(adt) = at.class {
        return format!("`{}`", tcx.adt(adt).name);
    }
    let Some(owner) = at.owner else {
        return "this code".to_owned();
    };
    let data = tcx.def(owner);
    if let Some(parent) = data.parent {
        return match tcx.def(parent).kind {
            DefKind::Extend => "this `extend` block".to_owned(),
            _ => tcx
                .def(parent)
                .name()
                .map_or("this code".to_owned(), |n| format!("`{n}`")),
        };
    }
    match data.kind {
        DefKind::Test | DefKind::StaticAssert => "this code".to_owned(),
        _ => data
            .name()
            .map_or("this code".to_owned(), |n| format!("`{n}`")),
    }
}

/// EN0313 for `name` at `at`, when it is a top-level variable that code there
/// cannot see; `None` when it is none, or in the statements and the `.test.en` part
/// (where it is simply not found).
pub(crate) fn invisible_var(sema: &Sema, at: ScopeAt, name: Ident) -> Option<Diagnostic> {
    let top = &sema.res.toplevel;
    if top.module != Some(at.module) || at.test_part || at.statements {
        return None;
    }
    let var = top.vars.iter().find(|v| v.name == name.name)?;
    let viewer = viewer(sema, at);
    let local = local_fn_at(sema, at);
    let label = match local {
        Some(_) => format!("`{}` is declared below {viewer}", name.name),
        None => "only the top-level statements and the local functions below it see it".to_owned(),
    };
    let mut diag = Diagnostic::new(
        Code::EN0313,
        format!(
            "`{}` is a top-level variable, which {viewer} can't see",
            name.name
        ),
        name.span,
        label,
    );
    if var.span.is_dummy() {
        diag = diag.with_help(Help::text("`os.args()` gives the arguments anywhere"));
    } else {
        diag = diag.with_secondary(var.span, format!("`{}` is declared here", name.name));
    }
    Some(diag)
}

/// EN0313 for a use of local function `def` at `at` that cannot evaluate its
/// hidden arguments: anywhere but the statements and other local functions.
pub(crate) fn check_use(sema: &mut Sema, at: ScopeAt, def: DefId, span: Span) {
    if let Some(diag) = call_diag(sema, at, def, span) {
        sema.emit(diag);
    }
}

fn call_diag(sema: &Sema, at: ScopeAt, def: DefId, span: Span) -> Option<Diagnostic> {
    if sema.tcx.def(def).kind != DefKind::LocalFn
        || at.statements
        || at.test_part
        || local_fn_at(sema, at).is_some()
    {
        return None;
    }
    let first = *hidden_args(sema, def).first()?;
    let name = sema.tcx.def(def).name().unwrap_or_else(|| intern("_"));
    let var = sema.res.toplevel.var(first).name;
    Some(
        Diagnostic::new(
            Code::EN0313,
            format!(
                "`{name}` uses top-level variables, so only the top-level statements can call it"
            ),
            span,
            "used here, outside the top-level statements",
        )
        .with_secondary(
            sema.tcx.def(def).name_span,
            format!("`{name}` uses `{var}`, a top-level variable"),
        ),
    )
}

/// Collects the top-level variables, walks every body of every user module, then
/// computes the hidden arguments and reports the uses of local functions that
/// cannot supply them.
pub(crate) fn compute(sema: &mut Sema) {
    let program = sema.program;
    let entry = &program.modules[program.entry];
    let entry_module = sema.module_id(program.entry);
    if !entry.library && !entry.ast.stmts.is_empty() {
        let mut top = TopLevel {
            module: Some(entry_module),
            ..TopLevel::default()
        };
        top.vars.push(TopVarDef {
            name: intern("args"),
            span: Span::DUMMY,
            order: 0,
        });
        for (k, stmt) in entry.ast.stmts.iter().enumerate() {
            match &stmt.kind {
                ast::StmtKind::VarDecl(v) => {
                    let mut names = Vec::new();
                    binding_names(&v.binding, &mut names);
                    for name in names {
                        top.vars.push(TopVarDef {
                            name: name.name,
                            span: name.span,
                            order: k + 1,
                        });
                    }
                }
                ast::StmtKind::LocalFn { .. } => {
                    if let Some(&def) = sema.res.item_defs.get(&stmt.id) {
                        top.local_fns.insert(def, k + 1);
                    }
                }
                _ => {}
            }
        }
        sema.res.toplevel = top;
    }
    let mut out = Walked::default();
    walk_all(sema, &mut out);
    // Hidden arguments: a least fixed point over the local functions each names.
    let locals: Vec<DefId> = sema.res.toplevel.local_fns.keys().copied().collect();
    let mut hidden: BTreeMap<DefId, BTreeSet<TopVar>> = locals
        .iter()
        .map(|f| (*f, out.uses.get(f).cloned().unwrap_or_default()))
        .collect();
    loop {
        let mut changed = false;
        for f in &locals {
            let named: Vec<DefId> = out
                .refs
                .get(f)
                .cloned()
                .unwrap_or_default()
                .into_iter()
                .collect();
            for g in named {
                let from: Vec<TopVar> = hidden
                    .get(&g)
                    .map(|s| s.iter().copied().collect())
                    .unwrap_or_default();
                let set = hidden.get_mut(f).expect("every local function has a set");
                for v in from {
                    changed |= set.insert(v);
                }
            }
        }
        if !changed {
            break;
        }
    }
    sema.res.toplevel.hidden = hidden
        .into_iter()
        .map(|(f, set)| (f, set.into_iter().collect()))
        .collect();
    for (at, def, span) in out.calls {
        check_use(sema, at, def, span);
    }
}

/// What the walk found: per local function, the top-level variables and the local
/// functions its body names; and every naming of a local function elsewhere.
#[derive(Default)]
struct Walked {
    uses: BTreeMap<DefId, BTreeSet<TopVar>>,
    refs: BTreeMap<DefId, BTreeSet<DefId>>,
    calls: Vec<(ScopeAt, DefId, Span)>,
}

/// The names a binding declares, in order.
fn binding_names(b: &ast::Binding, out: &mut Vec<Ident>) {
    match b {
        ast::Binding::Name(name) => out.push(*name),
        ast::Binding::Object { fields, .. } => {
            for (field, sub) in fields {
                match sub {
                    Some(sub) => binding_names(sub, out),
                    None => out.push(*field),
                }
            }
        }
        ast::Binding::Tuple { elems, .. } => {
            for e in elems {
                binding_names(e, out);
            }
        }
    }
}

/// Walks every body of every user module, in load and source order.
fn walk_all(sema: &mut Sema, out: &mut Walked) {
    let program = sema.program;
    if let Some(module) = sema.res.toplevel.module
        && let Some(BodyAst::Statements(stmts)) = sema.decls.body_ast(BodyOwner::Statements(module))
    {
        let mut w = Walker::new(sema, ScopeAt::statements(module), out);
        w.frames.push(vec![(intern("args"), Span::DUMMY)]);
        w.frames.push(Vec::new());
        for stmt in stmts {
            w.stmt(stmt);
        }
    }
    let items = sema.decls.items.clone();
    for item in &items {
        let index = sema.res.index(item.module);
        // Library bodies are never typed at M2; an imported file with statements is
        // EN0312 already, and its names would only repeat that.
        let loaded = &program.modules[index];
        if loaded.library || (index != program.entry && !loaded.ast.stmts.is_empty()) {
            continue;
        }
        let at = ScopeAt {
            owner: Some(item.def),
            ..ScopeAt::module(item.module, item.test_part)
        };
        match &item.kind {
            ItemAstKind::Function(f) | ItemAstKind::LocalFn(f) => {
                Walker::new(sema, at, out).function(&f.params, &f.body);
            }
            ItemAstKind::Class(adt, c, members) => {
                let class_at = ScopeAt {
                    owner: None,
                    class: Some(*adt),
                    ..at
                };
                for (member, def) in c.members.iter().zip(members) {
                    let at = ScopeAt {
                        owner: *def,
                        ..class_at
                    };
                    let mut w = Walker::new(sema, at, out);
                    match &member.kind {
                        ast::ClassMemberKind::Field(f) => {
                            if let Some(e) = &f.default {
                                w.expr(e);
                            }
                        }
                        ast::ClassMemberKind::Constructor(ctor) => {
                            w.frames.push(Vec::new());
                            for p in &ctor.params {
                                if let Some(e) = &p.default {
                                    w.expr(e);
                                }
                                w.declare(p.name);
                            }
                            w.body(&ctor.body);
                        }
                        ast::ClassMemberKind::Destructor(d) => w.block(&d.body),
                        ast::ClassMemberKind::Method(m) => {
                            if let Some(body) = &m.body {
                                w.function(&m.params, body);
                            }
                        }
                    }
                }
            }
            ItemAstKind::Enum(_, e, methods) => {
                for v in &e.variants {
                    if let ast::VariantPayload::Value(value) = &v.payload {
                        Walker::new(sema, at, out).expr(value);
                    }
                }
                for (m, &def) in e.methods.iter().zip(methods) {
                    if let Some(body) = &m.body {
                        let at = ScopeAt {
                            owner: Some(def),
                            ..at
                        };
                        Walker::new(sema, at, out).function(&m.params, body);
                    }
                }
            }
            ItemAstKind::Const(c) => Walker::new(sema, at, out).expr(&c.value),
            ItemAstKind::Static(u) => {
                if let Some(value) = &u.value {
                    Walker::new(sema, at, out).expr(value);
                }
            }
            ItemAstKind::StaticAssert => {
                if let Some(BodyAst::Const(cond)) = sema.decls.body_ast(BodyOwner::Const(item.def))
                {
                    Walker::new(sema, at, out).expr(cond);
                }
            }
            ItemAstKind::Test => {
                if let Some(BodyAst::Test(arrow)) = sema.decls.body_ast(BodyOwner::Test(item.def)) {
                    Walker::new(sema, at, out).arrow(arrow);
                }
                if let Some(arrow) = sema.decls.test_cases.get(&item.def).copied() {
                    Walker::new(sema, at, out).arrow(arrow);
                }
            }
            ItemAstKind::Interface(..)
            | ItemAstKind::FieldsInterface(_)
            | ItemAstKind::Alias(_)
            | ItemAstKind::StrUnion
            | ItemAstKind::Declare(_)
            | ItemAstKind::Extend(..) => {}
        }
    }
}

/// Resolves the names one body writes, with its own block scopes.
struct Walker<'w, 'a> {
    sema: &'w mut Sema<'a>,
    at: ScopeAt,
    /// The local function whose body this is.
    local_fn: Option<DefId>,
    frames: Vec<Vec<(Symbol, Span)>>,
    out: &'w mut Walked,
}

impl<'w, 'a> Walker<'w, 'a> {
    fn new(sema: &'w mut Sema<'a>, at: ScopeAt, out: &'w mut Walked) -> Walker<'w, 'a> {
        let local_fn = local_fn_at(sema, at).map(|(f, _)| f);
        Walker {
            sema,
            at,
            local_fn,
            frames: Vec::new(),
            out,
        }
    }

    /// Declares a local in the innermost block; a second one there is EN0307.
    fn declare(&mut self, name: Ident) {
        if self.frames.is_empty() {
            self.frames.push(Vec::new());
        }
        let frame = self.frames.last_mut().expect("a frame");
        if let Some(&(_, first)) = frame.iter().find(|(n, _)| *n == name.name) {
            self.sema.emit(
                Diagnostic::new(
                    Code::EN0307,
                    format!("`{}` is defined twice", name.name),
                    name.span,
                    "defined again here",
                )
                .with_secondary(first, format!("the first `{}` is here", name.name)),
            );
            return;
        }
        frame.push((name.name, name.span));
    }

    fn declare_binding(&mut self, b: &ast::Binding) {
        let mut names = Vec::new();
        binding_names(b, &mut names);
        for name in names {
            self.declare(name);
        }
    }

    fn is_local(&self, name: Symbol) -> bool {
        self.frames
            .iter()
            .rev()
            .any(|frame| frame.iter().any(|(n, _)| *n == name))
    }

    /// The locals in scope, innermost first, each name once, with their places.
    fn visible_locals(&self) -> Vec<(Symbol, Span)> {
        let mut seen = BTreeSet::new();
        let mut out = Vec::new();
        for frame in self.frames.iter().rev() {
            for &(name, span) in frame.iter().rev() {
                if !span.is_dummy() && seen.insert(name) {
                    out.push((name, span));
                }
            }
        }
        out
    }

    /// A name written as a value.
    fn use_name(&mut self, name: Symbol, span: Span) {
        if self.is_local(name) {
            return;
        }
        let ident = Ident { name, span };
        match lookup_value(self.sema, self.at, ident) {
            Res::TopVar(v) => {
                if let Some(f) = self.local_fn {
                    self.out.uses.entry(f).or_default().insert(v);
                }
            }
            Res::Err => {
                let locals = self.visible_locals();
                unresolved_with(self.sema, self.at, ident, NameKind::Value, &locals);
            }
            Res::Def(d) => self.named_fn(d, span),
            Res::Fns(defs) => {
                for d in defs {
                    self.named_fn(d, span);
                }
            }
            _ => {}
        }
    }

    /// A local function named in this body.
    fn named_fn(&mut self, def: DefId, span: Span) {
        if self.sema.tcx.def(def).kind != DefKind::LocalFn {
            return;
        }
        match self.local_fn {
            Some(f) => {
                self.out.refs.entry(f).or_default().insert(def);
            }
            None => {
                if !self.at.statements {
                    self.out.calls.push((self.at, def, span));
                }
            }
        }
    }

    /// A function's parameters and the top level of its body share one scope, as in
    /// TypeScript: a body's own `let x` beside a parameter `x` is EN0307, while a
    /// nested block may shadow it.
    fn function(&mut self, params: &[ast::Param], body: &ast::Block) {
        self.frames.push(Vec::new());
        for p in params {
            if let Some(e) = &p.default {
                self.expr(e);
            }
            self.declare_binding(&p.binding);
        }
        self.body(body);
        self.frames.pop();
    }

    fn arrow(&mut self, a: &ast::ArrowFn) {
        self.frames.push(Vec::new());
        for p in &a.params {
            self.declare(p.name);
        }
        match &a.body {
            ast::ArrowBody::Expr(e) => self.expr(e),
            ast::ArrowBody::Block(b) => self.body(b),
        }
        self.frames.pop();
    }

    /// The statements of a function's body, in the frame of its parameters.
    fn body(&mut self, b: &ast::Block) {
        for s in &b.stmts {
            self.stmt(s);
        }
    }

    fn block(&mut self, b: &ast::Block) {
        self.frames.push(Vec::new());
        for s in &b.stmts {
            self.stmt(s);
        }
        self.frames.pop();
    }

    fn var_decl(&mut self, v: &ast::VarDecl) {
        if let Some(e) = &v.init {
            self.expr(e);
        }
        self.declare_binding(&v.binding);
    }

    fn stmt(&mut self, s: &ast::Stmt) {
        match &s.kind {
            ast::StmtKind::VarDecl(v) => self.var_decl(v),
            ast::StmtKind::If(i) => self.if_stmt(i),
            ast::StmtKind::While(w) | ast::StmtKind::DoWhile(w) => {
                self.expr(&w.cond);
                self.block(&w.body);
            }
            ast::StmtKind::For(f) => {
                self.frames.push(Vec::new());
                match &f.init {
                    Some(ast::ForInit::VarDecl(v)) => self.var_decl(v),
                    Some(ast::ForInit::Expr(e)) => self.expr(e),
                    None => {}
                }
                if let Some(e) = &f.cond {
                    self.expr(e);
                }
                if let Some(e) = &f.step {
                    self.expr(e);
                }
                self.block(&f.body);
                self.frames.pop();
            }
            ast::StmtKind::ForOf(f) => {
                match &f.source {
                    ast::ForOfSource::Range(a, b) => {
                        self.expr(a);
                        self.expr(b);
                    }
                    ast::ForOfSource::Expr(e) => self.expr(e),
                }
                self.frames.push(Vec::new());
                self.declare_binding(&f.binding);
                self.block(&f.body);
                self.frames.pop();
            }
            ast::StmtKind::Return(e) => {
                if let Some(e) = e {
                    self.expr(e);
                }
            }
            ast::StmtKind::Break(_) | ast::StmtKind::Continue(_) => {}
            ast::StmtKind::Block(b) | ast::StmtKind::Unsafe(b) => self.block(b),
            ast::StmtKind::Labeled(_, inner) => self.stmt(inner),
            ast::StmtKind::Expr(e) => self.expr(e),
            // A local function is a body of its own, walked as an item.
            ast::StmtKind::LocalFn { .. } => {}
            ast::StmtKind::Expect(x) => {
                self.expr(&x.actual);
                for arg in &x.args {
                    match arg {
                        ast::MatcherArg::Expr(e) => self.expr(e),
                        ast::MatcherArg::Arm(v) => self.arm_value(v),
                    }
                }
            }
            ast::StmtKind::Assert { cond, .. } => self.expr(cond),
        }
    }

    fn if_stmt(&mut self, i: &ast::IfStmt) {
        self.expr(&i.cond);
        self.block(&i.then_block);
        match &i.else_branch {
            Some(ast::ElseBranch::If(inner)) => self.if_stmt(inner),
            Some(ast::ElseBranch::Block(b)) => self.block(b),
            None => {}
        }
    }

    /// An arm value: literals and conditions are expressions; a path names a case
    /// or a constant, which typing decides (EN0502), or under `match (true)` is a
    /// condition (the caller's).
    fn arm_value(&mut self, v: &ast::ArmValue) {
        match v {
            ast::ArmValue::Value(e) => self.expr(e),
            ast::ArmValue::Range(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            ast::ArmValue::Null(_)
            | ast::ArmValue::Case(_)
            | ast::ArmValue::Ok(_)
            | ast::ArmValue::Err(_) => {}
        }
    }

    fn fields(&mut self, fields: &[ast::FieldInit]) {
        for f in fields {
            match &f.value {
                Some(e) => self.expr(e),
                None => self.use_name(f.name.name, f.name.span),
            }
        }
    }

    fn expr(&mut self, e: &ast::Expr) {
        match &e.kind {
            ast::ExprKind::Int { .. }
            | ast::ExprKind::Float(_)
            | ast::ExprKind::Str(_)
            | ast::ExprKind::RawTemplate(_)
            | ast::ExprKind::Bool(_)
            | ast::ExprKind::Null
            | ast::ExprKind::This
            | ast::ExprKind::Super
            | ast::ExprKind::TypeMember { .. }
            | ast::ExprKind::SizeForm(_)
            | ast::ExprKind::Error => {}
            ast::ExprKind::Template(parts) => {
                for part in parts {
                    if let ast::TplPart::Expr(e) = part {
                        self.expr(e);
                    }
                }
            }
            ast::ExprKind::Ident(name) => self.use_name(*name, e.span),
            ast::ExprKind::Array(elems) => {
                for elem in elems {
                    match elem {
                        ast::ArrayElem::Item(e) | ast::ArrayElem::Spread { expr: e, .. } => {
                            self.expr(e)
                        }
                    }
                }
            }
            ast::ExprKind::Repeat(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            ast::ExprKind::New { init, .. } => match init {
                ast::NewInit::Args(args) => {
                    for a in args {
                        self.expr(a);
                    }
                }
                ast::NewInit::Fields(fields) => self.fields(fields),
            },
            ast::ExprKind::CaseLit { fields, .. } | ast::ExprKind::ObjectLit(fields) => {
                self.fields(fields)
            }
            ast::ExprKind::Match { subject, arms } => {
                self.expr(subject);
                let mut inner = &**subject;
                while let ast::ExprKind::Paren(e) = &inner.kind {
                    inner = e;
                }
                // Under `match (true)` a path is a condition, whose first name is used.
                let conditions = matches!(inner.kind, ast::ExprKind::Bool(true));
                for arm in arms {
                    for v in &arm.values {
                        match v {
                            ast::ArmValue::Case(path) if conditions => {
                                if let Some(first) = path.first() {
                                    self.use_name(first.name, first.span);
                                }
                            }
                            _ => self.arm_value(v),
                        }
                    }
                    if let Some(g) = &arm.guard {
                        self.expr(g);
                    }
                    match &arm.body {
                        ast::ArmBody::Expr(e) => self.expr(e),
                        ast::ArmBody::Block(b) => self.block(b),
                        ast::ArmBody::Return(e) => {
                            if let Some(e) = e {
                                self.expr(e);
                            }
                        }
                        ast::ArmBody::Break(_) | ast::ArmBody::Continue(_) => {}
                    }
                }
            }
            ast::ExprKind::Asm(asm) => {
                self.expr(&asm.template);
                for option in asm.options.iter().flatten() {
                    match &option.kind {
                        ast::AsmOptionKind::In(regs) | ast::AsmOptionKind::Out(regs) => {
                            for r in regs {
                                match &r.value {
                                    Some(e) => self.expr(e),
                                    None => self.use_name(r.reg.name, r.reg.span),
                                }
                            }
                        }
                        ast::AsmOptionKind::Clobbers(_) => {}
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
            ast::ExprKind::Member { base, .. } => self.expr(base),
            ast::ExprKind::IncDec { target, .. } => self.expr(target),
            ast::ExprKind::Binary(_, a, b)
            | ast::ExprKind::Logical(_, a, b)
            | ast::ExprKind::Coalesce(a, b)
            | ast::ExprKind::Index(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            ast::ExprKind::Assign { target, value, .. } => {
                self.expr(target);
                self.expr(value);
            }
            ast::ExprKind::Ternary(c, a, b) => {
                self.expr(c);
                self.expr(a);
                self.expr(b);
            }
            ast::ExprKind::Call { callee, args, .. } => {
                self.expr(callee);
                for a in args {
                    self.expr(a);
                }
            }
            ast::ExprKind::Arrow(a) => self.arrow(a),
        }
    }
}
