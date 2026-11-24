//! Name lookup from a [`ScopeAt`] (A:886): type parameters and `Self`, then the
//! module's own items (and its `.test.en` part's, from the part), then its imports,
//! then the preludes of its layers, then primitive type names and compiler forms.
//! Locals come first in a body; they live in typeck's [`ScopeStack`]. Lookup emits
//! nothing: `Res::Err` when absent, which `suggest.rs` reports.
//!
//! A program's top-level variables are locals of its statements body, and typeck's
//! scope stack finds them there. A local function sees, below its own locals, the
//! top-level variables declared above it (S:981), as `Res::TopVar`, one of its
//! hidden arguments; and `args` is a top-level variable of the statements declared
//! before the first one (S:1143, plan choice), so it resolves there too when no
//! local shadows it. A `.test.en` part sees no local function (S:1720), and nothing
//! else sees a top-level variable (EN0313, `suggest.rs`).

use std::collections::BTreeMap;

use enrang_base::{Span, Symbol};
use enrang_hir::{DefKind, FormName, LocalId, LoopId, PrimTy, Res, Vis};
use enrang_syntax::ast::{self, Ident};

use crate::cx::Sema;
use crate::resolve::suggest::NameKind;
use crate::resolve::{ScopeAt, prelude, res_of, toplevel};

/// A value name: a top-level variable a local function sees, the module's items,
/// imports, preludes, then forms and primitive type names (for `i32.MAX`).
pub(crate) fn lookup_value(sema: &Sema, at: ScopeAt, name: Ident) -> Res {
    if let Some(var) = toplevel::visible_var(sema, at, name.name) {
        return Res::TopVar(var);
    }
    if let Some(res) = lookup_item(sema, at, name.name) {
        return res;
    }
    if let Some(form) = FormName::from_name(name.name.as_str()) {
        return Res::Form(form);
    }
    match PrimTy::from_name(name.name.as_str()) {
        Some(prim) => Res::PrimType(prim),
        None => Res::Err,
    }
}

/// A type path: one name, or a namespace and a name (`ns.T`).
pub(crate) fn lookup_type(sema: &Sema, at: ScopeAt, path: &[Ident]) -> Res {
    match path {
        [] => Res::Err,
        [name] => lookup_type_name(sema, at, name.name),
        [first, rest @ ..] => {
            let mut res = lookup_type_name(sema, at, first.name);
            for segment in rest {
                res = match res {
                    Res::Namespace(m) => {
                        let index = sema.res.index(m);
                        public_member(sema, index, segment.name).unwrap_or(Res::Err)
                    }
                    _ => Res::Err,
                };
            }
            res
        }
    }
}

fn lookup_type_name(sema: &Sema, at: ScopeAt, name: Symbol) -> Res {
    if let Some(g) = at.generics {
        let params = sema.tcx.all_params(g);
        if let Some(&p) = params
            .iter()
            .rev()
            .find(|&&p| sema.tcx.param(p).name == name && sema.tcx.param(p).implicit.is_none())
        {
            return Res::TyParam(p);
        }
    }
    if at.self_param.is_some() && name.as_str() == "Self" {
        return Res::SelfTy;
    }
    if let Some(res) = lookup_item(sema, at, name) {
        return res;
    }
    match PrimTy::from_name(name.as_str()) {
        Some(prim) => Res::PrimType(prim),
        None => Res::Err,
    }
}

/// The definitions of `name` a scope's table holds, without the local functions a
/// `.test.en` part never sees.
fn visible_defs(sema: &Sema, at: ScopeAt, defs: &[enrang_hir::DefId]) -> Vec<enrang_hir::DefId> {
    defs.iter()
        .copied()
        .filter(|&d| !(at.test_part && sema.tcx.def(d).kind == DefKind::LocalFn))
        .collect()
}

/// The module's own items, its imports, then its preludes, nearest layer first.
fn lookup_item(sema: &Sema, at: ScopeAt, name: Symbol) -> Option<Res> {
    let index = sema.res.index(at.module);
    let scope = &sema.res.scopes[index];
    if at.test_part
        && let Some(defs) = scope.test_names.get(&name)
    {
        return Some(res_of(sema.tcx, defs));
    }
    if let Some(defs) = scope.names.get(&name) {
        let defs = visible_defs(sema, at, defs);
        if !defs.is_empty() {
            return Some(res_of(sema.tcx, &defs));
        }
    }
    if at.test_part
        && let Some(res) = sema.res.test_imports[index].get(&name)
    {
        return Some(res.clone());
    }
    if let Some(res) = sema.res.imports[index].get(&name) {
        return Some(res.clone());
    }
    let module = sema.tcx.module(at.module).path;
    for layer in prelude::visible(sema, module).into_iter().rev() {
        if let Some(res) = layer.get(&name) {
            return Some(res.clone());
        }
    }
    None
}

/// What a namespace for the module at load index `index` shows as `name` (SPEC
/// 4.12): a `public` item, or what the module re-exports; otherwise its child
/// module `p/name`, for folders and files alike, as `import { x } from "p"` binds.
pub(crate) fn public_member(sema: &Sema, index: usize, name: Symbol) -> Option<Res> {
    if let Some(defs) = sema.res.scopes[index].names.get(&name) {
        let public: Vec<_> = defs
            .iter()
            .copied()
            .filter(|&d| {
                sema.tcx.def(d).vis == Vis::Public && sema.tcx.def(d).kind != DefKind::LocalFn
            })
            .collect();
        if !public.is_empty() {
            return Some(res_of(sema.tcx, &public));
        }
    }
    if reexports(sema, index, name)
        && let Some(res) = sema.res.imports[index].get(&name)
    {
        return Some(res.clone());
    }
    child_module(sema, index, name).map(|child| Res::Namespace(sema.module_id(child)))
}

/// Whether the module at `index` re-exports `name` with a `public import`.
pub(crate) fn reexports(sema: &Sema, index: usize, name: Symbol) -> bool {
    sema.program.modules[index].ast.imports.iter().any(|i| {
        i.public
            && match &i.kind {
                ast::ImportKind::Named(names) => {
                    names.iter().any(|n| n.alias.unwrap_or(n.name).name == name)
                }
                ast::ImportKind::Namespace(alias) => alias.name == name,
            }
    })
}

/// The loaded child module `p/name` of the module at `index`.
pub(crate) fn child_module(sema: &Sema, index: usize, name: Symbol) -> Option<usize> {
    let parent = sema.program.modules[index].path;
    sema.program.child_of(parent, name.as_str())
}

/// What a name in scope at `at` is, for "did you mean" (A:886): a local's or type
/// parameter's declaration, an item of the module, an import, or a name the
/// preludes, the forms or the primitive types give (which has no place to show).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Candidate {
    Local(Span),
    TyParam(Span),
    Item(enrang_hir::DefId),
    Import(Span),
    Elsewhere,
}

/// The names in scope at `at` below the locals, nearest first, for "did you mean":
/// type parameters (for a type), top-level variables a local function sees, the
/// module's items, its imports, its preludes, then forms (for a value) and the
/// primitive type names. For a type, only type names, and never a namespace, which
/// stands only before a `.`; for a name before a `.` in a type path
/// ([`NameKind::Namespace`]), only namespaces.
pub(crate) fn candidates(sema: &Sema, at: ScopeAt, kind: NameKind) -> Vec<(Symbol, Candidate)> {
    let mut out = Vec::new();
    let is_type = |d: enrang_hir::DefId| {
        matches!(
            sema.tcx.def(d).kind,
            DefKind::Adt(_) | DefKind::TypeAlias | DefKind::StrUnion(_)
        )
    };
    let fits = |res: &Res| match (kind, res) {
        (NameKind::Value, Res::Def(_) | Res::Fns(_) | Res::Namespace(_)) => true,
        (NameKind::Type, Res::Def(d)) => is_type(*d),
        (NameKind::Namespace, Res::Namespace(_)) => true,
        _ => false,
    };
    match kind {
        NameKind::Type => {
            if let Some(g) = at.generics {
                for p in sema.tcx.all_params(g).into_iter().rev() {
                    let param = sema.tcx.param(p);
                    if param.implicit.is_none() {
                        out.push((param.name, Candidate::TyParam(param.span)));
                    }
                }
            }
        }
        NameKind::Value => {
            for (name, span) in toplevel::visible_vars(sema, at) {
                out.push((name, Candidate::Local(span)));
            }
        }
        NameKind::Namespace => {}
    }
    let index = sema.res.index(at.module);
    let scope = &sema.res.scopes[index];
    if kind != NameKind::Namespace {
        let mut tables: Vec<&BTreeMap<Symbol, Vec<enrang_hir::DefId>>> = Vec::new();
        if at.test_part {
            tables.push(&scope.test_names);
        }
        tables.push(&scope.names);
        for table in tables {
            for (name, defs) in table {
                let defs = visible_defs(sema, at, defs);
                if let Some(&d) = defs
                    .iter()
                    .find(|&&d| kind == NameKind::Value || is_type(d))
                {
                    out.push((*name, Candidate::Item(d)));
                }
            }
        }
    }
    let mut imports: Vec<(bool, &BTreeMap<Symbol, Res>)> = Vec::new();
    if at.test_part {
        imports.push((true, &sema.res.test_imports[index]));
    }
    imports.push((false, &sema.res.imports[index]));
    for (part, table) in imports {
        for (name, res) in table {
            if fits(res) {
                let span = sema.res.import_spans.get(&(index, part, *name)).copied();
                out.push((*name, span.map_or(Candidate::Elsewhere, Candidate::Import)));
            }
        }
    }
    let module = sema.tcx.module(at.module).path;
    for layer in prelude::visible(sema, module).into_iter().rev() {
        for (name, res) in layer {
            if fits(res) {
                out.push((*name, Candidate::Elsewhere));
            }
        }
    }
    if kind == NameKind::Value {
        for form in FormName::ALL {
            out.push((enrang_base::intern(form.name()), Candidate::Elsewhere));
        }
    }
    if kind != NameKind::Namespace {
        for name in PrimTy::NAMES {
            out.push((enrang_base::intern(name), Candidate::Elsewhere));
        }
    }
    out
}

/// The members of the namespace for the module at load index `index`, for "did you
/// mean" at a segment of a type path: its `public` types and the types it
/// re-exports when `types` (the last segment); otherwise (a segment a `.` follows)
/// the namespaces it re-exports and its loaded child modules.
pub(crate) fn member_candidates(
    sema: &Sema,
    index: usize,
    types: bool,
) -> Vec<(Symbol, Candidate)> {
    let mut out = Vec::new();
    let is_type = |d: enrang_hir::DefId| {
        matches!(
            sema.tcx.def(d).kind,
            DefKind::Adt(_) | DefKind::TypeAlias | DefKind::StrUnion(_)
        )
    };
    if types {
        for (name, defs) in &sema.res.scopes[index].names {
            if let Some(&d) = defs
                .iter()
                .find(|&&d| sema.tcx.def(d).vis == Vis::Public && is_type(d))
            {
                out.push((*name, Candidate::Item(d)));
            }
        }
    }
    for (name, res) in &sema.res.imports[index] {
        let fits = match res {
            Res::Def(d) => types && is_type(*d),
            Res::Namespace(_) => !types,
            _ => false,
        };
        if fits && reexports(sema, index, *name) {
            out.push((*name, Candidate::Elsewhere));
        }
    }
    if !types {
        let parent = &sema.program.modules[index];
        let prefix = format!("{}/", parent.path);
        for m in &sema.program.modules {
            if m.library == parent.library
                && let Some(rest) = m.path.as_str().strip_prefix(&prefix)
                && !rest.contains('/')
            {
                out.push((enrang_base::intern(rest), Candidate::Elsewhere));
            }
        }
    }
    out
}

/// The locals and labels of the blocks a body is inside, innermost last (plan d.3
/// "Body scopes"). An inner block may shadow an outer name; a same-block
/// redeclaration is EN0307, which the caller reports from [`ScopeStack::declare`].
/// A function's or arrow's parameters and the top level of its body are one block,
/// as in TypeScript and as resolution's walker treats them (`toplevel.rs`).
#[allow(dead_code)] // Labels serve 3A's `break` and `continue`.
#[derive(Clone, Debug, Default)]
pub(crate) struct ScopeStack {
    frames: Vec<BTreeMap<Symbol, LocalId>>,
    labels: Vec<(Symbol, LoopId)>,
}

impl ScopeStack {
    pub fn push(&mut self) {
        self.frames.push(BTreeMap::new());
    }

    pub fn pop(&mut self) {
        self.frames.pop();
    }

    /// Declares `name` in the innermost block; returns the local it replaces in
    /// that same block, if any.
    pub fn declare(&mut self, name: Symbol, local: LocalId) -> Option<LocalId> {
        if self.frames.is_empty() {
            self.push();
        }
        self.frames
            .last_mut()
            .and_then(|frame| frame.insert(name, local))
    }

    pub fn lookup(&self, name: Symbol) -> Option<LocalId> {
        self.frames
            .iter()
            .rev()
            .find_map(|frame| frame.get(&name).copied())
    }

    /// Every local in scope, innermost first, each name once: the candidates of
    /// "did you mean" ([`crate::resolve::suggest::unresolved_with`]).
    pub fn visible(&self) -> Vec<(Symbol, LocalId)> {
        let mut seen = std::collections::BTreeSet::new();
        let mut out = Vec::new();
        for frame in self.frames.iter().rev() {
            for (&name, &local) in frame {
                if seen.insert(name) {
                    out.push((name, local));
                }
            }
        }
        out
    }

    #[allow(dead_code)]
    pub fn push_label(&mut self, name: Symbol, id: LoopId) {
        self.labels.push((name, id));
    }

    #[allow(dead_code)]
    pub fn pop_label(&mut self) {
        self.labels.pop();
    }

    #[allow(dead_code)]
    pub fn label(&self, name: Symbol) -> Option<LoopId> {
        self.labels
            .iter()
            .rev()
            .find(|(n, _)| *n == name)
            .map(|(_, id)| *id)
    }
}
