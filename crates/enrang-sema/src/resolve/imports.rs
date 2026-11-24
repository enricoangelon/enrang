//! Pass 2 of resolution (plan d.3; SPEC 4.12's binding rule): imports, re-exports,
//! the preludes, each module's import closure, then a program's top-level
//! variables and the names written in bodies (`toplevel.rs`).
//!
//! `import { x } from "p"` binds the `public` item `x` of `p`, or one `p` re-exports
//! (`public import`), resolved to a fixed point along re-export chains; otherwise a
//! namespace for the child module `p/x`, for user folders as for `os` (the loader
//! loaded it); a `private` item is EN0311, and a name that is neither an item of `p`
//! nor a child module EN0305. A child module with top-level statements is EN0312 at
//! the name, as an import of its path would be, and so is a child folder holding
//! one. `import * as n from "p"` binds a
//! namespace for `p`, a folder's own module included. A second binding of one name in
//! a module, by another import or by one of its own items, is EN0307 at the import:
//! between two imports, at the later one in source order, however many re-export
//! rounds either takes to bind.

use std::collections::{BTreeMap, BTreeSet};

use enrang_base::{BitSet, Span, Symbol};
use enrang_diag::{Code, Diagnostic};
use enrang_hir::{DefKind, ModuleId, ModulePath, Res, Vis};
use enrang_syntax::ast;

use crate::cx::Sema;
use crate::load::{ImportEdge, ImportTarget, graph};
use crate::resolve::scope::{child_module, reexports};
use crate::resolve::{prelude, res_of, toplevel};

/// One import name still to bind.
struct Pending<'a> {
    module: usize,
    test_part: bool,
    name: ast::ImportName,
    target: &'a ImportTarget,
    spec: &'a str,
}

/// Binds every import, then the preludes and the closures, then resolves a
/// program's top-level variables and the names its bodies write.
pub(crate) fn resolve(sema: &mut Sema) {
    let program = sema.program;
    let mut pending = Vec::new();
    // The first binding of each name in a module or its part, in source order: a
    // later one is EN0307 against it, whichever would bind first (ARCHITECTURE 1).
    let mut first: BTreeMap<(usize, bool, Symbol), Span> = BTreeMap::new();
    for (index, loaded) in program.modules.iter().enumerate() {
        let parts = std::iter::once((&loaded.ast, &loaded.imports, false)).chain(
            loaded
                .test_part
                .as_ref()
                .map(|p| (&p.ast, &p.imports, true)),
        );
        for (file, edges, test_part) in parts {
            for (import, edge) in file.imports.iter().zip(edges.iter()) {
                let ImportEdge {
                    target: Some(target),
                    ..
                } = edge
                else {
                    // A path that names nothing was reported (EN0305): what it
                    // would bind is not reported again at each use.
                    let names: Vec<Symbol> = match &import.kind {
                        ast::ImportKind::Namespace(alias) => vec![alias.name],
                        ast::ImportKind::Named(names) => names
                            .iter()
                            .map(|n| n.alias.unwrap_or(n.name).name)
                            .collect(),
                    };
                    for name in names {
                        sema.res.failed_imports.insert((index, test_part, name));
                    }
                    continue;
                };
                match &import.kind {
                    ast::ImportKind::Namespace(alias) => {
                        if let ImportTarget::Module(m) = target
                            && !repeated(sema, &mut first, (index, test_part), *alias)
                        {
                            if script(program, *m) {
                                // EN0312 at the import; its members would only
                                // repeat it.
                                sema.res
                                    .failed_imports
                                    .insert((index, test_part, alias.name));
                                continue;
                            }
                            let res = Res::Namespace(sema.module_id(*m));
                            bind(sema, index, test_part, *alias, res);
                        }
                    }
                    ast::ImportKind::Named(names) => {
                        for name in names {
                            let local = name.alias.unwrap_or(name.name);
                            if repeated(sema, &mut first, (index, test_part), local) {
                                continue;
                            }
                            pending.push(Pending {
                                module: index,
                                test_part,
                                name: *name,
                                target,
                                spec: import.path.value.as_str(),
                            });
                        }
                    }
                }
            }
        }
    }
    // Re-export chains resolve to a fixed point: a name bound in one round may be
    // what another module's import re-exports.
    loop {
        let before = pending.len();
        pending.retain(|p| !try_bind(sema, p, false));
        if pending.len() == before {
            break;
        }
    }
    for p in &pending {
        try_bind(sema, p, true);
    }
    prelude::compute(sema);
    closures(sema);
    toplevel::compute(sema);
}

/// Whether `name` was bound before by an import of the same module part; if so,
/// EN0307 at `name`, and it binds nothing.
fn repeated(
    sema: &mut Sema,
    first: &mut BTreeMap<(usize, bool, Symbol), Span>,
    (module, test_part): (usize, bool),
    name: ast::Ident,
) -> bool {
    match first.get(&(module, test_part, name.name)) {
        Some(&earlier) => {
            sema.emit(defined_twice(name, earlier));
            true
        }
        None => {
            first.insert((module, test_part, name.name), name.span);
            false
        }
    }
}

/// Binds `name` in a module's (or its part's) import table; a name the module
/// itself declares is EN0307 (a name two imports bind was reported by
/// [`repeated`]).
fn bind(sema: &mut Sema, module: usize, test_part: bool, name: ast::Ident, res: Res) {
    // The declaration of the same name, and whether it is in the import's file.
    let declared = {
        let scope = &sema.res.scopes[module];
        let own = scope.names.get(&name.name).map(|defs| (defs, !test_part));
        own.or_else(|| {
            test_part
                .then(|| scope.test_names.get(&name.name).map(|defs| (defs, true)))
                .flatten()
        })
        .and_then(|(defs, same_file)| defs.first().map(|&d| (d, same_file)))
        .map(|(d, same_file)| (sema.tcx.def(d).name_span, same_file))
    };
    if let Some((decl, same_file)) = declared {
        // Source order decides which is first (S:13.1): a declaration below the
        // import is the one defined again.
        let diag = if same_file && decl.lo > name.span.lo {
            Diagnostic::new(
                Code::EN0307,
                format!("`{}` is defined twice", name.name),
                decl,
                "defined again here",
            )
            .with_secondary(name.span, format!("the first `{}` is here", name.name))
        } else {
            defined_twice(name, decl)
        };
        sema.emit(diag);
        return;
    }
    sema.res
        .import_spans
        .insert((module, test_part, name.name), name.span);
    let table = if test_part {
        &mut sema.res.test_imports[module]
    } else {
        &mut sema.res.imports[module]
    };
    table.insert(name.name, res);
}

/// EN0307 at a second binding of `name`.
fn defined_twice(name: ast::Ident, first: Span) -> Diagnostic {
    Diagnostic::new(
        Code::EN0307,
        format!("`{}` is defined twice", name.name),
        name.span,
        "defined again here",
    )
    .with_secondary(first, format!("the first `{}` is here", name.name))
}

/// Binds one import name if its target says what it is; with `report`, reports it
/// (EN0305) when it cannot. Returns whether it is done.
fn try_bind(sema: &mut Sema, p: &Pending, report: bool) -> bool {
    let local = p.name.alias.unwrap_or(p.name.name);
    let wanted = p.name.name;
    let child = match p.target {
        ImportTarget::Module(target) => {
            let target = *target;
            if script(sema.program, target) {
                // EN0312 at the import (graph.rs): one mistake, one diagnostic, so
                // its names are neither EN0311 nor EN0305.
                failed(sema, p, local);
                return true;
            }
            if !sema.program.modules[target].folder {
                let defs = sema.res.scopes[target]
                    .names
                    .get(&wanted.name)
                    .cloned()
                    .unwrap_or_default();
                if !defs.is_empty() {
                    let public: Vec<_> = defs
                        .iter()
                        .copied()
                        .filter(|&d| {
                            sema.tcx.def(d).vis == Vis::Public
                                && sema.tcx.def(d).kind != DefKind::LocalFn
                        })
                        .collect();
                    if public.is_empty() {
                        private(sema, wanted, target);
                        failed(sema, p, local);
                    } else {
                        let res = res_of(sema.tcx, &public);
                        bind(sema, p.module, p.test_part, local, res);
                    }
                    return true;
                }
                if reexports(sema, target, wanted.name) {
                    return match sema.res.imports[target].get(&wanted.name).cloned() {
                        Some(res) => {
                            bind(sema, p.module, p.test_part, local, res);
                            true
                        }
                        // The re-export's own import failed and was reported, or
                        // it waits for another round.
                        None => {
                            if report {
                                failed(sema, p, local);
                            }
                            report
                        }
                    };
                }
            }
            child_module(sema, target, wanted.name)
        }
        ImportTarget::Folder(folder) => sema
            .program
            .child_of(ModulePath::new(folder), wanted.name.as_str()),
    };
    if let Some(child) = child {
        if !sema.program.modules[child].ast.stmts.is_empty() {
            let diag = graph::statements_diag(sema, child, wanted.span);
            sema.emit(diag);
        } else if sema.program.modules[child].folder
            && let Some(inner) = graph::script_below(sema.program, child)
        {
            let diag = graph::folder_statements_diag(sema, inner, wanted.span);
            sema.emit(diag);
        }
        let res = Res::Namespace(sema.module_id(child));
        bind(sema, p.module, p.test_part, local, res);
        return true;
    }
    if report {
        sema.err(
            Code::EN0305,
            format!(
                "`{}` is neither an item nor a module of `{}`",
                wanted.name, p.spec
            ),
            wanted.span,
            "not found",
        );
        failed(sema, p, local);
    }
    report
}

/// Whether the module at `index` is a file with top-level statements, which no
/// import may name (EN0312, S:799).
fn script(program: &crate::load::LoadedProgram, index: usize) -> bool {
    let m = &program.modules[index];
    !m.folder && !m.ast.stmts.is_empty()
}

/// Records that `p` bound nothing under `local`, which was reported.
fn failed(sema: &mut Sema, p: &Pending, local: ast::Ident) {
    sema.res
        .failed_imports
        .insert((p.module, p.test_part, local.name));
}

/// EN0311: importing a `private` item.
fn private(sema: &mut Sema, name: ast::Ident, target: usize) {
    let shown = graph::file_name(sema, target);
    sema.err(
        Code::EN0311,
        format!("`{}` is private to `{shown}`", name.name),
        name.span,
        "a private item",
    );
}

/// Each module's import closure, which `extend` lookup reads (A:886; plan choice):
/// for a user module, itself, every library module, and every module its imports
/// reach, transitively; for a library module, the modules its imports and the
/// preludes it sees reach, transitively.
fn closures(sema: &mut Sema) {
    let program = sema.program;
    let count = sema.tcx.module_count();
    let library: Vec<usize> = (0..program.modules.len())
        .filter(|&i| program.modules[i].library)
        .collect();
    let preludes: Vec<Option<usize>> = vec![
        program.index_of("core/prelude"),
        program.index_of("alloc/prelude"),
        program.index_of(&format!("{}/prelude", program.os_folder)),
    ];
    let edges: Vec<Vec<usize>> = program
        .modules
        .iter()
        .map(|m| {
            let mut out: Vec<usize> = m
                .imports
                .iter()
                .chain(m.test_part.iter().flat_map(|p| p.imports.iter()))
                .flat_map(|e| {
                    let mut reached = e.children.clone();
                    if let Some(ImportTarget::Module(t)) = &e.target {
                        reached.push(*t);
                    }
                    reached
                })
                .collect();
            if m.library {
                let path = m.path.as_str();
                let layers = if path.starts_with("core/") {
                    1
                } else if path.starts_with("alloc/") {
                    2
                } else {
                    3
                };
                out.extend(preludes[..layers].iter().flatten().copied());
            }
            out
        })
        .collect();
    for start in 0..program.modules.len() {
        let mut seen = BTreeSet::new();
        let mut stack = vec![start];
        while let Some(m) = stack.pop() {
            if seen.insert(m) {
                stack.extend(edges[m].iter().copied());
            }
        }
        if !program.modules[start].library {
            seen.extend(library.iter().copied());
        }
        let mut closure: BitSet<ModuleId> = BitSet::new(count);
        for i in seen {
            closure.insert(sema.module_id(i));
        }
        let module = sema.module_id(start);
        sema.tcx.module_mut(module).closure = closure;
    }
}
