//! The module graph (plan d.2; A:884, SPEC 4.12): import cycles, imports of files
//! with top-level statements, and the order modules are checked in.
//!
//! The edges of a module are its own file's imports, each to the module it names
//! and to the child modules its names reach (`p/x`), re-exports included, since a
//! `public import` is an import ("the cycle check follows re-exports"); a `.test.en`
//! part is a unit above its module, so its imports are no edges (SPEC 4.12). For the
//! order only, every module also depends on the preludes it sees (A:884, SPEC 8.1).
//!
//! - EN0304: each strongly connected set of user modules, or a module importing
//!   itself, is one cycle, reported at the import that closes it in the module with
//!   the least path, the first of its imports (in source order) that leads back into
//!   the set; the message follows the shortest path back. Library modules are the
//!   library's own business (rtlib's tests).
//! - EN0312: an import, test parts' included, of a module with top-level statements,
//!   or of a folder as a namespace with such a module below it, with the help to
//!   write `unsafe let` when one of them is a plain `let` (S:758).
//! - The order: the topological order of the condensed graph, a module's imports
//!   first, ready sets broken by the least module path of each set and the members
//!   of a set by path (A:884), so no order depends on load order or file listing.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use enrang_base::Span;
use enrang_diag::{Code, Diagnostic, Help};
use enrang_hir::{ModuleId, ModulePath};
use enrang_syntax::ast;

use crate::cx::Sema;
use crate::load::{ImportEdge, ImportTarget, LoadedProgram};

/// Reports EN0304 and EN0312 and returns the order modules are checked in.
pub(crate) fn check(sema: &mut Sema) -> Vec<ModuleId> {
    let program = sema.program;
    let edges = import_edges(program);
    let with_preludes = order_edges(program, &edges);
    let sccs = tarjan(&with_preludes);
    for scc in &sccs {
        report_cycle(sema, scc, &edges);
    }
    statements_imported(sema);
    order(program, &with_preludes, &sccs)
        .into_iter()
        .map(|index| sema.module_id(index))
        .collect()
}

/// The modules one import declaration leads to.
fn reached(edge: &ImportEdge) -> Vec<usize> {
    let mut out = Vec::new();
    if let Some(ImportTarget::Module(m)) = &edge.target {
        out.push(*m);
    }
    out.extend(edge.children.iter().copied());
    out
}

/// Each module's own imports, as the modules each declaration leads to, in source
/// order.
fn import_edges(program: &LoadedProgram) -> Vec<Vec<Vec<usize>>> {
    program
        .modules
        .iter()
        .map(|m| m.imports.iter().map(reached).collect())
        .collect()
}

/// The edges the order and the strongly connected sets are computed on: the import
/// edges, then the preludes each module sees.
fn order_edges(program: &LoadedProgram, edges: &[Vec<Vec<usize>>]) -> Vec<Vec<usize>> {
    let core = program.index_of("core/prelude");
    let alloc = program.index_of("alloc/prelude");
    let os = program.index_of(&format!("{}/prelude", program.os_folder));
    program
        .modules
        .iter()
        .enumerate()
        .map(|(index, m)| {
            let mut out: Vec<usize> = edges[index].iter().flatten().copied().collect();
            let path = m.path.as_str();
            let in_core = m.library && (path == "core" || path.starts_with("core/"));
            let in_alloc = m.library && (path == "alloc" || path.starts_with("alloc/"));
            let mut seen = vec![core];
            if !in_core {
                seen.push(alloc);
                if !in_alloc {
                    seen.push(os);
                }
            }
            out.extend(seen.into_iter().flatten().filter(|&p| p != index));
            out
        })
        .collect()
}

/// Tarjan's strongly connected components, each sorted by load index.
fn tarjan(edges: &[Vec<usize>]) -> Vec<Vec<usize>> {
    struct State<'e> {
        edges: &'e [Vec<usize>],
        index: Vec<Option<usize>>,
        low: Vec<usize>,
        on_stack: Vec<bool>,
        stack: Vec<usize>,
        next: usize,
        out: Vec<Vec<usize>>,
    }
    fn visit(s: &mut State, v: usize) {
        s.index[v] = Some(s.next);
        s.low[v] = s.next;
        s.next += 1;
        s.stack.push(v);
        s.on_stack[v] = true;
        for &w in &s.edges[v] {
            match s.index[w] {
                None => {
                    visit(s, w);
                    s.low[v] = s.low[v].min(s.low[w]);
                }
                Some(iw) if s.on_stack[w] => s.low[v] = s.low[v].min(iw),
                Some(_) => {}
            }
        }
        if Some(s.low[v]) == s.index[v] {
            let mut scc = Vec::new();
            while let Some(w) = s.stack.pop() {
                s.on_stack[w] = false;
                scc.push(w);
                if w == v {
                    break;
                }
            }
            scc.sort_unstable();
            s.out.push(scc);
        }
    }
    let n = edges.len();
    let mut s = State {
        edges,
        index: vec![None; n],
        low: vec![0; n],
        on_stack: vec![false; n],
        stack: Vec::new(),
        next: 0,
        out: Vec::new(),
    };
    for v in 0..n {
        if s.index[v].is_none() {
            visit(&mut s, v);
        }
    }
    s.out
}

/// The file name a message shows for a module (`user.en`), as EN0311 does.
pub(crate) fn file_name(sema: &Sema, index: usize) -> String {
    let file = sema.program.modules[index].file;
    let shown = sema.tcx.map().file(file).path.display().to_string();
    shown
        .trim_end_matches('/')
        .rsplit('/')
        .next()
        .unwrap_or(&shown)
        .to_owned()
}

/// EN0304 for one strongly connected set, if it is a cycle of user modules.
fn report_cycle(sema: &mut Sema, scc: &[usize], edges: &[Vec<Vec<usize>>]) {
    let program = sema.program;
    if scc.iter().any(|&m| program.modules[m].library) {
        return;
    }
    let members: BTreeSet<usize> = scc.iter().copied().collect();
    let first = *scc
        .iter()
        .min_by_key(|&&m| program.modules[m].path)
        .expect("a component has a member");
    // The first import of the least module that leads back into the set.
    let Some((import, next)) = edges[first].iter().enumerate().find_map(|(i, reached)| {
        reached
            .iter()
            .find(|m| members.contains(m))
            .map(|&next| (i, next))
    }) else {
        return;
    };
    let span = program.modules[first].ast.imports[import].path.span;
    let message = if next == first {
        format!("import cycle: `{}` imports itself", file_name(sema, first))
    } else {
        let chain = path_back(edges, &members, next, first);
        let mut text = format!(
            "import cycle: `{}` imports `{}`",
            file_name(sema, first),
            file_name(sema, next)
        );
        for &m in &chain {
            text.push_str(&format!(", which imports `{}`", file_name(sema, m)));
        }
        text
    };
    sema.err(Code::EN0304, message, span, "this import closes the cycle");
}

/// The modules after `from` on the shortest import path from `from` to `to` inside
/// `members`, `to` last; ties go to the earlier import.
fn path_back(
    edges: &[Vec<Vec<usize>>],
    members: &BTreeSet<usize>,
    from: usize,
    to: usize,
) -> Vec<usize> {
    let mut parent: BTreeMap<usize, usize> = BTreeMap::new();
    let mut queue = VecDeque::from([from]);
    let mut seen = BTreeSet::from([from]);
    while let Some(m) = queue.pop_front() {
        if m == to {
            break;
        }
        for &next in edges[m].iter().flatten() {
            if members.contains(&next) && seen.insert(next) {
                parent.insert(next, m);
                queue.push_back(next);
            }
        }
    }
    let mut chain = vec![to];
    let mut at = to;
    while let Some(&p) = parent.get(&at) {
        if p == from {
            break;
        }
        chain.push(p);
        at = p;
    }
    chain.reverse();
    chain
}

/// EN0312 at every import of a module with top-level statements. A folder imported
/// as a namespace binds every module below it (SPEC 4.12), so its import is EN0312
/// when one of them has statements: the first by path is named, and the entry is
/// never one (it is the program, not a module of the folder).
fn statements_imported(sema: &mut Sema) {
    let program = sema.program;
    let mut found = Vec::new();
    for module in &program.modules {
        let parts = std::iter::once((&module.ast, &module.imports))
            .chain(module.test_part.iter().map(|p| (&p.ast, &p.imports)));
        for (file, edges) in parts {
            for (import, edge) in file.imports.iter().zip(edges) {
                let Some(ImportTarget::Module(m)) = &edge.target else {
                    continue;
                };
                if !program.modules[*m].ast.stmts.is_empty() {
                    found.push((*m, import.path.span, None));
                } else if program.modules[*m].folder
                    && let Some(inner) = script_below(program, *m)
                {
                    found.push((inner, import.path.span, Some(*m)));
                }
            }
        }
    }
    for (target, span, folder) in found {
        let diag = match folder {
            Some(_) => folder_statements_diag(sema, target, span),
            None => statements_diag(sema, target, span),
        };
        sema.emit(diag);
    }
}

/// EN0312 for a folder imported at `span` (as a namespace, or by name as a child
/// of its parent) that holds the module `target` with top-level statements.
pub(crate) fn folder_statements_diag(sema: &Sema, target: usize, span: Span) -> Diagnostic {
    let mut diag = statements_diag(sema, target, span);
    let shown = sema
        .tcx
        .map()
        .file(sema.program.modules[target].file)
        .path
        .display();
    diag.primary.text = format!("the folder imported here holds `{shown}`");
    diag
}

/// The module below the folder module `folder`, by least path, that has top-level
/// statements, other than the entry.
pub(crate) fn script_below(program: &LoadedProgram, folder: usize) -> Option<usize> {
    let path = program.modules[folder].path.as_str();
    let library = program.modules[folder].library;
    let below = |m: &str| user_below(path, m);
    (0..program.modules.len())
        .filter(|&i| {
            let m = &program.modules[i];
            i != program.entry
                && m.library == library
                && below(m.path.as_str())
                && !m.ast.stmts.is_empty()
        })
        .min_by_key(|&i| program.modules[i].path)
}

/// Whether the module path `m` lies below the folder path `folder`, both
/// normalised. The input's directory itself, `.` (reached as `../app` from
/// `app/`), holds every module that does not lead out of it; a folder of `..`
/// only, `k` of them, holds every module with fewer than `k` leading `..`, and
/// those with `k` and more after them; any other folder the paths below it.
fn user_below(folder: &str, m: &str) -> bool {
    let ups = |p: &str| p.split('/').take_while(|s| *s == "..").count();
    if folder == "." {
        return ups(m) == 0 && !m.starts_with('/');
    }
    let k = folder.split('/').count();
    if ups(folder) == k {
        let j = ups(m);
        return j < k || (j == k && m.split('/').count() > k);
    }
    m.starts_with(&format!("{folder}/"))
}

/// EN0312: `target` has top-level statements and is imported at `span`.
pub(crate) fn statements_diag(sema: &Sema, target: usize, span: Span) -> Diagnostic {
    let stmts = &sema.program.modules[target].ast.stmts;
    let name = file_name(sema, target);
    let plain_let = stmts.iter().find(|s| {
        matches!(
            &s.kind,
            ast::StmtKind::VarDecl(v) if v.mutable
        )
    });
    let mut diag = Diagnostic::new(
        Code::EN0312,
        format!("`{name}` has top-level statements, so it can't be imported"),
        span,
        "imported here",
    );
    match plain_let {
        Some(stmt) => {
            diag = diag
                .with_secondary(stmt.span, "a plain top-level `let` is a statement")
                .with_help(Help::text("for static storage, write `unsafe let`"));
        }
        None => {
            if let Some(stmt) = stmts.first() {
                diag = diag.with_secondary(stmt.span, "the first top-level statement is here");
            }
        }
    }
    diag
}

/// Kahn's algorithm over the condensed graph; dependencies first.
fn order(program: &LoadedProgram, edges: &[Vec<usize>], sccs: &[Vec<usize>]) -> Vec<usize> {
    let mut scc_of = vec![0; edges.len()];
    for (i, scc) in sccs.iter().enumerate() {
        for &m in scc {
            scc_of[m] = i;
        }
    }
    let key = |i: usize| -> ModulePath {
        sccs[i]
            .iter()
            .map(|&m| program.modules[m].path)
            .min()
            .expect("a component has a member")
    };
    let mut deps: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); sccs.len()];
    let mut dependents: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); sccs.len()];
    for (m, out) in edges.iter().enumerate() {
        for &dep in out {
            let (a, b) = (scc_of[m], scc_of[dep]);
            if a != b {
                deps[a].insert(b);
                dependents[b].insert(a);
            }
        }
    }
    let mut ready: BTreeSet<(ModulePath, usize)> = (0..sccs.len())
        .filter(|&i| deps[i].is_empty())
        .map(|i| (key(i), i))
        .collect();
    let mut out = Vec::with_capacity(edges.len());
    while let Some(first) = ready.pop_first() {
        let i = first.1;
        let mut members = sccs[i].clone();
        members.sort_by_key(|&m| program.modules[m].path);
        out.extend(members);
        for &d in &dependents[i] {
            deps[d].remove(&i);
            if deps[d].is_empty() {
                ready.insert((key(d), d));
            }
        }
    }
    out
}
