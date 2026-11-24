//! The prelude, injected per target layer (A:884, SPEC 8.1): every module sees,
//! below its own items and imports, the public names of `core/prelude`; every
//! module outside `core` those of `alloc/prelude`; every module outside `core` and
//! `alloc` those of `os/<layer>/prelude`. A prelude's public names are its
//! `public` items and what it re-exports.

use std::collections::BTreeMap;

use enrang_base::Symbol;
use enrang_hir::{DefKind, ModulePath, Res, Vis};
use enrang_syntax::ast;

use crate::cx::Sema;
use crate::resolve::res_of;

/// The names each layer's prelude adds.
#[derive(Clone, Debug, Default)]
pub(crate) struct Preludes {
    pub core: BTreeMap<Symbol, Res>,
    pub alloc: BTreeMap<Symbol, Res>,
    pub os: BTreeMap<Symbol, Res>,
}

pub(crate) fn compute(sema: &mut Sema) {
    let os = format!("{}/prelude", sema.program.os_folder);
    sema.res.preludes = Preludes {
        core: names_of(sema, "core/prelude"),
        alloc: names_of(sema, "alloc/prelude"),
        os: names_of(sema, &os),
    };
}

/// The public names of the module at `path`, empty when it is not loaded.
fn names_of(sema: &Sema, path: &str) -> BTreeMap<Symbol, Res> {
    let path = ModulePath::new(path);
    let Some(index) = sema.program.modules.iter().position(|m| m.path == path) else {
        return BTreeMap::new();
    };
    let mut names = BTreeMap::new();
    for (name, defs) in &sema.res.scopes[index].names {
        let public: Vec<_> = defs
            .iter()
            .copied()
            .filter(|&d| {
                sema.tcx.def(d).vis == Vis::Public && sema.tcx.def(d).kind != DefKind::LocalFn
            })
            .collect();
        if !public.is_empty() {
            names.insert(*name, res_of(sema.tcx, &public));
        }
    }
    for import in &sema.program.modules[index].ast.imports {
        if !import.public {
            continue;
        }
        let bound: Vec<Symbol> = match &import.kind {
            ast::ImportKind::Named(list) => list
                .iter()
                .map(|n| n.alias.unwrap_or(n.name).name)
                .collect(),
            ast::ImportKind::Namespace(alias) => vec![alias.name],
        };
        for name in bound {
            if let Some(res) = sema.res.imports[index].get(&name) {
                names.insert(name, res.clone());
            }
        }
    }
    names
}

/// The preludes a module sees, nearest layer last. Only a library module is in a
/// layer: a user module's path never reads as a library key (`load/paths.rs`).
pub(crate) fn visible<'t>(sema: &'t Sema, module: ModulePath) -> Vec<&'t BTreeMap<Symbol, Res>> {
    let path = module.as_str();
    let library = module.is_library();
    let in_core = library && (path == "core" || path.starts_with("core/"));
    let in_alloc = library && (path == "alloc" || path.starts_with("alloc/"));
    let mut layers = vec![&sema.res.preludes.core];
    if !in_core {
        layers.push(&sema.res.preludes.alloc);
        if !in_alloc {
            layers.push(&sema.res.preludes.os);
        }
    }
    layers
}
