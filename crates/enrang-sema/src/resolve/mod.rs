//! Name resolution (plan d.3; A:886, SPEC 4.12): two passes over items, then the
//! scopes bodies are typed in.
//!
//! Pass 1 (`items.rs`) gives every item and member a `DefId` with its `ItemPath`
//! and builds each module's scope (EN0307); pass 2 (`imports.rs`) binds imports
//! (EN0305, EN0307, EN0311, EN0312 for a child module), re-exports to a fixed
//! point, the prelude of each layer (`prelude.rs`) and each module's import closure,
//! then `toplevel.rs` collects a program's top-level variables, resolves the names
//! every user body writes (EN0301, EN0307, EN0313, the SPEC 16 names) and computes
//! local functions' hidden arguments. `scope.rs` looks names up from a [`ScopeAt`];
//! `suggest.rs` reports what is not found, with "did you mean".

pub(crate) mod imports;
pub(crate) mod items;
pub(crate) mod prelude;
pub(crate) mod scope;
pub(crate) mod suggest;
pub(crate) mod toplevel;

use std::collections::BTreeMap;

use enrang_base::{BitSet, Symbol};
use enrang_hir::{
    AdtId, DefData, DefId, DefKind, GenericsId, ItemPath, ModuleId, ModuleInfo, ParamId, Res, Tcx,
};
use enrang_syntax::NodeId;

use crate::load::LoadedProgram;

/// Where a name is looked up: the module, the generics in scope (an item's own,
/// linked to its parent's), the class (for visibility), an interface's `Self`,
/// whether the use is in the module's `.test.en` part, the definition whose
/// signature or body is being resolved (a local function sees the top-level
/// variables declared above it, S:981), and whether this is a program's top-level
/// statements (where a local function with hidden arguments may be called).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) struct ScopeAt {
    pub module: ModuleId,
    pub generics: Option<GenericsId>,
    pub class: Option<AdtId>,
    pub self_param: Option<ParamId>,
    pub test_part: bool,
    pub owner: Option<DefId>,
    pub statements: bool,
}

impl ScopeAt {
    /// The top level of `module`.
    pub fn module(module: ModuleId, test_part: bool) -> ScopeAt {
        ScopeAt {
            module,
            generics: None,
            class: None,
            self_param: None,
            test_part,
            owner: None,
            statements: false,
        }
    }

    /// A program's top-level statements in `module`.
    pub fn statements(module: ModuleId) -> ScopeAt {
        ScopeAt {
            statements: true,
            ..ScopeAt::module(module, false)
        }
    }
}

/// The names one module declares, by name; several for an overload set.
#[derive(Clone, Debug, Default)]
pub(crate) struct ModuleScope {
    /// The module's own file's items, local functions included.
    pub names: BTreeMap<Symbol, Vec<DefId>>,
    /// Items of the `.test.en` part, seen only from the part.
    pub test_names: BTreeMap<Symbol, Vec<DefId>>,
}

/// What resolution keeps for the passes after it.
#[derive(Debug, Default)]
pub(crate) struct ResolveTables {
    /// Each loaded module's id, by load index.
    pub modules: Vec<ModuleId>,
    /// The load index of each module.
    pub index_of: BTreeMap<ModuleId, usize>,
    /// Each module's own names, by load index.
    pub scopes: Vec<ModuleScope>,
    /// What each module's imports bind, by load index.
    pub imports: Vec<BTreeMap<Symbol, Res>>,
    /// What each module's `.test.en` part's imports bind.
    pub test_imports: Vec<BTreeMap<Symbol, Res>>,
    /// Where each import binding's name is written: load index, `.test.en` part,
    /// name.
    pub import_spans: BTreeMap<(usize, bool, Symbol), enrang_base::Span>,
    /// The names each layer's prelude adds.
    pub preludes: prelude::Preludes,
    /// The definition of each item node.
    pub item_defs: BTreeMap<NodeId, DefId>,
    /// A program's top-level variables and local functions' hidden arguments.
    pub toplevel: toplevel::TopLevel,
    /// The names imports failed to bind, reported at the import (EN0305 for a path
    /// or a name that names nothing, EN0311 for a private item): load index,
    /// `.test.en` part, local name. A use of one is not reported again.
    pub failed_imports: std::collections::BTreeSet<(usize, bool, Symbol)>,
}

impl ResolveTables {
    /// The load index of `module`.
    pub fn index(&self, module: ModuleId) -> usize {
        self.index_of[&module]
    }

    /// Whether `name`, unresolved at `at`, is the local name of an import that
    /// failed and was reported, by the module or, from its part, by the part.
    pub fn import_failed(&self, at: ScopeAt, name: Symbol) -> bool {
        let index = self.index(at.module);
        self.failed_imports.contains(&(index, false, name))
            || (at.test_part && self.failed_imports.contains(&(index, true, name)))
    }
}

/// Defines every loaded module in `tcx`, in load order, each with its
/// `DefKind::Module` definition.
pub(crate) fn define_modules(tcx: &mut Tcx, program: &LoadedProgram, tables: &mut ResolveTables) {
    for (index, loaded) in program.modules.iter().enumerate() {
        let mut info = ModuleInfo::new(loaded.path, loaded.library, loaded.file);
        info.test_part = loaded.test_part.as_ref().map(|p| p.file);
        info.has_statements = !loaded.ast.stmts.is_empty();
        let module = tcx.define_module(info);
        let def = tcx.define_def(DefData::new(
            ItemPath::module(loaded.path),
            DefKind::Module,
            module,
            loaded.ast.span,
        ));
        tcx.module_mut(module).def = Some(def);
        tables.modules.push(module);
        tables.index_of.insert(module, index);
        tables.scopes.push(ModuleScope::default());
        tables.imports.push(BTreeMap::new());
        tables.test_imports.push(BTreeMap::new());
    }
    let count = tcx.module_count();
    for &module in &tables.modules {
        tcx.module_mut(module).closure = BitSet::new(count);
    }
}

/// The `Res` of a set of definitions of one name: an overload set for functions,
/// the definition itself otherwise.
pub(crate) fn res_of(tcx: &Tcx, defs: &[DefId]) -> Res {
    match defs {
        [] => Res::Err,
        [one]
            if !matches!(
                tcx.def(*one).kind,
                DefKind::Fn | DefKind::LocalFn | DefKind::DeclareFn
            ) =>
        {
            Res::Def(*one)
        }
        many => Res::Fns(many.to_vec()),
    }
}
