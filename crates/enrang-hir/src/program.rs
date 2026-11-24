//! What phase 2 returns (A:750 "typed bodies, signatures, module graph"; its fields
//! are silent there).

use std::collections::BTreeMap;
use std::sync::Arc;

use enrang_base::{Span, Symbol};
use enrang_syntax::ast::{CompileKind, TestMode};

use crate::body::{Body, FieldInits};
use crate::ids::{AdtId, DefId, ModuleId, TopVar};
use crate::ty::Ty;

/// A checked program. Maps keyed by id are for lookup only: a reader that produces
/// output walks them in `ItemPath` order (ARCHITECTURE 1).
#[derive(Clone, Debug, Default)]
pub struct CheckedProgram {
    /// Topological order of the imports, ties broken by module path (A:884).
    pub modules: Vec<ModuleId>,
    pub entry: Entry,
    /// Functions, methods, constructors, destructors, local functions, constants'
    /// initialisers and test bodies.
    pub bodies: BTreeMap<DefId, Arc<Body>>,
    /// The entry module's top-level statements.
    pub statements: Option<Arc<Body>>,
    /// Field initialisers and override defaults, typed once per class (SPEC 4.3).
    pub field_inits: BTreeMap<AdtId, FieldInits>,
    /// The test items of the `.test.en` parts loaded in `ParseMode::Test`.
    pub tests: Vec<TestItem>,
    /// Every satisfaction sema's one satisfaction routine recorded (`implements`,
    /// C22, `&I` and by-value interface parameters, bounds, `where`, written type
    /// arguments): one per member found and interface member, the first by site,
    /// sorted by the item paths of `found` then `member`. Phase 3's fitting reads it
    /// (A:1356; M3 plan K6).
    pub satisfactions: Vec<SatisfactionRecord>,
    /// Each local function's hidden arguments, in `TopVar` order: the top-level
    /// variables it reads or writes, directly or through the local functions it
    /// calls, declared above it (N13; M3 plan K7). The HIR `Call` lists none.
    pub hidden_args: BTreeMap<DefId, Vec<TopVar>>,
    /// The program's top-level variables, `TopVar` indexing them (`args` first).
    pub top_vars: Vec<TopVarInfo>,
}

/// One recorded satisfaction (M3 plan K6): `ty` used as the interface `iface` at
/// `site` relies on `found` for the interface member `member`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SatisfactionRecord {
    pub ty: Ty,
    pub iface: Ty,
    pub member: DefId,
    pub found: DefId,
    pub site: Span,
}

/// A top-level variable (SPEC 7, N13; M3 plan K7): its name, the type and
/// mutability the statements gave it, and its declaration (`DUMMY` for `args`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TopVarInfo {
    pub name: Symbol,
    pub ty: Ty,
    pub mutable: bool,
    pub span: Span,
}

/// Where a program starts (SPEC 7).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Default)]
pub enum Entry {
    /// The entry module's top-level statements.
    Statements(ModuleId),
    /// `function main`.
    Main(DefId),
    /// A freestanding `@entry` function.
    EntryFn(DefId),
    /// Nothing runs: a library-like module checked on its own.
    #[default]
    None,
}

/// One test item (SPEC 12).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TestItem {
    /// The ID path: `describe` names and the test's name joined by ` > `.
    pub id: String,
    pub def: DefId,
    pub module: ModuleId,
    pub kind: TestItemKind,
    pub span: Span,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TestItemKind {
    /// `test(...)` or `test.mode(...)`; its body is `BodyOwner::Test(def)`.
    Test { mode: Option<TestMode> },
    /// `compileFails` or `compileOk`, not checked at M2.
    Compile(CompileKind),
}
