//! The module loader (plan d.2; A:884, SPEC 4.12): phase 1 of a program.
//!
//! Order, for determinism (ARCHITECTURE 1): the entry, then its `.test.en` part
//! (in `ParseMode::Test`), then a breadth-first walk of import declarations in source
//! order, each module loaded once; then every module of `core`, `alloc` and
//! `os/<layer>` in key order (plan choice: the whole library of the target's layers
//! is loaded on every run), and whatever their imports reach. Module indices follow
//! load order, and nothing in output depends on them.
//!
//! User files are added to the source map as `FileOrigin::User` under their
//! normalised path relative to the input's directory (`src/util.en`, never
//! `./src/util.en`), and a user module's path is that path, spelled `./core/x` when
//! it reads as a library key (`paths.rs`); library files as
//! `FileOrigin::Library` under `lib/<key>.en`, which is how the parser knows a
//! library module (SPEC 3.1). An import that names nothing is EN0305 at its path,
//! recorded here and reported at the start of phase 2.
//!
//! SPEC 4.12's binding rule reaches child modules: `import { serial, vga } from
//! "./drivers"` names the modules `drivers/serial.en` and `drivers/vga.en`, and
//! `import { x } from "./p"` names the child module `p/x` when `p` declares no `x`;
//! the loader loads each such child when the import is walked (an import's
//! [`ImportEdge::children`]). `import * as d from "./drivers"` binds a namespace for
//! the folder itself: the loader gives the folder a module of its own with no text
//! ([`LoadedModule::folder`], an empty file in the source map, plan choice, since a
//! namespace is a `ModuleId`), and loads every child module and sub-folder of it, so
//! `d.serial` resolves. The cycle check, EN0312 and the topological order are
//! `graph.rs`'s.

pub(crate) mod graph;
mod paths;
mod source;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use enrang_base::{FileId, FileOrigin, SourceMap, Span, Symbol};
use enrang_diag::{Code, DiagCtx, Diagnostic};
use enrang_hir::ModulePath;
use enrang_syntax::{NodeIdGen, ParseMode, ast, parse_file, report_invalid_utf8};
use enrang_target::TargetSpec;

use crate::{LoadError, ProgramInput};
use paths::Spec;
use source::{Child, SourceProvider};

/// A loaded program: its modules in load order, the entry first.
#[derive(Debug)]
pub struct LoadedProgram {
    pub modules: Vec<LoadedModule>,
    /// The index of the entry module (always 0).
    pub entry: usize,
    pub mode: ParseMode,
    /// The OS layer's library folder (`os/linux_x64`).
    pub os_folder: &'static str,
    /// What loading found for phase 2 to report (EN0305).
    pub(crate) pending: Vec<Diagnostic>,
    /// The load index of each module path.
    pub(crate) by_path: BTreeMap<ModulePath, usize>,
    /// The child module `p/x` of each parent module path `p` the loader reached,
    /// by name, as the loader spelled it (`x` for the input directory `.`, and a
    /// path that re-enters the input directory spelled from inside it).
    pub(crate) children: BTreeMap<(ModulePath, String), usize>,
}

impl LoadedProgram {
    /// The load index of the module at `path` (`src/util`, `core/mem`), if loaded.
    pub fn index_of(&self, path: &str) -> Option<usize> {
        self.by_path.get(&ModulePath::new(path)).copied()
    }

    /// The loaded child module `parent/name` (SPEC 4.12), built the one way the
    /// loader builds it, so the input directory `.` and a path re-entering it name
    /// the same module whichever way the entry was spelled (plan d.2, G31).
    pub(crate) fn child_of(&self, parent: ModulePath, name: &str) -> Option<usize> {
        if let Some(&index) = self.children.get(&(parent, name.to_owned())) {
            return Some(index);
        }
        if parent.is_library() {
            return self.index_of(&format!("{parent}/{name}"));
        }
        let rel = match paths::user_rel(parent) {
            "." => name.to_owned(),
            rel => format!("{rel}/{name}"),
        };
        self.by_path.get(&paths::user_module(&rel)).copied()
    }
}

/// One module: its own file, and in `ParseMode::Test` its `.test.en` part.
#[derive(Debug)]
pub struct LoadedModule {
    pub path: ModulePath,
    pub library: bool,
    pub file: FileId,
    pub ast: ast::File,
    /// One per `ast.imports` entry.
    pub imports: Vec<ImportEdge>,
    pub test_part: Option<LoadedPart>,
    /// A folder imported as a namespace: no text of its own, and its members are
    /// its child modules (SPEC 4.12).
    pub folder: bool,
}

/// A module's `.test.en` part, a unit above it (A:884).
#[derive(Debug)]
pub struct LoadedPart {
    pub file: FileId,
    pub ast: ast::File,
    /// One per `ast.imports` entry; not counted for EN0304.
    pub imports: Vec<ImportEdge>,
}

/// Where one import declaration leads; `target` is `None` when its path names
/// nothing (EN0305).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportEdge {
    pub target: Option<ImportTarget>,
    /// The child modules its names reach (`p/x`, SPEC 4.12), by load index, in the
    /// order the names are written.
    pub children: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ImportTarget {
    /// A module, by load index: a file, or a folder imported as a namespace.
    Module(usize),
    /// A folder whose files are child modules (SPEC 4.12), named by `{ x }`: the
    /// module path a user folder would have (`src/drivers`, `./core`), or its library
    /// key (`core`, `os/linux_x64`), so `{folder}/{x}` is its child's module path.
    Folder(String),
}

/// A user file that could not be read: the module's own file, or its `.test.en`
/// part (`part` names it).
struct Unread {
    part: Option<PathBuf>,
    error: std::io::Error,
}

/// What one import declaration asks for, copied out of the tree.
struct ImportAsk {
    spec: Arc<str>,
    span: Span,
    /// `None` for `* as n`; the names of `{ ... }` otherwise.
    names: Option<Vec<Symbol>>,
}

struct Loader<'i, 'm> {
    provider: SourceProvider<'i>,
    map: &'m mut SourceMap,
    ids: &'m mut NodeIdGen,
    dcx: &'m mut DiagCtx,
    mode: ParseMode,
    os_folder: &'static str,
    modules: Vec<LoadedModule>,
    by_path: BTreeMap<ModulePath, usize>,
    children: BTreeMap<(ModulePath, String), usize>,
    pending: Vec<Diagnostic>,
}

pub(crate) fn load(
    input: &ProgramInput,
    target: &TargetSpec,
    map: &mut SourceMap,
    ids: &mut NodeIdGen,
    dcx: &mut DiagCtx,
) -> Result<LoadedProgram, LoadError> {
    let mut loader = Loader {
        provider: SourceProvider::new(input),
        map,
        ids,
        dcx,
        mode: input.mode,
        os_folder: paths::os_folder(target.os),
        modules: Vec::new(),
        by_path: BTreeMap::new(),
        children: BTreeMap::new(),
        pending: Vec::new(),
    };
    let entry = paths::normalize(&input.entry);
    if let Err(Unread { part, error }) = loader.load_user(&entry) {
        return Err(LoadError::Unreadable {
            path: part.unwrap_or_else(|| input.entry.clone()),
            error,
        });
    }
    // A compile fixture of a library-only rule is a library module (G50).
    if input.library_entry
        && let Some(entry) = loader.modules.first_mut()
    {
        entry.library = true;
    }
    let mut next = 0;
    loop {
        while next < loader.modules.len() {
            loader.resolve_imports(next);
            next += 1;
        }
        let missing: Vec<String> = loader
            .provider
            .lib_keys()
            .into_iter()
            .filter(|key| loader.in_layers(key))
            .filter(|key| !loader.by_path.contains_key(&ModulePath::new(key)))
            .collect();
        if missing.is_empty() {
            break;
        }
        for key in missing {
            loader.load_lib(&key);
        }
    }
    loader.dcx.finish_phase().map_err(LoadError::Aborted)?;
    Ok(LoadedProgram {
        modules: loader.modules,
        entry: 0,
        mode: input.mode,
        os_folder: loader.os_folder,
        pending: loader.pending,
        by_path: loader.by_path,
        children: loader.children,
    })
}

/// The name an item declares in its module's scope, if any.
pub(crate) fn item_name(item: &ast::Item) -> Option<ast::Ident> {
    match &item.kind {
        ast::ItemKind::Function(f) => Some(f.name),
        ast::ItemKind::Class(c) => Some(c.name),
        ast::ItemKind::Enum(e) => Some(e.name),
        ast::ItemKind::Interface(i) => Some(i.name),
        ast::ItemKind::TypeAlias(a) => Some(a.name),
        ast::ItemKind::TopConst(c) => Some(c.name),
        ast::ItemKind::UnsafeLet(u) => Some(u.name),
        ast::ItemKind::DeclareFn(d) => Some(d.name),
        ast::ItemKind::Extend(_)
        | ast::ItemKind::StaticAssert { .. }
        | ast::ItemKind::Describe(_)
        | ast::ItemKind::Test(_)
        | ast::ItemKind::CompileCase(_) => None,
    }
}

/// Whether `file` declares `name`: an item, a local function, or a name one of its
/// `public import`s re-exports.
fn declares(file: &ast::File, name: Symbol) -> bool {
    file.items
        .iter()
        .any(|i| item_name(i).is_some_and(|n| n.name == name))
        || file.stmts.iter().any(
            |s| matches!(&s.kind, ast::StmtKind::LocalFn { decl, .. } if decl.name.name == name),
        )
        || file.imports.iter().any(|i| {
            i.public
                && match &i.kind {
                    ast::ImportKind::Named(names) => {
                        names.iter().any(|n| n.alias.unwrap_or(n.name).name == name)
                    }
                    ast::ImportKind::Namespace(alias) => alias.name == name,
                }
        })
}

fn asks(file: &ast::File) -> Vec<ImportAsk> {
    file.imports
        .iter()
        .map(|i| ImportAsk {
            spec: Arc::from(i.path.value.as_str()),
            span: i.path.span,
            names: match &i.kind {
                ast::ImportKind::Named(names) => Some(names.iter().map(|n| n.name.name).collect()),
                ast::ImportKind::Namespace(_) => None,
            },
        })
        .collect()
}

impl Loader<'_, '_> {
    /// Whether a library key belongs to a layer the target loads.
    fn in_layers(&self, key: &str) -> bool {
        ["core", "alloc", self.os_folder]
            .iter()
            .any(|layer| key.starts_with(&format!("{layer}/")))
    }

    fn parse(&mut self, file: FileId) -> ast::File {
        parse_file(self.map.file(file), self.ids, self.mode, self.dcx)
    }

    /// The user path (without `.en`) or library key of module `index`, which its
    /// relative imports and child modules start from.
    fn rel(&self, index: usize) -> &'static str {
        let m = &self.modules[index];
        if m.library {
            m.path.as_str()
        } else {
            paths::user_rel(m.path)
        }
    }

    /// The module path of the user or library file or folder `rel`.
    fn module_path(rel: &str, library: bool) -> ModulePath {
        if library {
            ModulePath::new(rel)
        } else {
            paths::user_module(rel)
        }
    }

    /// Reads, adds and parses a user file and, in `ParseMode::Test`, its part.
    /// `rel` is normalised. A part that exists and cannot be read stops the load as
    /// the file itself would: the module is never checked without it.
    fn load_user(&mut self, rel: &Path) -> Result<usize, Unread> {
        let spelled = paths::rel_of(rel);
        let inside = self.provider.reenter(&spelled);
        let reentered = (inside != spelled).then(|| PathBuf::from(format!("{inside}.en")));
        let rel = reentered.as_deref().unwrap_or(rel);
        let path = paths::user_module(&inside);
        if let Some(&index) = self.by_path.get(&path) {
            return Ok(index);
        }
        let part = (self.mode == ParseMode::Test)
            .then(|| paths::test_part_of(rel))
            .flatten()
            .filter(|part| self.provider.user_exists(part));
        let text = self
            .provider
            .read_user(rel)
            .map_err(|error| Unread { part: None, error })?;
        let part_text = match &part {
            Some(part) => Some(self.provider.read_user(part).map_err(|error| Unread {
                part: Some(part.clone()),
                error,
            })?),
            None => None,
        };
        let file = self.map.add(rel.to_path_buf(), text.text, FileOrigin::User);
        report_invalid_utf8(self.map.file(file), &text.invalid, self.dcx);
        let ast = self.parse(file);
        let mut test_part = None;
        if let (Some(part), Some(text)) = (part, part_text) {
            let part_file = self.map.add(part, text.text, FileOrigin::User);
            report_invalid_utf8(self.map.file(part_file), &text.invalid, self.dcx);
            let part_ast = self.parse(part_file);
            test_part = Some(LoadedPart {
                file: part_file,
                ast: part_ast,
                imports: Vec::new(),
            });
        }
        Ok(self.push(path, false, file, ast, test_part, false))
    }

    /// Adds and parses a library module.
    fn load_lib(&mut self, key: &str) -> Option<usize> {
        let path = ModulePath::new(key);
        if let Some(&index) = self.by_path.get(&path) {
            return Some(index);
        }
        let text = self.provider.lib(key)?;
        let file = self.map.add(
            PathBuf::from(format!("lib/{key}.en")),
            text,
            FileOrigin::Library,
        );
        let ast = self.parse(file);
        Some(self.push(path, true, file, ast, None, false))
    }

    /// The module of a folder imported as a namespace, created with no text, and
    /// every child module and sub-folder of it loaded.
    fn folder_module(&mut self, folder: &str, library: bool) -> usize {
        let inside = match library {
            true => folder.to_owned(),
            false => self.provider.reenter(folder),
        };
        let folder = inside.as_str();
        let path = Self::module_path(folder, library);
        if let Some(&index) = self.by_path.get(&path) {
            return index;
        }
        let (shown, origin) = if library {
            (format!("lib/{folder}/"), FileOrigin::Library)
        } else {
            (format!("{folder}/"), FileOrigin::User)
        };
        let file = self.map.add(PathBuf::from(shown), Arc::from(""), origin);
        let start = self.map.file(file).start;
        let ast = ast::File {
            imports: Vec::new(),
            stmts: Vec::new(),
            items: Vec::new(),
            span: Span {
                lo: start,
                hi: start,
            },
        };
        let index = self.push(path, library, file, ast, None, true);
        let children = if library {
            self.provider.lib_children(folder)
        } else {
            self.provider.user_children(Path::new(folder))
        };
        for child in children {
            match child {
                Child::File(name) | Child::Folder(name) => {
                    self.child(folder, library, &name);
                }
            }
        }
        index
    }

    /// The child module `parent/name`: a file, or a sub-folder as a namespace,
    /// recorded for the resolver ([`LoadedProgram::child_of`]).
    fn child(&mut self, parent: &str, library: bool, name: &str) -> Option<usize> {
        let index = self.child_unrecorded(parent, library, name)?;
        self.children
            .insert((Self::module_path(parent, library), name.to_owned()), index);
        Some(index)
    }

    fn child_unrecorded(&mut self, parent: &str, library: bool, name: &str) -> Option<usize> {
        let path = match (library, parent) {
            (false, ".") => name.to_owned(),
            (false, _) => self.provider.reenter(&format!("{parent}/{name}")),
            (true, _) => format!("{parent}/{name}"),
        };
        if let Some(&index) = self.by_path.get(&Self::module_path(&path, library)) {
            return Some(index);
        }
        if library {
            if self.provider.lib(&path).is_some() {
                return self.load_lib(&path);
            }
            if self.provider.lib_is_folder(&path) {
                return Some(self.folder_module(&path, true));
            }
            return None;
        }
        let file = PathBuf::from(format!("{path}.en"));
        if self.provider.user_exists(&file) {
            return self.load_user(&file).ok();
        }
        if self.provider.user_is_dir(Path::new(&path)) {
            return Some(self.folder_module(&path, false));
        }
        None
    }

    fn push(
        &mut self,
        path: ModulePath,
        library: bool,
        file: FileId,
        ast: ast::File,
        test_part: Option<LoadedPart>,
        folder: bool,
    ) -> usize {
        let index = self.modules.len();
        self.by_path.insert(path, index);
        self.modules.push(LoadedModule {
            path,
            library,
            file,
            ast,
            imports: Vec::new(),
            test_part,
            folder,
        });
        index
    }

    /// Resolves every import of module `index`, loading what they reach.
    fn resolve_imports(&mut self, index: usize) {
        let own = asks(&self.modules[index].ast);
        let part = self.modules[index]
            .test_part
            .as_ref()
            .map(|p| asks(&p.ast))
            .unwrap_or_default();
        let edges: Vec<ImportEdge> = own.iter().map(|ask| self.resolve_one(index, ask)).collect();
        self.modules[index].imports = edges;
        let edges: Vec<ImportEdge> = part
            .iter()
            .map(|ask| self.resolve_one(index, ask))
            .collect();
        if let Some(part) = &mut self.modules[index].test_part {
            part.imports = edges;
        }
    }

    fn resolve_one(&mut self, importer: usize, ask: &ImportAsk) -> ImportEdge {
        let from = self.rel(importer);
        let library = self.modules[importer].library;
        let mut children = Vec::new();
        let spec = paths::classify(&ask.spec, from, library, self.os_folder);
        if let Spec::User(rel) = &spec
            && rel
                .rsplit('/')
                .next()
                .is_some_and(|last| last.ends_with(".test"))
        {
            // `foo.test.en` is a part of the module `foo.en`, never a module of its
            // own (S:799): its path names no module.
            self.pending.push(
                Diagnostic::new(
                    Code::EN0305,
                    format!("import path not found: `{}`", ask.spec),
                    ask.span,
                    "a `.test.en` file is a test part, not a module",
                )
                .note(
                    "a test part belongs to the module of the same name, which it sees whole; nothing imports it",
                ),
            );
            return ImportEdge {
                target: None,
                children,
            };
        }
        let target = match spec {
            Spec::Library(key) => {
                if self.provider.lib(&key).is_some() {
                    self.load_lib(&key).map(ImportTarget::Module)
                } else if self.provider.lib_is_folder(&key) {
                    Some(self.folder_target(&key, true, ask, &mut children))
                } else {
                    None
                }
            }
            Spec::User(rel) => {
                let rel = self.provider.reenter(&rel);
                let file = PathBuf::from(format!("{rel}.en"));
                let path = paths::user_module(&rel);
                if let Some(&index) = self.by_path.get(&path) {
                    Some(ImportTarget::Module(index))
                } else if self.provider.user_exists(&file) {
                    self.load_user(&file).ok().map(ImportTarget::Module)
                } else if self.provider.user_is_dir(Path::new(&rel)) {
                    Some(self.folder_target(&rel, false, ask, &mut children))
                } else {
                    None
                }
            }
            Spec::Invalid => None,
        };
        if let (Some(ImportTarget::Module(m)), Some(names)) = (&target, &ask.names) {
            let m = *m;
            for &name in names {
                if self.modules[m].folder || !declares(&self.modules[m].ast, name) {
                    let parent = self.rel(m);
                    let child_library = self.modules[m].library;
                    if let Some(child) = self.child(parent, child_library, name.as_str()) {
                        children.push(child);
                    }
                }
            }
        }
        if target.is_none() {
            self.pending.push(Diagnostic::new(
                Code::EN0305,
                format!("import path not found: `{}`", ask.spec),
                ask.span,
                "no file, folder or library module has this path",
            ));
        }
        ImportEdge { target, children }
    }

    /// A folder named by an import: for `* as n` the folder's own module; for
    /// `{ x }`, the folder, with each named child loaded.
    fn folder_target(
        &mut self,
        folder: &str,
        library: bool,
        ask: &ImportAsk,
        children: &mut Vec<usize>,
    ) -> ImportTarget {
        match &ask.names {
            None => ImportTarget::Module(self.folder_module(folder, library)),
            Some(names) => {
                for &name in names {
                    if let Some(child) = self.child(folder, library, name.as_str()) {
                        children.push(child);
                    }
                }
                ImportTarget::Folder(Self::module_path(folder, library).as_str().to_owned())
            }
        }
    }
}
