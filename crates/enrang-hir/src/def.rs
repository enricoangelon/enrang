//! Definitions: what every item, member and module is in `Tcx` (ARCHITECTURE 2.4;
//! its fields are silent there and defined here).

use enrang_base::{BitSet, FileId, Span, Symbol};
use enrang_target::FeatureSet;

use crate::ids::{AdtId, DefId, GenericsId, HostCallId, ModuleId};
use crate::intrinsic::IntrinsicName;
use crate::lang::LangItem;
use crate::path::{ItemPath, ModulePath};
use crate::ty::{Abi, Ty};

/// An item's or member's visibility (A:183). An item states `public` or `private`;
/// class members may also be `protected`; interface members and `extend` blocks
/// state none and are `Public`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Vis {
    Public,
    Private,
    Protected,
}

/// What a definition is.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum DefKind {
    /// A top-level `function`.
    Fn,
    /// A function among a program's top-level statements (SPEC 7, N13).
    LocalFn,
    /// `declare function`: foreign, intrinsic or host call.
    DeclareFn,
    /// A method of a class, enum, interface or `extend` block.
    Method,
    Ctor,
    Dtor,
    /// A top-level `const`.
    Const,
    /// `unsafe let`.
    Static,
    /// A class, enum or method interface.
    Adt(AdtId),
    /// A `type` alias, or a fields-only interface, which is an alias of an object
    /// type (SPEC 4.4): transparent, expanded at use.
    TypeAlias,
    /// A string-literal union alias: an enum with `str_union` (SPEC 4.3).
    StrUnion(AdtId),
    /// An `extend` block.
    Extend,
    /// A top-level `assert` in a file with no statements.
    StaticAssert,
    /// A `test`, `describe` or `compileFails`/`compileOk` item.
    Test,
    Module,
}

impl DefKind {
    /// Whether a definition of this kind has a [`crate::FnSig`].
    pub fn has_sig(self) -> bool {
        matches!(
            self,
            DefKind::Fn
                | DefKind::LocalFn
                | DefKind::DeclareFn
                | DefKind::Method
                | DefKind::Ctor
                | DefKind::Dtor
        )
    }
}

/// Flags of a member that neither its kind nor its signature records.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Default)]
pub struct DefFlags {
    /// `abstract` on a method.
    pub is_abstract: bool,
    /// `override` on a method.
    pub is_override: bool,
    /// The declaration has a body: false for `;` (abstract, interface and library
    /// members) and for `declare function`.
    pub has_body: bool,
}

/// One definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefData {
    pub path: ItemPath,
    pub kind: DefKind,
    pub module: ModuleId,
    pub vis: Vis,
    /// The name as written, or the keyword (`constructor`, `extend`, `test`).
    pub name_span: Span,
    pub span: Span,
    /// The class, enum, interface or `extend` block of a member.
    pub parent: Option<DefId>,
    pub attrs: Attrs,
    pub flags: DefFlags,
    /// Declared in a module's `.test.en` part.
    pub test_part: bool,
}

impl DefData {
    /// A public definition with no parent, attributes or flags; `name_span` is `span`.
    pub fn new(path: ItemPath, kind: DefKind, module: ModuleId, span: Span) -> DefData {
        DefData {
            path,
            kind,
            module,
            vis: Vis::Public,
            name_span: span,
            span,
            parent: None,
            attrs: Attrs::default(),
            flags: DefFlags::default(),
            test_part: false,
        }
    }

    /// The definition's own name, the last segment of its path.
    pub fn name(&self) -> Option<Symbol> {
        self.path.name()
    }
}

/// The lowered decorators of a definition (SPEC 3.1's table, S:325-347); everything
/// is off by default.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Attrs {
    pub must_use: bool,
    pub requires: FeatureSet,
    pub section: Option<Symbol>,
    pub at: Option<u64>,
    pub abi: Option<Abi>,
    pub dll: Option<Symbol>,
    /// `@intrinsic("Kind")`: the kind's name; the payload (a `Ty`, an `AluOp`) is
    /// decided at each call (`IntrinsicKind`).
    pub intrinsic: Option<IntrinsicName>,
    pub host_call: Option<HostCallId>,
    pub lang: Option<LangItem>,
    pub packed: bool,
    pub repr: Option<Repr>,
    pub align: Option<u32>,
    pub entry: bool,
    pub panic_handler: bool,
    /// `@interrupt`, with `errorCode`.
    pub interrupt: Option<bool>,
    pub naked: bool,
    pub bits: Option<u8>,
    pub global_allocator: bool,
    pub was: Option<Symbol>,
    pub dev_migrate: bool,
    pub owner: bool,
}

/// `@repr("C" | "u8" | "u16" | "u32")` (SPEC 7.6).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Repr {
    C,
    U8,
    U16,
    U32,
}

impl Repr {
    pub fn from_name(name: &str) -> Option<Repr> {
        match name {
            "C" => Some(Repr::C),
            "u8" => Some(Repr::U8),
            "u16" => Some(Repr::U16),
            "u32" => Some(Repr::U32),
            _ => None,
        }
    }
}

/// A module of the program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleInfo {
    pub path: ModulePath,
    /// Part of the embedded library.
    pub library: bool,
    pub file: FileId,
    /// The `.test.en` part, loaded in `ParseMode::Test` only.
    pub test_part: Option<FileId>,
    /// The import closure `extend` lookup reads (A:886): the modules whose `extend`
    /// blocks this module sees. Empty until resolution fills it.
    pub closure: BitSet<ModuleId>,
    /// The file has top-level statements (EN0312 on importing it).
    pub has_statements: bool,
    /// The module's own definition (`DefKind::Module`).
    pub def: Option<DefId>,
}

impl ModuleInfo {
    pub fn new(path: ModulePath, library: bool, file: FileId) -> ModuleInfo {
        ModuleInfo {
            path,
            library,
            file,
            test_part: None,
            closure: BitSet::new(0),
            has_statements: false,
            def: None,
        }
    }
}

/// A type alias's parameters and body (`DefKind::TypeAlias`), expanded at each use
/// with its type arguments. A fields-only interface is one whose body is an
/// `Object` (SPEC 4.4).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AliasDef {
    pub generics: GenericsId,
    pub ty: Ty,
}
