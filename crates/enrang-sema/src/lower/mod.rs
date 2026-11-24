//! Declaration lowering (plan c and d.4): every declaration's types, signatures and
//! ADTs into `Tcx`.
//!
//! Order (d.4): ADT headers (generics, an interface's `Self`, an `extend` block's
//! parameters), then bounds, bases and `implements`, then the cycles of bases (EN0401,
//! plan choice, which leave every base chain finite), then fields and cases (a class
//! after its base, flattened), then recursion (EN0408), then aliases (lazily, so a
//! use expands one before its turn; a visiting set gives EN0437), then signatures
//! (functions, methods, constructors, destructors, `declare`, interface and `extend`
//! members), then the types of constants and statics (EN0802), then `extend`
//! patterns (EN0439, EN0806 in user code), then the decorators and what they decide
//! (EN0806, EN0808, EN0814-EN0817, EN0819, EN0826, EN0827, EN1030), then the paths
//! of overloads, and last the error arguments of `Result` (EN0454), which need every
//! class's fields. The ASTs of the bodies to type, and the scope each definition
//! resolves in, are kept in [`DeclTables`] for typing.
//!
//! EN0409 has no trigger here: a function's, a field's and a constructor's
//! parameter cannot omit its type in the grammar (plan d.4), so only an arrow
//! parameter can, which typing reports (4C).

pub(crate) mod adts;
pub(crate) mod consts_decl;
pub(crate) mod decorators;
pub(crate) mod extend;
pub(crate) mod sigs;
pub(crate) mod types;

use std::collections::BTreeMap;

use enrang_hir::{AdtId, BodyOwner, DefId, ModuleId, Ty};
use enrang_syntax::ast;

use crate::cx::Sema;
use crate::resolve::ScopeAt;

/// One collected declaration, with references into the loaded program's AST.
#[derive(Clone, Debug)]
pub(crate) struct ItemAst<'a> {
    pub def: DefId,
    pub module: ModuleId,
    pub test_part: bool,
    pub kind: ItemAstKind<'a>,
}

/// The AST of a declaration. Member lists hold one entry per AST member: the
/// member's definition, or `None` for a field.
#[derive(Clone, Debug)]
pub(crate) enum ItemAstKind<'a> {
    Function(&'a ast::FunctionDecl),
    LocalFn(&'a ast::FunctionDecl),
    Class(AdtId, &'a ast::ClassDecl, Vec<Option<DefId>>),
    Enum(AdtId, &'a ast::EnumDecl, Vec<DefId>),
    Interface(AdtId, &'a ast::InterfaceDecl, Vec<Option<DefId>>),
    /// A fields-only interface: an alias of an object type (SPEC 4.4).
    FieldsInterface(&'a ast::InterfaceDecl),
    Alias(&'a ast::TypeAlias),
    StrUnion,
    Const(&'a ast::TopConst),
    Static(&'a ast::UnsafeLet),
    Declare(&'a ast::DeclareFn),
    Extend(&'a ast::ExtendDecl, Vec<DefId>),
    StaticAssert,
    Test,
}

/// The AST of a body to type.
#[derive(Copy, Clone, Debug)]
pub(crate) enum BodyAst<'a> {
    Function(&'a ast::FunctionDecl),
    Method(&'a ast::MethodDecl),
    Ctor(&'a ast::Constructor),
    Dtor(&'a ast::Destructor),
    Statements(&'a [ast::Stmt]),
    Const(&'a ast::Expr),
    Test(&'a ast::ArrowFn),
}

/// What lowering keeps for typing.
#[derive(Debug, Default)]
pub(crate) struct DeclTables<'a> {
    /// Every declaration, in collection order (load order, then source order).
    pub items: Vec<ItemAst<'a>>,
    /// The bodies to type of each user module, in source order: statements, items,
    /// then the `.test.en` part.
    pub owners: BTreeMap<ModuleId, Vec<BodyOwner>>,
    pub bodies: BTreeMap<BodyOwner, BodyAst<'a>>,
    /// The scope each definition's signature and body resolve in.
    pub scopes: BTreeMap<DefId, ScopeAt>,
    /// Aliases and fields-only interfaces, lowered on first use.
    pub aliases: BTreeMap<DefId, AliasAst<'a>>,
    /// Aliases being lowered, for EN0437, and those already reported.
    pub alias_visiting: BTreeMap<DefId, bool>,
    /// The case generator of each `test.each` (`TestExtra::Cases`).
    pub test_cases: BTreeMap<DefId, &'a ast::ArrowFn>,
    /// Every declaration is lowered: a `Result` written from now on is checked at
    /// once (EN0454).
    pub lowered: bool,
    /// The `Result<T, E>` types written before that: `T`, `E`, `E`'s span.
    pub error_args: Vec<(Ty, Ty, enrang_base::Span)>,
    /// The classes whose fields are lowered, and those being lowered: a length
    /// that lays out a class lowers its fields first, whatever the order of the
    /// declarations (`adts::ensure_fields`).
    pub fields_done: std::collections::BTreeSet<enrang_hir::AdtId>,
    pub fields_active: std::collections::BTreeSet<enrang_hir::AdtId>,
}

/// An alias's AST and where it was declared.
#[derive(Copy, Clone, Debug)]
pub(crate) struct AliasAst<'a> {
    pub kind: AliasKind<'a>,
    pub module: ModuleId,
    pub test_part: bool,
}

#[derive(Copy, Clone, Debug)]
pub(crate) enum AliasKind<'a> {
    Alias(&'a ast::TypeAlias),
    Fields(&'a ast::InterfaceDecl),
}

impl<'a> DeclTables<'a> {
    /// The AST to type for `owner`.
    pub fn body_ast(&self, owner: BodyOwner) -> Option<BodyAst<'a>> {
        self.bodies.get(&owner).copied()
    }

    /// The bodies of `module`, in the order they are typed.
    pub fn owners_of(&self, module: ModuleId) -> Vec<BodyOwner> {
        self.owners.get(&module).cloned().unwrap_or_default()
    }

    /// The scope a body resolves in: its definition's, or for top-level statements
    /// the module's.
    pub fn scope_of(&self, owner: BodyOwner) -> Option<ScopeAt> {
        match owner {
            BodyOwner::Statements(module) => Some(ScopeAt::statements(module)),
            BodyOwner::Fn(def) | BodyOwner::Const(def) | BodyOwner::Test(def) => {
                self.scopes.get(&def).copied()
            }
        }
    }
}

/// Lowers every declaration, in d.4's order.
pub(crate) fn decls(sema: &mut Sema) {
    let items = sema.decls.items.clone();
    for item in &items {
        match &item.kind {
            ItemAstKind::Alias(a) => {
                sema.decls.aliases.insert(
                    item.def,
                    AliasAst {
                        kind: AliasKind::Alias(a),
                        module: item.module,
                        test_part: item.test_part,
                    },
                );
            }
            ItemAstKind::FieldsInterface(i) => {
                sema.decls.aliases.insert(
                    item.def,
                    AliasAst {
                        kind: AliasKind::Fields(i),
                        module: item.module,
                        test_part: item.test_part,
                    },
                );
            }
            _ => {}
        }
    }
    for item in &items {
        adts::header(sema, item);
    }
    for item in &items {
        adts::bounds(sema, item);
    }
    adts::base_cycles(sema, &items);
    adts::fields(sema, &items);
    adts::recursion(sema, &items);
    for item in &items {
        if matches!(
            item.kind,
            ItemAstKind::Alias(_) | ItemAstKind::FieldsInterface(_)
        ) {
            types::ensure_alias(sema, item.def);
        }
    }
    for item in &items {
        sigs::lower(sema, item);
    }
    for item in &items {
        consts_decl::lower(sema, item);
    }
    for item in &items {
        extend::lower(sema, item);
    }
    decorators::check(sema);
    sigs::overload_paths(sema);
    sema.decls.lowered = true;
    for (ok, err, span) in std::mem::take(&mut sema.decls.error_args) {
        types::check_error_type(sema, ok, err, span);
    }
}
