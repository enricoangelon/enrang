//! Classes, enums and method interfaces (ARCHITECTURE 2.4; SPEC 4.3, 4.4).

use enrang_base::{Span, Symbol};

use crate::def::{Repr, Vis};
use crate::ids::{AdtId, DefId, FieldIdx, GenericsId, ParamId, StringId, VariantIdx};
use crate::lang::LangItem;
use crate::ty::Ty;

/// A class, enum or method interface: the target of `TyKind::Adt`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdtDef {
    /// Its definition (`DefKind::Adt` or `DefKind::StrUnion`).
    pub def: DefId,
    pub name: Symbol,
    pub generics: GenericsId,
    pub kind: AdtKind,
}

impl AdtDef {
    pub fn is_class(&self) -> bool {
        matches!(self.kind, AdtKind::Class(_))
    }

    pub fn is_enum(&self) -> bool {
        matches!(self.kind, AdtKind::Enum(_))
    }

    pub fn is_interface(&self) -> bool {
        matches!(self.kind, AdtKind::Interface(_))
    }

    pub fn as_class(&self) -> Option<&ClassDef> {
        match &self.kind {
            AdtKind::Class(class) => Some(class),
            _ => None,
        }
    }

    pub fn as_enum(&self) -> Option<&EnumDef> {
        match &self.kind {
            AdtKind::Enum(e) => Some(e),
            _ => None,
        }
    }

    pub fn as_interface(&self) -> Option<&IfaceDef> {
        match &self.kind {
            AdtKind::Interface(i) => Some(i),
            _ => None,
        }
    }

    /// The methods it declares itself: a class's, an enum's or an interface's.
    pub fn own_methods(&self) -> &[DefId] {
        match &self.kind {
            AdtKind::Class(class) => &class.methods,
            AdtKind::Enum(e) => &e.methods,
            AdtKind::Interface(i) => &i.methods,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdtKind {
    Class(ClassDef),
    Enum(EnumDef),
    Interface(IfaceDef),
}

/// `abstract`, `final` or neither (SPEC 4.3).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum ClassModifier {
    Plain,
    Abstract,
    Final,
}

/// A class.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassDef {
    pub modifier: ClassModifier,
    /// `extends`: an `Adt` of a class, with its arguments.
    pub base: Option<Ty>,
    /// `implements`: interfaces, `Copy` among them.
    pub implements: Vec<Ty>,
    /// `implements Copy` written on this class (never inherited, SPEC O4).
    pub copy: bool,
    /// Flattened: the base's fields first, so a `FieldIdx` names one field in the
    /// whole chain and an `override` resolves to the base's index (A:896).
    pub fields: Vec<FieldDef>,
    /// The index of the first field this class declares.
    pub own_from: u32,
    /// Inherited fields given a new default here (A:326's last sentence).
    pub overrides: Vec<FieldIdx>,
    pub methods: Vec<DefId>,
    pub ctors: Vec<DefId>,
    pub dtor: Option<DefId>,
    /// The class has a hidden method-table pointer: it is not `final`, or it extends
    /// a class that has one (SPEC 4.3, 11).
    pub hidden_table: bool,
}

impl ClassDef {
    /// A plain class with no base, member or field.
    pub fn new(modifier: ClassModifier) -> ClassDef {
        ClassDef {
            modifier,
            base: None,
            implements: Vec::new(),
            copy: false,
            fields: Vec::new(),
            own_from: 0,
            overrides: Vec::new(),
            methods: Vec::new(),
            ctors: Vec::new(),
            dtor: None,
            hidden_table: modifier != ClassModifier::Final,
        }
    }

    /// The fields this class declares itself, with their indices.
    pub fn own_fields(&self) -> impl Iterator<Item = (FieldIdx, &FieldDef)> {
        self.fields
            .iter()
            .enumerate()
            .skip(self.own_from as usize)
            .map(|(i, f)| (FieldIdx(i as u32), f))
    }

    /// The field named `name` in the flattened list.
    pub fn field_named(&self, name: Symbol) -> Option<(FieldIdx, &FieldDef)> {
        self.fields
            .iter()
            .enumerate()
            .rev()
            .find(|(_, f)| f.name == name)
            .map(|(i, f)| (FieldIdx(i as u32), f))
    }
}

/// A class's field, or an enum case's (SPEC 4.3; A:326-331). `readonly` before a
/// reference's `&` is not part of `Ty`: `readonly_refs` lists the reference parts
/// declared so, each as the tuple positions from the field to it, `[]` being the
/// field itself. The `readonly` modifier is separate: no assignment after
/// construction. A subclass's `override` adds no `FieldDef`.
///
/// Departure D4: the last four fields are additions ARCHITECTURE does not list.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldDef {
    pub name: Symbol,
    pub ty: Ty,
    pub vis: Vis,
    pub readonly: bool,
    pub readonly_refs: Vec<Vec<u32>>,
    /// An initialiser is written (`= e`), or the field is `x?: T` (default `null`).
    pub has_default: bool,
    /// The class that declares it; for an enum case's field, the enum.
    pub declared_in: AdtId,
    pub span: Span,
    /// `x?: T`.
    pub optional: bool,
}

impl FieldDef {
    /// A public, writable field with no default.
    pub fn new(name: Symbol, ty: Ty, declared_in: AdtId) -> FieldDef {
        FieldDef {
            name,
            ty,
            vis: Vis::Public,
            readonly: false,
            readonly_refs: Vec::new(),
            has_default: false,
            declared_in,
            span: Span::DUMMY,
            optional: false,
        }
    }
}

/// An enum, a string-literal union (`str_union`), or a lang enum such as `Result`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnumDef {
    pub variants: Vec<VariantDef>,
    pub values: EnumValues,
    pub repr: Option<Repr>,
    pub str_union: bool,
    pub methods: Vec<DefId>,
}

impl EnumDef {
    pub fn new(variants: Vec<VariantDef>) -> EnumDef {
        EnumDef {
            variants,
            values: EnumValues::None,
            repr: None,
            str_union: false,
            methods: Vec::new(),
        }
    }

    /// No case has a field.
    pub fn is_payload_free(&self) -> bool {
        self.variants.iter().all(|v| v.fields.is_empty())
    }

    pub fn variant_named(&self, name: Symbol) -> Option<(VariantIdx, &VariantDef)> {
        self.variants
            .iter()
            .enumerate()
            .find(|(_, v)| v.name == name)
            .map(|(i, v)| (VariantIdx(i as u32), v))
    }
}

/// Which explicit values an enum's cases carry: none, integers, or texts; a mix is
/// EN0456 (SPEC 4.3).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum EnumValues {
    None,
    Ints,
    Texts,
}

/// One case.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VariantDef {
    pub name: Symbol,
    pub fields: Vec<FieldDef>,
    pub value: Option<VariantValue>,
    pub span: Span,
}

impl VariantDef {
    pub fn new(name: Symbol) -> VariantDef {
        VariantDef {
            name,
            fields: Vec::new(),
            value: None,
            span: Span::DUMMY,
        }
    }
}

/// A case's written value, after constant evaluation.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum VariantValue {
    Int(i128),
    Text(StringId),
}

/// A method interface (SPEC 4.4). A fields-only interface is no `AdtDef`: it is an
/// alias of an object type. `Self` in its members is the implicit parameter
/// `self_param` (SPEC 4.4).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IfaceDef {
    pub methods: Vec<DefId>,
    /// A sealed interface (`__Int`, `__Float`, `VolatileValue`, `AtomicValue`,
    /// `AtomicBits`), whose implementers are the compiler's table (SPEC 4.4).
    pub sealed: Option<LangItem>,
    pub self_param: ParamId,
}

/// The input of `Tcx::define_adt` (A:753): everything of an [`AdtDef`] and its
/// definition but ids, for sema and for MIR fixtures, which need no front end.
/// `Tcx::define_adt` makes the definition (`DefKind::Adt`, or `StrUnion` for a
/// string-literal union) and the ADT.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdtDecl {
    pub data: crate::def::DefData,
    pub name: Symbol,
    pub generics: GenericsId,
    pub kind: AdtKind,
}
