//! Signatures, generics and bounds (ARCHITECTURE 2.4, 4 "Position checks").

use enrang_base::{Span, Symbol};
use enrang_target::FeatureSet;

use crate::def::{Attrs, DefData, DefKind, Vis};
use crate::ids::{AdtId, BoundId, DefId, GenericsId, ModuleId, ParamId, ShapeId, TyList};
use crate::path::ItemPath;
use crate::tcx::Tcx;
use crate::ty::{Abi, Ty};

/// A function's signature (A:280-284): what typing reads at a call. Bodies infer
/// everything else; type checking never reads a contract (N1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnSig {
    /// The function's own type parameters, linked to its class's or `extend`'s.
    pub generics: GenericsId,
    /// A method's `where` clause: bounds on its class's or `extend`'s parameters.
    pub where_bounds: Vec<(ParamId, Vec<BoundId>)>,
    /// `None` for a function or constructor; a method's receiver kind otherwise.
    pub receiver: Option<Receiver>,
    pub params: Vec<ParamSig>,
    pub ret: Ty,
    /// D14: the parameter names of a function type written as the result, kept
    /// outside the type (see [`ParamSig::fn_names`]).
    pub ret_fn_names: Option<Vec<Symbol>>,
    /// `readonly` before the return type (SPEC 3.1).
    pub ret_readonly: bool,
    pub unsafety: bool,
    /// `@requires(...)` (SPEC 10.3).
    pub requires: FeatureSet,
    pub abi: Abi,
}

impl FnSig {
    /// A safe, non-generic-beyond-`generics` signature with no receiver, no `where`,
    /// no required features and Enrang's calling convention.
    pub fn new(generics: GenericsId, params: Vec<ParamSig>, ret: Ty) -> FnSig {
        FnSig {
            generics,
            where_bounds: Vec::new(),
            receiver: None,
            params,
            ret,
            ret_fn_names: None,
            ret_readonly: false,
            unsafety: false,
            requires: FeatureSet::EMPTY,
            abi: Abi::Enrang,
        }
    }

    /// The number of arguments a call must pass at least: parameters with no default
    /// (`x?: T` has the default `null`, SPEC 4.14).
    pub fn required_params(&self) -> usize {
        self.params.iter().filter(|p| !p.has_default).count()
    }
}

/// One parameter of a signature; it carries its mark (A:281). ARCHITECTURE names it
/// without defining it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParamSig {
    /// The binding's name; a destructuring parameter's hidden name is `_`.
    pub name: Symbol,
    /// The type, with `x?: T` already collapsed to `T | null` (A:888).
    pub ty: Ty,
    pub mark: Mark,
    /// A default value (`= e`) or `?`.
    pub has_default: bool,
    /// D14: when the parameter's type is a function or closure type written here,
    /// under at most one `| null`, the names of that type's parameters. A type
    /// keeps no names (A:288), but SPEC 4.5's EN0615 prints the type as written,
    /// `fn(let s: &string) => void` (`Tcx::fn_ty_string`). `None` otherwise, and for
    /// a type reached through an alias.
    pub fn_names: Option<Vec<Symbol>>,
    pub span: Span,
}

impl ParamSig {
    pub fn new(name: Symbol, ty: Ty) -> ParamSig {
        ParamSig {
            name,
            ty,
            mark: Mark::None,
            has_default: false,
            fn_names: None,
            span: Span::DUMMY,
        }
    }
}

/// A method's receiver: `m()`, `let m()` or `const m()`; `move m()`; `static m()`
/// (A:286).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Receiver {
    Ref(Mark),
    Move,
    Static,
}

/// A written permission mark (SPEC 5); bodies infer the rest (A:287).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Mark {
    None,
    Let,
    Const,
}

/// A generics list: the item's own parameters, after its parent's (a method's
/// class, an `extend`'s block).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Generics {
    pub parent: Option<GenericsId>,
    pub params: Vec<ParamId>,
}

impl Generics {
    pub fn new(parent: Option<GenericsId>, params: Vec<ParamId>) -> Generics {
        Generics { parent, params }
    }
}

/// A type parameter. `index` is its place in its own list; `implicit` marks one the
/// compiler made (departure D5: "each interface-typed parameter is a class of its
/// own", A:892-894).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TyParamDef {
    pub name: Symbol,
    pub owner: DefId,
    pub index: u32,
    pub bounds: Vec<BoundId>,
    pub implicit: Option<Implicit>,
    pub span: Span,
}

/// Why the compiler made a type parameter (D5): a by-value or `&` parameter of a
/// method-interface type is an implicit `X extends I`, and so is an interface's own
/// `Self` (SPEC 4.4); a by-value or `&` parameter of an object type, a fields-only
/// interface included, is an implicit parameter bounded by that shape, one copy per
/// shape passed (SPEC 4.5 C20, A:599); `Opaque` stands for a two-word `&I` value
/// read in a body, "a class of its own" (A:894).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Implicit {
    Interface(AdtId),
    Shape(ShapeId),
    Opaque,
}

/// Why a method is compiled once per type (SPEC 4.3, 4.4, A:1279): it has no
/// method-table slot, so it is never overridden (EN0460) and never `Virtual`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum OncePerType {
    /// Type parameters of its own.
    OwnParams,
    /// A by-value interface parameter (an `&I` one has a copy for two-word
    /// arguments, which a slot can name).
    InterfaceByValue,
    /// An object-type parameter, by value or behind `&` (plan G25).
    ObjectParam,
}

impl OncePerType {
    /// The head of EN0460 for method `name`.
    pub fn message(self, name: Symbol) -> String {
        let why = match self {
            OncePerType::OwnParams => "has its own type parameters",
            OncePerType::InterfaceByValue => "takes an interface by value",
            OncePerType::ObjectParam => "takes an object type",
        };
        format!("`{name}` {why}, so it can't be overridden")
    }
}

impl Tcx {
    /// Whether method `def` is compiled once per type, and why.
    pub fn once_per_type(&self, def: DefId) -> Option<OncePerType> {
        let sig = self.sig_opt(def)?;
        let own = &self.generics(sig.generics).params;
        let implicit = |p: ParamId| self.param(p).implicit;
        if own.iter().any(|&p| implicit(p).is_none()) {
            return Some(OncePerType::OwnParams);
        }
        let by_value = own.iter().any(|&p| {
            matches!(implicit(p), Some(Implicit::Interface(_)))
                && sig.params.iter().any(|ps| ps.ty == self.mk_param(p))
        });
        if by_value {
            return Some(OncePerType::InterfaceByValue);
        }
        own.iter()
            .any(|&p| matches!(implicit(p), Some(Implicit::Shape(_))))
            .then_some(OncePerType::ObjectParam)
    }
}

/// A bound: an interface (nominal satisfaction, or the compiler's table for a sealed
/// one) or a class (by name, SPEC 4.10), with its type arguments.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Bound {
    Iface { adt: AdtId, args: TyList },
    Class { adt: AdtId, args: TyList },
}

impl Bound {
    pub fn adt(&self) -> AdtId {
        match self {
            Bound::Iface { adt, .. } | Bound::Class { adt, .. } => *adt,
        }
    }

    pub fn args(&self) -> TyList {
        match self {
            Bound::Iface { args, .. } | Bound::Class { args, .. } => *args,
        }
    }
}

/// The bounds in force while one body is typed or a predicate is asked: written
/// bounds are read from each [`TyParamDef`], so this holds what a `where` clause or
/// an inferred bound adds.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct ParamEnv {
    pub bounds: Vec<(ParamId, Vec<BoundId>)>,
}

impl ParamEnv {
    /// No added bound.
    pub fn empty() -> ParamEnv {
        ParamEnv::default()
    }

    /// The bounds this environment adds to `p`.
    pub fn bounds_of(&self, p: ParamId) -> impl Iterator<Item = BoundId> + '_ {
        self.bounds
            .iter()
            .filter(move |(param, _)| *param == p)
            .flat_map(|(_, bounds)| bounds.iter().copied())
    }
}

/// The input of `Tcx::define_fn` (A:754): a definition and its signature, so a MIR
/// fixture builds functions with no front end.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnDecl {
    pub path: ItemPath,
    pub kind: DefKind,
    pub module: ModuleId,
    pub vis: Vis,
    pub span: Span,
    pub parent: Option<DefId>,
    pub attrs: Attrs,
    pub sig: FnSig,
}

impl FnDecl {
    /// The definition part, with the name span and flags left at their defaults.
    pub fn data(&self) -> DefData {
        let mut data = DefData::new(self.path.clone(), self.kind, self.module, self.span);
        data.vis = self.vis;
        data.parent = self.parent;
        data.attrs = self.attrs.clone();
        data
    }
}

/// What a declaration's bodies show of each of its type parameters (A:892), in the
/// order of its generics list: `views_ok` when the signature and body use it only
/// behind `&`, so it may stand for a `Slice<U>`; `strings_ok` when nothing converts
/// its `&T` to an `&I`, so it may stand for `string`. Computed after every body is
/// typed (`passes::views` in sema).
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct TyParamFacts {
    pub views_ok: Vec<bool>,
    pub strings_ok: Vec<bool>,
}
