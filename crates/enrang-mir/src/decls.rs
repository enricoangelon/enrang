//! Declarations in the MIR text form (ARCHITECTURE 1 "Text formats decouple the
//! pipeline", 2.5; M3 plan b.6): printing the declarations bodies reference, and
//! defining a parsed module's declarations in a new `Tcx` through the public
//! `define_*` API, each stated contract in the contract memo and each class flag in
//! the class-contract memo, so borrowck reads them as any declared contract.
//!
//! A declaration states its contract as a body-less Enrang position does (A:562):
//! `let` before a reference parameter it writes, `move` or `static` before `fn`,
//! `readonly` before a read-only result, then `perms`, `sources`, `through_fields`,
//! `through_read`, `stores` (each with its bits), `moves` and `result`. A written
//! contract is completed from the marks (perms), `sources()` (no loans) and the
//! result type; a declaration with none leaves the memo empty, for borrowck's
//! declared defaults. The printed form is complete, so it reads back the same.

use std::collections::{BTreeMap, BTreeSet};

use enrang_base::{BytePos, FileId, Idx, Span, Symbol, intern};
use enrang_hir::{
    Abi, AdtDecl, AdtId, AdtKind, Attrs, Bound, BoundId, ClassContract, ClassDef, ClassModifier,
    ConstTree, ConstValue, Contract, DefData, DefId, DefKind, EnumDef, EnumValues, ExtendDef,
    Feature, FeatureSet, FieldDef, FieldIdx, FnRef, FnSig, Generics, IfaceDef, Implicit,
    IntrinsicKind, IntrinsicName, ItemPath, LangItem, Mark, ModuleId, ModuleInfo, ModulePath,
    ParamId, ParamSig, Perm, Reason, Receiver, Repr, ResultPerm, RetSources, Shape, Tcx, Ty,
    TyKind, TyParamDef, VariantDef, VariantValue, Vis,
};

use crate::body::{
    AggregateKind, Body, BodyOwner, Callee, ClosureFn, ConstKind, Operand, Rvalue, ShimKind,
    StatementKind, TerminatorKind,
};
use crate::parse::{
    AttrAst, BodyAst, ConstAst, ContractAst, DeclAst, DeclKind, FieldAst, GenParam, OwnerAst,
    PResult, ParentAst, PathAst, ReasonAst, ResultAst, ShimAst, TopLevel, TyAst, err, scalar,
    shim_of,
};
use crate::print::{PERMS, Printer, REASONS, REPRS, name_of, quote};
use crate::proj::PlaceTy;

// ---------------------------------------------------------------------------------
// Resolution.

/// What names resolve against: the module the text is in, every ADT by its short
/// name, every definition by its path.
pub(crate) struct Names {
    pub module: ModulePath,
    pub adts: Vec<(Symbol, AdtId, ModulePath)>,
    pub defs: BTreeMap<ItemPath, DefId>,
    pub modules: BTreeMap<ModulePath, ModuleId>,
}

impl Names {
    fn adt(&self, name: Symbol) -> Option<AdtId> {
        let mut found = self.adts.iter().filter(|(n, _, _)| *n == name);
        let all: Vec<_> = found.by_ref().collect();
        all.iter()
            .find(|(_, _, m)| *m == self.module)
            .or(all.first())
            .map(|(_, a, _)| *a)
    }

    pub fn path(&self, p: &PathAst) -> ItemPath {
        ItemPath {
            module: p.module.as_deref().map_or(self.module, ModulePath::new),
            segments: p.segs.iter().map(|s| s.name).collect(),
            overload: p.overload.clone(),
        }
    }

    fn def(&self, p: &PathAst) -> PResult<DefId> {
        let path = self.path(p);
        match self.defs.get(&path) {
            Some(&d) => Ok(d),
            None => err(p.at, format!("`{path}` is not declared")),
        }
    }
}

/// The type parameters in scope by name, and what `Self` is.
#[derive(Clone, Default)]
pub(crate) struct Scope {
    pub params: Vec<(Symbol, ParamId)>,
    pub self_ty: Option<Ty>,
}

impl Scope {
    /// The scope of a definition: every parameter of its generics chain, and `Self`
    /// in an interface's member.
    fn of_def(tcx: &Tcx, def: DefId) -> Scope {
        let generics = match tcx.def(def).kind {
            DefKind::Adt(a) | DefKind::StrUnion(a) => Some(tcx.adt(a).generics),
            DefKind::Extend => tcx
                .extends()
                .iter()
                .find(|e| e.def == def)
                .map(|e| e.generics),
            _ => tcx.sig_opt(def).map(|s| s.generics),
        };
        let params = generics.map_or_else(Vec::new, |g| {
            tcx.all_params(g)
                .into_iter()
                .map(|p| (tcx.param(p).name, p))
                .collect()
        });
        let iface = |d: DefId| {
            tcx.adt_of(d)
                .and_then(|a| tcx.adt(a).as_interface().map(|i| i.self_param))
        };
        let self_param = iface(def).or_else(|| tcx.def(def).parent.and_then(iface));
        Scope {
            params,
            self_ty: self_param.map(|p| tcx.mk_param(p)),
        }
    }
}

pub(crate) fn resolve_ty(tcx: &Tcx, names: &Names, scope: &Scope, t: &TyAst) -> PResult<Ty> {
    let c = *tcx.common();
    let go = |t: &TyAst| resolve_ty(tcx, names, scope, t);
    Ok(match t {
        TyAst::Named { name, args, at } => {
            let n = name.as_str();
            let prim = match n {
                "bool" => Some(c.bool),
                "int" | "i32" => Some(c.i32),
                "i8" => Some(c.i8),
                "i16" => Some(c.i16),
                "i64" => Some(c.i64),
                "u8" => Some(c.u8),
                "u16" => Some(c.u16),
                "u32" => Some(c.u32),
                "u64" => Some(c.u64),
                "isize" => Some(c.isize),
                "usize" => Some(c.usize),
                "f32" => Some(c.f32),
                "f64" => Some(c.f64),
                "void" => Some(c.void),
                "never" => Some(c.never),
                "string" => Some(c.str),
                _ => None,
            };
            if let Some(p) = prim
                && args.is_empty()
            {
                return Ok(p);
            }
            let args: Vec<Ty> = args.iter().map(go).collect::<PResult<_>>()?;
            if let [one] = args[..] {
                if n == "Slice" {
                    return Ok(tcx.mk_slice(one));
                }
                if n == "Box" {
                    return Ok(tcx.mk_box(one));
                }
            }
            if args.is_empty() {
                if n == "Self"
                    && let Some(t) = scope.self_ty
                {
                    return Ok(t);
                }
                if let Some(&(_, p)) = scope.params.iter().rev().find(|(pn, _)| pn == name) {
                    return Ok(tcx.mk_param(p));
                }
            }
            let Some(adt) = names.adt(*name) else {
                return err(*at, format!("no type `{n}`"));
            };
            let mut args = args;
            let want = tcx.generics(tcx.adt(adt).generics).params.len();
            if tcx.is_lang_adt(adt, LangItem::Result)
                && args.len() == 1
                && let Some(failure) = tcx.lang_adt(LangItem::Failure)
            {
                args.push(tcx.mk_adt(failure, &[]));
            }
            if args.len() != want {
                return err(*at, format!("`{n}` takes {want} type arguments"));
            }
            tcx.mk_adt(adt, &args)
        }
        TyAst::Ref(t) => tcx.mk_ref(go(t)?),
        TyAst::Raw(t) => tcx.mk_raw(go(t)?),
        TyAst::Nullable(t) => tcx.mk_nullable(go(t)?),
        TyAst::Array(t) => tcx.mk_array(go(t)?),
        TyAst::Fixed(t, n) => tcx.mk_fixed(go(t)?, *n),
        TyAst::Tuple(parts) => {
            let parts: Vec<Ty> = parts.iter().map(go).collect::<PResult<_>>()?;
            tcx.mk_tuple(&parts)
        }
        TyAst::Object(fields) => {
            let mut fs = Vec::new();
            let mut optional = Vec::new();
            for (name, opt, t) in fields {
                fs.push((*name, go(t)?));
                if *opt {
                    optional.push(*name);
                }
            }
            tcx.mk_object_shape(Shape::with_optional(fs, optional))
        }
        TyAst::Fn {
            abi,
            unsafety,
            params,
            ret,
            readonly,
            closure,
        } => {
            let sig = enrang_hir::FnPtrSig {
                unsafety: *unsafety,
                params: params
                    .iter()
                    .map(|(m, t)| Ok((go(t)?, *m)))
                    .collect::<PResult<_>>()?,
                ret: go(ret)?,
                ret_readonly: *readonly,
            };
            if *closure {
                tcx.mk_closure(sig)
            } else {
                let abi = match abi.as_deref() {
                    None => Abi::Enrang,
                    Some("win64") => Abi::Win64,
                    Some("sysv") => Abi::Sysv,
                    Some(other) => return err(0, format!("no ABI `{other}`")),
                };
                tcx.mk_fn_ptr(abi, sig)
            }
        }
        TyAst::Error => c.error,
    })
}

/// A function with its type arguments: the parent segment's, then the last's; a
/// generic function written without any gets its own parameters.
pub(crate) fn fn_ref(tcx: &Tcx, names: &Names, scope: &Scope, p: &PathAst) -> PResult<FnRef> {
    let def = names.def(p)?;
    let mut args = Vec::new();
    for seg in &p.segs {
        for a in &seg.args {
            args.push(resolve_ty(tcx, names, scope, &a.ty)?);
        }
    }
    let args = if args.is_empty() {
        tcx.sig_opt(def)
            .map_or(tcx.empty_list(), |s| tcx.identity_args(s.generics))
    } else {
        tcx.intern_list(&args)
    };
    Ok(FnRef { def, args })
}

pub(crate) fn const_value(
    tcx: &Tcx,
    names: &Names,
    scope: &Scope,
    c: &ConstAst,
    ty: Ty,
    ctor: Option<Ty>,
) -> PResult<ConstValue> {
    if let Some(v) = scalar(tcx, c, ty) {
        return Ok(v);
    }
    Ok(match c {
        ConstAst::Fn(p) => ConstValue::FnAddr(fn_ref(tcx, names, scope, p)?),
        ConstAst::Static(p) => ConstValue::StaticAddr(names.def(p)?),
        ConstAst::Overridden(name, at) => {
            if let Ok(n) = name.parse::<u32>() {
                return Ok(ConstValue::Overridden(FieldIdx(n)));
            }
            match ctor.and_then(|t| PlaceTy::of(t).field_named(tcx, intern(name))) {
                Some(f) => ConstValue::Overridden(f),
                None => return err(*at, format!("no field `{name}` of the constructor's class")),
            }
        }
        ConstAst::Int(_, at) => return err(*at, format!("a number is no `{}`", tcx.ty_string(ty))),
        _ => return err(0, format!("not a constant of type `{}`", tcx.ty_string(ty))),
    })
}

pub(crate) fn const_tree(
    tcx: &Tcx,
    names: &Names,
    scope: &Scope,
    c: &ConstAst,
    ty: Ty,
    ctor: Option<Ty>,
) -> PResult<ConstTree> {
    let go = |c: &ConstAst, t: Ty| const_tree(tcx, names, scope, c, t, ctor);
    Ok(match (c, tcx.kind(ty)) {
        (ConstAst::Array(items), TyKind::Fixed(e, _) | TyKind::Array(e) | TyKind::Slice(e)) => {
            ConstTree::Array(items.iter().map(|c| go(c, e)).collect::<PResult<_>>()?)
        }
        (ConstAst::Tuple(items), TyKind::Tuple(parts)) => {
            let parts = tcx.list(parts);
            if parts.len() != items.len() {
                return err(0, "a tuple constant of another length");
            }
            ConstTree::Tuple(
                items
                    .iter()
                    .zip(parts.iter())
                    .map(|(c, &t)| go(c, t))
                    .collect::<PResult<_>>()?,
            )
        }
        (ConstAst::Object(fields), TyKind::Object(shape)) => {
            let shape = tcx.shape(shape);
            let mut out = Vec::new();
            for (name, t) in &shape.fields {
                let Some((_, c, _)) = fields.iter().find(|(n, _, _)| intern(n) == *name) else {
                    return err(0, format!("field `{name}` is missing"));
                };
                out.push(go(c, *t)?);
            }
            ConstTree::Object(out)
        }
        (
            ConstAst::Adt {
                ty: t,
                case,
                fields,
                at,
            },
            _,
        ) => {
            let t = resolve_ty(tcx, names, scope, t)?;
            let TyKind::Adt(adt, _) = tcx.kind(t) else {
                return err(*at, "a class or case constant needs a class or an enum");
            };
            let variant = match case {
                Some(name) => match crate::proj::variant_named(tcx, t, *name) {
                    Some(v) => Some(v),
                    None => return err(*at, format!("no case `{name}`")),
                },
                None => None,
            };
            let pt = PlaceTy { ty: t, variant };
            let mut out = Vec::new();
            for i in 0.. {
                let f = FieldIdx::new(i);
                let Some(fty) = pt.project(tcx, crate::body::Proj::Field(f)) else {
                    break;
                };
                let name = pt
                    .field_name(tcx, f)
                    .map_or_else(|| i.to_string(), |n| n.to_string());
                let Some((_, c, _)) = fields.iter().find(|(n, _, _)| *n == name) else {
                    return err(*at, format!("field `{name}` is missing"));
                };
                out.push(go(c, fty.ty)?);
            }
            ConstTree::Adt {
                adt,
                variant,
                fields: out,
            }
        }
        (ConstAst::Null, _) => ConstTree::Null,
        (ConstAst::Present(inner), TyKind::Nullable(t)) => {
            ConstTree::Present(Box::new(go(inner, t)?))
        }
        (ConstAst::View(elem, items), _) => {
            let elem = resolve_ty(tcx, names, scope, elem)?;
            ConstTree::View {
                elem,
                items: items.iter().map(|c| go(c, elem)).collect::<PResult<_>>()?,
            }
        }
        _ => ConstTree::Scalar(const_value(tcx, names, scope, c, ty, ctor)?),
    })
}

// ---------------------------------------------------------------------------------
// Defining a parsed module.

fn attr<'a>(attrs: &'a [AttrAst], name: &str) -> Option<&'a AttrAst> {
    attrs.iter().find(|a| a.name == name)
}

fn has(attrs: &[AttrAst], name: &str) -> bool {
    attr(attrs, name).is_some()
}

const KNOWN_ATTRS: [&str; 20] = [
    "lang",
    "final",
    "abstract",
    "copy",
    "unsafe",
    "naked",
    "entry",
    "panicHandler",
    "interrupt",
    "override",
    "private",
    "protected",
    "abi",
    "intrinsic",
    "hostCall",
    "declare",
    "local",
    "mustUse",
    "repr",
    "requires",
];

fn decl_path(d: &DeclAst) -> &PathAst {
    match &d.kind {
        DeclKind::Class { path, .. }
        | DeclKind::Enum { path, .. }
        | DeclKind::Iface { path, .. }
        | DeclKind::Static { path, .. }
        | DeclKind::Const { path, .. }
        | DeclKind::Extend { path, .. }
        | DeclKind::Test { path } => path,
        DeclKind::Fn(f) => &f.path,
    }
}

struct Definer<'t> {
    tcx: &'t mut Tcx,
    names: Names,
    file: FileId,
    base: BytePos,
}

impl Definer<'_> {
    fn span(&self, at: u32) -> Span {
        Span {
            lo: self.base + at,
            hi: self.base + at,
        }
    }

    fn module(&mut self, path: ModulePath) -> ModuleId {
        if let Some(&m) = self.names.modules.get(&path) {
            return m;
        }
        let m = self
            .tcx
            .define_module(ModuleInfo::new(path, path.is_library(), self.file));
        self.names.modules.insert(path, m);
        m
    }

    fn data(&mut self, d: &DeclAst, kind: DefKind) -> PResult<DefData> {
        let p = decl_path(d);
        let path = self.names.path(p);
        if self.names.defs.contains_key(&path) {
            return err(p.at, format!("`{path}` is declared twice"));
        }
        for a in &d.attrs {
            if !KNOWN_ATTRS.contains(&a.name.as_str()) && a.name != "str_union" {
                return err(a.at, format!("no attribute `@{}`", a.name));
            }
        }
        let module = self.module(path.module);
        let mut data = DefData::new(path, kind, module, self.span(p.at));
        if has(&d.attrs, "private") {
            data.vis = Vis::Private;
        } else if has(&d.attrs, "protected") {
            data.vis = Vis::Protected;
        }
        data.attrs = self.attrs(&d.attrs)?;
        Ok(data)
    }

    fn attrs(&mut self, attrs: &[AttrAst]) -> PResult<Attrs> {
        let mut out = Attrs {
            naked: has(attrs, "naked"),
            entry: has(attrs, "entry"),
            panic_handler: has(attrs, "panicHandler"),
            must_use: has(attrs, "mustUse"),
            interrupt: has(attrs, "interrupt").then_some(false),
            ..Attrs::default()
        };
        if let Some(a) = attr(attrs, "lang") {
            let name = a.arg.as_deref().unwrap_or("");
            match LangItem::from_name(name) {
                Some(item) => out.lang = Some(item),
                None => return err(a.at, format!("no lang item `{name}`")),
            }
        }
        if let Some(a) = attr(attrs, "abi") {
            out.abi = Some(match a.arg.as_deref() {
                Some("win64") => Abi::Win64,
                Some("sysv") => Abi::Sysv,
                _ => return err(a.at, "no such ABI"),
            });
        }
        if let Some(a) = attr(attrs, "intrinsic") {
            let name = a.arg.as_deref().unwrap_or("");
            match IntrinsicName::from_name(name) {
                Some(n) => out.intrinsic = Some(n),
                None => return err(a.at, format!("no intrinsic `{name}`")),
            }
        }
        if let Some(a) = attr(attrs, "hostCall") {
            out.host_call = Some(
                self.tcx
                    .intern_host_call(intern(a.arg.as_deref().unwrap_or(""))),
            );
        }
        if let Some(a) = attr(attrs, "repr") {
            out.repr = a.arg.as_deref().and_then(Repr::from_name);
        }
        if let Some(a) = attr(attrs, "requires") {
            let mut features = Vec::new();
            for name in a.arg.iter().chain(&a.more) {
                match Feature::from_name(name) {
                    Some(f) => features.push(f),
                    None => return err(a.at, format!("no feature `{name}`")),
                }
            }
            out.requires = FeatureSet::of(&features);
        }
        Ok(out)
    }

    fn record(&mut self, def: DefId) {
        let path = self.tcx.def(def).path.clone();
        self.names.defs.insert(path, def);
    }

    /// Generic parameters owned by `owner`, their bounds left for later.
    fn params(&mut self, owner: DefId, gens: &[GenParam]) -> Vec<ParamId> {
        gens.iter()
            .enumerate()
            .map(|(i, g)| {
                let span = self.span(g.at);
                self.tcx.define_param(TyParamDef {
                    name: g.name,
                    owner,
                    index: i as u32,
                    bounds: Vec::new(),
                    implicit: None,
                    span,
                })
            })
            .collect()
    }

    fn bounds(&mut self, params: &[ParamId], gens: &[GenParam], scope: &Scope) -> PResult<()> {
        for (&p, g) in params.iter().zip(gens) {
            let ids = self.bound_ids(g, scope)?;
            self.tcx.param_mut(p).bounds.extend(ids);
        }
        Ok(())
    }

    /// The bounds `g` states, defined.
    fn bound_ids(&mut self, g: &GenParam, scope: &Scope) -> PResult<Vec<BoundId>> {
        let mut out = Vec::new();
        for b in &g.bounds {
            let t = resolve_ty(self.tcx, &self.names, scope, b)?;
            let TyKind::Adt(adt, args) = self.tcx.kind(t) else {
                return err(g.at, "a bound is a class or an interface");
            };
            let bound = match self.tcx.adt(adt).is_interface() {
                true => Bound::Iface { adt, args },
                false => Bound::Class { adt, args },
            };
            out.push(self.tcx.define_bound(bound));
        }
        Ok(out)
    }

    /// The implicit parameters of `gens` (D5): each named and bounded by its
    /// interface or object type, resolved in `scope`, as sema makes them.
    fn implicits(&mut self, params: &[ParamId], gens: &[GenParam], scope: &Scope) -> PResult<()> {
        for (&p, g) in params.iter().zip(gens) {
            let Some(t) = &g.implicit else {
                continue;
            };
            let t = resolve_ty(self.tcx, &self.names, scope, t)?;
            let (implicit, bounds, name) = match self.tcx.kind(t) {
                TyKind::Adt(adt, args) if self.tcx.adt(adt).is_interface() => {
                    let b = self.tcx.define_bound(Bound::Iface { adt, args });
                    (Implicit::Interface(adt), vec![b], self.tcx.adt(adt).name)
                }
                TyKind::Object(s) => (
                    Implicit::Shape(s),
                    Vec::new(),
                    intern(&self.tcx.ty_string(t)),
                ),
                _ => {
                    return err(
                        g.at,
                        "an implicit parameter is an interface or an object type",
                    );
                }
            };
            let param = self.tcx.param_mut(p);
            (param.name, param.implicit, param.bounds) = (name, Some(implicit), bounds);
        }
        Ok(())
    }

    /// An `extend` block: its definition, parameters and bounds, and the type it
    /// extends; methods join it as they are defined.
    fn extend(&mut self, d: &DeclAst) -> PResult<()> {
        let DeclKind::Extend { generics, ty, .. } = &d.kind else {
            return Ok(());
        };
        let data = self.data(d, DefKind::Extend)?;
        let module = data.module;
        let def = self.tcx.define_def(data);
        self.record(def);
        let params = self.params(def, generics);
        let g = self
            .tcx
            .define_generics(Generics::new(None, params.clone()));
        let scope = Scope {
            params: params
                .iter()
                .map(|&p| (self.tcx.param(p).name, p))
                .collect(),
            self_ty: None,
        };
        self.bounds(&params, generics, &scope)?;
        let ty = resolve_ty(self.tcx, &self.names, &scope, ty)?;
        self.tcx.define_extend(ExtendDef {
            def,
            module,
            generics: g,
            ty,
            members: Vec::new(),
        });
        Ok(())
    }

    fn adt_shell(&mut self, d: &DeclAst) -> PResult<()> {
        let (gens, kind) = match &d.kind {
            DeclKind::Class { generics, .. } => {
                let modifier = if has(&d.attrs, "final") {
                    ClassModifier::Final
                } else if has(&d.attrs, "abstract") {
                    ClassModifier::Abstract
                } else {
                    ClassModifier::Plain
                };
                (generics, AdtKind::Class(ClassDef::new(modifier)))
            }
            DeclKind::Enum { generics, .. } => (generics, AdtKind::Enum(EnumDef::new(Vec::new()))),
            DeclKind::Iface { generics, .. } => (
                generics,
                AdtKind::Interface(IfaceDef {
                    methods: Vec::new(),
                    sealed: None,
                    self_param: ParamId(0),
                }),
            ),
            _ => return Ok(()),
        };
        let data = self.data(d, DefKind::Fn)?;
        let name = data.path.name().expect("an item has a name");
        let empty = self.tcx.empty_generics();
        let adt = self.tcx.define_adt(AdtDecl {
            data,
            name,
            generics: empty,
            kind,
        });
        let def = self.tcx.adt(adt).def;
        let params = self.params(def, gens);
        let g = self.tcx.define_generics(Generics::new(None, params));
        self.tcx.adt_mut(adt).generics = g;
        if let DeclKind::Iface { .. } = d.kind {
            let span = self.tcx.def(def).span;
            let p = self.tcx.define_param(TyParamDef {
                name: intern("Self"),
                owner: def,
                index: 0,
                bounds: Vec::new(),
                implicit: Some(Implicit::Interface(adt)),
                span,
            });
            let sealed = self.tcx.def(def).attrs.lang.filter(|l| l.is_sealed());
            if let AdtKind::Interface(i) = &mut self.tcx.adt_mut(adt).kind {
                i.self_param = p;
                i.sealed = sealed;
            }
        }
        if has(&d.attrs, "str_union") {
            self.tcx.def_mut(def).kind = DefKind::StrUnion(adt);
        }
        if let Some(item) = self.tcx.def(def).attrs.lang {
            self.tcx.set_lang(item, def);
        }
        self.names
            .adts
            .push((name, adt, self.tcx.def(def).path.module));
        self.record(def);
        Ok(())
    }

    fn adt_of_decl(&self, d: &DeclAst) -> AdtId {
        let path = self.names.path(decl_path(d));
        let def = self.names.defs[&path];
        self.tcx.adt_of(def).expect("an ADT")
    }

    fn fields(&self, adt: AdtId, scope: &Scope, fields: &[FieldAst]) -> PResult<Vec<FieldDef>> {
        fields
            .iter()
            .filter(|f| !f.is_override)
            .map(|f| {
                let ty = resolve_ty(self.tcx, &self.names, scope, &f.ty)?;
                Ok(FieldDef {
                    name: f.name,
                    ty,
                    vis: f.vis.unwrap_or(Vis::Public),
                    readonly: f.readonly,
                    readonly_refs: f.readonly_refs.clone(),
                    has_default: f.has_default,
                    declared_in: adt,
                    span: self.span(f.at),
                    optional: f.optional,
                })
            })
            .collect()
    }

    /// A class's flattened fields, base first, the base's substituted.
    fn fill_class(
        &mut self,
        d: &DeclAst,
        done: &mut BTreeSet<AdtId>,
        decls: &[DeclAst],
    ) -> PResult<()> {
        let adt = self.adt_of_decl(d);
        if !done.insert(adt) {
            return Ok(());
        }
        let DeclKind::Class {
            base, wtf, fields, ..
        } = &d.kind
        else {
            return Ok(());
        };
        let scope = Scope::of_def(self.tcx, self.tcx.adt(adt).def);
        let mut flat = Vec::new();
        let mut hidden_base = false;
        let base_ty = match base {
            Some(b) => {
                let t = resolve_ty(self.tcx, &self.names, &scope, b)?;
                let TyKind::Adt(badt, args) = self.tcx.kind(t) else {
                    return err(decl_path(d).at, "a base is a class");
                };
                if let Some(bd) = decls.iter().find(|x| {
                    matches!(x.kind, DeclKind::Class { .. }) && self.adt_of_decl(x) == badt
                }) {
                    self.fill_class(bd, done, decls)?;
                }
                let Some(bclass) = self.tcx.adt(badt).as_class() else {
                    return err(decl_path(d).at, "a base is a class");
                };
                hidden_base = bclass.hidden_table;
                let bfields = bclass.fields.clone();
                let params = self
                    .tcx
                    .generics(self.tcx.adt(badt).generics)
                    .params
                    .clone();
                let args = self.tcx.list(args);
                for mut f in bfields {
                    f.ty = self.tcx.subst(f.ty, &params, &args);
                    flat.push(f);
                }
                Some(t)
            }
            None => None,
        };
        let own_from = flat.len() as u32;
        let mut overrides = Vec::new();
        for f in fields.iter().filter(|f| f.is_override) {
            match flat[..own_from as usize]
                .iter()
                .rposition(|x| x.name == f.name)
            {
                Some(i) => overrides.push(FieldIdx::new(i)),
                None => return err(f.at, format!("no inherited field `{}`", f.name)),
            }
        }
        flat.extend(self.fields(adt, &scope, fields)?);
        let copy = has(&d.attrs, "copy");
        if let AdtKind::Class(c) = &mut self.tcx.adt_mut(adt).kind {
            c.base = base_ty;
            c.copy = copy;
            c.fields = flat;
            c.own_from = own_from;
            c.overrides = overrides;
            c.hidden_table = c.modifier != ClassModifier::Final || hidden_base;
        }
        if *wtf {
            self.tcx
                .class_contract_or_insert_with(adt, || ClassContract {
                    writes_through_fields: true,
                });
        }
        Ok(())
    }

    fn fill_enum(&mut self, d: &DeclAst) -> PResult<()> {
        let DeclKind::Enum { cases, .. } = &d.kind else {
            return Ok(());
        };
        let adt = self.adt_of_decl(d);
        let scope = Scope::of_def(self.tcx, self.tcx.adt(adt).def);
        let mut variants = Vec::new();
        let mut values = EnumValues::None;
        for c in cases {
            let mut v = VariantDef::new(c.name);
            v.span = self.span(c.at);
            for (name, t) in &c.fields {
                let ty = resolve_ty(self.tcx, &self.names, &scope, t)?;
                v.fields.push(FieldDef::new(*name, ty, adt));
            }
            v.value = match &c.value {
                Some(crate::parse::CaseValue::Int(n)) => {
                    values = EnumValues::Ints;
                    Some(VariantValue::Int(*n))
                }
                Some(crate::parse::CaseValue::Text(s)) => {
                    values = EnumValues::Texts;
                    Some(VariantValue::Text(self.tcx.intern_str(s)))
                }
                None => None,
            };
            variants.push(v);
        }
        let repr = self.tcx.def(self.tcx.adt(adt).def).attrs.repr;
        let str_union = has(&d.attrs, "str_union");
        if let AdtKind::Enum(e) = &mut self.tcx.adt_mut(adt).kind {
            e.variants = variants;
            e.values = values;
            e.repr = repr;
            e.str_union = str_union;
        }
        Ok(())
    }

    fn function(&mut self, d: &DeclAst) -> PResult<()> {
        let DeclKind::Fn(f) = &d.kind else {
            return Ok(());
        };
        let path = self.names.path(&f.path);
        let parent = if path.segments.len() > 1 {
            let mut pp = path.clone();
            pp.segments.pop();
            pp.overload = None;
            match self.names.defs.get(&pp) {
                Some(&p) => Some(p),
                None => return err(f.path.at, format!("`{pp}` is not declared")),
            }
        } else {
            None
        };
        let parent_adt = parent.and_then(|p| self.tcx.adt_of(p));
        let extend = parent.and_then(|p| self.tcx.extends().iter().position(|e| e.def == p));
        let parent_g = match (parent_adt, extend) {
            (Some(a), _) => Some(self.tcx.adt(a).generics),
            (None, Some(i)) => Some(self.tcx.extends()[i].generics),
            (None, None) => None,
        };
        let last = path.name().expect("a function has a name");
        let kind = match (parent_g, last.as_str()) {
            (Some(_), "#ctor") => DefKind::Ctor,
            (Some(_), "#dtor") => DefKind::Dtor,
            (Some(_), _) => DefKind::Method,
            (None, _) if has(&d.attrs, "local") => DefKind::LocalFn,
            (None, _) if has(&d.attrs, "declare") => DefKind::DeclareFn,
            (None, _) => DefKind::Fn,
        };
        let mut data = self.data(d, kind)?;
        data.parent = parent;
        data.flags.is_abstract = has(&d.attrs, "abstract");
        data.flags.is_override = has(&d.attrs, "override");
        data.flags.has_body = f.body.is_some();
        let def = self.tcx.define_def(data);
        self.record(def);
        let own = f.generics.clone();
        let params = self.params(def, &own);
        let g = self
            .tcx
            .define_generics(Generics::new(parent_g, params.clone()));
        let mut scope = Scope::of_def(self.tcx, parent.unwrap_or(def));
        if parent.is_none() {
            scope = Scope::default();
        }
        // An implicit parameter's placeholder name `_` is no type a text can name.
        for &p in &params {
            scope.params.push((self.tcx.param(p).name, p));
        }
        self.bounds(&params, &own, &scope)?;
        self.implicits(&params, &own, &scope)?;
        let mut where_bounds = Vec::new();
        for w in &f.wheres {
            let Some(&(_, p)) = scope.params.iter().find(|(n, _)| *n == w.name) else {
                return err(w.at, format!("no parameter `{}` to bound", w.name));
            };
            where_bounds.push((p, self.bound_ids(w, &scope)?));
        }
        let receiver = match (kind, f.receiver) {
            (DefKind::Method | DefKind::Dtor, Some(r)) => Some(r),
            (DefKind::Method | DefKind::Dtor, None) => Some(Receiver::Ref(
                f.params.first().map_or(Mark::None, |p| p.mark),
            )),
            (_, Some(Receiver::Static)) | (_, None) => None,
            (_, Some(_)) => return err(f.path.at, "only a method has a receiver"),
        };
        // A constructor's `this` is its first parameter, `_1: &C`, as a method's
        // receiver is, though its signature has no receiver (Tcx::takes_this).
        let skip = usize::from(
            kind == DefKind::Ctor || matches!(receiver, Some(Receiver::Ref(_) | Receiver::Move)),
        );
        if f.params.len() < skip {
            return err(
                f.path.at,
                "a method's or constructor's first parameter is `this`",
            );
        }
        for (i, p) in f.params.iter().enumerate() {
            if p.local as usize != i + 1 {
                return err(f.path.at, format!("parameter {} is not _{}", i + 1, i + 1));
            }
        }
        // Each parameter of type `I`, `&I`, `{..}` or `&{..}` takes the next implicit
        // parameter of that type, in order, as sema made them (D5); nothing nested.
        let tcx = &*self.tcx;
        let mut implicit = params
            .iter()
            .filter(|&&q| tcx.param(q).implicit.is_some())
            .peekable();
        let mut sig_params = Vec::new();
        for p in &f.params[skip..] {
            let mut ty = resolve_ty(tcx, &self.names, &scope, &p.ty)?;
            let (inner, by_ref) = match tcx.kind(ty) {
                TyKind::Ref(t) => (t, true),
                _ => (ty, false),
            };
            let of = match tcx.kind(inner) {
                TyKind::Adt(adt, _) => Some(Implicit::Interface(adt)),
                TyKind::Object(s) => Some(Implicit::Shape(s)),
                _ => None,
            };
            if let Some(&&q) = implicit.peek()
                && tcx.param(q).implicit == of
            {
                implicit.next();
                ty = match by_ref {
                    true => tcx.mk_ref(tcx.mk_param(q)),
                    false => tcx.mk_param(q),
                };
            }
            sig_params.push(ParamSig {
                name: intern(&format!("_{}", p.local)),
                ty,
                mark: p.mark,
                has_default: p.has_default,
                fn_names: None,
                span: p.span,
            });
        }
        let ret = resolve_ty(self.tcx, &self.names, &scope, &f.ret)?;
        let mut sig = FnSig::new(g, sig_params, ret);
        sig.where_bounds = where_bounds;
        sig.receiver = receiver;
        sig.ret_readonly = f.ret_readonly;
        sig.unsafety = has(&d.attrs, "unsafe");
        sig.abi = self.tcx.def(def).attrs.abi.unwrap_or(Abi::Enrang);
        sig.requires = self.tcx.def(def).attrs.requires;
        self.tcx.set_sig(def, sig);
        if let Some(item) = self.tcx.def(def).attrs.lang {
            self.tcx.set_lang(item, def);
        }
        if let Some(pa) = parent_adt {
            match &mut self.tcx.adt_mut(pa).kind {
                AdtKind::Class(c) => match kind {
                    DefKind::Ctor => c.ctors.push(def),
                    DefKind::Dtor => c.dtor = Some(def),
                    _ => c.methods.push(def),
                },
                AdtKind::Enum(e) => e.methods.push(def),
                AdtKind::Interface(i) => i.methods.push(def),
            }
        }
        if let Some(i) = extend {
            self.tcx.extend_mut(i).members.push(def);
        }
        if let Some(c) = &f.contract {
            let contract = self.contract(def, c)?;
            self.tcx.contract_or_insert_with(def, || contract);
        }
        Ok(())
    }

    fn contract(&self, def: DefId, c: &ContractAst) -> PResult<Contract> {
        let sig = self.tcx.sig(def);
        let perms = match &c.perms {
            Some(p) => p.clone(),
            None => {
                let mut perms = Vec::new();
                match sig.receiver {
                    Some(Receiver::Move) => perms.push(Perm::Own),
                    Some(Receiver::Ref(Mark::Let)) => perms.push(Perm::Write),
                    Some(Receiver::Ref(_)) => perms.push(Perm::Read),
                    // A constructor writes the object it builds.
                    _ if self.tcx.def(def).kind == DefKind::Ctor => perms.push(Perm::Write),
                    _ => {}
                }
                for p in &sig.params {
                    if matches!(self.tcx.kind(p.ty), TyKind::Ref(_)) {
                        perms.push(match p.mark {
                            Mark::Let => Perm::Write,
                            _ => Perm::Read,
                        });
                    }
                }
                perms
            }
        };
        let sources = match &c.sources {
            Some(v) if !v.is_empty() => RetSources::Params(v.clone()),
            _ => RetSources::NoLoans,
        };
        let result = match &c.result {
            Some(ResultAst::None) => ResultPerm::None,
            Some(ResultAst::Writable) => ResultPerm::Writable,
            Some(ResultAst::ReadOnly(r)) => ResultPerm::ReadOnly(self.reason(r)?),
            None if self.tcx.is_ref_type(sig.ret) => match sig.ret_readonly {
                true => ResultPerm::ReadOnly(Reason::Declared),
                false => ResultPerm::Writable,
            },
            None => ResultPerm::None,
        };
        Ok(Contract {
            perms,
            sources,
            result,
            through_fields: c.through_fields.clone(),
            through_read: c.through_read.clone(),
            stores: c.stores.clone(),
            moves_or_writes: c.moves.clone(),
        })
    }

    fn reason(&self, r: &ReasonAst) -> PResult<Reason> {
        Ok(match r {
            ReasonAst::Simple(r) => r.clone(),
            ReasonAst::Path(k, p) => {
                let path = self.names.path(p);
                match k {
                    0 => Reason::Constant(path),
                    1 => Reason::Static(path),
                    _ => Reason::ReadonlyResult(path),
                }
            }
            ReasonAst::Field(p, name) => {
                let path = self.names.path(p);
                let f = match name.parse::<u32>() {
                    Ok(n) => FieldIdx(n),
                    Err(_) => {
                        let class = self
                            .names
                            .defs
                            .get(&path)
                            .and_then(|&d| self.tcx.adt_of(d))
                            .and_then(|a| self.tcx.adt(a).as_class())
                            .and_then(|c| c.field_named(intern(name)));
                        match class {
                            Some((f, _)) => f,
                            None => return err(p.at, format!("no field `{name}` of `{path}`")),
                        }
                    }
                };
                Reason::ReadonlyField(path, f)
            }
        })
    }

    fn item(&mut self, d: &DeclAst) -> PResult<()> {
        match &d.kind {
            DeclKind::Static { ty, .. } => {
                let data = self.data(d, DefKind::Static)?;
                let def = self.tcx.define_def(data);
                self.record(def);
                let t = resolve_ty(self.tcx, &self.names, &Scope::default(), ty)?;
                self.tcx.set_item_ty(def, t);
            }
            DeclKind::Test { .. } => {
                let path = self.names.path(decl_path(d));
                if !self.names.defs.contains_key(&path) {
                    let data = self.data(d, DefKind::Test)?;
                    let def = self.tcx.define_def(data);
                    self.record(def);
                }
            }
            DeclKind::Const { ty, .. } => {
                let data = self.data(d, DefKind::Const)?;
                let def = self.tcx.define_def(data);
                self.record(def);
                let t = resolve_ty(self.tcx, &self.names, &Scope::default(), ty)?;
                self.tcx.set_item_ty(def, t);
            }
            _ => {}
        }
        Ok(())
    }

    fn const_value(&mut self, d: &DeclAst) -> PResult<()> {
        if let DeclKind::Const { value, .. } = &d.kind {
            let def = self.names.defs[&self.names.path(decl_path(d))];
            let ty = self.tcx.item_ty(def).expect("a constant has a type");
            let tree = const_tree(self.tcx, &self.names, &Scope::default(), value, ty, None)?;
            self.tcx.set_const(def, tree);
        }
        Ok(())
    }
}

/// Defines every declaration of `top` in `tcx` (plan b.6): modules, ADTs and their
/// parameters, bounds, fields and cases, functions with their signatures and
/// stated contracts, statics, tests, and constants with their values.
pub(crate) fn define(tcx: &mut Tcx, top: &TopLevel, file: FileId, base: BytePos) -> PResult<Names> {
    let module = ModulePath::new(top.module_name());
    let mut d = Definer {
        tcx,
        names: Names {
            module,
            adts: Vec::new(),
            defs: BTreeMap::new(),
            modules: BTreeMap::new(),
        },
        file,
        base,
    };
    d.module(module);
    for decl in &top.decls {
        d.adt_shell(decl)?;
    }
    for decl in &top.decls {
        let gens = match &decl.kind {
            DeclKind::Class { generics, .. }
            | DeclKind::Enum { generics, .. }
            | DeclKind::Iface { generics, .. } => generics,
            _ => continue,
        };
        let adt = d.adt_of_decl(decl);
        let def = d.tcx.adt(adt).def;
        let params = d.tcx.generics(d.tcx.adt(adt).generics).params.clone();
        let scope = Scope::of_def(d.tcx, def);
        d.bounds(&params, gens, &scope)?;
    }
    let mut done = BTreeSet::new();
    for decl in &top.decls {
        match decl.kind {
            DeclKind::Class { .. } => d.fill_class(decl, &mut done, &top.decls)?,
            DeclKind::Enum { .. } => d.fill_enum(decl)?,
            _ => {}
        }
    }
    for decl in &top.decls {
        d.extend(decl)?;
    }
    for decl in &top.decls {
        d.function(decl)?;
        d.item(decl)?;
    }
    for decl in &top.decls {
        d.const_value(decl)?;
    }
    Ok(d.names)
}

/// The resolution tables of an existing `tcx`, its texts in module `module`.
fn names_of(tcx: &Tcx, module: ModulePath) -> Names {
    let mut names = Names {
        module,
        adts: Vec::new(),
        defs: BTreeMap::new(),
        modules: BTreeMap::new(),
    };
    for (m, info) in tcx.modules() {
        names.modules.insert(info.path, m);
    }
    for (def, data) in tcx.defs() {
        names.defs.insert(data.path.clone(), def);
        if let DefKind::Adt(a) | DefKind::StrUnion(a) = data.kind {
            names.adts.push((tcx.adt(a).name, a, data.path.module));
        }
    }
    names
}

/// `redefine_adts`: each class or enum of `top` already in `tcx` gets the fields or
/// cases `top` gives it, keeping its id and parameters.
pub(crate) fn redefine(tcx: &mut Tcx, top: &TopLevel) -> PResult<()> {
    let module = ModulePath::new(top.module_name());
    let names = names_of(tcx, module);
    let mut d = Definer {
        tcx,
        names,
        file: FileId(0),
        base: BytePos(0),
    };
    for decl in &top.decls {
        let p = decl_path(decl);
        let path = d.names.path(p);
        let Some(adt) = d.names.defs.get(&path).and_then(|&x| d.tcx.adt_of(x)) else {
            return err(p.at, format!("`{path}` is no ADT of the module"));
        };
        let scope = Scope::of_def(d.tcx, d.tcx.adt(adt).def);
        match &decl.kind {
            DeclKind::Class { fields, .. } => {
                let own_from = d.tcx.adt(adt).as_class().map_or(0, |c| c.own_from as usize);
                let mut flat: Vec<FieldDef> = d
                    .tcx
                    .adt(adt)
                    .as_class()
                    .map(|c| c.fields[..own_from].to_vec())
                    .unwrap_or_default();
                flat.extend(d.fields(adt, &scope, fields)?);
                if let AdtKind::Class(c) = &mut d.tcx.adt_mut(adt).kind {
                    c.fields = flat;
                }
            }
            DeclKind::Enum { .. } => d.fill_enum(decl)?,
            _ => return err(p.at, "only classes and enums are redefined"),
        }
    }
    Ok(())
}

/// A body's owner, scope, return type and arguments (with their spans) from its
/// head: a function's declaration, or the head's own parameter list.
pub(crate) fn body_head(
    tcx: &Tcx,
    names: &Names,
    b: &BodyAst,
) -> PResult<(BodyOwner, Scope, Ty, Vec<(Ty, Span)>)> {
    let fn_scope = |def: DefId| Scope::of_def(tcx, def);
    let module = names.modules[&names.module];
    let (owner, scope) = match &b.owner {
        OwnerAst::Fn(p) => {
            let def = names.def(p)?;
            let sig = tcx.sig(def);
            let scope = fn_scope(def);
            let mut args = Vec::new();
            let span = tcx.def(def).span;
            if tcx.takes_this(def) {
                args.push((tcx.mk_ref(self_ty(tcx, def)), span));
            }
            for p in &sig.params {
                args.push((p.ty, if p.span.is_dummy() { span } else { p.span }));
            }
            return Ok((BodyOwner::Fn(def), scope, sig.ret, args));
        }
        OwnerAst::Statements => (BodyOwner::Statements(module), Scope::default()),
        OwnerAst::Test(p) => (BodyOwner::Test(names.def(p)?), Scope::default()),
        OwnerAst::Arrow(parent, k) => {
            let (parent, scope) = match parent {
                ParentAst::Fn(p) => {
                    let d = names.def(p)?;
                    (enrang_hir::BodyOwner::Fn(d), fn_scope(d))
                }
                ParentAst::Const(p) => (
                    enrang_hir::BodyOwner::Const(names.def(p)?),
                    Scope::default(),
                ),
                ParentAst::Test(p) => {
                    (enrang_hir::BodyOwner::Test(names.def(p)?), Scope::default())
                }
                ParentAst::Statements => {
                    (enrang_hir::BodyOwner::Statements(module), Scope::default())
                }
            };
            (BodyOwner::Arrow(parent, enrang_hir::ArrowId(*k)), scope)
        }
        OwnerAst::Shim(s) => {
            let scope = Scope::default();
            let kind = match s {
                ShimAst::Ty(word, t) => shim_of(word, resolve_ty(tcx, names, &scope, t)?),
                ShimAst::Fn(true, p) => ShimKind::FnAsClosure(fn_ref(tcx, names, &scope, p)?),
                ShimAst::Fn(false, p) => ShimKind::StringForm(fn_ref(tcx, names, &scope, p)?),
                ShimAst::Env(a, c) => ShimKind::StringFormEnv {
                    from: resolve_ty(tcx, names, &scope, a)?,
                    to: resolve_ty(tcx, names, &scope, c)?,
                },
            };
            (BodyOwner::Shim(kind), scope)
        }
    };
    let ret = resolve_ty(
        tcx,
        names,
        &scope,
        b.ret
            .as_ref()
            .expect("a body with its own head has a return type"),
    )?;
    let mut args = Vec::new();
    for (i, p) in b.params.iter().enumerate() {
        if p.local as usize != i + 1 || p.mark != Mark::None {
            return err(0, format!("parameter {} is not `_{}: type`", i + 1, i + 1));
        }
        args.push((resolve_ty(tcx, names, &scope, &p.ty)?, p.span));
    }
    Ok((owner, scope, ret, args))
}

/// The type a method's `this` points at: its class or enum, an interface's `Self`,
/// an `extend` block's type.
pub(crate) fn self_ty(tcx: &Tcx, def: DefId) -> Ty {
    let Some(parent) = tcx.def(def).parent else {
        return tcx.common().error;
    };
    if let Some(adt) = tcx.adt_of(parent) {
        return match &tcx.adt(adt).kind {
            AdtKind::Interface(i) => tcx.mk_param(i.self_param),
            _ => tcx.adt_identity(adt),
        };
    }
    tcx.extends()
        .iter()
        .find(|e| e.def == parent)
        .map_or(tcx.common().error, |e| e.ty)
}

// ---------------------------------------------------------------------------------
// Printing.

/// Every definition the bodies reference, and what those reference in turn: the
/// ADTs of their types, the functions they call or name, statics, the parents of
/// methods, the owners of arrows.
fn referenced(tcx: &Tcx, bodies: &[&Body]) -> BTreeSet<DefId> {
    let mut tys: Vec<Ty> = Vec::new();
    let mut defs: Vec<DefId> = Vec::new();
    let fns = |f: enrang_hir::FnRef, tys: &mut Vec<Ty>, defs: &mut Vec<DefId>| {
        defs.push(f.def);
        tys.extend(tcx.list(f.args).iter().copied());
    };
    let op = |o: &Operand, tys: &mut Vec<Ty>, defs: &mut Vec<DefId>| {
        if let Operand::Const(c) = o {
            tys.push(c.ty);
            if let ConstKind::Value(v) = &c.kind {
                match v {
                    ConstValue::FnAddr(f) => {
                        defs.push(f.def);
                        tys.extend(tcx.list(f.args).iter().copied());
                    }
                    ConstValue::StaticAddr(d) => defs.push(*d),
                    _ => {}
                }
            }
        }
    };
    for b in bodies {
        match b.owner {
            BodyOwner::Fn(d) | BodyOwner::Test(d) => defs.push(d),
            BodyOwner::Arrow(p, _) => match p {
                enrang_hir::BodyOwner::Fn(d)
                | enrang_hir::BodyOwner::Const(d)
                | enrang_hir::BodyOwner::Test(d) => defs.push(d),
                enrang_hir::BodyOwner::Statements(_) => {}
            },
            BodyOwner::Statements(_) => {}
            BodyOwner::Shim(k) => match k {
                ShimKind::FnAsClosure(f) | ShimKind::StringForm(f) => fns(f, &mut tys, &mut defs),
                ShimKind::StringFormEnv { from, to } => tys.extend([from, to]),
                ShimKind::DropGlue(t)
                | ShimKind::CloneGlue(t)
                | ShimKind::EqGlue(t)
                | ShimKind::ShowGlue(t)
                | ShimKind::DisplayGlue(t)
                | ShimKind::NamedFill(t) => tys.push(t),
            },
        }
        tys.extend(b.locals.iter().map(|l| l.ty));
        tys.extend(b.captures.iter().map(|c| c.ty));
        tys.extend(b.literals.iter().map(|l| l.ty));
        for block in b.blocks.iter() {
            let stmts = block.stmts.iter().map(|s| (Some(&s.kind), None));
            for (st, term) in stmts.chain([(None, Some(&block.term.kind))]) {
                crate::verify::operands(st, term).for_each(|o| op(o, &mut tys, &mut defs));
                match st {
                    Some(StatementKind::Assign { value, .. }) => match value {
                        Rvalue::Cast(_, _, t) | Rvalue::Aggregate(AggregateKind::Fixed(t), _) => {
                            tys.push(*t)
                        }
                        Rvalue::Aggregate(AggregateKind::Adt { adt, args, .. }, _) => {
                            tys.push(tcx.mk_adt(*adt, &tcx.list(*args)))
                        }
                        Rvalue::Aggregate(AggregateKind::Object(s), _) => {
                            tys.push(tcx.mk_object_shape((*tcx.shape(*s)).clone()))
                        }
                        Rvalue::ClosureValue {
                            func: ClosureFn::Named(f),
                            ..
                        } => fns(*f, &mut tys, &mut defs),
                        _ => {}
                    },
                    Some(StatementKind::SetTable { class, .. }) => tys.push(*class),
                    Some(StatementKind::Intrinsic { kind, .. }) => match kind {
                        IntrinsicKind::SizeOf(t)
                        | IntrinsicKind::AlignOf(t)
                        | IntrinsicKind::AllocArray(t)
                        | IntrinsicKind::SliceFromRaw(t)
                        | IntrinsicKind::OffsetOf(t, _) => tys.push(*t),
                        _ => {}
                    },
                    _ => {}
                }
                match term {
                    Some(TerminatorKind::Call {
                        callee: Callee::Fn(f) | Callee::Virtual { method: f, .. },
                        ..
                    }) => fns(*f, &mut tys, &mut defs),
                    Some(TerminatorKind::Call {
                        callee: Callee::Foreign(f),
                        ..
                    }) => defs.push(f.def),
                    Some(TerminatorKind::Call {
                        callee: Callee::NamedFill { class, .. } | Callee::ImplicitCtor { class },
                        ..
                    }) => tys.push(*class),
                    _ => {}
                }
            }
        }
    }
    let mut out = BTreeSet::new();
    let mut seen_tys = BTreeSet::new();
    loop {
        if let Some(t) = tys.pop() {
            if seen_tys.insert(t) {
                if let TyKind::Adt(adt, _) = tcx.kind(t) {
                    defs.push(tcx.adt(adt).def);
                }
                tys.extend(tcx.children(t));
            }
            continue;
        }
        let Some(d) = defs.pop() else {
            break;
        };
        if !out.insert(d) {
            continue;
        }
        let data = tcx.def(d);
        defs.extend(data.parent);
        match data.kind {
            DefKind::Adt(a) | DefKind::StrUnion(a) => {
                let adt = tcx.adt(a);
                for p in tcx.all_params(adt.generics) {
                    for &b in &tcx.param(p).bounds {
                        let bound = tcx.bound(b);
                        tys.push(tcx.mk_adt(bound.adt(), &tcx.list(bound.args())));
                    }
                }
                match &adt.kind {
                    AdtKind::Class(c) => {
                        tys.extend(c.base);
                        tys.extend(c.fields.iter().map(|f| f.ty));
                    }
                    AdtKind::Enum(e) => {
                        tys.extend(
                            e.variants
                                .iter()
                                .flat_map(|v| v.fields.iter().map(|f| f.ty)),
                        );
                    }
                    AdtKind::Interface(_) => {}
                }
            }
            DefKind::Const | DefKind::Static => {
                tys.extend(tcx.item_ty(d));
                if let Some(tree) = tcx.const_value(d) {
                    let mut stack = vec![tree];
                    while let Some(t) = stack.pop() {
                        match t {
                            ConstTree::Scalar(ConstValue::FnAddr(f)) => defs.push(f.def),
                            ConstTree::Scalar(ConstValue::StaticAddr(s)) => defs.push(*s),
                            ConstTree::Array(items)
                            | ConstTree::Tuple(items)
                            | ConstTree::Object(items) => stack.extend(items),
                            ConstTree::Adt { adt, fields, .. } => {
                                defs.push(tcx.adt(*adt).def);
                                stack.extend(fields);
                            }
                            ConstTree::Present(inner) => stack.push(inner),
                            ConstTree::View { elem, items } => {
                                tys.push(*elem);
                                stack.extend(items);
                            }
                            _ => {}
                        }
                    }
                }
            }
            DefKind::Extend => {
                if let Some(e) = tcx.extends().iter().find(|e| e.def == d) {
                    tys.push(e.ty);
                    let params = &tcx.generics(e.generics).params;
                    let bounds = params.iter().flat_map(|&p| tcx.param(p).bounds.clone());
                    tys.extend(bounds.map(|b| bound_ty(tcx, b)));
                }
            }
            _ => {
                if let Some(sig) = tcx.sig_opt(d) {
                    tys.extend(sig.params.iter().map(|p| p.ty));
                    tys.push(sig.ret);
                    let own = tcx.generics(sig.generics).params.iter();
                    let bounds = own.flat_map(|&p| tcx.param(p).bounds.clone());
                    let wheres = sig.where_bounds.iter().flat_map(|(_, b)| b.iter().copied());
                    tys.extend(bounds.chain(wheres).map(|b| bound_ty(tcx, b)));
                }
            }
        }
    }
    out
}

/// The declarations `bodies` reference, in `ItemPath` order, but the functions and
/// tests whose bodies print as their own heads.
pub(crate) fn print_decls(p: &Printer, bodies: &[&Body]) -> String {
    let tcx = p.tcx;
    let owners: BTreeSet<DefId> = bodies
        .iter()
        .filter_map(|b| match b.owner {
            BodyOwner::Fn(d) | BodyOwner::Test(d) => Some(d),
            _ => None,
        })
        .collect();
    let mut defs: Vec<DefId> = referenced(tcx, bodies)
        .into_iter()
        .filter(|d| !owners.contains(d))
        .filter(|&d| {
            matches!(
                tcx.def(d).kind,
                DefKind::Adt(_)
                    | DefKind::StrUnion(_)
                    | DefKind::Extend
                    | DefKind::Fn
                    | DefKind::LocalFn
                    | DefKind::DeclareFn
                    | DefKind::Method
                    | DefKind::Ctor
                    | DefKind::Dtor
                    | DefKind::Const
                    | DefKind::Static
                    | DefKind::Test
            )
        })
        .collect();
    defs.sort_by(|a, b| tcx.def(*a).path.cmp(&tcx.def(*b).path));
    let mut out = String::new();
    for d in defs {
        out.push_str(&decl(p, d));
    }
    out
}

/// The `@` attributes of a definition, in a fixed order.
fn attr_text(p: &Printer, d: DefId) -> String {
    let tcx = p.tcx;
    let data = tcx.def(d);
    let a = &data.attrs;
    let class = tcx.adt_of(d).and_then(|adt| tcx.adt(adt).as_class());
    let modifier = class.map(|c| c.modifier);
    let sig = tcx.sig_opt(d);
    let arg = |name: &str, v: Option<&str>| v.map(|v| format!("@{name}({})", quote(v)));
    let parts = [
        arg("lang", a.lang.map(|l| l.name())),
        (data.vis == Vis::Private).then(|| "@private".to_owned()),
        (data.vis == Vis::Protected).then(|| "@protected".to_owned()),
        (modifier == Some(ClassModifier::Final)).then(|| "@final".to_owned()),
        (modifier == Some(ClassModifier::Abstract)).then(|| "@abstract".to_owned()),
        class.is_some_and(|c| c.copy).then(|| "@copy".to_owned()),
        (tcx.adt_of(d).and_then(|adt| tcx.adt(adt).as_enum()))
            .is_some_and(|e| e.str_union)
            .then(|| "@str_union".to_owned()),
        arg("repr", a.repr.map(|r| name_of(REPRS, &r))),
        sig.is_some_and(|s| s.unsafety)
            .then(|| "@unsafe".to_owned()),
        arg("abi", sig.and_then(|s| s.abi.name())),
        sig.filter(|s| !s.requires.is_empty()).map(|s| {
            let names: Vec<String> = s.requires.iter().map(|f| quote(f.name())).collect();
            format!("@requires({})", names.join(", "))
        }),
    ];
    let mut parts: Vec<String> = parts.into_iter().flatten().collect();
    for (on, name) in [
        (a.naked, "@naked"),
        (a.entry, "@entry"),
        (a.panic_handler, "@panicHandler"),
        (a.interrupt.is_some(), "@interrupt"),
        (a.must_use, "@mustUse"),
        (data.flags.is_abstract, "@abstract"),
        (data.flags.is_override, "@override"),
        (data.kind == DefKind::DeclareFn, "@declare"),
        (data.kind == DefKind::LocalFn, "@local"),
    ] {
        if on {
            parts.push(name.to_owned());
        }
    }
    parts.extend(arg("intrinsic", a.intrinsic.map(|i| i.name())));
    parts.extend(arg(
        "hostCall",
        a.host_call.map(|h| tcx.host_call_name(h).as_str()),
    ));
    parts.dedup();
    parts.iter().map(|s| format!("{s} ")).collect()
}

/// A bound as the type it names.
fn bound_ty(tcx: &Tcx, b: BoundId) -> Ty {
    let b = tcx.bound(b);
    tcx.mk_adt(b.adt(), &tcx.list(b.args()))
}

/// `T extends A & B`, a parameter's name with its bounds, or `T` alone.
fn bounded(p: &Printer, name: Symbol, bounds: &[BoundId]) -> String {
    let bounds: Vec<String> = bounds.iter().map(|&b| p.ty(bound_ty(p.tcx, b))).collect();
    match bounds.is_empty() {
        true => name.to_string(),
        false => format!("{name} extends {}", bounds.join(" & ")),
    }
}

/// `<T extends A & B, U, implicit I>`: the parameters with their bounds, an
/// implicit one (D5) as the interface or object type that makes it.
fn generics_text(p: &Printer, params: &[ParamId]) -> Vec<String> {
    let tcx = p.tcx;
    params
        .iter()
        .map(|&id| {
            let param = tcx.param(id);
            match param.implicit {
                Some(Implicit::Interface(_)) if param.bounds.len() == 1 => {
                    format!("implicit {}", p.ty(bound_ty(tcx, param.bounds[0])))
                }
                Some(Implicit::Shape(s)) => format!(
                    "implicit {}",
                    p.ty(tcx.mk_object_shape((*tcx.shape(s)).clone()))
                ),
                _ => bounded(p, param.name, &param.bounds),
            }
        })
        .collect()
}

fn decl(p: &Printer, d: DefId) -> String {
    let tcx = p.tcx;
    let data = tcx.def(d);
    let attrs = attr_text(p, d);
    match data.kind {
        DefKind::Adt(a) | DefKind::StrUnion(a) => {
            let adt = tcx.adt(a);
            let gens = generics_text(p, &tcx.generics(adt.generics).params);
            let path = p.path_with_args(&data.path, &[(data.path.segments.len() - 1, gens)]);
            match &adt.kind {
                AdtKind::Class(c) => {
                    let base = c
                        .base
                        .map(|b| format!(" extends {}", p.ty(b)))
                        .unwrap_or_default();
                    let wtf = match tcx.class_contract_memo(a) {
                        Some(ClassContract {
                            writes_through_fields: true,
                        }) => " writes_through_fields",
                        _ => "",
                    };
                    let mut lines = Vec::new();
                    for &f in &c.overrides {
                        let field = &c.fields[f.index()];
                        lines.push(format!(
                            "  {}: {} = default override;\n",
                            field.name,
                            p.ty(field.ty)
                        ));
                    }
                    for (_, f) in c.own_fields() {
                        lines.push(format!("  {}\n", field_text(p, f)));
                    }
                    let body = match lines.is_empty() {
                        true => " }".to_owned(),
                        false => format!("\n{}}}", lines.concat()),
                    };
                    format!("{attrs}class {path}{base}{wtf} {{{body}\n")
                }
                AdtKind::Enum(e) => {
                    let cases: Vec<String> = e
                        .variants
                        .iter()
                        .map(|v| {
                            let mut s = v.name.to_string();
                            if !v.fields.is_empty() {
                                let fs: Vec<String> = v
                                    .fields
                                    .iter()
                                    .map(|f| format!("{}: {}", f.name, p.ty(f.ty)))
                                    .collect();
                                s.push_str(&format!(" {{ {} }}", fs.join(", ")));
                            }
                            match v.value {
                                Some(VariantValue::Int(n)) => s.push_str(&format!(" = {n}")),
                                Some(VariantValue::Text(t)) => {
                                    s.push_str(&format!(" = {}", quote(&tcx.str(t))))
                                }
                                None => {}
                            }
                            s
                        })
                        .collect();
                    format!("{attrs}enum {path} {{ {} }}\n", cases.join(", "))
                }
                AdtKind::Interface(_) => format!("{attrs}interface {path} {{ }}\n"),
            }
        }
        DefKind::Const => {
            let ty = tcx.item_ty(d).unwrap_or(tcx.common().error);
            let value = tcx
                .const_value(d)
                .map_or_else(|| "void".to_owned(), |t| p.const_tree(ty, t));
            format!("{attrs}const {}: {} = {value};\n", p.def_path(d), p.ty(ty))
        }
        DefKind::Static => {
            let ty = tcx.item_ty(d).unwrap_or(tcx.common().error);
            format!("{attrs}static {}: {};\n", p.def_path(d), p.ty(ty))
        }
        DefKind::Test => format!("{attrs}test {};\n", p.def_path(d)),
        DefKind::Extend => {
            let e = tcx
                .extends()
                .iter()
                .find(|e| e.def == d)
                .expect("a defined block");
            let gens = generics_text(p, &tcx.generics(e.generics).params);
            let path = p.path_with_args(&data.path, &[(data.path.segments.len() - 1, gens)]);
            format!("{attrs}extend {path}: {};\n", p.ty(e.ty))
        }
        _ => format!("{};\n", fn_head(p, d).0),
    }
}

/// A field line: `[private ][readonly ]name[?]: [readonly ]ty[ readonly_at([0, 1])][ = default];`,
/// `readonly_at` listing the tuple positions of the nested `readonly &` parts.
fn field_text(p: &Printer, f: &FieldDef) -> String {
    let vis = match f.vis {
        Vis::Private => "private ",
        Vis::Protected => "protected ",
        Vis::Public => "",
    };
    let readonly = if f.readonly { "readonly " } else { "" };
    let optional = if f.optional { "?" } else { "" };
    let whole = f.readonly_refs.iter().any(|r| r.is_empty());
    let ty_ro = if whole { "readonly " } else { "" };
    let nested: Vec<String> = f
        .readonly_refs
        .iter()
        .filter(|r| !r.is_empty())
        .map(|r| format!("[{}]", ints(r)))
        .collect();
    let at = match nested.is_empty() {
        true => String::new(),
        false => format!(" readonly_at({})", nested.join(", ")),
    };
    let default = if f.has_default { " = default" } else { "" };
    format!(
        "{vis}{readonly}{}{optional}: {ty_ro}{}{at}{default};",
        f.name,
        p.ty(f.ty)
    )
}

/// A function's declaration line, its contract included, and how many arguments
/// it declares (the receiver and the signature's parameters).
pub(crate) fn fn_head(p: &Printer, d: DefId) -> (String, usize) {
    let tcx = p.tcx;
    let data = tcx.def(d);
    let sig = tcx.sig(d);
    let attrs = attr_text(p, d);
    let prefix = match sig.receiver {
        Some(Receiver::Static) => "static ",
        Some(Receiver::Move) => "move ",
        _ => "",
    };
    let last = data.path.segments.len() - 1;
    let own = generics_text(p, &tcx.generics(sig.generics).params);
    let mut args = vec![(last, own)];
    if last > 0
        && let Some(parent) = tcx.generics(sig.generics).parent
    {
        let names: Vec<String> = tcx
            .all_params(parent)
            .into_iter()
            .map(|id| tcx.param(id).name.to_string())
            .collect();
        args.push((last - 1, names));
    }
    let path = p.path_with_args(&data.path, &args);
    let mut params = Vec::new();
    if let Some(r @ (Receiver::Ref(_) | Receiver::Move)) = sig.receiver {
        let mark = match r {
            Receiver::Ref(Mark::Let) => "let ",
            Receiver::Ref(Mark::Const) => "const ",
            _ => "",
        };
        params.push(format!("{mark}_1: {}", p.ty(tcx.mk_ref(self_ty(tcx, d)))));
    } else if data.kind == DefKind::Ctor {
        params.push(format!("_1: {}", p.ty(tcx.mk_ref(self_ty(tcx, d)))));
    }
    for sp in &sig.params {
        let mark = match sp.mark {
            Mark::Let => "let ",
            Mark::Const => "const ",
            Mark::None => "",
        };
        let default = if sp.has_default { " = default" } else { "" };
        params.push(format!(
            "{mark}_{}: {}{default}",
            params.len() + 1,
            p.ty(sp.ty)
        ));
    }
    let readonly = if sig.ret_readonly { "readonly " } else { "" };
    let mut head = format!(
        "{attrs}{prefix}fn {path}({}) -> {readonly}{}",
        params.join(", "),
        p.ty(sig.ret)
    );
    let wheres: Vec<String> = (sig.where_bounds.iter())
        .map(|(q, bounds)| bounded(p, tcx.param(*q).name, bounds))
        .collect();
    if !wheres.is_empty() {
        head.push_str(&format!(" where {}", wheres.join(", ")));
    }
    if let Some(c) = tcx.contract_memo(d) {
        head.push_str(&contract_text(p, &c));
    }
    (head, params.len())
}

fn ints(v: &[u32]) -> String {
    v.iter().map(u32::to_string).collect::<Vec<_>>().join(", ")
}

/// ` perms(..) sources(..)[ through_fields(..)][ through_read(..)][ stores(..)][ moves(..)] result ..`.
fn contract_text(p: &Printer, c: &Contract) -> String {
    let mut s = String::new();
    let perms: Vec<&str> = c.perms.iter().map(|perm| name_of(PERMS, perm)).collect();
    s.push_str(&format!(" perms({})", perms.join(", ")));
    match &c.sources {
        RetSources::NoLoans => s.push_str(" sources()"),
        RetSources::Params(v) => s.push_str(&format!(" sources({})", ints(v))),
    }
    if !c.through_fields.is_empty() {
        s.push_str(&format!(" through_fields({})", ints(&c.through_fields)));
    }
    if !c.through_read.is_empty() {
        s.push_str(&format!(" through_read({})", ints(&c.through_read)));
    }
    if !c.stores.is_empty() {
        let stores: Vec<String> = c
            .stores
            .iter()
            .map(|st| {
                let mut t = format!("{} -> {}", st.from, st.into);
                for (on, word) in [
                    (st.fields_only, " fields_only"),
                    (st.read_set_only, " read_set_only"),
                    (st.read, " read"),
                ] {
                    if on {
                        t.push_str(word);
                    }
                }
                t
            })
            .collect();
        s.push_str(&format!(" stores({})", stores.join(", ")));
    }
    if !c.moves_or_writes.is_empty() {
        let bits: Vec<&str> = c
            .moves_or_writes
            .iter()
            .map(|&b| if b { "1" } else { "0" })
            .collect();
        s.push_str(&format!(" moves({})", bits.join(", ")));
    }
    let result = match &c.result {
        ResultPerm::None => "none".to_owned(),
        ResultPerm::Writable => "writable".to_owned(),
        ResultPerm::ReadOnly(r) => format!("readonly({})", reason_text(p, r)),
    };
    s.push_str(&format!(" result {result}"));
    s
}

fn reason_text(p: &Printer, r: &Reason) -> String {
    match r {
        Reason::Constant(path) => format!("constant {}", p.path(path)),
        Reason::Static(path) => format!("static {}", p.path(path)),
        Reason::ReadonlyResult(path) => format!("readonly_result {}", p.path(path)),
        Reason::ReadonlyField(path, f) => {
            let name = p
                .tcx
                .defs()
                .find(|(_, d)| &d.path == path)
                .and_then(|(d, _)| p.tcx.adt_of(d))
                .and_then(|a| p.tcx.adt(a).as_class())
                .and_then(|c| c.fields.get(f.index()))
                .map_or_else(|| f.index().to_string(), |fd| fd.name.to_string());
            format!("readonly_field {}.{name}", p.path(path))
        }
        Reason::StoredSource(n) => format!("stored {n}"),
        r => name_of(REASONS, r).to_owned(),
    }
}
