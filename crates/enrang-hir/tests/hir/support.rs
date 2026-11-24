//! A small hand-built program for the cases: a `Tcx` for a target, and short ways to
//! define classes, enums, interfaces, methods and `extend` blocks with the public
//! `define_*` API, as a MIR fixture would with no front end.

use std::sync::Arc;

use enrang_base::{BitSet, FileId, SourceMap, Span, intern};
use enrang_hir::{
    AdtDecl, AdtId, AdtKind, Bound, ClassDef, ClassModifier, DefData, DefId, DefKind, EnumDef,
    ExtendDef, FieldDef, FnDecl, FnSig, Generics, GenericsId, IfaceDef, Implicit, ItemPath,
    LangItem, ModuleId, ModuleInfo, ModulePath, ParamId, ParamSig, Receiver, Tcx, Ty, TyKind,
    TyParamDef, VariantDef, Vis,
};
use enrang_target::{TargetOpts, resolve};

/// An enum case's field type: one of the enum's parameters, or a type.
#[derive(Copy, Clone)]
pub enum F {
    P(usize),
    T(Ty),
}

/// A program under construction.
pub struct World {
    pub tcx: Tcx,
    /// The module everything is defined in unless a case makes another.
    pub module: ModuleId,
    extend_count: usize,
}

impl World {
    /// An empty program for `x86_64-linux`.
    pub fn new() -> World {
        World::for_target("x86_64-linux")
    }

    pub fn for_target(target: &str) -> World {
        let (spec, _) = resolve(target, &TargetOpts::default()).expect("a target");
        let mut tcx = Tcx::new(Arc::new(spec), Arc::new(SourceMap::new()));
        let module = tcx.define_module(ModuleInfo::new(
            ModulePath::new("src/main"),
            false,
            FileId(0),
        ));
        World {
            tcx,
            module,
            extend_count: 0,
        }
    }

    /// Another module, which sees the first one's `extend` blocks only if `sees`.
    pub fn other_module(&mut self, path: &str, sees: &[ModuleId]) -> ModuleId {
        let m = self
            .tcx
            .define_module(ModuleInfo::new(ModulePath::new(path), false, FileId(0)));
        let count = self.tcx.module_count();
        let mut closure = BitSet::new(count);
        for &seen in sees {
            closure.insert(seen);
        }
        self.tcx.module_mut(m).closure = closure;
        m
    }

    fn path(&self, segments: &[&str]) -> ItemPath {
        let module = self.tcx.module(self.module).path;
        ItemPath {
            module,
            segments: segments.iter().map(|s| intern(s)).collect(),
            overload: None,
        }
    }

    fn data(&self, segments: &[&str], kind: DefKind, vis: Vis) -> DefData {
        let mut data = DefData::new(self.path(segments), kind, self.module, Span::DUMMY);
        data.vis = vis;
        data
    }

    /// Type parameters `names` owned by `owner`, as a generics list under `parent`.
    pub fn params(
        &mut self,
        owner: DefId,
        parent: Option<GenericsId>,
        names: &[&str],
    ) -> (GenericsId, Vec<ParamId>) {
        let params: Vec<ParamId> = names
            .iter()
            .enumerate()
            .map(|(i, name)| {
                self.tcx.define_param(TyParamDef {
                    name: intern(name),
                    owner,
                    index: i as u32,
                    bounds: Vec::new(),
                    implicit: None,
                    span: Span::DUMMY,
                })
            })
            .collect();
        let g = self
            .tcx
            .define_generics(Generics::new(parent, params.clone()));
        (g, params)
    }

    fn adt(&mut self, name: &str, kind: AdtKind, params: &[&str]) -> (AdtId, Vec<Ty>) {
        let empty = self.tcx.empty_generics();
        let adt = self.tcx.define_adt(AdtDecl {
            data: self.data(&[name], DefKind::TypeAlias, Vis::Public),
            name: intern(name),
            generics: empty,
            kind,
        });
        let def = self.tcx.adt(adt).def;
        let (g, ps) = self.params(def, None, params);
        self.tcx.adt_mut(adt).generics = g;
        let tys = ps.iter().map(|&p| self.tcx.mk_param(p)).collect();
        (adt, tys)
    }

    /// A class with type parameters `params`; fields and methods come later.
    pub fn class(
        &mut self,
        name: &str,
        modifier: ClassModifier,
        params: &[&str],
    ) -> (AdtId, Vec<Ty>) {
        self.adt(name, AdtKind::Class(ClassDef::new(modifier)), params)
    }

    /// Sets a class's base, flattening the base's fields in front.
    pub fn extends(&mut self, class: AdtId, base: Ty) {
        let TyKind::Adt(base_adt, base_args) = self.tcx.kind(base) else {
            panic!("a class base");
        };
        let params = self
            .tcx
            .generics(self.tcx.adt(base_adt).generics)
            .params
            .clone();
        let args = self.tcx.list(base_args);
        let inherited: Vec<FieldDef> = self
            .tcx
            .adt(base_adt)
            .as_class()
            .expect("a class")
            .fields
            .iter()
            .map(|f| FieldDef {
                ty: self.tcx.subst(f.ty, &params, &args),
                ..f.clone()
            })
            .collect();
        let AdtKind::Class(def) = &mut self.tcx.adt_mut(class).kind else {
            panic!("a class");
        };
        def.base = Some(base);
        def.own_from = inherited.len() as u32;
        let own = std::mem::take(&mut def.fields);
        def.fields = inherited;
        def.fields.extend(own);
    }

    /// Adds a field to a class.
    pub fn field(&mut self, class: AdtId, name: &str, ty: Ty, vis: Vis) {
        let mut field = FieldDef::new(intern(name), ty, class);
        field.vis = vis;
        let AdtKind::Class(def) = &mut self.tcx.adt_mut(class).kind else {
            panic!("a class");
        };
        def.fields.push(field);
    }

    pub fn set_copy(&mut self, class: AdtId) {
        if let AdtKind::Class(def) = &mut self.tcx.adt_mut(class).kind {
            def.copy = true;
        }
    }

    /// A destructor on a class.
    pub fn dtor(&mut self, class: AdtId) -> DefId {
        let name = self.tcx.adt(class).name.as_str().to_owned();
        let parent = self.tcx.adt(class).def;
        let generics = self.tcx.adt(class).generics;
        let void = self.tcx.common().void;
        let mut sig = FnSig::new(generics, Vec::new(), void);
        sig.receiver = Some(Receiver::Ref(enrang_hir::Mark::None));
        let mut decl = self.fn_decl(&[&name, "#dtor"], DefKind::Dtor, sig, Vis::Public);
        decl.parent = Some(parent);
        let d = self.tcx.define_fn(decl);
        if let AdtKind::Class(def) = &mut self.tcx.adt_mut(class).kind {
            def.dtor = Some(d);
        }
        d
    }

    fn fn_decl(&self, segments: &[&str], kind: DefKind, sig: FnSig, vis: Vis) -> FnDecl {
        FnDecl {
            path: self.path(segments),
            kind,
            module: self.module,
            vis,
            span: Span::DUMMY,
            parent: None,
            attrs: Default::default(),
            sig,
        }
    }

    /// A method of a class, enum or interface with these parameter types.
    pub fn method(&mut self, adt: AdtId, name: &str, params: &[Ty], ret: Ty, vis: Vis) -> DefId {
        let owner = self.tcx.adt(adt).name.as_str().to_owned();
        let parent_def = self.tcx.adt(adt).def;
        let parent_generics = self.tcx.adt(adt).generics;
        let generics = self
            .tcx
            .define_generics(Generics::new(Some(parent_generics), Vec::new()));
        let params = params
            .iter()
            .enumerate()
            .map(|(i, &ty)| ParamSig::new(intern(&format!("p{i}")), ty))
            .collect();
        let mut sig = FnSig::new(generics, params, ret);
        sig.receiver = Some(Receiver::Ref(enrang_hir::Mark::None));
        let mut decl = self.fn_decl(&[&owner, name], DefKind::Method, sig, vis);
        decl.parent = Some(parent_def);
        let m = self.tcx.define_fn(decl);
        match &mut self.tcx.adt_mut(adt).kind {
            AdtKind::Class(c) => c.methods.push(m),
            AdtKind::Enum(e) => e.methods.push(m),
            AdtKind::Interface(i) => i.methods.push(m),
        }
        m
    }

    /// An enum whose cases have these fields; `params` name its type parameters.
    pub fn enumeration(
        &mut self,
        name: &str,
        params: &[&str],
        cases: &[(&str, &[(&str, F)])],
    ) -> (AdtId, Vec<Ty>) {
        let (adt, tys) = self.adt(name, AdtKind::Enum(EnumDef::new(Vec::new())), params);
        let mut variants = Vec::new();
        for (case, fields) in cases {
            let mut variant = VariantDef::new(intern(case));
            for (field, ty) in fields.iter() {
                let ty = match *ty {
                    F::P(i) => tys[i],
                    F::T(ty) => ty,
                };
                variant.fields.push(FieldDef::new(intern(field), ty, adt));
            }
            variants.push(variant);
        }
        if let AdtKind::Enum(e) = &mut self.tcx.adt_mut(adt).kind {
            e.variants = variants;
        }
        (adt, tys)
    }

    /// A method interface, sealed when `sealed` names its lang item.
    pub fn interface(
        &mut self,
        name: &str,
        params: &[&str],
        sealed: Option<LangItem>,
    ) -> (AdtId, Vec<Ty>) {
        let placeholder = ParamId(u32::MAX);
        let (adt, tys) = self.adt(
            name,
            AdtKind::Interface(IfaceDef {
                methods: Vec::new(),
                sealed,
                self_param: placeholder,
            }),
            params,
        );
        let def = self.tcx.adt(adt).def;
        let self_param = self.tcx.define_param(TyParamDef {
            name: intern("Self"),
            owner: def,
            index: 0,
            bounds: Vec::new(),
            implicit: Some(Implicit::Interface(adt)),
            span: Span::DUMMY,
        });
        if let AdtKind::Interface(i) = &mut self.tcx.adt_mut(adt).kind {
            i.self_param = self_param;
        }
        (adt, tys)
    }

    /// Registers a definition as a lang item.
    pub fn lang(&mut self, item: LangItem, adt: AdtId) {
        let def = self.tcx.adt(adt).def;
        self.tcx.set_lang(item, def);
    }

    /// Bounds parameter `p` by the interface or class `adt`.
    pub fn bound(&mut self, p: ParamId, adt: AdtId, class: bool) {
        let args = self.tcx.empty_list();
        let b = self.tcx.define_bound(if class {
            Bound::Class { adt, args }
        } else {
            Bound::Iface { adt, args }
        });
        self.tcx.param_mut(p).bounds.push(b);
    }

    /// A type parameter bounded by `bounds`, owned by a fresh function.
    pub fn bounded_param(&mut self, name: &str, bounds: &[AdtId]) -> (ParamId, Ty) {
        let owner =
            self.tcx
                .define_def(self.data(&[&format!("f_{name}")], DefKind::Fn, Vis::Public));
        let (_, ps) = self.params(owner, None, &[name]);
        for &b in bounds {
            self.bound(ps[0], b, false);
        }
        (ps[0], self.tcx.mk_param(ps[0]))
    }

    /// An `extend` block in module `module` over `pattern`, built by `make` from the
    /// block's own parameters, with one method per name.
    pub fn extend_block(
        &mut self,
        module: ModuleId,
        params: &[(&str, &[AdtId])],
        make: &dyn Fn(&Tcx, &[Ty]) -> Ty,
        methods: &[&str],
    ) -> Vec<DefId> {
        let n = self.extend_count;
        self.extend_count += 1;
        let segment = format!("#extend{n}");
        let saved = self.module;
        self.module = module;
        let def = self
            .tcx
            .define_def(self.data(&[&segment], DefKind::Extend, Vis::Public));
        let names: Vec<&str> = params.iter().map(|(name, _)| *name).collect();
        let (g, ps) = self.params(def, None, &names);
        for (p, (_, bounds)) in ps.iter().zip(params) {
            for &b in bounds.iter() {
                self.bound(*p, b, false);
            }
        }
        let tys: Vec<Ty> = ps.iter().map(|&p| self.tcx.mk_param(p)).collect();
        let ty = make(&self.tcx, &tys);
        let void = self.tcx.common().void;
        let mut members = Vec::new();
        for name in methods {
            let generics = self.tcx.define_generics(Generics::new(Some(g), Vec::new()));
            let mut decl = self.fn_decl(
                &[&segment, name],
                DefKind::Method,
                FnSig::new(generics, Vec::new(), void),
                Vis::Public,
            );
            decl.parent = Some(def);
            members.push(self.tcx.define_fn(decl));
        }
        self.tcx.define_extend(ExtendDef {
            def,
            module,
            generics: g,
            ty,
            members: members.clone(),
        });
        self.module = saved;
        members
    }
}
