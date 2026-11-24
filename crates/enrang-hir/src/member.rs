//! Member lookup on one type (SPEC 4.3, A:760): own members, then inherited ones,
//! then the `extend` blocks of the looking module's import closure (A:886), then,
//! for `T[]` and `T[N]` only, the members of `Slice<T>` through C18 on the receiver
//! (S:1378, A:2014; plan doc gap G9: SPEC 4.3's lookup does not say so).
//!
//! This is lookup on one type `U`; stripping a reference, `Box` auto-deref,
//! narrowing and visibility (EN0308) are sema's (`typeck/member.rs`). The one
//! visibility rule applied here is that a base class's `private` members are never
//! found from a subclass (A:896). A destructor is never a member (SPEC 4.4).

use enrang_base::{Idx, Symbol};

use crate::adt::AdtKind;
use crate::body::Adjust;
use crate::def::Vis;
use crate::ids::{AdtId, BoundId, DefId, FieldIdx, ModuleId, ParamId, TyList};
use crate::lang::LangItem;
use crate::sig::{Bound, ParamEnv};
use crate::tcx::{ExtendDef, Tcx};
use crate::ty::{IntTy, Ty, TyKind};

/// What a lookup found.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemberRef {
    pub kind: MemberKind,
    /// `FixedToSlice` or `ArrayToSlice` when the member is `Slice<T>`'s, reached from
    /// a `T[N]` or a `T[]` (C18 on the receiver).
    pub via_slice: Option<Adjust>,
    /// The class, enum, interface or `extend` block of the first member found.
    pub owner: DefId,
    /// The owner's type arguments at this receiver: a class's arguments (a base's
    /// as the subclass instantiates it), or what an `extend` block's parameters
    /// bound to.
    pub args: TyList,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MemberKind {
    /// A field of a class, by its flattened index.
    Field { adt: AdtId, field: FieldIdx },
    /// One or more methods of one name: own, then inherited, then `extend`.
    Methods(Vec<FoundMethod>),
}

/// One method a lookup found, with the owner it was found on and that owner's type
/// arguments at the receiver.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct FoundMethod {
    pub def: DefId,
    pub owner: DefId,
    pub args: TyList,
}

impl Tcx {
    /// Lookup of `name` on `t` from module `from` (A:760).
    pub fn member(&self, t: Ty, name: Symbol, from: ModuleId) -> Option<MemberRef> {
        self.member_in(t, name, from, &ParamEnv::empty())
    }

    /// [`Tcx::member`] inside a body whose environment `env` adds bounds to type
    /// parameters (a method's `where` clause, S:323): a type parameter has the
    /// members of its declared bounds and of the bounds `env` adds.
    pub fn member_in(
        &self,
        t: Ty,
        name: Symbol,
        from: ModuleId,
        env: &ParamEnv,
    ) -> Option<MemberRef> {
        if let Some(found) = self.member_on(t, name, from, env) {
            return Some(found);
        }
        let (elem, adjust) = match self.kind(t) {
            TyKind::Array(elem) => (elem, Adjust::ArrayToSlice),
            TyKind::Fixed(elem, _) => (elem, Adjust::FixedToSlice),
            _ => return None,
        };
        let mut found = self.member_on(self.mk_slice(elem), name, from, env)?;
        found.via_slice = Some(adjust);
        Some(found)
    }

    fn member_on(&self, t: Ty, name: Symbol, from: ModuleId, env: &ParamEnv) -> Option<MemberRef> {
        let mut methods = Vec::new();
        match self.kind(t) {
            TyKind::Adt(adt, args) => {
                if let Some(field) = self.own_member(adt, args, name, &mut methods) {
                    return Some(field);
                }
            }
            TyKind::Str | TyKind::Slice(_) | TyKind::Array(_) | TyKind::Boxed(_) => {
                if let Some((adt, args)) = self.lang_class_of(t)
                    && let Some(field) = self.own_member(adt, args, name, &mut methods)
                {
                    return Some(field);
                }
            }
            TyKind::Param(p) => {
                if let Some(field) = self.bound_member(p, name, env, &mut methods) {
                    return Some(field);
                }
            }
            _ => {}
        }
        for ext in self.extends() {
            if !self.sees_extend(from, ext) {
                continue;
            }
            let Some(args) = self.match_extend(ext, t) else {
                continue;
            };
            for &m in &ext.members {
                if self.def(m).name() == Some(name) {
                    methods.push(FoundMethod {
                        def: m,
                        owner: ext.def,
                        args,
                    });
                }
            }
        }
        let first = *methods.first()?;
        Some(MemberRef {
            kind: MemberKind::Methods(methods),
            via_slice: None,
            owner: first.owner,
            args: first.args,
        })
    }

    /// The `@lang` class behind a normalised kind (A:758): `string`, `Slice<T>`,
    /// `T[]` or `Box<T>`, with its arguments; `None` for any other type, or before
    /// the library declares the class.
    pub fn lang_class_of(&self, t: Ty) -> Option<(AdtId, TyList)> {
        let (item, args) = match self.kind(t) {
            TyKind::Str => (LangItem::Str, Vec::new()),
            TyKind::Slice(e) => (LangItem::Slice, vec![e]),
            TyKind::Array(e) => (LangItem::Array, vec![e]),
            TyKind::Boxed(e) => (LangItem::Boxed, vec![e]),
            _ => return None,
        };
        Some((self.lang_adt(item)?, self.intern_list(&args)))
    }

    /// A class's field, or the methods of a class (own, then inherited), an enum or
    /// an interface, pushed onto `methods`.
    fn own_member(
        &self,
        adt: AdtId,
        args: TyList,
        name: Symbol,
        methods: &mut Vec<FoundMethod>,
    ) -> Option<MemberRef> {
        let def = self.adt(adt);
        match &def.kind {
            AdtKind::Class(class) => {
                for (i, field) in class.fields.iter().enumerate().rev() {
                    if field.name != name {
                        continue;
                    }
                    if field.declared_in != adt && field.vis == Vis::Private {
                        continue;
                    }
                    return Some(MemberRef {
                        kind: MemberKind::Field {
                            adt,
                            field: FieldIdx::new(i),
                        },
                        via_slice: None,
                        owner: def.def,
                        args,
                    });
                }
                self.class_methods(adt, args, name, true, methods);
            }
            AdtKind::Enum(e) => {
                for &m in &e.methods {
                    if self.def(m).name() == Some(name) {
                        methods.push(FoundMethod {
                            def: m,
                            owner: def.def,
                            args,
                        });
                    }
                }
            }
            AdtKind::Interface(i) => {
                for &m in &i.methods {
                    if self.def(m).name() == Some(name) {
                        methods.push(FoundMethod {
                            def: m,
                            owner: def.def,
                            args,
                        });
                    }
                }
            }
        }
        None
    }

    /// The methods named `name` of a class and its bases, skipping a base's
    /// `private` ones and any inherited method an own one overrides (same parameter
    /// types, and both `static` or neither: a `static` method never overrides and
    /// is never overridden, so a value receiver still finds the instance method
    /// beside a `static` one with its parameters).
    fn class_methods(
        &self,
        adt: AdtId,
        args: TyList,
        name: Symbol,
        own: bool,
        out: &mut Vec<FoundMethod>,
    ) {
        let def = self.adt(adt);
        let Some(class) = def.as_class() else {
            return;
        };
        for &m in &class.methods {
            let data = self.def(m);
            if data.name() != Some(name) || (!own && data.vis == Vis::Private) {
                continue;
            }
            let params = self.method_params_at(m, args);
            let is_static = |d: DefId| {
                self.sig_opt(d)
                    .is_some_and(|s| s.receiver == Some(crate::sig::Receiver::Static))
            };
            let overridden = out.iter().any(|found| {
                let other = self.method_params_at(found.def, found.args);
                is_static(found.def) == is_static(m)
                    && other.len() == params.len()
                    && other
                        .iter()
                        .zip(params.iter())
                        .all(|(&a, &b)| self.same_ignoring_rows(a, b))
            });
            if !overridden {
                out.push(FoundMethod {
                    def: m,
                    owner: def.def,
                    args,
                });
            }
        }
        if let Some((base, base_args)) = self.base_of(adt, args) {
            self.class_methods(base, base_args, name, false, out);
        }
    }

    /// A method's parameter types with its owner's parameters replaced by `args`.
    pub fn method_params_at(&self, m: DefId, args: TyList) -> Vec<Ty> {
        let Some(sig) = self.sig_opt(m) else {
            return Vec::new();
        };
        let owner_params = match self.generics(sig.generics).parent {
            Some(parent) => self.all_params(parent),
            None => Vec::new(),
        };
        let args = self.list(args);
        let n = owner_params.len().min(args.len());
        sig.params
            .iter()
            .map(|p| self.subst(p.ty, &owner_params[..n], &args[..n]))
            .collect()
    }

    /// The first method named `name` of a class (own or inherited), an enum or an
    /// interface.
    pub fn find_method(&self, adt: AdtId, args: TyList, name: Symbol) -> Option<DefId> {
        let mut methods = Vec::new();
        match self.own_member(adt, args, name, &mut methods) {
            Some(_) => None,
            None => methods.first().map(|m| m.def),
        }
    }

    /// Members a type parameter has through its bounds, its declared ones then the
    /// ones `env` adds: an interface bound's methods, a class bound's `public`
    /// fields and methods (SPEC 4.10).
    ///
    /// A method one bound declares with the same signature as a method already
    /// found on another, with `Self` standing for `p`, is that method, so a bound
    /// written twice, as a `where` clause restating a declared bound, adds nothing:
    /// the class bound's is kept, so a call dispatches through the class's table,
    /// as `T extends Animal & Speaker` with `speak()` in both (plan choice; the
    /// docs do not say how members shared by two bounds resolve).
    fn bound_member(
        &self,
        p: ParamId,
        name: Symbol,
        env: &ParamEnv,
        methods: &mut Vec<FoundMethod>,
    ) -> Option<MemberRef> {
        let mut bounds: Vec<BoundId> = self
            .param(p)
            .bounds
            .iter()
            .copied()
            .chain(env.bounds_of(p))
            .collect();
        // Class bounds first: a sort that keeps the written order otherwise.
        bounds.sort_by_key(|&b| !matches!(self.bound(b), Bound::Class { .. }));
        let me = self.mk_param(p);
        let start = methods.len();
        for b in bounds {
            let (adt, args) = (self.bound(b).adt(), self.bound(b).args());
            let mut found = Vec::new();
            let field = self.own_member(adt, args, name, &mut found);
            if matches!(self.bound(b), Bound::Class { .. }) {
                if let Some(field) = field {
                    if let MemberKind::Field { adt, field: idx } = field.kind
                        && self.field_def(adt, None, idx).vis == Vis::Public
                    {
                        return Some(field);
                    }
                    continue;
                }
                found.retain(|m| self.def(m.def).vis == Vis::Public);
            }
            for m in found {
                let shared = methods[start..]
                    .iter()
                    .any(|seen| self.same_bound_method(*seen, m, me));
                if !shared {
                    methods.push(m);
                }
            }
        }
        None
    }

    /// Whether two methods found on a type parameter's bounds have one signature:
    /// both `static` or neither, and the same parameter and result types, each
    /// owner's parameters replaced by its arguments and an interface's `Self` by
    /// `me`, the parameter.
    fn same_bound_method(&self, a: FoundMethod, b: FoundMethod, me: Ty) -> bool {
        let (Some(x), Some(y)) = (self.bound_view(a, me), self.bound_view(b, me)) else {
            return false;
        };
        x.0 == y.0
            && x.1.len() == y.1.len()
            && x.1
                .iter()
                .zip(y.1.iter())
                .all(|(&s, &t)| self.same_ignoring_rows(s, t))
            && self.same_ignoring_rows(x.2, y.2)
    }

    /// A bound's method as [`Tcx::same_bound_method`] compares it: whether it is
    /// `static`, its parameter types and its result.
    fn bound_view(&self, m: FoundMethod, me: Ty) -> Option<(bool, Vec<Ty>, Ty)> {
        let sig = self.sig_opt(m.def)?;
        let mut params = match self.generics(sig.generics).parent {
            Some(parent) => self.all_params(parent),
            None => Vec::new(),
        };
        let mut args = self.list(m.args).to_vec();
        let n = params.len().min(args.len());
        params.truncate(n);
        args.truncate(n);
        if let Some(adt) = self.adt_of(m.owner)
            && let Some(iface) = self.adt(adt).as_interface()
        {
            params.push(iface.self_param);
            args.push(me);
        }
        let is_static = sig.receiver == Some(crate::sig::Receiver::Static);
        let tys = sig
            .params
            .iter()
            .map(|p| self.subst(p.ty, &params, &args))
            .collect();
        Some((is_static, tys, self.subst(sig.ret, &params, &args)))
    }

    /// Whether module `from` sees the `extend` block `ext`: it is `from` itself or in
    /// its import closure.
    fn sees_extend(&self, from: ModuleId, ext: &ExtendDef) -> bool {
        if ext.module == from {
            return true;
        }
        let closure = &self.module(from).closure;
        ext.module.index() < closure.domain_size() && closure.contains(ext.module)
    }

    /// The bindings of `ext`'s parameters when its pattern matches `t`, with sealed
    /// bounds checked against the compiler's implementer table.
    pub fn match_extend(&self, ext: &ExtendDef, t: Ty) -> Option<TyList> {
        let params = self.all_params(ext.generics);
        let mut binding: Vec<Option<Ty>> = vec![None; params.len()];
        if !self.match_pattern(ext.ty, t, &params, &mut binding) {
            return None;
        }
        let args: Vec<Ty> = params
            .iter()
            .zip(binding)
            .map(|(&p, bound)| bound.unwrap_or_else(|| self.mk_param(p)))
            .collect();
        Some(self.intern_list(&args))
    }

    fn match_pattern(
        &self,
        pat: Ty,
        t: Ty,
        params: &[ParamId],
        binding: &mut [Option<Ty>],
    ) -> bool {
        if let TyKind::Param(p) = self.kind(pat)
            && let Some(i) = params.iter().position(|&q| q == p)
        {
            if let Some(bound) = binding[i] {
                return self.same_ignoring_rows(bound, t);
            }
            if !self.meets_sealed_bounds(p, t) {
                return false;
            }
            binding[i] = Some(t);
            return true;
        }
        if pat == t {
            return true;
        }
        let same_shape = match (self.kind(pat), self.kind(t)) {
            (TyKind::Fixed(_, n), TyKind::Fixed(_, m)) => n == m,
            (TyKind::Adt(a, _), TyKind::Adt(b, _)) => a == b,
            (TyKind::FnPtr(a, _), TyKind::FnPtr(b, _)) => a == b,
            (TyKind::Object(a), TyKind::Object(b)) => {
                let (a, b) = (self.shape(a), self.shape(b));
                a.fields.len() == b.fields.len()
                    && a.fields
                        .iter()
                        .zip(b.fields.iter())
                        .all(|(x, y)| x.0 == y.0)
            }
            (a, b) => std::mem::discriminant(&a) == std::mem::discriminant(&b),
        };
        if !same_shape {
            return false;
        }
        let (pats, tys) = (self.children(pat), self.children(t));
        if pats.is_empty() {
            return false;
        }
        pats.len() == tys.len()
            && pats
                .iter()
                .zip(tys.iter())
                .all(|(&p, &t)| self.match_pattern(p, t, params, binding))
    }

    /// Whether `t` meets every sealed bound of the pattern parameter `p`; other
    /// bounds are left to the call's bound check.
    fn meets_sealed_bounds(&self, p: ParamId, t: Ty) -> bool {
        self.param(p).bounds.iter().all(|&b| {
            let Bound::Iface { adt, .. } = self.bound(b) else {
                return true;
            };
            match self.adt(*adt).as_interface().and_then(|i| i.sealed) {
                Some(item) => self.sealed_implements(item, t),
                None => true,
            }
        })
    }

    /// The compiler's implementer table of a sealed interface (SPEC 4.4): `__Int`
    /// the ten integers, `__Float` `f32 f64`, `AtomicValue` `u8 u16 u32 usize i32
    /// bool` (S:1586), `AtomicBits` `u16 u32 usize i32` (S:1593), `VolatileValue`
    /// `u8 u16 u32 i8 i16 i32 usize isize bool`, raw pointers, and `u64 i64` on
    /// `x86_64-*` (S:1226). A type parameter meets one it is bounded by.
    pub fn sealed_implements(&self, item: LangItem, t: Ty) -> bool {
        use IntTy::*;
        match self.kind(t) {
            TyKind::Param(q) => self.lang_adt(item).is_some_and(|target| {
                self.param(q)
                    .bounds
                    .iter()
                    .any(|&b| matches!(self.bound(b), Bound::Iface { adt, .. } if *adt == target))
            }),
            TyKind::Error => true,
            kind => match item {
                LangItem::Int => matches!(kind, TyKind::Int(_)),
                LangItem::Float => matches!(kind, TyKind::Float(_)),
                LangItem::AtomicValue => matches!(
                    kind,
                    TyKind::Int(U8 | U16 | U32 | Usize | I32) | TyKind::Bool
                ),
                LangItem::AtomicBits => matches!(kind, TyKind::Int(U16 | U32 | Usize | I32)),
                LangItem::VolatileValue => match kind {
                    TyKind::Int(U8 | U16 | U32 | I8 | I16 | I32 | Usize | Isize)
                    | TyKind::Bool
                    | TyKind::Raw(_) => true,
                    TyKind::Int(U64 | I64) => self.target().name.starts_with("x86_64-"),
                    _ => false,
                },
                _ => false,
            },
        }
    }
}
