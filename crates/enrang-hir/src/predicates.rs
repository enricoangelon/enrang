//! Type predicates: SPEC 4.1's `V`, `R`, `B` and `S` (A:266-279), Copy (SPEC O4),
//! drop (ARCHITECTURE 2.6) and Clone (SPEC 4.4, coinductive).
//!
//! `V`: no `Ref`, no `Closure` and no borrowing class or tuple anywhere, except that
//! it does not descend into an `FnPtr` signature. An interface type `I` by itself is
//! never in `V`, while `Box<I>` is. A view `Slice<U>` is never in `V` either. A type
//! parameter ranges over `V`. A borrowing class has a field outside `V`; a borrowing
//! tuple has a part in `S` outside `V`. `S` is `V`, a borrowing class or tuple,
//! `Nullable` of one, or `Ref` or `Nullable(Ref)` of `V`, a view, a borrowing value or
//! an interface (`R`).
//!
//! An inference variable and `Error` count as `V`, so that one error is not reported
//! twice; neither leaves phase 2.

use crate::adt::AdtKind;
use crate::ids::{AdtId, DefId, ParamId, TyList};
use crate::lang::LangItem;
use crate::sig::{Bound, ParamEnv};
use crate::tcx::Tcx;
use crate::ty::{Ty, TyKind};

/// `V` of SPEC 4.1: every position check calls this or [`is_slot_type`].
pub fn is_value_type(tcx: &Tcx, ty: Ty) -> bool {
    tcx.is_value_type(ty)
}

/// `S` of SPEC 4.1: what a local, temporary, parameter or result may hold.
pub fn is_slot_type(tcx: &Tcx, ty: Ty) -> bool {
    tcx.is_slot_type(ty)
}

impl Tcx {
    /// `V` (A:266-272).
    pub fn is_value_type(&self, t: Ty) -> bool {
        self.value_rec(t, &mut Vec::new())
    }

    fn value_rec(&self, t: Ty, visiting: &mut Vec<AdtId>) -> bool {
        match self.kind(t) {
            TyKind::Bool
            | TyKind::Int(_)
            | TyKind::Float(_)
            | TyKind::Void
            | TyKind::Never
            | TyKind::Str
            | TyKind::Param(_)
            | TyKind::Infer(_)
            | TyKind::Error
            | TyKind::FnPtr(..) => true,
            TyKind::Ref(_) | TyKind::Closure(_) | TyKind::Slice(_) => false,
            TyKind::Array(e) | TyKind::Fixed(e, _) | TyKind::Nullable(e) | TyKind::Raw(e) => {
                self.value_rec(e, visiting)
            }
            TyKind::Boxed(e) => self.value_rec(e, visiting) || self.is_interface_ty(e),
            TyKind::Tuple(parts) => self
                .list(parts)
                .iter()
                .all(|&p| self.value_rec(p, visiting)),
            TyKind::Object(shape) => self
                .shape(shape)
                .fields
                .iter()
                .all(|&(_, f)| self.value_rec(f, visiting)),
            TyKind::Adt(adt, args) => {
                if !self.list(args).iter().all(|&a| self.value_rec(a, visiting)) {
                    return false;
                }
                if visiting.contains(&adt) {
                    return true;
                }
                visiting.push(adt);
                let ok = match &self.adt(adt).kind {
                    AdtKind::Class(class) => {
                        class.fields.iter().all(|f| self.value_rec(f.ty, visiting))
                    }
                    AdtKind::Enum(e) => e
                        .variants
                        .iter()
                        .flat_map(|v| v.fields.iter())
                        .all(|f| self.value_rec(f.ty, visiting)),
                    AdtKind::Interface(_) => false,
                };
                visiting.pop();
                ok
            }
        }
    }

    /// An interface type `I` (a method interface with arguments in `V`).
    pub fn is_interface_ty(&self, t: Ty) -> bool {
        match self.kind(t) {
            TyKind::Adt(adt, args) => {
                self.adt(adt).is_interface()
                    && self.list(args).iter().all(|&a| self.is_value_type(a))
            }
            _ => false,
        }
    }

    /// A class with a field outside `V`: a reference field or one holding a
    /// borrowing value (SPEC 4.3, 5.1).
    pub fn is_borrowing_class(&self, adt: AdtId) -> bool {
        match &self.adt(adt).kind {
            AdtKind::Class(class) => class.fields.iter().any(|f| !self.is_value_type(f.ty)),
            _ => false,
        }
    }

    /// `B`: a borrowing class (with arguments in `V`), or a tuple whose parts are in
    /// `S` and not all in `V`.
    pub fn is_borrowing(&self, t: Ty) -> bool {
        match self.kind(t) {
            TyKind::Adt(adt, args) => {
                self.adt(adt).is_class()
                    && self.list(args).iter().all(|&a| self.is_value_type(a))
                    && self.is_borrowing_class(adt)
            }
            TyKind::Tuple(parts) => {
                let parts = self.list(parts);
                parts.iter().all(|&p| self.is_slot_type(p))
                    && !parts.iter().all(|&p| self.is_value_type(p))
            }
            _ => false,
        }
    }

    /// `R`: `&V`, `&Slice<V>`, `&B`, `&(B | null)` or `&I` (SPEC 4.1).
    pub fn is_ref_type(&self, t: Ty) -> bool {
        match self.kind(t) {
            TyKind::Ref(inner) => match self.kind(inner) {
                TyKind::Slice(elem) => self.is_value_type(elem),
                TyKind::Nullable(b) if self.is_borrowing(b) => true,
                _ => {
                    self.is_value_type(inner)
                        || self.is_borrowing(inner)
                        || self.is_interface_ty(inner)
                }
            },
            _ => false,
        }
    }

    /// `S` (A:273): `V`, `R`, `R | null`, `B`, `B | null`.
    pub fn is_slot_type(&self, t: Ty) -> bool {
        if self.is_value_type(t) || self.is_ref_type(t) || self.is_borrowing(t) {
            return true;
        }
        match self.kind(t) {
            TyKind::Nullable(inner) => self.is_ref_type(inner) || self.is_borrowing(inner),
            _ => false,
        }
    }

    /// Whether type parameter `p` is bounded by the interface `item`, by its own
    /// bounds or by `env`.
    pub fn param_bounded_by(&self, p: ParamId, env: &ParamEnv, item: LangItem) -> bool {
        let Some(target) = self.lang_adt(item) else {
            return false;
        };
        self.param(p)
            .bounds
            .iter()
            .copied()
            .chain(env.bounds_of(p))
            .any(|b| matches!(self.bound(b), Bound::Iface { adt, .. } if *adt == target))
    }

    /// SPEC O4: numerics, `bool`, `void`, `never`, `&T`, raw pointers, `fn` pointers,
    /// payload-free enums, `T[N]` and `T | null` of Copy, objects and tuples of Copy
    /// parts, a class declaring `implements Copy` (never inherited), `Result` when
    /// both arguments are Copy, and a parameter bounded by `Copy`.
    pub fn is_copy(&self, t: Ty, env: &ParamEnv) -> bool {
        match self.kind(t) {
            TyKind::Bool
            | TyKind::Int(_)
            | TyKind::Float(_)
            | TyKind::Void
            | TyKind::Never
            | TyKind::Ref(_)
            | TyKind::Raw(_)
            | TyKind::FnPtr(..)
            | TyKind::Error => true,
            TyKind::Str
            | TyKind::Array(_)
            | TyKind::Slice(_)
            | TyKind::Boxed(_)
            | TyKind::Closure(_)
            | TyKind::Infer(_) => false,
            TyKind::Fixed(e, _) | TyKind::Nullable(e) => self.is_copy(e, env),
            TyKind::Tuple(parts) => self.list(parts).iter().all(|&p| self.is_copy(p, env)),
            TyKind::Object(shape) => self
                .shape(shape)
                .fields
                .iter()
                .all(|&(_, f)| self.is_copy(f, env)),
            TyKind::Param(p) => self.param_bounded_by(p, env, LangItem::Copy),
            TyKind::Adt(adt, args) => match &self.adt(adt).kind {
                AdtKind::Class(class) => class.copy,
                AdtKind::Enum(e) => {
                    if self.is_lang_adt(adt, LangItem::Result) {
                        self.list(args).iter().all(|&a| self.is_copy(a, env))
                    } else {
                        e.is_payload_free()
                    }
                }
                AdtKind::Interface(_) => false,
            },
        }
    }

    /// Whether dropping a `t` runs code: it owns memory or has a destructor
    /// (ARCHITECTURE 2.6). A type parameter may, so it does.
    pub fn needs_drop(&self, t: Ty) -> bool {
        self.drop_rec(t, &mut Vec::new())
    }

    fn drop_rec(&self, t: Ty, visiting: &mut Vec<Ty>) -> bool {
        match self.kind(t) {
            TyKind::Str | TyKind::Array(_) | TyKind::Boxed(_) | TyKind::Param(_) => true,
            TyKind::Bool
            | TyKind::Int(_)
            | TyKind::Float(_)
            | TyKind::Void
            | TyKind::Never
            | TyKind::Slice(_)
            | TyKind::Ref(_)
            | TyKind::Raw(_)
            | TyKind::FnPtr(..)
            | TyKind::Closure(_)
            | TyKind::Infer(_)
            | TyKind::Error => false,
            TyKind::Fixed(e, _) | TyKind::Nullable(e) => self.drop_rec(e, visiting),
            TyKind::Tuple(parts) => self.list(parts).iter().any(|&p| self.drop_rec(p, visiting)),
            TyKind::Object(shape) => self
                .shape(shape)
                .fields
                .iter()
                .any(|&(_, f)| self.drop_rec(f, visiting)),
            TyKind::Adt(adt, args) => {
                if visiting.contains(&t) {
                    return false;
                }
                visiting.push(t);
                let result = match &self.adt(adt).kind {
                    AdtKind::Class(_) => {
                        self.class_dtor(adt, args).is_some()
                            || self
                                .adt_field_tys(adt, args)
                                .into_iter()
                                .any(|f| self.drop_rec(f, visiting))
                    }
                    AdtKind::Enum(_) => self
                        .adt_field_tys(adt, args)
                        .into_iter()
                        .any(|f| self.drop_rec(f, visiting)),
                    AdtKind::Interface(_) => true,
                };
                visiting.pop();
                result
            }
        }
    }

    /// The destructor of a class or of the nearest base class that has one. The
    /// walk stops at a class seen before, so a cyclic chain (which sema reports and
    /// breaks) can never loop.
    pub fn class_dtor(&self, adt: AdtId, args: TyList) -> Option<DefId> {
        let (mut adt, mut args) = (adt, args);
        let mut seen = Vec::new();
        loop {
            if seen.contains(&adt) {
                return None;
            }
            seen.push(adt);
            let class = self.adt(adt).as_class()?;
            if let Some(dtor) = class.dtor {
                return Some(dtor);
            }
            (adt, args) = self.base_of(adt, args)?;
        }
    }

    /// A class's base, with its arguments at the class's arguments `args`.
    pub fn base_of(&self, adt: AdtId, args: TyList) -> Option<(AdtId, TyList)> {
        let class = self.adt(adt).as_class()?;
        let base = class.base?;
        let params = self.generics(self.adt(adt).generics).params.clone();
        let args = self.list(args);
        let base = self.subst(base, &params, &args);
        match self.kind(base) {
            TyKind::Adt(base_adt, base_args) => Some((base_adt, base_args)),
            _ => None,
        }
    }

    /// Every field type of a class (flattened) or of every enum case, at `args`.
    pub fn adt_field_tys(&self, adt: AdtId, args: TyList) -> Vec<Ty> {
        let def = self.adt(adt);
        let params = self.generics(def.generics).params.clone();
        let args = self.list(args);
        let declared: Vec<Ty> = match &def.kind {
            AdtKind::Class(class) => class.fields.iter().map(|f| f.ty).collect(),
            AdtKind::Enum(e) => e
                .variants
                .iter()
                .flat_map(|v| v.fields.iter().map(|f| f.ty))
                .collect(),
            AdtKind::Interface(_) => Vec::new(),
        };
        declared
            .into_iter()
            .map(|t| self.subst(t, &params, &args))
            .collect()
    }

    /// SPEC 4.4's `Clone` row, coinductively: every Copy type in `V`; `string`;
    /// `T[]`, `T | null`, `T[N]`, tuples, objects, `Result` and `Box` when their parts
    /// are; a parameter bounded by `Clone` or `Copy`; a class or enum with a written
    /// `clone`, which always wins, or else one synthesised memberwise when every
    /// field is Clone and there is no destructor and no raw pointer field.
    pub fn is_clone(&self, t: Ty, env: &ParamEnv) -> bool {
        self.clone_rec(t, env, &mut Vec::new())
    }

    fn clone_rec(&self, t: Ty, env: &ParamEnv, assumed: &mut Vec<Ty>) -> bool {
        if assumed.contains(&t) {
            return true;
        }
        match self.kind(t) {
            TyKind::Bool
            | TyKind::Int(_)
            | TyKind::Float(_)
            | TyKind::Void
            | TyKind::Never
            | TyKind::Raw(_)
            | TyKind::FnPtr(..)
            | TyKind::Str
            | TyKind::Error => true,
            TyKind::Ref(_) | TyKind::Closure(_) | TyKind::Slice(_) | TyKind::Infer(_) => false,
            TyKind::Array(e) | TyKind::Fixed(e, _) | TyKind::Nullable(e) | TyKind::Boxed(e) => {
                self.clone_rec(e, env, assumed)
            }
            TyKind::Tuple(parts) => self
                .list(parts)
                .iter()
                .all(|&p| self.clone_rec(p, env, assumed)),
            TyKind::Object(shape) => self
                .shape(shape)
                .fields
                .iter()
                .all(|&(_, f)| self.clone_rec(f, env, assumed)),
            TyKind::Param(p) => {
                self.param_bounded_by(p, env, LangItem::Clone)
                    || self.param_bounded_by(p, env, LangItem::Copy)
            }
            TyKind::Adt(adt, args) => {
                if self.is_lang_adt(adt, LangItem::Result) {
                    return self
                        .list(args)
                        .iter()
                        .all(|&a| self.clone_rec(a, env, assumed));
                }
                let clone = enrang_base::intern("clone");
                if self.find_method(adt, args, clone).is_some() {
                    return true;
                }
                let def = self.adt(adt);
                if def.is_interface() {
                    return false;
                }
                if self.is_copy(t, env) && self.is_value_type(t) {
                    return true;
                }
                if def.is_class() && self.class_dtor(adt, args).is_some() {
                    return false;
                }
                let fields = self.adt_field_tys(adt, args);
                if fields
                    .iter()
                    .any(|&f| matches!(self.kind(f), TyKind::Raw(_)))
                {
                    return false;
                }
                assumed.push(t);
                let ok = fields.iter().all(|&f| self.clone_rec(f, env, assumed));
                assumed.pop();
                ok
            }
        }
    }
}
