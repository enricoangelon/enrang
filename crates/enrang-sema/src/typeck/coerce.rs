//! The coercion table of SPEC 4.5 as `Adjust` chains (plan d.7; A:888; owner 3A).
//!
//! `coerce(e, to, site)` is the only place that pushes `Adjust`s. An expression's
//! `ty` stays its own type, the one before its adjusts, as the operand of each step
//! needs (a `FixedToSlice` reads the array's length from it); the adjusts take it to
//! the site's type, which the context knows. `null` is the exception, typed at the
//! nullable it meets (D11). A failed coercion reports once and leaves the
//! expression typed `Error`.
//!
//! At one site at most one chain, at the top only: step 1 at most one of C13
//! (`LiteralDescriptor`, a string literal at `&string`), C04 (`BoxDeref`, `&Box<T>`
//! to `&T`), C05 and C08 (`ReadThrough`, `ReadThroughNullable`, through a reference
//! to a Copy type), C21 (`Upcast`, `&D` or `Box<D>` to a base), C22 (4C's
//! `coerce_iface`), C11/C12/C14-C17 (4C's `coerce_fn`); step 2 C18 (`FixedToSlice`,
//! `ArrayToSlice`, to `&Slice<T>`); step 3 one wrap, C06 (`WrapNull`) or C07
//! (`WrapNullRef`). C09 (`NeverToAny`) stands alone; C10 is unification. C19
//! (`WrapOk`) is 4C's `check_return`. Nothing nests: `T[]` never becomes
//! `(T | null)[]`.
//!
//! The 4C hooks are asked with the site's whole type first and, when that is a
//! nullable and they decline, with its payload, whose result this file wraps:
//! `coerce_fn` before unification for a function value or a function-typed site
//! (C12 records `ArrowToClosure` even where the types agree), `coerce_iface` once
//! unification and the chains above have failed.
//!
//! Failures, in order: `&T[N]` or `&Slice<T>` where `&T[]` is expected, EN0401 `a
//! fixed array can't grow` or `a part of an array can't grow` with the helps of
//! A:888 and S:606; a value where a reference is expected, EN0612 with a fix-it
//! inserting `&` (G17, S:684); extra fields where the declared type fixes the
//! storage, EN0440 (S:601), and a by-value object parameter's value there, EN0440
//! `` `x` may have more fields than `{ name: string }` ``, or at another such
//! parameter EN0401 `` `b` may hold another class than `a` `` (S:601, T:861);
//! otherwise EN0401 `mismatched types: expected `E`, found `F``, labelled `this is
//! `F``, with a secondary at what set the expectation (`` `E` is required by this
//! annotation ``, G05; `by this parameter` and `by the return type`, plan choice),
//! and G05's note and `.toString()` help between numbers and strings, which
//! parenthesises an expression that is not atomic. EN0422 (`r = v` on a reference
//! variable) is the assignment's, in `expr.rs`. A coercion from or to `Error`
//! unifies the two, so a variable the rejected side meets is bound to `Error` and
//! reports nothing more.

use enrang_base::{Span, Symbol};
use enrang_diag::{Code, Diagnostic, Edit, Help};
use enrang_hir::{
    self as hir, Adjust, AdtKind, ConstValue, ExprKind, IntTy, LangItem, Res, Ty, TyKind, Vis,
};
use enrang_syntax::ast;

use crate::resolve::scope;
use crate::typeck::{FnCtxt, Site};

impl FnCtxt<'_, '_> {
    /// `e` coerced to `to` at `site` (S:656).
    pub(crate) fn coerce(&mut self, mut e: hir::Expr, to: Ty, site: Site) -> hir::Expr {
        let target = self.shallow(to);
        // A narrowed referent read where a value is wanted (C08 through a fact).
        if !matches!(
            self.sema.tcx.kind(target),
            TyKind::Ref(_) | TyKind::Infer(_)
        ) && self
            .nullable_payload(target)
            .is_none_or(|p| !matches!(self.sema.tcx.kind(self.shallow(p)), TyKind::Ref(_)))
            && matches!(self.sema.tcx.kind(self.shallow(e.ty)), TyKind::Ref(_))
        {
            e = self.read_narrowed(e);
        }
        let from = self.shallow(e.ty);
        if self.is_error(from) || self.is_error(target) {
            // `Error` binds the variables it meets, so one rejection reports once.
            let _ = self.unify(from, target);
            return e;
        }
        let payload = self.nullable_payload(target);
        if self.fn_like(&e, target) {
            if let Some(converted) = self.coerce_fn(e.clone(), to) {
                return converted;
            }
            if let Some(payload) = payload
                && let Some(converted) = self.coerce_fn(e.clone(), payload)
            {
                return self.wrap(converted, payload);
            }
        }
        if let Some(adjusts) = self.literal_descriptor(&e, target) {
            e.adjust.extend(adjusts);
            return e;
        }
        if self.unify(from, target) {
            return e;
        }
        if self.sema.tcx.kind(from) == TyKind::Never {
            e.adjust.push(Adjust::NeverToAny);
            return e;
        }
        if let Some(adjusts) = self.chain(from, target) {
            e.adjust.extend(adjusts);
            return e;
        }
        // C20 at a reference: `&p` meets `&{ name: string }` (or one `| null`) at
        // any site, the real shape kept behind the reference (S:601, S:678).
        if self.subset_ref(from, target) {
            return e;
        }
        if let Some(payload) = payload
            && self.subset_ref(from, payload)
        {
            return self.wrap(e, payload);
        }
        if let Some(converted) = self.coerce_iface(e.clone(), to, site) {
            return converted;
        }
        if let Some(payload) = payload
            && let Some(converted) = self.coerce_iface(e.clone(), payload, site)
        {
            return self.wrap(converted, payload);
        }
        self.coerce_failed(e, from, target, site)
    }

    /// C20 at a reference: whether `from` is `&X`, `X` an object type or a class
    /// instance, and `target` is `&{ .. }` whose every field `X` has, public, at a
    /// type that unifies (bound when it does). An implicit shape parameter's
    /// fields count the same way (S:601, "behind a reference").
    fn subset_ref(&mut self, from: Ty, target: Ty) -> bool {
        let tcx = &*self.sema.tcx;
        let (TyKind::Ref(f), TyKind::Ref(t)) = (tcx.kind(from), tcx.kind(target)) else {
            return false;
        };
        let (f, t) = (self.shallow(f), self.shallow(t));
        let TyKind::Object(want) = tcx.kind(t) else {
            return false;
        };
        let have: Vec<(Symbol, Ty)> = match tcx.kind(f) {
            TyKind::Object(shape) => tcx.shape(shape).fields.clone(),
            TyKind::Adt(adt, args) => match &tcx.adt(adt).kind {
                AdtKind::Class(class) => class
                    .fields
                    .iter()
                    .enumerate()
                    .filter(|(_, field)| field.vis == Vis::Public)
                    .map(|(i, field)| {
                        (
                            field.name,
                            tcx.field_ty(adt, None, hir::FieldIdx(i as u32), args),
                        )
                    })
                    .collect(),
                _ => return false,
            },
            TyKind::Param(_) => match self.implicit_shape(f) {
                Some(have) => have,
                None => return false,
            },
            _ => return false,
        };
        let want = tcx.shape(want).fields.clone();
        let snapshot = self.infer.vars.clone();
        let covers = want.iter().all(|(name, w)| {
            have.iter()
                .find(|(n, _)| n == name)
                .is_some_and(|(_, h)| self.unify(*h, *w))
        });
        if !covers {
            self.infer.vars = snapshot;
        }
        covers
    }

    /// The payload of a nullable `t`.
    fn nullable_payload(&self, t: Ty) -> Option<Ty> {
        match self.sema.tcx.kind(t) {
            TyKind::Nullable(inner) => Some(self.shallow(inner)),
            _ => None,
        }
    }

    /// `e`, already converted to `payload`, wrapped into `payload | null` (C06/C07).
    fn wrap(&self, mut e: hir::Expr, payload: Ty) -> hir::Expr {
        e.adjust.push(self.wrap_step(payload));
        e
    }

    fn wrap_step(&self, payload: Ty) -> Adjust {
        match self.sema.tcx.kind(payload) {
            TyKind::Ref(_) => Adjust::WrapNullRef,
            _ => Adjust::WrapNull,
        }
    }

    /// Whether 4C's function conversions may apply: a function-typed site, or an
    /// arrow or function value.
    fn fn_like(&self, e: &hir::Expr, target: Ty) -> bool {
        let fn_ty = |t: Ty| {
            matches!(
                self.sema.tcx.kind(t),
                TyKind::FnPtr(..) | TyKind::Closure(_)
            )
        };
        fn_ty(target)
            || self.nullable_payload(target).is_some_and(fn_ty)
            || matches!(
                e.kind,
                ExprKind::Arrow(_) | ExprKind::Const(ConstValue::FnAddr(_))
            )
            || fn_ty(self.shallow(e.ty))
    }

    /// C13: a string literal at `&string` (or `&string | null`) takes its static
    /// descriptor. The target is resolved deeply first, so a `&T | null` whose `T`
    /// is a variable already bound to `string` (`names.find(..)` on an inferred
    /// array, a generic `&T | null` result) counts as `&string | null`.
    fn literal_descriptor(&self, e: &hir::Expr, target: Ty) -> Option<Vec<Adjust>> {
        if !matches!(e.kind, ExprKind::Const(ConstValue::Str(_))) || !e.adjust.is_empty() {
            return None;
        }
        let target = self.resolve(target);
        let str_ref = self.sema.tcx.mk_ref(self.sema.tcx.common().str);
        if target == str_ref {
            return Some(vec![Adjust::LiteralDescriptor]);
        }
        match self.nullable_payload(target) {
            Some(payload) if payload == str_ref => {
                Some(vec![Adjust::LiteralDescriptor, Adjust::WrapNullRef])
            }
            _ => None,
        }
    }

    /// `e` with C13 applied when it is a string literal and `target` is `&string`
    /// or `&string | null`, and whether it was: for the places that take a string
    /// literal as a reference with no coercion site, the right side of `??` and the
    /// branches of a ternary or `match` with no expected type (S:827, S:962).
    pub(crate) fn str_literal_at(&mut self, mut e: hir::Expr, target: Ty) -> (hir::Expr, bool) {
        let target = self.shallow(target);
        match self.literal_descriptor(&e, target) {
            Some(adjusts) => {
                e.adjust.extend(adjusts);
                (e, true)
            }
            None => (e, false),
        }
    }

    /// The chain from `from` to `target`, when one exists: C08 alone, a wrap after
    /// an exact match or steps 1-2, or steps 1-2 alone.
    fn chain(&mut self, from: Ty, target: Ty) -> Option<Vec<Adjust>> {
        let tcx = &*self.sema.tcx;
        // C08: `&T | null` to `T | null` when `T` is Copy.
        if let (TyKind::Nullable(f), TyKind::Nullable(t)) = (tcx.kind(from), tcx.kind(target))
            && let TyKind::Ref(inner) = tcx.kind(self.shallow(f))
            && self.copy(inner)
            && self.unify(inner, t)
        {
            return Some(vec![Adjust::ReadThroughNullable]);
        }
        if let Some(payload) = self.nullable_payload(target) {
            let wrap = self.wrap_step(payload);
            if self.unify(from, payload) {
                return Some(vec![wrap]);
            }
            let mut steps = self.steps(from, payload)?;
            steps.push(wrap);
            return Some(steps);
        }
        self.steps(from, target)
    }

    /// Steps 1 and 2 from `from` to `target`: C18 alone, one of C04, C05, C21 alone,
    /// or one of them followed by C18.
    fn steps(&mut self, from: Ty, target: Ty) -> Option<Vec<Adjust>> {
        if let Some(step) = self.to_slice(from, target) {
            return Some(vec![step]);
        }
        for (step, mid) in self.first_steps(from) {
            if self.unify(mid, target) {
                return Some(vec![step]);
            }
            if let Some(slice) = self.to_slice(mid, target) {
                return Some(vec![step, slice]);
            }
        }
        None
    }

    /// C18: `&T[N]` or a whole `&T[]` to `&Slice<T>`.
    fn to_slice(&mut self, from: Ty, target: Ty) -> Option<Adjust> {
        let tcx = &*self.sema.tcx;
        let (TyKind::Ref(f), TyKind::Ref(t)) = (tcx.kind(from), tcx.kind(target)) else {
            return None;
        };
        let TyKind::Slice(elem) = tcx.kind(self.shallow(t)) else {
            return None;
        };
        let (step, from_elem) = match tcx.kind(self.shallow(f)) {
            TyKind::Fixed(e, _) => (Adjust::FixedToSlice, e),
            TyKind::Array(e) => (Adjust::ArrayToSlice, e),
            _ => return None,
        };
        self.unify(from_elem, elem).then_some(step)
    }

    /// The step-1 conversions `from` allows, each with the type it gives: C04
    /// `&Box<T>` to `&T`, C05 `&T` to a Copy `T`, C21 to each base class.
    fn first_steps(&self, from: Ty) -> Vec<(Adjust, Ty)> {
        let tcx = &*self.sema.tcx;
        let mut out = Vec::new();
        match tcx.kind(from) {
            TyKind::Ref(inner) => {
                let inner = self.shallow(inner);
                match tcx.kind(inner) {
                    TyKind::Boxed(boxed) => out.push((Adjust::BoxDeref, tcx.mk_ref(boxed))),
                    TyKind::Adt(adt, args) => {
                        for base in self.bases(adt, args) {
                            out.push((Adjust::Upcast, tcx.mk_ref(base)));
                        }
                    }
                    _ => {}
                }
                if self.copy(inner) {
                    out.push((Adjust::ReadThrough, inner));
                }
            }
            TyKind::Boxed(inner) => {
                if let TyKind::Adt(adt, args) = tcx.kind(self.shallow(inner)) {
                    for base in self.bases(adt, args) {
                        out.push((Adjust::Upcast, tcx.mk_box(base)));
                    }
                }
            }
            _ => {}
        }
        out
    }

    /// The base classes of class `adt` at `args`, nearest first.
    fn bases(&self, adt: hir::AdtId, args: hir::TyList) -> Vec<Ty> {
        let tcx = &*self.sema.tcx;
        let mut out = Vec::new();
        let mut current = (adt, args);
        let mut seen = vec![adt];
        while let Some((base, base_args)) = tcx.base_of(current.0, current.1) {
            if seen.contains(&base) {
                break;
            }
            seen.push(base);
            out.push(tcx.mk_adt(base, &tcx.list(base_args)));
            current = (base, base_args);
        }
        out
    }

    /// Whether the resolved `t` is Copy here.
    fn copy(&self, t: Ty) -> bool {
        let t = self.resolve(t);
        !self.sema.tcx.has_infer(t) && self.sema.tcx.is_copy(t, &self.env)
    }

    /// Whether `from` would reach `target` by unification or a chain; nothing
    /// changes.
    fn would_coerce(&mut self, from: Ty, target: Ty) -> bool {
        let snapshot = self.infer.vars.clone();
        let ok = self.unify(from, target) || self.chain(from, target).is_some();
        self.infer.vars = snapshot;
        ok
    }

    /// Reports why `e` (of type `from`) does not reach `target` at `site`.
    fn coerce_failed(&mut self, mut e: hir::Expr, from: Ty, target: Ty, site: Site) -> hir::Expr {
        let span = e.span;
        let (shown_from, shown_target) = (self.resolve(from), self.resolve(target));
        // A class whose base is unknown, or one converting to an interface its
        // `implements` failed: reported at the class (EN0302, EN0416).
        if self.sema.conversion_reported(shown_from, shown_target) {
            e.ty = self.error_ty();
            return e;
        }
        if !self.report_cannot_grow(&e, from, target)
            && !self.report_object_iface(&e, from, target)
            && !self.report_missing_ref(&e, from, target, site)
            && !self.report_extra_fields(&e, from, target)
            && !self.report_missing_optional(&e, from, target)
        {
            self.report_mismatch(&e, from, target, site);
        }
        e.ty = self.error_ty();
        let _ = span;
        e
    }

    /// S:629's EN0401 for an object type, or `&` to one, where an interface of
    /// methods, or `&` to one (one `| null` included), is expected.
    fn report_object_iface(&mut self, e: &hir::Expr, from: Ty, target: Ty) -> bool {
        let tcx = &*self.sema.tcx;
        let target = self.nullable_payload(target).unwrap_or(target);
        let (from_v, target_v) = match (tcx.kind(from), tcx.kind(target)) {
            (TyKind::Ref(f), TyKind::Ref(t)) => (self.shallow(f), self.shallow(t)),
            (TyKind::Ref(_), _) | (_, TyKind::Ref(_)) => return false,
            _ => (from, target),
        };
        let TyKind::Adt(iface, _) = tcx.kind(target_v) else {
            return false;
        };
        self.report_object_at_iface(e.span, from_v, iface)
    }

    /// EN0401 for `&T[N]` or `&Slice<T>` where `&T[]` is expected (A:888, S:606).
    fn report_cannot_grow(&mut self, e: &hir::Expr, from: Ty, target: Ty) -> bool {
        let tcx = &*self.sema.tcx;
        let target = self.nullable_payload(target).unwrap_or(target);
        let (TyKind::Ref(f), TyKind::Ref(t)) = (tcx.kind(from), tcx.kind(target)) else {
            return false;
        };
        let TyKind::Array(want) = tcx.kind(self.shallow(t)) else {
            return false;
        };
        let (fixed, elem) = match tcx.kind(self.shallow(f)) {
            TyKind::Fixed(elem, _) => (true, elem),
            TyKind::Slice(elem) => (false, elem),
            _ => return false,
        };
        let mut probe = self.infer.clone();
        if !super::infer::unify_in(tcx, &mut probe, elem, want) {
            return false;
        }
        let (sf, st) = (self.ty_str(from), self.ty_str(target));
        let elem_s = self.ty_str(want);
        let arg = self.snippet(e.span);
        let callee = self.arg_context(e.span);
        // S:1422: a part's label names the parameter that may grow it.
        let label = match &callee {
            Some(ArgContext {
                callee,
                param: Some(param),
                ..
            }) if !fixed => format!("`{callee}` takes `{param}: {st}`, a whole array it may grow"),
            _ => format!("expected `{st}`, found `{sf}`"),
        };
        let mut diag = Diagnostic::new(
            Code::EN0401,
            if fixed {
                "a fixed array can't grow"
            } else {
                "a part of an array can't grow"
            },
            e.span,
            label,
        );
        if fixed {
            let place = arg.trim_start_matches('&').trim().to_owned();
            let take = match &callee {
                Some(call) => match &call.param {
                    Some(param) => format!(
                        "if `{}` only reads or sets elements, take `{param}: &Slice<{elem_s}>`",
                        call.callee
                    ),
                    None => format!(
                        "if `{}` only reads or sets elements, take `&Slice<{elem_s}>`",
                        call.callee
                    ),
                },
                None => format!("if only elements are read or set, use `&Slice<{elem_s}>`"),
            };
            diag = diag.with_help(Help::text(format!(
                "{take}; to let it grow, make `{place}` {} `{elem_s}[]`",
                crate::classes::sig::article(&elem_s)
            )));
        } else {
            let whole = self.slice_receiver(e);
            match (&callee, whole) {
                (Some(call), Some(whole)) => {
                    diag = diag.with_help(Help::text(format!(
                        "pass the whole array: {}(&{whole})",
                        call.callee
                    )));
                }
                // A part that is a parameter: change that parameter's type (T:1044).
                (
                    Some(ArgContext {
                        callee,
                        param: Some(param),
                        ..
                    }),
                    None,
                ) if matches!(e.kind, hir::ExprKind::Local(l)
                    if matches!(self.locals[l].kind, hir::LocalKind::Param(_))) =>
                {
                    diag = diag.with_help(Help::text(format!(
                        "`{callee}` takes `{param}: &{elem_s}[]`, so take `{arg}: &{elem_s}[]` in place of `{sf}`"
                    )));
                }
                _ => {
                    diag = diag.with_help(Help::text(format!(
                        "take `&Slice<{elem_s}>` to accept a part, or pass a whole `&{elem_s}[]`"
                    )));
                }
            }
        }
        self.sema.emit(diag);
        true
    }

    /// For a `x.slice(..)` call on a whole-array place `x`, `x` as written.
    fn slice_receiver(&self, e: &hir::Expr) -> Option<String> {
        let ExprKind::Call {
            receiver: Some(receiver),
            ..
        } = &e.kind
        else {
            return None;
        };
        let text = self.snippet(e.span);
        let (base, rest) = text.split_once('.')?;
        if !rest.trim_start().starts_with("slice") {
            return None;
        }
        let whole = matches!(
            self.sema.tcx.kind(self.peel_one(receiver.ty)),
            TyKind::Array(_)
        );
        whole.then(|| base.trim().to_owned())
    }

    fn peel_one(&self, t: Ty) -> Ty {
        let t = self.shallow(t);
        match self.sema.tcx.kind(t) {
            TyKind::Ref(inner) => self.shallow(inner),
            _ => t,
        }
    }

    /// EN0612 for a value where a reference is expected, when `&` would make it fit
    /// (S:684, G17).
    fn report_missing_ref(&mut self, e: &hir::Expr, from: Ty, target: Ty, site: Site) -> bool {
        let tcx = &*self.sema.tcx;
        let reference = self.nullable_payload(target).unwrap_or(target);
        if !matches!(tcx.kind(reference), TyKind::Ref(_)) {
            return false;
        }
        let is_ref = |t: Ty| matches!(tcx.kind(t), TyKind::Ref(_) | TyKind::Raw(_));
        if is_ref(from)
            || self
                .nullable_payload(from)
                .is_some_and(|p| matches!(tcx.kind(p), TyKind::Ref(_)))
        {
            return false;
        }
        let borrowed = tcx.mk_ref(from);
        if !self.would_coerce(borrowed, target) {
            return false;
        }
        let (sf, st) = (self.ty_str(from), self.ty_str(target));
        let message = match (site, self.arg_context(e.span), self.name) {
            (Site::Arg, Some(call), _) => {
                format!("missing `&`: `{}` takes a reference", call.callee)
            }
            (Site::Return, _, Some(name)) if self.arrow_stack.is_empty() => {
                format!("missing `&`: `{name}` returns a reference")
            }
            _ => "missing `&`: a reference is expected here".to_owned(),
        };
        let text = self.snippet(e.span);
        // An operand that binds looser than prefix `&` is parenthesised, so the
        // fix-it borrows the whole of it (S:3.5): `&(a + "y")`.
        let loose = matches!(
            e.kind,
            ExprKind::Binary(..)
                | ExprKind::Logical(..)
                | ExprKind::Coalesce(..)
                | ExprKind::Ternary(..)
                | ExprKind::Cast(..)
                | ExprKind::Assign { .. }
                | ExprKind::Arrow(_)
                | ExprKind::Destructure { .. }
        ) && !text.starts_with('(');
        let (shown, edits) = match loose {
            true => (
                format!("&({text})"),
                vec![Edit::insert(e.span.lo, "&("), Edit::insert(e.span.hi, ")")],
            ),
            false => (format!("&{text}"), vec![Edit::insert(e.span.lo, "&")]),
        };
        self.sema.emit(
            Diagnostic::new(
                Code::EN0612,
                message,
                e.span,
                format!("expected `{st}`, found `{sf}`"),
            )
            .note(
                "a reference is only ever made by writing `&`; with no `&`, a value is moved or copied.",
            )
            .with_help(Help::machine(format!("write `{shown}`"), edits)),
        );
        true
    }

    /// EN0440 for an object or class value with more fields than the object type it
    /// meets, where the declared type fixes the storage (S:601, S:678); for a
    /// by-value object parameter, which stands for any value with those fields
    /// (D5), EN0440 `` `x` may have more fields than `{ name: string }` `` where its
    /// fields cover the target's, and EN0401 `` `b` may hold another class than `a` ``
    /// at another such parameter (S:601, T:861).
    fn report_extra_fields(&mut self, e: &hir::Expr, from: Ty, target: Ty) -> bool {
        let tcx = &*self.sema.tcx;
        // Behind a reference the real shape is kept (C20, `subset_ref`).
        let from_v = from;
        // A value meets `T | null` through C06 as it meets `T`: the payload is
        // the storage its declared type fixes (A:892).
        let target_v = match tcx.kind(target) {
            TyKind::Nullable(inner) if !matches!(tcx.kind(from_v), TyKind::Nullable(_)) => {
                self.shallow(inner)
            }
            _ => target,
        };
        if let Some(have) = self.implicit_shape(from_v) {
            return self.report_shape_param(e, &have, target_v);
        }
        let TyKind::Object(want) = tcx.kind(target_v) else {
            return false;
        };
        let have: Vec<(Symbol, Ty)> = match tcx.kind(from_v) {
            TyKind::Object(shape) => tcx.shape(shape).fields.clone(),
            TyKind::Adt(adt, args) => match &tcx.adt(adt).kind {
                AdtKind::Class(class) => class
                    .fields
                    .iter()
                    .enumerate()
                    .filter(|(_, f)| f.vis == Vis::Public)
                    .map(|(i, f)| {
                        (
                            f.name,
                            tcx.field_ty(adt, None, hir::FieldIdx(i as u32), args),
                        )
                    })
                    .collect(),
                _ => return false,
            },
            _ => return false,
        };
        let want = tcx.shape(want).fields.clone();
        let mut probe = self.infer.clone();
        let covers = want.iter().all(|(name, t)| {
            have.iter()
                .any(|(n, h)| n == name && super::infer::unify_in(tcx, &mut probe, *h, *t))
        });
        let extra = have
            .iter()
            .find(|(name, _)| !want.iter().any(|(n, _)| n == name));
        let (true, Some((extra, _))) = (covers, extra) else {
            return false;
        };
        let text = self.snippet(e.span);
        let st = self.ty_str(target_v);
        let smaller: Vec<String> = want
            .iter()
            .map(|(name, _)| format!("{name}: {text}.{name}"))
            .collect();
        let mut diag = Diagnostic::new(
            Code::EN0440,
            format!("`{text}` has a field `{extra}` that `{st}` does not have"),
            e.span,
            format!("this has more fields than `{st}`"),
        )
        .with_help(Help::text(format!(
            "build the smaller object: `{{ {} }}`",
            smaller.join(", ")
        )));
        // Only for the whole initialiser of an annotated variable (S:601): at a
        // field or an element the variable is another value.
        if let (Some(name), Some((init, _))) = (self.init_name, self.init_annotation)
            && init == e.span
        {
            diag = diag.with_help(Help::text(format!(
                "or keep a reference: `const {name} = &{text};`"
            )));
        }
        self.sema.emit(diag);
        true
    }

    /// The fields of the shape the implicit parameter `t` stands for (D5).
    fn implicit_shape(&self, t: Ty) -> Option<Vec<(Symbol, Ty)>> {
        let tcx = &*self.sema.tcx;
        match tcx.kind(t) {
            TyKind::Param(p) => match tcx.param(p).implicit {
                Some(hir::Implicit::Shape(shape)) => Some(tcx.shape(shape).fields.clone()),
                _ => None,
            },
            _ => None,
        }
    }

    /// The diagnostics of [`Self::report_extra_fields`] for a value of a by-value
    /// object parameter, whose fields are `have`, at `target`.
    fn report_shape_param(&mut self, e: &hir::Expr, have: &[(Symbol, Ty)], target: Ty) -> bool {
        let text = self.snippet(e.span);
        if self.implicit_shape(target).is_some() {
            let Some(other) = self
                .params
                .iter()
                .find(|&&p| self.shallow(self.locals[p].ty) == target)
                .and_then(|&p| self.locals[p].name)
            else {
                return false;
            };
            self.sema.emit(Diagnostic::new(
                Code::EN0401,
                format!("`{text}` may hold another class than `{other}`"),
                e.span,
                "each by-value object parameter stands for a type of its own",
            ));
            return true;
        }
        let tcx = &*self.sema.tcx;
        let TyKind::Object(want) = tcx.kind(target) else {
            return false;
        };
        let want = tcx.shape(want).fields.clone();
        let mut probe = self.infer.clone();
        let covers = want.iter().all(|(name, t)| {
            have.iter()
                .any(|(n, h)| n == name && super::infer::unify_in(tcx, &mut probe, *h, *t))
        });
        if !covers {
            return false;
        }
        let st = self.ty_str(target);
        let smaller: Vec<String> = want
            .iter()
            .map(|(name, _)| format!("{name}: {text}.{name}"))
            .collect();
        self.sema.emit(
            Diagnostic::new(
                Code::EN0440,
                format!("`{text}` may have more fields than `{st}`"),
                e.span,
                format!("`{text}` stands for any value with these fields"),
            )
            .with_help(Help::text(format!(
                "build the smaller object: `{{ {} }}`",
                smaller.join(", ")
            ))),
        );
        true
    }

    /// EN0401 `mismatched types` (G05).
    fn report_mismatch(&mut self, e: &hir::Expr, from: Ty, target: Ty, site: Site) {
        // `null` typed at a nullable hint is shown as written.
        let sf = match e.kind {
            ExprKind::NullLit => "null".to_owned(),
            _ => self.ty_str(from),
        };
        let st = self.ty_str(target);
        let mut diag = Diagnostic::new(
            Code::EN0401,
            format!("mismatched types: expected `{st}`, found `{sf}`"),
            e.span,
            format!("this is `{sf}`"),
        );
        if let Some((span, by)) = self.expectation_source(e.span, site) {
            diag = diag.with_secondary(span, format!("`{st}` is required by {by}"));
        }
        if sf == st {
            // Two types that print alike, such as classes of one name from two modules.
            diag = diag.note(format!(
                "these are two different types, both written `{st}` here"
            ));
        }
        if matches!(e.kind, ExprKind::ArrayBuild { .. })
            && matches!(self.sema.tcx.kind(target), TyKind::Fixed(..))
        {
            diag = diag.note("a spread builds a growable array, never a fixed one");
        }
        let display_from = self.resolve_display(from);
        let display_target = self.resolve_display(target);
        let tcx = &*self.sema.tcx;
        let is_number = |t: Ty| matches!(tcx.kind(t), TyKind::Int(_) | TyKind::Float(_));
        let is_text = |t: Ty| match tcx.kind(t) {
            TyKind::Str => true,
            TyKind::Ref(inner) => tcx.kind(inner) == TyKind::Str,
            _ => false,
        };
        if (is_text(display_target) && is_number(display_from))
            || (is_number(display_target) && is_text(display_from))
        {
            diag = diag.note("Enrang never converts between numbers and strings implicitly.");
            if tcx.kind(display_target) == TyKind::Str {
                // `a + 1` becomes `(a + 1).toString()`, never `a + 1.toString()`.
                let edits = match self.atomic_before_dot(e) {
                    true => vec![Edit::insert(e.span.hi, ".toString()")],
                    false => vec![
                        Edit::insert(e.span.lo, "("),
                        Edit::insert(e.span.hi, ").toString()"),
                    ],
                };
                diag = diag.with_help(Help::suggest("convert it explicitly", edits));
            }
        }
        self.sema.emit(diag);
    }

    /// Whether `.m()` written after `e` applies to all of `e`: a name, a field, an
    /// element, a call, an unsigned literal, or anything in parentheses.
    fn atomic_before_dot(&self, e: &hir::Expr) -> bool {
        let text = self.snippet(e.span);
        if text.starts_with('(') && text.ends_with(')') {
            return true;
        }
        match &e.kind {
            ExprKind::Const(_) => !text.starts_with('-'),
            ExprKind::Local(_)
            | ExprKind::Static(_)
            | ExprKind::Field(..)
            | ExprKind::Index(..)
            | ExprKind::Call { .. }
            | ExprKind::Template(_) => true,
            _ => false,
        }
    }

    fn resolve_display(&self, t: Ty) -> Ty {
        super::infer::display_in(self.sema.tcx, &self.infer, t)
    }

    /// The span and wording of what set the expected type at `site`: the
    /// annotation of the local being initialised, the parameter of the call, or the
    /// result type of the function.
    fn expectation_source(&self, span: Span, site: Site) -> Option<(Span, &'static str)> {
        match site {
            Site::Init => {
                let (init, annotation) = self.init_annotation?;
                contains(init, span).then_some((annotation, "this annotation"))
            }
            Site::Arg => {
                let call = self.arg_context(span)?;
                call.param_span.map(|p| (p, "this parameter"))
            }
            Site::Return => {
                if !self.arrow_stack.is_empty() {
                    return None;
                }
                self.ret_span.map(|r| (r, "the return type"))
            }
            Site::Field | Site::Assign | Site::Element | Site::Branch => None,
        }
    }

    /// The call whose argument `span` is, innermost first, with the callee's name
    /// and, when the callee is one known function, the parameter's name and span.
    pub(crate) fn arg_context(&self, span: Span) -> Option<ArgContext> {
        for frame in self.calls.iter().rev() {
            let Some(index) = frame.args.iter().position(|&a| contains(a, span)) else {
                continue;
            };
            let callee = frame.callee?;
            let mut context = ArgContext {
                callee,
                param: None,
                param_span: None,
            };
            if frame.callee_span.is_dummy() {
                return Some(context);
            }
            let ident = ast::Ident {
                name: callee,
                span: frame.callee_span,
            };
            let is_name = self.snippet(frame.callee_span) == callee.as_str();
            if is_name
                && self.scopes.lookup(callee).is_none()
                && let Res::Fns(defs) = scope::lookup_value(self.sema, self.at, ident)
                && defs.len() == 1
                && let Some(sig) = self.sema.tcx.sig_opt(defs[0])
                && let Some(param) = sig.params.get(index)
            {
                context.param = Some(param.name);
                context.param_span = (!param.span.is_dummy()).then_some(param.span);
            }
            return Some(context);
        }
        None
    }

    /// Whether `t` is an integer type, for the messages of literals.
    #[allow(dead_code)]
    pub(crate) fn int_of(&self, t: Ty) -> Option<IntTy> {
        match self.sema.tcx.kind(self.shallow(t)) {
            TyKind::Int(int) => Some(int),
            _ => None,
        }
    }

    /// Whether `t` is `Result<T, E>`.
    #[allow(dead_code)]
    pub(crate) fn is_result(&self, t: Ty) -> bool {
        match self.sema.tcx.kind(self.shallow(t)) {
            TyKind::Adt(adt, _) => self.sema.tcx.is_lang_adt(adt, LangItem::Result),
            _ => false,
        }
    }
}

/// The call an argument belongs to, as a coercion's message names it.
#[derive(Clone, Debug)]
pub(crate) struct ArgContext {
    pub callee: Symbol,
    pub param: Option<Symbol>,
    pub param_span: Option<Span>,
}

/// Whether `outer` contains `inner`.
fn contains(outer: Span, inner: Span) -> bool {
    !outer.is_dummy() && outer.lo <= inner.lo && inner.hi <= outer.hi
}
