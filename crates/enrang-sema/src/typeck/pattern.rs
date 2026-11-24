//! Destructuring (plan d.11; SPEC 3.3, 5.6; owner 4B): object and tuple patterns,
//! nesting, with the binding mode set by the source (a reference gives references,
//! an owned value copies or moves each part); a pattern over an array at any depth
//! is EN1042; EN0506 for a nullable, enum or `Result` source (plan choice).
//!
//! Each level of a pattern takes apart one value. When the value is a reference,
//! every binding below is a reference into it (`&F`, or the field's own reference
//! when the field is one, O7); otherwise each part is copied or moved out (`F`), and
//! a part that is not Copy moving out of a path kills the facts on it (S:742). A
//! reference source is recorded as a `Binding` against the facts it reaches
//! (A:898). Object fields are found by name as `.` finds them, so an unknown field
//! is EN0303 and a hidden one EN0308; a method named there is EN0303 (plan choice).
//! A tuple pattern needs a tuple of as many parts, else EN0401 (plan choice); over
//! `T[]`, `T[N]` or a view it is EN1042 (S:996), whose message, note and help follow
//! SPEC 16. A value that may not match, a nullable or an enum, `Result` included, is
//! EN0506 at the pattern (plan choice, d.11).
//!
//! An assignment pattern (`[a, b] = xs`, `({ x, y } = p)`, D9) stores each part
//! into its target, a local or any place (D17's `Pat::Place`, S:418): a tuple
//! pattern's targets give the right side an expected tuple type (S:735), coerced
//! as a whole; an object pattern gives none, its fields are found by name on the
//! value as a declaration's are, and each field's type must be its target's
//! (EN0401 at the target otherwise, plan choice: a part takes no coercion). EN1042
//! comes from [`FnCtxt::check_assign_arrays`] before the right side is coerced.

use enrang_base::Span;
use enrang_diag::{Code, Diagnostic, Help};
use enrang_hir::{
    self as hir, BindingMode, ExprKind, FactPath, FieldIdx, LocalKind, MemberKind, Pat, PathStep,
    RecordKind, Ty, TyKind,
};
use enrang_syntax::ast;

use crate::typeck::infer::VarKind;
use crate::typeck::{Expect, FnCtxt, Site};

/// One part of a destructuring assignment's target, typed before its value.
enum AssignPart {
    /// A local or another place.
    Place(hir::Expr),
    Tuple(Vec<AssignPart>, Span),
    Object(Vec<(ast::Ident, AssignPart)>, Span),
    /// A part reported already (a default, EN1010; a spread; an unknown name).
    Error,
}

/// How the names of a pattern are declared.
#[derive(Copy, Clone, Debug)]
pub(crate) struct PatCx {
    /// `let` rather than `const`.
    pub mutable: bool,
    /// A `for...of` loop's binding, rather than a declaration's.
    pub for_loop: bool,
}

impl FnCtxt<'_, '_> {
    /// The pattern `b` binds from `init`, and its mode: `Ref` for a reference source,
    /// `Owned` for an owned place or rvalue (A:355, S:989-993).
    pub(crate) fn check_destructure(
        &mut self,
        b: &ast::Binding,
        init: hir::Expr,
    ) -> (Pat, BindingMode) {
        let mode = match self.sema.tcx.kind(self.shallow(init.ty)) {
            TyKind::Ref(_) => BindingMode::Ref,
            _ => BindingMode::Owned,
        };
        let place = self.source_place(&init);
        let cx = PatCx {
            mutable: false,
            for_loop: false,
        };
        let pat = self.pattern(b, init.ty, place, cx, Some(&init));
        (pat, mode)
    }

    /// The bindings of a `for...of` loop whose each turn gives a `ty`.
    pub(crate) fn bind_pattern(&mut self, b: &ast::Binding, ty: Ty, cx: PatCx) -> Pat {
        self.pattern(b, ty, None, cx, None)
    }

    /// `[a, b] = [b, a];` and `({ x, y } = p);` (D9, D17, S:418): the parts are
    /// typed as places first; a tuple pattern gives the value its expected type.
    pub(crate) fn check_destructure_assign(
        &mut self,
        target: &ast::Expr,
        value: &ast::Expr,
        span: Span,
    ) -> hir::Expr {
        let part = self.assign_part(target);
        let value = match &part {
            AssignPart::Tuple(..) => {
                let ty = self.part_expected(&part);
                let value = self.check_expr(value, Expect::Has(ty));
                if self.check_assign_arrays(target, value.ty) {
                    return self.error_expr(span);
                }
                if self.is_error(value.ty) {
                    return self.error_expr(span);
                }
                self.coerce(value, ty, Site::Assign)
            }
            _ => {
                let value = self.check_expr(value, Expect::None);
                if self.is_error(value.ty) {
                    return self.error_expr(span);
                }
                value
            }
        };
        let (value, ty) = self.object_source(value, &part);
        let Some(pat) = self.assign_pat(part, ty) else {
            return self.error_expr(span);
        };
        for place in pat.places() {
            self.kill_write(place);
        }
        self.kill_bound(&pat, span);
        let void = self.sema.tcx.common().void;
        self.mk_expr(
            void,
            span,
            ExprKind::Destructure {
                pat,
                value: Box::new(value),
            },
        )
    }

    /// The facts on each local a pattern assigns end (S:742).
    fn kill_bound(&mut self, pat: &Pat, span: Span) {
        match pat {
            Pat::Bind(local) => {
                let ty = self.locals[*local].ty;
                let place = self.mk_expr(ty, span, ExprKind::Local(*local));
                self.kill_write(&place);
            }
            Pat::Object(fields) => fields.iter().for_each(|(_, p)| self.kill_bound(p, span)),
            Pat::Tuple(parts) => parts.iter().for_each(|p| self.kill_bound(p, span)),
            Pat::Place(_) => {}
        }
    }

    /// An object pattern destructures the place a reference value points at, and
    /// a `Box`'s contents: the value as the pattern reads it, and its type.
    fn object_source(&mut self, value: hir::Expr, part: &AssignPart) -> (hir::Expr, Ty) {
        let ty = self.shallow(value.ty);
        if !matches!(part, AssignPart::Object(..)) {
            return (value, ty);
        }
        match self.sema.tcx.kind(ty) {
            TyKind::Ref(inner) => {
                let inner = self.shallow(inner);
                let span = value.span;
                let e = self.mk_expr(inner, span, ExprKind::Deref(Box::new(value)));
                (e, inner)
            }
            _ => (value, ty),
        }
    }

    /// The typed target `e` of a destructuring assignment.
    fn assign_part(&mut self, e: &ast::Expr) -> AssignPart {
        let e = crate::typeck::expr::strip_parens(e);
        match &e.kind {
            ast::ExprKind::Array(elems) => {
                let mut parts = Vec::new();
                let mut broken = false;
                for elem in elems {
                    match elem {
                        ast::ArrayElem::Item(item) => parts.push(self.assign_part(item)),
                        ast::ArrayElem::Spread { expr, .. } => {
                            let _ = self.check_expr(expr, Expect::None);
                            broken = true;
                        }
                    }
                }
                match broken {
                    true => AssignPart::Error,
                    false => AssignPart::Tuple(parts, e.span),
                }
            }
            ast::ExprKind::ObjectLit(fields) => {
                let parts = fields
                    .iter()
                    .map(|f| {
                        let part = match &f.value {
                            Some(v) => self.assign_part(v),
                            None => self.name_part(f.name),
                        };
                        (f.name, part)
                    })
                    .collect();
                AssignPart::Object(parts, e.span)
            }
            // A default (`a = 1`) is EN1010, reported by the parser.
            ast::ExprKind::Assign { .. } | ast::ExprKind::Error => AssignPart::Error,
            _ => {
                let place = self.check_place(e, Expect::None);
                match self.is_error(place.ty) {
                    true => AssignPart::Error,
                    false => AssignPart::Place(place),
                }
            }
        }
    }

    /// The target `{ x }` of an object pattern names: the place `x` is.
    fn name_part(&mut self, name: ast::Ident) -> AssignPart {
        // A synthesised name, as construct.rs synthesises reads.
        let e = ast::Expr {
            id: ast::NodeId(u32::MAX),
            kind: ast::ExprKind::Ident(name.name),
            span: name.span,
        };
        self.assign_part(&e)
    }

    /// The type a part gives the value: a place's own type; a tuple of its parts';
    /// for an object pattern (or a part reported), a variable the value decides.
    fn part_expected(&mut self, part: &AssignPart) -> Ty {
        match part {
            AssignPart::Place(e) => e.ty,
            AssignPart::Tuple(parts, _) => {
                let tys: Vec<Ty> = parts.iter().map(|p| self.part_expected(p)).collect();
                self.sema.tcx.mk_tuple(&tys)
            }
            AssignPart::Object(_, span) => self.new_var(VarKind::Any, *span, "this object pattern"),
            AssignPart::Error => self.error_ty(),
        }
    }

    /// The pattern of `part` over a value of type `ty`; `None` once a part is
    /// reported.
    fn assign_pat(&mut self, part: AssignPart, ty: Ty) -> Option<Pat> {
        let ty = self.shallow(ty);
        match part {
            AssignPart::Error => None,
            AssignPart::Place(e) => {
                if self.is_error(ty) {
                    return None;
                }
                if !self.unify(ty, e.ty) {
                    let (want, have) = (self.ty_str(e.ty), self.ty_str(ty));
                    self.sema.emit(Diagnostic::new(
                        Code::EN0401,
                        format!("mismatched types: expected `{want}`, found `{have}`"),
                        e.span,
                        format!("this part of the value is `{have}`"),
                    ));
                    return None;
                }
                Some(match (&e.kind, e.adjust.is_empty()) {
                    (ExprKind::Local(local), true) => Pat::Bind(*local),
                    _ => Pat::Place(Box::new(e)),
                })
            }
            AssignPart::Tuple(parts, span) => {
                let elems = match self.sema.tcx.kind(ty) {
                    TyKind::Tuple(elems) if self.sema.tcx.list(elems).len() == parts.len() => {
                        self.sema.tcx.list(elems).to_vec()
                    }
                    _ if self.is_error(ty) => return None,
                    _ => {
                        let shown = self.ty_str(ty);
                        self.sema.emit(Diagnostic::new(
                            Code::EN0401,
                            format!(
                                "mismatched types: expected a tuple of {}, found `{shown}`",
                                parts_count(parts.len())
                            ),
                            span,
                            format!("this pattern has {}", parts_count(parts.len())),
                        ));
                        return None;
                    }
                };
                let mut pats = Vec::new();
                let mut ok = true;
                for (part, elem) in parts.into_iter().zip(elems) {
                    match self.assign_pat(part, elem) {
                        Some(p) => pats.push(p),
                        None => ok = false,
                    }
                }
                ok.then_some(Pat::Tuple(pats))
            }
            AssignPart::Object(fields, span) => {
                if self.is_error(ty) || self.refutable(ty, span) {
                    return None;
                }
                let base = self.mk_expr(ty, span, ExprKind::Never);
                let mut out = Vec::new();
                let mut ok = true;
                for (name, part) in fields {
                    let Some((field, field_ty, _)) = self.pattern_field(&base, name) else {
                        ok = false;
                        continue;
                    };
                    match self.assign_pat(part, field_ty) {
                        Some(p) => out.push((field, p)),
                        None => ok = false,
                    }
                }
                ok.then_some(Pat::Object(out))
            }
        }
    }

    /// EN1042 for each tuple target of the assignment pattern `target` whose value,
    /// of type `ty`, is an array (S:996); whether one was reported.
    pub(crate) fn check_assign_arrays(&mut self, target: &ast::Expr, ty: Ty) -> bool {
        let ast::ExprKind::Array(elems) = &target.kind else {
            return false;
        };
        let t = self.shallow(ty);
        let inner = match self.sema.tcx.kind(t) {
            TyKind::Ref(inner) => self.shallow(inner),
            _ => t,
        };
        match self.sema.tcx.kind(inner) {
            TyKind::Array(_) | TyKind::Fixed(..) | TyKind::Slice(_) => {
                self.array_pattern(target.span, inner);
                true
            }
            TyKind::Tuple(parts) => {
                let parts = self.sema.tcx.list(parts);
                let mut reported = false;
                for (e, &part) in elems.iter().zip(parts.iter()) {
                    if let ast::ArrayElem::Item(e) = e {
                        let e = crate::typeck::expr::strip_parens(e);
                        reported |= self.check_assign_arrays(e, part);
                    }
                }
                reported
            }
            _ => false,
        }
    }

    /// The place `init` is read from when owned, or refers to when it is a
    /// reference, when that is a path.
    fn source_place(&self, init: &hir::Expr) -> Option<FactPath> {
        if let ExprKind::Borrow(inner) = &init.kind {
            return self.adjusted_path(inner);
        }
        let mut path = self.adjusted_path(init)?;
        if let TyKind::Ref(_) = self.sema.tcx.kind(self.shallow(init.ty)) {
            path.steps.push(PathStep::Deref);
        }
        Some(path)
    }

    /// One level of a pattern over a value of type `ty`, read from or referring to
    /// `place`; `origin` is the destructured expression, which records name.
    fn pattern(
        &mut self,
        b: &ast::Binding,
        ty: Ty,
        place: Option<FactPath>,
        cx: PatCx,
        origin: Option<&hir::Expr>,
    ) -> Pat {
        match b {
            ast::Binding::Name(name) => {
                self.move_part(ty, place.as_ref(), name.span);
                Pat::Bind(self.bind_name(name, ty, cx))
            }
            ast::Binding::Object { fields, span } => {
                let (by_ref, inner) = self.level(ty, place.as_ref(), origin);
                if self.is_error(inner) || self.refutable(inner, *span) {
                    return self.bind_errors(b, cx);
                }
                let base = self.mk_expr(ty, *span, ExprKind::Never);
                let mut out = Vec::new();
                for (name, sub) in fields {
                    let others: Vec<enrang_base::Symbol> = fields
                        .iter()
                        .map(|(n, _)| n.name)
                        .filter(|n| *n != name.name)
                        .collect();
                    let saved = std::mem::replace(&mut self.taken_names, others);
                    let found = self.pattern_field(&base, *name);
                    self.taken_names = saved;
                    let Some((field, field_ty, boxes)) = found else {
                        match sub {
                            Some(sub) => {
                                self.bind_errors(sub, cx);
                            }
                            None => {
                                let error = self.error_ty();
                                self.bind_name(name, error, cx);
                            }
                        }
                        continue;
                    };
                    let field_place = place.clone().map(|mut p| {
                        p.steps.extend(std::iter::repeat_n(PathStep::Deref, boxes));
                        p.steps.push(PathStep::Field(field));
                        p
                    });
                    let field_is_ref =
                        matches!(self.sema.tcx.kind(self.shallow(field_ty)), TyKind::Ref(_));
                    let part = match by_ref {
                        true => self.ref_to(field_ty),
                        false => field_ty,
                    };
                    // An owned pattern that binds a name to a reference field copies
                    // the reference: recorded against the facts below its referent,
                    // as `const r = h.r;` is (S:742).
                    let binds_name = matches!(sub, None | Some(ast::Binding::Name(_)));
                    if !by_ref
                        && field_is_ref
                        && binds_name
                        && let (Some(fp), Some(o)) = (&field_place, origin)
                    {
                        let mut referent = fp.clone();
                        referent.steps.push(PathStep::Deref);
                        self.record_binding(&referent, o);
                    }
                    let pat = match sub {
                        Some(sub) => {
                            let inner_place = match field_is_ref {
                                true => field_place.map(|mut p| {
                                    p.steps.push(PathStep::Deref);
                                    p
                                }),
                                false => field_place,
                            };
                            self.pattern(sub, part, inner_place, cx, origin)
                        }
                        None => {
                            if !by_ref {
                                self.move_part(part, field_place.as_ref(), name.span);
                            }
                            Pat::Bind(self.bind_name(name, part, cx))
                        }
                    };
                    out.push((field, pat));
                }
                Pat::Object(out)
            }
            ast::Binding::Tuple { elems, span } => {
                let (by_ref, inner) = self.level(ty, place.as_ref(), origin);
                if self.is_error(inner) || self.refutable(inner, *span) {
                    return self.bind_errors(b, cx);
                }
                let parts = match self.sema.tcx.kind(inner) {
                    TyKind::Array(_) | TyKind::Fixed(..) | TyKind::Slice(_) => {
                        self.array_pattern(*span, inner);
                        return self.bind_errors(b, cx);
                    }
                    TyKind::Tuple(parts) => self.sema.tcx.list(parts).to_vec(),
                    TyKind::Infer(_) if self.var_kind(inner) == Some(VarKind::Any) => {
                        let vars: Vec<Ty> = elems
                            .iter()
                            .map(|_| self.new_var(VarKind::Any, *span, "a part of this pattern"))
                            .collect();
                        let tuple = self.sema.tcx.mk_tuple(&vars);
                        self.unify(inner, tuple);
                        vars
                    }
                    _ => {
                        let shown = self.ty_str(inner);
                        self.sema.emit(Diagnostic::new(
                            Code::EN0401,
                            format!("mismatched types: expected a tuple, found `{shown}`"),
                            *span,
                            format!("this pattern takes a tuple apart, but the value is `{shown}`"),
                        ));
                        return self.bind_errors(b, cx);
                    }
                };
                if parts.len() != elems.len() {
                    let shown = self.ty_str(inner);
                    self.sema.emit(Diagnostic::new(
                        Code::EN0401,
                        format!(
                            "mismatched types: expected a tuple of {}, found `{shown}`",
                            parts_count(elems.len())
                        ),
                        *span,
                        format!("this pattern has {}", parts_count(elems.len())),
                    ));
                    return self.bind_errors(b, cx);
                }
                let pats = elems
                    .iter()
                    .zip(parts)
                    .map(|(e, part)| {
                        let part = match by_ref {
                            true => self.ref_to(part),
                            false => part,
                        };
                        // A tuple part is reached by an index: no path (S:739).
                        self.pattern(e, part, None, cx, origin)
                    })
                    .collect();
                Pat::Tuple(pats)
            }
        }
    }

    /// One level's value: whether it is a reference, and the type it reaches; a
    /// reference into a path is recorded as a `Binding` (A:898).
    fn level(
        &mut self,
        ty: Ty,
        place: Option<&FactPath>,
        origin: Option<&hir::Expr>,
    ) -> (bool, Ty) {
        let t = self.shallow(ty);
        match self.sema.tcx.kind(t) {
            TyKind::Ref(inner) => {
                if let (Some(place), Some(origin)) = (place, origin) {
                    self.record_binding(place, origin);
                }
                (true, self.shallow(inner))
            }
            _ => (false, t),
        }
    }

    /// Records `origin`, a destructured reference to `place`, against the facts below
    /// `place`.
    fn record_binding(&mut self, place: &FactPath, origin: &hir::Expr) {
        let mut at = origin.clone();
        at.adjust.clear();
        let facts: Vec<_> = self
            .flow
            .facts
            .iter()
            .filter(|(p, _)| place.is_proper_prefix_of(p))
            .map(|(_, id)| *id)
            .collect();
        for fact in facts {
            let known = self
                .records
                .iter()
                .any(|r| r.fact == fact && r.expr == at.id && r.kind == RecordKind::Binding);
            if !known {
                self.records.push(hir::NarrowRecord {
                    fact,
                    expr: at.id,
                    kind: RecordKind::Binding,
                    span: at.span,
                });
            }
        }
    }

    /// A part of type `ty` moving out of `place`: when it is not Copy, the facts on
    /// it die (S:742).
    fn move_part(&mut self, ty: Ty, place: Option<&FactPath>, span: Span) {
        let Some(place) = place else {
            return;
        };
        let t = self.resolve(ty);
        let tcx = &*self.sema.tcx;
        if tcx.has_infer(t) || tcx.is_copy(t, &self.env) {
            return;
        }
        let place = place.clone();
        self.kill_path(&place, span);
    }

    /// The field `name` of the value `base` stands for, as `.` finds it: its index,
    /// type, and the `Box`es looked through; `None` once reported.
    fn pattern_field(
        &mut self,
        base: &hir::Expr,
        name: ast::Ident,
    ) -> Option<(FieldIdx, Ty, usize)> {
        let member = self.lookup_on(base.clone(), name, false);
        let boxes = member
            .receiver
            .adjust
            .iter()
            .filter(|a| **a == hir::Adjust::BoxDeref)
            .count();
        if let Some((field, ty)) = member.object_field {
            return Some((field, ty, boxes));
        }
        let found = member.found?;
        match found.kind {
            MemberKind::Field { adt, field } => Some((
                field,
                self.sema.tcx.field_ty(adt, None, field, found.args),
                boxes,
            )),
            MemberKind::Methods(_) => {
                let shown = self.ty_str(member.at);
                self.sema.emit(Diagnostic::new(
                    Code::EN0303,
                    format!("`{shown}` has no field `{}`", name.name),
                    name.span,
                    format!("`{}` is a method, which a pattern can't take", name.name),
                ));
                None
            }
        }
    }

    /// EN0506 when a value of type `t` may not have the shape of a pattern at
    /// `span`: a nullable, or an enum, `Result` included (plan d.11).
    fn refutable(&mut self, t: Ty, span: Span) -> bool {
        let tcx = &*self.sema.tcx;
        let (head, label) = match tcx.kind(t) {
            TyKind::Nullable(_) => ("test it first", "it may be `null`"),
            TyKind::Adt(adt, _) if tcx.adt(adt).as_enum().is_some() => {
                ("match it first", "it may hold another case")
            }
            _ => return false,
        };
        let shown = self.ty_str(t);
        self.sema.emit(Diagnostic::new(
            Code::EN0506,
            format!(
                "this pattern can't destructure {} `{shown}`: {head}",
                crate::classes::sig::article(&shown)
            ),
            span,
            label,
        ));
        true
    }

    /// EN1042 at the tuple pattern `span` over the array type `t` (S:996, SPEC 16).
    pub(crate) fn array_pattern(&mut self, span: Span, t: Ty) {
        let shown = self.ty_str(t);
        // The note fits the kind of array (`t` is the array, past any `&`): a
        // fixed array's length is known.
        let note = match self.sema.tcx.kind(self.shallow(t)) {
            TyKind::Fixed(..) => {
                "only a tuple is destructured by position; a fixed array's elements are read by index"
            }
            _ => {
                "an array's length is known only when the program runs, so a pattern can't name its elements"
            }
        };
        self.sema.emit(
            Diagnostic::new(
                Code::EN1042,
                "array destructuring is not supported yet",
                span,
                format!("the value is `{shown}`, an array"),
            )
            .note(note)
            .with_help(Help::text("Index the array, or return a tuple")),
        );
    }

    /// `&t`, or `t` itself when it is already a reference (O7).
    fn ref_to(&self, t: Ty) -> Ty {
        match self.sema.tcx.kind(self.shallow(t)) {
            TyKind::Ref(_) => t,
            _ => self.sema.tcx.mk_ref(t),
        }
    }

    /// Declares the binding `name` of type `ty`.
    fn bind_name(&mut self, name: &ast::Ident, ty: Ty, cx: PatCx) -> hir::LocalId {
        let kind = match cx.for_loop {
            true => LocalKind::ForBinding,
            false => self
                .top_var(name.name, name.span)
                .map_or(LocalKind::PatBinding, LocalKind::TopVar),
        };
        self.declare(Some(name.name), ty, cx.mutable, kind, name.span)
    }

    /// Every name of `b`, typed `Error`, once its value was rejected.
    fn bind_errors(&mut self, b: &ast::Binding, cx: PatCx) -> Pat {
        let error = self.error_ty();
        match b {
            ast::Binding::Name(name) => Pat::Bind(self.bind_name(name, error, cx)),
            ast::Binding::Object { fields, .. } => {
                for (name, sub) in fields {
                    match sub {
                        Some(sub) => {
                            self.bind_errors(sub, cx);
                        }
                        None => {
                            self.bind_name(name, error, cx);
                        }
                    }
                }
                Pat::Object(Vec::new())
            }
            ast::Binding::Tuple { elems, .. } => {
                Pat::Tuple(elems.iter().map(|e| self.bind_errors(e, cx)).collect())
            }
        }
    }
}

/// `1 part`, `2 parts`.
fn parts_count(n: usize) -> String {
    match n {
        1 => "1 part".to_owned(),
        n => format!("{n} parts"),
    }
}
