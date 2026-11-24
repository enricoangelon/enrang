//! Member lookup with auto-deref, and member expressions (plan d.8; SPEC 4.3, 4.4,
//! 4.8; A:760, A:896; owner 3B).
//!
//! [`FnCtxt::lookup_member`] is SPEC 4.3's one rule for `.` and `?.`: the receiver
//! as its facts type it (`narrowed`, 4B), one `&` stripped as a `Deref` node, then
//! `Tcx::member` on that type, and on a miss through `Box<V>` the same on `V`, each
//! step a `BoxDeref` adjust on the receiver. An unnarrowed nullable has only the
//! members of the nullable type itself; a miss whose payload has the member is
//! EN0303 with a `?.` fix-it and a narrowing help, which also covers `a?.b.c`
//! (T:635). `?.` looks up on the payload and never short-circuits; on an owned
//! nullable rvalue it is EN0413 (S:750). `?.` on a `&(T | null)` strips the `&` as a
//! `Deref` first, and on a payload that is itself nullable (`n?.next` of a field
//! `next: Box<Node> | null` is `&(Box<Node> | null) | null`) the next `?.` looks
//! through both nulls (plan choice; S:750 is silent). An `OptionalChain` records
//! neither the payload's steps (`BoxDeref`s, C18) nor a call's receiver as passed,
//! which ARCHITECTURE's `OptChain` has no slot for: MIR re-derives them from the
//! base's type and the callee (plan doc gap G37). A member a lookup finds but the code here
//! may not see is EN0308 (A:896): a `private` one outside its class's body, a
//! `protected` one outside the class and its subclasses, and a base's `private`
//! member, which `Tcx::member` never finds from a subclass, is reported as such too,
//! unless the code is in that base's body, which sees it through a subclass value.
//! A class-bounded `T` sees the bound's `public` members only, and its others are
//! EN0308 (T:1014). `destructor` is never a member: EN0606 (S:648). A member access
//! on a still-unknown variable is EN0410 at once, and on an integer or float
//! variable it finds the members of `__Int` or `__Float` with `Self` set to that
//! variable (S:733). A method found on an interface type takes `Self` from 4C
//! (`self_of`). A payload narrowed to an enum case (`Fact::Case`, 4B) has that case's
//! fields; read outside its arm, such a field is EN0303 with a note naming the case.
//!
//! [`FnCtxt::check_member_expr`] types a member expression: a path through a type, a
//! namespace or a form (`Color.Red`, `i64.MAX`, `u.helper`) is `path.rs`'s
//! `static_member`; otherwise a field is `Field(receiver, idx)`, or with `?.` an
//! `OptionalChain` of type `&F | null` (S:750); a method read as a value is EN0441
//! for `length` (S:607, S:1383) and EN0303 for any other.

use std::collections::BTreeSet;
use std::sync::Arc;

use enrang_base::Idx;
use enrang_base::{BytePos, Span, Symbol, intern};
use enrang_diag::{Code, Diagnostic, Edit, Help, did_you_mean};
use enrang_hir::{
    self as hir, Adjust, AdtId, AdtKind, Bound, DefId, ExprKind, FieldIdx, FoundMethod, Implicit,
    LangItem, MemberKind, MemberRef, OptChain, OptMember, RecordKind, Shape, Ty, TyKind, Vis,
};
use enrang_syntax::ast::{self, Ident};

use crate::typeck::infer::VarKind;
use crate::typeck::{Expect, FnCtxt, ValueUse};

/// What a lookup found: the member, the receiver with its auto-deref adjusts, and
/// the receiver type it was found at.
///
/// `receiver` has type `at` once its adjusts apply: the base as its facts type it,
/// with one `&` stripped as a `Deref` node and each `Box` step a `BoxDeref`; for
/// `?.` it is the nullable base itself, and `at` the payload's type. A member found
/// on an interface type has `at` set to the class `Self` stands for (`self_of`).
#[derive(Clone, Debug)]
pub(crate) struct Member {
    pub found: Option<MemberRef>,
    pub receiver: hir::Expr,
    pub at: Ty,
    /// A field of an anonymous object type, or of the shape an implicit parameter
    /// stands for (D5), by its place in the shape, with its type: no `MemberRef`
    /// names one.
    pub object_field: Option<(FieldIdx, Ty)>,
    /// `found` is a member the compiler synthesises (D12): `clone` of a Clone type
    /// with no written `clone`, or `equals` of an `implements Eq` class with no
    /// written `equals`, found as the prelude interface's method with `Self` at
    /// `at`; a call to it is `Callee::Form(FormKind::Clone)` or `Equals`.
    pub synthesised: bool,
}

impl Member {
    fn new(found: Option<MemberRef>, receiver: hir::Expr, at: Ty) -> Member {
        Member {
            found,
            receiver,
            at,
            object_field: None,
            synthesised: false,
        }
    }

    fn synthesised(found: MemberRef, receiver: hir::Expr, at: Ty) -> Member {
        Member {
            synthesised: true,
            ..Member::new(Some(found), receiver, at)
        }
    }
}

/// One step of a lookup on one type.
enum Step {
    Found(MemberRef),
    Object(FieldIdx, Ty),
    Missed,
}

impl FnCtxt<'_, '_> {
    /// `base.name` or `base?.name`: SPEC 4.3's lookup, reporting a miss (EN0303,
    /// EN0308, EN0410, EN0413, EN0606). A found member the code here may not see is
    /// reported and still returned, so typing goes on.
    pub(crate) fn lookup_member(&mut self, base: hir::Expr, name: Ident, optional: bool) -> Member {
        let receiver = self.narrowed(base);
        self.lookup_on(receiver, name, optional)
    }

    /// [`Self::lookup_member`] on a receiver its facts already typed (`narrowed`),
    /// which `check_call` commits again after the arguments (A:898).
    pub(crate) fn lookup_on(&mut self, receiver: hir::Expr, name: Ident, optional: bool) -> Member {
        self.lookup_with(receiver, name, optional, false)
    }

    /// [`Self::lookup_on`]; `calling` for a method call, where only `static` methods
    /// found are left unchecked for visibility, since the call reports them as
    /// called through a value (EN0303), one diagnostic for one misuse.
    pub(crate) fn lookup_with(
        &mut self,
        receiver: hir::Expr,
        name: Ident,
        optional: bool,
        calling: bool,
    ) -> Member {
        // A by-value interface value produced here, as `b.unbox()` on a
        // `Box<Speaker>` gives, has no known class or size, even as a receiver
        // (S:631). A place of that type was reported at its declaration.
        if self.report_iface_rvalue(&receiver) {
            let error = self.error_ty();
            let mut receiver = receiver;
            receiver.ty = error;
            return Member::new(None, receiver, error);
        }
        // A method call makes a reference to its receiver, which is recorded
        // (S:742); a field read projects and makes none (4B).
        let original = receiver.clone();
        let member = self.lookup_found(receiver, name, optional, calling);
        if let Some(found) = &member.found
            && matches!(found.kind, MemberKind::Methods(_))
        {
            self.record_ref(&original, RecordKind::Receiver);
        }
        member
    }

    /// `e`, or, when it is a by-value interface value that is not a place, as
    /// `b.unbox()` on a `Box<Speaker>` gives, EN1006 and `e` typed `Error`: its class
    /// and so its size are unknown wherever it is used (S:631), as a receiver, a
    /// printed value or a template hole. A place of that type was reported at its
    /// declaration (positions).
    pub(crate) fn iface_rvalue(&mut self, mut e: hir::Expr) -> hir::Expr {
        if self.report_iface_rvalue(&e) {
            e.ty = self.error_ty();
        }
        e
    }

    /// EN1006 for `e` as [`Self::iface_rvalue`] reports it; whether it did.
    fn report_iface_rvalue(&mut self, e: &hir::Expr) -> bool {
        let t = self.resolve(e.ty);
        let unsized_value = !is_place(e) && !self.is_error(t) && self.sema.tcx.is_interface_ty(t);
        if unsized_value {
            self.report_iface_value(e);
        }
        unsized_value
    }

    /// [`Self::lookup_with`] before its receiver is recorded.
    fn lookup_found(
        &mut self,
        receiver: hir::Expr,
        name: Ident,
        optional: bool,
        calling: bool,
    ) -> Member {
        let error = self.error_ty();
        if name.name.as_str() == "destructor" {
            self.destructor_named(name.span, receiver.span);
            return Member::new(None, receiver, error);
        }
        if optional {
            // `?.` looks up on the payload of a nullable, reached through one `&` (a
            // `Deref` node) as `.` reaches its type (S:607), and through a variable
            // a later assignment decided (S:733).
            let t = self.resolved(receiver.ty);
            match self.sema.tcx.kind(t) {
                TyKind::Nullable(payload) => {
                    return self.lookup_optional(receiver, payload, name, calling);
                }
                TyKind::Ref(inner) => {
                    let inner = self.resolved(inner);
                    if let TyKind::Nullable(payload) = self.sema.tcx.kind(inner) {
                        let span = receiver.span;
                        let deref = self.mk_expr(inner, span, ExprKind::Deref(Box::new(receiver)));
                        return self.lookup_optional(deref, payload, name, calling);
                    }
                }
                _ => {}
            }
        }
        let (narrowed, case) = match &receiver.kind {
            ExprKind::NarrowedPayload(place, variant, _) => {
                (Some((**place).clone()), self.case_of(place, *variant))
            }
            _ => (None, None),
        };
        let mut receiver = receiver;
        let mut at = self.resolved(receiver.ty);
        if let TyKind::Ref(inner) = self.sema.tcx.kind(at) {
            let span = receiver.span;
            receiver = self.mk_expr(inner, span, ExprKind::Deref(Box::new(receiver)));
            at = self.resolved(inner);
        }
        match self.sema.tcx.kind(at) {
            TyKind::Error => return Member::new(None, receiver, at),
            TyKind::Infer(_) => return self.lookup_on_var(receiver, at, name),
            TyKind::Nullable(payload) => {
                let found = self.sema.tcx.member(at, name.name, self.at.module);
                if found.is_none() {
                    self.nullable_miss(&receiver, at, payload, name);
                }
                return Member::new(found, receiver, at);
            }
            _ => {}
        }
        if let Some((adt, variant, args)) = case
            && let Some(e) = self.sema.tcx.adt(adt).as_enum()
            && let Some(i) = e.variants[variant.index()]
                .fields
                .iter()
                .position(|f| f.name == name.name)
        {
            let field = FieldIdx::new(i);
            let ty = self.sema.tcx.field_ty(adt, Some(variant), field, args);
            let mut member = Member::new(None, receiver, at);
            member.object_field = Some((field, ty));
            return member;
        }
        loop {
            match self.step(at, name, calling) {
                Step::Found(found) => {
                    let at = self.self_at(&receiver, at);
                    return Member::new(Some(found), receiver, at);
                }
                Step::Object(field, ty) => {
                    let mut member = Member::new(None, receiver, at);
                    member.object_field = Some((field, ty));
                    return member;
                }
                Step::Missed => {}
            }
            match self.sema.tcx.kind(at) {
                TyKind::Boxed(inner) => {
                    receiver.adjust.push(Adjust::BoxDeref);
                    // An unannotated `new Box(x)` is `Box<?T>` with `?T` bound.
                    at = self.resolved(inner);
                }
                _ => break,
            }
        }
        if let Some(found) = self.synthesised_member(at, name) {
            return Member::synthesised(found, receiver, at);
        }
        if let Some(place) = narrowed
            && let Some(member) = self.on_nullable(place, name)
        {
            return member;
        }
        if let Some(found) = self.private_of_base(at, name) {
            return Member::new(Some(found), receiver, at);
        }
        if let Some(case) = self.case_with_field(at, name.name)
            && let Some(kill) = self.killed_case(&receiver)
        {
            // The arm's case fact was killed: the lost narrowing is the cause.
            let shown = self.ty_str(at);
            let place = self.source(receiver.span);
            self.sema.emit(
                Diagnostic::new(
                    Code::EN0303,
                    format!("`{shown}` has no member `{}`", name.name),
                    name.span,
                    "no such member",
                )
                .with_secondary(
                    kill,
                    format!("`{place}` is assigned here, so its case is no longer known"),
                )
                .note(format!(
                    "`{}` is a field of the case `{case}`, and the assignment ends what the `match` arm knew about `{place}`",
                    name.name
                )),
            );
            return Member::new(None, receiver, at);
        }
        self.member_miss(at, name);
        Member::new(None, receiver, at)
    }

    /// Where the case fact on the path `receiver` is was killed, if one was.
    fn killed_case(&self, receiver: &hir::Expr) -> Option<Span> {
        let path = self.adjusted_path(receiver)?;
        self.flow.kills.iter().find_map(|(&id, &span)| {
            let info = &self.facts[id];
            (info.path == path && matches!(info.fact, hir::Fact::Case(_))).then_some(span)
        })
    }

    /// A member the compiler synthesises on demand, which lookup on `at` missed
    /// (D12): `clone` of a type that satisfies `Clone` with no `clone` written or
    /// declared (S:639: a Copy type, `T[N]`, a tuple, an anonymous object type,
    /// `Result`, a class or enum cloned memberwise), and `equals` of a class that
    /// writes `implements Eq` with no `equals` (S:640). It is found as the prelude
    /// interface's method, `clone(): Self` or `equals(other: &Self): bool`, which a
    /// call takes `Self` of from the receiver (`Member.at`). An integer or float
    /// variable counts as its default type here.
    fn synthesised_member(&self, at: Ty, name: Ident) -> Option<MemberRef> {
        let tcx = &*self.sema.tcx;
        let shown = crate::typeck::infer::display_in(tcx, &self.infer, at);
        let item = match name.name.as_str() {
            "clone" if tcx.is_clone(shown, &self.env) => LangItem::Clone,
            "equals" => {
                let eq = tcx.lang_adt(LangItem::Eq)?;
                if !crate::classes::satisfy::synthesised_eq(tcx, shown, eq) {
                    return None;
                }
                LangItem::Eq
            }
            _ => return None,
        };
        if matches!(tcx.kind(shown), TyKind::Error | TyKind::Infer(_)) {
            return None;
        }
        let adt = tcx.lang_adt(item)?;
        let def = tcx
            .adt(adt)
            .as_interface()?
            .methods
            .iter()
            .copied()
            .find(|&m| tcx.def(m).name() == Some(name.name))?;
        let owner = tcx.adt(adt).def;
        let args = tcx.empty_list();
        Some(MemberRef {
            kind: MemberKind::Methods(vec![FoundMethod { def, owner, args }]),
            via_slice: None,
            owner,
            args,
        })
    }

    /// A base class's `private` member named `name`, which `Tcx::member` never finds
    /// from the subclass `at` (A:896), when the code here is in that base's body and
    /// so sees it (S:321): a field by its flattened index in `at`, or the base's
    /// methods of that name at the arguments `at` gives the base.
    fn private_of_base(&self, at: Ty, name: Ident) -> Option<MemberRef> {
        let tcx = &*self.sema.tcx;
        let TyKind::Adt(adt, args) = tcx.kind(at) else {
            return None;
        };
        let class = tcx.adt(adt).as_class()?;
        for (i, field) in class.fields.iter().enumerate().rev() {
            if field.name == name.name
                && field.declared_in != adt
                && field.vis == Vis::Private
                && self.sees(Vis::Private, field.declared_in)
            {
                return Some(MemberRef {
                    kind: MemberKind::Field {
                        adt,
                        field: FieldIdx::new(i),
                    },
                    via_slice: None,
                    owner: tcx.adt(adt).def,
                    args,
                });
            }
        }
        let mut current = tcx.base_of(adt, args);
        let mut steps = 0;
        while let Some((base, base_args)) = current {
            steps += 1;
            if steps > tcx.adts().count() {
                return None;
            }
            let def = tcx.adt(base);
            let class = def.as_class()?;
            if self.sees(Vis::Private, base) {
                let methods: Vec<FoundMethod> = class
                    .methods
                    .iter()
                    .filter(|&&m| {
                        let data = tcx.def(m);
                        data.name() == Some(name.name) && data.vis == Vis::Private
                    })
                    .map(|&m| FoundMethod {
                        def: m,
                        owner: def.def,
                        args: base_args,
                    })
                    .collect();
                if let Some(first) = methods.first().copied() {
                    return Some(MemberRef {
                        kind: MemberKind::Methods(methods),
                        via_slice: None,
                        owner: first.owner,
                        args: first.args,
                    });
                }
            }
            current = tcx.base_of(base, base_args);
        }
        None
    }

    /// The type a member found at `at` is called at: for an interface type, the
    /// class `Self` stands for (4C's `self_of`), asked of the receiver as it is once
    /// its adjusts apply, so after its `BoxDeref`s, with `?.` as with `.`.
    fn self_at(&mut self, receiver: &hir::Expr, at: Ty) -> Ty {
        if !self.sema.tcx.is_interface_ty(at) {
            return at;
        }
        let mut reached = receiver.clone();
        reached.ty = at;
        reached.adjust.clear();
        self.self_of(&reached)
    }

    /// The members of a narrowed nullable's own type, which the payload lacked
    /// (S:607): the receiver is taken at the nullable type, one `&` stripped, and
    /// recorded (S:742).
    fn on_nullable(&mut self, place: hir::Expr, name: Ident) -> Option<Member> {
        let mut receiver = place;
        let mut at = self.resolved(receiver.ty);
        if let TyKind::Ref(inner) = self.sema.tcx.kind(at) {
            let span = receiver.span;
            receiver = self.mk_expr(inner, span, ExprKind::Deref(Box::new(receiver)));
            at = self.resolved(inner);
        }
        if !matches!(self.sema.tcx.kind(at), TyKind::Nullable(_)) {
            return None;
        }
        let found = self.sema.tcx.member(at, name.name, self.at.module)?;
        self.record_ref(&receiver, RecordKind::Receiver);
        Some(Member::new(Some(found), receiver, at))
    }

    /// The lookup on one type: an anonymous object's field, or what `Tcx::member`
    /// finds, after the visibility check; with `calling`, methods all `static` are
    /// returned unchecked, for the call to report.
    fn step(&mut self, at: Ty, name: Ident, calling: bool) -> Step {
        if let Some(shape) = self.shape_of(at) {
            return match shape.position(name.name) {
                Some(i) => Step::Object(FieldIdx::new(i), shape.fields[i].1),
                None => Step::Missed,
            };
        }
        match self
            .sema
            .tcx
            .member_in(at, name.name, self.at.module, &self.env)
        {
            Some(found) if calling && self.all_static(&found) => Step::Found(found),
            Some(found) => Step::Found(self.check_visible(found, name)),
            None => Step::Missed,
        }
    }

    /// Whether `found` is methods, every one `static`.
    pub(crate) fn all_static(&self, found: &MemberRef) -> bool {
        let tcx = &*self.sema.tcx;
        match &found.kind {
            MemberKind::Methods(methods) => methods.iter().all(|m| {
                tcx.sig_opt(m.def)
                    .is_some_and(|s| s.receiver == Some(hir::Receiver::Static))
            }),
            MemberKind::Field { .. } => false,
        }
    }

    /// The enum case a narrowed payload of `place` is in (`Fact::Case` inside a
    /// `match` arm, 4B), with the enum and its arguments; `None` for a nullable's
    /// `Present` payload.
    fn case_of(
        &self,
        place: &hir::Expr,
        variant: hir::VariantIdx,
    ) -> Option<(AdtId, hir::VariantIdx, hir::TyList)> {
        let tcx = &*self.sema.tcx;
        let mut t = place.ty;
        loop {
            match tcx.kind(t) {
                TyKind::Ref(inner) | TyKind::Boxed(inner) => t = inner,
                TyKind::Adt(adt, args) => {
                    let e = tcx.adt(adt).as_enum()?;
                    return (variant.index() < e.variants.len()).then_some((adt, variant, args));
                }
                _ => return None,
            }
        }
    }

    /// The shape of an anonymous object type, or of the shape an implicit parameter
    /// stands for (D5).
    fn shape_of(&self, at: Ty) -> Option<Arc<Shape>> {
        let tcx = &*self.sema.tcx;
        match tcx.kind(at) {
            TyKind::Object(shape) => Some(tcx.shape(shape)),
            TyKind::Param(p) => match tcx.param(p).implicit {
                Some(Implicit::Shape(shape)) => Some(tcx.shape(shape)),
                _ => None,
            },
            _ => None,
        }
    }

    /// `base?.name` on a nullable base: lookup on the payload, one `&` stripped and
    /// through `Box`, with the base itself as the receiver; EN0413 when the base is
    /// an owned rvalue (S:750).
    fn lookup_optional(
        &mut self,
        receiver: hir::Expr,
        payload: Ty,
        name: Ident,
        calling: bool,
    ) -> Member {
        let tcx = &*self.sema.tcx;
        if !matches!(tcx.kind(payload), TyKind::Ref(_)) && !is_place(&receiver) {
            let shown = tcx.ty_string(receiver.ty);
            let span = self.optional_span(receiver.span, name.span);
            let written = self.source(receiver.span);
            // A call keeps its arguments, `v?.length()` (the innermost call frame is
            // this call's while its callee is looked up).
            let call = match (calling, self.calls.last()) {
                (true, Some(frame)) => {
                    let args: Vec<String> = frame.args.iter().map(|&a| self.source(a)).collect();
                    format!("({})", args.join(", "))
                }
                _ => String::new(),
            };
            // A name the help's `const` may declare: neither a local in scope nor
            // the variable this initialiser declares (EN0307 otherwise).
            let fresh = ["v", "value", "tmp", "found"]
                .into_iter()
                .map(enrang_base::intern)
                .find(|&n| self.scopes.lookup(n).is_none() && self.init_name != Some(n));
            let help = match fresh {
                Some(v) => format!(
                    "bind it first: `const {v} = {written};`, then `{v}?.{}{call}`",
                    name.name
                ),
                None => "bind it to a local first, then use `?.` on the local".to_owned(),
            };
            self.sema.emit(
                Diagnostic::new(
                    Code::EN0413,
                    "`?.` on an owned value: bind it first",
                    span,
                    format!("this `{shown}` is a temporary"),
                )
                .with_help(Help::text(help)),
            );
        }
        let mut at = self.resolved(payload);
        if let TyKind::Ref(inner) = self.sema.tcx.kind(at) {
            at = self.resolved(inner);
        }
        // A nullable field read with `?.` is `&(F | null) | null`: the next `?.`
        // looks through both nulls, so `n?.next?.value` reads `value` when neither
        // is `null` (S:607, plan choice; S:750 is silent).
        if let TyKind::Nullable(inner) = self.sema.tcx.kind(at) {
            at = self.resolved(inner);
        }
        loop {
            if let TyKind::Error = self.sema.tcx.kind(at) {
                return Member::new(None, receiver, at);
            }
            match self.step(at, name, calling) {
                Step::Found(found) => {
                    let at = self.self_at(&receiver, at);
                    return Member::new(Some(found), receiver, at);
                }
                Step::Object(field, ty) => {
                    let mut member = Member::new(None, receiver, at);
                    member.object_field = Some((field, ty));
                    return member;
                }
                Step::Missed => {}
            }
            match self.sema.tcx.kind(at) {
                TyKind::Boxed(inner) => at = inner,
                _ => break,
            }
        }
        if let Some(found) = self.synthesised_member(at, name) {
            return Member::synthesised(found, receiver, at);
        }
        if let Some(found) = self.private_of_base(at, name) {
            return Member::new(Some(found), receiver, at);
        }
        if let Some(case) = self.case_with_field(at, name.name)
            && let Some(kill) = self.killed_case(&receiver)
        {
            // The arm's case fact was killed: the lost narrowing is the cause.
            let shown = self.ty_str(at);
            let place = self.source(receiver.span);
            self.sema.emit(
                Diagnostic::new(
                    Code::EN0303,
                    format!("`{shown}` has no member `{}`", name.name),
                    name.span,
                    "no such member",
                )
                .with_secondary(
                    kill,
                    format!("`{place}` is assigned here, so its case is no longer known"),
                )
                .note(format!(
                    "`{}` is a field of the case `{case}`, and the assignment ends what the `match` arm knew about `{place}`",
                    name.name
                )),
            );
            return Member::new(None, receiver, at);
        }
        self.member_miss(at, name);
        Member::new(None, receiver, at)
    }

    /// A member access on an inference variable (S:733): EN0410 on one still
    /// unknown; on an integer or float one, the members of `i32` or `f64` with every
    /// argument bound to that representative rebound to the variable, so `Self` is
    /// the variable.
    fn lookup_on_var(&mut self, receiver: hir::Expr, at: Ty, name: Ident) -> Member {
        let TyKind::Infer(var) = self.sema.tcx.kind(at) else {
            return Member::new(None, receiver, at);
        };
        let root = self.infer.find(var);
        let common = *self.sema.tcx.common();
        let stand_in = match self.infer.vars[root].kind {
            VarKind::Int => common.i32,
            VarKind::Float => common.f64,
            VarKind::Any => {
                let written = self.source(receiver.span);
                self.sema.emit(
                    Diagnostic::new(
                        Code::EN0410,
                        format!("cannot infer the type of `{written}`"),
                        receiver.span,
                        "nothing here decides its type",
                    )
                    .with_help(Help::text("add a type annotation")),
                );
                let error = self.error_ty();
                self.infer.vars[root].value = Some(error);
                return Member::new(None, receiver, error);
            }
        };
        let Some(mut found) = self.sema.tcx.member(stand_in, name.name, self.at.module) else {
            if let Some(found) = self.synthesised_member(at, name) {
                return Member::synthesised(found, receiver, at);
            }
            self.member_miss(stand_in, name);
            return Member::new(None, receiver, at);
        };
        let rebind = |tcx: &hir::Tcx, args: hir::TyList| {
            let list: Vec<Ty> = tcx
                .list(args)
                .iter()
                .map(|&a| if a == stand_in { at } else { a })
                .collect();
            tcx.intern_list(&list)
        };
        found.args = rebind(self.sema.tcx, found.args);
        if let MemberKind::Methods(methods) = &mut found.kind {
            for m in methods.iter_mut() {
                m.args = rebind(self.sema.tcx, m.args);
            }
        }
        Member::new(Some(found), receiver, at)
    }

    /// `t` with its outermost bound inference variables replaced by their values.
    fn resolved(&mut self, mut t: Ty) -> Ty {
        while let TyKind::Infer(var) = self.sema.tcx.kind(t) {
            let root = self.infer.find(var);
            match self.infer.vars[root].value {
                Some(value) => t = value,
                None => break,
            }
        }
        t
    }

    /// A member expression (plan c.5): a path through a type, a namespace or a form,
    /// a field (`Field`, or `OptionalChain` with `?.`), or a method read as a value
    /// (EN0441 for `length`, otherwise EN0303).
    pub(crate) fn check_member_expr(&mut self, e: &ast::Expr, ex: Expect) -> hir::Expr {
        let ast::ExprKind::Member {
            base,
            name,
            optional,
        } = &e.kind
        else {
            return self.error_expr(e.span);
        };
        if matches!(base.kind, ast::ExprKind::Super) {
            self.super_outside_call(base.span);
            return self.error_expr(e.span);
        }
        if !optional && let Some(path) = self.path_base(base) {
            return self.static_member(path, base, *name, e.span, ex);
        }
        let base_e = self.check_operand(base, *optional);
        let member = self.lookup_member(base_e, *name, *optional);
        if let Some((field, ty)) = member.object_field {
            return self.field_expr(member, field, ty, *optional, e.span);
        }
        let Some(found) = member.found.clone() else {
            return self.error_expr(e.span);
        };
        match found.kind {
            MemberKind::Field { adt, field } => {
                let ty = self.sema.tcx.field_ty(adt, None, field, found.args);
                self.field_expr(member, field, ty, *optional, e.span)
            }
            MemberKind::Methods(_) => {
                self.method_as_value(&member, base, *name, *optional);
                self.error_expr(e.span)
            }
        }
    }

    /// `receiver.field`, or with `?.` on a nullable receiver an `OptionalChain` of
    /// type `&F | null` (`F | null` when `F` is a reference, S:750).
    pub(crate) fn field_expr(
        &mut self,
        member: Member,
        field: FieldIdx,
        ty: Ty,
        optional: bool,
        span: Span,
    ) -> hir::Expr {
        let nullable_base = matches!(
            self.sema.tcx.kind(self.shallow(member.receiver.ty)),
            TyKind::Nullable(_)
        );
        if optional && nullable_base {
            let tcx = &*self.sema.tcx;
            let inner = match tcx.kind(ty) {
                TyKind::Ref(_) => ty,
                _ => tcx.mk_ref(ty),
            };
            let result = tcx.mk_nullable(inner);
            return self.mk_expr(
                result,
                span,
                ExprKind::OptionalChain(Box::new(OptChain {
                    base: member.receiver,
                    member: OptMember::Field(field),
                    void_result: false,
                })),
            );
        }
        self.mk_expr(ty, span, ExprKind::Field(Box::new(member.receiver), field))
    }

    /// A method named where a value is read: EN0441 for `length` (S:1383's helps),
    /// EN0303 for any other; the helps call it with `?.` where it was written so.
    fn method_as_value(&mut self, member: &Member, base: &ast::Expr, name: Ident, optional: bool) {
        let dot = if optional { "?." } else { "." };
        let written = self.source(base.span);
        // The receiver as far as it is known here, as EN0303 prints it: an array
        // literal's element variable is bound by now, so `names.length` on
        // `["ann", "bo"]` names `string[]`, never `_[]`.
        let at = self.resolve(member.at);
        let shown = self.ty_str(at);
        let tcx = &*self.sema.tcx;
        if name.name.as_str() == "length" {
            let help = match tcx.kind(at) {
                TyKind::Str => {
                    let counts = match &base.kind {
                        ast::ExprKind::Str(s) => {
                            Some((s.as_str().len(), s.as_str().chars().count()))
                        }
                        _ => None,
                    };
                    match counts {
                        Some((bytes, chars)) => format!(
                            "`{written}{dot}length()` counts bytes ({bytes} here); `{written}{dot}charCount()` counts characters ({chars} here)"
                        ),
                        None => format!(
                            "`{written}{dot}length()` counts bytes; `{written}{dot}charCount()` counts characters"
                        ),
                    }
                }
                _ => format!("`{written}{dot}length()`"),
            };
            self.sema.emit(
                Diagnostic::new(
                    Code::EN0441,
                    format!("`length` is a method on `{shown}`"),
                    name.span,
                    "a method, called as `length()`",
                )
                .with_help(Help::text(help)),
            );
            return;
        }
        self.sema.emit(
            Diagnostic::new(
                Code::EN0303,
                format!("`{shown}` has no field `{}`", name.name),
                name.span,
                "a method, not a field",
            )
            .note(format!(
                "`{}` is a method: call it, `{written}{dot}{}()`",
                name.name, name.name
            )),
        );
    }

    /// Types a member's base, or a callee's receiver, as `check_expr` would with no
    /// expected type, except that a member base is typed by [`Self::check_member_expr`]
    /// here, so a chain types the same whichever stage dispatches `Member`.
    /// `optional` says whether it is reached with `?.`: a receiver of `.` needs a
    /// value that is not `null` (`value_use`), since `?.` never short-circuits and
    /// `a?.b.c` is EN0303 again (S:607).
    pub(crate) fn check_operand(&mut self, e: &ast::Expr, optional: bool) -> hir::Expr {
        let saved = self.value_use;
        self.value_use = if optional {
            ValueUse::Any
        } else {
            ValueUse::NonNull
        };
        let typed = match &e.kind {
            ast::ExprKind::Member { .. } => self.check_member_expr(e, Expect::None),
            _ => {
                self.inherit_use = true;
                self.check_expr(e, Expect::None)
            }
        };
        self.value_use = saved;
        typed
    }

    /// EN0606: a destructor named as a member (S:648); `span` is the call, or the
    /// member's name when it is not called.
    pub(crate) fn destructor_named(&mut self, span: Span, receiver: Span) {
        let written = self.source(receiver);
        self.sema.emit(
            Diagnostic::new(
                Code::EN0606,
                format!("a destructor runs by itself: call `dispose({written})`"),
                span,
                "a destructor is never called by name",
            )
            .note(
                "a destructor runs once, at the end of the object's life; `dispose` ends it early",
            ),
        );
    }

    /// `super` anywhere but `super(...)` and `super.m(...)` (plan c.5, choice: EN0219).
    pub(crate) fn super_outside_call(&mut self, span: Span) {
        self.sema.emit(Diagnostic::new(
            Code::EN0219,
            "`super` outside a call",
            span,
            "`super` is called, as `super(...)` or `super.m()`",
        ));
    }

    // ---------------------------------------------------------------------------
    // Visibility (A:896).

    /// `found` after the visibility check: a member the code here may not see is
    /// EN0308; methods some of which it sees keep only those.
    pub(crate) fn check_visible(&mut self, mut found: MemberRef, name: Ident) -> MemberRef {
        match &mut found.kind {
            MemberKind::Field { adt, field } => {
                let def = self.sema.tcx.field_def(*adt, None, *field);
                let (vis, declared, decl) = (def.vis, def.declared_in, def.span);
                if !self.sees(vis, declared) {
                    self.not_visible(name, vis, declared, decl);
                }
            }
            MemberKind::Methods(methods) => {
                let seen: Vec<FoundMethod> = methods
                    .iter()
                    .copied()
                    .filter(|m| self.sees_method(m.def))
                    .collect();
                if seen.is_empty() {
                    if let Some(first) = methods.first().copied() {
                        let data = self.sema.tcx.def(first.def);
                        let (vis, decl) = (data.vis, data.name_span);
                        if let Some(declared) = self.declaring_adt(first.def) {
                            self.not_visible(name, vis, declared, decl);
                        }
                    }
                } else if seen.len() < methods.len() {
                    found.owner = seen[0].owner;
                    found.args = seen[0].args;
                    *methods = seen;
                }
            }
        }
        found
    }

    /// EN0308 for constructor `ctor` chosen at `span` (the class a `new` names, or
    /// `super`) when the code here may not see it (S:321, S:580): a `private` one
    /// outside its class's body, a `protected` one outside the class and its
    /// subclasses.
    pub(crate) fn check_ctor_visible(&mut self, ctor: DefId, span: Span) {
        if self.sees_method(ctor) {
            return;
        }
        let vis = self.sema.tcx.def(ctor).vis;
        let decl = crate::typeck::overload::decl_name_span(self.sema.tcx, ctor);
        if let Some(declared) = self.declaring_adt(ctor) {
            let name = Ident {
                name: intern("constructor"),
                span,
            };
            self.not_visible(name, vis, declared, decl);
        }
    }

    /// Whether the code here sees method `m`.
    fn sees_method(&self, m: DefId) -> bool {
        let vis = self.sema.tcx.def(m).vis;
        match self.declaring_adt(m) {
            Some(declared) => self.sees(vis, declared),
            None => true,
        }
    }

    /// The class, enum or interface that declares member `m`.
    fn declaring_adt(&self, m: DefId) -> Option<AdtId> {
        let parent = self.sema.tcx.def(m).parent?;
        self.sema.tcx.adt_of(parent)
    }

    /// Whether the code here sees a member of `declared` with visibility `vis`: a
    /// `private` one inside the body of `declared` only, a `protected` one inside
    /// `declared` and its subclasses (A:896).
    fn sees(&self, vis: Vis, declared: AdtId) -> bool {
        let here = self.enclosing_adt();
        match vis {
            Vis::Public => true,
            Vis::Private => here == Some(declared),
            Vis::Protected => here.is_some_and(|c| self.extends_class(c, declared)),
        }
    }

    /// The class or enum whose body the code here is in: the scope's class, or the
    /// parent of the member whose body this is.
    fn enclosing_adt(&self) -> Option<AdtId> {
        if let Some(class) = self.at.class {
            return Some(class);
        }
        let hir::BodyOwner::Fn(def) = self.owner else {
            return None;
        };
        self.declaring_adt(def)
    }

    /// Whether class `c` is `base` or extends it, directly or through others.
    fn extends_class(&self, c: AdtId, base: AdtId) -> bool {
        let tcx = &*self.sema.tcx;
        let mut cur = Some(c);
        let mut steps = 0;
        while let Some(adt) = cur {
            if adt == base {
                return true;
            }
            steps += 1;
            if steps > tcx.adts().count() {
                return false;
            }
            cur = tcx
                .adt(adt)
                .as_class()
                .and_then(|class| class.base)
                .and_then(|b| match tcx.kind(b) {
                    TyKind::Adt(b, _) => Some(b),
                    _ => None,
                });
        }
        false
    }

    /// EN0308 for `name`, declared `vis` in `declared` at `decl`.
    fn not_visible(&mut self, name: Ident, vis: Vis, declared: AdtId, decl: Span) {
        let tcx = &*self.sema.tcx;
        let class = tcx.adt(declared).name;
        let (message, label) = match vis {
            Vis::Protected => (
                format!("`{}` is protected in `{class}`", name.name),
                format!("only `{class}` and its subclasses can use it"),
            ),
            _ => (
                format!("`{}` is private to `{class}`", name.name),
                format!("only the body of `{class}` can use it"),
            ),
        };
        let mut diag = Diagnostic::new(Code::EN0308, message, name.span, label);
        let user = !tcx.module(tcx.def(tcx.adt(declared).def).module).library;
        if user && !decl.is_dummy() {
            diag = diag.with_secondary(decl, format!("`{}` is declared here", name.name));
        }
        self.sema.emit(diag);
    }

    // ---------------------------------------------------------------------------
    // Misses.

    /// A miss on `at` (no nullable): EN0308 when a member of that name exists that
    /// the code here may not see (a base's `private` one, a bound's non-`public`
    /// one), otherwise EN0303 with "did you mean" over the type's members.
    fn member_miss(&mut self, at: Ty, name: Ident) {
        self.member_miss_with(at, name, None);
    }

    /// [`Self::member_miss`], with the members of `also` (a nullable's payload)
    /// among the names "did you mean" tries.
    fn member_miss_with(&mut self, at: Ty, name: Ident, also: Option<Ty>) {
        if self.sema.tcx.references_error(at) {
            return;
        }
        // A class whose `extends` names no class may inherit the member: that
        // error was reported at the class.
        if let TyKind::Adt(adt, _) = self.sema.tcx.kind(at)
            && self.sema.base_unknown(adt)
        {
            return;
        }
        if let Some((vis, declared, decl)) = self.hidden_member(at, name.name) {
            self.not_visible(name, vis, declared, decl);
            return;
        }
        let shown = self.ty_str(at);
        let mut diag = Diagnostic::new(
            Code::EN0303,
            format!("`{shown}` has no member `{}`", name.name),
            name.span,
            "no such member",
        );
        if let Some(case) = self.case_with_field(at, name.name) {
            diag = diag.note(format!(
                "`{}` is a field of the case `{case}`: read it in that case's `match` arm",
                name.name
            ));
        }
        let mut names = self.member_names(at);
        if let Some(also) = also {
            names.extend(self.member_names(also));
            names.sort_by_key(|n| n.as_str());
            names.dedup();
        }
        let names: Vec<&str> = names
            .iter()
            .filter(|n| !self.taken_names.contains(n))
            .map(|n| n.as_str())
            .collect();
        if let Some(found) = did_you_mean(name.name.as_str(), &names) {
            diag = diag.with_help(Help::machine(
                format!("did you mean `{found}`?"),
                vec![Edit::replace(name.span, found)],
            ));
        }
        self.sema.emit(diag);
    }

    /// The first case of the enum `at` with a field `name`.
    fn case_with_field(&self, at: Ty, name: Symbol) -> Option<Symbol> {
        let tcx = &*self.sema.tcx;
        let TyKind::Adt(adt, _) = tcx.kind(at) else {
            return None;
        };
        tcx.adt(adt)
            .as_enum()?
            .variants
            .iter()
            .find(|v| v.fields.iter().any(|f| f.name == name))
            .map(|v| v.name)
    }

    /// A miss on the unnarrowed nullable `at` with payload `payload`: EN0303, with a
    /// `?.` fix-it and a narrowing help when the payload has the member (S:607,
    /// T:635), otherwise as any miss on the payload.
    fn nullable_miss(&mut self, receiver: &hir::Expr, at: Ty, payload: Ty, name: Ident) {
        if self.sema.tcx.references_error(at) {
            return;
        }
        let mut inner = payload;
        if let TyKind::Ref(t) = self.sema.tcx.kind(inner) {
            inner = t;
        }
        let mut has = false;
        let mut found: Option<MemberRef> = None;
        loop {
            let on_shape = self
                .shape_of(inner)
                .is_some_and(|shape| shape.position(name.name).is_some());
            if on_shape {
                has = true;
                break;
            }
            if let Some(member) = self.sema.tcx.member(inner, name.name, self.at.module) {
                found = Some(member);
                has = true;
                break;
            }
            match self.sema.tcx.kind(inner) {
                TyKind::Boxed(t) => inner = t,
                _ => break,
            }
        }
        if !has {
            self.member_miss_with(at, name, Some(inner));
            return;
        }
        let shown = self.sema.tcx.ty_string(at);
        let written = self.source(receiver.span);
        let mut diag = Diagnostic::new(
            Code::EN0303,
            format!("`{shown}` has no member `{}`", name.name),
            name.span,
            "this value may be `null`",
        );
        // `?.` makes the value nullable: offered only where a `null` there still
        // checks (`value_use`), not as `return s?.toUpperCase();` in a function
        // returning `string`, `a.zip?.length() > 0`, or `u?.name.length()`, whose
        // `.length` misses again (S:607).
        let fits = match self.value_use {
            ValueUse::Any => true,
            ValueUse::NonNull => false,
            // `?.f` keeps a reference to the field, read through only when Copy.
            ValueUse::Copied => match &found {
                Some(MemberRef {
                    kind: MemberKind::Field { adt, field },
                    args,
                    ..
                }) => {
                    let tcx = &*self.sema.tcx;
                    tcx.is_copy(tcx.field_ty(*adt, None, *field, *args), &self.env)
                }
                Some(_) => true,
                None => false,
            },
        };
        let mut offered = false;
        if fits && let Some(dot) = self.dot_before(receiver.span, name.span) {
            diag = diag.with_help(Help::machine(
                format!(
                    "use `?.{}`, which reads it only when the value is not `null`",
                    name.name
                ),
                vec![Edit::insert(dot, "?")],
            ));
            offered = true;
        }
        let lead = if offered { "or narrow" } else { "narrow" };
        // Only a path narrows (S:739): a `?.` chain or a call never does.
        if self.adjusted_path(receiver).is_some() {
            diag = diag.with_help(Help::text(format!(
                "{lead} it first: `if ({written} != null) {{ ... }}`"
            )));
        } else if !offered {
            diag = diag.with_help(Help::text(format!(
                "keep it in a constant and narrow that: `const v = {written}; if (v != null) {{ ... }}`"
            )));
        }
        self.sema.emit(diag);
    }

    /// A member named `name` on `at` that lookup skips because the code here may
    /// not see it: a `private` member of a base class (A:896), or a non-`public`
    /// member of a class bound (S:764); its visibility, class and declaration.
    fn hidden_member(&self, at: Ty, name: Symbol) -> Option<(Vis, AdtId, Span)> {
        let tcx = &*self.sema.tcx;
        let classes: Vec<AdtId> = match tcx.kind(at) {
            TyKind::Adt(adt, _) => {
                let mut chain = Vec::new();
                let mut cur = tcx.adt(adt).as_class().and_then(|c| c.base);
                while let Some(b) = cur {
                    let TyKind::Adt(b, _) = tcx.kind(b) else {
                        break;
                    };
                    if chain.contains(&b) {
                        break;
                    }
                    chain.push(b);
                    cur = tcx.adt(b).as_class().and_then(|c| c.base);
                }
                chain
            }
            TyKind::Param(p) => tcx
                .param(p)
                .bounds
                .iter()
                .filter_map(|&b| match tcx.bound(b) {
                    Bound::Class { adt, .. } => Some(*adt),
                    Bound::Iface { .. } => None,
                })
                .collect(),
            _ => Vec::new(),
        };
        let bound = matches!(tcx.kind(at), TyKind::Param(_));
        for adt in classes {
            let Some(class) = tcx.adt(adt).as_class() else {
                continue;
            };
            for field in &class.fields {
                if field.name == name
                    && field.declared_in == adt
                    && (field.vis == Vis::Private || (bound && field.vis != Vis::Public))
                {
                    return Some((field.vis, adt, field.span));
                }
            }
            for &m in &class.methods {
                let data = tcx.def(m);
                if data.name() == Some(name)
                    && (data.vis == Vis::Private || (bound && data.vis != Vis::Public))
                {
                    return Some((data.vis, adt, data.name_span));
                }
            }
        }
        None
    }

    /// The names of the members of `at` the code here sees, for "did you mean"
    /// (A:886): fields and methods, own, inherited and `extend` ones, and for an
    /// array those of `Slice<T>`.
    pub(crate) fn member_names(&self, at: Ty) -> Vec<Symbol> {
        if let Some(shape) = self.shape_of(at) {
            return shape.fields.iter().map(|(name, _)| *name).collect();
        }
        let tcx = &*self.sema.tcx;
        let mut names: BTreeSet<Symbol> = BTreeSet::new();
        let mut adts: Vec<AdtId> = Vec::new();
        match tcx.kind(at) {
            TyKind::Adt(adt, _) => adts.push(adt),
            TyKind::Param(p) => {
                for &b in &tcx.param(p).bounds {
                    adts.push(tcx.bound(b).adt());
                }
            }
            _ => {
                if let Some((adt, _)) = tcx.lang_class_of(at) {
                    adts.push(adt);
                }
            }
        }
        if let TyKind::Array(_) | TyKind::Fixed(..) = tcx.kind(at)
            && let Some(slice) = tcx.lang_adt(LangItem::Slice)
        {
            adts.push(slice);
        }
        let mut seen = Vec::new();
        while let Some(adt) = adts.pop() {
            if seen.contains(&adt) {
                continue;
            }
            seen.push(adt);
            let def = tcx.adt(adt);
            if let AdtKind::Class(class) = &def.kind {
                names.extend(class.fields.iter().map(|f| f.name));
                if let Some(TyKind::Adt(base, _)) = class.base.map(|b| tcx.kind(b)) {
                    adts.push(base);
                }
            }
            names.extend(def.own_methods().iter().filter_map(|&m| tcx.def(m).name()));
        }
        for ext in tcx.extends() {
            names.extend(ext.members.iter().filter_map(|&m| tcx.def(m).name()));
        }
        names
            .into_iter()
            .filter(|&n| match tcx.member(at, n, self.at.module) {
                Some(found) => match &found.kind {
                    MemberKind::Field { adt, field } => {
                        let f = tcx.field_def(*adt, None, *field);
                        self.sees(f.vis, f.declared_in)
                    }
                    MemberKind::Methods(methods) => methods.iter().any(|m| self.sees_method(m.def)),
                },
                None => false,
            })
            .collect()
    }

    // ---------------------------------------------------------------------------
    // Source positions.

    /// The source text under `span`.
    pub(crate) fn source(&self, span: Span) -> String {
        if span.is_dummy() {
            return String::new();
        }
        self.sema.tcx.map().text(span).to_owned()
    }

    /// The position of the `.` between a member's base and its name.
    fn dot_before(&self, base: Span, name: Span) -> Option<BytePos> {
        if base.is_dummy() || name.is_dummy() || base.hi > name.lo {
            return None;
        }
        let gap = Span {
            lo: base.hi,
            hi: name.lo,
        };
        let text = self.sema.tcx.map().text(gap);
        let offset = text.rfind('.')?;
        Some(BytePos(base.hi.0 + u32::try_from(offset).ok()?))
    }

    /// The span of `?.name`: from the `?` before the name to its end; the name
    /// alone when the source has no `?` there.
    fn optional_span(&self, base: Span, name: Span) -> Span {
        if base.is_dummy() || name.is_dummy() || base.hi > name.lo {
            return name;
        }
        let gap = Span {
            lo: base.hi,
            hi: name.lo,
        };
        let text = self.sema.tcx.map().text(gap);
        match text.rfind('?').and_then(|o| u32::try_from(o).ok()) {
            Some(offset) => Span {
                lo: BytePos(base.hi.0 + offset),
                hi: name.hi,
            },
            None => name,
        }
    }
}

/// Whether `e` names storage that outlives the expression: a local, a static, a
/// dereference, or a field, payload or element of one (EN0413's "rvalue" is
/// anything else).
fn is_place(e: &hir::Expr) -> bool {
    match &e.kind {
        ExprKind::Local(_) | ExprKind::Static(_) | ExprKind::Deref(_) => true,
        ExprKind::Field(base, _)
        | ExprKind::NarrowedPayload(base, _, _)
        | ExprKind::Index(base, _) => is_place(base),
        _ => false,
    }
}
