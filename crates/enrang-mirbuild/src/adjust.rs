//! Adjust chains (A:392-410, A:898, A:935-936; M3 plan c.6): each step applied to
//! the value the expression produced, with `Convert` for C18, C21 and C22. HIR
//! types an expression before its chain, so a step whose target only the context
//! knows (an upcast, an interface, `Ok`) takes it from `want`, the type the chain
//! ends at, under the wraps that follow it.

use enrang_hir::{self as hir, Adjust, ConstValue, ExprKind as K, LangItem, Ty, TyKind};
use enrang_mir::{
    AggregateKind, BorrowOrigin, ClassHolder, ClassOp, ClosureFn, ConstKind, ConvKind, Operand,
    Proj, Rvalue, StatementKind,
};

use crate::builder::Builder;
use crate::expr::Val;

impl Builder<'_> {
    /// `e` lowered with its adjust chain, and the type it ends at.
    pub(crate) fn adjusted(&mut self, e: &hir::Expr, want: Option<Ty>) -> (Val, Ty) {
        let first = e.adjust.first().copied();
        if let (K::Borrow(x), Some(Adjust::FixedToSlice)) = (&e.kind, first)
            && matches!(&x.kind, K::ArrayLit(es) if es.iter().all(constant))
        {
            let op = crate::lower_literal_view(self, e);
            let ty = want.unwrap_or_else(|| self.slice_of(e.ty));
            return (Val::Op(op), ty);
        }
        if let (K::Arrow(a), Some(Adjust::FnToPtr | Adjust::FnToUnsafePtr)) = (&e.kind, first) {
            return (Val::Rv(Rvalue::ArrowFn(*a)), want.unwrap_or(e.ty));
        }
        if let (K::Arrow(a), Some(Adjust::ArrowToClosure)) = (&e.kind, first) {
            // The closure, then the wraps after it (a nullable closure parameter).
            let ty = want.map_or(e.ty, |w| self.under_wraps(w, &e.adjust[1..]));
            let t = self.new_temp(ty, e.span);
            crate::lower_arrow_value(self, *a, t.into(), e.span);
            return self.chain_from(e, 1, Val::Place(t.into()), ty, want);
        }
        let v = self.val(e);
        self.chain(e, v, want)
    }

    /// Applies `e`'s adjust chain to `v`, of type `e.ty`.
    pub(crate) fn chain(&mut self, e: &hir::Expr, v: Val, want: Option<Ty>) -> (Val, Ty) {
        self.chain_from(e, 0, v, e.ty, want)
    }

    /// Applies `e`'s adjust chain from step `from` on to `v`, of type `ty`.
    fn chain_from(
        &mut self,
        e: &hir::Expr,
        from: usize,
        mut v: Val,
        mut ty: Ty,
        want: Option<Ty>,
    ) -> (Val, Ty) {
        let tcx = self.cx.tcx;
        let span = e.span;
        for (k, &a) in e.adjust.iter().enumerate().skip(from) {
            let rest = &e.adjust[k + 1..];
            let target = want.map(|w| self.under_wraps(w, rest));
            let last = rest.is_empty();
            (v, ty) = match a {
                Adjust::AutoBorrow => {
                    let r = tcx.mk_ref(ty);
                    let (place, origin) = match crate::expr::read(v) {
                        Val::Place(p) if !self.is_temp(p) => {
                            self.guard(p, span);
                            self.borrow_class_check(e.id, p, span);
                            (p, BorrowOrigin::AutoBorrow)
                        }
                        v => (self.temp_of(v, ty, span), BorrowOrigin::TempArg),
                    };
                    (
                        self.rv_or_temp(Rvalue::Ref { place, origin }, r, last, span),
                        r,
                    )
                }
                Adjust::Reborrow | Adjust::BoxDeref if matches!(tcx.kind(ty), TyKind::Ref(_)) => {
                    let mut inner = self.deref_of(v, ty, span);
                    let mut out = ty;
                    if a == Adjust::BoxDeref {
                        inner = self.body.project(inner, Proj::Deref);
                        out = tcx.mk_ref(self.place_ty(inner));
                    }
                    self.guard(inner, span);
                    self.borrow_class_check(e.id, inner, span);
                    let rv = Rvalue::Ref {
                        place: inner,
                        origin: BorrowOrigin::Reborrow,
                    };
                    (self.rv_or_temp(rv, out, last, span), out)
                }
                Adjust::Reborrow => (v, ty),
                Adjust::BoxDeref => {
                    let p = self.val_place(v, ty, span);
                    let inner = self.body.project(p, Proj::Deref);
                    let t = self.place_ty(inner);
                    (Val::Place(inner), t)
                }
                Adjust::ReadThrough => {
                    let inner = self.deref_of(v, ty, span);
                    let t = self.place_ty(inner);
                    (Val::Place(inner), t)
                }
                Adjust::ReadThroughNullable => self.read_through_nullable(v, ty, span),
                Adjust::WrapNull | Adjust::WrapNullRef => {
                    let out = target
                        .filter(|t| matches!(tcx.kind(*t), TyKind::Nullable(_)))
                        .unwrap_or_else(|| tcx.mk_nullable(ty));
                    let op = self.use_val(v, ty, span);
                    (
                        Val::Rv(Rvalue::Aggregate(AggregateKind::Present, vec![op])),
                        out,
                    )
                }
                Adjust::WrapOk => {
                    let out = target.unwrap_or(ty);
                    let op = self.use_val(v, ty, span);
                    let rv = match tcx.kind(out) {
                        TyKind::Adt(adt, args) if tcx.is_lang_adt(adt, LangItem::Result) => {
                            let kind = AggregateKind::Adt {
                                adt,
                                variant: Some(hir::VariantIdx::OK),
                                args,
                            };
                            Rvalue::Aggregate(kind, vec![op])
                        }
                        _ => Rvalue::Use(op),
                    };
                    (Val::Rv(rv), out)
                }
                Adjust::NeverToAny => (v, target.unwrap_or(ty)),
                Adjust::LiteralDescriptor => {
                    let out = tcx.mk_ref(tcx.common().str);
                    (Val::Op(retype(self.use_val(v, ty, span), out)), out)
                }
                Adjust::FnToPtr | Adjust::FnToUnsafePtr | Adjust::FnToHandler => {
                    let out = target.unwrap_or(ty);
                    (Val::Op(retype(self.use_val(v, ty, span), out)), out)
                }
                Adjust::ArrowToClosure => {
                    let out = target.unwrap_or(ty);
                    (self.to_closure(v, ty, span), out)
                }
                Adjust::ClosureReborrow => {
                    let p = self.val_place(v, ty, span);
                    (Val::Rv(Rvalue::ClosureReborrow(p)), ty)
                }
                Adjust::FixedToSlice
                | Adjust::ArrayToSlice
                | Adjust::Upcast
                | Adjust::BoxToInterface
                | Adjust::RefToInterface => {
                    let kind = ConvKind::of_adjust(a).expect("a conversion");
                    let out = match kind {
                        ConvKind::FixedToSlice | ConvKind::ArrayToSlice => self.slice_of(ty),
                        _ => target.unwrap_or(ty),
                    };
                    let op = self.use_val(v, ty, span);
                    (
                        self.rv_or_temp(Rvalue::Convert(kind, op), out, last, span),
                        out,
                    )
                }
            };
        }
        (v, ty)
    }

    /// C12 (c.6, c.16) on a value that is not an arrow: a local holding a closure
    /// is reborrowed, as C14 passes a closure parameter on; an `fn` value is
    /// held by the env of `closure(fn_value, _e)`; a function name is
    /// `closure(fn f, _e)`, whose env holds a local function's hidden arguments
    /// as captures (A:1360), `&v` or `&*v [closure-capture]`, and is empty else.
    fn to_closure(&mut self, v: Val, ty: Ty, span: enrang_base::Span) -> Val {
        let tcx = self.cx.tcx;
        if let TyKind::Closure(_) = tcx.kind(ty) {
            let p = self.val_place(v, ty, span);
            self.guard(p, span);
            return Val::Rv(Rvalue::ClosureReborrow(p));
        }
        let op = self.use_val(v, ty, span);
        let (func, ops) = match &op {
            Operand::Const(c) => match c.kind {
                ConstKind::Value(ConstValue::FnAddr(f)) => (ClosureFn::Named(f), None),
                _ => (ClosureFn::FnValue, Some(vec![op])),
            },
            _ => (ClosureFn::FnValue, Some(vec![op])),
        };
        let ops = match (func, ops) {
            (_, Some(ops)) => ops,
            (ClosureFn::Named(f), None) => self.hidden_captures(f.def, span),
            _ => Vec::new(),
        };
        let tys: Vec<Ty> = (ops.iter())
            .map(|o| match o {
                Operand::Copy(p) | Operand::Move(p) => self.place_ty(*p),
                Operand::Const(c) => c.ty,
            })
            .collect();
        let kind = match ops.is_empty() {
            true => AggregateKind::Tuple,
            false => AggregateKind::ClosureEnv,
        };
        let env = self.new_temp(tcx.mk_tuple(&tys), span);
        self.assign(env.into(), Rvalue::Aggregate(kind, ops), span);
        Val::Rv(Rvalue::ClosureValue {
            func,
            env: env.into(),
        })
    }

    /// `want` with the wraps of `rest` taken off: the type a step before them
    /// makes.
    fn under_wraps(&self, mut want: Ty, rest: &[Adjust]) -> Ty {
        let tcx = self.cx.tcx;
        for a in rest.iter().rev() {
            want = match (a, tcx.kind(want)) {
                (Adjust::WrapNull | Adjust::WrapNullRef, TyKind::Nullable(t)) => t,
                (Adjust::WrapOk, TyKind::Adt(_, args)) => tcx.list(args)[0],
                _ => want,
            };
        }
        want
    }

    /// An rvalue as the chain's result, left for the destination when it is the
    /// last step, stored into a temporary otherwise.
    fn rv_or_temp(&mut self, rv: Rvalue, ty: Ty, last: bool, span: enrang_base::Span) -> Val {
        if last {
            return Val::Rv(rv);
        }
        let t = self.new_temp(ty, span);
        self.assign(t.into(), rv, span);
        Val::Op(Operand::Move(t.into()))
    }

    /// `v` as a place: a place as it is, anything else in a statement temporary.
    pub(crate) fn val_place(
        &mut self,
        v: Val,
        ty: Ty,
        span: enrang_base::Span,
    ) -> enrang_mir::Place {
        match crate::expr::read(v) {
            Val::Place(p) => p,
            v => self.temp_of(v, ty, span),
        }
    }

    /// `*r` for a reference value `v` of type `ty`.
    fn deref_of(&mut self, v: Val, ty: Ty, span: enrang_base::Span) -> enrang_mir::Place {
        let p = self.val_place(v, ty, span);
        self.body.project(p, Proj::Deref)
    }

    /// C08 (c.6): a `&T | null` read through into a `T | null`.
    fn read_through_nullable(&mut self, v: Val, ty: Ty, span: enrang_base::Span) -> (Val, Ty) {
        let tcx = self.cx.tcx;
        let r = self.val_place(v, ty, span);
        let inner = match tcx.kind(ty) {
            TyKind::Nullable(t) => match tcx.kind(t) {
                TyKind::Ref(i) => i,
                _ => t,
            },
            _ => ty,
        };
        let out = tcx.mk_nullable(inner);
        let d = self.new_temp(out, span);
        let disc = self.new_temp(tcx.common().u32, span);
        self.assign(disc.into(), Rvalue::Discriminant(r), span);
        let (present, null, join) = (self.new_block(), self.new_block(), self.new_block());
        self.terminate(
            enrang_mir::TerminatorKind::Switch {
                value: Operand::Move(disc.into()),
                arms: vec![(0, null)],
                otherwise: Some(present),
            },
            span,
        );
        self.switch_to(present);
        let payload = self.present(r);
        let obj = self.body.project(payload, Proj::Deref);
        let val = self.new_temp(inner, span);
        self.guard(obj, span);
        if self.through(obj) == Some(ClassHolder::Ref) {
            let st = StatementKind::CheckClass {
                place: obj,
                op: ClassOp::CopyOut,
                via: ClassHolder::Ref,
            };
            self.push(st, span);
        }
        self.assign(val.into(), Rvalue::Use(Operand::Copy(obj)), span);
        let wrap = Rvalue::Aggregate(AggregateKind::Present, vec![Operand::Move(val.into())]);
        self.assign(d.into(), wrap, span);
        self.goto(join, span);
        self.switch_to(null);
        self.assign(
            d.into(),
            Rvalue::Aggregate(AggregateKind::Null, Vec::new()),
            span,
        );
        self.goto(join, span);
        self.switch_to(join);
        (Val::Place(d.into()), out)
    }

    /// `&Slice<T>` for a `&T[N]` or `&T[]`.
    fn slice_of(&self, t: Ty) -> Ty {
        let tcx = self.cx.tcx;
        let elem = match tcx.kind(t) {
            TyKind::Ref(i) => match tcx.kind(i) {
                TyKind::Fixed(e, _) | TyKind::Array(e) => e,
                _ => return t,
            },
            _ => return t,
        };
        tcx.mk_ref(tcx.mk_slice(elem))
    }
}

/// `op` with the type `ty`: a constant retyped (a text as a `&string`
/// descriptor, a function name as an `fn` value).
fn retype(op: Operand, ty: Ty) -> Operand {
    match op {
        Operand::Const(mut c) => {
            c.ty = ty;
            Operand::Const(c)
        }
        op => op,
    }
}

/// A constant element of a literal view (c.18): a constant, a constant read, a
/// payload-free case, a nested literal of these.
fn constant(e: &hir::Expr) -> bool {
    match &e.kind {
        K::Const(_) | K::Static(_) => true,
        K::VariantLit { fields, .. } => fields.is_empty(),
        K::ArrayLit(es) => es.iter().all(constant),
        _ => false,
    }
}
