//! Expressions (M3 plan c.5): each lowered as a place (c.4), an operand or an
//! rvalue not yet stored ([`Val`]), then its adjust chain (c.6), then used: copied,
//! moved, reborrowed (O7) or stored into a destination. 2C's constructs go to
//! their entry points (`matches`, `result`, `spread`, `closure`, `consts`).

use enrang_base::Span;
use enrang_hir::{self as hir, ConstValue, ExprKind as K, LangItem, Ty, TyKind};
use enrang_mir::{
    AggregateKind, BinOp, BorrowOrigin, CheckedOp, ClassHolder, ClassOp, FormCall, IntrinsicKind,
    LocalKind, Operand, Place, Proj, Rvalue, StatementKind, TerminatorKind, UnOp,
};

use crate::builder::Builder;

/// A lowered expression before it is used.
#[derive(Clone, Debug)]
pub(crate) enum Val {
    /// The value lies in this place.
    Place(Place),
    Op(Operand),
    /// An rvalue not yet stored, of the expression's adjusted type.
    Rv(Rvalue),
    /// The place an assignment to a non-Copy place stored into, as its value
    /// (A:942): a use that keeps it moves it, recorded for EN0621; any other use
    /// reads the place.
    Assigned(Place),
}

impl Builder<'_> {
    /// `e` as an operand, its adjust chain applied.
    pub(crate) fn operand_of(&mut self, e: &hir::Expr) -> Operand {
        self.operand_at(e, None)
    }

    /// `e` as an operand, its adjust chain ending at `want` when known.
    pub(crate) fn operand_at(&mut self, e: &hir::Expr, want: Option<Ty>) -> Operand {
        let (v, ty) = self.adjusted_through(e, want);
        self.use_val(v, ty, e.span)
    }

    /// `e` with its adjust chain, an operand of type `&T` where a `T` is wanted read
    /// through: operators see through one reference and carry no adjust (S:684).
    pub(crate) fn adjusted_through(&mut self, e: &hir::Expr, want: Option<Ty>) -> (Val, Ty) {
        let (v, ty) = self.adjusted(e, want);
        match (self.cx.tcx.kind(ty), want) {
            (TyKind::Ref(t), Some(w)) if t == w => {
                let p = match v {
                    Val::Place(p) => p,
                    v => {
                        let r = self.new_temp(ty, e.span);
                        self.store(r.into(), v, e.span);
                        r.into()
                    }
                };
                (Val::Place(self.body.project(p, Proj::Deref)), t)
            }
            _ => (v, ty),
        }
    }

    /// Evaluates `e` into `dest`.
    pub(crate) fn lower_into(&mut self, e: &hir::Expr, dest: Place) {
        if e.adjust.is_empty() && self.lower_raw(e, dest) {
            return;
        }
        let want = self.place_ty(dest);
        let (v, _) = self.adjusted(e, Some(want));
        self.store(dest, v, e.span);
    }

    /// Stores `v` into `dest`: a reborrow's temporary (O7), or a place's guard run
    /// and class check, then its copy or move.
    pub(crate) fn store(&mut self, dest: Place, v: Val, span: Span) {
        let rv = match v {
            Val::Place(p) => match self.reborrow(p, span) {
                Some(op) => Rvalue::Use(op),
                None => {
                    let op = self.read_op(p);
                    self.guard(p, span);
                    self.class_check(p, &op, span);
                    Rvalue::Use(op)
                }
            },
            Val::Op(op) => Rvalue::Use(op),
            Val::Rv(rv) => rv,
            Val::Assigned(p) => return self.move_assigned(dest, p, span),
        };
        self.assign(dest, rv, span);
    }

    /// `v`, of type `ty`, as an operand: a reference local reborrowed (O7), a
    /// guarded place, one needing a class check or a reference-carrying field or
    /// part read into a temporary directly after its run, an rvalue or a kept
    /// assignment value stored into one.
    pub(crate) fn use_val(&mut self, v: Val, ty: Ty, span: Span) -> Operand {
        if let Val::Op(op) = v {
            return op;
        }
        if let Val::Place(p) = v {
            if let Some(op) = self.reborrow(p, span) {
                return op;
            }
            let op = self.read_op(p);
            // A reference read out of a field or part is one `Use(Copy)` into a
            // slot, where phase 3 gives it its loan (A:935); a borrowing value
            // moved out of one is one `Use(Move)` into a slot too, since phase 3
            // reads the sets of an aggregate's, a conversion's or a call's
            // operands from locals only (V09).
            let ref_copy = !p.is_local() && !self.cx.tcx.is_value_type(self.place_ty(p));
            if !self.needs_guard(p) && self.class_op(p, &op).is_none() && !ref_copy {
                return op;
            }
        }
        let ty = match &v {
            Val::Place(p) | Val::Assigned(p) => self.place_ty(*p),
            _ => ty,
        };
        let t = self.new_temp(ty, span);
        self.store(t.into(), v, span);
        Operand::Move(t.into())
    }

    /// `copy p` for a Copy type, `move p` otherwise; a temporary is always moved.
    pub(crate) fn read_op(&self, p: Place) -> Operand {
        match !self.is_temp(p) && self.is_copy(self.place_ty(p)) {
            true => Operand::Copy(p),
            false => Operand::Move(p),
        }
    }

    /// O7: a use of a reference local, `this` or a narrowed reference local's
    /// payload as a value is `_t = &*r [reborrow]`, moved; a temporary is moved, a
    /// field or part copied (`None`).
    fn reborrow(&mut self, p: Place, span: Span) -> Option<Operand> {
        if !matches!(self.cx.tcx.kind(self.place_ty(p)), TyKind::Ref(_)) {
            return None;
        }
        let kind = self.body.locals[p.local].kind;
        let narrowed = match self.body.projs(p) {
            [] => true,
            [
                Proj::Variant(hir::VariantIdx::PRESENT),
                Proj::Field(hir::FieldIdx(0)),
            ] => {
                matches!(
                    self.cx.tcx.kind(self.body.locals[p.local].ty),
                    TyKind::Nullable(_)
                )
            }
            _ => false,
        };
        if matches!(kind, LocalKind::Temp | LocalKind::ClosureEnv) || !narrowed {
            return None;
        }
        self.guard(p, span);
        let place = self.body.project(p, Proj::Deref);
        let t = self.new_temp(self.place_ty(p), span);
        let rv = Rvalue::Ref {
            place,
            origin: BorrowOrigin::Reborrow,
        };
        self.assign(t.into(), rv, span);
        Some(Operand::Move(t.into()))
    }

    /// The exact-class event of reading `p` with `op` (A:943): a whole-object copy
    /// out through a reference, or a move out of a box, of a class that can be
    /// extended or a type parameter.
    pub(crate) fn class_op(&self, p: Place, op: &Operand) -> Option<(ClassOp, ClassHolder)> {
        let via = self.through(p)?;
        match (op, via) {
            (Operand::Copy(_), _) => Some((ClassOp::CopyOut, via)),
            (Operand::Move(_), ClassHolder::Box) => Some((ClassOp::Unbox, via)),
            _ => None,
        }
    }

    /// `ClassHolder` of `p`'s last `Deref` when `p` is a whole object of a class
    /// that can be extended, or of a type parameter, reached through it.
    pub(crate) fn through(&self, p: Place) -> Option<ClassHolder> {
        let tcx = self.cx.tcx;
        let projs = self.body.projs(p);
        if projs.last() != Some(&Proj::Deref) || !self.extensible(self.place_ty(p)) {
            return None;
        }
        let mut pt = enrang_mir::PlaceTy::of(self.body.locals[p.local].ty);
        for &x in &projs[..projs.len() - 1] {
            pt = pt.project(tcx, x)?;
        }
        match tcx.kind(pt.ty) {
            TyKind::Ref(_) => Some(ClassHolder::Ref),
            TyKind::Boxed(_) => Some(ClassHolder::Box),
            _ => None,
        }
    }

    /// A class that can be extended, or a type parameter (A:943).
    pub(crate) fn extensible(&self, t: Ty) -> bool {
        let tcx = self.cx.tcx;
        match tcx.kind(t) {
            TyKind::Param(_) => true,
            TyKind::Adt(adt, _) => tcx
                .adt(adt)
                .as_class()
                .is_some_and(|c| c.modifier != hir::ClassModifier::Final),
            _ => false,
        }
    }

    /// Emits `check_class(p, op, via)` for the exact-class event of reading `p`.
    pub(crate) fn class_check(&mut self, p: Place, op: &Operand, span: Span) {
        if let Some((op, via)) = self.class_op(p, op) {
            self.push(StatementKind::CheckClass { place: p, op, via }, span);
        }
    }

    /// Lowers `e` before its adjust chain.
    pub(crate) fn val(&mut self, e: &hir::Expr) -> Val {
        let tcx = self.cx.tcx;
        match &e.kind {
            K::Local(_)
            | K::Field(..)
            | K::Deref(_)
            | K::Index(..)
            | K::NarrowedPayload(..)
            | K::Static(_) => Val::Place(self.place_of(e)),
            K::NonNull(x) => Val::Place(crate::lower_non_null(self, x)),
            K::Assign { .. } | K::IncDec { .. } => self.lower_assign(e, true),
            K::Const(c) => Val::Op(Operand::constant(*c, e.ty)),
            K::NullLit => Val::Rv(Rvalue::Aggregate(AggregateKind::Null, Vec::new())),
            K::Try(x, kind) => Val::Op(crate::lower_try(self, x, *kind)),
            K::ArrayLit(es) => match tcx.kind(e.ty) {
                TyKind::Fixed(t, _) => {
                    let ops = self.operands(es.iter().map(|x| (x, Some(t))));
                    Val::Rv(Rvalue::Aggregate(AggregateKind::Fixed(t), ops))
                }
                _ => self.in_temp(e),
            },
            K::Repeat(x, n) => {
                let elem = match tcx.kind(e.ty) {
                    TyKind::Fixed(t, _) => Some(t),
                    _ => None,
                };
                let op = self.operand_at(x, elem);
                Val::Rv(Rvalue::Aggregate(AggregateKind::Repeat(*n), vec![op]))
            }
            K::TupleLit(es) => {
                let parts = match tcx.kind(e.ty) {
                    TyKind::Tuple(l) => tcx.list(l).to_vec(),
                    _ => Vec::new(),
                };
                let ops = self.operands(es.iter().zip(parts.iter().map(|&t| Some(t))));
                Val::Rv(Rvalue::Aggregate(AggregateKind::Tuple, ops))
            }
            K::ObjectLit {
                shape,
                fields,
                eval,
            } => {
                let shape = match tcx.kind(e.ty) {
                    TyKind::Object(s) => s,
                    _ => *shape,
                };
                let tys: Vec<Option<Ty>> =
                    tcx.shape(shape).fields.iter().map(|f| Some(f.1)).collect();
                let ops = self.operands_in(fields, &tys, eval);
                Val::Rv(Rvalue::Aggregate(AggregateKind::Object(shape), ops))
            }
            K::VariantLit {
                adt,
                variant,
                args,
                fields,
                eval,
            } => {
                let tys: Vec<Option<Ty>> = (0..fields.len())
                    .map(|f| {
                        Some(tcx.field_ty(*adt, Some(*variant), hir::FieldIdx(f as u32), *args))
                    })
                    .collect();
                let ops = self.operands_in(fields, &tys, eval);
                let kind = AggregateKind::Adt {
                    adt: *adt,
                    variant: Some(*variant),
                    args: *args,
                };
                Val::Rv(Rvalue::Aggregate(kind, ops))
            }
            K::Unary(op, x) => {
                let t = pointee(tcx, x.ty);
                let o = self.operand_at(x, Some(t));
                Val::Rv(match (op, tcx.kind(t)) {
                    (hir::UnOp::Neg, TyKind::Int(_)) => Rvalue::CheckedNeg(o),
                    (hir::UnOp::Neg, _) => Rvalue::Unary(UnOp::Neg, o),
                    (hir::UnOp::Not, _) => Rvalue::Unary(UnOp::Not, o),
                    (hir::UnOp::BitNot, _) => Rvalue::Unary(UnOp::BitNot, o),
                })
            }
            K::Binary(op, a, b) => self.binary(e, *op, a, b),
            K::Cast(x, k) => {
                let through = *k != hir::CastKind::RefToRaw;
                let o = self.operand_at(x, through.then(|| pointee(tcx, x.ty)));
                Val::Rv(Rvalue::Cast(*k, o, e.ty))
            }
            // `&CONST` names the constant's static: a reference with an empty
            // loan set and the top-level `const` mark (S:756, A:970, c.18).
            K::Borrow(x)
                if x.adjust.is_empty()
                    && matches!(x.kind, K::Static(d) if tcx.def(d).kind == hir::DefKind::Const)
                    && !matches!(tcx.kind(x.ty), TyKind::Ref(_)) =>
            {
                let K::Static(d) = x.kind else {
                    unreachable!("a constant")
                };
                Val::Op(Operand::constant(ConstValue::StaticAddr(d), e.ty))
            }
            K::Borrow(x) => {
                let (p, origin) = self.borrowed(x);
                self.borrow_class_check(e.id, p, e.span);
                Val::Rv(Rvalue::Ref { place: p, origin })
            }
            K::AddrOf(x) => {
                let p = self.adjusted_place(x);
                self.guard(p, x.span);
                Val::Rv(Rvalue::AddrOf(p))
            }
            _ => self.in_temp(e),
        }
    }

    /// `e`, of a kind that writes a destination, lowered into a temporary.
    fn in_temp(&mut self, e: &hir::Expr) -> Val {
        let t = self.new_temp(e.ty, e.span);
        if !self.lower_raw(e, t.into()) {
            unreachable!("a value expression lowers into its destination");
        }
        Val::Place(t.into())
    }

    /// Lowers `e`, ignoring its adjust chain, into `dest` when its kind writes a
    /// destination itself; false for the kinds [`Builder::val`] lowers.
    pub(crate) fn lower_raw(&mut self, e: &hir::Expr, dest: Place) -> bool {
        let span = e.span;
        match &e.kind {
            K::ArrayLit(es) if !matches!(self.cx.tcx.kind(e.ty), TyKind::Fixed(..)) => {
                let TyKind::Array(t) = self.cx.tcx.kind(e.ty) else {
                    return false;
                };
                let args = self.operands(es.iter().map(|x| (x, Some(t))));
                let kind = IntrinsicKind::AllocArray(t);
                self.intrinsic(kind, args, dest, span);
            }
            K::Call { .. } => {
                self.lower_call(e, dest);
            }
            K::New { .. } | K::NewNamed { .. } => {
                self.lower_new(e, dest);
            }
            K::Logical(op, a, b) => self.logical(*op, a, b, dest, span),
            K::Ternary(c, a, b) => {
                let (then_, else_) = (self.new_block(), self.new_block());
                self.cond_to(c, then_, else_);
                let join = self.new_block();
                for (block, arm) in [(then_, a), (else_, b)] {
                    self.switch_to(block);
                    self.lower_into(arm, dest);
                    self.goto(join, span);
                }
                self.switch_to(join);
            }
            K::Template(parts) => {
                let args = self.template_args(parts);
                self.form_call(FormCall::Template, args, dest, span);
            }
            K::Match { subject, arms } => crate::lower_match(self, subject, arms, dest, span),
            K::Coalesce(a, d) => crate::lower_coalesce(self, a, d, dest),
            K::OptionalChain(c) => crate::lower_opt_chain(self, c, dest, span),
            K::ArrayBuild { elem, parts } => {
                crate::lower_array_build(self, *elem, parts, dest, span)
            }
            K::Arrow(a) => crate::lower_arrow_value(self, *a, dest, span),
            K::Destructure { pat, value } => {
                crate::lower_destructure(self, pat, hir::BindingMode::Owned, value);
            }
            K::Asm(a) => {
                self.asm(a);
            }
            K::VoidOp(x) => {
                self.discard(x);
            }
            K::Never => self.terminate(TerminatorKind::Unreachable, span),
            _ => return false,
        }
        true
    }

    /// Evaluates `e` for its effects into a temporary that drops at the end of the
    /// statement (`void e`, an expression statement).
    pub(crate) fn discard(&mut self, e: &hir::Expr) {
        let t = self.new_temp(e.ty, e.span);
        self.lower_into(e, t.into());
    }

    /// The operands of `es`, left to right (O6): a place read later stays a place
    /// only while every later operand is free of effects.
    pub(crate) fn operands<'e>(
        &mut self,
        es: impl IntoIterator<Item = (&'e hir::Expr, Option<Ty>)>,
    ) -> Vec<Operand> {
        let es: Vec<(&hir::Expr, Option<Ty>)> = es.into_iter().collect();
        let mut out = Vec::with_capacity(es.len());
        for (i, &(e, want)) in es.iter().enumerate() {
            let (v, ty) = self.adjusted_through(e, want);
            let later_pure = es[i + 1..].iter().all(|(x, _)| pure(x));
            let op = match v {
                Val::Place(p) if !later_pure => {
                    let op = self.use_val(Val::Place(p), ty, e.span);
                    self.materialize(op, ty, e.span)
                }
                v => self.use_val(v, ty, e.span),
            };
            if let Operand::Move(p) = op
                && self.is_temp(p)
            {
                self.note(e.id, p.local);
            }
            out.push(op);
        }
        out
    }

    /// The operands of `es`, typed `tys`, evaluated in the order `eval` lists their
    /// indices, then the rest in their own order (O6), and given back in their own
    /// order: an object literal's values as written, its aggregate in shape order.
    fn operands_in(&mut self, es: &[hir::Expr], tys: &[Option<Ty>], eval: &[u32]) -> Vec<Operand> {
        let mut order: Vec<usize> = (eval.iter())
            .map(|&i| i as usize)
            .filter(|&i| i < es.len())
            .collect();
        order.extend((0..es.len()).filter(|i| !eval.contains(&(*i as u32))));
        let ops = self.operands(
            order
                .iter()
                .map(|&i| (&es[i], tys.get(i).copied().flatten())),
        );
        let mut out: Vec<Option<Operand>> = vec![None; es.len()];
        for (i, op) in order.into_iter().zip(ops) {
            out[i] = Some(op);
        }
        out.into_iter()
            .map(|op| op.expect("each operand once"))
            .collect()
    }

    /// `op` in a temporary, unless it already is one or a constant.
    pub(crate) fn materialize(&mut self, op: Operand, ty: Ty, span: Span) -> Operand {
        match &op {
            Operand::Const(_) => op,
            Operand::Move(p) | Operand::Copy(p) if self.is_temp(*p) => op,
            _ => {
                let t = self.new_temp(ty, span);
                self.assign(t.into(), Rvalue::Use(op), span);
                Operand::Move(t.into())
            }
        }
    }

    /// The place `&x` borrows and its origin: a place `[explicit]`, an rvalue in a
    /// statement temporary `[temp-arg]` (c.5).
    pub(crate) fn borrowed(&mut self, x: &hir::Expr) -> (Place, BorrowOrigin) {
        let (v, ty) = self.adjusted(x, None);
        match read(v) {
            Val::Place(p) if !self.is_temp(p) => {
                self.guard(p, x.span);
                (p, BorrowOrigin::Explicit)
            }
            v => (self.temp_of(v, ty, x.span), BorrowOrigin::TempArg),
        }
    }

    /// `v` in a statement temporary that lives to the end of the statement.
    pub(crate) fn temp_of(&mut self, v: Val, ty: Ty, span: Span) -> Place {
        let t = match v {
            Val::Place(p) if self.is_temp(p) => p.local,
            v => {
                let t = self.new_temp(ty, span);
                self.store(t.into(), v, span);
                t
            }
        };
        self.scope_local(t);
        t.into()
    }

    pub(crate) fn is_temp(&self, p: Place) -> bool {
        p.is_local() && self.body.locals[p.local].kind == LocalKind::Temp
    }

    /// A binary operator (c.5): checked integer arithmetic, wrapping bitwise and
    /// float operations, comparisons through a common type (b.4), `string +
    /// string` as `Concat`, `==` and `<` on other types through `Eq` and `Ord`.
    fn binary(&mut self, e: &hir::Expr, op: hir::BinOp, a: &hir::Expr, b: &hir::Expr) -> Val {
        use hir::BinOp as B;
        let tcx = self.cx.tcx;
        let (ta, tb) = (pointee(tcx, a.ty), pointee(tcx, b.ty));
        let (ka, kb) = (tcx.kind(ta), tcx.kind(tb));
        let cmp = matches!(op, B::Lt | B::Le | B::Gt | B::Ge | B::Eq | B::Ne);
        if op == B::Add && ka == TyKind::Str {
            let args = vec![self.shared_arg(a), self.shared_arg(b)];
            let d = self.new_temp(e.ty, e.span);
            self.form_call(FormCall::Concat, args, d.into(), e.span);
            return Val::Place(d.into());
        }
        if cmp && !scalar(tcx, ta) {
            return self.compare_call(e, op, a, b);
        }
        let ops = self.operands([(a, Some(ta)), (b, Some(tb))]);
        let [x, y]: [Operand; 2] = ops.try_into().expect("two operands");
        if let (true, TyKind::Int(ia), TyKind::Int(ib)) = (cmp, ka, kb)
            && ia != ib
        {
            return self.mixed_compare(e, op, (x, ia), (y, ib));
        }
        Val::Rv(arith(op, matches!(ka, TyKind::Int(_)), x, y))
    }

    /// A comparison of two integer types: both widened to the narrowest type
    /// holding both ranges; a signed 64-bit value against an unsigned one tests
    /// the sign first (b.4, A:941).
    fn mixed_compare(
        &mut self,
        e: &hir::Expr,
        op: hir::BinOp,
        (x, ia): (Operand, hir::IntTy),
        (y, ib): (Operand, hir::IntTy),
    ) -> Val {
        let tcx = self.cx.tcx;
        let ptr = tcx.target().layout.ptr_bytes * 8;
        let (wa, wb) = (ia.bits(ptr), ib.bits(ptr));
        let common = match (ia.is_signed(), ib.is_signed()) {
            (true, true) | (false, false) => Some(if wa >= wb { ia } else { ib }),
            (s, _) => {
                let (signed, sw, uw) = if s { (ia, wa, wb) } else { (ib, wb, wa) };
                match sw > uw {
                    true => Some(signed),
                    false => [hir::IntTy::I16, hir::IntTy::I32, hir::IntTy::I64]
                        .into_iter()
                        .find(|t| t.bits(ptr) > uw),
                }
            }
        };
        let w = binop(op);
        let cast = |b: &mut Self, o: Operand, from: hir::IntTy, to: hir::IntTy| {
            if from == to {
                return o;
            }
            let t = tcx.common().int(to);
            let d = b.new_temp(t, e.span);
            b.assign(
                d.into(),
                Rvalue::Cast(hir::CastKind::IntToInt, o, t),
                e.span,
            );
            Operand::Move(d.into())
        };
        if let Some(c) = common {
            let (x, y) = (cast(self, x, ia, c), cast(self, y, ib, c));
            return Val::Rv(Rvalue::Binary(w, x, y));
        }
        // A signed value below zero is below every unsigned one.
        let (signed, s_ty) = if ia.is_signed() { (&x, ia) } else { (&y, ib) };
        let bool_ty = tcx.common().bool;
        let neg = self.new_temp(bool_ty, e.span);
        let zero = Operand::constant(
            ConstValue::Int(0, tcx.common().int(s_ty)),
            tcx.common().int(s_ty),
        );
        self.assign(
            neg.into(),
            Rvalue::Binary(BinOp::Lt, signed.clone(), zero),
            e.span,
        );
        let d = self.new_temp(bool_ty, e.span);
        let (yes, no, join) = (self.new_block(), self.new_block(), self.new_block());
        self.switch_bool(Operand::Move(neg.into()), yes, no, e.span);
        self.switch_to(yes);
        let signed_first = ia.is_signed();
        let result = match w {
            BinOp::Ne => true,
            BinOp::Eq => false,
            BinOp::Lt | BinOp::Le => signed_first,
            _ => !signed_first,
        };
        self.assign(
            d.into(),
            Rvalue::Use(Operand::constant(ConstValue::Bool(result), bool_ty)),
            e.span,
        );
        self.goto(join, e.span);
        self.switch_to(no);
        let u = if ia.is_signed() { ib } else { ia };
        let (x, y) = (cast(self, x, ia, u), cast(self, y, ib, u));
        self.assign(d.into(), Rvalue::Binary(w, x, y), e.span);
        self.goto(join, e.span);
        self.switch_to(join);
        Val::Place(d.into())
    }

    /// `==` and `!=` on other types (c.5, A:1358): against `null`, a test of the
    /// tag; else the operand type's `equals` member (the `Eq` interface's when it
    /// has none written) on two shared borrows.
    fn compare_call(&mut self, e: &hir::Expr, op: hir::BinOp, a: &hir::Expr, b: &hir::Expr) -> Val {
        let tcx = self.cx.tcx;
        let bool_ty = tcx.common().bool;
        let w = binop(op);
        if let Some(x) = [(a, b), (b, a)]
            .into_iter()
            .find_map(|(x, n)| matches!(n.kind, K::NullLit).then_some(x))
        {
            // A reference to a nullable (`a: &(T | null)`) is tested through: the
            // tag is the referent's, as `*a == null` tests it.
            let mut p = self.adjusted_place(x);
            while matches!(tcx.kind(self.place_ty(p)), TyKind::Ref(_)) {
                p = self.body.project(p, Proj::Deref);
            }
            self.guard(p, x.span);
            let u32_ = tcx.common().u32;
            let d = self.new_temp(u32_, e.span);
            self.assign(d.into(), Rvalue::Discriminant(p), e.span);
            let null = Operand::constant(ConstValue::Int(0, u32_), u32_);
            return Val::Rv(Rvalue::Binary(w, Operand::Move(d.into()), null));
        }
        let args = vec![self.shared_arg(a), self.shared_arg(b)];
        let d = self.new_temp(bool_ty, e.span);
        let name = enrang_base::intern("equals");
        let found = tcx
            .member(a.ty, name, self.module())
            .and_then(|m| match m.kind {
                hir::MemberKind::Methods(ms) => ms.first().map(|f| hir::FnRef {
                    def: f.def,
                    args: f.args,
                }),
                hir::MemberKind::Field { .. } => None,
            });
        let eq_member = || {
            let adt = tcx.lang_adt(LangItem::Eq)?;
            let def = *tcx.adt(adt).as_interface()?.methods.first()?;
            Some(hir::FnRef {
                def,
                args: tcx.intern_list(&[a.ty]),
            })
        };
        let Some(f) = found.or_else(eq_member) else {
            return Val::Op(Operand::constant(ConstValue::Bool(false), bool_ty));
        };
        self.call(enrang_mir::Callee::Fn(f), args, d.into(), e.span);
        let r = Operand::Move(d.into());
        Val::Rv(match op {
            hir::BinOp::Ne => Rvalue::Unary(UnOp::Not, r),
            _ => Rvalue::Use(r),
        })
    }

    /// The module of the body's owner.
    pub(crate) fn module(&self) -> hir::ModuleId {
        match self.hir.owner {
            hir::BodyOwner::Statements(m) => m,
            hir::BodyOwner::Fn(d) | hir::BodyOwner::Const(d) | hir::BodyOwner::Test(d) => {
                self.cx.tcx.def(d).module
            }
        }
    }

    /// `a && b`, `a || b` into `dest`: `a`, a switch, `b` in its own temporary
    /// scope (D2).
    /// `a && b` and `a || b`: `a` into a temporary, then `dest` stored once on
    /// each path, from the temporary where `a` decides and from `b` where it does
    /// not, so a `const` destination is assigned exactly once (EN0613).
    fn logical(&mut self, op: hir::LogOp, a: &hir::Expr, b: &hir::Expr, dest: Place, span: Span) {
        let t = Place::local(self.new_temp(self.cx.tcx.common().bool, a.span));
        self.lower_into(a, t);
        let (rhs, short, join) = (self.new_block(), self.new_block(), self.new_block());
        let (then_, else_) = match op {
            hir::LogOp::And => (rhs, short),
            hir::LogOp::Or => (short, rhs),
        };
        self.switch_bool(Operand::Copy(t), then_, else_, span);
        match op {
            hir::LogOp::And => self.fact_tests(a, rhs, crate::stmt::NONE),
            hir::LogOp::Or => self.fact_tests(a, crate::stmt::NONE, rhs),
        }
        self.switch_to(short);
        self.assign(dest, Rvalue::Use(Operand::Copy(t)), span);
        self.goto(join, span);
        self.switch_to(rhs);
        self.in_temps(b.span, |s| s.lower_into(b, dest));
        self.goto(join, span);
        self.switch_to(join);
    }

    /// `switch op [0: else_, otherwise: then_]` (b.4).
    pub(crate) fn switch_bool(
        &mut self,
        op: Operand,
        then_: enrang_mir::BlockId,
        else_: enrang_mir::BlockId,
        span: Span,
    ) {
        self.terminate(
            TerminatorKind::Switch {
                value: op,
                arms: vec![(0, else_)],
                otherwise: Some(then_),
            },
            span,
        );
    }

    /// A shared borrow of an argument of a form, a template hole or an operand
    /// of `Concat`, `Eq` or `Ord` (A:977): a reference passes as itself (O7), a
    /// place is auto-borrowed, an rvalue borrowed in a statement temporary.
    pub(crate) fn shared_arg(&mut self, e: &hir::Expr) -> Operand {
        let (v, ty) = self.adjusted(e, None);
        if matches!(self.cx.tcx.kind(ty), TyKind::Ref(_)) {
            return self.use_val(v, ty, e.span);
        }
        let (place, origin) = match read(v) {
            // A packed field is copied to a temporary first (A:977).
            Val::Place(p) if !self.is_temp(p) && crate::tests_forms::packed(self, p) => {
                self.guard(p, e.span);
                let v = Val::Op(Operand::Copy(p));
                (self.temp_of(v, ty, e.span), BorrowOrigin::TempArg)
            }
            Val::Place(p) if !self.is_temp(p) => {
                self.guard(p, e.span);
                (p, BorrowOrigin::AutoBorrow)
            }
            v => (self.temp_of(v, ty, e.span), BorrowOrigin::TempArg),
        };
        let t = self.new_temp(self.cx.tcx.mk_ref(ty), e.span);
        self.assign(t.into(), Rvalue::Ref { place, origin }, e.span);
        Operand::Move(t.into())
    }

    /// A template's arguments (c.5): text parts as `&string` constants, holes as
    /// shared borrows.
    pub(crate) fn template_args(&mut self, parts: &[hir::TplPart]) -> Vec<Operand> {
        let tcx = self.cx.tcx;
        let text = tcx.mk_ref(tcx.common().str);
        parts
            .iter()
            .map(|p| match p {
                hir::TplPart::Text(s) => Operand::constant(ConstValue::Str(*s), text),
                hir::TplPart::Hole(e) => self.shared_arg(e),
            })
            .collect()
    }

    /// An `asm` statement in an `Asm` region nested in the current one (c.5).
    fn asm(&mut self, a: &hir::HirAsm) {
        let ins: Vec<(enrang_base::Symbol, Operand)> = a
            .ins
            .iter()
            .map(|(n, e)| (*n, self.operand_of(e)))
            .collect();
        let outs: Vec<(enrang_base::Symbol, Option<Place>)> = a
            .outs
            .iter()
            .map(|(n, e)| (*n, e.as_ref().map(|e| self.adjusted_place(e))))
            .collect();
        let outer = self.region;
        self.region = Some(self.new_region(enrang_mir::UnsafeKind::Asm, a.span));
        let st = enrang_mir::AsmStmt {
            template: a.template,
            ins,
            outs,
            clobbers: a.clobbers.clone(),
        };
        self.push(StatementKind::Asm(Box::new(st)), a.span);
        self.region = outer;
    }
}

/// `v` where a use reads it without keeping it: an assignment's value is the
/// place assigned (A:942).
pub(crate) fn read(v: Val) -> Val {
    match v {
        Val::Assigned(p) => Val::Place(p),
        v => v,
    }
}

/// An expression whose evaluation has no effect, so an earlier operand may read
/// its place after it.
pub(crate) fn pure(e: &hir::Expr) -> bool {
    match &e.kind {
        K::Local(_) | K::Const(_) | K::Static(_) | K::NullLit => true,
        K::Field(b, _) | K::Deref(b) | K::NarrowedPayload(b, ..) | K::Cast(b, _) | K::Borrow(b) => {
            pure(b)
        }
        K::Unary(_, b) => pure(b),
        _ => false,
    }
}

/// What an operator's operand acts on: `T` for a `&T` (S:684), else the type.
pub(crate) fn pointee(tcx: &hir::Tcx, t: Ty) -> Ty {
    match tcx.kind(t) {
        TyKind::Ref(x) => x,
        _ => t,
    }
}

/// A type `==` and `<` compare directly: numbers, `bool`, raw pointers, `fn`
/// pointers, payload-free enums.
fn scalar(tcx: &hir::Tcx, t: Ty) -> bool {
    match tcx.kind(t) {
        TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Raw(_) | TyKind::FnPtr(..) => {
            true
        }
        TyKind::Adt(adt, _) => {
            !tcx.is_lang_adt(adt, LangItem::Result)
                && tcx.adt(adt).as_enum().is_some_and(|e| e.is_payload_free())
        }
        TyKind::Error | TyKind::Never => true,
        _ => false,
    }
}

/// `x op y`: checked on integers for `+ - * / %` and shifts (S 9.2), wrapping
/// otherwise (c.5).
pub(crate) fn arith(op: hir::BinOp, int: bool, x: Operand, y: Operand) -> Rvalue {
    use hir::BinOp as B;
    let checked = match op {
        B::Add if int => Some(CheckedOp::Add),
        B::Sub if int => Some(CheckedOp::Sub),
        B::Mul if int => Some(CheckedOp::Mul),
        B::Div if int => Some(CheckedOp::Div),
        B::Rem if int => Some(CheckedOp::Rem),
        B::Shl if int => Some(CheckedOp::Shl),
        B::Shr if int => Some(CheckedOp::Shr),
        _ => None,
    };
    match checked {
        Some(c) => Rvalue::Checked(c, x, y),
        None => Rvalue::Binary(binop(op), x, y),
    }
}

/// The wrapping MIR operator of a HIR one.
fn binop(op: hir::BinOp) -> BinOp {
    use hir::BinOp as B;
    match op {
        B::Mul => BinOp::Mul,
        B::Div => BinOp::Div,
        B::Rem => BinOp::Rem,
        B::Add => BinOp::Add,
        B::Sub => BinOp::Sub,
        B::Shl => BinOp::Shl,
        B::Shr => BinOp::Shr,
        B::Lt => BinOp::Lt,
        B::Le => BinOp::Le,
        B::Gt => BinOp::Gt,
        B::Ge => BinOp::Ge,
        B::Eq => BinOp::Eq,
        B::Ne => BinOp::Ne,
        B::BitAnd => BinOp::BitAnd,
        B::BitXor => BinOp::BitXor,
        B::BitOr => BinOp::BitOr,
    }
}
