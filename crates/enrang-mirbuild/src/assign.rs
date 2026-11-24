//! Assignments (D3, A:942, A:934; M3 plan c.8): the target's operands first, the
//! right side, then the old value's `Drop` and the store, each with the target's
//! own guard run; compound assignment, `++` and `--`; the value an assignment
//! leaves, and the EN0621 record of a use that would keep it.

use enrang_base::Span;
use enrang_hir::{self as hir, ConstValue, ExprKind as K, Ty, TyKind};
use enrang_mir::{
    BorrowOrigin, ClassOp, DropOrigin, FormCall, Operand, Place, Point, Rvalue, StatementKind,
};

use crate::builder::Builder;
use crate::expr::Val;

impl Builder<'_> {
    /// Lowers an assignment, compound assignment, `++` or `--`, returning the value
    /// it leaves when `value` (S:518): a temporary for a Copy place, the place
    /// itself, read after the store, for another (`Val::Assigned`).
    pub(crate) fn lower_assign(&mut self, e: &hir::Expr, value: bool) -> Val {
        let span = e.span;
        let void = Val::Op(Operand::constant(
            ConstValue::Void,
            self.cx.tcx.common().void,
        ));
        match &e.kind {
            K::Assign {
                op: None,
                target,
                value: v,
            } => {
                let x = self.place_of(target);
                let ty = self.place_ty(x);
                let id = v.id;
                let (v, _) = self.adjusted(v, Some(ty));
                let keep = value && self.is_copy(ty);
                let drops = self.cx.tcx.needs_drop(ty);
                let (store, kept) = match (keep || drops || self.needs_guard(x), v) {
                    (true, v) => {
                        let op = self.use_val(v, ty, span);
                        let op = self.materialize(op, ty, span);
                        match keep {
                            true => (Rvalue::Use(copy_of(&op)), Some(op)),
                            false => (Rvalue::Use(op), None),
                        }
                    }
                    (false, Val::Rv(rv)) => (rv, None),
                    (false, v) => (Rvalue::Use(self.use_val(v, ty, span)), None),
                };
                if drops {
                    self.drop_old(x, span);
                }
                self.write(x, store, span);
                if x.is_local() {
                    self.note(id, x.local);
                }
                match (value, kept) {
                    (_, Some(op)) => Val::Op(op),
                    (true, None) => Val::Assigned(x),
                    (false, None) => void,
                }
            }
            K::Assign {
                op: Some(op),
                target,
                value: v,
            } => {
                let x = self.place_of(target);
                let ty = self.place_ty(x);
                if !self.is_copy(ty) {
                    self.append(x, v, span);
                    return if value { Val::Assigned(x) } else { void };
                }
                let old = self.read_old(x, span);
                let rhs = self.operand_at(v, Some(crate::expr::pointee(self.cx.tcx, v.ty)));
                self.compound(x, *op, old, rhs, value, span).unwrap_or(void)
            }
            K::IncDec {
                target,
                inc,
                prefix,
            } => {
                let x = self.place_of(target);
                let ty = self.place_ty(x);
                let old = self.read_old(x, span);
                let one = Operand::constant(one(self.cx.tcx, ty), ty);
                let op = if *inc {
                    hir::BinOp::Add
                } else {
                    hir::BinOp::Sub
                };
                let new = self.compound(x, op, old.clone(), one, value && *prefix, span);
                match (value, *prefix) {
                    (true, true) => new.unwrap_or(void),
                    (true, false) => Val::Op(old),
                    (false, _) => void,
                }
            }
            _ => unreachable!("an assignment"),
        }
    }

    /// The old value of a Copy place, read into a temporary with its own guard run
    /// (O6), as `copy _old`.
    fn read_old(&mut self, x: Place, span: Span) -> Operand {
        let t = self.new_temp(self.place_ty(x), span);
        self.store(t.into(), Val::Place(x), span);
        Operand::Copy(t.into())
    }

    /// `x = old <op> rhs` with the store's guard run; the new value in a temporary
    /// when it is the expression's value.
    fn compound(
        &mut self,
        x: Place,
        op: hir::BinOp,
        old: Operand,
        rhs: Operand,
        value: bool,
        span: Span,
    ) -> Option<Val> {
        let ty = self.place_ty(x);
        let int = matches!(self.cx.tcx.kind(ty), TyKind::Int(_));
        let rv = crate::expr::arith(op, int, old, rhs);
        if !value {
            self.write(x, rv, span);
            return None;
        }
        let n = self.new_temp(ty, span);
        self.assign(n.into(), rv, span);
        self.write(x, Rvalue::Use(Operand::Copy(n.into())), span);
        Some(Val::Op(Operand::Move(n.into())))
    }

    /// `s += v` on a place that is not Copy (c.8): `_p = &s [compound-target]`
    /// after the target's operands and run, the right side, then `Append`.
    fn append(&mut self, x: Place, v: &hir::Expr, span: Span) {
        let tcx = self.cx.tcx;
        self.guard(x, span);
        let p = self.new_temp(tcx.mk_ref(self.place_ty(x)), span);
        let rv = Rvalue::Ref {
            place: x,
            origin: BorrowOrigin::CompoundTarget,
        };
        self.assign(p.into(), rv, span);
        let r = self.shared_arg(v);
        let d = self.new_temp(tcx.common().void, span);
        self.form_call(
            FormCall::Append,
            vec![Operand::Move(p.into()), r],
            d.into(),
            span,
        );
    }

    /// `drop(x) [assign]`, after `x`'s run and class check (D3).
    pub(crate) fn drop_old(&mut self, x: Place, span: Span) {
        self.guard(x, span);
        self.assign_check(x, span);
        self.push(StatementKind::Drop(x, DropOrigin::Assign), span);
    }

    /// The store `x = rv`, after `x`'s run and class check.
    pub(crate) fn write(&mut self, x: Place, rv: Rvalue, span: Span) {
        self.guard(x, span);
        self.assign_check(x, span);
        self.assign(x, rv, span);
    }

    /// `check_class(x, assign, via)` for a whole object written through a
    /// reference or box (A:943).
    fn assign_check(&mut self, x: Place, span: Span) {
        if let Some(via) = self.through(x) {
            let st = StatementKind::CheckClass {
                place: x,
                op: ClassOp::Assign,
                via,
            };
            self.push(st, span);
        }
    }

    /// The move of an assignment's kept value `x` into `dest` (A:942): recorded
    /// for the move check, which reports EN0621 instead of moving.
    pub(crate) fn move_assigned(&mut self, dest: Place, x: Place, span: Span) {
        if let Some(b) = self.cursor {
            let at = Point::new(b, self.body.blocks[b].stmts.len());
            self.body.meta.assign_values.push(at);
        }
        self.assign(dest, Rvalue::Use(Operand::Move(x)), span);
    }
}

/// A copy of a temporary's operand, which the store copies and the value moves.
fn copy_of(op: &Operand) -> Operand {
    match op {
        Operand::Move(p) => Operand::Copy(*p),
        op => op.clone(),
    }
}

/// `1` of an integer or float type.
fn one(tcx: &hir::Tcx, ty: Ty) -> ConstValue {
    match tcx.kind(ty) {
        TyKind::Float(hir::FloatTy::F32) => ConstValue::Float(u64::from(1f32.to_bits()), ty),
        TyKind::Float(_) => ConstValue::Float(1f64.to_bits(), ty),
        _ => ConstValue::Int(1, ty),
    }
}
