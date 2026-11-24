//! Places and the guard runs (A:943, A:582; M3 plan c.4): `place_of`'s projections,
//! with index operands evaluated where they stand (O6), and [`Builder::guard`],
//! the run of `CheckBounds` and `CheckTag` a place needs directly before the
//! statement that uses it, derived from its projections, so a place built early
//! (a receiver, an assignment target) is guarded where it is used.

use enrang_base::Span;
use enrang_hir::{self as hir, Adjust, ConstValue, DefKind, ExprKind as K, TyKind, VariantIdx};
use enrang_mir::{Operand, Place, Point, Proj, Rvalue, StatementKind};

use crate::builder::Builder;
use crate::expr::Val;

impl Builder<'_> {
    /// The place `e` names, before its adjust chain (c.4). A value expression is
    /// evaluated into a temporary, which is the place.
    pub(crate) fn place_of(&mut self, e: &hir::Expr) -> Place {
        let tcx = self.cx.tcx;
        match &e.kind {
            K::Local(l) => self.local_place(*l),
            K::Field(b, f) => {
                let p = self.adjusted_place(b);
                self.body.project(p, Proj::Field(*f))
            }
            K::Deref(b) if matches!(tcx.kind(b.ty), TyKind::Raw(_)) => {
                let op = self.operand_of(b);
                let t = self.new_temp(b.ty, b.span);
                self.assign(t.into(), Rvalue::Use(op), b.span);
                self.body.place(t, &[Proj::Deref])
            }
            K::Deref(b) => {
                let p = self.adjusted_place(b);
                self.body.project(p, Proj::Deref)
            }
            K::Index(b, i) => {
                let p = self.adjusted_place(b);
                if let (TyKind::Fixed(_, n), K::Const(c)) = (tcx.kind(self.place_ty(p)), &i.kind)
                    && let Some(k) = c.as_i128(tcx).filter(|&k| k >= 0 && (k as u64) < n)
                {
                    return self.body.project(p, Proj::ConstIndex(k as u64));
                }
                let op = self.operand_of(i);
                let isize = tcx.common().isize;
                let t = self.new_temp(isize, i.span);
                let rv = match i.ty == isize {
                    true => Rvalue::Use(op),
                    false => Rvalue::Cast(hir::CastKind::IntToInt, op, isize),
                };
                self.assign(t.into(), rv, i.span);
                self.body.project(p, Proj::Index(t))
            }
            K::NarrowedPayload(b, v, fact) => {
                let p = self.adjusted_place(b);
                let nullable = matches!(tcx.kind(self.place_ty(p)), TyKind::Nullable(_));
                let case = self.body.project(p, Proj::Variant(*v));
                self.facts_of.insert(case, *fact);
                match nullable {
                    true => self.body.project(case, Proj::Field(hir::FieldIdx(0))),
                    false => case,
                }
            }
            K::Static(d) if tcx.def(*d).kind == DefKind::Static => {
                let addr = ConstValue::StaticAddr(*d);
                let ptr = tcx.mk_raw(e.ty);
                let t = self.new_temp(ptr, e.span);
                self.assign(t.into(), Rvalue::Use(Operand::constant(addr, ptr)), e.span);
                self.body.place(t, &[Proj::Deref])
            }
            K::Static(d) => {
                let t = self.new_temp(e.ty, e.span);
                crate::lower_const_read(self, *d, e.ty, t.into(), e.span);
                t.into()
            }
            _ => match self.val(e) {
                Val::Place(p) => p,
                v => {
                    let t = self.new_temp(e.ty, e.span);
                    self.store(t.into(), v, e.span);
                    t.into()
                }
            },
        }
    }

    /// The place `e` names after its adjust chain: each `BoxDeref` of a box adds a
    /// `Deref`; a chain that makes a value (a borrow, a conversion) is evaluated
    /// into a temporary.
    pub(crate) fn adjusted_place(&mut self, e: &hir::Expr) -> Place {
        let boxes = e.adjust.iter().all(|&a| a == Adjust::BoxDeref)
            && matches!(self.cx.tcx.kind(e.ty), TyKind::Boxed(_));
        if boxes {
            let mut p = self.place_of(e);
            for _ in &e.adjust {
                p = self.body.project(p, Proj::Deref);
            }
            return p;
        }
        let (v, ty) = self.adjusted(e, None);
        match crate::expr::read(v) {
            Val::Place(p) => p,
            v => {
                let t = self.new_temp(ty, e.span);
                self.store(t.into(), v, e.span);
                t.into()
            }
        }
    }

    /// Whether `p` needs a guard run: an index or a case projection.
    pub(crate) fn needs_guard(&self, p: Place) -> bool {
        self.body
            .projs(p)
            .iter()
            .any(|x| matches!(x, Proj::Index(_) | Proj::Variant(_)))
    }

    /// The guard run of `p` (c.4), to emit directly before the statement using it:
    /// for each index the `Len` of its base (itself guarded) first, then one run of
    /// `CheckBounds` and `CheckTag` in projection order. A narrowed case's
    /// `CheckTag` is recorded as its fact's use (c.20).
    pub fn guard(&mut self, p: Place, span: Span) {
        let projs = self.body.projs(p).to_vec();
        let mut run = Vec::new();
        for (k, &proj) in projs.iter().enumerate() {
            let base = self.body.place(p.local, &projs[..k]);
            match proj {
                Proj::Index(i) => {
                    self.guard(base, span);
                    let n = self.new_temp(self.cx.tcx.common().isize, span);
                    self.assign(n.into(), Rvalue::Len(base), span);
                    run.push(StatementKind::CheckBounds {
                        index: Operand::Copy(i.into()),
                        len: Operand::Copy(n.into()),
                    });
                }
                Proj::Variant(v) => run.push(StatementKind::CheckTag {
                    place: base,
                    variant: v,
                }),
                _ => {}
            }
        }
        for st in run {
            if let (StatementKind::CheckTag { place, variant }, Some(b)) = (&st, self.cursor) {
                let case = self.body.project(*place, Proj::Variant(*variant));
                if let Some(&fact) = self.facts_of.get(&case) {
                    let at = Point::new(b, self.body.blocks[b].stmts.len());
                    self.body.meta.narrowed_uses.push((fact, at));
                }
            }
            self.push(st, span);
        }
    }

    /// `(p as Present).0` of a nullable place, with its tag check (C08, `!`).
    pub(crate) fn present(&mut self, p: Place) -> Place {
        let case = self.body.project(p, Proj::Variant(VariantIdx::PRESENT));
        self.body.project(case, Proj::Field(hir::FieldIdx(0)))
    }
}
