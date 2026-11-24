//! Construction (A:939, SPEC 4.3; M3 plan c.10): `new` into its destination
//! (`SetTable`, the values, `&dest [auto-borrow]` last, the constructor), named
//! forms (`NamedFill`, D20), and a body's prologue: `MoveThis` (A:943), a
//! constructor's field initialisers and type defaults, behind `overridden(f)` in a
//! class that can be extended, then parameter defaults (A:937).

use enrang_hir::{
    self as hir, ClassModifier, ConstValue, DefKind, ExprKind as K, Receiver, TyKind,
};
use enrang_mir::{
    BorrowOrigin, Callee, ClassHolder, ClassOp, ConvKind, Local, Operand, Place, Proj, Rvalue,
    StatementKind, TerminatorKind,
};

use crate::builder::Builder;

impl Builder<'_> {
    /// Lowers a `new` or named form into `dest`; false when `e` is neither.
    pub(crate) fn lower_new(&mut self, e: &hir::Expr, dest: Place) -> bool {
        let tcx = self.cx.tcx;
        let span = e.span;
        let class = e.ty;
        let fresh = dest.is_local()
            && self.place_ty(dest) == class
            && self.body.locals[dest.local].kind != enrang_mir::LocalKind::Arg;
        let target: Place = match fresh {
            true => dest,
            false => self.new_temp(class, span).into(),
        };
        let void = tcx.common().void;
        match &e.kind {
            K::New { ctor, args, values } => {
                let is_ctor = tcx.def(*ctor).kind == DefKind::Ctor;
                if self.hidden_table(class) {
                    let st = StatementKind::SetTable {
                        place: target,
                        class,
                    };
                    self.push(st, span);
                }
                let f = hir::FnRef {
                    def: *ctor,
                    args: *args,
                };
                let params = if is_ctor {
                    self.params_of(f)
                } else {
                    Vec::new()
                };
                let mut ops = self.operands(values.iter().zip(params.iter().map(|&t| Some(t))));
                if is_ctor && tcx.sig(*ctor).params.iter().any(|p| p.has_default) {
                    let isize = tcx.common().isize;
                    let n = ConstValue::Int(values.len() as u128, isize);
                    ops.push(Operand::constant(n, isize));
                }
                let this = match is_ctor {
                    true => {
                        let base = tcx.def(*ctor).parent.and_then(|p| tcx.adt_of(p));
                        let own = match tcx.kind(class) {
                            TyKind::Adt(adt, _) => base == Some(adt),
                            _ => true,
                        };
                        // An inherited constructor: the subclass's synthesised one
                        // inlined, its initialisers first (A:939).
                        if let (false, Some(base)) = (own, base) {
                            self.inherited_defaults(target, class, base, &[], false, span);
                        }
                        let r = self.new_temp(tcx.mk_ref(class), span);
                        let rv = Rvalue::Ref {
                            place: target,
                            origin: BorrowOrigin::AutoBorrow,
                        };
                        self.assign(r.into(), rv, span);
                        let want = self.this_ty(f);
                        let op = Operand::Move(r.into());
                        match own {
                            true => op,
                            false => {
                                let u = self.new_temp(want, span);
                                let up = Rvalue::Convert(ConvKind::Upcast, op);
                                self.assign(u.into(), up, span);
                                Operand::Move(u.into())
                            }
                        }
                    }
                    false => {
                        let a = self.new_temp(tcx.mk_raw(class), span);
                        self.assign(a.into(), Rvalue::AddrOf(target), span);
                        Operand::Move(a.into())
                    }
                };
                let callee = match is_ctor {
                    true => Callee::Fn(f),
                    false => Callee::ImplicitCtor { class },
                };
                ops.insert(0, this);
                let d = self.new_temp(void, span);
                self.call(callee, ops, d.into(), span);
            }
            K::NewNamed {
                adt,
                args,
                fields,
                default_from,
            } => {
                let tys: Vec<_> = fields
                    .iter()
                    .map(|(f, _)| tcx.field_ty(*adt, None, *f, *args))
                    .collect();
                let mut ops = Vec::new();
                for (op, ty) in self
                    .operands(
                        fields
                            .iter()
                            .map(|(_, x)| x)
                            .zip(tys.iter().map(|&t| Some(t))),
                    )
                    .into_iter()
                    .zip(tys)
                {
                    ops.push(self.materialize(op, ty, span));
                }
                let a = self.new_temp(tcx.mk_raw(class), span);
                self.assign(a.into(), Rvalue::AddrOf(target), span);
                let callee = Callee::NamedFill {
                    class,
                    left_out: default_from.clone(),
                };
                let d = self.new_temp(void, span);
                self.call(callee, vec![Operand::Move(a.into())], d.into(), span);
                for ((f, _), op) in fields.iter().zip(ops) {
                    let place = self.body.project(target, Proj::Field(*f));
                    self.assign(place, Rvalue::Use(op), span);
                }
            }
            _ => return false,
        }
        // Built in place, the temporary gets its value when its construction
        // finishes, after its arguments' temporaries, so it ends before them (D2).
        self.created(target);
        if !fresh {
            self.assign(dest, Rvalue::Use(Operand::Move(target)), span);
        }
        true
    }

    /// Whether `class` has a hidden method-table pointer.
    fn hidden_table(&self, class: hir::Ty) -> bool {
        let tcx = self.cx.tcx;
        match tcx.kind(class) {
            TyKind::Adt(adt, _) => tcx.adt(adt).as_class().is_some_and(|c| c.hidden_table),
            _ => false,
        }
    }

    /// The prologue, before the written body (A:939, A:943, A:937).
    pub(crate) fn prologue(&mut self) {
        let tcx = self.cx.tcx;
        let hir::BodyOwner::Fn(def) = self.hir.owner else {
            return;
        };
        let data = tcx.def(def);
        let class = data.parent.and_then(|p| tcx.adt_of(p));
        let span = self.hir.span;
        let this = Place::local(Local(1));
        if tcx
            .sig_opt(def)
            .is_some_and(|s| s.receiver == Some(Receiver::Move))
            && let Some(name) = data.name()
        {
            let obj = self.body.project(this, Proj::Deref);
            if self.extensible(self.place_ty(obj)) {
                let st = StatementKind::CheckClass {
                    place: obj,
                    op: ClassOp::MoveThis(name),
                    via: ClassHolder::Ref,
                };
                self.push(st, span);
            }
        }
        if data.kind == DefKind::Ctor
            && let Some(adt) = class
            && let Some(c) = tcx.adt(adt).as_class()
        {
            let open = c.modifier != ClassModifier::Final;
            let obj = self.body.project(this, Proj::Deref);
            let args = tcx.identity_args(tcx.adt(adt).generics);
            for f in self.field_defaults(adt) {
                self.store_default(obj, adt, args, f, open, span);
            }
        }
        self.param_defaults();
    }

    /// The fields class `adt`'s constructor stores before its parameters'
    /// defaults (A:939): its own fields and those it overrides, in declaration
    /// order, each with an initialiser or a type default.
    fn field_defaults(&self, adt: hir::AdtId) -> Vec<hir::FieldIdx> {
        let tcx = self.cx.tcx;
        let Some(c) = tcx.adt(adt).as_class() else {
            return Vec::new();
        };
        let inits = self.cx.program.field_inits.get(&adt);
        let mut fields: Vec<hir::FieldIdx> = c.own_fields().map(|(f, _)| f).collect();
        fields.extend(c.overrides.iter().copied());
        fields.sort();
        let args = tcx.identity_args(tcx.adt(adt).generics);
        fields.retain(|&f| {
            inits.is_some_and(|i| i.inits.iter().any(|(g, _)| *g == f))
                || self.has_default(tcx.field_ty(adt, None, f, args))
        });
        fields
    }

    /// Field `f` of `obj` set to class `adt`'s initialiser or type default for it
    /// (A:939): in a class that can be extended, a `FieldInit` entered through a
    /// switch on `Overridden(f)`; else a plain store.
    fn store_default(
        &mut self,
        obj: Place,
        adt: hir::AdtId,
        args: hir::TyList,
        f: hir::FieldIdx,
        open: bool,
        span: enrang_base::Span,
    ) {
        let tcx = self.cx.tcx;
        let inits = self.cx.program.field_inits.get(&adt);
        let init = inits.and_then(|i| i.inits.iter().find(|(g, _)| *g == f));
        let ty = tcx.field_ty(adt, None, f, args);
        let field = self.body.project(obj, Proj::Field(f));
        let join = open.then(|| self.new_block());
        if let Some(join) = join {
            let init_bb = self.new_block();
            let bool_ty = tcx.common().bool;
            let test = Operand::constant(ConstValue::Overridden(f), bool_ty);
            self.terminate(
                TerminatorKind::Switch {
                    value: test,
                    arms: vec![(0, init_bb)],
                    otherwise: Some(join),
                },
                span,
            );
            self.switch_to(init_bb);
        }
        self.in_temps(span, |b| {
            let op = match init {
                Some((_, e)) => b.operand_at(e, Some(ty)),
                None => b.default_op(ty, span).expect("a type default"),
            };
            let st = match open {
                true => StatementKind::FieldInit { field, value: op },
                false => StatementKind::Assign {
                    dest: field,
                    value: Rvalue::Use(op),
                },
            };
            b.push(st, span);
        });
        if let Some(join) = join {
            self.goto(join, span);
            self.switch_to(join);
        }
        // An initialiser's expressions name no record of this body (c.20).
        self.expr_points.clear();
    }

    /// A subclass with no constructor over a base that has one (A:939): the
    /// synthesised constructor of each class from `class` up to, but not with,
    /// `base`, the class whose constructor runs, inlined before that call. Each
    /// stores its initialisers and type defaults into `obj`, most derived first,
    /// a field a class below already stored or `skip` holds skipped; behind
    /// `Overridden(f)` when `open` (a `super(...)` in a class that can be extended),
    /// plainly at a `new`, whose override set is empty.
    pub(crate) fn inherited_defaults(
        &mut self,
        obj: Place,
        class: hir::Ty,
        base: hir::AdtId,
        skip: &[hir::FieldIdx],
        open: bool,
        span: enrang_base::Span,
    ) {
        let tcx = self.cx.tcx;
        let TyKind::Adt(mut adt, mut args) = tcx.kind(class) else {
            return;
        };
        // The points this body recorded so far outlive the initialisers' own.
        let points = std::mem::take(&mut self.expr_points);
        let mut done: Vec<hir::FieldIdx> = skip.to_vec();
        while adt != base {
            for f in self.field_defaults(adt) {
                if !done.contains(&f) {
                    self.store_default(obj, adt, args, f, open, span);
                    done.push(f);
                }
            }
            match tcx.base_of(adt, args) {
                Some((a, l)) => (adt, args) = (a, l),
                None => break,
            }
        }
        self.expr_points = points;
    }

    /// Parameter defaults in parameter order (A:937): `p = d` when the call
    /// supplied fewer than `k + 1` parameters.
    fn param_defaults(&mut self) {
        let tcx = self.cx.tcx;
        let Some(count) = self.body.meta.defaults_count else {
            return;
        };
        let declared: Vec<hir::LocalId> = self
            .hir
            .params
            .iter()
            .copied()
            .filter(|&p| self.hir.locals[p].kind != hir::LocalKind::This)
            .collect();
        for (p, d) in &self.hir.param_defaults {
            let k = declared.iter().position(|q| q == p).unwrap_or(0);
            let isize = tcx.common().isize;
            let bool_ty = tcx.common().bool;
            let c = self.new_temp(bool_ty, d.span);
            let limit = Operand::constant(ConstValue::Int(k as u128 + 1, isize), isize);
            let lt = Rvalue::Binary(enrang_mir::BinOp::Lt, Operand::Copy(count.into()), limit);
            self.assign(c.into(), lt, d.span);
            let (set, join) = (self.new_block(), self.new_block());
            self.switch_bool(Operand::Move(c.into()), set, join, d.span);
            self.switch_to(set);
            let l = self.local(*p);
            self.in_temps(d.span, |b| b.lower_into(d, l.into()));
            self.goto(join, d.span);
            self.switch_to(join);
        }
    }

    /// Whether a type has a default (S:871).
    fn has_default(&self, ty: hir::Ty) -> bool {
        let tcx = self.cx.tcx;
        match tcx.kind(ty) {
            TyKind::Bool
            | TyKind::Int(_)
            | TyKind::Float(_)
            | TyKind::Str
            | TyKind::Array(_)
            | TyKind::Nullable(_)
            | TyKind::Raw(_)
            | TyKind::Void => true,
            TyKind::Fixed(e, _) => self.has_default(e),
            TyKind::Tuple(l) => tcx.list(l).iter().all(|&p| self.has_default(p)),
            TyKind::Object(s) => tcx.shape(s).fields.iter().all(|f| self.has_default(f.1)),
            _ => false,
        }
    }
}
