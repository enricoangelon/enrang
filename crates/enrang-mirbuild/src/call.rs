//! Calls (A:934, A:937, A:972-978; M3 plan c.7): receivers, O6 order, `Virtual`,
//! the supplied-count argument, hidden arguments (K7), forms (D19) and intrinsics.

use enrang_base::Span;
use enrang_hir::{
    self as hir, AdtKind, ClassModifier, ConstValue, ExprKind as K, FnRef, FormKind, LangItem,
    Receiver, Ty, TyKind, Vis,
};
use enrang_mir::{
    BorrowOrigin, Callee, ClassOp, ConvKind, ForeignRef, FormCall, IntrinsicKind, Operand, Place,
    Proj, Rvalue, StatementKind, TerminatorKind,
};

use crate::builder::Builder;

impl Builder<'_> {
    /// Lowers a call into `dest`; false when `e` is no call.
    pub(crate) fn lower_call(&mut self, e: &hir::Expr, dest: Place) -> bool {
        let K::Call {
            callee,
            receiver,
            args,
        } = &e.kind
        else {
            return false;
        };
        let span = e.span;
        match callee {
            hir::Callee::Form(f) => self.form(*f, receiver.as_deref(), args, dest, span),
            hir::Callee::Intrinsic(k, _) => {
                let ops = self.operands(args.iter().map(|a| (a, None)));
                self.intrinsic(*k, ops, dest, span);
            }
            hir::Callee::HostCall(id) => {
                let ops = self.operands(args.iter().map(|a| (a, None)));
                let st = StatementKind::HostCall {
                    id: *id,
                    args: ops,
                    dest: Some(dest),
                };
                self.push(st, span);
            }
            _ => self.plain_call(e.id, callee, receiver.as_deref(), args, dest, span),
        }
        true
    }

    /// A call of a function, method, constructor, `fn` value, closure or foreign
    /// function (c.7): the receiver's value first, the arguments left to right,
    /// hidden arguments, the supplied count, then the receiver's borrow (O6).
    fn plain_call(
        &mut self,
        id: hir::ExprId,
        callee: &hir::Callee,
        receiver: Option<&hir::Expr>,
        args: &[hir::Expr],
        dest: Place,
        span: Span,
    ) {
        let tcx = self.cx.tcx;
        let fref = match *callee {
            hir::Callee::Fn(f) | hir::Callee::Super(f) => Some(f),
            hir::Callee::BoundMember { found, args, .. } => Some(FnRef { def: found, args }),
            hir::Callee::SuperCtor {
                ctor: Some(def),
                args,
                ..
            } => Some(FnRef { def, args }),
            hir::Callee::Foreign(def) => Some(FnRef {
                def,
                args: tcx.empty_list(),
            }),
            _ => None,
        };
        let params = match callee {
            hir::Callee::FnPtr(x) => self.fn_params(x.ty),
            hir::Callee::Closure(l) => self.fn_params(self.hir.locals[*l].ty),
            _ => fref.map(|f| self.params_of(f)).unwrap_or_default(),
        };
        let fn_value = match callee {
            hir::Callee::FnPtr(x) => Some(self.operand_of(x)),
            _ => None,
        };
        // A `super(...)` in an arrow is EN0619 (A:939): its arguments are not
        // lowered, so that is its one report (see `super_this`).
        let misplaced = matches!(callee, hir::Callee::SuperCtor { .. })
            && matches!(self.body.owner, enrang_mir::BodyOwner::Arrow(..));
        let args = if misplaced { &[][..] } else { args };
        let by_move = matches!(
            fref.and_then(|f| tcx.sig_opt(f.def))
                .and_then(|s| s.receiver),
            Some(Receiver::Move)
        );
        let recv = receiver.map(|r| {
            let v = self.val(r);
            // A `move` receiver is a value operand, evaluated before the arguments
            // (O6): read in place after them, it would see what they change.
            if by_move && !args.iter().all(crate::expr::pure) {
                let (v, ty) = self.chain(r, v, None);
                let op = self.use_val(v, ty, r.span);
                return (
                    r,
                    crate::expr::Val::Op(self.materialize(op, ty, r.span)),
                    true,
                );
            }
            (r, v, false)
        });
        let mut ops = match fref.and_then(|f| self.mem_object(f)) {
            // Each object of `mem.replace` and `mem.swap` is checked directly
            // before the borrow that passes it, which reserves it to the call
            // (A:943): a check after that borrow would read under it.
            Some((op, n)) => {
                let mut ops = Vec::new();
                for (i, (a, &t)) in args.iter().zip(params.iter()).enumerate() {
                    match i < n {
                        true => ops.push(self.mem_arg(a, t, op)),
                        false => ops.extend(self.operands([(a, Some(t))])),
                    }
                }
                ops
            }
            None => self.operands(args.iter().zip(params.iter().map(|&t| Some(t)))),
        };
        if let Some(f) = fref.filter(|_| !misplaced) {
            ops.extend(self.hidden_args(id, f.def, span));
            if tcx
                .sig_opt(f.def)
                .is_some_and(|s| s.params.iter().any(|p| p.has_default))
            {
                let n = ConstValue::Int(args.len() as u128, tcx.common().isize);
                ops.push(Operand::constant(n, tcx.common().isize));
            }
        }
        let mut this = None;
        if let Some((r, v, done)) = recv {
            let want = match by_move {
                true => None,
                false => fref.map(|f| self.this_ty(f)),
            };
            let (v, ty) = match done {
                true => (v, r.ty),
                false => self.chain(r, v, want),
            };
            let op = self.use_val(v, ty, r.span);
            if let Operand::Move(p) = op
                && self.is_temp(p)
            {
                self.note(r.id, p.local);
            }
            this = Some((r, op));
        }
        if let hir::Callee::SuperCtor { .. } = callee {
            if !misplaced {
                self.between_defaults(fref, span);
            }
            ops.insert(0, self.super_this(fref, span));
        }
        let callee = match callee {
            hir::Callee::FnPtr(_) => Callee::FnPtr(fn_value.expect("an `fn` value")),
            hir::Callee::Closure(l) => Callee::ClosureLocal(self.closure_local(*l, span)),
            hir::Callee::Foreign(def) => Callee::Foreign(ForeignRef {
                def: *def,
                abi: tcx.sig(*def).abi,
            }),
            hir::Callee::SuperCtor {
                ctor: None,
                adt,
                args,
                ..
            } => Callee::ImplicitCtor {
                class: tcx.mk_adt(*adt, &tcx.list(*args)),
            },
            _ => {
                let f = fref.expect("a function");
                match &this {
                    Some((r, op)) if self.is_virtual(callee, f, r) => Callee::Virtual {
                        method: f,
                        table: copy_of(op),
                    },
                    _ => Callee::Fn(f),
                }
            }
        };
        if let Some((_, op)) = this {
            if let Some(f) = fref {
                self.object_check(f, &op, span);
            }
            ops.insert(0, op);
        }

        self.call(callee, ops, dest, span);
    }

    /// The exact-class check on the object of an `unbox` or `clone` call (A:943),
    /// before the call: `*b` of a box receiver, else the receiver's pointee, when
    /// reached through a reference or box of a class that can be extended.
    fn object_check(&mut self, f: FnRef, recv: &Operand, span: Span) {
        let op = match self.cx.tcx.def(f.def).name().map(|n| n.as_str()) {
            Some("unbox") => ClassOp::Unbox,
            Some("clone") => ClassOp::Clone,
            _ => return,
        };
        let Some(mut place) = self.borrowed_of(recv) else {
            return;
        };
        let boxed = matches!(self.cx.tcx.kind(self.place_ty(place)), TyKind::Boxed(_));
        if boxed {
            place = self.body.project(place, Proj::Deref);
        }
        if self.through(place).is_none() {
            return;
        }
        // An object whose place needs a guard run (a narrowed payload, an
        // element) is named through the receiver itself: `*a` of a reference to
        // it, `**a` of a reference to a box, `*a` of a box moved in. The check
        // ends the run before the `Call` (A:943), where no tag or bounds check
        // may stand, and every temporary but `a` is moved by then.
        if self.needs_guard(place)
            && let Some(arg) = recv.place()
        {
            let mut q = arg;
            if matches!(self.cx.tcx.kind(self.place_ty(q)), TyKind::Ref(_)) {
                q = self.body.project(q, Proj::Deref);
            }
            if boxed {
                q = self.body.project(q, Proj::Deref);
            }
            place = q;
        }
        if let Some(via) = self.through(place) {
            let st = StatementKind::CheckClass { place, op, via };
            self.push(st, span);
        }
    }

    /// The exact-class check of `mem.replace` (its first argument's object) and
    /// `mem.swap` (both arguments' objects), and how many arguments it takes.
    fn mem_object(&self, f: FnRef) -> Option<(ClassOp, usize)> {
        match self.cx.tcx.lang_item_of(f.def)? {
            LangItem::MemReplace => Some((ClassOp::Replace, 1)),
            LangItem::MemSwap => Some((ClassOp::Swap, 2)),
            _ => None,
        }
    }

    /// An object argument of `mem.replace` or `mem.swap`: its exact-class check
    /// directly before the borrow that passes it, an explicit `&p`, an
    /// auto-borrow, or the reborrow of a reference value (O7).
    fn mem_arg(&mut self, a: &hir::Expr, want: Ty, op: ClassOp) -> Operand {
        self.borrow_check = Some((op, a.id));
        let (v, ty) = self.adjusted_through(a, Some(want));
        if let (Some(_), crate::expr::Val::Place(p)) = (self.borrow_check, &v)
            && matches!(self.cx.tcx.kind(ty), TyKind::Ref(_))
        {
            let obj = self.body.project(*p, Proj::Deref);
            self.guard(obj, a.span);
            self.borrow_class_check(a.id, obj, a.span);
        }
        self.borrow_check = None;
        // The borrow is the argument's point, as `operands` notes it, so the
        // narrowing record sema made for it is placed (S:742).
        let op = self.use_val(v, ty, a.span);
        if let Operand::Move(p) = op
            && self.is_temp(p)
        {
            self.note(a.id, p.local);
        }
        op
    }

    /// The pending check of `borrow_check` when `arg` is its argument, on
    /// `place`, the object the argument's borrow is about to name, when reached
    /// through a reference or box of a class that can be extended (A:943).
    pub(crate) fn borrow_class_check(&mut self, arg: hir::ExprId, place: Place, span: Span) {
        if let Some((op, id)) = self.borrow_check
            && id == arg
        {
            self.borrow_check = None;
            if let Some(via) = self.through(place) {
                self.push(StatementKind::CheckClass { place, op, via }, span);
            }
        }
    }

    /// The place an argument's reference borrows: through the temporaries that
    /// carry it (a borrow, a copy, a conversion), as the current block made them.
    fn borrowed_of(&self, op: &Operand) -> Option<Place> {
        let mut place = op.place()?;
        while self.is_temp(place) {
            let at = self.last_assign(place.local)?;
            place = match self.body.stmt_at(at).map(|s| &s.kind) {
                Some(StatementKind::Assign { value, .. }) => match value {
                    Rvalue::Ref { place, .. } => *place,
                    Rvalue::Convert(_, o) | Rvalue::Use(o) => o.place()?,
                    _ => return None,
                },
                _ => return None,
            };
        }
        Some(place)
    }

    /// Before `super(...)` reaches the constructor of a class above the direct
    /// base, the synthesised constructors of the classes between, inlined: their
    /// initialisers into `*this`, behind `Overridden(f)` in a class that can be
    /// extended, the fields this class overrides skipped (A:939).
    fn between_defaults(&mut self, ctor: Option<FnRef>, span: Span) {
        let tcx = self.cx.tcx;
        let (hir::BodyOwner::Fn(me), Some(f)) = (self.hir.owner, ctor) else {
            return;
        };
        let class = tcx.def(me).parent.and_then(|p| tcx.adt_of(p));
        let target = tcx.def(f.def).parent.and_then(|p| tcx.adt_of(p));
        let (Some(class), Some(target)) = (class, target) else {
            return;
        };
        let Some(c) = tcx.adt(class).as_class() else {
            return;
        };
        let Some((base, args)) = tcx.base_of(class, tcx.identity_args(tcx.adt(class).generics))
        else {
            return;
        };
        if base == target {
            return;
        }
        let (open, skip) = (c.modifier != ClassModifier::Final, c.overrides.clone());
        let obj = self.body.place(enrang_mir::Local(1), &[Proj::Deref]);
        let base_ty = tcx.mk_adt(base, &tcx.list(args));
        self.inherited_defaults(obj, base_ty, target, &skip, open, span);
    }

    /// `this` passed to `super(...)` (c.7): `convert(upcast, &*_1 [reborrow])` to
    /// the base's constructor, `addr_of(*_1)` to an implicit one (D20). In an
    /// arrow, where `super(...)` is never valid and `this` is not captured, `this`
    /// is a temporary of the constructor's `&C` that nothing assigns: the body
    /// verifies, and the move check reports EN0619 at the call (A:939, A:1003).
    fn super_this(&mut self, ctor: Option<FnRef>, span: Span) -> Operand {
        let this = match self.body.owner {
            enrang_mir::BodyOwner::Arrow(..) => {
                let tcx = self.cx.tcx;
                let class = match self.hir.owner {
                    hir::BodyOwner::Fn(d) => tcx.def(d).parent.and_then(|p| tcx.adt_of(p)),
                    _ => None,
                };
                let ty = class.map_or(tcx.common().error, |c| tcx.adt_identity(c));
                Place::local(self.new_temp(tcx.mk_ref(ty), span))
            }
            _ => Place::local(enrang_mir::Local(1)),
        };
        let obj = self.body.project(this, Proj::Deref);
        match ctor {
            Some(f) => {
                let r = self.new_temp(self.place_ty(this), span);
                let rv = Rvalue::Ref {
                    place: obj,
                    origin: BorrowOrigin::Reborrow,
                };
                self.assign(r.into(), rv, span);
                let up = self.new_temp(self.this_ty(f), span);
                let conv = Rvalue::Convert(ConvKind::Upcast, Operand::Move(r.into()));
                self.assign(up.into(), conv, span);
                Operand::Move(up.into())
            }
            None => {
                let ptr = self.cx.tcx.mk_raw(self.place_ty(obj));
                let t = self.new_temp(ptr, span);
                self.assign(t.into(), Rvalue::AddrOf(obj), span);
                Operand::Move(t.into())
            }
        }
    }

    /// Ends the block in `callee(args) -> dest` and continues after it; a callee
    /// returning `never` has no next block and a `never` temporary for `dest`.
    pub(crate) fn call(&mut self, callee: Callee, args: Vec<Operand>, dest: Place, span: Span) {
        let never = self.cx.tcx.kind(self.place_ty(dest)) == TyKind::Never
            || matches!(callee.form(), Some(FormCall::Panic | FormCall::Unreachable));
        let next = (!never).then(|| self.new_block());
        let dest = match never && self.cx.tcx.kind(self.place_ty(dest)) != TyKind::Never {
            true => self.new_temp(self.cx.tcx.common().never, span).into(),
            false => dest,
        };
        self.terminate(
            TerminatorKind::Call {
                callee,
                args,
                dest,
                next,
            },
            span,
        );
        if let Some(n) = next {
            self.switch_to(n);
        }
    }

    /// Whether a method call goes through the table (c.7, V16): an overridable
    /// method of a class that can be extended, on a receiver reached through a
    /// reference or box, or a member of an interface; through a bound, a member
    /// on an interface `&I` or `Box<I>`, or an overridable method of a class that
    /// can be extended on a `T`, `&T` or `Box<T>` for a `T extends C` (A:1281), so
    /// phase 3 applies the declared contract and mono reaches the override. A
    /// `move` method is never: its object is copied or moved out first, with its
    /// class checked, so it is exactly the class (A:943).
    fn is_virtual(&self, callee: &hir::Callee, f: FnRef, r: &hir::Expr) -> bool {
        let tcx = self.cx.tcx;
        if tcx
            .sig_opt(f.def)
            .is_some_and(|s| s.receiver == Some(Receiver::Move))
        {
            return false;
        }
        if let hir::Callee::BoundMember { .. } = callee {
            let mut obj = r.ty;
            while let TyKind::Ref(t) | TyKind::Boxed(t) = tcx.kind(obj) {
                obj = t;
            }
            let Some(parent) = tcx.def(f.def).parent.and_then(|p| tcx.adt_of(p)) else {
                return false;
            };
            return match (&tcx.adt(parent).kind, tcx.kind(obj)) {
                (AdtKind::Interface(_), TyKind::Adt(a, _)) => tcx.adt(a).is_interface(),
                (AdtKind::Class(c), TyKind::Param(_)) => {
                    c.modifier != ClassModifier::Final && self.overridable(f.def)
                }
                _ => false,
            };
        }
        if !matches!(callee, hir::Callee::Fn(_)) {
            return false;
        }
        let borrowed = r.adjust.contains(&hir::Adjust::AutoBorrow);
        let through = match borrowed {
            false => matches!(tcx.kind(r.ty), TyKind::Ref(_) | TyKind::Boxed(_)),
            true => r.adjust.contains(&hir::Adjust::BoxDeref) || matches!(r.kind, K::Deref(_)),
        };
        let Some(parent) = tcx.def(f.def).parent.and_then(|p| tcx.adt_of(p)) else {
            return false;
        };
        match &tcx.adt(parent).kind {
            AdtKind::Interface(_) => true,
            AdtKind::Class(c) => {
                let recv_class = match tcx.kind(r.ty) {
                    TyKind::Ref(t) | TyKind::Boxed(t) => t,
                    _ => r.ty,
                };
                through
                    && self.extensible(recv_class)
                    && c.modifier != ClassModifier::Final
                    && self.overridable(f.def)
            }
            AdtKind::Enum(_) => false,
        }
    }

    /// Whether `def` can be overridden (A:1279): not `private`, not `static`, not
    /// compiled once per type.
    fn overridable(&self, def: hir::DefId) -> bool {
        let tcx = self.cx.tcx;
        tcx.def(def).vis != Vis::Private
            && tcx
                .sig_opt(def)
                .is_none_or(|s| s.receiver != Some(Receiver::Static))
            && tcx.once_per_type(def).is_none()
    }

    /// The parameter types of `f`, substituted, without `this`.
    pub(crate) fn params_of(&self, f: FnRef) -> Vec<Ty> {
        let tcx = self.cx.tcx;
        let Some(sig) = tcx.sig_opt(f.def) else {
            return Vec::new();
        };
        sig.params.iter().map(|p| self.subst(p.ty, f)).collect()
    }

    /// `t` of `f`'s signature at `f`'s type arguments; parameters beyond the
    /// arguments given stay (sema's convention, `Tcx::method_params_at`).
    pub(crate) fn subst(&self, t: Ty, f: FnRef) -> Ty {
        let tcx = self.cx.tcx;
        let Some(sig) = tcx.sig_opt(f.def) else {
            return t;
        };
        let mut params = tcx.all_params(sig.generics);
        let args = tcx.list(f.args);
        params.truncate(args.len());
        tcx.subst(t, &params, &args[..params.len()])
    }

    /// The type of `f`'s `this`: `&` its class, substituted.
    pub(crate) fn this_ty(&self, f: FnRef) -> Ty {
        let tcx = self.cx.tcx;
        let self_ty = tcx
            .def(f.def)
            .parent
            .map(|p| match tcx.adt_of(p) {
                Some(adt) => match &tcx.adt(adt).kind {
                    AdtKind::Interface(i) => tcx.mk_param(i.self_param),
                    _ => tcx.adt_identity(adt),
                },
                None => tcx
                    .extends()
                    .iter()
                    .find(|e| e.def == p)
                    .map_or(tcx.common().error, |e| e.ty),
            })
            .unwrap_or(tcx.common().error);
        self.subst(tcx.mk_ref(self_ty), f)
    }

    /// The parameter types of an `fn` or closure type.
    fn fn_params(&self, t: Ty) -> Vec<Ty> {
        let tcx = self.cx.tcx;
        match tcx.kind(t) {
            TyKind::FnPtr(_, s) | TyKind::Closure(s) => {
                tcx.fn_sig(s).params.iter().map(|p| p.0).collect()
            }
            TyKind::Nullable(t) => self.fn_params(t),
            _ => Vec::new(),
        }
    }

    /// The local a closure call goes through (A:972-973): the closure local
    /// itself; a nullable one narrowed, and one reached through a place (a
    /// capture `*(*_1).i` in an arrow, a hidden argument `*_k` in a local
    /// function), reborrowed into a temporary first.
    fn closure_local(&mut self, l: hir::LocalId, span: Span) -> enrang_mir::Local {
        let mut place = self.local_place(l);
        let mut ty = self.place_ty(place);
        if let TyKind::Nullable(inner) = self.cx.tcx.kind(ty) {
            place = self.present(place);
            self.guard(place, span);
            ty = inner;
        } else if place.is_local() {
            return place.local;
        }
        let f = self.new_temp(ty, span);
        self.assign(f.into(), Rvalue::ClosureReborrow(place), span);
        f
    }

    /// The hidden arguments of a call of local function `def` (K7, c.17): for each
    /// top-level variable it uses, `&v [hidden-arg]` of an owned variable, a
    /// reborrow `&*v [hidden-arg]` of a reference one, a copy of a nullable one.
    fn hidden_args(&mut self, call: hir::ExprId, def: hir::DefId, span: Span) -> Vec<Operand> {
        self.hidden_refs(Some(call), def, BorrowOrigin::HiddenArg, span)
    }

    /// The env of local function `def` passed as a closure (c.16, A:1360): its
    /// hidden arguments as captures, `&v` or `&*v [closure-capture]`.
    pub(crate) fn hidden_captures(&mut self, def: hir::DefId, span: Span) -> Vec<Operand> {
        self.hidden_refs(None, def, BorrowOrigin::ClosureCapture, span)
    }

    /// For each top-level variable local function `def` uses, `&v` of an owned
    /// variable, a reborrow `&*v` of a reference one, both with `origin`, or a
    /// copy of a nullable one; a call's records at each (c.20).
    fn hidden_refs(
        &mut self,
        call: Option<hir::ExprId>,
        def: hir::DefId,
        origin: BorrowOrigin,
        span: Span,
    ) -> Vec<Operand> {
        let Some(vars) = self.cx.program.hidden_args.get(&def) else {
            return Vec::new();
        };
        let tcx = self.cx.tcx;
        let mut out = Vec::new();
        for &v in vars {
            let place = self.top_var(v);
            let ty = self.cx.program.top_vars[v.0 as usize].ty;
            let (rv, t) = match tcx.kind(ty) {
                TyKind::Ref(_) => (Some(self.body.project(place, Proj::Deref)), ty),
                TyKind::Nullable(i) if matches!(tcx.kind(i), TyKind::Ref(_)) => (None, ty),
                _ => (Some(place), tcx.mk_ref(ty)),
            };
            let tmp = self.new_temp(t, span);
            let value = match rv {
                Some(place) => Rvalue::Ref { place, origin },
                None => Rvalue::Use(Operand::Copy(place)),
            };
            self.assign(tmp.into(), value, span);
            let Some(call) = call else {
                out.push(Operand::Move(tmp.into()));
                continue;
            };
            let at = self.last_assign(tmp);
            for (i, r) in self.hir.records.iter().enumerate() {
                let root = self.hir.facts[r.fact].path.root;
                let of_v = matches!(
                    self.hir.locals[root].kind,
                    hir::LocalKind::TopVar(x) | hir::LocalKind::Hidden(x) if x == v
                );
                if r.expr == call && r.kind == hir::RecordKind::HiddenArg && of_v {
                    self.record_points.extend(at.map(|p| (i, p)));
                }
            }
            out.push(Operand::Move(tmp.into()));
        }
        out
    }

    /// The place of top-level variable `v`'s value here: its local in the
    /// statements, `*_k` (or `_k` for a reference) in a local function.
    fn top_var(&mut self, v: hir::TopVar) -> Place {
        if let Some(&k) = self.hidden.get(&v) {
            let decl_ty = self.cx.program.top_vars[v.0 as usize].ty;
            return match self.body.locals[k].ty == decl_ty {
                true => k.into(),
                false => self.body.place(k, &[Proj::Deref]),
            };
        }
        // In an arrow, the variable is a local of the statements or, in a local
        // function, its hidden local, which the arrow captures (c.16).
        let l = self
            .hir
            .locals
            .iter_enumerated()
            .find(|(_, d)| {
                matches!(d.kind, hir::LocalKind::TopVar(x) | hir::LocalKind::Hidden(x) if x == v)
            })
            .map(|(l, _)| l)
            .expect("a top-level variable of the statements");
        self.local_place(l)
    }

    /// An intrinsic statement into `dest` (A:978).
    pub(crate) fn intrinsic(
        &mut self,
        kind: IntrinsicKind,
        args: Vec<Operand>,
        dest: Place,
        span: Span,
    ) {
        let st = StatementKind::Intrinsic {
            kind,
            args,
            dest: Some(dest),
        };
        self.push(st, span);
    }

    /// A compiler form (D19, c.7).
    fn form(
        &mut self,
        f: FormKind,
        receiver: Option<&hir::Expr>,
        args: &[hir::Expr],
        dest: Place,
        span: Span,
    ) {
        let tcx = self.cx.tcx;
        let all: Vec<&hir::Expr> = receiver.into_iter().chain(args).collect();
        // A template passed directly is flattened into its parts, which go
        // straight to the stream (A:976); how many operands each argument gave
        // keeps the arguments apart (`FormParts`).
        let shared = |b: &mut Self| -> (Vec<Operand>, Vec<u32>) {
            let mut out = Vec::new();
            let mut parts = Vec::new();
            for a in &all {
                let n = out.len();
                match &a.kind {
                    K::Template(tpl) if a.adjust.is_empty() && receiver.is_none() => {
                        out.extend(b.template_args(tpl))
                    }
                    _ => out.push(b.shared_arg(a)),
                }
                parts.push((out.len() - n) as u32);
            }
            (out, parts)
        };
        let simple = match f {
            FormKind::ConsoleLog => Some(FormCall::Log),
            FormKind::ConsoleError => Some(FormCall::Error),
            FormKind::WriteTo => Some(FormCall::WriteTo),
            FormKind::Panic => Some(FormCall::Panic),
            FormKind::ToString => Some(FormCall::ToString),
            FormKind::Assert => Some(FormCall::Assert),
            FormKind::Unreachable => Some(FormCall::Unreachable),
            _ => None,
        };
        if let Some(fc) = simple {
            let (ops, parts) = shared(self);
            match parts.iter().all(|&n| n == 1) {
                true => self.form_call(fc, ops, dest, span),
                false => self.call(Callee::FormParts { form: fc, parts }, ops, dest, span),
            }
            return;
        }
        let first = all.first().copied();
        match f {
            FormKind::Err(form) => {
                crate::lower_err(self, form, first.expect("an argument"), dest, span)
            }
            // `dispose(x)` takes its value by move (D5), as `mem.forget` does: into
            // a temporary, so every move check sees it (EN0601, EN0603-EN0605,
            // EN0607, EN0611, EN0617), and the temporary is dropped there.
            // A reference argument is evaluated too, its calls and moves included,
            // and only its drop is nothing: lowering nothing for it skipped
            // `dispose(pick(s, &a))`'s call, and with it the move of `s`.
            FormKind::Dispose => {
                let a = first.expect("an argument");
                let op = self.operand_of(a);
                let t = self.new_local(a.ty, enrang_mir::LocalKind::Temp, None, a.span);
                self.assign(t.into(), Rvalue::Use(op), span);
                if !matches!(tcx.kind(a.ty), TyKind::Ref(_)) {
                    let drop = StatementKind::Drop(t.into(), enrang_mir::DropOrigin::Scope);
                    self.push(drop, span);
                }
                self.push(StatementKind::StorageDead(t), span);
            }
            FormKind::MemForget => {
                let a = first.expect("an argument");
                let op = self.operand_of(a);
                let t = self.new_local(a.ty, enrang_mir::LocalKind::Temp, None, a.span);
                self.assign(t.into(), Rvalue::Use(op), span);
                self.push(StatementKind::StorageDead(t), span);
            }
            FormKind::SizeOf(t) => self.intrinsic(IntrinsicKind::SizeOf(t), vec![], dest, span),
            FormKind::AlignOf(t) => self.intrinsic(IntrinsicKind::AlignOf(t), vec![], dest, span),
            FormKind::OffsetOf(t, fi) => {
                self.intrinsic(IntrinsicKind::OffsetOf(t, fi), vec![], dest, span)
            }
            FormKind::CpuHas(ft) => self.intrinsic(IntrinsicKind::CpuHas(ft), vec![], dest, span),
            FormKind::Clone | FormKind::Fmt | FormKind::Equals => {
                let item = match f {
                    FormKind::Clone => LangItem::Clone,
                    FormKind::Fmt => LangItem::Display,
                    _ => LangItem::Eq,
                };
                let a = first.expect("a receiver");
                let obj_ty = match tcx.kind(a.ty) {
                    TyKind::Ref(t) => t,
                    _ => a.ty,
                };
                let def = tcx
                    .lang_adt(item)
                    .and_then(|adt| tcx.adt(adt).as_interface().map(|i| i.methods[0]))
                    .expect("a lang interface");
                let fref = FnRef {
                    def,
                    args: tcx.intern_list(&[obj_ty]),
                };
                let params = self.params_of(fref);
                let mut ops = vec![self.shared_arg(a)];
                let rest = all[1..].iter().zip(params).map(|(&x, t)| (x, Some(t)));
                ops.extend(self.operands(rest));
                // A clone of an object reached through a reference has its
                // exact-class check too (A:943), as a method call's has.
                if f == FormKind::Clone {
                    self.object_check(fref, &ops[0], span);
                }
                self.call(Callee::Fn(fref), ops, dest, span);
            }
            _ => unreachable!("a simple form"),
        }
    }

    /// `dest = form fc(args)` [D19].
    pub(crate) fn form_call(&mut self, fc: FormCall, args: Vec<Operand>, dest: Place, span: Span) {
        self.call(Callee::Form(fc), args, dest, span);
    }
}

/// A copy of a receiver operand, the `table` of a virtual call (b.4).
fn copy_of(op: &Operand) -> Operand {
    match op {
        Operand::Move(p) | Operand::Copy(p) => Operand::Copy(*p),
        Operand::Const(_) => op.clone(),
    }
}
