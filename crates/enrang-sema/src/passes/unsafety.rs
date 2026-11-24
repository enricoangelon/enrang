//! The five unsafe powers (plan d.17; SPEC 5.9 S:1096-1102, 7.2 S:1197, 7.7 S:1324,
//! 10.3 S:1578; owner 4E).
//!
//! Each finished body is walked with its `unsafe` depth: an `unsafe { }` block adds
//! one, and an `unsafe function` or `@naked` body starts at one. An arrow is walked
//! where it is written, at the depth of that place, so an arrow inside `unsafe` may
//! use the powers (plan choice; the docs are silent on arrows). Outside `unsafe`,
//! each of these is EN0801 at the operation:
//!
//! 1. dereferencing a raw pointer: a `*p` place read, written or borrowed, and the
//!    `*T` methods `read`, `write`, `readVolatile`, `writeVolatile`,
//!    `readUnaligned` and `writeUnaligned` (G13: `writing through a raw pointer
//!    needs `unsafe``, labelled `` `writeVolatile` dereferences `VGA`, a `*u16` ``);
//! 2. calling an `unsafe` function or method, a `declare` function, an intrinsic
//!    whose safety bit is clear, an `unsafe fn` value or an `@abi` function pointer
//!    (`` calling `f` needs `unsafe` ``);
//! 3. `asm` (`` `asm` needs `unsafe` ``);
//! 4. reading, writing or borrowing an `unsafe let` (`` using `count`, an `unsafe
//!    let`, needs `unsafe` ``);
//! 5. the same for an `unsafe let` placed with `@at`, whose rule names the fifth
//!    power.
//!
//! A `@requires` function called outside `unsafe` is EN0907 instead of EN0801
//! (`` calling `f` needs `unsafe`, because it requires `cmov` ``), and calling an
//! `@interrupt` function is EN0807 inside `unsafe` too. Every EN0801 carries the
//! rule naming its power and a help that wraps the innermost statement holding the
//! operation in `unsafe { ... }`; when that statement declares a local, which the
//! block would hide from what follows, or when there is no statement (an arrow's
//! expression body, a parameter default), the help has no edit (plan choice).
//!
//! A function that is not `unsafe` and, inside `unsafe`, reads or writes through
//! one of its raw-pointer parameters (directly, or through `add`, `sub` and raw
//! pointer casts of it) gets warning EN0828 at the first such dereference of each
//! parameter, `` `f` reads through the raw pointer `p` ``, with `help: mark it
//! `unsafe function`, or take a reference`; a method marked `override`, or one
//! named like a member of an interface its class implements, is exempt, since a
//! base method or an interface member fixes its signature (S:1197, T:912). An
//! operation outside `unsafe` is EN0801 already, so it gets no EN0828 (plan choice).

use std::collections::{BTreeMap, BTreeSet};

use enrang_base::Span;
use enrang_diag::{Code, Diagnostic, Edit, Help};
use enrang_hir::{
    Abi, ArmBody, ArmValue, ArrayPart, ArrowBodyKind, ArrowId, Block, Body, BodyOwner, Callee,
    CastKind, DefId, DefKind, ExpectArg, Expr, ExprKind, ForSource, IntrinsicKind, IntrinsicName,
    LocalId, LocalKind, OptMember, Stmt, StmtKind, Tcx, TplPart, TyKind,
};

use crate::classes::sig;
use crate::cx::Sema;

/// Checks the five powers of `b`. The initialiser of a `const`, an `unsafe let`
/// or a top-level `assert` is const eval's (S:756-758): every power used there is
/// not constant, EN0412 or EN1032 already, and `unsafe { }` could not help, so it
/// reports nothing more (one report per mistake, A:1159).
pub(crate) fn check(sema: &mut Sema, b: &Body) {
    let tcx = &*sema.tcx;
    if let BodyOwner::Const(def) = b.owner
        && matches!(
            tcx.def(def).kind,
            DefKind::Const | DefKind::StaticAssert | DefKind::Static
        )
    {
        return;
    }
    let fn_def = match b.owner {
        BodyOwner::Fn(def) => Some(def),
        _ => None,
    };
    let unsafe_fn = fn_def.is_some_and(|def| {
        tcx.sig_opt(def).is_some_and(|s| s.unsafety) || tcx.def(def).attrs.naked
    });
    let raw_params: BTreeSet<LocalId> = match fn_def {
        Some(def) if !unsafe_fn && !exempt_from_en0828(tcx, def) => b
            .params
            .iter()
            .copied()
            .filter(|&p| {
                matches!(b.locals[p].kind, LocalKind::Param(_))
                    && matches!(tcx.kind(b.locals[p].ty), TyKind::Raw(_))
            })
            .collect(),
        _ => BTreeSet::new(),
    };
    let mut w = Walker {
        tcx,
        body: b,
        depth: u32::from(unsafe_fn),
        stmt: None,
        walked: BTreeSet::new(),
        raw_params,
        warned: BTreeSet::new(),
        found: Vec::new(),
    };
    for (_, default) in &b.param_defaults {
        w.expr(default, Use::Read);
    }
    w.block(&b.root);
    // Arrows no expression names, if any, are walked at the body's own depth.
    let base = w.depth;
    for (id, _) in b.arrows.iter_enumerated() {
        if !w.walked.contains(&id) {
            w.depth = base;
            w.stmt = None;
            w.arrow(id);
        }
    }
    let found = std::mem::take(&mut w.found);
    for diag in found {
        sema.emit(diag);
    }
}

/// Whether a method's signature is fixed by a base method or an interface member,
/// so EN0828's help could not be followed (S:1197): an `override`, or a method
/// with the parameters of a member of an interface its class or a base implements
/// (the name alone is not enough: an overload no member fixes is not exempt).
fn exempt_from_en0828(tcx: &Tcx, def: DefId) -> bool {
    let data = tcx.def(def);
    if data.kind != DefKind::Method {
        return false;
    }
    if data.flags.is_override {
        return true;
    }
    let (Some(name), Some(parent)) = (data.name(), data.parent) else {
        return false;
    };
    let Some(own) = tcx.adt_of(parent) else {
        return false;
    };
    let own_args = tcx.identity_args(tcx.adt(own).generics);
    let self_ty = tcx.adt_identity(own);
    let Some(mine) = sig::view(tcx, def, &tcx.list(own_args), None) else {
        return false;
    };
    let mut cur = Some((own, own_args));
    let mut seen = Vec::new();
    while let Some((adt, args)) = cur {
        if seen.contains(&adt) {
            return false;
        }
        seen.push(adt);
        let Some(class) = tcx.adt(adt).as_class() else {
            return false;
        };
        let params = tcx.all_params(tcx.adt(adt).generics);
        let args_v = tcx.list(args);
        for &iface in &class.implements {
            let iface = tcx.subst(iface, &params, &args_v);
            let TyKind::Adt(i, iargs) = tcx.kind(iface) else {
                continue;
            };
            let iargs = tcx.list(iargs);
            for &m in tcx.adt(i).own_methods() {
                if tcx.def(m).name() == Some(name)
                    && let Some(member) = sig::view(tcx, m, &iargs, Some(self_ty))
                    && sig::same_params(tcx, &mine, &member)
                {
                    return true;
                }
            }
        }
        cur = tcx.base_of(adt, args);
    }
    false
}

/// How a place is used.
#[derive(Copy, Clone, PartialEq, Eq)]
enum Use {
    Read,
    Write,
    Borrow,
}

/// One of the five powers, for the message, the rule and the help.
#[derive(Copy, Clone, PartialEq, Eq)]
enum Power {
    Deref,
    Call,
    Asm,
    Static,
    At,
}

impl Power {
    fn rule(self) -> &'static str {
        match self {
            Power::Deref => {
                "`unsafe` grants exactly five powers; this one is \"dereference a raw pointer\". Nothing checks the address for you."
            }
            Power::Call => {
                "`unsafe` grants exactly five powers; this one is \"call an `unsafe` function\". Nothing checks that its conditions hold."
            }
            Power::Asm => {
                "`unsafe` grants exactly five powers; this one is \"`asm`\". Nothing checks what the instructions do."
            }
            Power::Static => {
                "`unsafe` grants exactly five powers; this one is \"read, write or borrow an `unsafe let`\". Nothing keeps other accesses to it apart."
            }
            Power::At => {
                "`unsafe` grants exactly five powers; this one is \"access `@at` storage\". Nothing checks the address for you."
            }
        }
    }

    fn help(self) -> &'static str {
        match self {
            Power::Deref | Power::At => "state that you have checked the address",
            Power::Call => "state that you have met its conditions",
            Power::Asm => "state that you have checked the instructions",
            Power::Static => "state that no other access overlaps this one",
        }
    }
}

/// The innermost statement around the walk: its span, and whether it declares a
/// local that an `unsafe` block around it would hide.
#[derive(Copy, Clone)]
struct StmtAt {
    span: Span,
    declares: bool,
}

struct Walker<'t> {
    tcx: &'t Tcx,
    body: &'t Body,
    depth: u32,
    stmt: Option<StmtAt>,
    walked: BTreeSet<ArrowId>,
    raw_params: BTreeSet<LocalId>,
    warned: BTreeSet<LocalId>,
    found: Vec<Diagnostic>,
}

impl Walker<'_> {
    fn block(&mut self, b: &Block) {
        for s in &b.stmts {
            self.stmt(s);
        }
    }

    fn stmt(&mut self, s: &Stmt) {
        let saved = self.stmt;
        self.stmt = Some(StmtAt {
            span: s.span,
            declares: matches!(s.kind, StmtKind::Let { .. } | StmtKind::Destructure { .. }),
        });
        match &s.kind {
            StmtKind::Let { init, .. } => {
                if let Some(e) = init {
                    self.expr(e, Use::Read);
                }
            }
            StmtKind::Destructure { init, .. } => self.expr(init, Use::Read),
            StmtKind::If { cond, then_, else_ } => {
                self.expr(cond, Use::Read);
                self.block(then_);
                if let Some(b) = else_ {
                    self.block(b);
                }
            }
            StmtKind::While { cond, body, .. } | StmtKind::DoWhile { body, cond, .. } => {
                self.expr(cond, Use::Read);
                self.block(body);
            }
            StmtKind::For {
                init,
                cond,
                step,
                body,
                ..
            } => {
                if let Some(s) = init {
                    self.stmt(s);
                }
                if let Some(c) = cond {
                    self.expr(c, Use::Read);
                }
                if let Some(s) = step {
                    self.stmt(s);
                }
                self.block(body);
            }
            StmtKind::ForOf { source, body, .. } => {
                match source {
                    ForSource::Path { place } => self.expr(place, Use::Borrow),
                    ForSource::Once { value, .. } => self.expr(value, Use::Read),
                    ForSource::Range { lo, hi } => {
                        self.expr(lo, Use::Read);
                        self.expr(hi, Use::Read);
                    }
                }
                self.block(body);
            }
            StmtKind::Return(e) => {
                if let Some(e) = e {
                    self.expr(e, Use::Read);
                }
            }
            StmtKind::Break(_) | StmtKind::Continue(_) => {}
            StmtKind::Block(b) => self.block(b),
            StmtKind::Unsafe(b) => {
                self.depth += 1;
                self.block(b);
                self.depth -= 1;
            }
            StmtKind::Expr(e) => self.expr(e, Use::Read),
            StmtKind::Expect(x) => {
                self.expr(&x.actual, Use::Read);
                for arg in &x.args {
                    match arg {
                        ExpectArg::Expr(e) => self.expr(e, Use::Read),
                        ExpectArg::Arm(ArmValue::Cond(e)) => self.expr(e, Use::Read),
                        ExpectArg::Arm(_) => {}
                    }
                }
            }
        }
        self.stmt = saved;
    }

    fn arrow(&mut self, id: ArrowId) {
        if !self.walked.insert(id) {
            return;
        }
        let body = self.body;
        match &body.arrows[id].body {
            ArrowBodyKind::Expr(e) => self.expr(e, Use::Read),
            ArrowBodyKind::Block(b) => self.block(b),
        }
    }

    fn expr(&mut self, e: &Expr, how: Use) {
        // A borrow adjust on a place makes its use a borrow.
        let how = if how == Use::Read && e.adjust.first() == Some(&enrang_hir::Adjust::AutoBorrow) {
            Use::Borrow
        } else {
            how
        };
        match &e.kind {
            ExprKind::Local(_) | ExprKind::Const(_) | ExprKind::Never | ExprKind::NullLit => {}
            ExprKind::Static(def) => self.static_use(*def, e.span, how),
            ExprKind::Field(base, _) | ExprKind::NarrowedPayload(base, _, _) => {
                self.expr(base, how)
            }
            ExprKind::Index(base, index) => {
                self.expr(base, how);
                self.expr(index, Use::Read);
            }
            ExprKind::Deref(base) => {
                if matches!(self.tcx.kind(base.ty), TyKind::Raw(_)) {
                    self.deref(e.span, base, None, how);
                }
                self.expr(base, Use::Read);
            }
            ExprKind::Template(parts) => {
                for part in parts {
                    if let TplPart::Hole(h) = part {
                        self.expr(h, Use::Read);
                    }
                }
            }
            ExprKind::ArrayLit(items)
            | ExprKind::TupleLit(items)
            | ExprKind::ObjectLit { fields: items, .. }
            | ExprKind::VariantLit { fields: items, .. } => {
                items.iter().for_each(|i| self.expr(i, Use::Read))
            }
            ExprKind::New { ctor, values, .. } => {
                self.call_def(*ctor, e.span, None);
                values.iter().for_each(|i| self.expr(i, Use::Read));
            }
            ExprKind::Repeat(value, _) => self.expr(value, Use::Read),
            ExprKind::ArrayBuild { parts, .. } => {
                for part in parts {
                    match part {
                        ArrayPart::Item(i) | ArrayPart::Spread(i, _) => self.expr(i, Use::Read),
                    }
                }
            }
            ExprKind::NewNamed { fields, .. } => {
                fields.iter().for_each(|(_, i)| self.expr(i, Use::Read))
            }
            ExprKind::Call {
                callee,
                receiver,
                args,
            } => {
                self.callee(callee, e.span, receiver.as_deref());
                if let Some(r) = receiver {
                    self.expr(r, Use::Read);
                }
                args.iter().for_each(|a| self.expr(a, Use::Read));
            }
            ExprKind::OptionalChain(chain) => {
                self.expr(&chain.base, Use::Read);
                if let OptMember::Call { callee, args } = &chain.member {
                    self.callee(callee, e.span, Some(&chain.base));
                    args.iter().for_each(|a| self.expr(a, Use::Read));
                }
            }
            ExprKind::Unary(_, a)
            | ExprKind::Cast(a, _)
            | ExprKind::Try(a, _)
            | ExprKind::NonNull(a)
            | ExprKind::VoidOp(a) => self.expr(a, Use::Read),
            ExprKind::Borrow(a) | ExprKind::AddrOf(a) => self.expr(a, Use::Borrow),
            ExprKind::Binary(_, a, b) | ExprKind::Logical(_, a, b) | ExprKind::Coalesce(a, b) => {
                self.expr(a, Use::Read);
                self.expr(b, Use::Read);
            }
            ExprKind::Ternary(a, b, c) => {
                self.expr(a, Use::Read);
                self.expr(b, Use::Read);
                self.expr(c, Use::Read);
            }
            ExprKind::Assign { target, value, .. } => {
                self.expr(target, Use::Write);
                self.expr(value, Use::Read);
            }
            ExprKind::IncDec { target, .. } => self.expr(target, Use::Write),
            ExprKind::Match { subject, arms } => {
                self.expr(subject, Use::Read);
                for arm in arms {
                    for value in &arm.values {
                        if let ArmValue::Cond(c) = value {
                            self.expr(c, Use::Read);
                        }
                    }
                    if let Some(g) = &arm.guard {
                        self.expr(g, Use::Read);
                    }
                    match &arm.body {
                        ArmBody::Expr(b) => self.expr(b, Use::Read),
                        ArmBody::Block(b) => self.block(b),
                        ArmBody::Return(Some(b)) => self.expr(b, Use::Read),
                        ArmBody::Return(None) | ArmBody::Break(_) | ArmBody::Continue(_) => {}
                    }
                }
            }
            ExprKind::Arrow(id) => self.arrow(*id),
            ExprKind::Asm(asm) => {
                if self.depth == 0 {
                    self.report(
                        Power::Asm,
                        "`asm` needs `unsafe`".to_owned(),
                        e.span,
                        "this runs instructions no check can see into".to_owned(),
                    );
                }
                asm.ins.iter().for_each(|(_, v)| self.expr(v, Use::Read));
                for v in asm.outs.iter().filter_map(|(_, v)| v.as_ref()) {
                    self.expr(v, Use::Write);
                }
            }
            ExprKind::Destructure { pat, value } => {
                for place in pat.places() {
                    self.expr(place, Use::Write);
                }
                self.expr(value, Use::Read);
            }
        }
    }

    /// The source under `span`.
    fn text(&self, span: Span) -> String {
        if span.is_dummy() {
            return String::new();
        }
        self.tcx.map().text(span).to_owned()
    }

    /// A read, write or borrow of `def`, if it is an `unsafe let` (powers 4 and 5).
    fn static_use(&mut self, def: DefId, span: Span, how: Use) {
        let data = self.tcx.def(def);
        if data.kind != DefKind::Static || self.depth > 0 {
            return;
        }
        let name = data
            .name()
            .map_or_else(String::new, |n| n.as_str().to_owned());
        let power = if data.attrs.at.is_some() {
            Power::At
        } else {
            Power::Static
        };
        let verb = match how {
            Use::Read => "reads",
            Use::Write => "writes",
            Use::Borrow => "borrows",
        };
        self.report(
            power,
            format!("using `{name}`, an `unsafe let`, needs `unsafe`"),
            span,
            format!("this {verb} the static storage `{name}`"),
        );
    }

    /// A dereference of the raw pointer `ptr` at `span`: a `*p` place (`method` is
    /// `None`) or a `*T` method (power 1), then EN0828's check.
    fn deref(&mut self, span: Span, ptr: &Expr, method: Option<&str>, how: Use) {
        let writes = match method {
            Some(name) => name.starts_with("write"),
            None => how == Use::Write,
        };
        if self.depth == 0 {
            let message = match (writes, how, method) {
                (true, _, _) => "writing through a raw pointer needs `unsafe`",
                (false, Use::Borrow, None) => "borrowing through a raw pointer needs `unsafe`",
                _ => "reading through a raw pointer needs `unsafe`",
            };
            let shown = self.tcx.ty_string(ptr.ty);
            let target = self.text(ptr.span);
            let label = match method {
                Some(name) => format!(
                    "`{name}` dereferences `{target}`, {} `{shown}`",
                    crate::classes::sig::article(&shown)
                ),
                None => format!(
                    "this dereferences `{target}`, {} `{shown}`",
                    crate::classes::sig::article(&shown)
                ),
            };
            self.report(Power::Deref, message.to_owned(), span, label);
            return;
        }
        let Some(param) = self.raw_param(ptr) else {
            return;
        };
        if !self.warned.insert(param) {
            return;
        }
        let body = self.body;
        let pname = body.locals[param]
            .name
            .map_or_else(String::new, |n| n.as_str().to_owned());
        let fname = match body.owner {
            BodyOwner::Fn(def) => self
                .tcx
                .def(def)
                .name()
                .map_or_else(String::new, |n| n.as_str().to_owned()),
            _ => String::new(),
        };
        let verb = if writes { "writes" } else { "reads" };
        self.found.push(
            Diagnostic::new(
                Code::EN0828,
                format!("`{fname}` {verb} through the raw pointer `{pname}`"),
                span,
                format!("`{pname}` holds whatever address a caller passes"),
            )
            .with_help(Help::text("mark it `unsafe function`, or take a reference")),
        );
    }

    /// The raw-pointer parameter `e` is, directly or through `add`, `sub` and raw
    /// pointer casts.
    fn raw_param(&self, e: &Expr) -> Option<LocalId> {
        match &e.kind {
            ExprKind::Local(l) if self.raw_params.contains(l) => Some(*l),
            ExprKind::Cast(inner, CastKind::RawToRaw) => self.raw_param(inner),
            ExprKind::Call {
                callee: Callee::Fn(f),
                receiver: Some(r),
                ..
            } if matches!(
                self.tcx.def(f.def).name().map(|n| n.as_str()),
                Some("add" | "sub")
            ) =>
            {
                self.raw_param(r)
            }
            _ => None,
        }
    }

    /// The checks of a call's callee at `span`.
    fn callee(&mut self, callee: &Callee, span: Span, receiver: Option<&Expr>) {
        match callee {
            Callee::Fn(f) | Callee::Super(f) => self.call_def(f.def, span, receiver),
            Callee::Foreign(def) => self.call_def(*def, span, receiver),
            Callee::BoundMember { found, .. } => self.call_def(*found, span, receiver),
            Callee::SuperCtor {
                ctor: Some(def), ..
            } => self.call_def(*def, span, None),
            Callee::Intrinsic(kind, _) => self.call_intrinsic(*kind, span, receiver),
            Callee::HostCall(id) => {
                if self.depth == 0 {
                    let name = self.tcx.host_call_name(*id);
                    self.report(
                        Power::Call,
                        format!("calling `{name}` needs `unsafe`"),
                        span,
                        format!("`{name}` is a `declare function`"),
                    );
                }
            }
            Callee::FnPtr(f) => {
                self.call_pointer(f, span);
                // The callee position is an expression too: `(*p)()` reads
                // through `p`, `pick()()` calls `pick` (powers 1 and 2).
                self.expr(f, Use::Read);
            }
            Callee::SuperCtor { ctor: None, .. } | Callee::Closure(_) | Callee::Form(_) => {}
        }
    }

    /// A call of `def`: EN0807 for an `@interrupt` function, EN0907 for a
    /// `@requires` one, else EN0801 for an `unsafe` or `declare` one; an `unsafe`
    /// pointer method on a raw receiver is a dereference.
    fn call_def(&mut self, def: DefId, span: Span, receiver: Option<&Expr>) {
        let tcx = self.tcx;
        let data = tcx.def(def);
        let name = data
            .name()
            .map_or_else(String::new, |n| n.as_str().to_owned());
        if data.attrs.interrupt.is_some() {
            self.found.push(Diagnostic::new(
                Code::EN0807,
                "an interrupt handler can't be called",
                span,
                format!("`{name}` is an `@interrupt` function, which only the CPU calls"),
            ));
            return;
        }
        let unsafety = tcx.sig_opt(def).is_some_and(|s| s.unsafety);
        let declared = data.kind == DefKind::DeclareFn;
        if !data.attrs.requires.is_empty() {
            if self.depth == 0 {
                let features: Vec<String> = data
                    .attrs
                    .requires
                    .iter()
                    .map(|f| format!("`{}`", f.name()))
                    .collect();
                let mut diag = Diagnostic::new(
                    Code::EN0907,
                    format!(
                        "calling `{name}` needs `unsafe`, because it requires {}",
                        features.join(", ")
                    ),
                    span,
                    "the CPU this runs on may lack what it requires",
                );
                diag = self.with_wrap_help(diag, Power::Call);
                self.found.push(diag);
            }
            return;
        }
        if !unsafety && !declared {
            return;
        }
        if let Some(r) = receiver
            && matches!(tcx.kind(r.ty), TyKind::Raw(_))
            && is_pointer_access(&name)
        {
            self.deref(span, r, Some(&name), Use::Read);
            return;
        }
        if self.depth > 0 {
            return;
        }
        let label = if declared {
            format!("`{name}` is a `declare function`")
        } else {
            format!("`{name}` is `unsafe`")
        };
        self.report(
            Power::Call,
            format!("calling `{name}` needs `unsafe`"),
            span,
            label,
        );
    }

    /// A call of an intrinsic: an access through a raw receiver, or a call, when its
    /// safety bit is clear.
    fn call_intrinsic(&mut self, kind: IntrinsicKind, span: Span, receiver: Option<&Expr>) {
        if kind.is_safe() {
            return;
        }
        let name = intrinsic_member(self.tcx, kind.name())
            .unwrap_or_else(|| kind.name().name().to_owned());
        if let Some(r) = receiver
            && matches!(self.tcx.kind(r.ty), TyKind::Raw(_))
        {
            self.deref(span, r, Some(&name), Use::Read);
            return;
        }
        if self.depth == 0 {
            self.report(
                Power::Call,
                format!("calling `{name}` needs `unsafe`"),
                span,
                format!("`{name}` is `unsafe`"),
            );
        }
    }

    /// A call through an `fn` value: `unsafe fn` values and `@abi` pointers.
    fn call_pointer(&mut self, f: &Expr, span: Span) {
        let TyKind::FnPtr(abi, sig) = self.tcx.kind(f.ty) else {
            return;
        };
        let unsafety = self.tcx.fn_sig(sig).unsafety;
        if (!unsafety && abi == Abi::Enrang) || self.depth > 0 {
            return;
        }
        let name = match &f.kind {
            ExprKind::Local(l) => self.body.locals[*l]
                .name
                .map_or_else(|| self.text(f.span), |n| n.as_str().to_owned()),
            _ => self.text(f.span),
        };
        let label = match abi.name() {
            Some(abi) if !unsafety => {
                format!("`{name}` runs foreign code through `@abi(\"{abi}\")`")
            }
            _ => format!("`{name}` is an `unsafe fn`"),
        };
        self.report(
            Power::Call,
            format!("calling `{name}` needs `unsafe`"),
            span,
            label,
        );
    }

    /// EN0801 at `span`, with the power's rule and help.
    fn report(&mut self, power: Power, message: String, span: Span, label: String) {
        let diag = Diagnostic::new(Code::EN0801, message, span, label).rule(power.rule());
        let diag = self.with_wrap_help(diag, power);
        self.found.push(diag);
    }

    /// The help that wraps the innermost statement in `unsafe { ... }`.
    fn with_wrap_help(&self, diag: Diagnostic, power: Power) -> Diagnostic {
        match self.stmt {
            Some(StmtAt {
                span,
                declares: false,
            }) => diag.with_help(Help::suggest(
                power.help(),
                vec![
                    Edit::insert(span.lo, "unsafe { "),
                    Edit::insert(span.hi, " }"),
                ],
            )),
            _ => diag.with_help(Help::text(format!(
                "{}, in an `unsafe {{ }}` block",
                power.help()
            ))),
        }
    }
}

/// Whether `name` is one of the `*T` members that read or write the pointee.
fn is_pointer_access(name: &str) -> bool {
    matches!(
        name,
        "read" | "write" | "readVolatile" | "writeVolatile" | "readUnaligned" | "writeUnaligned"
    )
}

/// The name of the library member an intrinsic binds, the first by item path when
/// several do.
fn intrinsic_member(tcx: &Tcx, kind: IntrinsicName) -> Option<String> {
    let mut found: BTreeMap<String, String> = BTreeMap::new();
    for (_, data) in tcx.defs() {
        if data.attrs.intrinsic == Some(kind)
            && let Some(name) = data.name()
        {
            found.insert(data.path.to_string(), name.as_str().to_owned());
        }
    }
    found.into_values().next()
}
