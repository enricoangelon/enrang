//! The MIR text form, printing side (ARCHITECTURE 2.5 "Text form"; M3 plan b.6).
//!
//! A printed module is `[target "..";] [module "..";]`, the declarations its bodies
//! reference in `ItemPath` order (`decls.rs`), then the bodies in owner order: the
//! statements body, then definitions by `ItemPath`, each arrow after its parent in
//! `ArrowId` order. Fields and cases print by name, tuple parts and switch values by
//! number; spans never print. `parse.rs` reads exactly this text back, and
//! `print_module(parse_module(t))` is `t` for any printed `t`.

use std::fmt::Write as _;

use enrang_base::Idx;
use enrang_hir::{
    AluOp, CastKind, ConstTree, ConstValue, ConvKind, DefId, Fact, FieldIdx, FnRef, IntrinsicKind,
    ItemPath, ModulePath, PathStep, Perm, Reason, RecordKind, Repr, Tcx, Ty, TyKind, VariantIdx,
};

use crate::body::{
    AggregateKind, BinOp, Body, BodyOwner, BorrowOrigin, Callee, CaptureKind, CheckedOp,
    ClassHolder, ClassOp, ClosureFn, ConstKind, DropOrigin, FormCall, LocalKind, LoopRole,
    LoopSource, MirPhase, MoveStep, Operand, Place, Proj, Rvalue, ShimKind, Statement,
    StatementKind, Terminator, TerminatorKind, UnOp, UnsafeKind,
};
use crate::decls;
use crate::ids::Local;
use crate::proj::{PlaceTy, variant_name};

/// The module a printed text is in when it names none.
pub const DEFAULT_MODULE: &str = "main";
/// The target a printed text is for when it names none (plan b.6, choice).
pub const DEFAULT_TARGET: &str = "x86_64-linux";

/// Prints `b` with the declarations it references (A:803).
pub fn print_body(tcx: &Tcx, b: &Body) -> String {
    print_module(tcx, [b])
}

/// Prints one module: the declarations every body references, once, then each
/// body in owner order.
pub fn print_module<'a>(tcx: &Tcx, bodies: impl IntoIterator<Item = &'a Body>) -> String {
    let mut bodies: Vec<&Body> = bodies.into_iter().collect();
    let module = bodies
        .iter()
        .find_map(|b| owner_module(tcx, b.owner))
        .unwrap_or(ModulePath::new(DEFAULT_MODULE));
    bodies.sort_by_cached_key(|b| owner_key(tcx, b.owner));
    let p = Printer { tcx, module };
    let mut out = String::new();
    let target: &str = &tcx.target().name;
    if target != DEFAULT_TARGET {
        let _ = writeln!(out, "target {};", quote(target));
    }
    if module.as_str() != DEFAULT_MODULE {
        let _ = writeln!(out, "module {};", quote(module.as_str()));
    }
    out.push_str(&decls::print_decls(&p, &bodies));
    for b in bodies {
        if !out.is_empty() {
            out.push('\n');
        }
        p.body(b, &mut out);
    }
    out
}

/// The module whose items a body's owner belongs to.
fn owner_module(tcx: &Tcx, owner: BodyOwner) -> Option<ModulePath> {
    let of_hir = |o: enrang_hir::BodyOwner| match o {
        enrang_hir::BodyOwner::Fn(d)
        | enrang_hir::BodyOwner::Const(d)
        | enrang_hir::BodyOwner::Test(d) => tcx.def(d).path.module,
        enrang_hir::BodyOwner::Statements(m) => tcx.module(m).path,
    };
    match owner {
        BodyOwner::Fn(d) | BodyOwner::Test(d) => Some(tcx.def(d).path.module),
        BodyOwner::Statements(m) => Some(tcx.module(m).path),
        BodyOwner::Arrow(parent, _) => Some(of_hir(parent)),
        BodyOwner::Shim(_) => None,
    }
}

/// Owner order (plan b.6): the statements body and its arrows first, then by
/// path, an arrow after its parent by `ArrowId`, shims last by their text.
fn owner_key(tcx: &Tcx, owner: BodyOwner) -> (u8, Option<ItemPath>, u32, String) {
    let parent = |o: enrang_hir::BodyOwner| match o {
        enrang_hir::BodyOwner::Fn(d)
        | enrang_hir::BodyOwner::Const(d)
        | enrang_hir::BodyOwner::Test(d) => (1, Some(tcx.def(d).path.clone())),
        enrang_hir::BodyOwner::Statements(_) => (0, None),
    };
    match owner {
        BodyOwner::Statements(_) => (0, None, 0, String::new()),
        BodyOwner::Fn(d) | BodyOwner::Test(d) => {
            (1, Some(tcx.def(d).path.clone()), 0, String::new())
        }
        BodyOwner::Arrow(o, a) => {
            let (rank, path) = parent(o);
            (rank, path, a.0 + 1, String::new())
        }
        BodyOwner::Shim(k) => {
            let p = Printer {
                tcx,
                module: ModulePath::new(DEFAULT_MODULE),
            };
            (2, None, 0, p.shim(k))
        }
    }
}

/// A string literal as the text form writes it.
pub(crate) fn quote(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            '\0' => out.push_str("\\0"),
            c if c.is_control() => {
                let _ = write!(out, "\\u{{{:x}}}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// A float constant: Rust's shortest round-trip spelling, `inf`, `-inf`, or the
/// bits of a NaN.
fn float_text(tcx: &Tcx, bits: u64, ty: Ty) -> String {
    let value = match tcx.kind(ty) {
        TyKind::Float(enrang_hir::FloatTy::F32) => f64::from(f32::from_bits(bits as u32)),
        _ => f64::from_bits(bits),
    };
    if value.is_nan() {
        format!("nan({bits:#x})")
    } else if value.is_infinite() {
        if value > 0.0 { "inf" } else { "-inf" }.to_owned()
    } else {
        let text = match tcx.kind(ty) {
            TyKind::Float(enrang_hir::FloatTy::F32) => format!("{:?}", f32::from_bits(bits as u32)),
            _ => format!("{value:?}"),
        };
        if text.contains(['.', 'e']) {
            text
        } else {
            format!("{text}.0")
        }
    }
}

/// The class a constructor body builds, whose fields `overridden(f)` names.
pub(crate) fn ctor_class(tcx: &Tcx, b: &Body) -> Option<Ty> {
    let BodyOwner::Fn(d) = b.owner else {
        return None;
    };
    let adt = tcx.adt_of(tcx.def(d).parent?)?;
    Some(tcx.adt_identity(adt))
}

/// What every printing function needs: the types, and the module paths print
/// relative to.
pub(crate) struct Printer<'t> {
    pub tcx: &'t Tcx,
    pub module: ModulePath,
}

impl Printer<'_> {
    pub fn ty(&self, t: Ty) -> String {
        self.tcx.ty_string(t)
    }

    /// An item path, its module first when it is not the printed module, an
    /// overload's parameter types as strings.
    pub fn path(&self, path: &ItemPath) -> String {
        self.path_with_args(path, &[])
    }

    /// A path whose segments carry type arguments (`Stack<i64>::pop`).
    pub fn path_with_args(&self, path: &ItemPath, args: &[(usize, Vec<String>)]) -> String {
        let mut out = String::new();
        if path.module != self.module {
            let _ = write!(out, "{}::", quote(path.module.as_str()));
        }
        for (i, seg) in path.segments.iter().enumerate() {
            if i > 0 {
                out.push_str("::");
            }
            out.push_str(seg.as_str());
            if let Some((_, parts)) = args.iter().find(|(at, _)| *at == i)
                && !parts.is_empty()
            {
                let _ = write!(out, "<{}>", parts.join(", "));
            }
        }
        if let Some(overload) = &path.overload {
            let parts: Vec<String> = overload.iter().map(|s| quote(s)).collect();
            let _ = write!(out, "@[{}]", parts.join(", "));
        }
        out
    }

    pub fn def_path(&self, d: DefId) -> String {
        self.path(&self.tcx.def(d).path)
    }

    /// Field `f` of `pt` by name; a tuple part, or a field of no known type, by
    /// number.
    pub fn field(&self, pt: Option<PlaceTy>, f: FieldIdx) -> String {
        let name = pt.and_then(|pt| pt.field_name(self.tcx, f));
        name.map_or_else(|| f.index().to_string(), |n| n.to_string())
    }

    /// Case `v` of `ty` by name, or by number.
    pub fn case(&self, ty: Option<Ty>, v: VariantIdx) -> String {
        let name = ty.and_then(|t| variant_name(self.tcx, t, v));
        name.map_or_else(|| v.index().to_string(), |n| n.to_string())
    }

    /// `::Case` of a case, nothing for a class.
    fn case_suffix(&self, pt: PlaceTy) -> String {
        let name = pt.variant.and_then(|v| variant_name(self.tcx, pt.ty, v));
        name.map(|n| format!("::{n}")).unwrap_or_default()
    }

    /// A function with its type arguments, the parent's on the parent segment.
    pub fn fn_ref(&self, f: FnRef) -> String {
        let path = &self.tcx.def(f.def).path;
        let args: Vec<String> = self.tcx.list(f.args).iter().map(|&t| self.ty(t)).collect();
        let own = self
            .tcx
            .sig_opt(f.def)
            .map_or(args.len(), |s| self.tcx.generics(s.generics).params.len())
            .min(args.len());
        let split = args.len() - own;
        let last = path.segments.len().saturating_sub(1);
        let mut parts = vec![(last, args[split..].to_vec())];
        if split > 0 && last > 0 {
            parts.push((last - 1, args[..split].to_vec()));
        }
        self.path_with_args(path, &parts)
    }

    // -----------------------------------------------------------------------------
    // Places, operands, constants.

    pub fn place(&self, b: &Body, p: Place) -> String {
        let projs: Vec<Proj> = b.projs(p).to_vec();
        self.place_from(b.locals[p.local].ty, p.local, &projs)
    }

    /// `local` with `projs`, its first type `ty`.
    pub fn place_from(&self, ty: Ty, local: Local, projs: &[Proj]) -> String {
        let mut s = local.to_string();
        let mut pt = Some(PlaceTy::of(ty));
        let mut deref = false;
        for &proj in projs {
            if deref && !matches!(proj, Proj::Deref | Proj::Variant(_)) {
                s = format!("({s})");
                deref = false;
            }
            match proj {
                Proj::Deref => {
                    s = format!("*{s}");
                    deref = true;
                }
                Proj::Field(f) => {
                    let _ = write!(s, ".{}", self.field(pt, f));
                }
                Proj::Variant(v) => {
                    s = format!("({s} as {})", self.case(pt.map(|t| t.ty), v));
                    deref = false;
                }
                Proj::Index(l) => {
                    let _ = write!(s, "[{l}]");
                }
                Proj::ConstIndex(n) => {
                    let _ = write!(s, "[{n}]");
                }
            }
            pt = pt.and_then(|pt| pt.project(self.tcx, proj));
        }
        s
    }

    pub fn operand(&self, b: &Body, op: &Operand) -> String {
        match op {
            Operand::Copy(p) => format!("copy {}", self.place(b, *p)),
            Operand::Move(p) => format!("move {}", self.place(b, *p)),
            Operand::Const(c) => {
                let value = match &c.kind {
                    ConstKind::Value(v) => self.const_value(Some(b), v),
                    ConstKind::LiteralAddr(k) => format!("static_addr(literal#{k})"),
                };
                format!("const {value}: {}", self.ty(c.ty))
            }
        }
    }

    fn operands(&self, b: &Body, ops: &[Operand]) -> String {
        let parts: Vec<String> = ops.iter().map(|op| self.operand(b, op)).collect();
        parts.join(", ")
    }

    /// A scalar constant without its type. `body` is the constructor whose class an
    /// `overridden(f)` names a field of.
    pub fn const_value(&self, body: Option<&Body>, v: &ConstValue) -> String {
        match *v {
            ConstValue::Int(bits, _) => v
                .as_i128(self.tcx)
                .map_or_else(|| bits.to_string(), |n| n.to_string()),
            ConstValue::Float(bits, t) => float_text(self.tcx, bits, t),
            ConstValue::Bool(b) => b.to_string(),
            ConstValue::Void => "void".to_owned(),
            ConstValue::Str(id) => quote(&self.tcx.str(id)),
            ConstValue::FnAddr(f) => format!("fn {}", self.fn_ref(f)),
            ConstValue::StaticAddr(d) => format!("static_addr({})", self.def_path(d)),
            ConstValue::Overridden(f) => {
                let class = body.and_then(|b| ctor_class(self.tcx, b));
                format!("overridden({})", self.field(class.map(PlaceTy::of), f))
            }
        }
    }

    /// A constant tree (a constant's value, a literal static), its scalars without
    /// types, which the reader takes from the declared type.
    pub fn const_tree(&self, ty: Ty, t: &ConstTree) -> String {
        let list = |items: &[ConstTree], tys: &dyn Fn(usize) -> Ty| -> String {
            let parts: Vec<String> = items
                .iter()
                .enumerate()
                .map(|(i, c)| self.const_tree(tys(i), c))
                .collect();
            parts.join(", ")
        };
        match t {
            ConstTree::Scalar(v) => self.const_value(None, v),
            ConstTree::Array(items) => {
                let elem = match self.tcx.kind(ty) {
                    TyKind::Fixed(e, _) | TyKind::Array(e) | TyKind::Slice(e) => e,
                    _ => ty,
                };
                format!("[{}]", list(items, &|_| elem))
            }
            ConstTree::Tuple(items) => {
                let parts = match self.tcx.kind(ty) {
                    TyKind::Tuple(l) => self.tcx.list(l).to_vec(),
                    _ => Vec::new(),
                };
                format!(
                    "tuple({})",
                    list(items, &|i| parts.get(i).copied().unwrap_or(ty))
                )
            }
            ConstTree::Object(items) => {
                let fields = match self.tcx.kind(ty) {
                    TyKind::Object(s) => self.tcx.shape(s).fields.clone(),
                    _ => Vec::new(),
                };
                let parts: Vec<String> = items
                    .iter()
                    .zip(&fields)
                    .map(|(c, (name, t))| format!("{name}: {}", self.const_tree(*t, c)))
                    .collect();
                format!("object {{ {} }}", parts.join(", "))
            }
            ConstTree::Adt {
                adt,
                variant,
                fields,
            } => {
                let args = match self.tcx.kind(ty) {
                    TyKind::Adt(_, a) => a,
                    _ => self.tcx.empty_list(),
                };
                let head = self.ty(self.tcx.mk_adt(*adt, &self.tcx.list(args)));
                let case_ty = PlaceTy {
                    ty: self.tcx.mk_adt(*adt, &self.tcx.list(args)),
                    variant: *variant,
                };
                let parts: Vec<String> = fields
                    .iter()
                    .enumerate()
                    .map(|(i, c)| {
                        let f = FieldIdx::new(i);
                        let t = case_ty
                            .project(self.tcx, Proj::Field(f))
                            .map_or(ty, |pt| pt.ty);
                        format!(
                            "{}: {}",
                            self.field(Some(case_ty), f),
                            self.const_tree(t, c)
                        )
                    })
                    .collect();
                let case = self.case_suffix(case_ty);
                format!("{head}{case} {{ {} }}", parts.join(", "))
            }
            ConstTree::Null => "null".to_owned(),
            ConstTree::Present(inner) => {
                let payload = match self.tcx.kind(ty) {
                    TyKind::Nullable(t) => t,
                    _ => ty,
                };
                format!("present({})", self.const_tree(payload, inner))
            }
            ConstTree::View { elem, items } => {
                format!("view<{}>[{}]", self.ty(*elem), list(items, &|_| *elem))
            }
        }
    }

    // -----------------------------------------------------------------------------
    // Rvalues, statements, terminators.

    pub fn rvalue(&self, b: &Body, rv: &Rvalue) -> String {
        match rv {
            Rvalue::Use(op) => self.operand(b, op),
            Rvalue::Ref { place, origin } => {
                format!("&{} [{}]", self.place(b, *place), name_of(ORIGINS, origin))
            }
            Rvalue::AddrOf(p) => format!("addr_of {}", self.place(b, *p)),
            Rvalue::Binary(op, x, y) => format!(
                "{}({}, {})",
                name_of(BINOPS, op),
                self.operand(b, x),
                self.operand(b, y)
            ),
            Rvalue::Checked(op, x, y) => format!(
                "checked_{}({}, {})",
                name_of(CHECKED, op),
                self.operand(b, x),
                self.operand(b, y)
            ),
            Rvalue::Unary(op, x) => format!("{}({})", name_of(UNOPS, op), self.operand(b, x)),
            Rvalue::CheckedNeg(x) => format!("checked_neg({})", self.operand(b, x)),
            Rvalue::Cast(k, x, t) => format!(
                "cast({}, {}, {})",
                name_of(CASTS, k),
                self.operand(b, x),
                self.ty(*t)
            ),
            Rvalue::Convert(k, x) => {
                format!("convert({}, {})", name_of(CONVS, k), self.operand(b, x))
            }
            Rvalue::Aggregate(kind, ops) => self.aggregate(b, kind, ops),
            Rvalue::Discriminant(p) => format!("discriminant({})", self.place(b, *p)),
            Rvalue::Len(p) => format!("len({})", self.place(b, *p)),
            Rvalue::ClosureValue { func, env } => {
                let f = match func {
                    ClosureFn::Arrow(a) => format!("arrow#{}", a.0),
                    ClosureFn::Named(f) => format!("fn {}", self.fn_ref(*f)),
                    ClosureFn::FnValue => "fn_value".to_owned(),
                };
                format!("closure({f}, {})", self.place(b, *env))
            }
            Rvalue::ClosureReborrow(p) => format!("closure_reborrow({})", self.place(b, *p)),
            Rvalue::ArrowFn(a) => format!("arrow_fn#{}", a.0),
        }
    }

    fn aggregate(&self, b: &Body, kind: &AggregateKind, ops: &[Operand]) -> String {
        match kind {
            AggregateKind::Fixed(t) => format!("fixed<{}>[{}]", self.ty(*t), self.operands(b, ops)),
            AggregateKind::Repeat(n) => {
                let op = ops
                    .first()
                    .map_or_else(String::new, |op| self.operand(b, op));
                format!("repeat({op}; {n})")
            }
            AggregateKind::Tuple => format!("tuple({})", self.operands(b, ops)),
            AggregateKind::Adt { adt, variant, args } => {
                let ty = self.tcx.mk_adt(*adt, &self.tcx.list(*args));
                let pt = PlaceTy {
                    ty,
                    variant: *variant,
                };
                let case = self.case_suffix(pt);
                format!("{}{case} {{{}}}", self.ty(ty), self.fields(b, pt, ops))
            }
            AggregateKind::Object(shape) => {
                let ty = self.tcx.mk_object_shape((*self.tcx.shape(*shape)).clone());
                format!(
                    "object {} {{{}}}",
                    self.ty(ty),
                    self.fields(b, PlaceTy::of(ty), ops)
                )
            }
            AggregateKind::Present => {
                let op = ops
                    .first()
                    .map_or_else(String::new, |op| self.operand(b, op));
                format!("present({op})")
            }
            AggregateKind::Null => "null".to_owned(),
            AggregateKind::ClosureEnv => format!("env({})", self.operands(b, ops)),
        }
    }

    /// ` name: op, name: op ` in field order, or `{}` when empty.
    fn fields(&self, b: &Body, pt: PlaceTy, ops: &[Operand]) -> String {
        if ops.is_empty() {
            return String::new();
        }
        let parts: Vec<String> = (ops.iter().enumerate())
            .map(|(i, op)| {
                format!(
                    "{}: {}",
                    self.field(Some(pt), FieldIdx::new(i)),
                    self.operand(b, op)
                )
            })
            .collect();
        format!(" {} ", parts.join(", "))
    }

    pub fn statement(&self, b: &Body, st: &Statement) -> String {
        let mut s = match &st.kind {
            StatementKind::Assign { dest, value } => {
                format!("{} = {}", self.place(b, *dest), self.rvalue(b, value))
            }
            StatementKind::CheckBounds { index, len } => format!(
                "check_bounds({}, {})",
                self.operand(b, index),
                self.operand(b, len)
            ),
            StatementKind::CheckTag { place, variant } => {
                let ty = b.place_ty(self.tcx, *place).map(|pt| pt.ty);
                format!(
                    "check_tag({}, {})",
                    self.place(b, *place),
                    self.case(ty, *variant)
                )
            }
            StatementKind::CheckClass { place, op, via } => {
                let op = match op {
                    ClassOp::MoveThis(name) => format!("move_this({name})"),
                    op => name_of(CLASS_OPS, op).to_owned(),
                };
                let via = name_of(HOLDERS, via);
                format!("check_class({}, {op}, {via})", self.place(b, *place))
            }
            StatementKind::SetTable { place, class } => {
                format!("set_table({}, {})", self.place(b, *place), self.ty(*class))
            }
            StatementKind::FieldInit { field, value } => format!(
                "field_init({}, {})",
                self.place(b, *field),
                self.operand(b, value)
            ),
            StatementKind::StorageLive(l) => format!("storage_live({l})"),
            StatementKind::StorageDead(l) => format!("storage_dead({l})"),
            StatementKind::Drop(p, origin) => {
                let tail = match origin {
                    DropOrigin::Scope => "",
                    DropOrigin::Assign => " [assign]",
                };
                format!("drop({}){tail}", self.place(b, *p))
            }
            StatementKind::DropGlue(p) => format!("drop_glue({})", self.place(b, *p)),
            StatementKind::Intrinsic { kind, args, dest } => format!(
                "{}intrinsic {}({})",
                self.dest(b, *dest),
                self.intrinsic(*kind),
                self.operands(b, args)
            ),
            StatementKind::Asm(asm) => {
                let mut parts = vec![quote(asm.template.as_str())];
                for (name, op) in &asm.ins {
                    parts.push(format!("{name} in {}", self.operand(b, op)));
                }
                for (name, p) in &asm.outs {
                    match p {
                        Some(p) => parts.push(format!("{name} out {}", self.place(b, *p))),
                        None => parts.push(format!("{name} out")),
                    }
                }
                for c in &asm.clobbers {
                    parts.push(format!("clobber {}", quote(c.as_str())));
                }
                format!("asm({})", parts.join(", "))
            }
            StatementKind::HostCall { id, args, dest } => format!(
                "{}host_call {}({})",
                self.dest(b, *dest),
                quote(self.tcx.host_call_name(*id).as_str()),
                self.operands(b, args)
            ),
            StatementKind::Nop => "nop".to_owned(),
        };
        if let Some(r) = st.region {
            let _ = write!(s, " @ {r}");
        }
        s
    }

    fn dest(&self, b: &Body, dest: Option<Place>) -> String {
        dest.map(|p| format!("{} = ", self.place(b, p)))
            .unwrap_or_default()
    }

    /// `SizeOf<i64>`, `AtomicAlu<add>`, `CpuHas<sse2>`, `OffsetOf<P, x>`.
    pub fn intrinsic(&self, k: IntrinsicKind) -> String {
        let name = k.name().name();
        let payload = match k {
            IntrinsicKind::AtomicAlu(op) => Some(name_of(ALU_OPS, &op).to_owned()),
            IntrinsicKind::AtomicIncDecTest(b) | IntrinsicKind::AtomicBitTest(b) => {
                Some(b.to_string())
            }
            IntrinsicKind::CpuHas(f) => Some(quote(f.name())),
            IntrinsicKind::SizeOf(t)
            | IntrinsicKind::AlignOf(t)
            | IntrinsicKind::AllocArray(t)
            | IntrinsicKind::SliceFromRaw(t) => Some(self.ty(t)),
            IntrinsicKind::OffsetOf(t, f) => Some(format!(
                "{}, {}",
                self.ty(t),
                self.field(Some(PlaceTy::of(t)), f)
            )),
            _ => None,
        };
        match payload {
            Some(p) => format!("{name}<{p}>"),
            None => name.to_owned(),
        }
    }

    pub fn callee(&self, b: &Body, c: &Callee) -> String {
        match c {
            Callee::Fn(f) => self.fn_ref(*f),
            Callee::FnPtr(op) => format!("fnptr({})", self.operand(b, op)),
            Callee::ClosureLocal(l) => format!("closure {l}"),
            Callee::Foreign(f) => format!("foreign {}", self.def_path(f.def)),
            Callee::Virtual { method, table } => {
                format!(
                    "virtual {} [{}]",
                    self.fn_ref(*method),
                    self.operand(b, table)
                )
            }
            Callee::Form(FormCall::Expect { matcher, negated }) => {
                let not = if *negated { "not " } else { "" };
                format!("form expect {not}{matcher}")
            }
            Callee::Form(form) => format!("form {}", name_of(FORMS, form)),
            Callee::FormParts { form, parts } => {
                let parts: Vec<String> = parts.iter().map(u32::to_string).collect();
                format!("form {}[{}]", name_of(FORMS, form), parts.join(", "))
            }
            Callee::NamedFill { class, left_out } => {
                let names: Vec<String> = (left_out.iter())
                    .map(|&f| self.field(Some(PlaceTy::of(*class)), f))
                    .collect();
                format!(
                    "named_fill {} leaving({})",
                    self.ty(*class),
                    names.join(", ")
                )
            }
            Callee::ImplicitCtor { class } => format!("implicit_ctor {}", self.ty(*class)),
        }
    }

    pub fn terminator(&self, b: &Body, t: &Terminator) -> String {
        let mut s = match &t.kind {
            TerminatorKind::Goto(bb) => format!("goto {bb}"),
            TerminatorKind::Switch {
                value,
                arms,
                otherwise,
            } => {
                let mut parts: Vec<String> =
                    arms.iter().map(|(v, bb)| format!("{v}: {bb}")).collect();
                if let Some(o) = otherwise {
                    parts.push(format!("otherwise: {o}"));
                }
                format!("switch {} [{}]", self.operand(b, value), parts.join(", "))
            }
            TerminatorKind::Call {
                callee,
                args,
                dest,
                next,
            } => format!(
                "{} = {}({}) -> {}",
                self.place(b, *dest),
                self.callee(b, callee),
                self.operands(b, args),
                next.map_or_else(|| "!".to_owned(), |n| n.to_string())
            ),
            TerminatorKind::Return => "return".to_owned(),
            TerminatorKind::Unreachable => "unreachable".to_owned(),
        };
        if let Some(r) = t.region {
            let _ = write!(s, " @ {r}");
        }
        s
    }

    // -----------------------------------------------------------------------------
    // Bodies.

    pub fn shim(&self, k: ShimKind) -> String {
        match k {
            ShimKind::DropGlue(t)
            | ShimKind::CloneGlue(t)
            | ShimKind::EqGlue(t)
            | ShimKind::ShowGlue(t)
            | ShimKind::DisplayGlue(t)
            | ShimKind::NamedFill(t) => {
                let name = TY_SHIMS.iter().find(|s| s.0(t) == k).map_or("", |s| s.1);
                format!("{name}({})", self.ty(t))
            }
            ShimKind::FnAsClosure(f) => format!("fn_as_closure({})", self.fn_ref(f)),
            ShimKind::StringForm(f) => format!("string_form({})", self.fn_ref(f)),
            ShimKind::StringFormEnv { from, to } => {
                format!("string_form_env({}, {})", self.ty(from), self.ty(to))
            }
        }
    }

    /// The parameter list of a body with no declaration of its own.
    fn arg_list(&self, b: &Body) -> String {
        let parts: Vec<String> = b
            .args()
            .map(|l| format!("{l}: {}", self.ty(b.locals[l].ty)))
            .collect();
        format!("({})", parts.join(", "))
    }

    /// The body's head: a function's declaration, or the owner and its arguments.
    fn head(&self, b: &Body) -> (String, usize) {
        let simple = |owner: String| {
            let head = format!("{owner} {} -> {}", self.arg_list(b), self.ty(b.ret_ty()));
            (head, b.arg_count as usize)
        };
        match b.owner {
            BodyOwner::Fn(d) => decls::fn_head(self, d),
            BodyOwner::Statements(_) => simple("statements".to_owned()),
            BodyOwner::Test(d) => simple(format!("test {}", self.def_path(d))),
            BodyOwner::Arrow(parent, a) => {
                let parent = match parent {
                    enrang_hir::BodyOwner::Fn(d) => format!("fn {}", self.def_path(d)),
                    enrang_hir::BodyOwner::Const(d) => format!("const {}", self.def_path(d)),
                    enrang_hir::BodyOwner::Test(d) => format!("test {}", self.def_path(d)),
                    enrang_hir::BodyOwner::Statements(_) => "statements".to_owned(),
                };
                simple(format!("arrow#{} of {parent}", a.0))
            }
            BodyOwner::Shim(k) => simple(format!("shim {}", self.shim(k))),
        }
    }

    pub fn body(&self, b: &Body, out: &mut String) {
        let (head, declared) = self.head(b);
        let _ = writeln!(out, "{head} {{");
        if b.phase != MirPhase::Built {
            let _ = writeln!(out, "  phase {};", name_of(PHASES, &b.phase));
        }
        for (l, decl) in b.locals.iter_enumerated() {
            let known = l == Local::RETURN || (l.0 as usize) <= declared;
            let plain = matches!(decl.kind, LocalKind::Return | LocalKind::Arg);
            if known && plain && !decl.mutable && decl.name.is_none() {
                continue;
            }
            let kind = match decl.kind {
                LocalKind::Return | LocalKind::User => String::new(),
                LocalKind::Arg if known => String::new(),
                LocalKind::HiddenLoop(r) => format!(" #{}", name_of(LOOP_ROLES, &r)),
                k => format!(" {}", name_of(LOCAL_KINDS, &k)),
            };
            let mutable = if decl.mutable { "mut " } else { "" };
            let _ = write!(out, "  let {mutable}{l}: {}{kind};", self.ty(decl.ty));
            if let Some(name) = decl.name {
                let _ = write!(out, " // {name}");
            }
            out.push('\n');
        }
        for (r, region) in b.unsafe_regions.iter_enumerated() {
            let kind = name_of(REGION_KINDS, &region.kind);
            let parent = region
                .parent
                .map(|p| format!(" in {p}"))
                .unwrap_or_default();
            let _ = writeln!(out, "  region {r}: {kind}{parent};");
        }
        for c in &b.captures {
            let kind = name_of(CAPTURES, &c.kind);
            let _ = writeln!(out, "  capture {}: {} {kind};", c.name, self.ty(c.ty));
        }
        for (flag, key) in &b.drop_flags {
            let projs: Vec<Proj> = key
                .steps
                .iter()
                .flat_map(|s| match *s {
                    MoveStep::Field(f) => vec![Proj::Field(f)],
                    MoveStep::VariantField(v, f) => vec![Proj::Variant(v), Proj::Field(f)],
                })
                .collect();
            let place = self.place_from(b.locals[key.local].ty, key.local, &projs);
            let _ = writeln!(out, "  drop_flag {flag}: {place};");
        }
        for (k, lit) in b.literals.iter().enumerate() {
            let _ = writeln!(
                out,
                "  literal#{k}: {} = {};",
                self.ty(lit.ty),
                self.const_tree(lit.ty, &lit.value)
            );
        }
        self.meta(b, out);
        for (bb, block) in b.blocks.iter_enumerated() {
            let _ = writeln!(out, "  {bb}: {{");
            for st in &block.stmts {
                let _ = writeln!(out, "    {};", self.statement(b, st));
            }
            let _ = writeln!(out, "    {};", self.terminator(b, &block.term));
            out.push_str("  }\n");
        }
        out.push_str("}\n");
    }

    fn meta(&self, b: &Body, out: &mut String) {
        let m = &b.meta;
        for l in &m.loops {
            let source = match &l.source {
                LoopSource::Path(p) => format!("path {}", self.place(b, *p)),
                LoopSource::Once(local) => format!("once {local}"),
            };
            let _ = writeln!(
                out,
                "  loop l{}: {source} preheader {} head {} bind {} binding {};",
                l.id.0, l.preheader, l.head, l.bind, l.binding
            );
        }
        for (f, fact) in m.facts.iter_enumerated() {
            let mut s = fact.root.to_string();
            let mut pt = Some(PlaceTy::of(b.locals[fact.root].ty));
            for step in &fact.steps {
                let proj = match step {
                    PathStep::Field(i) => {
                        let _ = write!(s, ".{}", self.field(pt, *i));
                        Some(Proj::Field(*i))
                    }
                    PathStep::Deref => {
                        s.push_str(".*");
                        Some(Proj::Deref)
                    }
                    PathStep::Payload => {
                        s.push_str(".?");
                        pt = pt.and_then(|pt| {
                            pt.project(self.tcx, Proj::Variant(enrang_hir::VariantIdx::PRESENT))
                        });
                        Some(Proj::Field(enrang_hir::FieldIdx(0)))
                    }
                };
                pt = match proj {
                    Some(p) => pt.and_then(|pt| pt.project(self.tcx, p)),
                    None => pt,
                };
            }
            let what = match fact.fact {
                Fact::NonNull => "nonnull".to_owned(),
                Fact::Case(v) => format!("case {}", self.case(pt.map(|t| t.ty), v)),
            };
            let _ = writeln!(out, "  fact f{}: {s} {what};", f.index());
        }
        for r in &m.records {
            let kind = name_of(RECORDS, &r.kind);
            let _ = writeln!(
                out,
                "  record f{} at {} {} {kind};",
                r.fact.index(),
                r.at,
                r.slot
            );
        }
        for (f, at) in &m.narrowed_uses {
            let _ = writeln!(out, "  use f{} at {at};", f.index());
        }
        for (f, bb) in &m.fact_tests {
            let _ = writeln!(out, "  test f{} at {bb};", f.index());
        }
        for at in &m.assign_values {
            let _ = writeln!(out, "  assign_value {at};");
        }
        if let Some(l) = m.defaults_count {
            let _ = writeln!(out, "  defaults {l};");
        }
    }
}

/// The text form's name tables: each payload-free variant with its spelling,
/// which [`name_of`] prints and [`named`] reads.
macro_rules! names {
    ($($table:ident: $ty:ty = [$($v:ident $s:literal),* $(,)?];)*) => {
        $(pub(crate) const $table: &[($ty, &str)] = &[$((<$ty>::$v, $s)),*];)*
    };
}

names! {
    ORIGINS: BorrowOrigin = [Explicit "explicit", AutoBorrow "auto-borrow", Reborrow "reborrow",
        Destructure "destructure", ForOfElement "for-of-element", ForOfHidden "for-of-hidden",
        ClosureCapture "closure-capture", HiddenArg "hidden-arg", TempArg "temp-arg",
        CompoundTarget "compound-target", LiteralView "literal-view"];
    BINOPS: BinOp = [Add "add", Sub "sub", Mul "mul", Div "div", Rem "rem", Shl "shl", Shr "shr",
        Ushr "ushr", BitAnd "bit_and", BitOr "bit_or", BitXor "bit_xor", Eq "eq", Ne "ne",
        Lt "lt", Le "le", Gt "gt", Ge "ge"];
    CHECKED: CheckedOp = [Add "add", Sub "sub", Mul "mul", Div "div", Rem "rem", Shl "shl",
        Shr "shr", Ushr "ushr"];
    UNOPS: UnOp = [Not "not", BitNot "bit_not", Neg "neg"];
    CASTS: CastKind = [IntToInt "int_to_int", IntToFloat "int_to_float",
        FloatToFloat "float_to_float", FloatToInt "float_to_int", EnumToInt "enum_to_int",
        BoolToInt "bool_to_int", UsizeToRaw "usize_to_raw", RawToUsize "raw_to_usize",
        RefToRaw "ref_to_raw", RawToRaw "raw_to_raw"];
    CONVS: ConvKind = [FixedToSlice "fixed_to_slice", ArrayToSlice "array_to_slice",
        Upcast "upcast", BoxToInterface "box_to_interface", RefToInterface "ref_to_interface"];
    FORMS: FormCall = [Log "log", Error "error", WriteTo "write_to", Panic "panic",
        Template "template", ToString "to_string", Assert "assert", Unreachable "unreachable",
        FailureText "failure_text", FailureMove "failure_move", FailureCopy "failure_copy",
        IntoFailure "into_failure", Concat "concat", Append "append"];
    PHASES: MirPhase = [Built "built", Elaborated "elaborated", Mono "mono"];
    LOCAL_KINDS: LocalKind = [Arg "arg", Temp "temp", DropFlag "flag", ClosureEnv "env",
        User "user"];
    LOOP_ROLES: LoopRole = [Index "i", Length "n", Source "src", IntoIter "iter",
        RangeCursor "cur", RangeEnd "end"];
    REGION_KINDS: UnsafeKind = [Block "block", Asm "asm", WholeBody "whole"];
    CAPTURES: CaptureKind = [Path "path", ThroughRef "through_ref", ClosureParam "closure_param"];
    RECORDS: RecordKind = [CallArg "call_arg", Receiver "receiver", Copy "copy",
        Binding "binding", Capture "capture", HiddenArg "hidden_arg"];
    CLASS_OPS: ClassOp = [Unbox "unbox", Assign "assign", CopyOut "copy_out", Replace "replace",
        Swap "swap", Clone "clone"];
    HOLDERS: ClassHolder = [Box "box", Ref "ref"];
    PERMS: Perm = [Read "read", Write "write", Own "own"];
    ALU_OPS: AluOp = [Add "add", Sub "sub", And "and", Or "or", Xor "xor"];
    REPRS: Repr = [C "C", U8 "u8", U16 "u16", U32 "u32"];
    REASONS: Reason = [Declared "declared", ConstRoot "const_root", StringPart "string_part",
        RawDeref "raw_deref", AliasedParts "aliased", ConstLiteral "const_literal"];
}

/// `v`'s spelling in `table`, empty when it has none.
pub(crate) fn name_of<T: PartialEq>(table: &[(T, &'static str)], v: &T) -> &'static str {
    table.iter().find(|e| e.0 == *v).map_or("", |e| e.1)
}

/// The variant of `table` spelled `s`.
pub(crate) fn named<T: Clone>(table: &[(T, &str)], s: &str) -> Option<T> {
    table.iter().find(|e| e.1 == s).map(|e| e.0.clone())
}

/// The shims whose payload is a type, with their spellings.
pub(crate) const TY_SHIMS: [(fn(Ty) -> ShimKind, &str); 6] = [
    (ShimKind::DropGlue, "drop_glue"),
    (ShimKind::CloneGlue, "clone_glue"),
    (ShimKind::EqGlue, "eq_glue"),
    (ShimKind::ShowGlue, "show_glue"),
    (ShimKind::DisplayGlue, "display_glue"),
    (ShimKind::NamedFill, "named_fill"),
];
