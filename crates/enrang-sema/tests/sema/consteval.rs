//! The sema suite's cases for the const interpreter (owner 2E; plan d.14, g.2; SPEC
//! 4.9; ARCHITECTURE 4 "Const eval"), on hand-built typed HIR. Each case writes the
//! source a front end would read, builds the HIR typing would make of it, every span
//! pointing into that text, and evaluates it through `ConstState` on `i386-linux`
//! and `x86_64-linux`, the two pointer sizes. The contexts that reach the
//! interpreter from source (top-level `const`, `unsafe let`, enum values, lengths,
//! asserts; owner 4F) are checked from Enrang source in [`from_source`], at the end.

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::Arc;

use enrang_base::{BytePos, FileOrigin, IdVec, SourceMap, Span, intern};
use enrang_diag::{Code, Diagnostic, EntryKind, RenderOpts, render_text};
use enrang_hir::{
    Adjust, AdtDecl, AdtId, AdtKind, ArrayPart, BinOp, Block, Body, BodyOwner, Callee, CastKind,
    ClassDef, ClassModifier, CommonTypes, ConstTree, ConstValue, DefData, DefId, DefKind, EnumDef,
    EnumValues, Expr, ExprId, ExprKind, FieldDef, FieldIdx, FnRef, FormKind, IntTy, ItemPath,
    LocalDecl, LocalKind, LogOp, ModuleId, ModuleInfo, ModulePath, OptChain, OptMember, SpreadKind,
    Stmt, StmtKind, Tcx, TplPart, Ty, TyKind, UnOp, VariantDef, VariantIdx, VariantValue,
};
use enrang_sema::{ConstError, ConstState, MAX_VALUES};
use enrang_target::{TargetOpts, resolve};
use enrang_testkit::Harness;

/// A target of each pointer size (SPEC 11: `P` is 4 on `i386-*`, 8 on `x86_64-*`).
const TARGETS: [&str; 2] = ["i386-linux", "x86_64-linux"];

/// A hand-built program over one source text, on one target.
struct World {
    tcx: Tcx,
    map: Arc<SourceMap>,
    src: String,
    start: u32,
    module: ModuleId,
    bodies: BTreeMap<DefId, Arc<Body>>,
    state: ConstState,
    next: u32,
}

impl World {
    fn new(target: &str, src: &str) -> World {
        let (spec, _) = resolve(target, &TargetOpts::default()).expect("a target");
        let mut map = SourceMap::new();
        let file = map.add(
            PathBuf::from("src/main.en"),
            Arc::from(src),
            FileOrigin::User,
        );
        let start = map.file(file).start.0;
        let map = Arc::new(map);
        let mut tcx = Tcx::new(Arc::new(spec), Arc::clone(&map));
        let module = tcx.define_module(ModuleInfo::new(ModulePath::new("src/main"), false, file));
        World {
            tcx,
            map,
            src: src.to_owned(),
            start,
            module,
            bodies: BTreeMap::new(),
            state: ConstState::new(),
            next: 0,
        }
    }

    fn t(&self) -> CommonTypes {
        *self.tcx.common()
    }

    fn p(&self) -> u64 {
        u64::from(self.tcx.target().layout.ptr_bytes)
    }

    fn span_at(&self, at: usize, len: usize) -> Span {
        Span {
            lo: BytePos(self.start + at as u32),
            hi: BytePos(self.start + (at + len) as u32),
        }
    }

    /// The span of `needle`, which the source holds once.
    fn at(&self, needle: &str) -> Span {
        let found: Vec<usize> = self.src.match_indices(needle).map(|(i, _)| i).collect();
        assert_eq!(
            found.len(),
            1,
            "`{needle}` is not in the source exactly once"
        );
        self.span_at(found[0], needle.len())
    }

    /// The span of `needle` inside `context`, which the source holds once.
    fn at_in(&self, context: &str, needle: &str) -> Span {
        let outer = self.at(context);
        let offset = context.find(needle).expect("the needle is in its context");
        self.span_at((outer.lo.0 - self.start) as usize + offset, needle.len())
    }

    /// The span of the last `needle` inside `context`, which the source holds once.
    fn at_last_in(&self, context: &str, needle: &str) -> Span {
        let outer = self.at(context);
        let offset = context.rfind(needle).expect("the needle is in its context");
        self.span_at((outer.lo.0 - self.start) as usize + offset, needle.len())
    }

    fn text(&self, span: Span) -> &str {
        self.map.text(span)
    }

    /// Integer literals of `ty` written `items`, found one after another inside
    /// `context`.
    fn ints_in(&mut self, ty: Ty, context: &str, items: &[&str]) -> Vec<Expr> {
        let base = (self.at(context).lo.0 - self.start) as usize;
        let mut from = 0;
        let mut exprs = Vec::new();
        for item in items {
            let offset = from
                + context[from..]
                    .find(item)
                    .expect("the item is in its context");
            from = offset + item.len();
            let span = self.span_at(base + offset, item.len());
            exprs.push(self.int_at(ty, parse_int(item), span));
        }
        exprs
    }

    fn expr(&mut self, ty: Ty, span: Span, kind: ExprKind) -> Expr {
        let id = ExprId(self.next);
        self.next += 1;
        Expr::new(id, ty, span, kind)
    }

    /// An integer literal of `ty` with `value`, at `span`.
    fn int_at(&mut self, ty: Ty, value: i128, span: Span) -> Expr {
        let bits = match self.tcx.kind(ty) {
            TyKind::Int(int) => int.bits(self.p() as u32 * 8),
            TyKind::Raw(_) => self.p() as u32 * 8,
            other => panic!("not an integer type: {other:?}"),
        };
        let mask = (1u128 << bits) - 1;
        self.expr(
            ty,
            span,
            ExprKind::Const(ConstValue::Int(value as u128 & mask, ty)),
        )
    }

    /// An integer literal written `text`, which the source holds once.
    fn int(&mut self, ty: Ty, text: &str) -> Expr {
        let value = parse_int(text);
        let span = self.at(text);
        self.int_at(ty, value, span)
    }

    fn float_at(&mut self, ty: Ty, value: f64, span: Span) -> Expr {
        let bits = match self.tcx.kind(ty) {
            TyKind::Float(enrang_hir::FloatTy::F32) => u64::from((value as f32).to_bits()),
            _ => value.to_bits(),
        };
        self.expr(ty, span, ExprKind::Const(ConstValue::Float(bits, ty)))
    }

    fn boolean(&mut self, value: bool, span: Span) -> Expr {
        let ty = self.t().bool;
        self.expr(ty, span, ExprKind::Const(ConstValue::Bool(value)))
    }

    fn string(&mut self, text: &str, span: Span) -> Expr {
        let ty = self.tcx.mk_ref(self.t().str);
        let id = self.tcx.intern_str(text);
        self.expr(ty, span, ExprKind::Const(ConstValue::Str(id)))
    }

    /// `a op b` over the text `whole`; a comparison is a `bool`, anything else has
    /// the left operand's type.
    fn bin(&mut self, op: BinOp, a: Expr, b: Expr, whole: Span) -> Expr {
        let ty = match op {
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => self.t().bool,
            _ => a.ty,
        };
        self.expr(ty, whole, ExprKind::Binary(op, Box::new(a), Box::new(b)))
    }

    fn cast(&mut self, a: Expr, kind: CastKind, ty: Ty, whole: Span) -> Expr {
        self.expr(ty, whole, ExprKind::Cast(Box::new(a), kind))
    }

    fn size_form(&mut self, form: FormKind, whole: Span) -> Expr {
        let ty = self.t().usize;
        self.expr(
            ty,
            whole,
            ExprKind::Call {
                callee: Callee::Form(form),
                receiver: None,
                args: Vec::new(),
            },
        )
    }

    fn path(&self, name: &str) -> ItemPath {
        ItemPath::item(self.tcx.module(self.module).path, intern(name))
    }

    /// The span of a declared name: `name` after `const ` or `let `, as the source
    /// holds it once.
    fn decl(&self, keyword: &str, name: &str) -> Span {
        let found: Vec<usize> = self
            .src
            .match_indices(&format!("{keyword} {name}"))
            .map(|(i, _)| i + keyword.len() + 1)
            .filter(|&i| {
                !self.src[i + name.len()..].starts_with(|c: char| c.is_alphanumeric() || c == '_')
            })
            .collect();
        assert_eq!(found.len(), 1, "`{keyword} {name}` is not declared once");
        self.span_at(found[0], name.len())
    }

    /// A top-level `const` named `name` whose typed initialiser is `init`.
    fn konst(&mut self, name: &str, init: Expr) -> DefId {
        let span = self.decl("const", name);
        self.konst_at(name, span, init)
    }

    fn konst_at(&mut self, name: &str, span: Span, init: Expr) -> DefId {
        let mut data = DefData::new(self.path(name), DefKind::Const, self.module, span);
        data.name_span = span;
        let def = self.tcx.define_def(data);
        self.tcx.set_item_ty(def, init.ty);
        let body = const_body(BodyOwner::Const(def), init);
        self.bodies.insert(def, Arc::new(body));
        def
    }

    /// A constant with no body, as one whose declaration failed.
    fn bodiless(&mut self, name: &str, ty: Ty) -> DefId {
        let span = self.decl("const", name);
        let mut data = DefData::new(self.path(name), DefKind::Const, self.module, span);
        data.name_span = span;
        let def = self.tcx.define_def(data);
        self.tcx.set_item_ty(def, ty);
        def
    }

    fn unsafe_let(&mut self, name: &str, ty: Ty) -> DefId {
        let span = self.decl("let", name);
        let mut data = DefData::new(self.path(name), DefKind::Static, self.module, span);
        data.name_span = span;
        let def = self.tcx.define_def(data);
        self.tcx.set_item_ty(def, ty);
        def
    }

    /// A read of the constant or `unsafe let` `def`, at `span`.
    fn read_at(&mut self, def: DefId, span: Span) -> Expr {
        let ty = self.tcx.item_ty(def).expect("a typed item");
        self.expr(ty, span, ExprKind::Static(def))
    }

    fn value(&mut self, def: DefId) -> Result<ConstTree, ConstError> {
        self.state.value_of(&self.tcx, &mut self.bodies, def)
    }

    /// `def`'s value with nothing memoised yet.
    fn fresh(&mut self, def: DefId) -> Result<ConstTree, ConstError> {
        ConstState::new().value_of(&self.tcx, &mut self.bodies, def)
    }

    /// The value of `e`, an expression of a body with no locals.
    fn eval(&mut self, e: &Expr) -> Result<ConstTree, ConstError> {
        let body = Body::empty(BodyOwner::Statements(self.module), e.ty, e.span);
        self.state.eval(&self.tcx, &mut self.bodies, &body, e)
    }

    /// A final class with `fields` (name, type, has a default, `x?:`).
    fn class(&mut self, name: &str, fields: &[(&str, Ty, bool, bool)]) -> (AdtId, Ty) {
        let adt = self.tcx.define_adt(AdtDecl {
            data: DefData::new(
                self.path(name),
                DefKind::TypeAlias,
                self.module,
                Span::DUMMY,
            ),
            name: intern(name),
            generics: self.tcx.empty_generics(),
            kind: AdtKind::Class(ClassDef::new(ClassModifier::Final)),
        });
        let defs: Vec<FieldDef> = fields
            .iter()
            .map(|&(field, ty, has_default, optional)| {
                let mut def = FieldDef::new(intern(field), ty, adt);
                def.has_default = has_default || optional;
                def.optional = optional;
                def
            })
            .collect();
        if let AdtKind::Class(class) = &mut self.tcx.adt_mut(adt).kind {
            class.fields = defs;
        }
        (adt, self.tcx.mk_adt(adt, &[]))
    }

    /// A payload-free enum with these cases and written values.
    fn enumeration(&mut self, name: &str, cases: &[(&str, Option<i128>)]) -> (AdtId, Ty) {
        let variants: Vec<VariantDef> = cases
            .iter()
            .map(|&(case, value)| {
                let mut v = VariantDef::new(intern(case));
                v.value = value.map(VariantValue::Int);
                v
            })
            .collect();
        let mut def = EnumDef::new(variants);
        if cases.iter().any(|(_, value)| value.is_some()) {
            def.values = EnumValues::Ints;
        }
        let adt = self.tcx.define_adt(AdtDecl {
            data: DefData::new(
                self.path(name),
                DefKind::TypeAlias,
                self.module,
                Span::DUMMY,
            ),
            name: intern(name),
            generics: self.tcx.empty_generics(),
            kind: AdtKind::Enum(def),
        });
        (adt, self.tcx.mk_adt(adt, &[]))
    }

    fn case(&mut self, adt: AdtId, variant: u32, fields: Vec<Expr>, span: Span) -> Expr {
        let ty = self.tcx.mk_adt(adt, &[]);
        let args = self.tcx.empty_list();
        self.expr(
            ty,
            span,
            ExprKind::VariantLit {
                adt,
                variant: VariantIdx(variant),
                args,
                fields,
                eval: Vec::new(),
            },
        )
    }

    /// Asserts a diagnostic's code, message, primary span and label, and that it
    /// has no secondary label.
    fn check(&self, diag: &Diagnostic, code: Code, message: &str, at: Span, label: &str) {
        assert_eq!(diag.code, code, "{diag:?}");
        assert_eq!(diag.message, message);
        assert_eq!(
            (self.text(diag.primary.span), diag.primary.span),
            (self.text(at), at)
        );
        assert_eq!(diag.primary.text, label);
        assert!(diag.secondary.is_empty(), "{diag:?}");
    }

    /// The value of an integer constant, by its type's signedness and width.
    fn int_of(&self, tree: &ConstTree) -> i128 {
        match tree {
            ConstTree::Scalar(value @ ConstValue::Int(_, ty)) => match self.tcx.kind(*ty) {
                TyKind::Int(_) => value.as_i128(&self.tcx).expect("an integer"),
                _ => panic!("not an integer: {tree:?}"),
            },
            _ => panic!("not an integer: {tree:?}"),
        }
    }

    fn render(&self, diag: &Diagnostic) -> String {
        render_text(
            std::slice::from_ref(diag),
            &self.map,
            &RenderOpts { color: false },
        )
    }
}

/// A `BodyOwner::Const` body holding `init` as its one expression statement, as
/// typing builds a constant's initialiser.
fn const_body(owner: BodyOwner, init: Expr) -> Body {
    let span = init.span;
    let mut body = Body::empty(owner, init.ty, span);
    body.expr_count = 0;
    body.root = Block {
        stmts: vec![Stmt {
            kind: StmtKind::Expr(init),
            span,
        }],
        span,
    };
    body
}

/// `parts` as lines, each ending in a line feed: a rendered golden.
fn lines(parts: &[&str]) -> String {
    parts.iter().map(|line| format!("{line}\n")).collect()
}

/// The diagnostic of a failure.
fn fail(result: Result<ConstTree, ConstError>) -> Diagnostic {
    match result {
        Err(ConstError::Fail(diag)) => *diag,
        other => panic!("expected a diagnostic, got {other:?}"),
    }
}

/// An integer written in decimal or hex, with `_` and a leading `-`.
fn parse_int(text: &str) -> i128 {
    let (negative, digits) = match text.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, text),
    };
    let digits = digits.replace('_', "");
    let value = match digits.strip_prefix("0x") {
        Some(hex) => i128::from_str_radix(hex, 16),
        None => digits.parse::<i128>(),
    }
    .expect("an integer literal");
    if negative { -value } else { value }
}

fn scalar_int(value: u128, ty: Ty) -> ConstTree {
    ConstTree::Scalar(ConstValue::Int(value, ty))
}

fn boolean(value: bool) -> ConstTree {
    ConstTree::Scalar(ConstValue::Bool(value))
}

/// `private const X = <a> <op> <b>;` with both operands of `int`, on `target`: the
/// world and the constant's value.
fn binary(
    target: &str,
    int: IntTy,
    a: &str,
    op: BinOp,
    b: &str,
) -> (World, Result<ConstTree, ConstError>) {
    let whole = format!("{a} {} {b}", op.as_str());
    let src = format!("private const X = {whole};\n");
    let mut w = World::new(target, &src);
    let ty = w.t().int(int);
    let at = "private const X = ".len();
    let x = w.int_at(ty, parse_int(a), w.span_at(at, a.len()));
    let y_at = at + a.len() + op.as_str().len() + 2;
    let y = w.int_at(ty, parse_int(b), w.span_at(y_at, b.len()));
    let e = w.bin(op, x, y, w.span_at(at, whole.len()));
    let def = w.konst("X", e);
    let result = w.value(def);
    (w, result)
}

impl World {
    fn logical(&mut self, op: LogOp, l: Expr, r: Expr, whole: Span) -> Expr {
        let ty = self.t().bool;
        self.expr(ty, whole, ExprKind::Logical(op, Box::new(l), Box::new(r)))
    }

    fn unary(&mut self, op: UnOp, a: Expr, whole: Span) -> Expr {
        let ty = a.ty;
        self.expr(ty, whole, ExprKind::Unary(op, Box::new(a)))
    }

    /// A definition of `kind` named `name` with no span, as a function.
    fn def_of(&mut self, name: &str, kind: DefKind) -> DefId {
        let data = DefData::new(self.path(name), kind, self.module, Span::DUMMY);
        self.tcx.define_def(data)
    }

    fn call(&mut self, ty: Ty, callee: Callee, args: Vec<Expr>, whole: Span) -> Expr {
        let kind = ExprKind::Call {
            callee,
            receiver: None,
            args,
        };
        self.expr(ty, whole, kind)
    }

    fn fn_callee(&self, def: DefId) -> Callee {
        let args = self.tcx.empty_list();
        Callee::Fn(FnRef { def, args })
    }

    /// The bracket literal `text` of `items`, of type `elem[items.len()]`.
    fn fixed_lit(&mut self, elem: Ty, text: &str, items: &[&str]) -> Expr {
        let items = self.ints_in(elem, text, items);
        let ty = self.tcx.mk_fixed(elem, items.len() as u64);
        self.expr(ty, self.at(text), ExprKind::ArrayLit(items))
    }

    /// `new C { ... }` at `text`.
    fn new_named(
        &mut self,
        adt: AdtId,
        fields: Vec<(FieldIdx, Expr)>,
        default_from: Vec<FieldIdx>,
        whole: Span,
    ) -> Expr {
        let ty = self.tcx.mk_adt(adt, &[]);
        let args = self.tcx.empty_list();
        let kind = ExprKind::NewNamed {
            adt,
            args,
            fields,
            default_from,
        };
        self.expr(ty, whole, kind)
    }

    /// `B`'s value is `A`'s, at the text `read`, as `private const B = A;`.
    fn alias(&mut self, name: &str, of: DefId, read: Span) -> DefId {
        let e = self.read_at(of, read);
        self.konst(name, e)
    }

    /// Gives the bodiless constant `def` the initialiser `init`.
    fn define(&mut self, def: DefId, init: Expr) {
        let body = const_body(BodyOwner::Const(def), init);
        self.bodies.insert(def, Arc::new(body));
    }
}

fn float(bits: f64, ty: Ty) -> ConstTree {
    ConstTree::Scalar(ConstValue::Float(bits.to_bits(), ty))
}

fn float32(bits: f32, ty: Ty) -> ConstTree {
    ConstTree::Scalar(ConstValue::Float(u64::from(bits.to_bits()), ty))
}

// ---------------------------------------------------------------------------------
// Registration: every case on both targets.

/// A case: its area, its name, its body (given the target).
type Case = (&'static str, &'static str, fn(&'static str));

const CASES: &[Case] = &[
    ("literals", "every literal is its own value", literals),
    (
        "arithmetic",
        "u8 shifts are logical and drop the bits shifted out",
        u8_shifts,
    ),
    (
        "arithmetic",
        "a shift count has its own integer type",
        shift_count_type,
    ),
    ("arithmetic", "unary operators", unary_operators),
    (
        "arithmetic",
        "floats compute in their own precision",
        float_arithmetic,
    ),
    ("arithmetic", "a 1024-term sum evaluates", long_sum),
    ("overflow", "the largest values still fit", largest_values),
    (
        "overflow",
        "division and remainder by zero",
        division_by_zero,
    ),
    (
        "overflow",
        "negating the minimum overflows, through a constant",
        negate_minimum,
    ),
    (
        "overflow",
        "a read constant takes part: `A + 1` at u8",
        read_overflow,
    ),
    (
        "shifts",
        "a count not below the width fails",
        shift_out_of_range,
    ),
    ("shifts", "isize's width is the target's", isize_shift),
    (
        "comparisons",
        "integers of two types compare their true values",
        mixed_ints,
    ),
    (
        "comparisons",
        "floats compare by IEEE, a NaN with nothing",
        float_comparisons,
    ),
    (
        "comparisons",
        "strings, bools, nullables and cases",
        other_comparisons,
    ),
    (
        "comparisons",
        "a class compares by calling `equals`: EN1032",
        class_comparison,
    ),
    (
        "logic",
        "`&&` and `||` skip their right operand as at run time",
        short_circuit,
    ),
    (
        "logic",
        "a skipped operand must still be constant",
        skipped_operand,
    ),
    ("casts", "int to int is checked", int_to_int),
    ("casts", "to usize at the target's width", to_usize),
    ("casts", "int to float rounds to nearest-even", int_to_float),
    (
        "casts",
        "float to float rounds, f32 to f64 is exact",
        float_to_float,
    ),
    (
        "casts",
        "float to int truncates and is checked",
        float_to_int,
    ),
    (
        "casts",
        "a payload-free enum's discriminant, checked",
        enum_to_int,
    ),
    (
        "casts",
        "bool to int and usize to a raw pointer",
        bool_and_raw,
    ),
    (
        "casts",
        "a cast under a wrap keeps its own type",
        wrapped_cast,
    ),
    ("constants", "read on demand and memoised", on_demand),
    (
        "constants",
        "a value stored in Tcx is read from there",
        stored_value,
    ),
    (
        "constants",
        "a constant with no initialiser was already reported",
        no_initialiser,
    ),
    (
        "constants",
        "a failed constant fails its readers with its diagnostic",
        propagation,
    ),
    (
        "constants",
        "a chain of 20000 constants needs no deep stack",
        long_chain,
    ),
    (
        "cycles",
        "`A = B; B = A` is EN0412 at A, entered from either",
        two_cycle,
    ),
    ("cycles", "a constant that reads itself", self_cycle),
    (
        "cycles",
        "a longer cycle starts at its first constant in source order",
        long_cycle,
    ),
    (
        "cycles",
        "a cycle through an operand `&&` skips is still a cycle",
        skipped_cycle,
    ),
    (
        "layout",
        "sizeOf and alignOf of primitives follow P",
        primitive_sizes,
    ),
    (
        "layout",
        "SPEC 11's Player, object and tuple",
        aggregate_sizes,
    ),
    (
        "layout",
        "a borrowing class is EN0412 with SPEC 4.9's note",
        borrowing_class,
    ),
    (
        "layout",
        "a borrowing tuple and a `&string` are not constant",
        borrowing_others,
    ),
    (
        "layout",
        "a type larger than isize.MAX has no size",
        too_large,
    ),
    (
        "layout",
        "a view by value or an error type",
        unsized_or_error,
    ),
    (
        "aggregates",
        "arrays, repeats, tuples and objects of constants",
        literals_of_constants,
    ),
    (
        "aggregates",
        "a class literal fills left-out fields with defaults",
        class_defaults,
    ),
    (
        "aggregates",
        "a field left to its initialiser is not constant",
        initialised_field,
    ),
    ("aggregates", "case literals and wraps", case_literals),
    (
        "views",
        "`&` of a bracket literal is a constant literal view",
        literal_views,
    ),
    (
        "views",
        "`&` of anything else is not constant",
        other_borrows,
    ),
    (
        "views",
        "a growable array literal allocates",
        growable_array,
    ),
    (
        "calls",
        "a call is EN1032 with SPEC 16's head, note and help",
        function_call,
    ),
    (
        "calls",
        "constructors, optional calls and forms are calls too",
        other_calls,
    ),
    (
        "spreads",
        "`...` is EN0412 at the token with the note",
        spreads,
    ),
    (
        "not-constant",
        "each part that is not constant is named",
        non_constant_parts,
    ),
    (
        "not-constant",
        "an expression typing rejected says nothing more",
        rejected,
    ),
    (
        "not-constant",
        "a long or multi-line part is `this expression`",
        long_parts,
    ),
    (
        "budget",
        "a constant holds at most MAX_VALUES values",
        budget,
    ),
    (
        "overflow",
        "`usize.MAX * usize.MAX` overflows on every target",
        usize_max_squared,
    ),
    (
        "comparisons",
        "`f32` compares by IEEE in its own precision",
        f32_comparisons,
    ),
    (
        "comparisons",
        "an enum with fields compares by calling `equals`: EN1032",
        payload_enum_comparison,
    ),
    (
        "conversions",
        "an `f32` prints in its own precision in a conversion label",
        f32_conversion_label,
    ),
    (
        "not-constant",
        "a part of 40 characters is quoted, one of 41 is not",
        quote_limit,
    ),
    (
        "budget",
        "a left-out fixed array's own node counts too",
        default_budget,
    ),
];

/// `a op b` at `int` and its value on both targets.
const ARITHMETIC: &[(IntTy, &str, BinOp, &str, i128)] = &[
    (IntTy::I64, "2", BinOp::Add, "3", 5),
    (IntTy::I64, "2", BinOp::Sub, "5", -3),
    (IntTy::I64, "6", BinOp::Mul, "-7", -42),
    (IntTy::I64, "-7", BinOp::Div, "2", -3),
    (IntTy::I64, "7", BinOp::Div, "-2", -3),
    (IntTy::I64, "-7", BinOp::Rem, "2", -1),
    (IntTy::I64, "7", BinOp::Rem, "-2", 1),
    (IntTy::I64, "12", BinOp::BitAnd, "10", 8),
    (IntTy::I64, "12", BinOp::BitOr, "10", 14),
    (IntTy::I64, "12", BinOp::BitXor, "10", 6),
    (IntTy::I64, "-1", BinOp::BitAnd, "255", 255),
    (IntTy::I64, "-16", BinOp::Shr, "2", -4),
    (IntTy::I64, "3", BinOp::Shl, "4", 48),
    (IntTy::I64, "1", BinOp::Shl, "63", i64::MIN as i128),
    (
        IntTy::I64,
        "9223372036854775807",
        BinOp::Add,
        "-9223372036854775807",
        0,
    ),
    (IntTy::I8, "-128", BinOp::Rem, "3", -2),
    (
        IntTy::U64,
        "18446744073709551615",
        BinOp::Div,
        "2",
        9223372036854775807,
    ),
];

/// `a op b` at `int`, which overflows on both targets.
const OVERFLOWS: &[(IntTy, &str, BinOp, &str)] = &[
    (IntTy::Usize, "0", BinOp::Sub, "1"),
    (IntTy::I64, "9223372036854775807", BinOp::Add, "1"),
    (IntTy::I64, "-9223372036854775808", BinOp::Sub, "1"),
    (IntTy::I64, "4294967296", BinOp::Mul, "4294967296"),
    (IntTy::U64, "18446744073709551615", BinOp::Add, "1"),
    (IntTy::I32, "65536", BinOp::Mul, "65536"),
    (IntTy::U8, "200", BinOp::Add, "56"),
    (IntTy::I8, "-100", BinOp::Sub, "29"),
    (IntTy::I64, "-9223372036854775808", BinOp::Div, "-1"),
    (IntTy::I64, "-9223372036854775808", BinOp::Rem, "-1"),
    (IntTy::I8, "-128", BinOp::Div, "-1"),
    (IntTy::I8, "-128", BinOp::Rem, "-1"),
    // Past `i128` itself, which a product of two `u64` reaches.
    (
        IntTy::U64,
        "18446744073709551615",
        BinOp::Mul,
        "18446744073709551615",
    ),
    (
        IntTy::U64,
        "0xC000000000000000",
        BinOp::Mul,
        "0xC000000000000000",
    ),
];

/// `a op b` at a pointer-sized `int`: it overflows on `i386` and is the value on
/// `x86_64` (SPEC 11).
const POINTER_SIZED: &[(IntTy, &str, BinOp, &str, i128)] = &[
    (IntTy::Isize, "2147483647", BinOp::Add, "1", 2147483648),
    (IntTy::Usize, "4294967295", BinOp::Add, "1", 4294967296),
    (IntTy::Isize, "-2147483648", BinOp::Sub, "1", -2147483649),
    (IntTy::Usize, "65536", BinOp::Mul, "65536", 4294967296),
];

pub fn register(h: &mut Harness) {
    for target in TARGETS {
        for &(area, name, body) in CASES {
            h.case(format!("consteval/{area}/{target}/{name}"), move || {
                body(target)
            });
        }
        for &(int, a, op, b, want) in ARITHMETIC {
            let name = format!(
                "consteval/arithmetic/{target}/{} `{a} {} {b}` is {want}",
                int.name(),
                op.as_str()
            );
            h.case(name, move || arithmetic_row(target, int, a, op, b, want));
        }
        for &(int, a, op, b) in OVERFLOWS {
            let name = format!(
                "consteval/overflow/{target}/{} `{a} {} {b}` overflows",
                int.name(),
                op.as_str()
            );
            h.case(name, move || overflow_row(target, int, a, op, b));
        }
        for &(int, a, op, b, wide) in POINTER_SIZED {
            let name = format!(
                "consteval/overflow/{target}/{} `{a} {} {b}` follows P",
                int.name(),
                op.as_str()
            );
            h.case(name, move || pointer_row(target, int, a, op, b, wide));
        }
    }
    from_source::register(h);
}

// ---------------------------------------------------------------------------------
// Literals and arithmetic.

fn literals(target: &'static str) {
    let src = concat!(
        "private const A: i64 = 42;\n",
        "private const B: bool = true;\n",
        "private const C: f64 = 2.5;\n",
        "public const NAME: &string = \"Ada\";\n",
        "private const E: i64 | null = null;\n",
        "private const F: i64 | null = 7;\n",
    );
    let mut w = World::new(target, src);
    let t = w.t();
    let a = w.int(t.i64, "42");
    let a = w.konst("A", a);
    let b = w.boolean(true, w.at("true"));
    let b = w.konst("B", b);
    let c = w.float_at(t.f64, 2.5, w.at("2.5"));
    let c = w.konst("C", c);
    let mut name = w.string("Ada", w.at("\"Ada\""));
    name.adjust.push(Adjust::LiteralDescriptor);
    let name = w.konst("NAME", name);
    let nullable = w.tcx.mk_nullable(t.i64);
    let e = w.expr(nullable, w.at_in("= null;", "null"), ExprKind::NullLit);
    let e = w.konst("E", e);
    let mut f = w.int(t.i64, "7");
    f.adjust.push(Adjust::WrapNull);
    let f = w.konst("F", f);
    assert_eq!(w.value(a), Ok(scalar_int(42, t.i64)));
    assert_eq!(w.value(b), Ok(boolean(true)));
    assert_eq!(w.value(c), Ok(float(2.5, t.f64)));
    let ada = w.tcx.intern_str("Ada");
    assert_eq!(w.value(name), Ok(ConstTree::Scalar(ConstValue::Str(ada))));
    assert_eq!(w.value(e), Ok(ConstTree::Null));
    let seven = Box::new(scalar_int(7, t.i64));
    assert_eq!(w.value(f), Ok(ConstTree::Present(seven)));
}

fn arithmetic_row(target: &'static str, int: IntTy, a: &str, op: BinOp, b: &str, want: i128) {
    let (w, value) = binary(target, int, a, op, b);
    let value = value.expect("a value");
    assert_eq!(w.int_of(&value), want);
    assert!(matches!(value, ConstTree::Scalar(ConstValue::Int(_, ty)) if ty == w.t().int(int)));
}

fn u8_shifts(target: &'static str) {
    for (a, op, b, want) in [
        ("240", BinOp::Shr, "4", 15),
        ("128", BinOp::Shl, "1", 0),
        ("255", BinOp::Shl, "4", 240),
    ] {
        let (w, value) = binary(target, IntTy::U8, a, op, b);
        assert_eq!(w.int_of(&value.expect("a value")), want, "{a} {op:?} {b}");
    }
}

fn shift_count_type(target: &'static str) {
    let mut w = World::new(target, "private const X = 1 << 3;\n");
    let t = w.t();
    let one = w.int(t.i64, "1");
    let three = w.int(t.u8, "3");
    let e = w.bin(BinOp::Shl, one, three, w.at("1 << 3"));
    let x = w.konst("X", e);
    assert_eq!(w.value(x), Ok(scalar_int(8, t.i64)));
}

fn unary_operators(target: &'static str) {
    let src = concat!(
        "private const A: i8 = -5;\n",
        "private const B = -A;\n",
        "private const C = ~A;\n",
        "private const D: u8 = 0;\n",
        "private const E = ~D;\n",
        "private const F = !true;\n",
        "private const G = -2.5;\n",
        "private const H: f32 = -0.75;\n",
    );
    let mut w = World::new(target, src);
    let t = w.t();
    let a = w.int(t.i8, "-5");
    let a = w.konst("A", a);
    let read = w.read_at(a, w.at_in("= -A", "A"));
    let neg = w.unary(UnOp::Neg, read, w.at("-A"));
    let b = w.konst("B", neg);
    let read = w.read_at(a, w.at_in("~A", "A"));
    let not = w.unary(UnOp::BitNot, read, w.at("~A"));
    let c = w.konst("C", not);
    let zero = w.int_at(t.u8, 0, w.at_in("D: u8 = 0", "0"));
    let d = w.konst("D", zero);
    let read = w.read_at(d, w.at_in("~D", "D"));
    let not = w.unary(UnOp::BitNot, read, w.at("~D"));
    let e = w.konst("E", not);
    let truth = w.boolean(true, w.at_in("!true", "true"));
    let not = w.unary(UnOp::Not, truth, w.at("!true"));
    let f = w.konst("F", not);
    let half = w.float_at(t.f64, 2.5, w.at_in("-2.5", "2.5"));
    let neg = w.unary(UnOp::Neg, half, w.at("-2.5"));
    let g = w.konst("G", neg);
    let b = w.value(b).expect("B");
    assert_eq!(w.int_of(&b), 5);
    let c = w.value(c).expect("C");
    assert_eq!(w.int_of(&c), 4);
    assert_eq!(w.value(e), Ok(scalar_int(255, t.u8)));
    assert_eq!(w.value(f), Ok(boolean(false)));
    assert_eq!(w.value(g), Ok(float(-2.5, t.f64)));
    let quarter = w.float_at(t.f32, 0.75, w.at_in("-0.75", "0.75"));
    let neg = w.unary(UnOp::Neg, quarter, w.at("-0.75"));
    let h = w.konst("H", neg);
    assert_eq!(w.value(h), Ok(float32(-0.75, t.f32)));
}

fn float_arithmetic(target: &'static str) {
    let src = concat!(
        "private const A = 0.1 + 0.2;\n",
        "private const B: f32 = 0.1 + 0.2;\n",
        "private const C = 7.5 % 2.0;\n",
        "private const D = 1.0 / 0.0;\n",
    );
    let mut w = World::new(target, src);
    let t = w.t();
    let sum = |w: &mut World, ty: Ty, context: &str| {
        let x = w.float_at(ty, 0.1, w.at_in(context, "0.1"));
        let y = w.float_at(ty, 0.2, w.at_in(context, "0.2"));
        w.bin(BinOp::Add, x, y, w.at_in(context, "0.1 + 0.2"))
    };
    let a = sum(&mut w, t.f64, "A = 0.1 + 0.2");
    let a = w.konst("A", a);
    let b = sum(&mut w, t.f32, "B: f32 = 0.1 + 0.2");
    let b = w.konst("B", b);
    let x = w.float_at(t.f64, 7.5, w.at("7.5"));
    let y = w.float_at(t.f64, 2.0, w.at("2.0"));
    let rem = w.bin(BinOp::Rem, x, y, w.at("7.5 % 2.0"));
    let c = w.konst("C", rem);
    let x = w.float_at(t.f64, 1.0, w.at("1.0"));
    let y = w.float_at(t.f64, 0.0, w.at("0.0"));
    let div = w.bin(BinOp::Div, x, y, w.at("1.0 / 0.0"));
    let d = w.konst("D", div);
    assert_eq!(w.value(a), Ok(float(0.1 + 0.2, t.f64)));
    assert_eq!(w.value(b), Ok(float32(0.1f32 + 0.2f32, t.f32)));
    assert_eq!(w.value(c), Ok(float(1.5, t.f64)));
    // IEEE: a float never fails (SPEC 4.6).
    assert_eq!(w.value(d), Ok(float(f64::INFINITY, t.f64)));
}

/// A chain as long as the parser's link limit (1024) evaluates within the stack.
fn long_sum(target: &'static str) {
    let terms = 1024;
    let text = vec!["1"; terms].join(" + ");
    let mut w = World::new(target, &format!("private const X = {text};\n"));
    let t = w.t();
    let at = "private const X = ".len();
    let mut e = w.int_at(t.i64, 1, w.span_at(at, 1));
    for i in 1..terms {
        let one = w.int_at(t.i64, 1, w.span_at(at + 4 * i, 1));
        e = w.bin(BinOp::Add, e, one, w.span_at(at, 4 * i + 1));
    }
    let x = w.konst("X", e);
    assert_eq!(w.value(x), Ok(scalar_int(terms as u128, t.i64)));
}

// ---------------------------------------------------------------------------------
// Overflow, division, shifts.

fn overflow_row(target: &'static str, int: IntTy, a: &str, op: BinOp, b: &str) {
    let (w, value) = binary(target, int, a, op, b);
    let shown = w.tcx.ty_string(w.t().int(int));
    let whole = format!("{a} {} {b}", op.as_str());
    // A part longer than 40 characters is `this expression`.
    let quoted = if whole.chars().count() <= 40 {
        format!("`{whole}`")
    } else {
        "this expression".to_owned()
    };
    // The label prints the values, and SPEC 9.1 writes the panic of `MIN % -1` as
    // `integer overflow: MIN / -1`.
    let shown_op = match op {
        BinOp::Rem => "/",
        _ => op.as_str(),
    };
    let panic = format!(
        "integer overflow: {} {shown_op} {}",
        parse_int(a),
        parse_int(b)
    );
    let diag = fail(value);
    w.check(
        &diag,
        Code::EN0412,
        &format!("constant evaluation failed: {quoted} overflows `{shown}`"),
        w.at(&whole),
        &panic,
    );
    assert!(diag.entries.is_empty() && diag.helps.is_empty());
}

fn usize_max_squared(target: &'static str) {
    let max = if target.starts_with("i386") {
        "4294967295"
    } else {
        "18446744073709551615"
    };
    overflow_row(target, IntTy::Usize, max, BinOp::Mul, max);
}

fn f32_comparisons(target: &'static str) {
    let mut w = World::new(target, "private const X = 0;\n");
    let t = w.t();
    let whole = w.at("0");
    for (a, b, op, want) in [
        (-0.0, 0.0, BinOp::Eq, true),
        (f64::NAN, f64::NAN, BinOp::Eq, false),
        (f64::NAN, f64::NAN, BinOp::Ne, true),
        (1.5, 1.5, BinOp::Eq, true),
    ] {
        let x = w.float_at(t.f32, a, whole);
        let y = w.float_at(t.f32, b, whole);
        let e = w.bin(op, x, y, whole);
        assert_eq!(w.eval(&e), Ok(boolean(want)), "{a} {op:?} {b}");
    }
}

fn payload_enum_comparison(target: &'static str) {
    let mut w = World::new(target, "private const E = Shape.Empty == Shape.Empty;\n");
    let t = w.t();
    let (shape, _) = w.enumeration("Shape", &[("Circle", None), ("Empty", None)]);
    if let AdtKind::Enum(e) = &mut w.tcx.adt_mut(shape).kind {
        e.variants[0]
            .fields
            .push(FieldDef::new(intern("radius"), t.f64, shape));
    }
    let a = w.case(
        shape,
        1,
        Vec::new(),
        w.at_in("E = Shape.Empty", "Shape.Empty"),
    );
    let b = w.case(
        shape,
        1,
        Vec::new(),
        w.at_in("== Shape.Empty", "Shape.Empty"),
    );
    let whole = w.at("Shape.Empty == Shape.Empty");
    let e = w.bin(BinOp::Eq, a, b, whole);
    let diag = fail(w.eval(&e));
    w.check(
        &diag,
        Code::EN1032,
        "compile-time function calls are not supported yet",
        whole,
        "this compares by calling `equals`",
    );
}

fn f32_conversion_label(target: &'static str) {
    let mut w = World::new(target, "private const X = 3.4e38 as i8;\n");
    let t = w.t();
    let x = w.float_at(t.f32, 3.4e38, w.at("3.4e38"));
    let e = w.cast(x, CastKind::FloatToInt, t.i8, w.at("3.4e38 as i8"));
    let diag = fail(w.eval(&e));
    assert_eq!(diag.primary.text, "conversion out of range: 3.4e38 as i8");
}

fn quote_limit(target: &'static str) {
    let forty = "abcdefghij.abcdefghij.abcdefghij.abcdefg";
    let src = format!("private const A = {forty};\nprivate const B = {forty}h;\n");
    let mut w = World::new(target, &src);
    let t = w.t();
    assert_eq!(forty.len(), 40);
    for (text, quoted) in [(forty.to_owned(), true), (format!("{forty}h"), false)] {
        let span = w.at(&format!("{text};"));
        let span = Span {
            lo: span.lo,
            hi: BytePos(span.hi.0 - 1),
        };
        let base = w.boolean(true, span);
        let field = w.expr(t.i64, span, ExprKind::Field(Box::new(base), FieldIdx(0)));
        let message = fail(w.eval(&field)).message;
        let want = if quoted {
            format!("constant evaluation failed: `{text}` is not constant")
        } else {
            "constant evaluation failed: this expression is not constant".to_owned()
        };
        assert_eq!(message, want);
    }
}

fn default_budget(target: &'static str) {
    let src = "private const A = new Fits {};\nprivate const B = new Over {};\n";
    let mut w = World::new(target, src);
    let t = w.t();
    // The literal's own node, the array's and its elements: `n + 2` values.
    let fits = w.tcx.mk_fixed(t.u8, MAX_VALUES - 2);
    let over = w.tcx.mk_fixed(t.u8, MAX_VALUES - 1);
    let (fits, _) = w.class("Fits", &[("data", fits, false, false)]);
    let (over, _) = w.class("Over", &[("data", over, false, false)]);
    let lit = w.new_named(fits, Vec::new(), vec![FieldIdx(0)], w.at("new Fits {}"));
    let a = w.konst("A", lit);
    assert!(w.value(a).is_ok());
    let whole = w.at("new Over {}");
    let lit = w.new_named(over, Vec::new(), vec![FieldIdx(0)], whole);
    let b = w.konst("B", lit);
    let diag = fail(w.value(b));
    w.check(
        &diag,
        Code::EN0412,
        "constant evaluation failed: `new Over {}` is too large to evaluate",
        whole,
        "a constant holds at most 1048576 values",
    );
}

fn pointer_row(target: &'static str, int: IntTy, a: &str, op: BinOp, b: &str, wide: i128) {
    let (w, value) = binary(target, int, a, op, b);
    if w.p() == 4 {
        let shown = w.tcx.ty_string(w.t().int(int));
        let whole = format!("{a} {} {b}", op.as_str());
        let diag = fail(value);
        w.check(
            &diag,
            Code::EN0412,
            &format!("constant evaluation failed: `{whole}` overflows `{shown}`"),
            w.at(&whole),
            &format!("integer overflow: {whole}"),
        );
    } else {
        assert_eq!(w.int_of(&value.expect("a value")), wide);
    }
}

fn largest_values(target: &'static str) {
    for (int, a, op, b, want) in [
        (
            IntTy::U64,
            "18446744073709551614",
            BinOp::Add,
            "1",
            u64::MAX as i128,
        ),
        (
            IntTy::I64,
            "-9223372036854775807",
            BinOp::Sub,
            "1",
            i64::MIN as i128,
        ),
        (IntTy::U8, "255", BinOp::Sub, "255", 0),
        (IntTy::I8, "-127", BinOp::Div, "-1", 127),
    ] {
        let (w, value) = binary(target, int, a, op, b);
        assert_eq!(w.int_of(&value.expect("a value")), want, "{a} {op:?} {b}");
    }
}

fn division_by_zero(target: &'static str) {
    for op in [BinOp::Div, BinOp::Rem] {
        let whole = format!("10 {} 0", op.as_str());
        let (w, value) = binary(target, IntTy::I64, "10", op, "0");
        let diag = fail(value);
        w.check(
            &diag,
            Code::EN0412,
            &format!("constant evaluation failed: `{whole}` divides by zero"),
            w.at(&whole),
            "division by zero",
        );
    }
}

fn negate_minimum(target: &'static str) {
    let src = "private const A: i8 = -128;\nprivate const B = -A;\n";
    let mut w = World::new(target, src);
    let t = w.t();
    let a = w.int(t.i8, "-128");
    let a = w.konst("A", a);
    let read = w.read_at(a, w.at_in("-A", "A"));
    let neg = w.unary(UnOp::Neg, read, w.at("-A"));
    let b = w.konst("B", neg);
    let diag = fail(w.value(b));
    w.check(
        &diag,
        Code::EN0412,
        "constant evaluation failed: `-A` overflows `i8`",
        w.at("-A"),
        "integer overflow: neg -128",
    );
}

fn read_overflow(target: &'static str) {
    let src = "private const A: u8 = 255;\nprivate const B = A + 1;\n";
    let mut w = World::new(target, src);
    let t = w.t();
    let a = w.int(t.u8, "255");
    let a = w.konst("A", a);
    let read = w.read_at(a, w.at_in("A + 1", "A"));
    let one = w.int(t.u8, "1");
    let sum = w.bin(BinOp::Add, read, one, w.at("A + 1"));
    let b = w.konst("B", sum);
    let diag = fail(w.value(b));
    w.check(
        &diag,
        Code::EN0412,
        "constant evaluation failed: `A + 1` overflows `u8`",
        w.at("A + 1"),
        "integer overflow: 255 + 1",
    );
    let golden = lines(&[
        "error[EN0412]: constant evaluation failed: `A + 1` overflows `u8`",
        " --> src/main.en:2:19",
        "  |",
        "2 | private const B = A + 1;",
        "  |                   ^^^^^ integer overflow: 255 + 1",
        "  |",
        "  = explain: run `enrang explain EN0412`",
        "",
        "error: aborting due to 1 previous error",
    ]);
    assert_eq!(w.render(&diag), golden);
}

fn shift_out_of_range(target: &'static str) {
    for (int, a, op, b, bits) in [
        (IntTy::I64, "1", BinOp::Shl, "64", 64),
        (IntTy::U8, "1", BinOp::Shr, "8", 8),
        (IntTy::I32, "1", BinOp::Shl, "-1", 32),
    ] {
        let whole = format!("{a} {} {b}", op.as_str());
        let (w, value) = binary(target, int, a, op, b);
        let diag = fail(value);
        w.check(
            &diag,
            Code::EN0412,
            &format!("constant evaluation failed: `{whole}` shifts out of range"),
            w.at(&whole),
            &format!("shift count {b} out of range for {bits} bits"),
        );
    }
}

fn isize_shift(target: &'static str) {
    let (w, value) = binary(target, IntTy::Isize, "1", BinOp::Shl, "32");
    if w.p() == 4 {
        let label = "shift count 32 out of range for 32 bits";
        assert_eq!(fail(value).primary.text, label);
    } else {
        assert_eq!(w.int_of(&value.expect("a value")), 1 << 32);
    }
}

// ---------------------------------------------------------------------------------
// Comparisons and logic.

fn mixed_ints(target: &'static str) {
    let src = concat!(
        "private const A = -1 < 18446744073709551615;\n",
        "private const B = -1 == 4294967295;\n",
        "private const C = 300 >= 255;\n",
        "private const D = 255 == 255;\n",
    );
    let mut w = World::new(target, src);
    let t = w.t();
    let x = w.int_at(t.i64, -1, w.at_in("A = -1", "-1"));
    let y = w.int(t.u64, "18446744073709551615");
    let lt = w.bin(BinOp::Lt, x, y, w.at("-1 < 18446744073709551615"));
    let a = w.konst("A", lt);
    let x = w.int_at(t.i32, -1, w.at_in("B = -1", "-1"));
    let y = w.int(t.u32, "4294967295");
    let eq = w.bin(BinOp::Eq, x, y, w.at("-1 == 4294967295"));
    let b = w.konst("B", eq);
    let x = w.int(t.i64, "300");
    let y = w.int_at(t.u8, 255, w.at_in("300 >= 255", "255"));
    let ge = w.bin(BinOp::Ge, x, y, w.at("300 >= 255"));
    let c = w.konst("C", ge);
    assert_eq!(w.value(a), Ok(boolean(true)));
    assert_eq!(w.value(b), Ok(boolean(false)));
    assert_eq!(w.value(c), Ok(boolean(true)));
    // Equal values of two types, under every comparison.
    let whole = w.at("255 == 255");
    for (op, want) in [
        (BinOp::Eq, true),
        (BinOp::Ne, false),
        (BinOp::Lt, false),
        (BinOp::Le, true),
        (BinOp::Gt, false),
        (BinOp::Ge, true),
    ] {
        let x = w.int_at(t.u8, 255, w.at_in("255 == 255", "255"));
        let y = w.int_at(t.i64, 255, w.at_last_in("255 == 255", "255"));
        let e = w.bin(op, x, y, whole);
        assert_eq!(w.eval(&e), Ok(boolean(want)), "255 {op:?} 255");
    }
}

fn float_comparisons(target: &'static str) {
    let src = "private const N = 0.0 / 0.0;\nprivate const Z = 0.5 - 0.5;\n";
    let mut w = World::new(target, src);
    let t = w.t();
    let x = w.float_at(t.f64, 0.0, w.at_in("0.0 / 0.0", "0.0"));
    let y = w.float_at(t.f64, 0.0, w.at_last_in("0.0 / 0.0", "0.0"));
    let nan = w.bin(BinOp::Div, x, y, w.at("0.0 / 0.0"));
    let n = w.konst("N", nan);
    let x = w.float_at(t.f64, 0.5, w.at_in("0.5 - 0.5", "0.5"));
    let y = w.float_at(t.f64, 0.5, w.at_last_in("0.5 - 0.5", "0.5"));
    let zero = w.bin(BinOp::Sub, x, y, w.at("0.5 - 0.5"));
    let z = w.konst("Z", zero);
    let whole = w.at("0.0 / 0.0");
    for (op, want) in [
        (BinOp::Eq, false),
        (BinOp::Ne, true),
        (BinOp::Lt, false),
        (BinOp::Le, false),
        (BinOp::Gt, false),
        (BinOp::Ge, false),
    ] {
        let a = w.read_at(n, whole);
        let b = w.read_at(n, whole);
        let e = w.bin(op, a, b, whole);
        assert_eq!(w.eval(&e), Ok(boolean(want)), "NaN {op:?} NaN");
    }
    let a = w.read_at(z, whole);
    let b = w.float_at(t.f64, -0.0, whole);
    let e = w.bin(BinOp::Eq, a, b, whole);
    assert_eq!(w.eval(&e), Ok(boolean(true)), "0.0 == -0.0");
}

fn other_comparisons(target: &'static str) {
    let src = concat!(
        "private const S = \"Ada\" == \"Ada\";\n",
        "private const T = \"Ada\" != \"Bo\";\n",
        "private const N: i64 | null = null;\n",
        "private const P: i64 | null = 7;\n",
    );
    let mut w = World::new(target, src);
    let t = w.t();
    let whole = w.at("\"Ada\" == \"Ada\"");
    let x = w.string("Ada", whole);
    let y = w.string("Ada", whole);
    let e = w.bin(BinOp::Eq, x, y, whole);
    assert_eq!(w.eval(&e), Ok(boolean(true)));
    let whole = w.at("\"Ada\" != \"Bo\"");
    let x = w.string("Ada", whole);
    let y = w.string("Bo", whole);
    let e = w.bin(BinOp::Ne, x, y, whole);
    assert_eq!(w.eval(&e), Ok(boolean(true)));
    let x = w.boolean(true, whole);
    let y = w.boolean(false, whole);
    let e = w.bin(BinOp::Eq, x, y, whole);
    assert_eq!(w.eval(&e), Ok(boolean(false)));
    let nullable = w.tcx.mk_nullable(t.i64);
    let null = w.expr(nullable, w.at_in("= null;", "null"), ExprKind::NullLit);
    let n = w.konst("N", null);
    let mut seven = w.int(t.i64, "7");
    seven.adjust.push(Adjust::WrapNull);
    let p = w.konst("P", seven);
    let pairs = [
        (n, None, true),
        (p, None, false),
        (p, Some(p), true),
        (n, Some(p), false),
    ];
    for (a, b, want) in pairs {
        let x = w.read_at(a, whole);
        let y = match b {
            Some(b) => w.read_at(b, whole),
            None => w.expr(nullable, whole, ExprKind::NullLit),
        };
        let e = w.bin(BinOp::Eq, x, y, whole);
        assert_eq!(w.eval(&e), Ok(boolean(want)));
    }
    let (color, _) = w.enumeration("Color", &[("Red", None), ("Green", None)]);
    for (x, y, want) in [(0, 0, true), (0, 1, false)] {
        let a = w.case(color, x, Vec::new(), whole);
        let b = w.case(color, y, Vec::new(), whole);
        let e = w.bin(BinOp::Eq, a, b, whole);
        assert_eq!(w.eval(&e), Ok(boolean(want)));
    }
}

fn class_comparison(target: &'static str) {
    let mut w = World::new(
        target,
        "private const E = new P { x: 1 } == new P { x: 2 };\n",
    );
    let t = w.t();
    let (class, _) = w.class("P", &[("x", t.i64, false, false)]);
    let one = w.int(t.i64, "1");
    let a = w.new_named(
        class,
        vec![(FieldIdx(0), one)],
        Vec::new(),
        w.at("new P { x: 1 }"),
    );
    let two = w.int(t.i64, "2");
    let b = w.new_named(
        class,
        vec![(FieldIdx(0), two)],
        Vec::new(),
        w.at("new P { x: 2 }"),
    );
    let whole = w.at("new P { x: 1 } == new P { x: 2 }");
    let e = w.bin(BinOp::Eq, a, b, whole);
    let diag = fail(w.eval(&e));
    w.check(
        &diag,
        Code::EN1032,
        "compile-time function calls are not supported yet",
        whole,
        "this compares by calling `equals`",
    );
}

/// `<left> <op> 1 / 0 == 0` inside `context`, which begins `X = ` and ends `;`.
fn guarded(w: &mut World, name: &str, left: bool, op: LogOp, context: &str) -> DefId {
    let t = w.t();
    let word = if left { "true" } else { "false" };
    let l = w.boolean(left, w.at_in(context, word));
    let one = w.int_at(t.i64, 1, w.at_in(context, "1"));
    let zero = w.int_at(t.i64, 0, w.at_in(context, "0"));
    let div = w.bin(BinOp::Div, one, zero, w.at_in(context, "1 / 0"));
    let zero = w.int_at(t.i64, 0, w.at_last_in(context, "0"));
    let eq = w.bin(BinOp::Eq, div, zero, w.at_in(context, "1 / 0 == 0"));
    let whole = w.at_in(context, &context[4..context.len() - 1]);
    let e = w.logical(op, l, eq, whole);
    w.konst(name, e)
}

fn short_circuit(target: &'static str) {
    let src = concat!(
        "private const A = false && 1 / 0 == 0;\n",
        "private const B = true || 1 / 0 == 0;\n",
        "private const C = true && 1 / 0 == 0;\n",
        "private const D = true && false;\n",
    );
    let mut w = World::new(target, src);
    let a = guarded(&mut w, "A", false, LogOp::And, "A = false && 1 / 0 == 0;");
    let b = guarded(&mut w, "B", true, LogOp::Or, "B = true || 1 / 0 == 0;");
    let c = guarded(&mut w, "C", true, LogOp::And, "C = true && 1 / 0 == 0;");
    assert_eq!(w.value(a), Ok(boolean(false)));
    assert_eq!(w.value(b), Ok(boolean(true)));
    let diag = fail(w.value(c));
    let message = "constant evaluation failed: `1 / 0` divides by zero";
    assert_eq!(diag.message, message);
    assert_eq!(diag.primary.span, w.at_in("C = true && 1 / 0", "1 / 0"));
    let l = w.boolean(true, w.at_in("D = true", "true"));
    let r = w.boolean(false, w.at_in("true && false", "false"));
    let e = w.logical(LogOp::And, l, r, w.at("true && false"));
    let d = w.konst("D", e);
    assert_eq!(w.value(d), Ok(boolean(false)));
}

fn skipped_operand(target: &'static str) {
    let src = concat!(
        "private unsafe let flag: bool = true;\n",
        "private const A = false && flag;\n",
        "private const B = false && ready();\n",
    );
    let mut w = World::new(target, src);
    let t = w.t();
    let flag = w.unsafe_let("flag", t.bool);
    let l = w.boolean(false, w.at_in("A = false", "false"));
    let r = w.read_at(flag, w.at_in("&& flag", "flag"));
    let e = w.logical(LogOp::And, l, r, w.at("false && flag"));
    let a = w.konst("A", e);
    let diag = fail(w.value(a));
    w.check(
        &diag,
        Code::EN0412,
        "constant evaluation failed: `flag` is not constant",
        w.at_in("&& flag", "flag"),
        "`flag` is an `unsafe let`, which can change at run time",
    );
    let ready = w.def_of("ready", DefKind::Fn);
    let l = w.boolean(false, w.at_in("B = false", "false"));
    let callee = w.fn_callee(ready);
    let call = w.call(t.bool, callee, Vec::new(), w.at("ready()"));
    let e = w.logical(LogOp::And, l, call, w.at("false && ready()"));
    let b = w.konst("B", e);
    let diag = fail(w.value(b));
    assert_eq!(diag.code, Code::EN1032);
    assert_eq!(diag.primary.span, w.at("ready()"));
}

// ---------------------------------------------------------------------------------
// Casts.

fn int_to_int(target: &'static str) {
    let src = concat!(
        "private const A = 300 as u8;\n",
        "private const B = 255 as u8;\n",
        "private const C = -1 as i8;\n",
        "private const D = -1 as u64;\n",
    );
    let mut w = World::new(target, src);
    let t = w.t();
    let cast = |w: &mut World, value: &str, to: Ty, text: &str| {
        let x = w.int_at(t.i64, parse_int(value), w.at_in(text, value));
        w.cast(x, CastKind::IntToInt, to, w.at(text))
    };
    let a = cast(&mut w, "300", t.u8, "300 as u8");
    let diag = fail(w.eval(&a));
    w.check(
        &diag,
        Code::EN0412,
        "constant evaluation failed: `300 as u8` is out of range for `u8`",
        w.at("300 as u8"),
        "conversion out of range: 300 as u8",
    );
    let b = cast(&mut w, "255", t.u8, "255 as u8");
    assert_eq!(w.eval(&b), Ok(scalar_int(255, t.u8)));
    let c = cast(&mut w, "-1", t.i8, "-1 as i8");
    assert_eq!(w.eval(&c), Ok(scalar_int(0xFF, t.i8)));
    let d = cast(&mut w, "-1", t.u64, "-1 as u64");
    let label = "conversion out of range: -1 as u64";
    assert_eq!(fail(w.eval(&d)).primary.text, label);
}

fn to_usize(target: &'static str) {
    let mut w = World::new(target, "private const A = 4294967296 as usize;\n");
    let t = w.t();
    let x = w.int(t.i64, "4294967296");
    let e = w.cast(x, CastKind::IntToInt, t.usize, w.at("4294967296 as usize"));
    let value = w.eval(&e);
    if w.p() == 4 {
        let diag = fail(value);
        let message = "constant evaluation failed: `4294967296 as usize` is out of range for \
                       `usize`";
        assert_eq!(diag.message, message);
        let label = "conversion out of range: 4294967296 as usize";
        assert_eq!(diag.primary.text, label);
    } else {
        assert_eq!(value, Ok(scalar_int(4294967296, t.usize)));
    }
}

fn int_to_float(target: &'static str) {
    let src = concat!(
        "private const A = 9007199254740993 as f64;\n",
        "private const B = 16777217 as f32;\n",
        "private const C = -5 as f64;\n",
        "private const D = 1152921573326323713 as f32;\n",
    );
    let mut w = World::new(target, src);
    let t = w.t();
    // 2^60 + 2^36 + 1 rounds once, up, to 2^60 + 2^37; through f64 it would first
    // lose the 1 and then tie down to 2^60.
    let once = (1u64 << 60) + (1u64 << 37);
    let rows = [
        ("9007199254740993", t.f64, float(9007199254740992.0, t.f64)),
        ("16777217", t.f32, float32(16777216.0, t.f32)),
        ("-5", t.f64, float(-5.0, t.f64)),
        ("1152921573326323713", t.f32, float32(once as f32, t.f32)),
    ];
    for (value, to, want) in rows {
        let text = format!("{value} as {}", w.tcx.ty_string(to));
        let x = w.int_at(t.i64, parse_int(value), w.at_in(&text, value));
        let e = w.cast(x, CastKind::IntToFloat, to, w.at(&text));
        assert_eq!(w.eval(&e), Ok(want), "{text}");
    }
}

fn float_to_float(target: &'static str) {
    let src = "private const A = 0.1 as f32;\nprivate const B = A as f64;\n";
    let mut w = World::new(target, src);
    let t = w.t();
    let x = w.float_at(t.f64, 0.1, w.at("0.1"));
    let e = w.cast(x, CastKind::FloatToFloat, t.f32, w.at("0.1 as f32"));
    let a = w.konst("A", e);
    let read = w.read_at(a, w.at_in("A as f64", "A"));
    let e = w.cast(read, CastKind::FloatToFloat, t.f64, w.at("A as f64"));
    let b = w.konst("B", e);
    assert_eq!(w.value(a), Ok(float32(0.1, t.f32)));
    assert_eq!(w.value(b), Ok(float(f64::from(0.1f32), t.f64)));
}

fn float_to_int(target: &'static str) {
    let mut w = World::new(target, "private const X = 0;\n");
    let t = w.t();
    let whole = w.at("0");
    for (value, to, want) in [
        (-3.9, t.i64, Some(-3i128)),
        (3.9, t.u8, Some(3)),
        (255.9, t.u8, Some(255)),
        (-0.5, t.u8, Some(0)),
        (-9223372036854775808.0, t.i64, Some(i64::MIN as i128)),
        (127.99, t.i8, Some(127)),
        (256.0, t.u8, None),
        (-1.0, t.u8, None),
        (9223372036854775808.0, t.i64, None),
        (128.0, t.i8, None),
        (f64::NAN, t.i32, None),
        (f64::INFINITY, t.u64, None),
    ] {
        let x = w.float_at(t.f64, value, whole);
        let e = w.cast(x, CastKind::FloatToInt, to, whole);
        let result = w.eval(&e);
        let to = w.tcx.ty_string(to);
        match want {
            Some(want) => assert_eq!(w.int_of(&result.expect("a value")), want, "{value} {to}"),
            None => {
                let label = format!("conversion out of range: {value:?} as {to}");
                assert_eq!(fail(result).primary.text, label);
            }
        }
    }
}

fn enum_to_int(target: &'static str) {
    let src = concat!(
        "private const A = Mode.B as u8;\n",
        "private const B = Mode.D as u8;\n",
        "private const C = Plain.Third as i64;\n",
    );
    let mut w = World::new(target, src);
    let t = w.t();
    let cases = [("A", Some(5)), ("B", None), ("C", Some(-2)), ("D", None)];
    let (mode, _) = w.enumeration("Mode", &cases);
    let cases = [("First", None), ("Second", None), ("Third", None)];
    let (plain, _) = w.enumeration("Plain", &cases);
    let b = w.case(mode, 1, Vec::new(), w.at("Mode.B"));
    let e = w.cast(b, CastKind::EnumToInt, t.u8, w.at("Mode.B as u8"));
    assert_eq!(w.eval(&e), Ok(scalar_int(6, t.u8)));
    let d = w.case(mode, 3, Vec::new(), w.at("Mode.D"));
    let e = w.cast(d, CastKind::EnumToInt, t.u8, w.at("Mode.D as u8"));
    let diag = fail(w.eval(&e));
    w.check(
        &diag,
        Code::EN0412,
        "constant evaluation failed: `Mode.D as u8` is out of range for `u8`",
        w.at("Mode.D as u8"),
        "conversion out of range: -1 as u8",
    );
    let third = w.case(plain, 2, Vec::new(), w.at("Plain.Third"));
    let e = w.cast(
        third,
        CastKind::EnumToInt,
        t.i64,
        w.at("Plain.Third as i64"),
    );
    assert_eq!(w.eval(&e), Ok(scalar_int(2, t.i64)));
}

fn bool_and_raw(target: &'static str) {
    let src = "private const A = true as i32;\nprivate const SCREEN = 0xB8000 as *u16;\n";
    let mut w = World::new(target, src);
    let t = w.t();
    let truth = w.boolean(true, w.at("true"));
    let e = w.cast(truth, CastKind::BoolToInt, t.i32, w.at("true as i32"));
    assert_eq!(w.eval(&e), Ok(scalar_int(1, t.i32)));
    let raw = w.tcx.mk_raw(t.u16);
    let addr = w.int(t.usize, "0xB8000");
    let e = w.cast(addr, CastKind::UsizeToRaw, raw, w.at("0xB8000 as *u16"));
    let screen = w.konst("SCREEN", e);
    assert_eq!(w.value(screen), Ok(scalar_int(0xB8000, raw)));
    // The reverse is not in SPEC 4.9's list.
    let read = w.read_at(screen, w.at("0xB8000 as *u16"));
    let e = w.cast(read, CastKind::RawToUsize, t.usize, w.at("0xB8000 as *u16"));
    let diag = fail(w.eval(&e));
    let message = "constant evaluation failed: `0xB8000 as *u16` is not constant";
    assert_eq!(diag.message, message);
    assert_eq!(diag.primary.text, "this conversion is not constant");
}

fn wrapped_cast(target: &'static str) {
    let mut w = World::new(target, "private const A: u8 | null = 255 as u8;\n");
    let t = w.t();
    let x = w.int(t.i64, "255");
    let nullable = w.tcx.mk_nullable(t.u8);
    // Whichever type typing records on a wrapped expression, the value is a `u8`.
    for ty in [t.u8, nullable] {
        let mut e = w.cast(x.clone(), CastKind::IntToInt, ty, w.at("255 as u8"));
        e.adjust.push(Adjust::WrapNull);
        let present = ConstTree::Present(Box::new(scalar_int(255, t.u8)));
        assert_eq!(w.eval(&e), Ok(present));
    }
}

// ---------------------------------------------------------------------------------
// Constants and cycles.

fn on_demand(target: &'static str) {
    let src = "private const C = B + A;\nprivate const B = A * 3;\nprivate const A = 2;\n";
    let mut w = World::new(target, src);
    let t = w.t();
    let two = w.int(t.i64, "2");
    let a = w.konst("A", two);
    let read = w.read_at(a, w.at_in("A * 3", "A"));
    let three = w.int(t.i64, "3");
    let mul = w.bin(BinOp::Mul, read, three, w.at("A * 3"));
    let b = w.konst("B", mul);
    let rb = w.read_at(b, w.at_in("B + A", "B"));
    let ra = w.read_at(a, w.at_in("B + A", "A"));
    let sum = w.bin(BinOp::Add, rb, ra, w.at("B + A"));
    let c = w.konst("C", sum);
    assert_eq!(w.value(c), Ok(scalar_int(8, t.i64)));
    // B and A were evaluated on the way and are kept.
    assert_eq!(w.state.result(b), Some(&Ok(scalar_int(6, t.i64))));
    assert_eq!(w.state.result(a), Some(&Ok(scalar_int(2, t.i64))));
    assert_eq!(w.value(b), Ok(scalar_int(6, t.i64)));
}

fn stored_value(target: &'static str) {
    let mut w = World::new(target, "private const A = 10;\nprivate const B = A * 3;\n");
    let t = w.t();
    let a = w.bodiless("A", t.i64);
    w.tcx.set_const(a, scalar_int(10, t.i64));
    let read = w.read_at(a, w.at_in("A * 3", "A"));
    let three = w.int(t.i64, "3");
    let mul = w.bin(BinOp::Mul, read, three, w.at("A * 3"));
    let b = w.konst("B", mul);
    assert_eq!(w.value(b), Ok(scalar_int(30, t.i64)));
    assert_eq!(w.value(a), Ok(scalar_int(10, t.i64)));
}

fn no_initialiser(target: &'static str) {
    let mut w = World::new(
        target,
        "private const A = broken;\nprivate const B = A + 1;\n",
    );
    let t = w.t();
    let a = w.bodiless("A", t.i64);
    let read = w.read_at(a, w.at_in("A + 1", "A"));
    let one = w.int(t.i64, "1");
    let sum = w.bin(BinOp::Add, read, one, w.at("A + 1"));
    let b = w.konst("B", sum);
    assert_eq!(w.value(b), Err(ConstError::Reported));
    assert_eq!(w.value(a), Err(ConstError::Reported));
}

fn propagation(target: &'static str) {
    let src = concat!(
        "private const A: u8 = 255 + 1;\n",
        "private const B = A;\n",
        "private const C = B;\n",
    );
    let mut w = World::new(target, src);
    let t = w.t();
    let x = w.int(t.u8, "255");
    let y = w.int(t.u8, "1");
    let sum = w.bin(BinOp::Add, x, y, w.at("255 + 1"));
    let a = w.konst("A", sum);
    let b = w.alias("B", a, w.at_in("B = A", "A"));
    let c = w.alias("C", b, w.at_in("C = B", "B"));
    let from_c = fail(w.fresh(c));
    let from_a = fail(w.fresh(a));
    assert_eq!(from_c, from_a);
    assert_eq!(from_a.primary.span, w.at("255 + 1"));
    let message = "constant evaluation failed: `255 + 1` overflows `u8`";
    assert_eq!(from_a.message, message);
}

fn long_chain(target: &'static str) {
    let mut w = World::new(target, "");
    let t = w.t();
    let n = 20_000;
    // C_i = C_(i+1) + 1, the last 0, evaluated from C_0, which needs every other.
    let defs: Vec<DefId> = (0..n)
        .map(|i| {
            let mut data = DefData::new(
                w.path(&format!("C{i}")),
                DefKind::Const,
                w.module,
                Span::DUMMY,
            );
            data.name_span = Span::DUMMY;
            let def = w.tcx.define_def(data);
            w.tcx.set_item_ty(def, t.i64);
            def
        })
        .collect();
    for i in 0..n {
        let init = if i + 1 == n {
            w.int_at(t.i64, 0, Span::DUMMY)
        } else {
            let read = w.read_at(defs[i + 1], Span::DUMMY);
            let one = w.int_at(t.i64, 1, Span::DUMMY);
            w.bin(BinOp::Add, read, one, Span::DUMMY)
        };
        w.define(defs[i], init);
    }
    assert_eq!(w.value(defs[0]), Ok(scalar_int((n - 1) as u128, t.i64)));
}

fn two_cycle(target: &'static str) {
    let mut w = World::new(target, "private const A = B;\nprivate const B = A;\n");
    let t = w.t();
    let a = w.bodiless("A", t.i64);
    let b = w.bodiless("B", t.i64);
    let rb = w.read_at(b, w.at_in("A = B", "B"));
    let ra = w.read_at(a, w.at_in("B = A", "A"));
    w.define(a, rb);
    w.define(b, ra);
    let from_a = fail(w.fresh(a));
    w.check(
        &from_a,
        Code::EN0412,
        "constant cycle: `A` uses `B`, which uses `A`",
        w.decl("const", "A"),
        "`A` depends on its own value",
    );
    let from_b = fail(w.fresh(b));
    assert_eq!(from_a, from_b);
    // Every constant of the cycle keeps the one diagnostic.
    let _ = w.value(b);
    assert_eq!(w.state.result(a), w.state.result(b));
    let golden = lines(&[
        "error[EN0412]: constant cycle: `A` uses `B`, which uses `A`",
        " --> src/main.en:1:15",
        "  |",
        "1 | private const A = B;",
        "  |               ^ `A` depends on its own value",
        "  |",
        "  = explain: run `enrang explain EN0412`",
        "",
        "error: aborting due to 1 previous error",
    ]);
    assert_eq!(w.render(&from_a), golden);
}

fn self_cycle(target: &'static str) {
    let mut w = World::new(target, "private const A = A + 1;\n");
    let t = w.t();
    let a = w.bodiless("A", t.i64);
    let read = w.read_at(a, w.at_in("A + 1", "A"));
    let one = w.int(t.i64, "1");
    let sum = w.bin(BinOp::Add, read, one, w.at("A + 1"));
    w.define(a, sum);
    let diag = fail(w.value(a));
    w.check(
        &diag,
        Code::EN0412,
        "constant cycle: `A` uses `A`",
        w.decl("const", "A"),
        "`A` depends on its own value",
    );
}

fn long_cycle(target: &'static str) {
    let src = concat!(
        "private const C = B + 1;\n",
        "private const A = B;\n",
        "private const B = D;\n",
        "private const D = A;\n",
    );
    let mut w = World::new(target, src);
    let t = w.t();
    let c = w.bodiless("C", t.i64);
    let a = w.bodiless("A", t.i64);
    let b = w.bodiless("B", t.i64);
    let d = w.bodiless("D", t.i64);
    let rb = w.read_at(b, w.at_in("B + 1", "B"));
    let one = w.int(t.i64, "1");
    let sum = w.bin(BinOp::Add, rb, one, w.at("B + 1"));
    w.define(c, sum);
    let rb = w.read_at(b, w.at_in("A = B", "B"));
    w.define(a, rb);
    let rd = w.read_at(d, w.at_in("B = D", "D"));
    w.define(b, rd);
    let ra = w.read_at(a, w.at_in("D = A", "A"));
    w.define(d, ra);
    let message = "constant cycle: `A` uses `B`, which uses `D`, which uses `A`";
    for entry in [c, a, b, d] {
        let diag = fail(w.fresh(entry));
        let label = "`A` depends on its own value";
        w.check(&diag, Code::EN0412, message, w.decl("const", "A"), label);
    }
}

fn skipped_cycle(target: &'static str) {
    let mut w = World::new(
        target,
        "private const A = false && B;\nprivate const B = A;\n",
    );
    let t = w.t();
    let a = w.bodiless("A", t.bool);
    let b = w.bodiless("B", t.bool);
    let l = w.boolean(false, w.at("false"));
    let rb = w.read_at(b, w.at_in("&& B", "B"));
    let and = w.logical(LogOp::And, l, rb, w.at("false && B"));
    w.define(a, and);
    let ra = w.read_at(a, w.at_in("B = A", "A"));
    w.define(b, ra);
    let message = "constant cycle: `A` uses `B`, which uses `A`";
    assert_eq!(fail(w.value(a)).message, message);
}

// ---------------------------------------------------------------------------------
// Layout.

fn primitive_sizes(target: &'static str) {
    let mut w = World::new(target, "private const X = sizeOf<i64>();\n");
    let t = w.t();
    let p = w.p();
    let whole = w.at("sizeOf<i64>()");
    let slice_ref = w.tcx.mk_ref(w.tcx.mk_slice(t.u8));
    for (form, want) in [
        (FormKind::SizeOf(t.i64), 8),
        (FormKind::AlignOf(t.i64), p),
        (FormKind::AlignOf(t.f64), p),
        (FormKind::SizeOf(t.usize), p),
        (FormKind::SizeOf(t.u16), 2),
        (FormKind::SizeOf(slice_ref), 2 * p),
        (FormKind::SizeOf(t.bool), 1),
    ] {
        let e = w.size_form(form, whole);
        let want = scalar_int(u128::from(want), t.usize);
        assert_eq!(w.eval(&e), Ok(want), "{form:?}");
    }
}

fn aggregate_sizes(target: &'static str) {
    let mut w = World::new(target, "private const X = offsetOf<Player>(\"score\");\n");
    let t = w.t();
    let p = w.p();
    let whole = w.at("offsetOf<Player>(\"score\")");
    let fields = [
        ("name", t.str, false, false),
        ("score", t.i64, false, false),
    ];
    let (_, player) = w.class("Player", &fields);
    let object = w.tcx.mk_object(vec![
        (intern("found"), t.bool),
        (intern("index"), t.i32),
        (intern("last"), t.bool),
    ]);
    let tuple = w.tcx.mk_tuple(&[t.bool, t.i32, t.bool]);
    for (form, want) in [
        (FormKind::SizeOf(player), if p == 4 { 20 } else { 32 }),
        (FormKind::OffsetOf(player, FieldIdx(1)), 3 * p),
        (FormKind::SizeOf(object), 8),
        (FormKind::OffsetOf(object, FieldIdx(0)), 4),
        (FormKind::OffsetOf(object, FieldIdx(1)), 0),
        (FormKind::SizeOf(tuple), 8),
        (FormKind::OffsetOf(tuple, FieldIdx(1)), 0),
        (FormKind::OffsetOf(tuple, FieldIdx(2)), 5),
    ] {
        let e = w.size_form(form, whole);
        let want = scalar_int(u128::from(want), t.usize);
        assert_eq!(w.eval(&e), Ok(want), "{form:?}");
    }
}

/// The note of SPEC 4.9, as SPEC writes it.
const SINK_NOTE: &str = "the layout of `Sink` depends on what its methods do with its references";

fn borrowing_class(target: &'static str) {
    let src = concat!(
        "private const SINK_BYTES = sizeOf<Sink>();\n",
        "private const A = alignOf<Sink>();\n",
    );
    let mut w = World::new(target, src);
    let t = w.t();
    let spec = std::fs::read_to_string(enrang_testkit::workspace_root().join("docs/SPEC.md"))
        .expect("docs/SPEC.md");
    assert!(
        spec.contains(&format!("`` {SINK_NOTE} ``")),
        "SPEC 4.9 changed its note"
    );
    let str_ref = w.tcx.mk_ref(t.str);
    let (_, sink) = w.class("Sink", &[("s", str_ref, false, false)]);
    let size = w.size_form(FormKind::SizeOf(sink), w.at("sizeOf<Sink>()"));
    let sink_bytes = w.konst("SINK_BYTES", size);
    let align = w.size_form(FormKind::AlignOf(sink), w.at("alignOf<Sink>()"));
    let a = w.konst("A", align);
    for (def, text) in [(sink_bytes, "sizeOf<Sink>()"), (a, "alignOf<Sink>()")] {
        let diag = fail(w.value(def));
        w.check(
            &diag,
            Code::EN0412,
            &format!("constant evaluation failed: `{text}` is not constant"),
            w.at(text),
            "`Sink` holds references",
        );
        assert_eq!(diag.entries.len(), 1);
        assert_eq!(diag.entries[0].kind, EntryKind::Note);
        assert_eq!(diag.entries[0].text, SINK_NOTE);
    }
    // The layout comes first, whatever the field (`offsetOf`).
    let form = FormKind::OffsetOf(sink, FieldIdx(0));
    let offset = w.size_form(form, w.at("sizeOf<Sink>()"));
    assert_eq!(fail(w.eval(&offset)).entries[0].text, SINK_NOTE);
    let diag = fail(w.fresh(sink_bytes));
    let golden = lines(&[
        "error[EN0412]: constant evaluation failed: `sizeOf<Sink>()` is not constant",
        " --> src/main.en:1:28",
        "  |",
        "1 | private const SINK_BYTES = sizeOf<Sink>();",
        "  |                            ^^^^^^^^^^^^^^ `Sink` holds references",
        "  |",
        &format!("  = note: {SINK_NOTE}"),
        "  = explain: run `enrang explain EN0412`",
        "",
        "error: aborting due to 1 previous error",
    ]);
    assert_eq!(w.render(&diag), golden);
}

fn borrowing_others(target: &'static str) {
    let src = concat!(
        "private const X = sizeOf<[i64, &string]>();\n",
        "private const Y = sizeOf<&string>();\n",
    );
    let mut w = World::new(target, src);
    let t = w.t();
    let str_ref = w.tcx.mk_ref(t.str);
    let tuple = w.tcx.mk_tuple(&[t.i64, str_ref]);
    let e = w.size_form(FormKind::SizeOf(tuple), w.at("sizeOf<[i64, &string]>()"));
    let diag = fail(w.eval(&e));
    assert_eq!(diag.primary.text, "`[i64, &string]` holds references");
    let note = "the layout of `[i64, &string]` depends on what the code using it does with its \
                references";
    assert_eq!(diag.entries[0].text, note);
    let e = w.size_form(FormKind::SizeOf(str_ref), w.at("sizeOf<&string>()"));
    let diag = fail(w.eval(&e));
    let label = "`&string` is a reference whose form follows its permission";
    assert_eq!(diag.primary.text, label);
    let note = "the layout of `&string` depends on what the code using it does with it";
    assert_eq!(diag.entries[0].text, note);
}

fn too_large(target: &'static str) {
    let mut w = World::new(target, "private const X = sizeOf<u8[3000000000]>();\n");
    let t = w.t();
    let big = w.tcx.mk_fixed(t.u8, 3_000_000_000);
    let e = w.size_form(FormKind::SizeOf(big), w.at("sizeOf<u8[3000000000]>()"));
    let value = w.eval(&e);
    if w.p() == 4 {
        let diag = fail(value);
        assert_eq!(diag.code, Code::EN0412);
        let label = "`u8[3000000000]` is larger than `isize.MAX` bytes";
        assert_eq!(diag.primary.text, label);
    } else {
        assert_eq!(value, Ok(scalar_int(3_000_000_000, t.usize)));
    }
}

fn unsized_or_error(target: &'static str) {
    let mut w = World::new(target, "private const X = sizeOf<Slice<u8>>();\n");
    let t = w.t();
    let slice = w.tcx.mk_slice(t.u8);
    let e = w.size_form(FormKind::SizeOf(slice), w.at("sizeOf<Slice<u8>>()"));
    let label = "`Slice<u8>` has no size of its own";
    assert_eq!(fail(w.eval(&e)).primary.text, label);
    let e = w.size_form(FormKind::SizeOf(t.error), w.at("sizeOf<Slice<u8>>()"));
    assert_eq!(w.eval(&e), Err(ConstError::Reported));
}

// ---------------------------------------------------------------------------------
// Aggregates and views.

fn literals_of_constants(target: &'static str) {
    let src = concat!(
        "private const A: i64[3] = [1, 2, 3];\n",
        "private const B: u8[4] = [0; 4];\n",
        "private const C: [i64, bool] = [9, true];\n",
        "private const D = { x: 5, y: 6 };\n",
    );
    let mut w = World::new(target, src);
    let t = w.t();
    let lit = w.fixed_lit(t.i64, "[1, 2, 3]", &["1", "2", "3"]);
    let a = w.konst("A", lit);
    let zero = w.int_at(t.u8, 0, w.at_in("[0; 4]", "0"));
    let fixed = w.tcx.mk_fixed(t.u8, 4);
    let rep = w.expr(fixed, w.at("[0; 4]"), ExprKind::Repeat(Box::new(zero), 4));
    let b = w.konst("B", rep);
    let nine = w.int_at(t.i64, 9, w.at_in("[9, true]", "9"));
    let truth = w.boolean(true, w.at("true"));
    let tuple = w.tcx.mk_tuple(&[t.i64, t.bool]);
    let lit = w.expr(
        tuple,
        w.at("[9, true]"),
        ExprKind::TupleLit(vec![nine, truth]),
    );
    let c = w.konst("C", lit);
    let object = w
        .tcx
        .mk_object(vec![(intern("x"), t.i64), (intern("y"), t.i64)]);
    let TyKind::Object(shape) = w.tcx.kind(object) else {
        panic!("an object type")
    };
    let fields = w.ints_in(t.i64, "{ x: 5, y: 6 }", &["5", "6"]);
    let kind = ExprKind::ObjectLit {
        shape,
        fields,
        eval: Vec::new(),
    };
    let lit = w.expr(object, w.at("{ x: 5, y: 6 }"), kind);
    let d = w.konst("D", lit);
    let ints = |values: &[u128], ty| values.iter().map(|&v| scalar_int(v, ty)).collect();
    assert_eq!(w.value(a), Ok(ConstTree::Array(ints(&[1, 2, 3], t.i64))));
    assert_eq!(w.value(b), Ok(ConstTree::Array(ints(&[0, 0, 0, 0], t.u8))));
    let pair = vec![scalar_int(9, t.i64), boolean(true)];
    assert_eq!(w.value(c), Ok(ConstTree::Tuple(pair)));
    assert_eq!(w.value(d), Ok(ConstTree::Object(ints(&[5, 6], t.i64))));
}

fn class_defaults(target: &'static str) {
    let mut w = World::new(target, "private const ORIGIN = new Point { x: 1, y: 2 };\n");
    let t = w.t();
    let tag = w.tcx.mk_nullable(t.u8);
    let flags = w.tcx.mk_fixed(t.u8, 2);
    let raw = w.tcx.mk_raw(t.u8);
    let label = w.tcx.mk_nullable(t.i64);
    let fields = [
        ("x", t.i64, false, false),
        ("y", t.i64, false, false),
        ("tag", tag, false, false),
        ("flags", flags, false, false),
        ("next", raw, false, false),
        ("ratio", t.f64, false, false),
        ("on", t.bool, false, false),
        ("label", label, true, true),
    ];
    let (point, _) = w.class("Point", &fields);
    let mut named = w.ints_in(t.i64, "{ x: 1, y: 2 }", &["1", "2"]);
    let y = named.pop().expect("y");
    let x = named.pop().expect("x");
    let fields = vec![(FieldIdx(0), x), (FieldIdx(1), y)];
    let left_out = (2..8).map(FieldIdx).collect();
    let lit = w.new_named(point, fields, left_out, w.at("new Point { x: 1, y: 2 }"));
    let origin = w.konst("ORIGIN", lit);
    let want = ConstTree::Adt {
        adt: point,
        variant: None,
        fields: vec![
            scalar_int(1, t.i64),
            scalar_int(2, t.i64),
            ConstTree::Null,
            ConstTree::Array(vec![scalar_int(0, t.u8), scalar_int(0, t.u8)]),
            scalar_int(0, raw),
            float(0.0, t.f64),
            boolean(false),
            ConstTree::Null,
        ],
    };
    assert_eq!(w.value(origin), Ok(want));
}

fn initialised_field(target: &'static str) {
    let mut w = World::new(
        target,
        "private const DEFAULT = new Config { verbose: true };\n",
    );
    let t = w.t();
    let fields = [
        ("retries", t.i64, true, false),
        ("verbose", t.bool, false, false),
    ];
    let (config, _) = w.class("Config", &fields);
    let truth = w.boolean(true, w.at("true"));
    let whole = w.at("new Config { verbose: true }");
    let lit = w.new_named(config, vec![(FieldIdx(1), truth)], vec![FieldIdx(0)], whole);
    let def = w.konst("DEFAULT", lit);
    let diag = fail(w.value(def));
    let label = "`retries` is left to its initialiser, which runs at run time";
    w.check(
        &diag,
        Code::EN0412,
        "constant evaluation failed: `new Config { verbose: true }` is not constant",
        whole,
        label,
    );
    // An `override` in the chain gives a field a written default too.
    if let AdtKind::Class(class) = &mut w.tcx.adt_mut(config).kind {
        class.fields[0].has_default = false;
        class.overrides.push(FieldIdx(0));
    }
    assert_eq!(fail(w.fresh(def)).primary.text, label);
    // A field whose type has no default (a string) has no constant default.
    let (named, _) = w.class("Named", &[("name", t.str, false, false)]);
    let lit = w.new_named(named, Vec::new(), vec![FieldIdx(0)], whole);
    let label = "`name` has no constant default";
    assert_eq!(fail(w.eval(&lit)).primary.text, label);
    // A left-out fixed array's default counts each element against the budget.
    let buffer = w.tcx.mk_fixed(t.u8, 2_000_000);
    let (big, _) = w.class("Big", &[("buf", buffer, false, false)]);
    let lit = w.new_named(big, Vec::new(), vec![FieldIdx(0)], whole);
    let label = "a constant holds at most 1048576 values";
    assert_eq!(fail(w.eval(&lit)).primary.text, label);
}

fn case_literals(target: &'static str) {
    let mut w = World::new(
        target,
        "private const T: Token | null = Token.Num { value: 5 };\n",
    );
    let t = w.t();
    let adt = w.tcx.define_adt(AdtDecl {
        data: DefData::new(w.path("Token"), DefKind::TypeAlias, w.module, Span::DUMMY),
        name: intern("Token"),
        generics: w.tcx.empty_generics(),
        kind: AdtKind::Enum(EnumDef::new(Vec::new())),
    });
    let mut num = VariantDef::new(intern("Num"));
    num.fields.push(FieldDef::new(intern("value"), t.i64, adt));
    if let AdtKind::Enum(en) = &mut w.tcx.adt_mut(adt).kind {
        en.variants = vec![num, VariantDef::new(intern("Add"))];
    }
    let five = w.int(t.i64, "5");
    let mut case = w.case(adt, 0, vec![five], w.at("Token.Num { value: 5 }"));
    case.adjust.push(Adjust::WrapNull);
    let def = w.konst("T", case);
    let want = ConstTree::Adt {
        adt,
        variant: Some(VariantIdx(0)),
        fields: vec![scalar_int(5, t.i64)],
    };
    assert_eq!(w.value(def), Ok(ConstTree::Present(Box::new(want))));
}

fn literal_views(target: &'static str) {
    let src = concat!(
        "public const PRIMES: &Slice<i64> = &[2, 3, 5, 7];\n",
        "private const ZEROS: &u8[3] = &[0; 3];\n",
        "private const COPY = PRIMES;\n",
    );
    let mut w = World::new(target, src);
    let t = w.t();
    let lit = w.fixed_lit(t.i64, "[2, 3, 5, 7]", &["2", "3", "5", "7"]);
    let slice_ref = w.tcx.mk_ref(w.tcx.mk_slice(t.i64));
    let whole = w.at("&[2, 3, 5, 7]");
    let mut view = w.expr(slice_ref, whole, ExprKind::Borrow(Box::new(lit)));
    view.adjust.push(Adjust::FixedToSlice);
    let primes = w.konst("PRIMES", view);
    let zero = w.int_at(t.u8, 0, w.at_in("[0; 3]", "0"));
    let fixed = w.tcx.mk_fixed(t.u8, 3);
    let rep = w.expr(fixed, w.at("[0; 3]"), ExprKind::Repeat(Box::new(zero), 3));
    let fixed_ref = w.tcx.mk_ref(fixed);
    let view = w.expr(fixed_ref, w.at("&[0; 3]"), ExprKind::Borrow(Box::new(rep)));
    let zeros = w.konst("ZEROS", view);
    let copy = w.alias("COPY", primes, w.at_in("COPY = PRIMES", "PRIMES"));
    let items = [2, 3, 5, 7].iter().map(|&v| scalar_int(v, t.i64)).collect();
    let want = ConstTree::View { elem: t.i64, items };
    assert_eq!(w.value(primes), Ok(want.clone()));
    assert_eq!(w.value(copy), Ok(want));
    let items = vec![scalar_int(0, t.u8); 3];
    assert_eq!(w.value(zeros), Ok(ConstTree::View { elem: t.u8, items }));
}

fn other_borrows(target: &'static str) {
    let src = "private const A: i64[2] = [1, 2];\nprivate const B: &Slice<i64> = &A;\n";
    let mut w = World::new(target, src);
    let t = w.t();
    let lit = w.fixed_lit(t.i64, "[1, 2]", &["1", "2"]);
    let a = w.konst("A", lit);
    let read = w.read_at(a, w.at_in("&A", "A"));
    let fixed_ref = w.tcx.mk_ref(w.tcx.mk_fixed(t.i64, 2));
    let mut borrow = w.expr(fixed_ref, w.at("&A"), ExprKind::Borrow(Box::new(read)));
    borrow.adjust.push(Adjust::FixedToSlice);
    let b = w.konst("B", borrow);
    let diag = fail(w.value(b));
    w.check(
        &diag,
        Code::EN0412,
        "constant evaluation failed: `&A` is not constant",
        w.at("&A"),
        "only `&` of a bracket literal is constant",
    );
}

fn growable_array(target: &'static str) {
    let mut w = World::new(target, "private const XS = [1, 2];\n");
    let t = w.t();
    let items = w.ints_in(t.i64, "[1, 2]", &["1", "2"]);
    let array = w.tcx.mk_array(t.i64);
    let lit = w.expr(array, w.at("[1, 2]"), ExprKind::ArrayLit(items));
    let diag = fail(w.eval(&lit));
    w.check(
        &diag,
        Code::EN0412,
        "constant evaluation failed: `[1, 2]` is not constant",
        w.at("[1, 2]"),
        "an `i64[]` allocates at run time",
    );
}

// ---------------------------------------------------------------------------------
// Calls, spreads, parts that are not constant, the budget.

fn function_call(target: &'static str) {
    let mut w = World::new(target, "private const A = double(2);\n");
    let t = w.t();
    let double = w.def_of("double", DefKind::Fn);
    let two = w.int(t.i64, "2");
    let callee = w.fn_callee(double);
    let call = w.call(t.i64, callee, vec![two], w.at("double(2)"));
    let a = w.konst("A", call);
    let diag = fail(w.value(a));
    w.check(
        &diag,
        Code::EN1032,
        "compile-time function calls are not supported yet",
        w.at("double(2)"),
        "this calls a function",
    );
    let note = "a constant is computed while compiling, and the compiler does not run functions \
                yet.";
    assert_eq!(diag.entries.len(), 1);
    assert_eq!(diag.entries[0].kind, EntryKind::Note);
    assert_eq!(diag.entries[0].text, note);
    assert_eq!(diag.helps.len(), 1);
    let help = "Use a literal expression, or initialise at startup";
    assert_eq!(diag.helps[0].message, help);
    assert!(diag.helps[0].edits.is_empty());
    let golden = lines(&[
        "error[EN1032]: compile-time function calls are not supported yet",
        " --> src/main.en:1:19",
        "  |",
        "1 | private const A = double(2);",
        "  |                   ^^^^^^^^^ this calls a function",
        "  |",
        &format!("  = note: {note}"),
        &format!("help: {help}"),
        "  = explain: run `enrang explain EN1032`",
        "",
        "error: aborting due to 1 previous error",
    ]);
    assert_eq!(w.render(&diag), golden);
}

fn other_calls(target: &'static str) {
    let src = concat!(
        "private const B = new Box(5);\n",
        "private const C = n?.next();\n",
        "private const D = toString(1);\n",
    );
    let mut w = World::new(target, src);
    let t = w.t();
    let ctor = w.def_of("Box", DefKind::Ctor);
    let five = w.int(t.i64, "5");
    let args = w.tcx.empty_list();
    let kind = ExprKind::New {
        ctor,
        args,
        values: vec![five],
    };
    let new = w.expr(t.i64, w.at("new Box(5)"), kind);
    let diag = fail(w.eval(&new));
    assert_eq!(diag.code, Code::EN1032);
    assert_eq!(diag.primary.text, "this calls a constructor");
    let next = w.def_of("next", DefKind::Method);
    let nullable = w.tcx.mk_nullable(t.i64);
    let base = w.expr(nullable, w.at_in("n?.next()", "n"), ExprKind::NullLit);
    let callee = w.fn_callee(next);
    let chain = OptChain {
        base,
        member: OptMember::Call {
            callee,
            args: Vec::new(),
        },
        void_result: false,
    };
    let opt = w.expr(
        nullable,
        w.at("n?.next()"),
        ExprKind::OptionalChain(Box::new(chain)),
    );
    let diag = fail(w.eval(&opt));
    assert_eq!(
        (diag.code, diag.primary.span),
        (Code::EN1032, w.at("n?.next()"))
    );
    let one = w.int(t.i64, "1");
    let form = Callee::Form(FormKind::ToString);
    let call = w.call(t.str, form, vec![one], w.at("toString(1)"));
    assert_eq!(fail(w.eval(&call)).code, Code::EN1032);
}

fn spreads(target: &'static str) {
    let src = concat!(
        "private const X: i64[2] = [1, 2];\n",
        "private const Y = [0, ...X];\n",
        "private const Z = [... X];\n",
    );
    let mut w = World::new(target, src);
    let t = w.t();
    let lit = w.fixed_lit(t.i64, "[1, 2]", &["1", "2"]);
    let x = w.konst("X", lit);
    let array = w.tcx.mk_array(t.i64);
    let zero = w.int_at(t.i64, 0, w.at_in("[0, ...X]", "0"));
    let operand = w.read_at(x, w.at_in("...X", "X"));
    let parts = vec![
        ArrayPart::Item(zero),
        ArrayPart::Spread(operand, SpreadKind::Fixed(2)),
    ];
    let kind = ExprKind::ArrayBuild { elem: t.i64, parts };
    let build = w.expr(array, w.at("[0, ...X]"), kind);
    let y = w.konst("Y", build);
    let diag = fail(w.value(y));
    w.check(
        &diag,
        Code::EN0412,
        "constant evaluation failed: `...` is not constant",
        w.at_in("...X", "..."),
        "this spread",
    );
    assert_eq!(diag.entries.len(), 1);
    assert_eq!(diag.entries[0].text, "a spread allocates at run time");
    // Space between the token and the operand.
    let operand = w.read_at(x, w.at_in("... X", "X"));
    let parts = vec![ArrayPart::Spread(operand, SpreadKind::Fixed(2))];
    let kind = ExprKind::ArrayBuild { elem: t.i64, parts };
    let build = w.expr(array, w.at("[... X]"), kind);
    assert_eq!(fail(w.eval(&build)).primary.span, w.at_in("... X", "..."));
    // Typing reports the same error at the token it saw (S:756, A:890).
    let dots = w.at_in("[0, ...X]", "...");
    let from_typing = ConstError::spread(&w.tcx, dots);
    assert_eq!(from_typing, ConstError::Fail(Box::new(fail(w.fresh(y)))));
}

fn non_constant_parts(target: &'static str) {
    let src = concat!(
        "let n = 3; private const A = n;\n",
        "private unsafe let screen: u16 = 0;\n",
        "private const B = screen;\n",
        "private const C = `${1}`;\n",
        "private const D = P.x;\n",
        "private const E = double;\n",
        "private const F = c ? 1 : 2;\n",
    );
    let mut w = World::new(target, src);
    let t = w.t();
    // A local of the body being evaluated.
    let mut locals = IdVec::new();
    let n = locals.push(LocalDecl {
        name: Some(intern("n")),
        ty: t.i64,
        mutable: true,
        kind: LocalKind::User,
        span: w.at_in("let n", "n"),
    });
    let mut body = Body::empty(BodyOwner::Statements(w.module), t.i64, Span::DUMMY);
    body.locals = locals;
    let read = w.expr(t.i64, w.at_in("A = n", "n"), ExprKind::Local(n));
    let diag = fail(w.state.eval(&w.tcx, &mut w.bodies, &body, &read));
    w.check(
        &diag,
        Code::EN0412,
        "constant evaluation failed: `n` is not constant",
        w.at_in("A = n", "n"),
        "`n` is a local variable",
    );
    let screen = w.unsafe_let("screen", t.u16);
    let read = w.read_at(screen, w.at_in("B = screen", "screen"));
    let label = "`screen` is an `unsafe let`, which can change at run time";
    assert_eq!(fail(w.eval(&read)).primary.text, label);
    let hole = w.int_at(t.i64, 1, w.at_in("`${1}`", "1"));
    let kind = ExprKind::Template(vec![TplPart::Hole(hole)]);
    let template = w.expr(t.str, w.at("`${1}`"), kind);
    let diag = fail(w.eval(&template));
    assert_eq!(
        diag.message,
        "constant evaluation failed: ``${1}`` is not constant"
    );
    assert_eq!(diag.primary.text, "a template builds a string at run time");
    let base = w.boolean(true, w.at_in("P.x", "P"));
    let field = w.expr(
        t.i64,
        w.at("P.x"),
        ExprKind::Field(Box::new(base), FieldIdx(0)),
    );
    let diag = fail(w.eval(&field));
    w.check(
        &diag,
        Code::EN0412,
        "constant evaluation failed: `P.x` is not constant",
        w.at("P.x"),
        "this is not a constant expression",
    );
    let f = w.def_of("double", DefKind::Fn);
    let args = w.tcx.empty_list();
    let value = ConstValue::FnAddr(FnRef { def: f, args });
    let addr = w.expr(
        t.usize,
        w.at_in("E = double", "double"),
        ExprKind::Const(value),
    );
    let label = "a function's address is not a constant";
    assert_eq!(fail(w.eval(&addr)).primary.text, label);
    let c = w.boolean(true, w.at_in("c ?", "c"));
    let one = w.int_at(t.i64, 1, w.at_in("c ? 1 : 2", "1"));
    let two = w.int_at(t.i64, 2, w.at_in("c ? 1 : 2", "2"));
    let kind = ExprKind::Ternary(Box::new(c), Box::new(one), Box::new(two));
    let ternary = w.expr(t.i64, w.at("c ? 1 : 2"), kind);
    let message = "constant evaluation failed: `c ? 1 : 2` is not constant";
    assert_eq!(fail(w.eval(&ternary)).message, message);
    // A conversion that only happens at run time.
    let mut through = w.int_at(t.i64, 3, w.at_in("let n = 3", "3"));
    through.adjust.push(Adjust::ReadThrough);
    let label = "this conversion happens at run time";
    assert_eq!(fail(w.eval(&through)).primary.text, label);
}

fn rejected(target: &'static str) {
    let mut w = World::new(target, "private const A = oops + 1;\n");
    let t = w.t();
    let bad = w.expr(t.error, w.at("oops"), ExprKind::Never);
    let one = w.int_at(t.i64, 1, w.at_in("oops + 1", "1"));
    let sum = w.bin(BinOp::Add, bad, one, w.at("oops + 1"));
    assert_eq!(w.eval(&sum), Err(ConstError::Reported));
    assert_eq!(ConstError::Reported.diagnostic(), None);
    let dots = w.at("+");
    let spread = ConstError::spread(&w.tcx, dots);
    let diag = fail(Err(spread.clone()));
    assert_eq!(spread.diagnostic(), Some(&diag));
}

fn long_parts(target: &'static str) {
    let long = "aVeryLongName.anotherLongName.yetAnotherOne";
    let src = format!("private const A = {long};\nprivate const B = x\n  .y;\n");
    let mut w = World::new(target, &src);
    let t = w.t();
    assert!(long.len() > 40);
    let message = "constant evaluation failed: this expression is not constant";
    let base = w.boolean(true, w.at("aVeryLongName"));
    let field = w.expr(
        t.i64,
        w.at(long),
        ExprKind::Field(Box::new(base), FieldIdx(0)),
    );
    assert_eq!(fail(w.eval(&field)).message, message);
    let base = w.boolean(true, w.at_in("= x", "x"));
    let field = w.expr(
        t.i64,
        w.at("x\n  .y"),
        ExprKind::Field(Box::new(base), FieldIdx(0)),
    );
    assert_eq!(fail(w.eval(&field)).message, message);
}

fn budget(target: &'static str) {
    assert_eq!(MAX_VALUES, 1 << 20);
    let src = concat!(
        "private const A = [0; 1048575];\n",
        "private const B = [0; 1048576];\n",
        "private const C = [0; 600000];\n",
        "private const D = [C, C];\n",
    );
    let mut w = World::new(target, src);
    let t = w.t();
    let repeat = |w: &mut World, n: u64, text: &str| {
        let zero = w.int_at(t.u8, 0, w.at_in(text, "0"));
        let fixed = w.tcx.mk_fixed(t.u8, n);
        w.expr(fixed, w.at(text), ExprKind::Repeat(Box::new(zero), n))
    };
    // Exactly MAX_VALUES values: the array and its elements.
    let a = repeat(&mut w, 1_048_575, "[0; 1048575]");
    let a = w.konst("A", a);
    match w.value(a) {
        Ok(ConstTree::Array(items)) => assert_eq!(items.len(), 1_048_575),
        other => panic!("{:?}", other.map(|_| ())),
    }
    let b = repeat(&mut w, 1_048_576, "[0; 1048576]");
    let b = w.konst("B", b);
    let diag = fail(w.value(b));
    w.check(
        &diag,
        Code::EN0412,
        "constant evaluation failed: `[0; 1048576]` is too large to evaluate",
        w.at("[0; 1048576]"),
        "a constant holds at most 1048576 values",
    );
    let c = repeat(&mut w, 600_000, "[0; 600000]");
    let c = w.konst("C", c);
    let first = w.read_at(c, w.at_in("[C, C]", "C"));
    let second = w.read_at(c, w.at_in(", C]", "C"));
    let fixed = w.tcx.mk_fixed(w.tcx.mk_fixed(t.u8, 600_000), 2);
    let lit = w.expr(
        fixed,
        w.at("[C, C]"),
        ExprKind::ArrayLit(vec![first, second]),
    );
    let d = w.konst("D", lit);
    let diag = fail(w.value(d));
    assert_eq!(diag.primary.span, w.at_in(", C]", "C"));
    let message = "constant evaluation failed: `C` is too large to evaluate";
    assert_eq!(diag.message, message);
    // A huge count fails before anything is built.
    let big = repeat(&mut w, u64::MAX, "[0; 1048576]");
    let label = "a constant holds at most 1048576 values";
    assert_eq!(fail(w.eval(&big)).primary.text, label);
}

// ---------------------------------------------------------------------------------
// From source (owner 4F; plan d.14's contexts, g.2): programs checked by `load` and
// `analyze`, each context handing its typed HIR to the interpreter.

pub(crate) mod from_source {
    use enrang_hir::{ArmValue, ConstTree, ConstValue, ExprKind, StmtKind, Tcx, VariantValue};
    use enrang_testkit::Harness;

    use crate::support::{MINI_LIB, Run, fake_lib, run_with};

    /// The program of `text` as `src/main.en` on `x86_64-linux`, with the fake
    /// library.
    pub(crate) fn src(text: &str) -> Run {
        src_on("x86_64-linux", text)
    }

    /// The program of `text` as `src/main.en` on `target`.
    pub(crate) fn src_on(target: &str, text: &str) -> Run {
        run_with(&[("src/main.en", text)], fake_lib(MINI_LIB), target)
    }

    /// Each diagnostic of a run, in order: its code, `line:col` of its primary
    /// span, its message and its primary label.
    pub(crate) fn diags(r: &Run) -> Vec<[String; 4]> {
        r.diags
            .iter()
            .map(|d| {
                let loc = r.map.loc(d.primary.span.lo);
                [
                    d.code.name().to_owned(),
                    format!("{}:{}", loc.line, loc.col),
                    d.message.clone(),
                    d.primary.text.clone(),
                ]
            })
            .collect()
    }

    /// A row of [`diags`].
    pub(crate) fn diag(code: &str, at: &str, message: &str, label: &str) -> [String; 4] {
        [code, at, message, label].map(str::to_owned)
    }

    /// Asserts that `text` gives exactly `want`.
    pub(crate) fn gives(text: &str, want: &[[String; 4]]) {
        let r = src(text);
        assert_eq!(diags(&r), want, "{text}\n{}", r.rendered());
    }

    /// The value kept for the constant or `unsafe let` `name` of `src/main`.
    pub(crate) fn value(r: &Run, name: &str) -> Option<ConstTree> {
        let def = r.def(&format!("src/main::{name}"));
        r.tcx.const_value(def).cloned()
    }

    /// The integer of a scalar constant, and its type as messages spell it.
    pub(crate) fn int(tcx: &Tcx, tree: &ConstTree) -> (i128, String) {
        match tree {
            ConstTree::Scalar(v @ ConstValue::Int(_, ty)) => {
                (v.as_i128(tcx).expect("an integer"), tcx.ty_string(*ty))
            }
            other => panic!("not an integer constant: {other:?}"),
        }
    }

    /// The integer value of constant `name` with its type.
    fn int_of(r: &Run, name: &str) -> (i128, String) {
        let tree = value(r, name).unwrap_or_else(|| panic!("`{name}` has no value"));
        int(&r.tcx, &tree)
    }

    /// The type of `src/main::Class::field`'s field as messages spell it.
    fn field_ty(r: &Run, class: &str, field: &str) -> String {
        let def = r.def(&format!("src/main::{class}"));
        let adt = r.tcx.adt_of(def).expect("a class");
        let class_def = r.tcx.adt(adt).as_class().expect("a class");
        let (_, f) = class_def
            .field_named(enrang_base::intern(field))
            .expect("the field");
        r.tcx.ty_string(f.ty)
    }

    const NOTE: &str = "a spread allocates at run time";

    pub fn register(h: &mut Harness) {
        constants(h);
        spreads(h);
        lengths(h);
        enums(h);
        asserts(h);
        review(h);
    }

    /// Stage 6's review fixes and the cases the mutation gate found unpinned.
    fn review(h: &mut Harness) {
        h.case(
            "consteval/source/S:756: a local that shadows a constant is no constant in a body's length",
            || {
                gives(
                    "public const K: usize = 5;\npublic function f(): void { const K = 2; const a: u8[K] = [0, 0, 0, 0, 0]; const b = [0; K]; }\n",
                    &[
                        diag(
                            "EN0412",
                            "2:54",
                            "constant evaluation failed: `K` is not constant",
                            "`K` is a local variable",
                        ),
                        diag(
                            "EN0412",
                            "2:90",
                            "constant evaluation failed: `K` is not constant",
                            "`K` is a local variable",
                        ),
                    ],
                );
                // The constant itself, with no local of its name, is one.
                src("public const K: usize = 5;\npublic function f(): void { const a: u8[K] = [0, 0, 0, 0, 0]; }\n").clean();
            },
        );
        h.case(
            "consteval/source/a namespace's constant is a simple length in a declaration's type",
            || {
                let r = run_with(
                    &[
                        ("src/main.en", "import * as m from \"./m\";\npublic function f(x: u8[m.N]): void { }\n"),
                        ("src/m.en", "public const N: usize = 3;\n"),
                    ],
                    fake_lib(MINI_LIB),
                    "x86_64-linux",
                );
                r.clean();
                let def = r.def("src/main::f");
                assert_eq!(r.tcx.ty_string(r.tcx.sig(def).params[0].ty), "u8[3]");
            },
        );
        h.case(
            "consteval/source/a length of 0 is no negative length (mutant M28)",
            || {
                src("public const Z: usize = 0;\npublic function f(x: u8[Z]): void { }\n").clean();
            },
        );
        h.case(
            "consteval/source/a constant can't hold an array behind `| null`, nor a class with a destructor (mutants M30, M33)",
            || {
                gives(
                    "public const A: i64[] | null = null;\n",
                    &[diag(
                        "EN0412",
                        "1:14",
                        "constant evaluation failed: a constant can't hold an `i64[]`",
                        "`i64[]` owns heap memory",
                    )],
                );
                gives(
                    "public final class D { public x: i32; public destructor() { } }\npublic const R: D = new D { x: 1 };\n",
                    &[diag(
                        "EN0412",
                        "2:14",
                        "constant evaluation failed: a constant can't hold a `D`",
                        "`D` has a destructor",
                    )],
                );
            },
        );
        h.case(
            "consteval/source/an annotation already reported is no EN0410 for its initialiser",
            || {
                gives(
                    "public function f(n: usize): void { const a: u8[n] = []; }\n",
                    &[diag(
                        "EN0412",
                        "1:49",
                        "constant evaluation failed: `n` is not constant",
                        "`n` is a local variable",
                    )],
                );
                gives(
                    "public function f(): void { const a: Foo = []; }\n",
                    &[diag(
                        "EN0302",
                        "1:38",
                        "cannot find type `Foo` in this scope",
                        "not found",
                    )],
                );
            },
        );
    }

    // -----------------------------------------------------------------------------
    // Top-level constants and `unsafe let` initialisers (S:756, S:758, S:1351).

    fn constants(h: &mut Harness) {
        h.case(
            "consteval/source/a constant's value is kept, constants read in any order",
            || {
                for text in [
                    "private const N: usize = 4;\nprivate const M = N * 2;\n",
                    "private const M = N * 2;\nprivate const N: usize = 4;\n",
                ] {
                    let r = src(text);
                    r.clean();
                    assert_eq!(int_of(&r, "N"), (4, "usize".to_owned()), "{text}");
                    assert_eq!(int_of(&r, "M"), (8, "usize".to_owned()), "{text}");
                }
            },
        );
        h.case(
            "consteval/source/an unannotated integer constant defaults to `int` (S:756)",
            || {
                let r = src("private const K = 3;\nprivate const L = -K;\n");
                r.clean();
                assert_eq!(int_of(&r, "K"), (3, "int".to_owned()));
                assert_eq!(int_of(&r, "L"), (-3, "int".to_owned()));
            },
        );
        h.case(
            "consteval/source/S:756's `PRIMES` and `NAME` are constants",
            || {
                let r = src(
                    "public const PRIMES: &Slice<i64> = &[2, 3, 5, 7];\npublic const NAME: &string = \"Ada\";\npublic const FOUR: &u8[4] = &[1, 2, 3, 4];\n",
                );
                r.clean();
                assert!(matches!(
                    value(&r, "FOUR"),
                    Some(ConstTree::View { items, .. }) if items.len() == 4
                ));
                match value(&r, "PRIMES") {
                    Some(ConstTree::View { elem, items }) => {
                        assert_eq!(r.tcx.ty_string(elem), "i64");
                        let ints: Vec<i128> = items.iter().map(|i| int(&r.tcx, i).0).collect();
                        assert_eq!(ints, [2, 3, 5, 7]);
                    }
                    other => panic!("not a view: {other:?}"),
                }
                match value(&r, "NAME") {
                    Some(ConstTree::Scalar(ConstValue::Str(id))) => {
                        assert_eq!(&*r.tcx.str(id), "Ada");
                    }
                    other => panic!("not a string literal: {other:?}"),
                }
            },
        );
        h.case(
            "consteval/source/fixed-array, repeat, tuple and nullable constants",
            || {
                let r = src("private const F: i64[3] = [1, 2, 3];
private const R = [0; 2];
private const T: [i64, bool] = [1, true];
private const N: i64 | null = null;
private const P: i64 | null = 5;
");
                r.clean();
                let ints = |tree: &ConstTree| match tree {
                    ConstTree::Array(items) => {
                        items.iter().map(|i| int(&r.tcx, i).0).collect::<Vec<_>>()
                    }
                    other => panic!("not an array: {other:?}"),
                };
                assert_eq!(ints(&value(&r, "F").expect("F")), [1, 2, 3]);
                assert_eq!(ints(&value(&r, "R").expect("R")), [0, 0]);
                assert_eq!(value(&r, "N"), Some(ConstTree::Null));
                match value(&r, "P") {
                    Some(ConstTree::Present(inner)) => assert_eq!(int(&r.tcx, &inner).0, 5),
                    other => panic!("not present: {other:?}"),
                }
                match value(&r, "T") {
                    Some(ConstTree::Tuple(parts)) => {
                        assert_eq!(int(&r.tcx, &parts[0]).0, 1);
                        assert_eq!(parts[1], ConstTree::Scalar(ConstValue::Bool(true)));
                    }
                    other => panic!("not a tuple: {other:?}"),
                }
            },
        );
        h.case(
            "consteval/source/class, case and object literals of constants (S:756)",
            || {
                let r = src("public final class Point { public x: i64; public y: i64 = 0; public z: i64 | null; }
public enum Shape { Circle { r: i64 }, Dot }
private const P = new Point { x: 1 };
private const C = Shape.Circle { r: K };
private const D = Shape.Dot;
private const O: { a: i64, b: bool } = { a: K, b: false };
private const K: i64 = 2;
");
                assert_eq!(
                    diags(&r),
                    [diag(
                        "EN0412",
                        "3:19",
                        "constant evaluation failed: `new Point { x: 1 }` is not constant",
                        "`y` is left to its initialiser, which runs at run time",
                    )],
                    "{}",
                    r.rendered()
                );
                match value(&r, "C") {
                    Some(ConstTree::Adt { variant, fields, .. }) => {
                        assert_eq!(variant, Some(enrang_hir::VariantIdx(0)));
                        assert_eq!(int(&r.tcx, &fields[0]).0, 2);
                    }
                    other => panic!("not a case: {other:?}"),
                }
                assert!(matches!(
                    value(&r, "D"),
                    Some(ConstTree::Adt { variant: Some(enrang_hir::VariantIdx(1)), .. })
                ));
                match value(&r, "O") {
                    Some(ConstTree::Object(fields)) => {
                        assert_eq!(fields.len(), 2);
                        assert!(fields.contains(&ConstTree::Scalar(ConstValue::Bool(false))));
                    }
                    other => panic!("not an object: {other:?}"),
                }
                let r = src("public final class Point { public x: i64; public z: i64 | null; }
private const P = new Point { x: 1 };
");
                r.clean();
                match value(&r, "P") {
                    Some(ConstTree::Adt { variant: None, fields, .. }) => {
                        assert_eq!(int(&r.tcx, &fields[0]).0, 1);
                        assert_eq!(fields[1], ConstTree::Null);
                    }
                    other => panic!("not a class literal: {other:?}"),
                }
            },
        );
        h.case(
            "consteval/source/a cycle of annotated constants is EN0412 at the first (S:756)",
            || {
                let r = src("private const A: i32 = B;\nprivate const B: i32 = A;\n");
                assert_eq!(
                    r.rendered(),
                    "error[EN0412]: constant cycle: `A` uses `B`, which uses `A`
 --> src/main.en:1:15
  |
1 | private const A: i32 = B;
  |               ^ `A` depends on its own value
  |
  = explain: run `enrang explain EN0412`

error: aborting due to 1 previous error
"
                );
                // S:756's own spelling, unannotated.
                gives(
                    "private const A = B; private const B = A;\n",
                    &[diag(
                        "EN0412",
                        "1:15",
                        "constant cycle: `A` uses `B`, which uses `A`",
                        "`A` depends on its own value",
                    )],
                );
                gives(
                    "private const A = 1;\nprivate const B = A + C;\nprivate const C = B;\n",
                    &[diag(
                        "EN0412",
                        "2:15",
                        "constant cycle: `B` uses `C`, which uses `B`",
                        "`B` depends on its own value",
                    )],
                );
            },
        );
        h.case(
            "consteval/source/EN0412: overflow and division by zero, with the panic's text",
            || {
                let r = src("private const A: u8 = 255 + 1;\n");
                assert_eq!(
                    r.rendered(),
                    "error[EN0412]: constant evaluation failed: `255 + 1` overflows `u8`
 --> src/main.en:1:23
  |
1 | private const A: u8 = 255 + 1;
  |                       ^^^^^^^ integer overflow: 255 + 1
  |
  = explain: run `enrang explain EN0412`

error: aborting due to 1 previous error
"
                );
                gives(
                    "private unsafe let s: usize = 3 / 0;\n",
                    &[diag(
                        "EN0412",
                        "1:31",
                        "constant evaluation failed: `3 / 0` divides by zero",
                        "division by zero",
                    )],
                );
                // Checked at the target's width: `usize` is 32 bits on `i386`.
                let text = "private const W: usize = 65536 * 65536;\n";
                src_on("x86_64-linux", text).clean();
                let r = src_on("i386-linux", text);
                assert_eq!(
                    diags(&r),
                    [diag(
                        "EN0412",
                        "1:26",
                        "constant evaluation failed: `65536 * 65536` overflows `usize`",
                        "integer overflow: 65536 * 65536",
                    )]
                );
            },
        );
        h.case(
            "consteval/source/a constant holds no heap: a string or a growable array is EN0412",
            || {
                let r = src("private const W = \"x\";\n");
                assert_eq!(
                    r.rendered(),
                    "error[EN0412]: constant evaluation failed: a constant can't hold a `string`
 --> src/main.en:1:15
  |
1 | private const W = \"x\";
  |               ^ `string` owns heap memory
  |
help: a string literal is a constant as a `&string`: write the type `&string`
  = explain: run `enrang explain EN0412`

error: aborting due to 1 previous error
"
                );
                gives(
                    "private const T = [1, 2, 3];\n",
                    &[diag(
                        "EN0412",
                        "1:19",
                        "constant evaluation failed: `[1, 2, 3]` is not constant",
                        "an `int[]` allocates at run time",
                    )],
                );
            },
        );
        h.case(
            "consteval/source/EN1032: a call in a `const` or `unsafe let` initialiser (S:3481)",
            || {
                let r = src(
                    "private function f(): i32 { return 1; }\nprivate const C = f();\n",
                );
                assert_eq!(
                    r.rendered(),
                    "error[EN1032]: compile-time function calls are not supported yet
 --> src/main.en:2:19
  |
2 | private const C = f();
  |                   ^^^ this calls a function
  |
  = note: a constant is computed while compiling, and the compiler does not run functions yet.
help: Use a literal expression, or initialise at startup
  = explain: run `enrang explain EN1032`

error: aborting due to 1 previous error
"
                );
                gives(
                    "private function f(): usize { return 1; }\nprivate unsafe let s: usize = f() + 1;\n",
                    &[diag(
                        "EN1032",
                        "2:31",
                        "compile-time function calls are not supported yet",
                        "this calls a function",
                    )],
                );
            },
        );
        h.case(
            "consteval/source/an `unsafe let` is no constant, and its own value is kept",
            || {
                let r = src("private unsafe let s: usize = 3;\n");
                r.clean();
                assert_eq!(int_of(&r, "s"), (3, "usize".to_owned()));
                // In a constant's initialiser that is EN0412 alone: no `unsafe`
                // could make it constant, so 4E adds no EN0801 (one report per
                // mistake, stage 6 review).
                gives(
                    "private unsafe let s: usize = 3;\nprivate const C: usize = s;\n",
                    &[diag(
                        "EN0412",
                        "2:26",
                        "constant evaluation failed: `s` is not constant",
                        "`s` is an `unsafe let`, which can change at run time",
                    )],
                );
            },
        );
        h.case(
            "consteval/source/a constant read as a `match` arm value is its value",
            || {
                let r = src(
                    "private const K = 2;\npublic function f(x: i32): i32 { return match (x) { K => 1, default => 0 }; }\n",
                );
                r.clean();
                let program = r.program.as_ref().expect("checked");
                let body = &program.bodies[&r.def("src/main::f")];
                let Some(StmtKind::Return(Some(ret))) = body.root.stmts.first().map(|s| &s.kind)
                else {
                    panic!("a return");
                };
                let ExprKind::Match { arms, .. } = &ret.kind else {
                    panic!("a match");
                };
                match arms[0].values.as_slice() {
                    [ArmValue::Const(v @ ConstValue::Int(_, ty))] => {
                        assert_eq!(v.as_i128(&r.tcx), Some(2));
                        assert_eq!(r.tcx.ty_string(*ty), "int");
                    }
                    other => panic!("not the constant's value: {other:?}"),
                }
                // A constant that failed gives its own error and nothing more.
                gives(
                    "private const K: u8 = 200 + 100;\npublic function f(x: u8): i32 { return match (x) { K => 1, default => 0 }; }\n",
                    &[diag(
                        "EN0412",
                        "1:23",
                        "constant evaluation failed: `200 + 100` overflows `u8`",
                        "integer overflow: 200 + 100",
                    )],
                );
            },
        );
    }

    // -----------------------------------------------------------------------------
    // `...` in a `ConstExpr` (S:756, T:746): EN0412 at the token, with the note,
    // before any expected type is compared.

    fn spreads(h: &mut Harness) {
        h.case(
            "consteval/source/a spread in a constant is EN0412 at `...`, before any EN0401",
            || {
                let r = src(
                    "private const X: i64[3] = [1, 2, 3];\nprivate const Y: i64[2] = [...X];\n",
                );
                assert_eq!(
                    r.rendered(),
                    "error[EN0412]: constant evaluation failed: `...` is not constant
 --> src/main.en:2:28
  |
2 | private const Y: i64[2] = [...X];
  |                            ^^^ this spread
  |
  = note: a spread allocates at run time
  = explain: run `enrang explain EN0412`

error: aborting due to 1 previous error
"
                );
                let r = src("private const X: i64[3] = [1, 2, 3];\nprivate const Y = [...X];\n");
                assert_eq!(r.diags.len(), 1, "{}", r.rendered());
                assert_eq!(r.diags[0].entries.len(), 1);
            },
        );
        let cases: [(&str, &str, &str); 5] = [
            (
                "an `unsafe let` initialiser",
                "private const X: i64[2] = [1, 2];\nprivate unsafe let s: i64[3] = [...X];\n",
                "2:33",
            ),
            (
                "a `RepeatLit` count",
                "private const X: i64[2] = [1, 2];\npublic function f(): void { const a = [0; [...X][0]]; }\n",
                "2:44",
            ),
            (
                "a `T[N]` length",
                "private const X: i64[2] = [1, 2];\npublic class P { public xs: u8[[...X][0]]; }\n",
                "2:33",
            ),
            (
                "a top-level `assert` in a file with no statements",
                "private const X: i64[2] = [1, 2];\nassert([...X].length() == 2, \"two\");\n",
                "2:9",
            ),
            (
                "an enum value",
                "private const X: i64[2] = [1, 2];\nprivate enum E { A = [...X][0] }\n",
                "2:23",
            ),
        ];
        for (place, text, at) in cases {
            h.case(
                format!("consteval/source/a spread in {place} is EN0412 with the note"),
                move || {
                    let r = src(text);
                    assert_eq!(
                        diags(&r),
                        [diag(
                            "EN0412",
                            at,
                            "constant evaluation failed: `...` is not constant",
                            "this spread",
                        )],
                        "{}",
                        r.rendered()
                    );
                    assert!(r.rendered().contains(&format!("= note: {NOTE}")));
                },
            );
        }
        h.case(
            "consteval/source/a spread in a body or a field initialiser is no `ConstExpr`",
            || {
                src("private const X: i64[2] = [1, 2];
public function f(): void { const ys = [...X]; }
public class C { public zs: i64[] = [...X]; }
")
                .clean();
            },
        );
    }

    // -----------------------------------------------------------------------------
    // `T[N]` lengths and `RepeatLit` counts (`eval_len`).

    fn lengths(h: &mut Harness) {
        h.case(
            "consteval/source/a length is a constant expression, read in any order",
            || {
                let r = src("public class A {
  public xs: u8[M];
  public ys: u8[(3)];
  public zs: u8[u8.MAX];
  public ws: u8[N + 1];
}
private const M = N * 2;
private const N: usize = 4;
");
                r.clean();
                assert_eq!(field_ty(&r, "A", "xs"), "u8[8]");
                assert_eq!(field_ty(&r, "A", "ys"), "u8[3]");
                assert_eq!(field_ty(&r, "A", "zs"), "u8[255]");
                assert_eq!(field_ty(&r, "A", "ws"), "u8[5]");
            },
        );
        h.case(
            "consteval/source/lengths in a signature, a body and a repeat count",
            || {
                let r = src("public function f(x: &u8[N]): void {
  const a: u8[N] = [0; N];
  const b = [1; N * 2];
}
private const N: usize = 2;
");
                r.clean();
                assert_eq!(r.sig("src/main::f"), "(x: &u8[2]) => void");
                let program = r.program.as_ref().expect("checked");
                let body = &program.bodies[&r.def("src/main::f")];
                let tys: Vec<String> = body
                    .locals
                    .iter()
                    .filter(|l| l.name.is_some_and(|n| n.as_str() != "x"))
                    .map(|l| r.tcx.ty_string(l.ty))
                    .collect();
                assert_eq!(tys, ["u8[2]", "int[4]"]);
            },
        );
        h.case(
            "consteval/source/a local or `this` in a length is EN0412",
            || {
                gives(
                    "public function f(n: usize): void { const a = [0; n]; }\n",
                    &[diag(
                        "EN0412",
                        "1:51",
                        "constant evaluation failed: `n` is not constant",
                        "`n` is a local variable",
                    )],
                );
                // A top-level `const` among statements is a variable (S:756).
                gives(
                    "const n = 3;\nconst a: u8[n] = [0, 0, 0];\n",
                    &[diag(
                        "EN0412",
                        "2:13",
                        "constant evaluation failed: `n` is not constant",
                        "`n` is a local variable",
                    )],
                );
                gives(
                    "public class C {\n  public n: usize = 2;\n  public f(): void { const a = [0; this.n]; }\n}\n",
                    &[diag(
                        "EN0412",
                        "3:36",
                        "constant evaluation failed: `this` is not constant",
                        "an object known only at run time",
                    )],
                );
            },
        );
        h.case(
            "consteval/source/a length of no integer type, negative, or reading an `unsafe let`",
            || {
                gives(
                    "public class P { public xs: u8[1.5]; }\n",
                    &[diag(
                        "EN0401",
                        "1:32",
                        "mismatched types: expected `usize`, found `f64`",
                        "this is `f64`",
                    )],
                );
                gives(
                    "private const N: i32 = -1;\npublic class P { public xs: u8[N]; }\n",
                    &[diag(
                        "EN0412",
                        "2:32",
                        "constant evaluation failed: `N` is negative",
                        "this is -1, and a length can't be negative",
                    )],
                );
                gives(
                    "private unsafe let s: usize = 3;\npublic class P { public xs: u8[s]; }\n",
                    &[diag(
                        "EN0412",
                        "2:32",
                        "constant evaluation failed: `s` is not constant",
                        "`s` is an `unsafe let`, which can change at run time",
                    )],
                );
                gives(
                    "private function n(): usize { return 2; }\npublic class P { public xs: u8[n()]; }\n",
                    &[diag(
                        "EN1032",
                        "2:32",
                        "compile-time function calls are not supported yet",
                        "this calls a function",
                    )],
                );
            },
        );
        h.case(
            "consteval/source/a literal length must fit `usize` (EN0411 on `i386`)",
            || {
                let text = "private unsafe let big: u8[5000000000];\n";
                let r = src_on("x86_64-linux", text);
                r.clean();
                assert_eq!(
                    r.tcx
                        .ty_string(r.tcx.item_ty(r.def("src/main::big")).expect("typed")),
                    "u8[5000000000]"
                );
                let r = src_on("i386-linux", text);
                assert_eq!(
                    diags(&r),
                    [diag(
                        "EN0411",
                        "1:28",
                        "`5000000000` doesn't fit `usize`",
                        "`usize` holds 0 to 4294967295",
                    )]
                );
            },
        );
        h.case(
            "consteval/source/a name in no scope in a length is EN0301 alone",
            || {
                let r = src("public class P { public xs: u8[M]; }\n");
                assert_eq!(r.codes(), ["EN0301"], "{}", r.rendered());
                assert_eq!(diags(&r)[0][1], "1:32");
            },
        );
        h.case(
            "consteval/source/a length that reads itself is a cycle",
            || {
                gives(
                    "private const A: usize = [0; A][0];\n",
                    &[diag(
                        "EN0412",
                        "1:15",
                        "constant cycle: `A` uses `A`",
                        "`A` depends on its own value",
                    )],
                );
                gives(
                    "public class P { public xs: u8[Q]; }\nprivate const Q: usize = R;\nprivate const R: usize = Q;\n",
                    &[diag(
                        "EN0412",
                        "2:15",
                        "constant cycle: `Q` uses `R`, which uses `Q`",
                        "`Q` depends on its own value",
                    )],
                );
            },
        );
        h.case(
            "consteval/source/a length reading what is not complete where it is written is EN0412",
            || {
                // A computed case value that reads a layout is known only once
                // declarations are; a class's layout too.
                let r = src("private enum E { A = sizeOf<Q>() as i32, B }\npublic class P { public xs: u8[E.B as usize]; }\npublic class Q { public a: i64 = 0; public b: i64 = 0; }\n");
                assert_eq!(
                    r.rendered(),
                    "error[EN0412]: constant evaluation failed: `E.B as usize` is not known where this type is written
 --> src/main.en:2:32
  |
2 | public class P { public xs: u8[E.B as usize]; }
  |                                ^^^^^^^^^^^^ a declaration's types are sized before the declarations this reads are complete
  |
help: write it with literals, constants, operators, `as` and `sizeOf` of types declared above
  = explain: run `enrang explain EN0412`

error: aborting due to 1 previous error
"
                );
                // A class laid out by a length gets its fields first, wherever it is
                // declared (fix-6: SPEC 4.9 sets no order).
                gives(
                    "public class P { public xs: u8[sizeOf<Q>()]; }\npublic class Q { public a: i64 = 0; }\n",
                    &[],
                );
                // Literal or constant case values are known wherever the enum is,
                // computed when a length first reads them (stage 6 review).
                let r = src("public class P { public xs: u8[E.B as usize]; }\nprivate enum E { A, B = 5 }\n");
                r.clean();
                assert_eq!(field_ty(&r, "P", "xs"), "u8[5]");
                let r = src("private enum E { A, B = K }\nprivate const K = 3;\npublic class P { public xs: u8[E.B as usize]; }\n");
                r.clean();
                assert_eq!(field_ty(&r, "P", "xs"), "u8[3]");
                let r = src("public const K: i32 = 2;\npublic enum E { A = K, B }\npublic function f(x: u8[E.B as usize]): void { }\n");
                r.clean();
                let r = src("private enum E { A, B = 5 }\npublic class P { public xs: u8[E.B as usize]; }\n");
                r.clean();
                assert_eq!(field_ty(&r, "P", "xs"), "u8[5]");
                src("private enum E { A, B = K }\nprivate const K = 3;\npublic function f(): void { const xs: u8[E.B as usize] = [0; 3]; }\n").clean();
            },
        );
    }

    // -----------------------------------------------------------------------------
    // Enum values (S:591) and `@repr`'s fit (S:1288).

    fn enums(h: &mut Harness) {
        h.case(
            "consteval/source/a computed case value, and the case after it",
            || {
                let r = src("private const K = 4;
private enum E { A = K * 2, B, C = 1 }
private const X = E.A as i32;
private const Y = E.B as i32;
private const Z = E.C as i32;
");
                r.clean();
                assert_eq!(int_of(&r, "X").0, 8);
                assert_eq!(int_of(&r, "Y").0, 9);
                assert_eq!(int_of(&r, "Z").0, 1);
                let adt = r.tcx.adt_of(r.def("src/main::E")).expect("an enum");
                let values: Vec<Option<VariantValue>> = r
                    .tcx
                    .adt(adt)
                    .as_enum()
                    .expect("an enum")
                    .variants
                    .iter()
                    .map(|v| v.value)
                    .collect();
                assert_eq!(
                    values,
                    [Some(VariantValue::Int(8)), None, Some(VariantValue::Int(1))]
                );
            },
        );
        h.case(
            "consteval/source/a case value may read another enum's, declared later",
            || {
                let r = src("private enum E1 { A = X, B }
private const X = E2.B as i32;
private enum E2 { B = K + 1 }
private const K = 7;
private const Y = E1.B as i32;
");
                r.clean();
                assert_eq!(int_of(&r, "X").0, 8);
                assert_eq!(int_of(&r, "Y").0, 9);
            },
        );
        h.case(
            "consteval/source/a case read before its value is computed is EN0412",
            || {
                gives(
                    "private enum E { A = E.B as i32, B = K }\nprivate const K = 7;\n",
                    &[diag(
                        "EN0412",
                        "1:22",
                        "constant evaluation failed: `E.B as i32` is not constant",
                        "the value of `E.B` is not computed yet here",
                    )],
                );
                gives(
                    "private enum E1 { A = E2.B as i32 }\nprivate enum E2 { B = E1.A as i32 }\n",
                    &[diag(
                        "EN0412",
                        "2:23",
                        "constant evaluation failed: `E1.A as i32` is not constant",
                        "the value of `E1.A` is not computed yet here",
                    )],
                );
                // An earlier case is computed already.
                let r = src("private enum E { A = K, B = E.A as i32 + 1 }\nprivate const K = 7;\nprivate const Y = E.B as i32;\n");
                r.clean();
                assert_eq!(int_of(&r, "Y").0, 8);
            },
        );
        h.case(
            "consteval/source/a failed case value is reported once, and so is what reads it",
            || {
                let text = "private enum E { A = 1 / 0, B }\nprivate const Y = E.B as i32;\n";
                gives(
                    text,
                    &[diag(
                        "EN0412",
                        "1:22",
                        "constant evaluation failed: `1 / 0` divides by zero",
                        "division by zero",
                    )],
                );
                // `B` follows `A`, which has no value, so neither has `Y`.
                assert_eq!(value(&src(text), "Y"), None);
                gives(
                    "private function f(): i32 { return 1; }\nprivate enum E { A = f() }\n",
                    &[diag(
                        "EN1032",
                        "2:22",
                        "compile-time function calls are not supported yet",
                        "this calls a function",
                    )],
                );
                gives(
                    "private enum E { A = 1.5 }\n",
                    &[diag(
                        "EN0401",
                        "1:22",
                        "mismatched types: expected an integer, found `f64`",
                        "a case's value is an integer, or else a string literal",
                    )],
                );
            },
        );
        h.case(
            "consteval/source/`@repr` values that do not fit are EN0412 (S:1288)",
            || {
                let r = src("@repr(\"u8\") private enum F { A = 256 }\n");
                assert_eq!(
                    r.rendered(),
                    "error[EN0412]: constant evaluation failed: `256` does not fit `u8`
 --> src/main.en:1:34
  |
1 | @repr(\"u8\") private enum F { A = 256 }
  |                                  ^^^ `F` is `@repr(\"u8\")`, which holds 0 to 255
  |
  = explain: run `enrang explain EN0412`

error: aborting due to 1 previous error
"
                );
                gives(
                    "private const K: u8 = 255;\n@repr(\"u8\") private enum E { A = K, B }\n",
                    &[diag(
                        "EN0412",
                        "2:37",
                        "constant evaluation failed: `B` would be 256, which does not fit `u8`",
                        "`E` is `@repr(\"u8\")`, which holds 0 to 255",
                    )],
                );
                gives(
                    "@repr(\"u16\") private enum E { A = 65535, B }\n",
                    &[diag(
                        "EN0412",
                        "1:42",
                        "constant evaluation failed: `B` would be 65536, which does not fit `u16`",
                        "`E` is `@repr(\"u16\")`, which holds 0 to 65535",
                    )],
                );
                gives(
                    "@repr(\"u32\") private enum E { A = -1 }\n",
                    &[diag(
                        "EN0412",
                        "1:35",
                        "constant evaluation failed: `-1` does not fit `u32`",
                        "`E` is `@repr(\"u32\")`, which holds 0 to 4294967295",
                    )],
                );
                src("@repr(\"u8\") private enum E { A = 254, B }\n@repr(\"u16\") private enum G { A = K }\nprivate const K = 65535;\n").clean();
            },
        );
    }

    // -----------------------------------------------------------------------------
    // Compile-time asserts (S:756, A:918): EN0415.

    fn asserts(h: &mut Harness) {
        h.case(
            "consteval/source/EN0415: a top-level assert whose condition is false",
            || {
                let r = src("assert(1 + 1 == 3, \"math\");\n");
                assert_eq!(
                    r.rendered(),
                    "error[EN0415]: compile-time assert failed: math
 --> src/main.en:1:8
  |
1 | assert(1 + 1 == 3, \"math\");
  |        ^^^^^^^^^^ this is `false`
  |
  = explain: run `enrang explain EN0415`

error: aborting due to 1 previous error
"
                );
                gives(
                    "assert(N > 3);\nprivate const N = 3;\n",
                    &[diag(
                        "EN0415",
                        "1:8",
                        "compile-time assert failed",
                        "this is `false`",
                    )],
                );
                src("assert(N == 3, \"three\");\nprivate const N = 3;\n").clean();
            },
        );
        h.case(
            "consteval/source/an assert among statements: constant at compile time, else at run time",
            || {
                gives(
                    "let x = 1;\nassert(1 + 1 == 3, \"math\");\nassert(x == 2);\nconsole.log(x);\n",
                    &[diag(
                        "EN0415",
                        "2:8",
                        "compile-time assert failed: math",
                        "this is `false`",
                    )],
                );
                src("let x = 1;\nassert(x == 2, \"run time\");\nassert(1 + 1 == 2);\n").clean();
            },
        );
        h.case(
            "consteval/source/an assert's condition that fails to evaluate is EN0412 or EN1032",
            || {
                gives(
                    "assert(1 / 0 == 0, \"div\");\n",
                    &[diag(
                        "EN0412",
                        "1:8",
                        "constant evaluation failed: `1 / 0` divides by zero",
                        "division by zero",
                    )],
                );
                gives(
                    "assert(f() == 1);\nprivate function f(): i32 { return 1; }\n",
                    &[diag(
                        "EN1032",
                        "1:8",
                        "compile-time function calls are not supported yet",
                        "this calls a function",
                    )],
                );
            },
        );
        h.case(
            "consteval/source/MR-9: `sizeOf` of a borrowing class is no constant (S:756, T:872)",
            || {
                let text = "public class Sink {
  private out: &string;
  public constructor(out: &string) { this.out = out; }
  public fill(): void { const buf: u8[SINK_BYTES] = [0; SINK_BYTES]; }
}
private const SINK_BYTES = sizeOf<Sink>();
";
                let r = src(text);
                let rows = diags(&r);
                assert_eq!(
                    rows[0],
                    diag(
                        "EN0412",
                        "6:28",
                        "constant evaluation failed: `sizeOf<Sink>()` is not constant",
                        "`Sink` holds references",
                    ),
                    "{}",
                    r.rendered()
                );
                assert!(
                    r.rendered().contains(
                        "= note: the layout of `Sink` depends on what its methods do with its references"
                    ),
                    "{}",
                    r.rendered()
                );
                assert!(rows.iter().all(|row| row[0] == "EN0412"), "{}", r.rendered());
                // Inside a body it folds at mono, and phase 2 accepts it.
                src("public class Sink {
  private out: &string;
  public constructor(out: &string) { this.out = out; }
}
public function size(): usize { return sizeOf<Sink>(); }
")
                .clean();
            },
        );
    }
}
