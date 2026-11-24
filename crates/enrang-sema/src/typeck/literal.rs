//! Literals (plan d.6; SPEC 4.7 S:728; owner 3A): an integer literal takes an `Int`
//! variable, a `-` directly before it folding first; a literal that does not fit its
//! final type is EN0411, with the `: i64` fix-it when the type came from the `int`
//! default; a float literal keeps its text and is parsed once at its final width, so
//! an `f32` literal is correctly rounded; a string literal is a `string` with
//! `cap == 0` (S:962), which takes `LiteralDescriptor` where `&string` is expected
//! (C13, `coerce.rs`), and a `VariantLit` at a string-literal union (a text not in
//! the union is EN0401 `` `"lft"` is not a `Direction` ``, S:592). Plan c.5 types a
//! literal `&string`; S:962 types it `string`, as the field defaults of S:585-587,
//! the object literal of S:600 and the EN0455 example of S:1139 need.
//!
//! An integer literal whose final type is a float becomes that float's constant,
//! rounded once to nearest from the integer (plan choice). A literal, integer or
//! float, that rounds to infinity at its final width does not fit (plan choice).

use enrang_base::{Span, Symbol, intern};
use enrang_diag::{Code, Diagnostic, Edit, Help, did_you_mean};
use enrang_hir::{
    self as hir, AdtKind, ConstValue, ExprId, ExprKind, FloatTy, IntTy, Ty, TyKind, VariantIdx,
    VariantValue,
};
use enrang_syntax::ast;

use crate::typeck::infer::VarKind;
use crate::typeck::{Deferred, Expect, FnCtxt, Literal};

impl FnCtxt<'_, '_> {
    pub(crate) fn check_literal(&mut self, e: &ast::Expr, ex: Expect) -> hir::Expr {
        match &e.kind {
            ast::ExprKind::Int { value, .. } => self.int_literal(*value, false, e.span, ex),
            ast::ExprKind::Float(text) => self.float_literal(*text, e.span, ex),
            ast::ExprKind::Str(text) | ast::ExprKind::RawTemplate(text) => {
                self.str_literal(*text, e.span, ex)
            }
            ast::ExprKind::Bool(b) => {
                let ty = self.sema.tcx.common().bool;
                self.mk_expr(ty, e.span, ExprKind::Const(ConstValue::Bool(*b)))
            }
            _ => self.error_expr(e.span),
        }
    }

    /// An integer literal, `negative` when a `-` was written directly before it.
    pub(crate) fn int_literal(
        &mut self,
        value: u128,
        negative: bool,
        span: Span,
        ex: Expect,
    ) -> hir::Expr {
        let ty = self.new_var(VarKind::Int, span, "this number");
        self.adopt_numeric(ty, ex);
        let e = self.mk_expr(ty, span, ExprKind::Const(ConstValue::Int(value, ty)));
        self.deferred.push(Deferred::LiteralFit {
            expr: e.id,
            span,
            ty,
            literal: Literal::Int { value, negative },
        });
        e
    }

    /// A float literal with its text (a folded `-` included).
    pub(crate) fn float_literal(&mut self, text: Symbol, span: Span, ex: Expect) -> hir::Expr {
        let ty = self.new_var(VarKind::Float, span, "this number");
        self.adopt_numeric(ty, ex);
        let e = self.mk_expr(ty, span, ExprKind::Const(ConstValue::Float(0, ty)));
        self.deferred.push(Deferred::LiteralFit {
            expr: e.id,
            span,
            ty,
            literal: Literal::Float(text),
        });
        e
    }

    /// A number literal's variable takes the expected numeric type, through one
    /// `| null`, when it may (a hint or a coercion site alike).
    fn adopt_numeric(&mut self, var: Ty, ex: Expect) {
        let Some(t) = ex.ty() else {
            return;
        };
        let mut t = self.shallow(t);
        if let TyKind::Nullable(inner) = self.sema.tcx.kind(t) {
            t = self.shallow(inner);
        }
        let numeric = matches!(
            self.sema.tcx.kind(t),
            TyKind::Int(_) | TyKind::Float(_) | TyKind::Infer(_)
        );
        if numeric && self.var_kind(t) != Some(VarKind::Any) {
            self.unify(var, t);
        }
    }

    /// A string literal: `&string`, or a case of the expected string-literal union.
    fn str_literal(&mut self, text: Symbol, span: Span, ex: Expect) -> hir::Expr {
        let union = ex.ty().and_then(|t| {
            let t = self.shallow(t);
            let t = match self.sema.tcx.kind(t) {
                TyKind::Nullable(inner) => inner,
                _ => t,
            };
            self.str_union_of(t).map(|adt| (adt, self.shallow(t)))
        });
        if let Some((adt, union_ty)) = union {
            return self.union_value(text, span, adt, union_ty);
        }
        let id = self.sema.tcx.intern_str(text.as_str());
        let str_ty = self.sema.tcx.common().str;
        self.mk_expr(str_ty, span, ExprKind::Const(ConstValue::Str(id)))
    }

    /// The case of string-literal union `adt` whose text is `text`; EN0401 when none
    /// is (S:592).
    pub(crate) fn union_value(
        &mut self,
        text: Symbol,
        span: Span,
        adt: hir::AdtId,
        union_ty: Ty,
    ) -> hir::Expr {
        match self.union_case(adt, text) {
            Some(variant) => {
                let args = match self.sema.tcx.kind(union_ty) {
                    TyKind::Adt(_, args) => args,
                    _ => self.sema.tcx.empty_list(),
                };
                self.mk_expr(
                    union_ty,
                    span,
                    ExprKind::VariantLit {
                        adt,
                        variant,
                        args,
                        fields: Vec::new(),
                        eval: Vec::new(),
                    },
                )
            }
            None => {
                self.report_not_in_union(text, span, adt);
                self.error_expr(span)
            }
        }
    }

    /// The case of string-literal union `adt` whose text is `text`.
    pub(crate) fn union_case(&self, adt: hir::AdtId, text: Symbol) -> Option<VariantIdx> {
        let tcx = &*self.sema.tcx;
        let AdtKind::Enum(e) = &tcx.adt(adt).kind else {
            return None;
        };
        e.variants
            .iter()
            .position(|v| match v.value {
                Some(VariantValue::Text(id)) => *tcx.str(id) == *text.as_str(),
                _ => v.name == text,
            })
            .map(|i| VariantIdx(i as u32))
    }

    /// EN0401 `` `"lft"` is not a `Direction` ``, with "did you mean" over the
    /// union's texts (S:592).
    pub(crate) fn report_not_in_union(&mut self, text: Symbol, span: Span, adt: hir::AdtId) {
        let tcx = &*self.sema.tcx;
        let name = tcx.adt(adt).name;
        let texts: Vec<String> = match &tcx.adt(adt).kind {
            AdtKind::Enum(e) => e
                .variants
                .iter()
                .map(|v| match v.value {
                    Some(VariantValue::Text(id)) => tcx.str(id).to_string(),
                    _ => v.name.as_str().to_owned(),
                })
                .collect(),
            _ => Vec::new(),
        };
        let quoted = format!("{:?}", text.as_str());
        let mut diag = Diagnostic::new(
            Code::EN0401,
            format!(
                "`{quoted}` is not {} `{name}`",
                crate::classes::sig::article(&name.to_string())
            ),
            span,
            format!("not one of `{name}`'s values"),
        );
        let candidates: Vec<&str> = texts.iter().map(String::as_str).collect();
        if let Some(best) = did_you_mean(text.as_str(), &candidates) {
            let best = format!("{best:?}");
            diag = diag.with_help(Help::machine(
                format!("did you mean `{best}`?"),
                vec![Edit::replace(span, best.clone())],
            ));
        }
        self.sema.emit(diag);
    }

    /// EN0411 when the literal does not fit its final type (S:728); otherwise its
    /// constant at that type, for `resolve_body`.
    pub(crate) fn check_literal_fit(
        &mut self,
        expr: ExprId,
        span: Span,
        ty: Ty,
        literal: &Literal,
    ) {
        let root = match self.sema.tcx.kind(ty) {
            TyKind::Infer(v) => Some(self.infer.root(v)),
            _ => None,
        };
        let ty = self.resolve(ty);
        let tcx = &*self.sema.tcx;
        let ptr_bits = u32::from(tcx.target().layout.ptr_bytes) * 8;
        let value = match (tcx.kind(ty), literal) {
            (TyKind::Int(int), Literal::Int { value, negative }) => {
                int_bits(int, ptr_bits, *value, *negative).map(|bits| ConstValue::Int(bits, ty))
            }
            (TyKind::Float(float), Literal::Int { value, negative }) => {
                int_float_bits(float, *value, *negative).map(|bits| ConstValue::Float(bits, ty))
            }
            (TyKind::Float(float), Literal::Float(text)) => {
                parse_float(float, text.as_str()).map(|bits| ConstValue::Float(bits, ty))
            }
            _ => return,
        };
        match value {
            Some(value) => {
                self.literal_values.insert(expr, value);
            }
            None => {
                let defaulted = root.is_some_and(|r| self.infer.defaulted.contains(&r));
                self.report_misfit(span, ty, literal, defaulted, root);
            }
        }
    }

    /// EN0411 `` `3_000_000_000` doesn't fit `int` ``, with the `: i64` fix-it on the
    /// local the literal typed when its type came from the `int` default (S:728).
    fn report_misfit(
        &mut self,
        span: Span,
        ty: Ty,
        literal: &Literal,
        defaulted: bool,
        root: Option<hir::InferVar>,
    ) {
        let text = self.snippet(span);
        let shown = self.sema.tcx.ty_string(ty);
        let tcx = &*self.sema.tcx;
        let ptr_bits = u32::from(tcx.target().layout.ptr_bytes) * 8;
        let label = match tcx.kind(ty) {
            TyKind::Int(int) => {
                let (min, max) = int_range(int, ptr_bits);
                format!("`{shown}` holds {min} to {max}")
            }
            _ => format!("this is out of `{shown}`'s range"),
        };
        let mut diag = Diagnostic::new(
            Code::EN0411,
            format!("`{text}` doesn't fit `{shown}`"),
            span,
            label,
        );
        if defaulted
            && let Literal::Int { value, negative } = literal
            && let Some(root) = root
        {
            let wider = [IntTy::I64, IntTy::U64]
                .into_iter()
                .find(|&int| int_bits(int, ptr_bits, *value, *negative).is_some());
            let local = self
                .infer
                .locals
                .iter()
                .find(|(v, _)| self.infer.root(*v) == root)
                .map(|&(_, name)| name);
            if let (Some(wider), Some(name)) = (wider, local) {
                let wider = wider.name();
                diag = diag.with_help(Help::machine(
                    format!("give it a wider type: `: {wider}`"),
                    vec![Edit::insert(name.hi, format!(": {wider}"))],
                ));
            }
        }
        self.sema.emit(diag);
    }

    /// The literal under a `-` written directly before it (S:728): `-5` and `-1.5`.
    pub(crate) fn negative_literal(
        &mut self,
        operand: &ast::Expr,
        span: Span,
        ex: Expect,
    ) -> Option<hir::Expr> {
        match &super::expr::strip_parens(operand).kind {
            ast::ExprKind::Int { value, .. } => Some(self.int_literal(*value, true, span, ex)),
            ast::ExprKind::Float(text) => {
                let text = intern(&format!("-{}", text.as_str()));
                Some(self.float_literal(text, span, ex))
            }
            _ => None,
        }
    }
}

/// The two's-complement bits of `value` (negated when `negative`) at `int`,
/// zero-extended; `None` when it does not fit.
pub(crate) fn int_bits(int: IntTy, ptr_bits: u32, value: u128, negative: bool) -> Option<u128> {
    let bits = int.bits(ptr_bits);
    let mask = if bits == 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    };
    if int.is_signed() {
        let limit = 1u128 << (bits - 1);
        if negative {
            if value > limit {
                return None;
            }
            Some(value.wrapping_neg() & mask)
        } else if value >= limit {
            None
        } else {
            Some(value)
        }
    } else if negative {
        (value == 0).then_some(0)
    } else if value > mask {
        None
    } else {
        Some(value)
    }
}

/// The smallest and largest values of `int`, printed.
fn int_range(int: IntTy, ptr_bits: u32) -> (String, String) {
    let bits = int.bits(ptr_bits);
    if int.is_signed() {
        let max = (1u128 << (bits - 1)) - 1;
        (format!("-{}", max + 1), max.to_string())
    } else {
        ("0".to_owned(), ((1u128 << bits) - 1).to_string())
    }
}

/// The integer `value` (negated when `negative`) rounded once to `float`, to
/// nearest, as the bits a `ConstValue::Float` keeps: straight from the integer, so
/// an `f32` is never rounded through an `f64` first (S:728). `None` when it rounds
/// to infinity, as a float literal that does.
fn int_float_bits(float: FloatTy, value: u128, negative: bool) -> Option<u64> {
    match float {
        FloatTy::F32 => {
            let x = value as f32;
            let x = if negative { -x } else { x };
            x.is_finite().then(|| u64::from(x.to_bits()))
        }
        FloatTy::F64 => {
            let x = value as f64;
            let x = if negative { -x } else { x };
            x.is_finite().then(|| x.to_bits())
        }
    }
}

/// `text` parsed once at `float`'s width, correctly rounded; `None` when it rounds
/// to infinity.
fn parse_float(float: FloatTy, text: &str) -> Option<u64> {
    let clean: String = text.chars().filter(|&c| c != '_').collect();
    match float {
        FloatTy::F32 => {
            let x: f32 = clean.parse().ok()?;
            x.is_finite().then(|| u64::from(x.to_bits()))
        }
        FloatTy::F64 => {
            let x: f64 = clean.parse().ok()?;
            x.is_finite().then(|| x.to_bits())
        }
    }
}
