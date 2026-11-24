//! `for...of` (plan d.10; SPEC 5.6; A:429-438, A:902-910; owner 4B): `check_for_of`
//! types the source and classifies it by ARCHITECTURE 2.4's rules 1-6 into
//! `ForSource` (`Range`, `Path`, `Once` in `Ref` or `Owned` mode); a source that is
//! not an array, a fixed array or a view after one `&` is EN1015, as is `for...in`.
//!
//! The order is ARCHITECTURE 4's: (1) the source is typed under the facts in force;
//! (2) classified, the first rule that fits winning: a range is `Range`; a leading
//! `&` of a path is `Path` over that path, of any other place or of an rvalue `Once`
//! in `Ref` mode; a path of reference type is `Path` over its `Deref`; a path of an
//! owned array type, or any owned value, is `Once` in `Owned` mode, which moves a
//! path (S:742); and a value of reference type that is no path is `Once` in `Ref`
//! mode (rule 5, which names rvalues, read to cover a static or an element of
//! reference type too: plan choice); (3) the body alone is prescanned, so the source
//! has used its facts already; (4) its kills spare the source facts, those of each
//! `NarrowedPayload` in a `Path`'s place, which the loop holds (phase 3 rejects a
//! change of them, EN0706, EN0709); (5) the body is checked, each `break` and
//! `continue` of this loop keeping its state, a `break outer` counting for `outer`;
//! (6) the source facts are not checked again at the back edges; (7) the state after
//! the loop is the head's, joined with every `break` of the loop.
//!
//! The binding is `&F` over a `Path` or a `Ref` source (the element's own reference
//! when `F` is one, O7), `F` over an `Owned` one, and the bounds' integer type over
//! a range, whose bounds are one integer type (EN0401 when they differ, EN0403 when
//! they are no integers, plan choice). An owned `T[N]` is copied element by element,
//! so a non-Copy `T` is EN1015 with a help naming `T[]` (S:1009); a `Box<T[]>` is
//! EN1015 with a `&*b` help, a string and any user type EN1015 with SPEC 16's helps,
//! and `for...in` EN1015 at `in`, each with SPEC 16's message head and a `= note:`
//! giving the reason (plan choice).

use std::collections::BTreeSet;

use enrang_base::Span;
use enrang_diag::{Code, Diagnostic, Edit, Help};
use enrang_hir::{
    self as hir, BindingMode, ExprKind, FactId, ForSource, Pat, StmtKind, Ty, TyKind, is_path_place,
};
use enrang_syntax::ast;

use crate::typeck::infer::VarKind;
use crate::typeck::narrow::Prescan;
use crate::typeck::pattern::PatCx;
use crate::typeck::{Expect, FnCtxt, NumNeed};

/// Why a source is EN1015.
enum Unsupported {
    /// `Box<T[]>`: borrow the array inside.
    Boxed,
    /// A string.
    Text,
    /// An owned `T[N]` of a non-Copy `T`.
    FixedMove(Ty),
    /// A nullable whose payload is a source: narrow it first.
    Nullable,
    /// Anything else, a user type above all: expose an array, or `get(i)` and
    /// `length()`.
    Other,
    /// An integer: count up to it with a range.
    Value,
}

impl FnCtxt<'_, '_> {
    /// A `for...of` loop (A:902-910).
    pub(crate) fn check_for_of(&mut self, s: &ast::ForOfStmt) -> StmtKind {
        // (1), (2)
        let (source, binding) = match (&s.source, s.in_keyword) {
            (ast::ForOfSource::Range(lo, hi), _) => self.range_source(lo, hi),
            (ast::ForOfSource::Expr(e), None) => self.expr_source(e),
            (ast::ForOfSource::Expr(e), Some(span)) => {
                self.report_for_in(span);
                let value = self.check_expr(e, Expect::None);
                (Self::once(value, BindingMode::Owned), self.error_ty())
            }
        };
        // (3), (4)
        let keep = match &source {
            ForSource::Path { place } => source_facts(place),
            _ => BTreeSet::new(),
        };
        self.prescan_kill_except(Prescan::ForOf(&s.binding, &s.body), &keep);
        let head = self.flow.clone();
        // (5)
        let id = self.enter_loop();
        self.scopes.push();
        let cx = PatCx {
            mutable: s.mutable,
            for_loop: true,
        };
        let pat = match &s.binding {
            ast::Binding::Name(name) => Pat::Bind(self.declare(
                Some(name.name),
                binding,
                s.mutable,
                hir::LocalKind::ForBinding,
                name.span,
            )),
            pattern => self.bind_pattern(pattern, binding, cx),
        };
        let body = self.check_block(&s.body);
        self.scopes.pop();
        self.exit_loop();
        // (6), (7)
        self.loop_exit(id, Some(head));
        StmtKind::ForOf {
            id,
            pat,
            source,
            body,
        }
    }

    /// `a..b`: both bounds of one integer type, which the binding has.
    fn range_source(&mut self, lo: &ast::Expr, hi: &ast::Expr) -> (ForSource, Ty) {
        let lo = self.check_expr(lo, Expect::None);
        let hi = self.check_expr(hi, Expect::Has(lo.ty));
        let error = self.error_ty();
        if self.is_error(lo.ty) || self.is_error(hi.ty) {
            return (ForSource::Range { lo, hi }, error);
        }
        if !self.unify(lo.ty, hi.ty) {
            let (sl, sh) = (self.ty_str(lo.ty), self.ty_str(hi.ty));
            self.sema.emit(Diagnostic::new(
                Code::EN0401,
                format!("mismatched types: expected `{sl}`, found `{sh}`"),
                hi.span,
                format!("this is `{sh}`"),
            ));
            return (ForSource::Range { lo, hi }, error);
        }
        let ty = self.shallow(lo.ty);
        match self.sema.tcx.kind(ty) {
            TyKind::Int(_) => {}
            TyKind::Infer(_) if self.var_kind(ty) == Some(VarKind::Int) => {
                self.defer_num_use(lo.span, ty, NumNeed::Integer(".."));
            }
            TyKind::Infer(_) if self.var_kind(ty) == Some(VarKind::Any) => {
                // Still unknown: it must become an integer.
                let int = self.new_var(VarKind::Int, lo.span, "the bounds of this range");
                self.unify(ty, int);
                self.defer_num_use(lo.span, int, NumNeed::Integer(".."));
            }
            _ => {
                let shown = self.ty_str(ty);
                self.sema.emit(Diagnostic::new(
                    Code::EN0403,
                    format!("`..` needs integers, found `{shown}`"),
                    lo.span,
                    format!("this is `{shown}`"),
                ));
                return (ForSource::Range { lo, hi }, error);
            }
        }
        (ForSource::Range { lo, hi }, ty)
    }

    /// A source expression, typed under the facts in force and classified (A:429).
    fn expr_source(&mut self, e: &ast::Expr) -> (ForSource, Ty) {
        let value = self.check_expr(e, Expect::None);
        let error = self.error_ty();
        if self.is_error(value.ty) {
            let source = ForSource::Once {
                value,
                mode: BindingMode::Owned,
            };
            return (source, error);
        }
        let t = self.shallow(value.ty);
        // Rule 2: a leading `&`.
        if let ExprKind::Borrow(inner) = &value.kind
            && value.adjust.is_empty()
        {
            let pointee = self.shallow(inner.ty);
            let Some(elem) = self.element_of(pointee) else {
                self.report_source(&value, pointee);
                return (Self::once(value, BindingMode::Ref), error);
            };
            let binding = self.element_ref(elem);
            if self.is_source_path(inner) {
                let ExprKind::Borrow(inner) = value.kind else {
                    unreachable!("matched above");
                };
                return (ForSource::Path { place: *inner }, binding);
            }
            return (Self::once(value, BindingMode::Ref), binding);
        }
        if let TyKind::Ref(pointee) = self.sema.tcx.kind(t) {
            let pointee = self.shallow(pointee);
            let Some(elem) = self.element_of(pointee) else {
                self.report_source(&value, pointee);
                return (Self::once(value, BindingMode::Ref), error);
            };
            let binding = self.element_ref(elem);
            // Rule 3: a path of reference type borrows through it.
            if value.adjust.is_empty() && self.is_source_path(&value) {
                let span = value.span;
                let place = self.mk_expr(pointee, span, ExprKind::Deref(Box::new(value)));
                return (ForSource::Path { place }, binding);
            }
            // Rule 5: a reference value.
            return (Self::once(value, BindingMode::Ref), binding);
        }
        // Rules 4 and 6: the loop takes the value.
        let Some(elem) = self.element_of(t) else {
            self.report_source(&value, t);
            return (Self::once(value, BindingMode::Owned), error);
        };
        if let TyKind::Fixed(..) = self.sema.tcx.kind(t) {
            let resolved = self.resolve(elem);
            let tcx = &*self.sema.tcx;
            if !tcx.has_infer(resolved) && !tcx.is_copy(resolved, &self.env) {
                self.report_unsupported(&value, Unsupported::FixedMove(elem));
                return (Self::once(value, BindingMode::Owned), error);
            }
        }
        self.kill_move(&value);
        (Self::once(value, BindingMode::Owned), elem)
    }

    /// Whether `e` is a path in 5.6's sense: a narrowing path (4.8), so no index and
    /// no tuple part (S:739), which `is_path_place` also holds of.
    fn is_source_path(&self, e: &hir::Expr) -> bool {
        is_path_place(self.sema.tcx, e) && self.place_path(e).is_some()
    }

    fn once(value: hir::Expr, mode: BindingMode) -> ForSource {
        ForSource::Once { value, mode }
    }

    /// The element type of an array, a fixed array or a view.
    fn element_of(&self, t: Ty) -> Option<Ty> {
        match self.sema.tcx.kind(self.shallow(t)) {
            TyKind::Array(elem) | TyKind::Fixed(elem, _) | TyKind::Slice(elem) => Some(elem),
            _ => None,
        }
    }

    /// The binding over a borrowed source of elements `elem`: `&elem`, or the
    /// element itself when it is a reference (O7).
    fn element_ref(&self, elem: Ty) -> Ty {
        match self.sema.tcx.kind(self.shallow(elem)) {
            TyKind::Ref(_) => elem,
            _ => self.sema.tcx.mk_ref(elem),
        }
    }

    /// EN1015 for a source whose type `t`, one `&` peeled, is no array, fixed array
    /// or view.
    fn report_source(&mut self, value: &hir::Expr, t: Ty) {
        let tcx = &*self.sema.tcx;
        let why = match tcx.kind(self.shallow(t)) {
            TyKind::Boxed(inner) if self.element_of(inner).is_some() => Unsupported::Boxed,
            TyKind::Str => Unsupported::Text,
            TyKind::Nullable(inner) => {
                let inner = self.shallow(inner);
                let inner = match tcx.kind(inner) {
                    TyKind::Ref(i) => self.shallow(i),
                    _ => inner,
                };
                match self.element_of(inner) {
                    Some(_) => Unsupported::Nullable,
                    None => Unsupported::Other,
                }
            }
            TyKind::Int(_) => Unsupported::Value,
            _ if self.var_kind(self.shallow(t)) == Some(VarKind::Int) => Unsupported::Value,
            _ => Unsupported::Other,
        };
        self.report_unsupported(value, why);
    }

    /// EN1015 at the source `value` (SPEC 16).
    fn report_unsupported(&mut self, value: &hir::Expr, why: Unsupported) {
        // The label shows the source as written, its `&` included.
        let shown = self.ty_str(value.ty);
        let text = self.snippet(value.span);
        // The operand of a leading `&`, which `&*b` replaces, and which a null test
        // names: `if (tags != null)` narrows `tags`, and `&tags != null` would not.
        let boxed = match &value.kind {
            ExprKind::Borrow(inner) => self.snippet(inner.span),
            _ => text.clone(),
        };
        let (note, help) = match why {
            Unsupported::Boxed => (
                "a loop goes over an array, a fixed array, a view or a range, through at most one `&`, and a `Box` is none of them".to_owned(),
                Help::suggest(
                    format!("loop over the array in the box: `&*{boxed}`"),
                    vec![Edit::replace(value.span, format!("&*{boxed}"))],
                ),
            ),
            Unsupported::Text => (
                "a string is UTF-8 bytes, and a loop over it would have to choose bytes or code points".to_owned(),
                Help::text(format!(
                    "loop over its indexes and read each byte with `{boxed}.byteAt(i)`"
                )),
            ),
            Unsupported::FixedMove(elem) => {
                let elem = self.ty_str(elem);
                (
                    format!("a loop takes a fixed array by copying each element, and `{elem}` is not Copy"),
                    Help::text(format!(
                        "use {} `{elem}[]` for owned non-Copy elements, or borrow it: `&{text}`",
                        crate::classes::sig::article(&elem)
                    )),
                )
            }
            Unsupported::Nullable => (
                format!("`{boxed}` may be `null`, and a loop needs the array itself"),
                Help::text(format!("narrow it first: `if ({boxed} != null) {{ ... }}`")),
            ),
            Unsupported::Other => (
                "a loop goes over an array, a fixed array, a view or a range; iterators of other types come later".to_owned(),
                Help::text("Expose an array, or a `get(i)` and `length()`"),
            ),
            Unsupported::Value => (
                "a loop goes over an array, a fixed array, a view or a range".to_owned(),
                Help::text(format!(
                    "to count up to it, loop over a range: `for (const i of 0..{text})`"
                )),
            ),
        };
        self.sema.emit(
            Diagnostic::new(
                Code::EN1015,
                "this `for...of` source is not supported yet",
                value.span,
                format!("this is `{shown}`"),
            )
            .note(note)
            .with_help(help),
        );
    }

    /// EN1015 at the `in` of `for...in` (S:3466).
    fn report_for_in(&mut self, span: Span) {
        self.sema.emit(
            Diagnostic::new(
                Code::EN1015,
                "this `for...of` source is not supported yet",
                span,
                "`for...in` walks an object's keys",
            )
            .note("an Enrang object has no keys to walk; `for...of` goes over the elements of an array")
            .with_help(Help::suggest(
                "to loop over an array's elements, write `of`",
                vec![Edit::replace(span, "of")],
            )),
        );
    }
}

/// The facts a `Path` source was typed through: those of each `NarrowedPayload` in
/// its place (A:904).
fn source_facts(place: &hir::Expr) -> BTreeSet<FactId> {
    let mut out = BTreeSet::new();
    let mut at = place;
    loop {
        match &at.kind {
            ExprKind::NarrowedPayload(inner, _, fact) => {
                out.insert(*fact);
                at = inner;
            }
            ExprKind::Field(inner, _) | ExprKind::Deref(inner) => at = inner,
            _ => return out,
        }
    }
}
