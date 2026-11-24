//! `extend` blocks (SPEC 3.1 "Library-only forms"): the pattern type each extends,
//! with the block's own parameters, recorded in `Tcx` for member lookup
//! (`Tcx::member` reads the blocks of the looking module's import closure, A:886).
//! The members' signatures are `sigs.rs`'s.
//!
//! `extend` in user code is EN0806, with the help `make it a class` (S:600); in the
//! library, a pattern that is an anonymous object type or a tuple, written out or
//! through an alias, is EN0439 (S:350). Neither block is recorded.

use enrang_diag::{Code, Diagnostic, Help};
use enrang_hir::{ExtendDef, TyKind};

use crate::cx::Sema;
use crate::lower::types::lower_ty;
use crate::lower::{ItemAst, ItemAstKind};

pub(crate) fn lower(sema: &mut Sema, item: &ItemAst) {
    let ItemAstKind::Extend(x, members) = &item.kind else {
        return;
    };
    let at = sema.decls.scopes[&item.def];
    let ty = lower_ty(sema, at, &x.ty);
    let library = sema.tcx.module(item.module).library;
    if !library {
        let span = enrang_base::Span {
            lo: sema.tcx.def(item.def).span.lo,
            hi: x.ty.span.hi,
        };
        sema.emit(
            Diagnostic::new(
                Code::EN0806,
                "`extend` is a library-only form",
                span,
                "only `core`, `alloc` and `os` may extend a type",
            )
            .with_help(Help::text("make it a class")),
        );
        return;
    }
    if matches!(sema.tcx.kind(ty), TyKind::Object(_) | TyKind::Tuple(_)) {
        sema.err(
            Code::EN0439,
            "an anonymous object type or a tuple can't have methods",
            x.ty.span,
            "no type of its own to extend",
        );
        return;
    }
    let generics = at.generics.expect("a header defined the generics");
    sema.tcx.define_extend(ExtendDef {
        def: item.def,
        module: item.module,
        generics,
        ty,
        members: members.clone(),
    });
}
