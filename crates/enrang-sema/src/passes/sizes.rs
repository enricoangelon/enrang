//! Phase 4's size check at M2 (plan d.17; SPEC 11 S:1628; owner 4F): EN0435.
//!
//! No type or static may exceed the target's `isize.MAX` bytes, and a `T[N]` may not
//! have `N` above `isize.MAX` whatever `T` is (S:1628). Every concrete type written
//! in a user declaration is laid out, with each concrete part of it: a static's or
//! constant's type, reported at its name; a field's, at the field; a parameter's, at
//! the parameter; a result's, at the function's name (**choice**: the HIR keeps no
//! span of a written type, and this pass sees no AST); and a non-generic class or
//! enum as a whole, at its name, when it is too large itself rather than through a
//! field. A class or enum written inside a type is checked where it is declared,
//! never again at each use, and a type that mentions a type parameter, a generic
//! class's instance and a generic body are mono's (M4).
//!
//! A frame is counted as its body's locals, each at the next offset aligned for it,
//! in declaration order, parameters, `this`, hidden arguments and an arrow's own
//! locals left out (they live in the caller's frame, in registers or in the arrow's
//! frame, which is counted the same way on its own): one that takes a frame past
//! `2^31 - 1` bytes on any target
//! (`enrang_layout::FRAME_MAX`) is EN0435 at that local, as is a local whose type is
//! too large (**choice**: WD-4's exact frame rows need codegen's frame layout and
//! wait for M5, plan doc gap G16), and so is a local whose type holds a generic
//! class's instance that is too large, which no declaration check lays out
//! (`A<A<u64>>` on `i386`). A local whose layout waits for contracts (a
//! `&string`, a borrowing class) counts for nothing here.
//!
//! Each declaration and each body reports once; the rest of the program is checked
//! all the same. Only user modules are checked.

use enrang_base::Span;
use enrang_diag::{Code, DiagCtx, Diagnostic};
use enrang_hir::{AdtKind, Body, BodyOwner, CheckedProgram, DefKind, LocalKind, Tcx, Ty, TyKind};
use enrang_layout::{FRAME_MAX, Frame, LayoutError, layout_of};

pub(crate) fn check(p: &CheckedProgram, tcx: &Tcx, dcx: &mut DiagCtx) {
    for (def, data) in tcx.defs() {
        if tcx.module(data.module).library {
            continue;
        }
        if matches!(data.kind, DefKind::Static | DefKind::Const)
            && let Some(ty) = tcx.item_ty(def)
        {
            declared(tcx, dcx, ty, data.name_span);
        }
        if let Some(sig) = tcx.sig_opt(def) {
            for param in &sig.params {
                let span = if param.span.is_dummy() {
                    data.name_span
                } else {
                    param.span
                };
                declared(tcx, dcx, param.ty, span);
            }
            declared(tcx, dcx, sig.ret, data.name_span);
        }
    }
    for (adt, def) in tcx.adts() {
        if tcx.module(tcx.def(def.def).module).library {
            continue;
        }
        let fields: Vec<_> = match &def.kind {
            AdtKind::Class(class) => class
                .fields
                .iter()
                .filter(|f| f.declared_in == adt)
                .collect(),
            AdtKind::Enum(e) => e.variants.iter().flat_map(|v| &v.fields).collect(),
            AdtKind::Interface(_) => continue,
        };
        for field in fields {
            declared(tcx, dcx, field.ty, field.span);
        }
        if tcx.all_params(def.generics).is_empty() {
            let ty = tcx.adt_identity(adt);
            if whole_too_large(tcx, ty) {
                dcx.emit(too_large_diag(tcx, ty, tcx.def(def.def).name_span));
            }
        }
    }
    for body in p.bodies.values().chain(&p.statements) {
        frame(tcx, dcx, body);
    }
}

/// EN0435 for the first part of `ty` that is too large, at `span`.
fn declared(tcx: &Tcx, dcx: &mut DiagCtx, ty: Ty, span: Span) {
    if let Some(large) = too_large(tcx, ty) {
        dcx.emit(too_large_diag(tcx, large, span));
    }
}

/// The first part of `ty`, outermost first, that is too large in itself: never a
/// class or enum, which is checked where it is declared, nor what such a type holds,
/// nor a part that mentions a type parameter.
fn too_large(tcx: &Tcx, ty: Ty) -> Option<Ty> {
    let mut parts = Vec::new();
    tcx.any_ty(ty, &mut |_, t| {
        parts.push(t);
        false
    });
    parts.iter().copied().find_map(|t| {
        if matches!(tcx.kind(t), TyKind::Adt(..))
            || tcx.has_params(t)
            || tcx.has_infer(t)
            || tcx.references_error(t)
        {
            return None;
        }
        match layout_of(tcx, t) {
            Err(LayoutError::TooLarge { ty: found }) if parts.contains(&found) => Some(found),
            _ => None,
        }
    })
}

/// Whether the non-generic class or enum `ty` is too large as a whole, its fields
/// each fitting.
fn whole_too_large(tcx: &Tcx, ty: Ty) -> bool {
    matches!(layout_of(tcx, ty), Err(LayoutError::TooLarge { ty: found }) if found == ty)
}

/// EN0435 for `large` at `span` (plan e's head).
fn too_large_diag(tcx: &Tcx, large: Ty, span: Span) -> Diagnostic {
    let target = tcx.target();
    let max = target.layout.isize_max();
    let label = match tcx.kind(large) {
        TyKind::Fixed(_, n) if n > max => {
            format!("it has {n} elements, more than `isize.MAX` ({max})")
        }
        _ => format!("it takes more than `isize.MAX` bytes ({max})"),
    };
    Diagnostic::new(
        Code::EN0435,
        format!(
            "`{}` is too large for `{}`",
            tcx.ty_string(large),
            target.name
        ),
        span,
        label,
    )
}

/// The frame of a non-generic body: EN0435 at the local whose type is too large or
/// that takes the frame past `FRAME_MAX`.
fn frame(tcx: &Tcx, dcx: &mut DiagCtx, body: &Body) {
    if let BodyOwner::Fn(def) = body.owner
        && let Some(sig) = tcx.sig_opt(def)
        && !tcx.all_params(sig.generics).is_empty()
    {
        return;
    }
    // Each local belongs to the frame of the innermost arrow whose body holds it,
    // else to the body's own (an arrow's locals live in the arrow's frame).
    let spans: Vec<enrang_base::Span> = body.arrows.iter().map(|a| a.span).collect();
    let owner_of = |at: enrang_base::Span| -> Option<usize> {
        spans
            .iter()
            .enumerate()
            .filter(|(_, s)| !at.is_dummy() && s.lo <= at.lo && at.hi <= s.hi)
            .min_by_key(|(_, s)| s.hi.0 - s.lo.0)
            .map(|(i, _)| i)
    };
    let mut frames: Vec<Option<usize>> = vec![None];
    frames.extend((0..spans.len()).map(Some));
    for which in frames {
        if !one_frame(tcx, dcx, body, which, &owner_of) {
            return;
        }
    }
}

/// The frame `which` of `body` (`None` its own, `Some(i)` its `i`-th arrow's);
/// `false` once an EN0435 is reported.
fn one_frame(
    tcx: &Tcx,
    dcx: &mut DiagCtx,
    body: &Body,
    which: Option<usize>,
    owner_of: &dyn Fn(enrang_base::Span) -> Option<usize>,
) -> bool {
    let mut frame = Frame::new();
    for local in body.locals.iter() {
        if matches!(
            local.kind,
            LocalKind::This | LocalKind::Param(_) | LocalKind::Hidden(_) | LocalKind::Arrow(_)
        ) || tcx.has_params(local.ty)
            || owner_of(local.span) != which
        {
            continue;
        }
        let span = if local.span.is_dummy() {
            body.span
        } else {
            local.span
        };
        if let Some(large) = too_large(tcx, local.ty) {
            dcx.emit(too_large_diag(tcx, large, span));
            return false;
        }
        let layout = match layout_of(tcx, local.ty) {
            Ok(layout) => layout,
            // A generic class's instance is laid out first here, since its
            // declaration is mono's: one too large in itself, as `A<A<u64>>` with
            // `T[65536]` fields is on `i386`, is EN0435 at the local, naming the
            // part that is too large when the local's type writes it. A type with
            // no instance in it was reported where its class or enum is declared.
            Err(LayoutError::TooLarge { ty: found }) if has_instance(tcx, local.ty) => {
                let mut parts = Vec::new();
                tcx.any_ty(local.ty, &mut |_, t| {
                    parts.push(t);
                    false
                });
                let shown = if parts.contains(&found) {
                    found
                } else {
                    local.ty
                };
                dcx.emit(too_large_diag(tcx, shown, span));
                return false;
            }
            Err(_) => continue,
        };
        if frame.push(&layout).is_none() {
            let name = local
                .name
                .map_or_else(|| "this binding".to_owned(), |n| format!("`{n}`"));
            let owner = match which {
                None => owner_name(tcx, body.owner),
                Some(_) => format!("an arrow in {}", owner_name(tcx, body.owner)),
            };
            dcx.emit(Diagnostic::new(
                Code::EN0435,
                format!(
                    "the stack frame of {owner} is too large for `{}`",
                    tcx.target().name
                ),
                span,
                format!("{name} takes it past {FRAME_MAX} bytes"),
            ));
            return false;
        }
    }
    true
}

/// Whether `ty` holds an instance of a generic class or enum, whose layout no
/// declaration check sees (mono's at M4).
fn has_instance(tcx: &Tcx, ty: Ty) -> bool {
    tcx.any_ty(
        ty,
        &mut |tcx, t| matches!(tcx.kind(t), TyKind::Adt(_, args) if !tcx.list(args).is_empty()),
    )
}

/// How a message names the code a body belongs to.
fn owner_name(tcx: &Tcx, owner: BodyOwner) -> String {
    match owner {
        BodyOwner::Statements(_) => "the top-level statements".to_owned(),
        BodyOwner::Test(_) => "this test".to_owned(),
        BodyOwner::Fn(def) | BodyOwner::Const(def) => match tcx.def(def).name() {
            Some(name) => format!("`{name}`"),
            None => "this body".to_owned(),
        },
    }
}
