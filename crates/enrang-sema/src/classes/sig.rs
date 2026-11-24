//! Signatures compared as the class rules compare them (plan d.16; SPEC 4.3, 4.4,
//! 4.14): a method's parameter and result types seen at an owner's arguments, its
//! own type parameters matched by position, so `show<T>(x: &T)` and `show<U>(x:
//! &U)` have one signature; and the type defaults a field may start at (S:582).
//! Whether a method is compiled once per type is `Tcx::once_per_type`, which the
//! MIR verifier reads too (V16).

use enrang_hir::{AdtId, Bound, DefId, Implicit, ParamId, Receiver, Tcx, Ty, TyKind};

/// A method's signature with its owner's type parameters replaced by an owner's
/// arguments (and an interface's `Self` by the type asked about); its own type
/// parameters stay, to be matched by position.
#[derive(Clone, Debug)]
pub(crate) struct SigView {
    pub def: DefId,
    /// Its own type parameters, written and implicit (D5), in order.
    pub own: Vec<ParamId>,
    pub params: Vec<Ty>,
    pub ret: Ty,
    /// The replacement applied: owner parameters (and `Self`) to arguments.
    from: Vec<ParamId>,
    to: Vec<Ty>,
}

/// `def`'s signature at `owner_args`, with an interface member's `Self` replaced by
/// `self_ty` when given; `None` for what has no signature.
pub(crate) fn view(
    tcx: &Tcx,
    def: DefId,
    owner_args: &[Ty],
    self_ty: Option<Ty>,
) -> Option<SigView> {
    let sig = tcx.sig_opt(def)?;
    let mut from = match tcx.generics(sig.generics).parent {
        Some(parent) => tcx.all_params(parent),
        None => Vec::new(),
    };
    let n = from.len().min(owner_args.len());
    from.truncate(n);
    let mut to = owner_args[..n].to_vec();
    if let Some(self_ty) = self_ty
        && let Some(parent) = tcx.def(def).parent
        && let Some(adt) = tcx.adt_of(parent)
        && let Some(iface) = tcx.adt(adt).as_interface()
    {
        from.push(iface.self_param);
        to.push(self_ty);
    }
    let params = sig
        .params
        .iter()
        .map(|p| tcx.subst(p.ty, &from, &to))
        .collect();
    let ret = tcx.subst(sig.ret, &from, &to);
    Some(SigView {
        def,
        own: tcx.generics(sig.generics).params.clone(),
        params,
        ret,
        from,
        to,
    })
}

/// `b`'s own type parameters as `a`'s, by position.
fn own_as(tcx: &Tcx, a: &SigView, b: &SigView, t: Ty) -> Ty {
    let to: Vec<Ty> = a.own.iter().map(|&p| tcx.mk_param(p)).collect();
    tcx.subst(t, &b.own, &to)
}

/// The same number of own type parameters, each implicit one (D5) standing for the
/// same interface or shape, and equal parameter types: the key an override is
/// matched by and an overload is told apart by (SPEC 4.14). Written own type
/// parameters match by position whatever their bounds, which no call can tell
/// apart.
pub(crate) fn same_params(tcx: &Tcx, a: &SigView, b: &SigView) -> bool {
    a.own.len() == b.own.len()
        && a.params.len() == b.params.len()
        && (0..a.own.len()).all(|i| same_implicit(tcx, a, b, i))
        && a.params
            .iter()
            .zip(&b.params)
            .all(|(&x, &y)| tcx.same_ignoring_rows(x, own_as(tcx, a, b, y)))
}

/// Whether the `i`-th own type parameters of `a` and `b` are both written, or both
/// implicit for the same interface (their bounds) or the same shape.
fn same_implicit(tcx: &Tcx, a: &SigView, b: &SigView, i: usize) -> bool {
    match (tcx.param(a.own[i]).implicit, tcx.param(b.own[i]).implicit) {
        (None, None) | (Some(Implicit::Opaque), Some(Implicit::Opaque)) => true,
        (Some(Implicit::Interface(_)), Some(Implicit::Interface(_))) => {
            same_param_bounds(tcx, a, b, i)
        }
        (Some(Implicit::Shape(x)), Some(Implicit::Shape(y))) => {
            let x = tcx.subst(tcx.intern_ty(TyKind::Object(x)), &a.from, &a.to);
            let y = tcx.subst(tcx.intern_ty(TyKind::Object(y)), &b.from, &b.to);
            tcx.same_ignoring_rows(x, own_as(tcx, a, b, y))
        }
        _ => false,
    }
}

/// Equal result types, own type parameters matched by position.
pub(crate) fn same_ret(tcx: &Tcx, a: &SigView, b: &SigView) -> bool {
    tcx.same_ignoring_rows(a.ret, own_as(tcx, a, b, b.ret))
}

/// Equal bounds on each pair of own type parameters (SPEC 4.4).
pub(crate) fn same_bounds(tcx: &Tcx, a: &SigView, b: &SigView) -> bool {
    a.own.len() == b.own.len() && (0..a.own.len()).all(|i| same_param_bounds(tcx, a, b, i))
}

/// Equal bounds on the `i`-th own type parameters of `a` and `b`, `b`'s own
/// parameters read as `a`'s.
fn same_param_bounds(tcx: &Tcx, a: &SigView, b: &SigView, i: usize) -> bool {
    let bounds = |v: &SigView, p: ParamId, map_own: bool| -> Vec<(bool, AdtId, Vec<Ty>)> {
        tcx.param(p)
            .bounds
            .iter()
            .map(|&id| {
                let bound = tcx.bound(id);
                let args = tcx
                    .list(bound.args())
                    .iter()
                    .map(|&t| {
                        let t = tcx.subst(t, &v.from, &v.to);
                        if map_own { own_as(tcx, a, v, t) } else { t }
                    })
                    .collect();
                (matches!(bound, Bound::Iface { .. }), bound.adt(), args)
            })
            .collect()
    };
    let (x, y) = (bounds(a, a.own[i], false), bounds(b, b.own[i], true));
    x.len() == y.len()
        && x.iter().zip(&y).all(|(l, r)| {
            l.0 == r.0
                && l.1 == r.1
                && l.2.len() == r.2.len()
                && l.2
                    .iter()
                    .zip(&r.2)
                    .all(|(&s, &t)| tcx.same_ignoring_rows(s, t))
        })
}

/// Whether `def` is a `static` method.
pub(crate) fn is_static(tcx: &Tcx, def: DefId) -> bool {
    tcx.sig_opt(def)
        .is_some_and(|s| s.receiver == Some(Receiver::Static))
}

/// Whether a field of type `t` starts at its type's default when nothing sets it
/// (S:582, O3): numbers, `bool`, `string`, arrays, `T | null` and raw pointers;
/// plan choice where SPEC lists nothing: a fixed array, a tuple or an object type
/// when every part has one, and `void`. Classes, enums, `Box`, `Result`,
/// references, type parameters and functions have none.
pub(crate) fn has_type_default(tcx: &Tcx, t: Ty) -> bool {
    match tcx.kind(t) {
        TyKind::Bool
        | TyKind::Int(_)
        | TyKind::Float(_)
        | TyKind::Str
        | TyKind::Array(_)
        | TyKind::Nullable(_)
        | TyKind::Raw(_)
        | TyKind::Void
        | TyKind::Error => true,
        TyKind::Fixed(e, _) => has_type_default(tcx, e),
        TyKind::Tuple(parts) => tcx.list(parts).iter().all(|&p| has_type_default(tcx, p)),
        TyKind::Object(shape) => tcx
            .shape(shape)
            .fields
            .iter()
            .all(|&(_, f)| has_type_default(tcx, f)),
        _ => false,
    }
}

/// `a` or `an` before a backticked type name, by how it is read: `an` before a
/// vowel sound (`an int`, `an i64`, `an Error`, `an f64`), `a` before a `u` read
/// as "you" (`a u8`, `a usize`, `a User`) and before anything else.
pub(crate) fn article(shown: &str) -> &'static str {
    let mut chars = shown.chars();
    match (chars.next(), chars.next()) {
        (Some('a' | 'e' | 'i' | 'o' | 'A' | 'E' | 'I' | 'O'), _) => "an",
        (Some('f'), Some(d)) if d.is_ascii_digit() => "an",
        _ => "a",
    }
}

/// `` a `T` `` or `` an `T` `` for the type shown as `shown`.
pub(crate) fn a_ty(shown: &str) -> String {
    format!("{} `{shown}`", article(shown))
}

/// `m(x: i64): string`, as a note shows a signature.
pub(crate) fn sig_string(tcx: &Tcx, v: &SigView) -> String {
    let name = tcx
        .def(v.def)
        .name()
        .map_or_else(String::new, |n| n.to_string());
    let sig = tcx.sig(v.def);
    // Each type parameter with its bounds (S:615: they are part of the signature).
    let own: Vec<String> = v
        .own
        .iter()
        .filter(|&&p| tcx.param(p).implicit.is_none())
        .map(|&p| {
            let def = tcx.param(p);
            let bounds: Vec<String> = def
                .bounds
                .iter()
                .map(|&b| {
                    let bound = tcx.bound(b);
                    tcx.ty_string(tcx.mk_adt(bound.adt(), &tcx.list(bound.args())))
                })
                .collect();
            match bounds.is_empty() {
                true => def.name.to_string(),
                false => format!("{} extends {}", def.name, bounds.join(" & ")),
            }
        })
        .collect();
    let generics = match own.is_empty() {
        true => String::new(),
        false => format!("<{}>", own.join(", ")),
    };
    let params: Vec<String> = sig
        .params
        .iter()
        .zip(&v.params)
        .map(|(p, &t)| format!("{}: {}", p.name, tcx.ty_string(t)))
        .collect();
    format!(
        "{name}{generics}({}): {}",
        params.join(", "),
        tcx.ty_string(v.ret)
    )
}
