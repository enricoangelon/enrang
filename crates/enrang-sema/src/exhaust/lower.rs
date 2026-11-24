//! A `hir::Match` read as one column (plan d.13): the subject's type as a
//! [`Space`], each arm value as a [`Pat`].
//!
//! `match` only looks at its subject (SPEC 6), so references and boxes around it
//! are looked through, at each level of `| null` too: `s: &Shape` matches as a
//! `Shape` (G12). Every arm value but `null` and `default` wraps in `Present`
//! once per level of `| null`, and `null` matches the outermost level (S:1134).
//! A subject that is the constant `true` or `false`, as in `match (true)`, holds
//! that one value.

use enrang_hir::{
    AdtId, Arm, ArmValue, ConstValue, Expr, ExprKind, FloatTy, Tcx, Ty, TyKind, VariantValue,
};

use super::matrix::{Pat, Space, float_key};
use super::{ArmPat, Guard};

/// What a subject's type is at its innermost level, under every `| null`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Base {
    /// An enum, `Result` or a string-literal union.
    Enum(AdtId),
    Bool,
    /// The subject is this constant: its one value is case 0 of `Enum(1)`.
    ConstBool(bool),
    Int,
    Float,
    Str,
    Opaque,
}

/// A subject's column.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Column {
    pub space: Space,
    /// The type at each level, outermost first, references and boxes looked
    /// through: one entry per `| null`, then the innermost type.
    pub levels: Vec<Ty>,
    pub base: Base,
}

impl Column {
    /// How many levels of `| null` the subject has.
    pub(crate) fn depth(&self) -> usize {
        self.levels.len() - 1
    }
}

/// `t` with every reference and box around it looked through.
fn peel(tcx: &Tcx, mut t: Ty) -> Ty {
    loop {
        match tcx.kind(t) {
            TyKind::Ref(inner) | TyKind::Boxed(inner) => t = inner,
            _ => return t,
        }
    }
}

/// The column of `subject`, or `None` when its type was rejected (`Error`), is
/// `never`, or is still being inferred.
pub(crate) fn column(tcx: &Tcx, subject: &Expr) -> Option<Column> {
    if tcx.references_error(subject.ty) || tcx.has_infer(subject.ty) {
        return None;
    }
    let mut levels = Vec::new();
    let mut t = peel(tcx, subject.ty);
    loop {
        levels.push(t);
        match tcx.kind(t) {
            TyKind::Nullable(inner) => t = peel(tcx, inner),
            _ => break,
        }
    }
    let constant = match &subject.kind {
        ExprKind::Const(ConstValue::Bool(b)) if levels.len() == 1 => Some(*b),
        _ => None,
    };
    let (base, mut space) = match tcx.kind(t) {
        TyKind::Never | TyKind::Error | TyKind::Infer(_) => return None,
        TyKind::Bool => match constant {
            Some(b) => (Base::ConstBool(b), Space::Enum(1)),
            None => (Base::Bool, Space::Bool),
        },
        TyKind::Int(_) => (Base::Int, Space::Int),
        TyKind::Float(_) => (Base::Float, Space::Float),
        TyKind::Str => (Base::Str, Space::Str),
        TyKind::Adt(adt, _) => match tcx.adt(adt).as_enum() {
            Some(e) => (Base::Enum(adt), Space::Enum(e.variants.len() as u32)),
            None => (Base::Opaque, Space::Opaque),
        },
        _ => (Base::Opaque, Space::Opaque),
    };
    for _ in 1..levels.len() {
        space = Space::Nullable(Box::new(space));
    }
    Some(Column {
        space,
        levels,
        base,
    })
}

/// The values of `arm` as patterns of `column`: `default` is one `Wild`, a
/// condition of `match (true)` a `Wild` with its own guard. `None` when a value
/// does not fit the subject's type.
pub(crate) fn arm_pats(tcx: &Tcx, column: &Column, arm: &Arm) -> Option<Vec<ArmPat>> {
    let guard = if arm.guard.is_some() {
        Guard::Arm
    } else {
        Guard::None
    };
    if arm.values.is_empty() {
        return Some(vec![ArmPat {
            pat: Pat::Wild,
            guard,
        }]);
    }
    arm.values
        .iter()
        .map(|value| match value {
            ArmValue::Cond(_) => Some(ArmPat {
                pat: Pat::Wild,
                guard: Guard::Own,
            }),
            ArmValue::Null => (column.depth() > 0).then_some(ArmPat {
                pat: Pat::Null,
                guard,
            }),
            _ => {
                let mut pat = atom(tcx, column.base, value)?;
                for _ in 0..column.depth() {
                    pat = Pat::Present(Box::new(pat));
                }
                Some(ArmPat { pat, guard })
            }
        })
        .collect()
}

/// A value other than `null`, `default` and a condition, at the innermost level.
fn atom(tcx: &Tcx, base: Base, value: &ArmValue) -> Option<Pat> {
    match (base, value) {
        (Base::Enum(adt), ArmValue::Case(v)) => {
            let cases = tcx.adt(adt).as_enum()?.variants.len();
            ((v.0 as usize) < cases).then_some(Pat::Case(v.0))
        }
        (Base::Enum(adt), ArmValue::Const(ConstValue::Str(id))) => {
            let e = tcx.adt(adt).as_enum().filter(|e| e.str_union)?;
            let text = tcx.str(*id);
            e.variants
                .iter()
                .position(|v| match v.value {
                    Some(VariantValue::Text(t)) => tcx.str(t) == text,
                    _ => v.name.as_str() == &*text,
                })
                .map(|i| Pat::Case(i as u32))
        }
        (Base::Bool, ArmValue::Const(ConstValue::Bool(b))) => Some(Pat::Bool(*b)),
        (Base::ConstBool(c), ArmValue::Const(ConstValue::Bool(b))) => {
            Some(if *b == c { Pat::Case(0) } else { Pat::Empty })
        }
        (Base::Int, ArmValue::Const(c)) => {
            let v = c.as_i128(tcx)?;
            Some(Pat::Range(v, v.checked_add(1)?))
        }
        (Base::Int, ArmValue::Range(lo, hi)) => {
            Some(Pat::Range(lo.as_i128(tcx)?, hi.as_i128(tcx)?))
        }
        (Base::Float, ArmValue::Const(ConstValue::Float(bits, ty))) => {
            let value = match tcx.kind(*ty) {
                TyKind::Float(FloatTy::F32) => f64::from(f32::from_bits(*bits as u32)),
                TyKind::Float(FloatTy::F64) => f64::from_bits(*bits),
                _ => return None,
            };
            Some(float_key(value).map_or(Pat::Empty, Pat::Float))
        }
        (Base::Str, ArmValue::Const(ConstValue::Str(id))) => {
            Some(Pat::Str(tcx.str(*id).to_string()))
        }
        _ => None,
    }
}
