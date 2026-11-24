//! Slots (A:1036; M3 plan d.4; owner 2E): what can hold loans, and how. A slot is
//! every local whose type is ref-carrying, the closure-env and closure-value locals,
//! one phantom `Hold(l)` per `for...of` over a path, and one phantom `Caller(m)` per
//! parameter `m` whose pointee is a borrowing value (never an Own `this`).

use enrang_hir::{LoopId, Mark, Receiver, Tcx, Ty, TyKind};
use enrang_mir::{Body, BodyOwner, Local, LocalKind, LoopSource};

/// A place loans are held in: a ref-carrying local, a `for...of` hold, or the
/// borrowing value behind parameter `m` (`Caller(m)`).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum SlotId {
    Local(Local),
    Hold(LoopId),
    Caller(u32),
}

/// How a slot holds: a reference to a borrowing value keeps `fields` and
/// `rfields`; a borrowing value itself keeps `rfields` and `wfields`, its `fields`
/// being its `held`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum SlotKind {
    Plain,
    PtrBorrowing,
    ValueBorrowing,
}

/// The slots of one body, in `SlotId` order.
#[derive(Clone, Debug, Default)]
pub struct Slots {
    pub list: Vec<(SlotId, SlotKind)>,
}

impl Slots {
    /// Every slot of `b` (A:1036).
    pub fn collect(tcx: &Tcx, b: &Body) -> Slots {
        let mut list = Vec::new();
        for (l, d) in b.locals.iter_enumerated() {
            let closure = closure_ty(tcx, d.ty);
            if closure || d.kind == LocalKind::ClosureEnv || ref_carrying(tcx, d.ty) {
                list.push((SlotId::Local(l), kind_of(tcx, d.ty)));
            }
        }
        for lp in &b.meta.loops {
            if let LoopSource::Path(_) = lp.source {
                list.push((SlotId::Hold(lp.id), SlotKind::Plain));
            }
        }
        let own = own_this(tcx, b);
        for l in b.args() {
            if kind_of(tcx, b.locals[l].ty) == SlotKind::PtrBorrowing && !(own && l.0 == 1) {
                list.push((SlotId::Caller(l.0 - 1), SlotKind::Plain));
            }
        }
        list.sort();
        Slots { list }
    }

    pub fn kind(&self, s: SlotId) -> Option<SlotKind> {
        self.list
            .binary_search_by_key(&s, |(id, _)| *id)
            .ok()
            .map(|i| self.list[i].1)
    }

    pub fn has(&self, s: SlotId) -> bool {
        self.kind(s).is_some()
    }
}

/// `is_slot_type` and not `is_value_type`: a reference, a borrowing class or tuple,
/// or either one nullable; and a reference to `R | null` or `B | null`.
pub(crate) fn ref_carrying(tcx: &Tcx, ty: Ty) -> bool {
    (tcx.is_slot_type(ty) && !tcx.is_value_type(ty))
        || closure_ref(tcx, ty)
        || ref_nullable(tcx, ty)
}

/// A reference to a nullable reference or borrowing value: `&(W | null)` as a
/// parameter or `const r = &w` writes it, and `&(&T | null)` as a form's
/// `[temp-arg]` or `[auto-borrow]` makes it for an `R | null` argument (A:977).
/// What it points at holds loans, so reads through it keep them and stores
/// through it are recorded, as through `&W` (S:849, S:775).
fn ref_nullable(tcx: &Tcx, ty: Ty) -> bool {
    match tcx.kind(ty) {
        TyKind::Ref(t) => match tcx.kind(t) {
            TyKind::Nullable(u) => tcx.is_borrowing(u) || matches!(tcx.kind(u), TyKind::Ref(_)),
            _ => false,
        },
        _ => false,
    }
}

/// A reference to a closure, or to a nullable one, which is how an arrow captures
/// a closure local or parameter (A:971), or a tuple with such a part, as the environment holding it:
/// no type the user writes, but the capture's loan must reach the capturing
/// closure's value, so that capturing `f` holds `f` exclusively for as long as
/// that closure lives (S:974, A:1259).
fn closure_ref(tcx: &Tcx, ty: Ty) -> bool {
    match tcx.kind(ty) {
        TyKind::Ref(t) => closure_ty(tcx, t),
        TyKind::Tuple(parts) => tcx.list(parts).iter().any(|&p| closure_ref(tcx, p)),
        _ => false,
    }
}

/// A closure type, or a nullable one (`handler?: (k: u8) => void`), which is
/// used as exclusively as a closure is once narrowed (A:973).
pub(crate) fn closure_ty(tcx: &Tcx, ty: Ty) -> bool {
    match tcx.kind(ty) {
        TyKind::Closure(_) => true,
        TyKind::Nullable(t) => matches!(tcx.kind(t), TyKind::Closure(_)),
        _ => false,
    }
}

/// A borrowing class or tuple, or a nullable one.
pub(crate) fn bvalue(tcx: &Tcx, ty: Ty) -> bool {
    match tcx.kind(ty) {
        TyKind::Nullable(t) => tcx.is_borrowing(t),
        _ => tcx.is_borrowing(ty),
    }
}

/// What a reference, or a nullable one, points at.
pub(crate) fn pointee(tcx: &Tcx, ty: Ty) -> Option<Ty> {
    match tcx.kind(ty) {
        TyKind::Ref(t) => Some(t),
        TyKind::Nullable(r) => match tcx.kind(r) {
            TyKind::Ref(t) => Some(t),
            _ => None,
        },
        _ => None,
    }
}

pub(crate) fn kind_of(tcx: &Tcx, ty: Ty) -> SlotKind {
    if bvalue(tcx, ty) {
        SlotKind::ValueBorrowing
    } else if pointee(tcx, ty).is_some_and(|p| bvalue(tcx, p)) {
        SlotKind::PtrBorrowing
    } else {
        SlotKind::Plain
    }
}

/// The body is a `move` method, whose `this` (`_1`) is Own.
pub(crate) fn own_this(tcx: &Tcx, b: &Body) -> bool {
    matches!(b.owner, BodyOwner::Fn(d)
        if tcx.sig_opt(d).is_some_and(|s| s.receiver == Some(Receiver::Move)))
}

/// `l` is `this` or a declared parameter not marked `let` (A:1063).
pub(crate) fn fixed_param(tcx: &Tcx, b: &Body, l: Local) -> bool {
    let BodyOwner::Fn(d) = b.owner else {
        return false;
    };
    let Some(sig) = tcx.sig_opt(d) else {
        return false;
    };
    let this = usize::from(tcx.takes_this(d));
    match (l.0 as usize).checked_sub(1 + this) {
        _ if this == 1 && l.0 == 1 => true,
        Some(k) => sig.params.get(k).is_some_and(|p| p.mark != Mark::Let),
        None => false,
    }
}

/// The contract index of an argument local: its position, `this` 0 (A:1038).
pub(crate) fn param_index(b: &Body, l: Local) -> Option<u32> {
    (l.0 >= 1 && l.0 <= b.arg_count).then(|| l.0 - 1)
}
