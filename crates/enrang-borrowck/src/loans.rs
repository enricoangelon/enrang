//! Loans and their keys (A:1013-1036; M3 plan d.4; owner 2E): a loan's path in
//! normal form, the loan table of one body, and the keys `held` tracks.
//!
//! Every loan a statement may make gets its `LoanId` before the dataflow, in (block,
//! index, sub-index) order; whether N4 gives a reborrow, a nullable copy's payload
//! or a part of a held tuple a loan at all is decided by `held` (plan d.5), so ids
//! never depend on write-liveness.

use enrang_base::{IdVec, Idx, Span};
use enrang_hir::{FieldIdx, LoopId, Tcx, Ty, TyKind, VariantIdx};
use enrang_mir::{
    Body, BorrowOrigin, Local, LocalKind, LoopSource, Operand, PlaceTy, Point, Proj, Rvalue,
    StatementKind,
};

use crate::slots::{bvalue, pointee};

/// A loan's path in normal form: it crosses at most one reference (A:1028-1032).
#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct LoanPath {
    pub root: Local,
    pub through_ref: bool,
    pub steps: Vec<Step>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Step {
    Field(FieldIdx),
    Variant(VariantIdx),
    /// `[i]`.
    Elem,
    BoxDeref,
    /// Environment field `i` of an arrow body's `_1`.
    Capture(u32),
    /// The reference fields of the borrowing value behind a reference slot.
    Fields,
}

/// One loan; whether it is exclusive is a mode (plan d.7), not stored here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Loan {
    pub path: LoanPath,
    pub span: Span,
    pub origin: BorrowOrigin,
    pub site: Point,
    pub kind: LoanKind,
}

#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum LoanKind {
    Site,
    Copy,
    Part(Vec<u32>),
    Payload,
    Hold(LoopId),
    HoldCrossing(LoopId),
    Closure,
}

/// A loan of one body, dense in the order of the statements that make them
/// (choice: A:1264's "sites in `LoanId` order" is then source order).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct LoanId(pub u32);

impl Idx for LoanId {
    fn new(i: usize) -> Self {
        LoanId(u32::try_from(i).expect("LoanId exceeds u32"))
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

/// What `held` holds: a site loan in one of its turns, or what a parameter brings.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum LoanKey {
    Site(LoanId, Turn),
    Param(u32),
    Fields(u32),
    RFields(u32),
    Hold(LoopId),
}

/// A `for...of` bind's loan has three keys (ledger 84): this turn's, an earlier
/// turn's of this run, an earlier run's; every other loan has `Any`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Turn {
    Any,
    This,
    EarlierThisRun,
    EarlierRuns,
}

/// The loans of one body, made before the dataflow (plan d.4), sorted by site.
#[derive(Clone, Debug, Default)]
pub struct Loans {
    pub table: IdVec<LoanId, Loan>,
}

/// Which reference a place crosses, the one crossing of its normal form.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Cross {
    None,
    /// `*t`, or `*(t as Present).0`, of a reference local `t`.
    Ref(Local),
    /// A captured reference of an arrow body.
    Env,
    /// A reference field of the borrowing local `b`; `ro`: a field declared
    /// `readonly &` in `b` itself (or its payload narrowed to present).
    LocalField {
        b: Local,
        ro: bool,
    },
    /// A reference field of `*t`, `ro` likewise.
    PtrField {
        t: Local,
        ro: bool,
    },
}

const PAYLOAD: [Proj; 2] = [Proj::Variant(VariantIdx::PRESENT), Proj::Field(FieldIdx(0))];

/// `steps` name a field declared `readonly &` of the value of type `ty` itself, or
/// of its payload narrowed to present, or that field's own payload when the field
/// is nullable; never a tuple part.
pub(crate) fn readonly_field(tcx: &Tcx, ty: Ty, steps: &[Proj]) -> bool {
    let (ty, steps) = match (tcx.kind(ty), steps.strip_prefix(&PAYLOAD[..])) {
        (TyKind::Nullable(t), Some(rest)) => (t, rest),
        _ => (ty, steps),
    };
    // A nullable field's payload is the reference the field holds: `this.seen!`
    // of a `readonly &i64[] | null` field reads the read set (`INF-04-read-bit-put`).
    let steps = match steps {
        [f @ Proj::Field(_), rest @ ..] if rest == PAYLOAD => std::slice::from_ref(f),
        _ => steps,
    };
    let ([Proj::Field(f)], TyKind::Adt(adt, _)) = (steps, tcx.kind(ty)) else {
        return false;
    };
    tcx.adt(adt)
        .as_class()
        .and_then(|c| c.fields.get(f.index()))
        .is_some_and(|f| f.readonly_refs.iter().any(|p| p.is_empty()))
}

/// The normal form of the place `root` + `projs`, its crossing and its type; `None`
/// through a raw pointer, which makes no loan (A:1034).
pub(crate) fn normalize(
    tcx: &Tcx,
    b: &Body,
    root: Local,
    projs: &[Proj],
) -> Option<(LoanPath, Cross, Ty)> {
    let root_ty = b.locals[root].ty;
    let env = b.locals[root].kind == LocalKind::ClosureEnv;
    let mut pt = PlaceTy::of(root_ty);
    let mut path = LoanPath {
        root,
        through_ref: false,
        steps: Vec::new(),
    };
    let mut cross = Cross::None;
    let mut from = 0; // where the steps since the last crossing begin
    // The steps naming the reference field or part crossed, kept so that loans
    // through two different reference fields or parts stay apart (choice, plan
    // d.14; A:1032 drops them).
    let mut cross_len = 0;
    for (i, &p) in projs.iter().enumerate() {
        match (p, tcx.kind(pt.ty)) {
            (Proj::Deref, TyKind::Raw(_)) => return None,
            (Proj::Deref, TyKind::Boxed(_)) => path.steps.push(Step::BoxDeref),
            (Proj::Deref, _) if i == 0 => {
                path.through_ref = true;
                cross = if env { Cross::None } else { Cross::Ref(root) };
                from = 1;
            }
            (Proj::Deref, _) => {
                let inner = &projs[from..i];
                cross = match cross {
                    _ if env && cross == Cross::None => {
                        path.steps = vec![Step::Capture(field_of(inner))];
                        Cross::Env
                    }
                    Cross::None if inner == PAYLOAD => {
                        path.steps.clear();
                        Cross::Ref(root)
                    }
                    Cross::None => {
                        cross_len = path.steps.len();
                        Cross::LocalField {
                            b: root,
                            ro: readonly_field(tcx, root_ty, inner),
                        }
                    }
                    Cross::Ref(t) => {
                        let ro = pointee(tcx, root_ty).is_some_and(|ty| {
                            readonly_field(
                                tcx,
                                ty,
                                inner.strip_prefix(&PAYLOAD[..]).unwrap_or(inner),
                            )
                        });
                        path.steps.insert(0, Step::Fields);
                        cross_len = path.steps.len();
                        Cross::PtrField { t, ro }
                    }
                    // A second crossing collapses into the first (choice).
                    Cross::LocalField { b, .. } => {
                        path.steps.truncate(cross_len);
                        Cross::LocalField { b, ro: false }
                    }
                    Cross::PtrField { t, .. } => {
                        path.steps.truncate(cross_len);
                        Cross::PtrField { t, ro: false }
                    }
                    Cross::Env => {
                        path.steps.truncate(1);
                        Cross::Env
                    }
                };
                path.through_ref = true;
                from = i + 1;
            }
            (Proj::Field(f), _) => path.steps.push(Step::Field(f)),
            (Proj::Variant(v), _) => path.steps.push(Step::Variant(v)),
            (Proj::ConstIndex(k), TyKind::Tuple(_)) => {
                path.steps.push(Step::Field(FieldIdx::new(k as usize)))
            }
            (Proj::Index(_) | Proj::ConstIndex(_), _) => path.steps.push(Step::Elem),
        }
        pt = pt.project(tcx, p)?;
    }
    Some((path, cross, pt.ty))
}

fn field_of(inner: &[Proj]) -> u32 {
    match inner {
        [Proj::Field(f), ..] => f.0,
        _ => 0,
    }
}

/// The projections to each reference inside a value of type `ty`: the value
/// itself, a nullable one's payload, each reference part of a tuple, nested.
pub(crate) fn ref_parts(tcx: &Tcx, ty: Ty) -> Vec<Vec<Proj>> {
    match tcx.kind(ty) {
        TyKind::Ref(_) => vec![Vec::new()],
        TyKind::Nullable(t) => ref_parts(tcx, t)
            .into_iter()
            .map(|p| PAYLOAD.iter().copied().chain(p).collect())
            .collect(),
        TyKind::Tuple(parts) => {
            let mut out = Vec::new();
            for (k, &t) in tcx.list(parts).iter().enumerate() {
                for p in ref_parts(tcx, t) {
                    out.push(
                        std::iter::once(Proj::Field(FieldIdx::new(k)))
                            .chain(p)
                            .collect(),
                    );
                }
            }
            out
        }
        _ => Vec::new(),
    }
}

/// A part path as `LoanKind::Part` records it: the tuple part indices, a
/// nullable's payload looked through, as write-liveness names parts.
pub(crate) fn part_key(projs: &[Proj]) -> Vec<u32> {
    let mut out = Vec::new();
    let mut payload = false;
    for p in projs {
        match p {
            Proj::Variant(_) => payload = true,
            Proj::Field(_) if payload => payload = false,
            Proj::Field(f) => out.push(f.0),
            _ => {}
        }
    }
    out
}

/// The part of a copy's destination a `Part` loan `k` is for: `k` less the parts
/// the copied place itself names (`d = copy t.0` gives `d` the loan of `t.0`).
pub(crate) fn dest_part<'k>(b: &Body, loan: &Loan, k: &'k [u32]) -> &'k [u32] {
    let named = match b.stmt_at(loan.site).map(|s| &s.kind) {
        Some(StatementKind::Assign {
            value: Rvalue::Use(Operand::Copy(p)),
            ..
        }) => part_key(b.projs(*p)).len(),
        _ => 0,
    };
    &k[named.min(k.len())..]
}

/// The steps after the reference a copied place crosses: after `*t`, or after
/// `*(t as Present).0` of a narrowed nullable reference.
pub(crate) fn after_deref(projs: &[Proj]) -> &[Proj] {
    match projs.iter().position(|p| *p == Proj::Deref) {
        Some(i) => &projs[i + 1..],
        None => projs,
    }
}

/// Where a copied place sits: in the borrowing local `b` (no deref), or behind the
/// reference slot `t` (one leading deref); the steps after that.
pub(crate) fn container(tcx: &Tcx, b: &Body, root: Local, projs: &[Proj]) -> Option<bool> {
    let ty = b.locals[root].ty;
    // `*t`, or `*(t as Present).0`, the narrowed reference as its one crossing
    // (A:1030).
    let through = match projs {
        [Proj::Deref, rest @ ..] => Some(rest),
        [
            Proj::Variant(VariantIdx::PRESENT),
            Proj::Field(FieldIdx(0)),
            Proj::Deref,
            rest @ ..,
        ] => Some(rest),
        _ => None,
    };
    // A second crossing collapses into the first, as `normalize` collapses a loan's
    // path: a place reached through a reference field of a value reached through
    // another, `this.next.next.v`, sits where the first crossing leads. With no
    // container such a copy made no loan and held nothing, and a store through it
    // stored nothing (`this.next.v` copied, then pushed under a borrow of `v[0]`).
    match through {
        Some(rest) if !rest.is_empty() => {
            pointee(tcx, ty).filter(|p| bvalue(tcx, *p)).map(|_| true)
        }
        None if !projs.is_empty() && bvalue(tcx, ty) => Some(false),
        _ => None,
    }
}

impl Loans {
    /// Every loan `b` may make (plan d.4), in (block, index, sub-index) order.
    pub fn collect(tcx: &Tcx, b: &Body) -> Loans {
        let mut out = Loans::default();
        for (block, data) in b.blocks.iter_enumerated() {
            for (i, st) in data.stmts.iter().enumerate() {
                let site = Point::new(block, i);
                let StatementKind::Assign { value, .. } = &st.kind else {
                    continue;
                };
                let mut add = |path: LoanPath, origin, kind| {
                    out.table.push(Loan {
                        path,
                        span: st.span,
                        origin,
                        site,
                        kind,
                    });
                };
                match value {
                    Rvalue::Ref { place, origin } => {
                        let projs = b.projs(*place);
                        if let Some((path, _, _)) = normalize(tcx, b, place.local, projs) {
                            add(path, *origin, LoanKind::Site);
                        }
                        let local = |l: Local| LoanPath {
                            root: l,
                            through_ref: false,
                            steps: Vec::new(),
                        };
                        if *origin == BorrowOrigin::ClosureCapture
                            && projs == [Proj::Deref]
                            && b.locals[place.local].kind != LocalKind::ClosureEnv
                        {
                            add(local(place.local), *origin, LoanKind::Closure);
                        }
                    }
                    Rvalue::ClosureReborrow(f) => {
                        if let Some((path, _, _)) = normalize(tcx, b, f.local, b.projs(*f)) {
                            add(path, BorrowOrigin::Reborrow, LoanKind::Site);
                        }
                    }
                    Rvalue::Use(Operand::Copy(p)) => {
                        for (path, kind) in copy_loans(tcx, b, p.local, b.projs(*p)) {
                            add(path, BorrowOrigin::Reborrow, kind);
                        }
                    }
                    _ => {}
                }
            }
            for lp in &b.meta.loops {
                let LoopSource::Path(src) = lp.source else {
                    continue;
                };
                if lp.preheader != block {
                    continue;
                }
                let site = b.terminator_point(block);
                let projs = b.projs(src);
                let mut push = |path, kind| {
                    out.table.push(Loan {
                        path,
                        span: lp.span,
                        origin: BorrowOrigin::ForOfHidden,
                        site,
                        kind,
                    })
                };
                if let Some((path, _, _)) = normalize(tcx, b, src.local, projs) {
                    push(path, LoanKind::Hold(lp.id));
                }
                // A shared loan on each reference the source path goes through.
                let mut pt = PlaceTy::of(b.locals[src.local].ty);
                for (i, &p) in projs.iter().enumerate() {
                    if p == Proj::Deref && matches!(tcx.kind(pt.ty), TyKind::Ref(_)) {
                        if let Some((path, _, _)) = normalize(tcx, b, src.local, &projs[..i]) {
                            push(path, LoanKind::HoldCrossing(lp.id));
                        }
                    }
                    match pt.project(tcx, p) {
                        Some(next) => pt = next,
                        None => break,
                    }
                }
            }
        }
        out
    }

    /// The loans made at `p`, in sub-index order.
    pub fn at(&self, p: Point) -> impl Iterator<Item = (LoanId, &Loan)> {
        let lo = self.table.as_slice().partition_point(|l| l.site < p);
        self.table
            .iter_enumerated()
            .skip(lo)
            .take_while(move |(_, l)| l.site == p)
    }
}

/// The loans a `Use(Copy p)` may make: a nullable reference local's payload, each
/// part of a borrowing tuple local or of one behind a reference (`parts`), each
/// reference copied out of a field or part of a borrowing value (`copies`, or
/// `parts` for a part of a tuple held directly in a local).
fn copy_loans(tcx: &Tcx, b: &Body, root: Local, projs: &[Proj]) -> Vec<(LoanPath, LoanKind)> {
    let ty = b.locals[root].ty;
    let deref_of = |prefix: &[Proj], part: &[Proj]| {
        let full: Vec<Proj> = prefix
            .iter()
            .chain(part)
            .copied()
            .chain([Proj::Deref])
            .collect();
        normalize(tcx, b, root, &full).map(|(p, _, _)| p)
    };
    let parts = |prefix: &[Proj], t: Ty| {
        ref_parts(tcx, t)
            .into_iter()
            .filter_map(|k| Some((deref_of(prefix, &k)?, LoanKind::Part(part_key(&k)))))
            .collect::<Vec<_>>()
    };
    let pointee_ty = pointee(tcx, ty);
    let tuple = |t: Ty| bvalue(tcx, t) && !matches!(tcx.kind(strip_null(tcx, t)), TyKind::Adt(..));
    match projs {
        [] if pointee_ty.is_some() && matches!(tcx.kind(ty), TyKind::Nullable(_)) => {
            deref_of(&PAYLOAD, &[])
                .map(|p| (p, LoanKind::Payload))
                .into_iter()
                .collect()
        }
        [] if tuple(ty) => parts(&[], ty),
        [Proj::Deref] if pointee_ty.is_some_and(tuple) => parts(projs, pointee_ty.unwrap_or(ty)),
        _ => {
            let Some(through) = container(tcx, b, root, projs) else {
                return Vec::new();
            };
            let Some(pt) = projs_ty(tcx, ty, projs) else {
                return Vec::new();
            };
            // A part of a tuple held directly in a local, or in a nullable one's
            // payload: parts(b)'s choice (A:935).
            // Only tuple parts all the way: a reference field of a borrowing value
            // inside a part, `t[0].dst`, is copied out of that value (`copies`),
            // which takes its loan through `t` (T:1012 `FV-02-alias-nested`).
            let parts_of = projs.strip_prefix(&PAYLOAD[..]).unwrap_or(projs);
            let start = match parts_of.len() == projs.len() {
                true => ty,
                false => strip_null(tcx, ty),
            };
            let held_tuple = !through
                && matches!(tcx.kind(strip_null(tcx, ty)), TyKind::Tuple(_))
                && tuple_parts_only(tcx, start, parts_of);
            ref_parts(tcx, pt)
                .into_iter()
                .filter_map(|k| {
                    let path = deref_of(projs, &k)?;
                    let kind = match held_tuple {
                        true => LoanKind::Part(part_key(
                            &projs.iter().chain(&k).copied().collect::<Vec<_>>(),
                        )),
                        false => LoanKind::Copy,
                    };
                    Some((path, kind))
                })
                .collect()
        }
    }
}

/// Whether each of `projs`, from a value of type `ty`, is a part of a tuple.
fn tuple_parts_only(tcx: &Tcx, ty: Ty, projs: &[Proj]) -> bool {
    let mut t = ty;
    for &p in projs {
        let (Proj::Field(f), TyKind::Tuple(l)) = (p, tcx.kind(t)) else {
            return false;
        };
        match tcx.list(l).get(f.index()) {
            Some(&next) => t = next,
            None => return false,
        }
    }
    true
}

pub(crate) fn strip_null(tcx: &Tcx, t: Ty) -> Ty {
    match tcx.kind(t) {
        TyKind::Nullable(i) => i,
        _ => t,
    }
}

pub(crate) fn projs_ty(tcx: &Tcx, ty: Ty, projs: &[Proj]) -> Option<Ty> {
    let mut pt = PlaceTy::of(ty);
    for &p in projs {
        pt = pt.project(tcx, p)?;
    }
    Some(pt.ty)
}
