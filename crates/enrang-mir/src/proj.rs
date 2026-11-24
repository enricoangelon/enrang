//! Projection lists and places: the per-body interner, the type of a place, the
//! names a place prints with, and the walkers every pass shares (M3 plan b.2).
//!
//! A body's places are visited in one fixed order: blocks by index, each block's
//! statements then its terminator, the parts of each in field order, then the
//! `for...of` sources of `PhaseMeta`. `canonicalize_projs` re-interns in that
//! order, so two bodies with the same places compare equal whatever order they
//! were built in, which the text round trip relies on.

use std::collections::BTreeMap;
use std::sync::Arc;

use enrang_base::{Idx, Symbol};
use enrang_hir::{AdtKind, FieldIdx, Tcx, Ty, TyKind, VariantIdx, VariantValue};

use crate::body::{
    AdtNames, AggregateKind, Body, BodyNames, Callee, LoopSource, Operand, Place, Proj, Rvalue,
    StatementKind, TerminatorKind,
};
use crate::ids::{Local, Point, ProjId};

/// One body's interned projection lists; `ProjId(0)` is the empty list.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjTable {
    lists: Vec<Arc<[Proj]>>,
    ids: BTreeMap<Arc<[Proj]>, ProjId>,
}

impl Default for ProjTable {
    fn default() -> ProjTable {
        ProjTable::new()
    }
}

impl ProjTable {
    /// A table holding only the empty list.
    pub fn new() -> ProjTable {
        let mut table = ProjTable {
            lists: Vec::new(),
            ids: BTreeMap::new(),
        };
        table.intern(&[]);
        table
    }

    pub fn intern(&mut self, projs: &[Proj]) -> ProjId {
        if let Some(&id) = self.ids.get(projs) {
            return id;
        }
        let id = ProjId::new(self.lists.len());
        let list: Arc<[Proj]> = Arc::from(projs);
        self.lists.push(Arc::clone(&list));
        self.ids.insert(list, id);
        id
    }

    pub fn get(&self, id: ProjId) -> &[Proj] {
        &self.lists[id.index()]
    }

    /// `base` with one more projection.
    pub fn project(&mut self, base: Place, p: Proj) -> Place {
        let mut list = self.get(base.proj).to_vec();
        list.push(p);
        Place {
            local: base.local,
            proj: self.intern(&list),
        }
    }

    pub fn len(&self) -> usize {
        self.lists.len()
    }

    pub fn is_empty(&self) -> bool {
        self.lists.is_empty()
    }
}

impl Body {
    /// The projections of `p`.
    pub fn projs(&self, p: Place) -> &[Proj] {
        self.projs.get(p.proj)
    }

    /// `base` with one more projection, interned in this body.
    pub fn project(&mut self, base: Place, p: Proj) -> Place {
        self.projs.project(base, p)
    }

    /// The place `local` with `projs`, interned in this body.
    pub fn place(&mut self, local: Local, projs: &[Proj]) -> Place {
        Place {
            local,
            proj: self.projs.intern(projs),
        }
    }

    /// The type of `p`, `None` where a projection does not fit its base.
    pub fn place_ty(&self, tcx: &Tcx, p: Place) -> Option<PlaceTy> {
        let mut pt = PlaceTy::of(self.locals[p.local].ty);
        for &proj in self.projs(p) {
            pt = pt.project(tcx, proj)?;
        }
        Some(pt)
    }

    /// Whether `p` dereferences a reference, a raw pointer or a box anywhere.
    pub fn has_deref(&self, p: Place) -> bool {
        self.projs(p).contains(&Proj::Deref)
    }
}

/// A place's type, and the case a `Variant` projection selected, which the next
/// `Field` reads (`(_1 as Some).0`).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct PlaceTy {
    pub ty: Ty,
    pub variant: Option<VariantIdx>,
}

impl PlaceTy {
    pub fn of(ty: Ty) -> PlaceTy {
        PlaceTy { ty, variant: None }
    }

    /// The type after `p`, `None` where `p` does not fit.
    pub fn project(self, tcx: &Tcx, p: Proj) -> Option<PlaceTy> {
        let kind = tcx.kind(self.ty);
        let ty = match (p, self.variant) {
            (Proj::Deref, None) => match kind {
                TyKind::Ref(t) | TyKind::Raw(t) | TyKind::Boxed(t) => t,
                _ => return None,
            },
            (Proj::Field(f), Some(v)) => match kind {
                TyKind::Adt(adt, args) => {
                    let e = tcx.adt(adt).as_enum()?;
                    e.variants.get(v.index())?.fields.get(f.index())?;
                    tcx.field_ty(adt, Some(v), f, args)
                }
                TyKind::Nullable(t) if v == VariantIdx::PRESENT && f.index() == 0 => t,
                _ => return None,
            },
            (Proj::Field(f), None) => match kind {
                TyKind::Adt(adt, args) => {
                    tcx.adt(adt).as_class()?.fields.get(f.index())?;
                    tcx.field_ty(adt, None, f, args)
                }
                TyKind::Tuple(parts) => *tcx.list(parts).get(f.index())?,
                TyKind::Object(shape) => tcx.shape(shape).fields.get(f.index())?.1,
                TyKind::Param(param) => return PlaceTy::of(bound_of(tcx, param)?).project(tcx, p),
                _ => return None,
            },
            (Proj::Variant(v), None) => {
                variant_count(tcx, self.ty).filter(|&n| v.index() < n)?;
                return Some(PlaceTy {
                    ty: self.ty,
                    variant: Some(v),
                });
            }
            (Proj::Index(_) | Proj::ConstIndex(_), None) => match kind {
                TyKind::Array(t) | TyKind::Fixed(t, _) | TyKind::Slice(t) => t,
                TyKind::Tuple(parts) => match p {
                    Proj::ConstIndex(i) => *tcx.list(parts).get(i as usize)?,
                    _ => return None,
                },
                _ => return None,
            },
            _ => return None,
        };
        Some(PlaceTy::of(ty))
    }

    /// The name `Field(f)` prints with here, `None` for a tuple part or a
    /// nullable's payload, which print as numbers.
    pub fn field_name(self, tcx: &Tcx, f: FieldIdx) -> Option<Symbol> {
        match (tcx.kind(self.ty), self.variant) {
            (TyKind::Adt(adt, _), None) => {
                Some(tcx.adt(adt).as_class()?.fields.get(f.index())?.name)
            }
            (TyKind::Adt(adt, _), Some(v)) => Some(
                tcx.adt(adt)
                    .as_enum()?
                    .variants
                    .get(v.index())?
                    .fields
                    .get(f.index())?
                    .name,
            ),
            (TyKind::Object(shape), None) => Some(tcx.shape(shape).fields.get(f.index())?.0),
            _ => None,
        }
    }

    /// The field named `name` here.
    pub fn field_named(self, tcx: &Tcx, name: Symbol) -> Option<FieldIdx> {
        match (tcx.kind(self.ty), self.variant) {
            (TyKind::Adt(adt, _), None) => tcx.adt(adt).as_class()?.field_named(name).map(|f| f.0),
            (TyKind::Adt(adt, _), Some(v)) => tcx
                .adt(adt)
                .as_enum()?
                .variants
                .get(v.index())?
                .fields
                .iter()
                .position(|f| f.name == name)
                .map(FieldIdx::new),
            (TyKind::Object(shape), None) => tcx.shape(shape).position(name).map(FieldIdx::new),
            _ => None,
        }
    }
}

/// The type a type parameter's fields are read through: its object type (an
/// implicit one, D5), or its first bounding class.
fn bound_of(tcx: &Tcx, p: enrang_hir::ParamId) -> Option<Ty> {
    let def = tcx.param(p);
    if let Some(enrang_hir::Implicit::Shape(s)) = def.implicit {
        return Some(tcx.mk_object_shape((*tcx.shape(s)).clone()));
    }
    def.bounds.iter().find_map(|&b| match tcx.bound(b) {
        enrang_hir::Bound::Class { adt, args } => Some(tcx.mk_adt(*adt, &tcx.list(*args))),
        enrang_hir::Bound::Iface { .. } => None,
    })
}

/// The number of cases of an enum or a nullable (2); `None` for anything else.
pub fn variant_count(tcx: &Tcx, ty: Ty) -> Option<usize> {
    match tcx.kind(ty) {
        TyKind::Adt(adt, _) => Some(tcx.adt(adt).as_enum()?.variants.len()),
        TyKind::Nullable(_) => Some(2),
        _ => None,
    }
}

/// The name of case `v` of an enum, or `Null`/`Present` of a nullable.
pub fn variant_name(tcx: &Tcx, ty: Ty, v: VariantIdx) -> Option<Symbol> {
    match tcx.kind(ty) {
        TyKind::Adt(adt, _) => Some(tcx.adt(adt).as_enum()?.variants.get(v.index())?.name),
        TyKind::Nullable(_) => match v {
            VariantIdx::NULL => Some(enrang_base::intern("Null")),
            VariantIdx::PRESENT => Some(enrang_base::intern("Present")),
            _ => None,
        },
        _ => None,
    }
}

/// The case named `name` of an enum or a nullable.
pub fn variant_named(tcx: &Tcx, ty: Ty, name: Symbol) -> Option<VariantIdx> {
    let n = variant_count(tcx, ty)?;
    (0..n)
        .map(VariantIdx::new)
        .find(|&v| variant_name(tcx, ty, v) == Some(name))
}

/// The value a `Switch` on the discriminant sees for case `v` (plan b.4): the
/// written value of a payload-free enum with values, the case index otherwise.
pub fn tag_value(tcx: &Tcx, ty: Ty, v: VariantIdx) -> u128 {
    if let TyKind::Adt(adt, _) = tcx.kind(ty)
        && let Some(e) = tcx.adt(adt).as_enum()
        && let Some(VariantValue::Int(value)) = e.variants.get(v.index()).and_then(|c| c.value)
    {
        return value as u128;
    }
    v.index() as u128
}

// ---------------------------------------------------------------------------------
// Walkers.

/// Calls `f` on every place of `op`.
fn operand_mut(op: &mut Operand, f: &mut dyn FnMut(&mut Place)) {
    if let Operand::Copy(p) | Operand::Move(p) = op {
        f(p);
    }
}

fn rvalue_mut(rv: &mut Rvalue, f: &mut dyn FnMut(&mut Place)) {
    match rv {
        Rvalue::Use(op) | Rvalue::Unary(_, op) | Rvalue::CheckedNeg(op) => operand_mut(op, f),
        Rvalue::Cast(_, op, _) | Rvalue::Convert(_, op) => operand_mut(op, f),
        Rvalue::Binary(_, a, b) | Rvalue::Checked(_, a, b) => {
            operand_mut(a, f);
            operand_mut(b, f);
        }
        Rvalue::Aggregate(_, ops) => ops.iter_mut().for_each(|op| operand_mut(op, f)),
        Rvalue::Ref { place, .. }
        | Rvalue::AddrOf(place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::ClosureReborrow(place)
        | Rvalue::ClosureValue { env: place, .. } => f(place),
        Rvalue::ArrowFn(_) => {}
    }
}

/// Calls `f` on every place of a statement, in field order.
pub fn statement_places_mut(kind: &mut StatementKind, g: &mut dyn FnMut(&mut Place)) {
    match kind {
        StatementKind::Assign { dest, value } => {
            g(dest);
            rvalue_mut(value, g);
        }
        StatementKind::CheckBounds { index, len } => {
            operand_mut(index, g);
            operand_mut(len, g);
        }
        StatementKind::CheckTag { place, .. }
        | StatementKind::CheckClass { place, .. }
        | StatementKind::SetTable { place, .. }
        | StatementKind::Drop(place, _)
        | StatementKind::DropGlue(place) => g(place),
        StatementKind::FieldInit { field, value } => {
            g(field);
            operand_mut(value, g);
        }
        StatementKind::Intrinsic { args, dest, .. }
        | StatementKind::HostCall { args, dest, .. } => {
            args.iter_mut().for_each(|op| operand_mut(op, g));
            if let Some(dest) = dest {
                g(dest);
            }
        }
        StatementKind::Asm(asm) => {
            asm.ins.iter_mut().for_each(|(_, op)| operand_mut(op, g));
            asm.outs.iter_mut().flat_map(|(_, p)| p).for_each(g);
        }
        StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop => {}
    }
}

/// Calls `f` on every place of a terminator, in field order.
pub fn terminator_places_mut(kind: &mut TerminatorKind, g: &mut dyn FnMut(&mut Place)) {
    match kind {
        TerminatorKind::Switch { value, .. } => operand_mut(value, g),
        TerminatorKind::Call {
            callee, args, dest, ..
        } => {
            match callee {
                Callee::FnPtr(op) | Callee::Virtual { table: op, .. } => operand_mut(op, g),
                _ => {}
            }
            args.iter_mut().for_each(|op| operand_mut(op, g));
            g(dest);
        }
        TerminatorKind::Goto(_) | TerminatorKind::Return | TerminatorKind::Unreachable => {}
    }
}

/// The places of a statement, in field order.
pub fn statement_places(kind: &StatementKind) -> Vec<Place> {
    let mut out = Vec::new();
    statement_places_mut(&mut kind.clone(), &mut |p| out.push(*p));
    out
}

/// The places of a terminator, in field order.
pub fn terminator_places(kind: &TerminatorKind) -> Vec<Place> {
    let mut out = Vec::new();
    terminator_places_mut(&mut kind.clone(), &mut |p| out.push(*p));
    out
}

/// Calls `f` on every place of every statement, terminator and loop source, in the
/// module doc's order, with the point it sits at (`None` for a loop source).
pub fn visit_places_mut(body: &mut Body, f: &mut dyn FnMut(Option<Point>, &mut Place)) {
    for (b, block) in body.blocks.iter_enumerated_mut() {
        for (i, st) in block.stmts.iter_mut().enumerate() {
            let at = Some(Point::new(b, i));
            statement_places_mut(&mut st.kind, &mut |p| f(at, p));
        }
        let at = Some(Point::new(b, block.stmts.len()));
        terminator_places_mut(&mut block.term.kind, &mut |p| f(at, p));
    }
    for l in &mut body.meta.loops {
        if let LoopSource::Path(p) = &mut l.source {
            f(None, p);
        }
    }
}

/// Every place of `body` with its point, in the module doc's order.
pub fn places(body: &Body) -> Vec<(Option<Point>, Place)> {
    let mut out = Vec::new();
    for (b, block) in body.blocks.iter_enumerated() {
        for (i, st) in block.stmts.iter().enumerate() {
            let at = Some(Point::new(b, i));
            out.extend(statement_places(&st.kind).into_iter().map(|p| (at, p)));
        }
        let at = Some(Point::new(b, block.stmts.len()));
        out.extend(
            terminator_places(&block.term.kind)
                .into_iter()
                .map(|p| (at, p)),
        );
    }
    for l in &body.meta.loops {
        if let LoopSource::Path(p) = &l.source {
            out.push((None, *p));
        }
    }
    out
}

/// Re-interns every projection list in the module doc's order, dropping lists no
/// place uses, so equal bodies built in different orders compare equal.
pub fn canonicalize_projs(body: &mut Body) {
    let old = std::mem::take(&mut body.projs);
    let mut new = ProjTable::new();
    visit_places_mut(body, &mut |_, p| p.proj = new.intern(old.get(p.proj)));
    body.projs = new;
}

impl BodyNames {
    /// The names of every ADT `body` names: in a local's type, along a place's
    /// projections, in an aggregate, a `SetTable`, a `NamedFill` or an implicit
    /// constructor (A:462).
    pub fn collect(tcx: &Tcx, body: &Body) -> BodyNames {
        let mut tys: Vec<Ty> = body.locals.iter().map(|l| l.ty).collect();
        for (_, place) in places(body) {
            let mut pt = PlaceTy::of(body.locals[place.local].ty);
            for &p in body.projs(place) {
                match pt.project(tcx, p) {
                    Some(next) => pt = next,
                    None => break,
                }
                tys.push(pt.ty);
            }
        }
        let mut adts = Vec::new();
        for block in body.blocks.iter() {
            for st in &block.stmts {
                match &st.kind {
                    StatementKind::Assign {
                        value: Rvalue::Aggregate(AggregateKind::Adt { adt, .. }, _),
                        ..
                    } => adts.push(*adt),
                    StatementKind::SetTable { class, .. } => tys.push(*class),
                    _ => {}
                }
            }
            if let TerminatorKind::Call {
                callee: Callee::NamedFill { class, .. } | Callee::ImplicitCtor { class },
                ..
            } = &block.term.kind
            {
                tys.push(*class);
            }
        }
        let mut seen = std::collections::BTreeSet::new();
        while let Some(t) = tys.pop() {
            if !seen.insert(t) {
                continue;
            }
            if let TyKind::Adt(adt, _) = tcx.kind(t) {
                adts.push(adt);
            }
            tys.extend(tcx.children(t));
        }
        let mut names = BodyNames::default();
        for adt in adts {
            let def = tcx.adt(adt);
            let path = tcx.def(def.def).path.clone();
            if names.adts.contains_key(&path) {
                continue;
            }
            let entry = match &def.kind {
                AdtKind::Class(c) => AdtNames {
                    fields: c.fields.iter().map(|f| f.name).collect(),
                    ..AdtNames::default()
                },
                AdtKind::Enum(e) => {
                    let ty = tcx.adt_identity(adt);
                    AdtNames {
                        fields: Vec::new(),
                        variants: e
                            .variants
                            .iter()
                            .map(|v| (v.name, v.fields.iter().map(|f| f.name).collect()))
                            .collect(),
                        tags: (0..e.variants.len())
                            .map(|v| tag_value(tcx, ty, VariantIdx::new(v)))
                            .collect(),
                    }
                }
                AdtKind::Interface(_) => continue,
            };
            names.adts.insert(path, entry);
        }
        names
    }
}
