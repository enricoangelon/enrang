//! `remap_ids` (A:794; M3 plan b.10): rewrites the field and case indices a body
//! uses by name, against changed definitions of its ADTs.
//!
//! The body's types are those of `new_defs`, whose ADTs keep their ids while their
//! fields or cases change order, as a dev-runtime schema change makes them (the
//! text form's `redefine_adts` makes one for tests). `Body::names` holds the names
//! the indices had when the body was built; every `Field` and `Variant` projection,
//! `CheckTag`, aggregate operand order, `Switch` tag value on a discriminant,
//! `FieldInit` place, `NamedFill` field, `overridden(f)` and narrowing fact step is
//! mapped through them, walking each place's types in the new definitions with the
//! steps already mapped. A name with no new field or case is `Missing`.

use std::collections::BTreeMap;
use std::fmt;

use enrang_base::{Idx, Symbol};
use enrang_hir::{
    AdtId, AdtKind, ConstValue, FieldIdx, ItemPath, PathStep, Tcx, Ty, TyKind, VariantIdx,
};

use crate::body::{
    AggregateKind, Body, BodyNames, Callee, ConstKind, Operand, Proj, Rvalue, StatementKind,
    TerminatorKind,
};
use crate::ids::Local;
use crate::proj::{PlaceTy, canonicalize_projs, tag_value, visit_places_mut};

/// Why a body could not be remapped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RemapError {
    /// The new definitions have no ADT at `path`, or it has no field or case `name`.
    Missing { path: ItemPath, name: Symbol },
}

impl fmt::Display for RemapError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RemapError::Missing { path, name } => write!(f, "`{path}` has no `{name}`"),
        }
    }
}

impl std::error::Error for RemapError {}

/// The index maps of one ADT: old to new field, case, and each case's fields, and
/// old to new tag values.
#[derive(Default)]
struct Maps {
    fields: Vec<FieldIdx>,
    variants: Vec<VariantIdx>,
    variant_fields: Vec<Vec<FieldIdx>>,
    tags: BTreeMap<u128, u128>,
}

struct Remapper<'t> {
    tcx: &'t Tcx,
    maps: BTreeMap<AdtId, Maps>,
}

impl Remapper<'_> {
    fn build<'t>(tcx: &'t Tcx, names: &BodyNames) -> Result<Remapper<'t>, RemapError> {
        let mut maps = BTreeMap::new();
        for (path, old) in &names.adts {
            let missing = |name: &str| RemapError::Missing {
                path: path.clone(),
                name: enrang_base::intern(name),
            };
            let Some((adt, def)) = tcx.adts().find(|(_, a)| &tcx.def(a.def).path == path) else {
                return Err(missing("(the ADT)"));
            };
            let mut m = Maps::default();
            match &def.kind {
                AdtKind::Class(c) => {
                    for name in &old.fields {
                        match c.field_named(*name) {
                            Some((f, _)) => m.fields.push(f),
                            None => return Err(missing(name.as_str())),
                        }
                    }
                }
                AdtKind::Enum(e) => {
                    let ty = tcx.adt_identity(adt);
                    for (i, (name, fields)) in old.variants.iter().enumerate() {
                        let Some((v, case)) = e.variant_named(*name) else {
                            return Err(missing(name.as_str()));
                        };
                        m.variants.push(v);
                        let mut fs = Vec::new();
                        for f in fields {
                            match case.fields.iter().position(|x| x.name == *f) {
                                Some(j) => fs.push(FieldIdx::new(j)),
                                None => return Err(missing(f.as_str())),
                            }
                        }
                        m.variant_fields.push(fs);
                        if let Some(&old_tag) = old.tags.get(i) {
                            m.tags.insert(old_tag, tag_value(tcx, ty, v));
                        }
                    }
                }
                AdtKind::Interface(_) => continue,
            }
            maps.insert(adt, m);
        }
        Ok(Remapper { tcx, maps })
    }

    fn adt(&self, ty: Ty) -> Option<&Maps> {
        match self.tcx.kind(ty) {
            TyKind::Adt(adt, _) => self.maps.get(&adt),
            _ => None,
        }
    }

    /// One projection list, mapped step by step through the new types.
    fn projs(&self, start: Ty, projs: &[Proj]) -> Vec<Proj> {
        let mut pt = Some(PlaceTy::of(start));
        let mut out = Vec::with_capacity(projs.len());
        for &p in projs {
            let mapped = match (p, pt) {
                (Proj::Field(f), Some(t)) => match (self.adt(t.ty), t.variant) {
                    (Some(m), None) => Proj::Field(m.fields.get(f.index()).copied().unwrap_or(f)),
                    (Some(m), Some(v)) => {
                        let old_v = m.variants.iter().position(|&x| x == v);
                        let nf = old_v
                            .and_then(|ov| m.variant_fields.get(ov))
                            .and_then(|fs| fs.get(f.index()).copied());
                        Proj::Field(nf.unwrap_or(f))
                    }
                    _ => p,
                },
                (Proj::Variant(v), Some(t)) => match self.adt(t.ty) {
                    Some(m) => Proj::Variant(m.variants.get(v.index()).copied().unwrap_or(v)),
                    None => p,
                },
                _ => p,
            };
            pt = pt.and_then(|t| t.project(self.tcx, mapped));
            out.push(mapped);
        }
        out
    }

    fn field_of(&self, class: Ty, f: FieldIdx) -> FieldIdx {
        self.adt(class)
            .and_then(|m| m.fields.get(f.index()).copied())
            .unwrap_or(f)
    }
}

/// Remaps `b`'s field and case indices by name against `new_defs` (A:794), and
/// refreshes `b.names`.
pub fn remap_ids(b: &mut Body, new_defs: &Tcx) -> Result<(), RemapError> {
    let r = Remapper::build(new_defs, &b.names)?;
    let tcx = new_defs;
    let local_tys: Vec<Ty> = b.locals.iter().map(|l| l.ty).collect();
    let old = b.projs.clone();
    let mut table = crate::proj::ProjTable::new();
    visit_places_mut(b, &mut |_, p| {
        let mapped = r.projs(local_tys[p.local.index()], old.get(p.proj));
        p.proj = table.intern(&mapped);
    });
    b.projs = table;
    // Locals assigned a discriminant, with the enum they read.
    let mut discr: BTreeMap<Local, Ty> = BTreeMap::new();
    let ctor = crate::print::ctor_class(tcx, b);
    for block in b.blocks.iter() {
        for st in &block.stmts {
            if let StatementKind::Assign {
                dest,
                value: Rvalue::Discriminant(p),
            } = &st.kind
                && dest.is_local()
                && let Some(t) = b.place_ty(tcx, *p)
            {
                discr.insert(dest.local, t.ty);
            }
        }
    }
    let place_tys: Vec<Option<Ty>> = {
        let mut out = Vec::new();
        for block in b.blocks.iter() {
            for st in &block.stmts {
                if let StatementKind::CheckTag { place, .. } = &st.kind {
                    out.push(b.place_ty(tcx, *place).map(|t| t.ty));
                }
            }
        }
        out
    };
    let mut tags = place_tys.into_iter();
    let operand = |op: &mut Operand| {
        if let Operand::Const(c) = op
            && let ConstKind::Value(ConstValue::Overridden(f)) = &mut c.kind
            && let Some(class) = ctor
        {
            *f = r.field_of(class, *f);
        }
    };
    for block in b.blocks.iter_mut() {
        for st in &mut block.stmts {
            match &mut st.kind {
                StatementKind::CheckTag { variant, .. } => {
                    if let Some(Some(ty)) = tags.next()
                        && let Some(m) = r.adt(ty)
                        && let Some(&nv) = m.variants.get(variant.index())
                    {
                        *variant = nv;
                    }
                }
                StatementKind::Assign {
                    value: Rvalue::Aggregate(AggregateKind::Adt { adt, variant, args }, ops),
                    ..
                } => {
                    ops.iter_mut().for_each(operand);
                    let Some(m) = r.maps.get(adt) else {
                        continue;
                    };
                    let (order, new_variant) = match variant {
                        Some(v) => {
                            let ov = v.index();
                            (
                                m.variant_fields.get(ov).cloned().unwrap_or_default(),
                                m.variants.get(ov).copied(),
                            )
                        }
                        None => (m.fields.clone(), None),
                    };
                    if let Some(nv) = new_variant {
                        *variant = Some(nv);
                    }
                    let ty = tcx.mk_adt(*adt, &tcx.list(*args));
                    let count = match (*variant, &tcx.adt(*adt).kind) {
                        (Some(v), AdtKind::Enum(e)) => e.variants[v.index()].fields.len(),
                        (None, AdtKind::Class(c)) => c.fields.len(),
                        _ => ops.len(),
                    };
                    let mut slots: Vec<Option<Operand>> = vec![None; count];
                    for (i, op) in ops.drain(..).enumerate() {
                        let to = order.get(i).copied().unwrap_or(FieldIdx::new(i));
                        if let Some(slot) = slots.get_mut(to.index()) {
                            *slot = Some(op);
                        }
                    }
                    let mut out = Vec::with_capacity(count);
                    for (i, slot) in slots.into_iter().enumerate() {
                        match slot {
                            Some(op) => out.push(op),
                            None => {
                                let pt = PlaceTy {
                                    ty,
                                    variant: *variant,
                                };
                                let name = pt
                                    .field_name(tcx, FieldIdx::new(i))
                                    .unwrap_or_else(|| enrang_base::intern("(a field)"));
                                return Err(RemapError::Missing {
                                    path: tcx.def(tcx.adt(*adt).def).path.clone(),
                                    name,
                                });
                            }
                        }
                    }
                    *ops = out;
                }
                StatementKind::Assign { value, .. } => match value {
                    Rvalue::Use(op) | Rvalue::Unary(_, op) | Rvalue::CheckedNeg(op) => operand(op),
                    Rvalue::Binary(_, x, y) | Rvalue::Checked(_, x, y) => {
                        operand(x);
                        operand(y);
                    }
                    _ => {}
                },
                StatementKind::FieldInit { value, .. } => operand(value),
                _ => {}
            }
        }
        match &mut block.term.kind {
            TerminatorKind::Switch { value, arms, .. } => {
                if let Some(p) = value.place()
                    && p.is_local()
                    && let Some(&ty) = discr.get(&p.local)
                    && let Some(m) = r.adt(ty)
                {
                    for (v, _) in arms.iter_mut() {
                        if let Some(&nv) = m.tags.get(v) {
                            *v = nv;
                        }
                    }
                }
                operand(value);
            }
            TerminatorKind::Call { callee, args, .. } => {
                args.iter_mut().for_each(operand);
                if let Callee::NamedFill { class, left_out } = callee {
                    for f in left_out.iter_mut() {
                        *f = r.field_of(*class, *f);
                    }
                }
            }
            _ => {}
        }
    }
    let facts: Vec<(Ty, Vec<PathStep>)> = b
        .meta
        .facts
        .iter()
        .map(|f| (b.locals[f.root].ty, f.steps.clone()))
        .collect();
    for (fact, (root_ty, steps)) in b.meta.facts.iter_mut().zip(facts) {
        let mut pt = Some(PlaceTy::of(root_ty));
        for (step, old_step) in fact.steps.iter_mut().zip(steps) {
            let proj = match old_step {
                PathStep::Field(f) => {
                    let nf = pt
                        .and_then(|t| r.adt(t.ty).filter(|_| t.variant.is_none()))
                        .and_then(|m| m.fields.get(f.index()).copied())
                        .unwrap_or(f);
                    *step = PathStep::Field(nf);
                    Some(Proj::Field(nf))
                }
                PathStep::Deref => Some(Proj::Deref),
                PathStep::Payload => {
                    pt = pt.and_then(|t| t.project(tcx, Proj::Variant(VariantIdx::PRESENT)));
                    Some(Proj::Field(FieldIdx(0)))
                }
            };
            pt = proj.and_then(|p| pt.and_then(|t| t.project(tcx, p)));
        }
    }
    canonicalize_projs(b);
    b.names = BodyNames::collect(tcx, b);
    Ok(())
}
