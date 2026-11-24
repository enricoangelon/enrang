//! Move paths (A:987; M3 plan d.1; owner 2D): a tree per local over
//! `local(.field | as variant .field)*`, a node per path moved, assigned or
//! dropped, plus, in a constructor, the `super` pseudo-path and `(*this).f` for
//! every field (A:1003). A reference, raw or `Box` deref and an index end a path
//! (A:987); only `*_1` of a constructor or a `move` method is the object itself.
//!
//! `MoveData` also carries what init dataflow needs from `Tcx`, so that
//! `InitResults::compute` needs none: each place's path, the extra effects of
//! constructor calls, `super(...)`, the named-form shim and `overridden(f)`
//! switches, and the uses those receivers exempt (c.10, D20).

use std::collections::{BTreeMap, BTreeSet};

use enrang_base::{IdVec, Idx};
use enrang_hir::{ClassModifier, ConstValue, ConvKind, DefKind, FieldIdx, Receiver, Tcx, TyKind};
use enrang_mir::{
    BinOp, BlockId, Body, BodyOwner, BorrowOrigin, Callee, ConstKind, Local, MovePathKey, MoveStep,
    Operand, Place, PlaceTy, Point, Proj, Rvalue, StatementKind, TerminatorKind, places,
};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct MovePathIdx(pub u32);

impl Idx for MovePathIdx {
    fn new(i: usize) -> Self {
        MovePathIdx(u32::try_from(i).expect("MovePathIdx exceeds u32"))
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

/// One node: its key, its parent, its children in creation order. The `super`
/// pseudo-path has no key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MovePath {
    pub key: Option<MovePathKey>,
    pub parent: Option<MovePathIdx>,
    pub children: Vec<MovePathIdx>,
}

/// What a point does to a path beyond its own statement (c.10, D20, A:1003).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Effect {
    /// The path and its children become initialised.
    Init,
    /// Moved out: uninitialised, and a move site.
    Move,
    /// Uninitialised otherwise (`StorageDead`, a drop, a named field still to set).
    Kill,
}

/// The move paths of one body. Only the roots, with no `lookup`, until
/// [`MoveData::build`] (the 1B entry point `collect` has no `Tcx`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MoveData {
    pub paths: IdVec<MovePathIdx, MovePath>,
    pub by_key: BTreeMap<MovePathKey, MovePathIdx>,
    pub super_path: Option<MovePathIdx>,
    /// Each place of the body: the deepest path that is a prefix of it, and
    /// whether that path is the whole place.
    pub lookup: BTreeMap<Place, (MovePathIdx, bool)>,
    /// A constructor: each field's path (`_1.f`), whether its class declares it,
    /// and whether it starts maybe-initialised (no default, and a class below may
    /// override it).
    pub ctor_fields: Option<Vec<(FieldIdx, MovePathIdx, bool, bool)>>,
    /// A `move` method: moves out of `*_1` are allowed.
    pub move_method: bool,
    /// Extra effects of a point, after its own.
    pub effects: BTreeMap<Point, Vec<(MovePathIdx, Effect)>>,
    /// Uses exempt from the init checks: a `new`'s borrow of its destination and
    /// the reborrow and upcast of `this` for `super(...)`.
    pub exempt: BTreeSet<Point>,
    /// The `super(...)` calls (wherever they are: EN0619 outside a constructor).
    pub supers: BTreeSet<Point>,
    /// The blocks entered when a parameter was left out, by a `switch` on
    /// `lt(copy #supplied, k)` (A:937), with that parameter's local: its
    /// default's store there is no EN0613.
    pub defaults: BTreeSet<(BlockId, Local)>,
    /// Places whose move is EN0607, out of a field of a class with a destructor:
    /// reported, and not applied, so its later uses get no second report.
    pub dtor_moves: BTreeSet<Place>,
}

/// Whether `ty` has a type default (S:871): numbers, `bool`, `string`, `T[]`,
/// `T | null`, raw pointers.
pub(crate) fn type_default(tcx: &Tcx, ty: enrang_hir::Ty) -> bool {
    matches!(
        tcx.kind(ty),
        TyKind::Int(_)
            | TyKind::Float(_)
            | TyKind::Bool
            | TyKind::Str
            | TyKind::Array(_)
            | TyKind::Nullable(_)
            | TyKind::Raw(_)
    )
}

/// The inlined synthesised constructor's stores into the fields of `dest` before
/// its borrow at `r` (c.10): back through every predecessor to
/// `set_table(dest, ..)`, a default's `?:`, `&&` or `??` joins included. They
/// write a value not built yet, so they are exempt from the parent check, as a
/// constructor's own field stores are.
fn inlined_stores(b: &Body, r: Point, dest: Place) -> Vec<Point> {
    let cfg = enrang_mir::Cfg::new(b);
    let mut out = Vec::new();
    let mut seen = BTreeSet::new();
    let mut work = vec![(r.block, r.index as usize)];
    while let Some((bb, end)) = work.pop() {
        let mut table = false;
        for i in (0..end).rev() {
            match &b.blocks[bb].stmts[i].kind {
                StatementKind::SetTable { place, .. } if *place == dest => {
                    table = true;
                    break;
                }
                StatementKind::Assign { dest: d, .. }
                    if d.local == dest.local
                        && b.projs(*d).len() > b.projs(dest).len()
                        && b.projs(*d).starts_with(b.projs(dest))
                        && !b.projs(*d).contains(&Proj::Deref) =>
                {
                    out.push(Point::new(bb, i));
                }
                _ => {}
            }
        }
        if table {
            continue;
        }
        for &p in &cfg.preds[bb] {
            if seen.insert(p) {
                work.push((p, b.blocks[p].stmts.len()));
            }
        }
    }
    out.sort();
    out
}

/// Whether `place` steps into a field of a class with a destructor before any
/// deref or index (EN0607, A:991).
fn dtor_field(tcx: &Tcx, b: &Body, place: Place) -> bool {
    let mut ty = PlaceTy::of(b.locals[place.local].ty);
    for &proj in b.projs(place) {
        match (proj, tcx.kind(ty.ty)) {
            (Proj::Deref | Proj::Index(_), _) => return false,
            (Proj::ConstIndex(_), k) if !matches!(k, TyKind::Tuple(_)) => return false,
            (Proj::Field(_), TyKind::Adt(adt, args))
                if ty.variant.is_none() && tcx.class_dtor(adt, args).is_some() =>
            {
                return true;
            }
            _ => {}
        }
        let Some(next) = ty.project(tcx, proj) else {
            return false;
        };
        ty = next;
    }
    false
}

/// The definition a body is, if a function's.
pub(crate) fn owner_def(b: &Body) -> Option<enrang_hir::DefId> {
    match b.owner {
        BodyOwner::Fn(d) => Some(d),
        _ => None,
    }
}

/// The value assigned to `l` last before `p` in `p`'s block, with its point.
pub(crate) fn def_of(b: &Body, p: Point, l: Local) -> Option<(Point, &Rvalue)> {
    let stmts = &b.blocks[p.block].stmts;
    (0..(p.index as usize).min(stmts.len()))
        .rev()
        .find_map(|i| match &stmts[i].kind {
            StatementKind::Assign { dest, value } if *dest == Place::local(l) => {
                Some((Point::new(p.block, i), value))
            }
            _ => None,
        })
}

impl MoveData {
    /// The 1B entry point, with no `Tcx`: the roots only; [`MoveData::build`]
    /// makes the rest.
    pub fn collect(b: &Body) -> MoveData {
        let mut md = MoveData::default();
        for l in b.locals.indices() {
            md.node(l, &[]);
        }
        md
    }

    /// The move paths of `b` with everything init dataflow needs.
    pub fn build(tcx: &Tcx, b: &Body) -> MoveData {
        let def = owner_def(b);
        let mut md = MoveData {
            move_method: def
                .and_then(|d| tcx.sig_opt(d))
                .is_some_and(|s| s.receiver == Some(Receiver::Move)),
            ..MoveData::default()
        };
        for l in b.locals.indices() {
            let root = md.node(l, &[]);
            md.lookup.insert(Place::local(l), (root, true));
        }
        let class = def
            .filter(|&d| tcx.def(d).kind == DefKind::Ctor)
            .and_then(|d| tcx.def(d).parent)
            .and_then(|p| tcx.adt_of(p))
            .and_then(|a| Some((a, tcx.adt(a).as_class()?)));
        if let Some((_, c)) = class {
            if c.base.is_some() {
                md.super_path = Some(md.paths.push(MovePath {
                    key: None,
                    parent: None,
                    children: Vec::new(),
                }));
            }
            let open = c.modifier != ClassModifier::Final;
            let fields = c.fields.iter().enumerate().map(|(i, f)| {
                let f_idx = FieldIdx::new(i);
                let node = md.node(Local(1), &[MoveStep::Field(f_idx)]);
                let default = f.has_default || type_default(tcx, f.ty);
                (f_idx, node, i >= c.own_from as usize, open && !default)
            });
            md.ctor_fields = Some(fields.collect());
        }
        // A node for every path moved, assigned or dropped.
        let all = places(b);
        for (at, place) in &all {
            let Some(at) = at else { continue };
            if md.tracked(b, *at, *place)
                && let (steps, true) = md.key(tcx, b, *place)
            {
                md.node(place.local, &steps);
            }
        }
        for (_, place) in all {
            let (steps, exact) = md.key(tcx, b, place);
            let found = (0..=steps.len()).rev().find_map(|n| {
                let key = MovePathKey {
                    local: place.local,
                    steps: steps[..n].to_vec(),
                };
                md.by_key.get(&key).map(|&i| (i, exact && n == steps.len()))
            });
            md.lookup
                .insert(place, found.expect("every local has a root path"));
        }
        md.dtor_moves = md
            .lookup
            .keys()
            .filter(|p| dtor_field(tcx, b, **p))
            .copied()
            .collect();
        md.receivers(tcx, b, class.map(|(_, c)| c));
        md
    }

    /// Whether `place` at `at` is moved, assigned or dropped there.
    fn tracked(&self, b: &Body, at: Point, place: Place) -> bool {
        use crate::init::{point_dests, point_operands};
        point_dests(b, at).contains(&place)
            || point_operands(b, at).contains(&&Operand::Move(place))
            || matches!(b.stmt_at(at).map(|s| &s.kind), Some(StatementKind::Drop(p, _)) if *p == place)
    }

    /// The node of `local.steps`, made with its prefixes when missing.
    fn node(&mut self, local: Local, steps: &[MoveStep]) -> MovePathIdx {
        let key = MovePathKey {
            local,
            steps: steps.to_vec(),
        };
        if let Some(&i) = self.by_key.get(&key) {
            return i;
        }
        let parent = (!steps.is_empty()).then(|| self.node(local, &steps[..steps.len() - 1]));
        let i = self.paths.push(MovePath {
            key: Some(key.clone()),
            parent,
            children: Vec::new(),
        });
        if let Some(p) = parent {
            self.paths[p].children.push(i);
        }
        self.by_key.insert(key, i);
        i
    }

    /// The longest path prefix of `place`, and whether it is all of it.
    fn key(&self, tcx: &Tcx, b: &Body, place: Place) -> (Vec<MoveStep>, bool) {
        let projs = b.projs(place);
        let mut ty = PlaceTy::of(b.locals[place.local].ty);
        let mut steps = Vec::new();
        let mut i = 0;
        while i < projs.len() {
            let this_obj = i == 0
                && place.local == Local(1)
                && (self.move_method || self.ctor_fields.is_some());
            let step = match (projs[i], projs.get(i + 1)) {
                (Proj::Deref, _) if this_obj => None,
                (Proj::Field(f), _) => Some(MoveStep::Field(f)),
                (Proj::ConstIndex(k), _) if matches!(tcx.kind(ty.ty), TyKind::Tuple(_)) => {
                    Some(MoveStep::Field(FieldIdx::new(k as usize)))
                }
                (Proj::Variant(v), Some(&Proj::Field(f))) => {
                    ty = ty.project(tcx, projs[i]).expect("a typed place");
                    i += 1;
                    Some(MoveStep::VariantField(v, f))
                }
                _ => return (steps, false),
            };
            steps.extend(step);
            ty = ty.project(tcx, projs[i]).expect("a typed place");
            i += 1;
        }
        (steps, true)
    }

    /// The effects and exemptions of `new`, `super(...)`, the named-form shim and
    /// a field initialiser's `overridden(f)` switch.
    fn receivers(&mut self, tcx: &Tcx, b: &Body, class: Option<&enrang_hir::ClassDef>) {
        for (bb, block) in b.blocks.iter_enumerated() {
            let at = b.terminator_point(bb);
            let mut fx = Vec::new();
            match &block.term.kind {
                TerminatorKind::Call { callee, args, .. } => {
                    let arg0 = args
                        .first()
                        .and_then(Operand::place)
                        .filter(|p| p.is_local());
                    let def0 = arg0.and_then(|p| def_of(b, at, p.local));
                    let init_fields = |md: &MoveData, all: bool| {
                        let own = class.map_or(0, |c| c.own_from as usize);
                        let fields = md.ctor_fields.iter().flatten();
                        fields
                            .filter(|f| f.0.index() < own)
                            .filter(|f| {
                                let fd = &class.expect("a class").fields[f.0.index()];
                                all || fd.has_default || type_default(tcx, fd.ty)
                            })
                            .map(|f| (f.1, Effect::Init))
                            .collect::<Vec<_>>()
                    };
                    match (callee, def0) {
                        (Callee::Fn(f), Some((q, Rvalue::Ref { place, origin })))
                            if tcx.def(f.def).kind == DefKind::Ctor
                                && *origin == BorrowOrigin::AutoBorrow =>
                        {
                            self.exempt.insert(q);
                            if let Some(&(n, true)) = self.lookup.get(place) {
                                fx.push((n, Effect::Init));
                            }
                        }
                        (Callee::Fn(f), Some((q, Rvalue::Convert(ConvKind::Upcast, op))))
                            if tcx.def(f.def).kind == DefKind::Ctor =>
                        {
                            self.exempt.insert(q);
                            let def = op
                                .place()
                                .filter(|t| t.is_local())
                                .and_then(|t| def_of(b, q, t.local));
                            match def {
                                // `new D(..)` of a class with no constructor of its
                                // own: the base's runs on `&dest` after the inlined
                                // synthesised one's stores (c.10, A:939). A `new`,
                                // never a `super(...)`.
                                Some((
                                    r,
                                    Rvalue::Ref {
                                        place,
                                        origin: BorrowOrigin::AutoBorrow,
                                    },
                                )) if !b.projs(*place).contains(&Proj::Deref) => {
                                    self.exempt.insert(r);
                                    self.exempt.extend(inlined_stores(b, r, *place));
                                    if let Some(&(n, true)) = self.lookup.get(place) {
                                        fx.push((n, Effect::Init));
                                    }
                                }
                                // `super(...)`: of `&*_1 [reborrow]` in a
                                // constructor, or misplaced (an arrow's unassigned
                                // `this`), EN0619 there.
                                def => {
                                    if let Some((r, Rvalue::Ref { place, .. })) = def
                                        && place.local == Local(1)
                                    {
                                        self.exempt.insert(r);
                                    }
                                    self.supers.insert(at);
                                    fx.extend(self.super_path.map(|s| (s, Effect::Init)));
                                    fx.extend(init_fields(self, true));
                                }
                            }
                        }
                        (Callee::ImplicitCtor { .. }, _) => {
                            self.supers.insert(at);
                            fx.extend(self.super_path.map(|s| (s, Effect::Init)));
                            fx.extend(init_fields(self, false));
                        }
                        (Callee::NamedFill { left_out, .. }, Some((_, Rvalue::AddrOf(dest)))) => {
                            if let Some(&(n, true)) = self.lookup.get(dest) {
                                fx.push((n, Effect::Init));
                                for &c in &self.paths[n].children {
                                    if let Some(MoveStep::Field(f)) =
                                        self.paths[c].key.as_ref().and_then(|k| k.steps.last())
                                        && !left_out.contains(f)
                                    {
                                        fx.push((c, Effect::Kill));
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
                TerminatorKind::Switch {
                    value: Operand::Copy(v) | Operand::Move(v),
                    otherwise: Some(missing),
                    ..
                } => {
                    // `lt(copy #supplied, const k + 1)`: declared parameter k,
                    // after `this`, was left out (c.10's `param_defaults`).
                    if let Some((_, Rvalue::Binary(BinOp::Lt, Operand::Copy(n), limit))) =
                        def_of(b, at, v.local)
                        && Some(n.local) == b.meta.defaults_count
                        && let Operand::Const(c) = limit
                        && let ConstKind::Value(ConstValue::Int(k, _)) = c.kind
                        && k >= 1
                    {
                        let this = owner_def(b).is_some_and(|d| tcx.takes_this(d));
                        let param = Local((usize::from(this) + k as usize) as u32);
                        self.defaults.insert((*missing, param));
                    }
                }
                TerminatorKind::Switch {
                    value: Operand::Const(c),
                    ..
                } => {
                    if let ConstKind::Value(ConstValue::Overridden(f)) = c.kind
                        && let Some(fields) = &self.ctor_fields
                        && let Some(&(_, n, ..)) = fields.iter().find(|x| x.0 == f)
                    {
                        fx.push((n, Effect::Init));
                    }
                }
                _ => {}
            }
            if !fx.is_empty() {
                self.effects.insert(at, fx);
            }
        }
    }

    /// Whether `a` is `n` or one of its ancestors.
    pub fn is_prefix(&self, a: MovePathIdx, n: MovePathIdx) -> bool {
        let mut cur = Some(n);
        while let Some(c) = cur {
            if c == a {
                return true;
            }
            cur = self.paths[c].parent;
        }
        false
    }

    /// `n` and its descendants, preorder.
    pub fn subtree(&self, n: MovePathIdx) -> Vec<MovePathIdx> {
        let mut out = vec![n];
        let mut i = 0;
        while i < out.len() {
            out.extend(self.paths[out[i]].children.iter().copied());
            i += 1;
        }
        out
    }

    /// The root path of local `l`.
    pub fn root(&self, l: Local) -> MovePathIdx {
        self.by_key[&MovePathKey {
            local: l,
            steps: Vec::new(),
        }]
    }
}
