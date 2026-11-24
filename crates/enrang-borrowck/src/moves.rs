//! Move and init reports (A:987-1007; M3 plan d.2; owner 2D): EN0601-EN0605,
//! EN0607, EN0610, EN0611, EN0613, EN0617, EN0618, EN0619, EN0621.
//!
//! Each use of a path that may be uninitialised is reported once per set of move
//! sites reaching it (A:1007): EN0611 when a site reaches it around a back edge,
//! else EN0601, EN0602 when none does. Uses rooted at a temporary or the return
//! slot are never reported: no user path names them, and compiler-built MIR reads
//! them only once they hold a value.

use std::collections::{BTreeMap, BTreeSet};

use enrang_base::{BitSet, Span};
use enrang_diag::Code;
use enrang_mir::{
    BlockId, Body, BodyOwner, BorrowOrigin, Callee, Cfg, DropOrigin, Local, LocalKind, LoopRole,
    LoopSource, Operand, Place, PlaceTy, Point, Proj, Rvalue, StatementKind, TerminatorKind,
};

use crate::cx::BodyCx;
use crate::init::{InitResults, effects, point_dests, point_operands, unset};
use crate::marks::{MarkOrigin, frozen};
use crate::movepaths::{Effect, MoveData, MovePathIdx};
use enrang_hir::{Tcx, TyKind};

/// A use the init states reject.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MoveError {
    pub code: Code,
    pub path: MovePathIdx,
    pub at: Point,
    pub span: Span,
    /// The move sites that reach the use, first in source order.
    pub moved_at: Vec<Span>,
}

/// Every move and init error of `cx.body`, in point order.
pub fn check(cx: &BodyCx, init: &InitResults) -> Vec<MoveError> {
    let md = &cx.moves;
    let mut c = Checker {
        tcx: cx.tcx,
        b: cx.body,
        md,
        cfg: Cfg::new(cx.body),
        errors: Vec::new(),
        uses: Vec::new(),
        again: Vec::new(),
    };
    init.replay(cx.body, md, |p, i, u| c.point(p, i, u));
    c.finish()
}

struct Checker<'a> {
    tcx: &'a Tcx,
    b: &'a Body,
    md: &'a MoveData,
    cfg: Cfg,
    errors: Vec<MoveError>,
    /// Uses of a path that may be uninit: point, path, and the paths that make
    /// it so, the maybe-uninit ancestors (or itself) and, for a whole use, the
    /// topmost maybe-uninit descendants.
    uses: Vec<(Point, MovePathIdx, Vec<MovePathIdx>)>,
    /// Uses of a path that an earlier operand of the same point moved, the use's
    /// span narrowed past that operand: `both(s, s)`, `[s, s]` (S 5).
    again: Vec<(Point, MovePathIdx, Span)>,
}

/// The span of the statement or terminator at `p`.
pub(crate) fn span_at(b: &Body, p: Point) -> Span {
    b.stmt_at(p).map_or(b.blocks[p.block].term.span, |s| s.span)
}

impl Checker<'_> {
    fn err(&mut self, code: Code, path: MovePathIdx, at: Point) {
        let span = span_at(self.b, at);
        self.errors.push(MoveError {
            code,
            path,
            at,
            span,
            moved_at: Vec::new(),
        });
    }

    fn point(&mut self, p: Point, i: &BitSet<MovePathIdx>, u: &BitSet<MovePathIdx>) {
        let (b, md) = (self.b, self.md);
        let kept = b.meta.assign_values.contains(&p);
        if !kept && !md.exempt.contains(&p) {
            self.moved_twice(p);
        }
        for op in point_operands(b, p) {
            if let Operand::Move(pl) = op {
                match kept {
                    true => self.err(Code::EN0621, md.lookup[pl].0, p),
                    false => self.moved(p, *pl),
                }
            }
        }
        if !md.exempt.contains(&p) {
            for (pl, hidden, tag) in reads(b, p) {
                self.read(p, pl, hidden, tag, u);
            }
        }
        // A `new`'s own stores into its destination are exempt with its borrow.
        for d in point_dests(b, p)
            .into_iter()
            .filter(|_| !md.exempt.contains(&p))
        {
            let field_init = matches!(
                b.stmt_at(p).map(|s| &s.kind),
                Some(StatementKind::FieldInit { .. })
            );
            self.write(p, d, field_init, i, u);
        }
        if let Some(StatementKind::Drop(d, DropOrigin::Assign)) = b.stmt_at(p).map(|s| &s.kind) {
            self.frozen_write(p, *d, i);
        }
        let ctor = md.ctor_fields.as_deref();
        if md.supers.contains(&p) {
            match (ctor, md.super_path) {
                (Some(_), Some(s)) if i.contains(s) => self.err(Code::EN0619, s, p),
                (Some(fields), Some(_)) => {
                    if let Some(f) = fields.iter().find(|f| f.2 && u.contains(f.1)) {
                        self.err(Code::EN0610, f.1, p);
                    }
                }
                _ => self.err(Code::EN0619, md.root(Local(1)), p),
            }
        }
        if let (Some(_), None, TerminatorKind::Return) =
            (ctor, b.stmt_at(p), &b.blocks[p.block].term.kind)
        {
            self.this_use(p, u, Code::EN0619);
        }
    }

    /// The operands of one point run in order, so a path an earlier operand moved
    /// is moved for the later ones: `both(s, s)` moves `s` twice, and `f(p, p.n)`
    /// reads a part of the moved `p`, each a use after the move (S 5). The use's
    /// span starts past the first operand that names the path's local, so the
    /// report narrows to the later operand.
    fn moved_twice(&mut self, p: Point) {
        let (b, md) = (self.b, self.md);
        let mut moved: Vec<MovePathIdx> = Vec::new();
        for op in point_operands(b, p) {
            let Some(pl) = op.place() else {
                continue;
            };
            let Some(&(n, _)) = md.lookup.get(&pl) else {
                continue;
            };
            if moved
                .iter()
                .any(|&m| md.is_prefix(m, n) || md.is_prefix(n, m))
            {
                let span = span_at(b, p);
                let name = b.locals[pl.local].name.map(|s| s.to_string());
                let first = name
                    .as_deref()
                    .and_then(|w| crate::report::word_in(self.tcx.map(), span, w));
                let span = first.map_or(span, |f| Span {
                    lo: f.hi,
                    hi: span.hi,
                });
                if !self.again.iter().any(|a| a.0 == p && a.1 == n) {
                    self.again.push((p, n, span));
                }
            }
            if let Operand::Move(_) = op {
                moved.push(n);
            }
        }
    }

    /// A use of a constructor's `this` (A:998): before `super(...)`, EN0610 (or
    /// `at_super`, EN0619 at an exit); then every field must be set, EN0610.
    fn this_use(&mut self, p: Point, u: &BitSet<MovePathIdx>, at_super: Code) {
        let md = self.md;
        if let Some(s) = md.super_path.filter(|&s| u.contains(s)) {
            return self.err(at_super, s, p);
        }
        let fields = md.ctor_fields.iter().flatten();
        if let Some(f) = fields.clone().find(|f| u.contains(f.1)) {
            self.err(Code::EN0610, f.1, p);
        }
    }

    /// A field of a constructor's `this` read: once `super(...)` ran and the
    /// field is set (S 4.3).
    fn this_field(&mut self, p: Point, n: MovePathIdx, whole: bool, u: &BitSet<MovePathIdx>) {
        let md = self.md;
        let missing = md.super_path.filter(|&s| u.contains(s));
        if let Some(m) = missing.or_else(|| unset(md, u, n, whole)) {
            self.err(Code::EN0610, m, p);
        }
    }

    /// A read of `pl`; a tag read (`check_tag`, `discriminant`) is shallow: the
    /// tag stays in the place when its payload's parts are moved out, so it
    /// needs `pl` and its prefixes initialised, never its children (d.14.23).
    fn read(&mut self, p: Point, pl: Place, hidden: bool, tag: bool, u: &BitSet<MovePathIdx>) {
        let md = self.md;
        let (n, whole) = md.lookup[&pl];
        let whole = whole && !tag;
        if md.ctor_fields.is_some() && pl.local == Local(1) {
            return match self.b.projs(pl) {
                [Proj::Deref, Proj::Field(_), ..] => self.this_field(p, n, whole, u),
                _ => self.this_use(p, u, Code::EN0610),
            };
        }
        if unset(md, u, n, whole).is_some() {
            // EN0618 is for a call above a variable it reads (N13): one declared
            // above the call, moved or never assigned, is read like any path
            // (EN0601, EN0602).
            match hidden && self.undeclared_at(pl.local, p) {
                true => self.err(Code::EN0618, n, p),
                false => self.uses.push((p, n, causes(md, u, n, whole))),
            }
        }
    }

    /// Whether some path from the entry reaches `p` before `l`'s `StorageLive`,
    /// its declaration: a call there runs above the variable (EN0618). A local
    /// with no `StorageLive` is declared where the body starts.
    fn undeclared_at(&self, l: Local, p: Point) -> bool {
        let b = self.b;
        let lives = |bb: BlockId, end: usize| {
            (b.blocks[bb].stmts[..end].iter())
                .any(|s| matches!(s.kind, StatementKind::StorageLive(x) if x == l))
        };
        if !(b.blocks.iter_enumerated()).any(|(bb, x)| lives(bb, x.stmts.len())) {
            return false;
        }
        let mut seen = BTreeSet::new();
        let mut work = vec![(p.block, p.index as usize)];
        while let Some((bb, end)) = work.pop() {
            if lives(bb, end) {
                continue;
            }
            if bb == BlockId::ENTRY {
                return true;
            }
            for &q in &self.cfg.preds[bb] {
                if seen.insert(q) {
                    work.push((q, b.blocks[q].stmts.len()));
                }
            }
        }
        false
    }

    fn write(
        &mut self,
        p: Point,
        d: Place,
        field_init: bool,
        i: &BitSet<MovePathIdx>,
        u: &BitSet<MovePathIdx>,
    ) {
        let (b, md) = (self.b, self.md);
        if d.is_local() {
            let after_drop = p.index > 0
                && matches!(&b.blocks[p.block].stmts.get(p.index as usize - 1).map(|s| &s.kind),
                    Some(StatementKind::Drop(x, DropOrigin::Assign)) if *x == d);
            if !after_drop {
                self.frozen_write(p, d, i);
            }
            return;
        }
        if let Some(fields) = md.ctor_fields.as_deref()
            && d.local == Local(1)
        {
            return match b.projs(d) {
                [Proj::Deref, Proj::Field(f), rest @ ..] if !rest.contains(&Proj::Deref) => {
                    let inherited = fields.iter().any(|x| x.0 == *f && !x.2);
                    if inherited && !field_init && md.super_path.is_some_and(|s| u.contains(s)) {
                        self.err(Code::EN0610, md.lookup[&d].0, p);
                    }
                }
                [Proj::Deref, Proj::Field(_), ..] => self.this_field(p, md.lookup[&d].0, false, u),
                _ => self.this_use(p, u, Code::EN0610),
            };
        }
        // `x.f = v`: a proper prefix not definitely init other than by moves of
        // its own fields; through a deref or an index, the base is read.
        let (n, whole) = md.lookup[&d];
        let target = match whole {
            true => md.paths[n].parent,
            false => Some(n),
        };
        if let Some(t) = target
            && unset(md, u, t, false).is_some()
        {
            self.uses.push((p, t, causes(md, u, t, false)));
        }
    }

    /// EN0613: an assignment to a `const` that may be init, or to a by-value
    /// parameter not marked `let`.
    fn frozen_write(&mut self, p: Point, d: Place, i: &BitSet<MovePathIdx>) {
        if !d.is_local() {
            return;
        }
        let root = self.md.root(d.local);
        match frozen(self.tcx, self.b, d.local) {
            Some(MarkOrigin::ConstRoot(_)) if i.contains(root) => self.err(Code::EN0613, root, p),
            // Only the callee's own store of a left-out parameter's default, in
            // a block its `#supplied` test dominates (A:937).
            Some(MarkOrigin::ByValueParam(_))
                if !self
                    .md
                    .defaults
                    .iter()
                    .any(|&(blk, l)| l == d.local && self.cfg.dominates(blk, p.block)) =>
            {
                self.err(Code::EN0613, root, p)
            }
            _ => {}
        }
    }

    /// The move out of `pl`: EN0603-EN0605 by the last deref or index it crosses,
    /// the one nearest the moved value (`names[0]` through a reference is EN0604,
    /// as `rustc`'s "cannot move out of index"), a box deref only when nothing
    /// before it is a reference or an index; EN0617 out of a capture of an
    /// arrow or a local function's hidden argument; EN0607 out of a class with a
    /// destructor, or out of a type parameter's value, when no deref or index is
    /// crossed.
    fn moved(&mut self, p: Point, pl: Place) {
        let (b, tcx) = (self.b, self.tcx);
        let root = &b.locals[pl.local];
        let hidden = match b.owner {
            BodyOwner::Fn(d) => {
                crate::r3::hidden(tcx, d, b).contains(&(pl.local.0.wrapping_sub(1)))
            }
            _ => false,
        };
        let mut ty = PlaceTy::of(root.ty);
        let (mut code, mut dtor) = (None, false);
        for (k, proj) in b.projs(pl).iter().enumerate() {
            let first = k == 0 && root.kind == LocalKind::Arg;
            let at_this = k == 0 && pl.local == Local(1);
            match (proj, tcx.kind(ty.ty)) {
                (Proj::Deref, TyKind::Ref(_)) if at_this && self.md.move_method => {}
                (Proj::Deref, TyKind::Ref(_))
                    if (at_this && matches!(b.owner, BodyOwner::Arrow(..)))
                        || (first && hidden) =>
                {
                    return self.err(Code::EN0617, self.md.lookup[&pl].0, p);
                }
                (Proj::Deref, TyKind::Ref(_) | TyKind::Raw(_)) => code = Some(Code::EN0603),
                // A box behind a reference or an index is moved out of that.
                (Proj::Deref, TyKind::Boxed(_)) => code = code.or(Some(Code::EN0605)),
                (
                    Proj::Index(_) | Proj::ConstIndex(_),
                    TyKind::Array(_) | TyKind::Slice(_) | TyKind::Fixed(..),
                ) => match root.kind == LocalKind::HiddenLoop(LoopRole::IntoIter) {
                    true => return,
                    false => code = Some(Code::EN0604),
                },
                (Proj::Field(_), TyKind::Adt(adt, args))
                    if ty.variant.is_none() && tcx.class_dtor(adt, args).is_some() =>
                {
                    dtor |= code.is_none();
                }
                // A type parameter's value, an implicit one for an object-type
                // parameter included, may be a class with a destructor or with
                // fields its bound does not list, and the body is checked once for
                // every type (4.10, S:603): no field moves out of it (H41), a
                // `@devMigrate` hook's `old` included until the dev runtime's
                // quarantine of what a hook leaves lands (M6).
                (Proj::Field(_), TyKind::Param(_)) => dtor |= code.is_none(),
                _ => {}
            }
            ty = ty.project(tcx, *proj).expect("a typed place");
        }
        if let Some(code) = code.or(dtor.then_some(Code::EN0607)) {
            self.err(code, self.md.lookup[&pl].0, p);
        }
    }

    /// The moves reaching `p` of each path in `causes` or an ancestor of it, and
    /// whether one does so around a back edge (A:1005). A branch stops at an init
    /// or kill of that path or an ancestor: an earlier move of a field assigned
    /// again since is no site.
    fn sites(
        &self,
        cfg: &Cfg,
        back: &BTreeSet<(BlockId, BlockId)>,
        p: Point,
        causes: &[MovePathIdx],
    ) -> BTreeMap<Point, bool> {
        let (b, md) = (self.b, self.md);
        let mut found: BTreeMap<Point, bool> = BTreeMap::new();
        for &n in causes {
            let mut seen = BTreeSet::new();
            let mut work = vec![(p.block, p.index as usize, false)];
            while let Some((bb, end, crossed)) = work.pop() {
                let stop = (0..end).rev().any(|idx| {
                    let q = Point::new(bb, idx);
                    effects(b, md, q).into_iter().rev().any(|(m, e)| match e {
                        Effect::Move if md.is_prefix(m, n) => {
                            // An earlier turn's only when every path from it
                            // crosses a back edge.
                            found
                                .entry(q)
                                .and_modify(|c| *c &= crossed)
                                .or_insert(crossed);
                            true
                        }
                        Effect::Move => false,
                        Effect::Init | Effect::Kill => md.is_prefix(m, n),
                    })
                });
                if stop {
                    continue;
                }
                for &pr in &cfg.preds[bb] {
                    let c = crossed || back.contains(&(pr, bb));
                    if cfg.reachable.contains(pr) && seen.insert((pr, c)) {
                        work.push((pr, b.blocks[pr].stmts.len() + 1, c));
                    }
                }
            }
        }
        found
    }

    /// One report per set of move sites (A:1007).
    fn finish(mut self) -> Vec<MoveError> {
        let (b, md) = (self.b, self.md);
        let cfg = &self.cfg;
        let back: BTreeSet<_> = cfg.back_edges(b).into_iter().collect();
        let loops = cfg.loops(b);
        // A site set, or for EN0602 the path; its uses and its earlier-turn sites.
        type Group = (Vec<(Span, Point, MovePathIdx)>, BTreeSet<Point>);
        let mut groups: BTreeMap<(Vec<Point>, Option<MovePathIdx>), Group> = BTreeMap::new();
        for (p, n, causes) in &self.uses {
            let (p, n) = (*p, *n);
            let mut root = n;
            while let Some(r) = md.paths[root].parent {
                root = r;
            }
            let local = md.paths[root].key.as_ref().map(|k| k.local);
            if local
                .is_some_and(|l| matches!(b.locals[l].kind, LocalKind::Temp | LocalKind::Return))
            {
                continue;
            }
            let found = self.sites(cfg, &back, p, causes);
            // A move of the loop's own held source, inside that loop, is the
            // hold's EN0709 alone (A:1007); a move of a path beside the source,
            // `h.other` under a hold on `h.items`, is still reported.
            let held_site = |q: &Point| {
                b.meta.loops.iter().any(|l| {
                    let LoopSource::Path(s) = &l.source else {
                        return false;
                    };
                    let Some(&(src, exact)) = md.lookup.get(s) else {
                        return false;
                    };
                    loops
                        .iter()
                        .any(|x| x.head == l.head && x.blocks.contains(q.block))
                        && effects(b, md, *q).iter().any(|&(m, e)| {
                            e == Effect::Move
                                && (md.is_prefix(m, src) || (exact && md.is_prefix(src, m)))
                        })
                })
            };
            let held = !found.is_empty() && found.keys().all(held_site);
            let key = match found.is_empty() {
                true => (Vec::new(), Some(n)),
                false if held => continue,
                false => (found.keys().copied().collect(), None),
            };
            let g = groups.entry(key).or_default();
            g.0.push((span_at(b, p), p, n));
            g.1.extend(found.into_iter().filter(|x| x.1).map(|x| x.0));
        }
        // A path moved by an earlier operand of the same point: that point is the
        // move site, which `sites` cannot see, since it looks before the use.
        for &(p, n, span) in &self.again {
            let mut root = n;
            while let Some(r) = md.paths[root].parent {
                root = r;
            }
            let local = md.paths[root].key.as_ref().map(|k| k.local);
            if local
                .is_some_and(|l| matches!(b.locals[l].kind, LocalKind::Temp | LocalKind::Return))
            {
                continue;
            }
            groups
                .entry((vec![p], None))
                .or_default()
                .0
                .push((span, p, n));
        }
        for ((sites, never), (uses, turn)) in groups {
            let &(span, at, path) = uses
                .iter()
                .min_by_key(|u| (u.0.lo, u.1))
                .expect("a group has a use");
            let mut moved_at: Vec<Span> = sites.iter().map(|&q| span_at(b, q)).collect();
            moved_at.sort_by_key(|s| s.lo);
            let first_turn = turn.iter().map(|&q| span_at(b, q)).min_by_key(|s| s.lo);
            let (code, span) = match (never, first_turn) {
                (Some(_), _) => (Code::EN0602, span),
                (None, Some(t)) => (Code::EN0611, t),
                (None, None) => (Code::EN0601, span),
            };
            self.errors.push(MoveError {
                code,
                path,
                at,
                span,
                moved_at,
            });
        }
        self.errors.sort_by_key(|e| (e.at, e.span.lo));
        self.errors
    }
}

/// The paths that make a use of `n` maybe-uninit: its maybe-uninit ancestors or
/// itself and, for a whole use, each maybe-uninit descendant whose parent is not.
fn causes(md: &MoveData, u: &BitSet<MovePathIdx>, n: MovePathIdx, whole: bool) -> Vec<MovePathIdx> {
    let mut out = Vec::new();
    let mut cur = Some(n);
    while let Some(c) = cur {
        if u.contains(c) {
            out.push(c);
        }
        cur = md.paths[c].parent;
    }
    if whole {
        let below = md.subtree(n).into_iter().skip(1);
        out.extend(
            below.filter(|&d| u.contains(d) && md.paths[d].parent.is_none_or(|q| !u.contains(q))),
        );
    }
    out
}

/// The places a point reads, with whether each is a hidden argument's borrow and
/// whether it reads only a tag.
fn reads(b: &Body, p: Point) -> Vec<(Place, bool, bool)> {
    let mut out: Vec<(Place, bool, bool)> = point_operands(b, p)
        .into_iter()
        .filter_map(|o| Some((o.place()?, false, false)))
        .collect();
    match b.stmt_at(p).map(|s| &s.kind) {
        Some(StatementKind::Assign { value, .. }) => match value {
            Rvalue::Ref { place, origin } => {
                out.push((*place, *origin == BorrowOrigin::HiddenArg, false))
            }
            Rvalue::Discriminant(pl) => out.push((*pl, false, true)),
            Rvalue::Len(pl)
            | Rvalue::ClosureReborrow(pl)
            | Rvalue::ClosureValue { env: pl, .. } => out.push((*pl, false, false)),
            _ => {}
        },
        Some(StatementKind::CheckTag { place, .. }) => out.push((*place, false, true)),
        Some(StatementKind::CheckClass { place, .. }) => out.push((*place, false, false)),
        None => {
            if let TerminatorKind::Call {
                callee: Callee::ClosureLocal(l),
                ..
            } = &b.blocks[p.block].term.kind
            {
                out.push((Place::local(*l), false, false));
            }
        }
        _ => {}
    }
    out
}
