//! Drop elaboration (A:595-605; M3 plan d.12; owner 2D): on `Built` MIR with the
//! init states of `check`, each `Drop(p)` becomes nothing (definitely uninit), a
//! `DropGlue(p)` (definitely init, no child moved), a `DropGlue` guarded by a
//! drop flag (maybe init), or a ladder over what is left: a class's fields in
//! reverse declaration order, an enum's active case behind a `switch` on its tag
//! (A:603). A flag is set where its path is initialised and cleared where it or a
//! parent is moved or killed; a constructor's field a class below may override
//! starts from `overridden(f)`. A constant literal view nothing writes through
//! becomes `const static_addr(literal#k)` and loses its temporary (A:970, plan
//! d.12's choice). `Body.drop_flags` records each flag's path.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};

use enrang_base::{BitSet, IdVec};
use enrang_hir::{ConstTree, ConstValue, FieldIdx, Tcx, Ty, TyKind, VariantIdx};
use enrang_mir::{
    AggregateKind, Block, BlockId, Body, BorrowOrigin, Cfg, ConstKind, Constant, LiteralStatic,
    Local, LocalDecl, LocalKind, MirPhase, MoveStep, Operand, Place, PlaceTy, Point, Proj, Rvalue,
    Statement, StatementKind, Terminator, TerminatorKind, tag_value,
};

use crate::BorrowFacts;
use crate::init::{InitResults, effects, entry};
use crate::movepaths::{Effect, MoveData, MovePathIdx, def_of};

/// What a `Drop` becomes, its places as projections of the dropped local.
enum Tree {
    Glue(Vec<Proj>),
    /// `if flag(n) { .. }`.
    Flag(MovePathIdx, Vec<Tree>),
    /// `switch discriminant(place)`, one arm per case with something to drop.
    Tag(Vec<Proj>, Ty, Vec<(VariantIdx, Vec<Tree>)>),
}

pub fn elaborate(tcx: &Tcx, mut b: Body, facts: &BorrowFacts) -> Body {
    let mut views = facts.static_views.clone();
    // The move paths and init states of `check`, or, when the entry block must
    // be split first (or `facts` were never computed), of the body as it is.
    let split = !Cfg::new(&b).preds[BlockId::ENTRY].is_empty();
    if split {
        let moved = split_entry(&mut b);
        let fix = |p: Point| match p.block == BlockId::ENTRY {
            true => Point::new(moved, p.index as usize),
            false => p,
        };
        views = views.into_iter().map(fix).collect();
    }
    let (md, init) = match split || facts.moves.lookup.is_empty() {
        true => {
            let md = MoveData::build(tcx, &b);
            let init = InitResults::compute(&b, &md);
            (Cow::Owned(md), Cow::Owned(init))
        }
        false => (Cow::Borrowed(&facts.moves), Cow::Borrowed(&facts.init)),
    };
    let (statics, dead, literals) = literal_statics(&b, &views);
    let mut plans: BTreeMap<Point, Vec<Tree>> = BTreeMap::new();
    init.replay(&b, &md, |p, i, u| {
        if let Some(StatementKind::Drop(pl, _)) = b.stmt_at(p).map(|s| &s.kind)
            && !dead.contains(&p)
        {
            let pt = b.place_ty(tcx, *pl).expect("a typed place");
            let tree = match md.lookup.get(pl) {
                Some(&(n, true)) => decide(tcx, &md, b.projs(*pl).to_vec(), pt, n, i, u),
                _ => vec![Tree::Glue(b.projs(*pl).to_vec())],
            };
            plans.insert(p, tree);
        }
    });
    let mut flagged = BTreeSet::new();
    plans.values().for_each(|t| flags_of(t, &mut flagged));
    let bool_ty = tcx.common().bool;
    let flags: BTreeMap<MovePathIdx, Local> = flagged
        .iter()
        .map(|&n| {
            (
                n,
                b.locals
                    .push(LocalDecl::new(bool_ty, LocalKind::DropFlag, b.span)),
            )
        })
        .collect();
    b.drop_flags = flags
        .iter()
        .map(|(n, l)| {
            (
                *l,
                md.paths[*n].key.clone().expect("a dropped path has a key"),
            )
        })
        .collect();
    let updates = updates(&b, &md, &init, &flags);
    let entry_sets = entry(&b, &md).0;
    let set = |l: Local, v: ConstValue, span, region| {
        let value = Rvalue::Use(Operand::constant(v, bool_ty));
        let dest = Place::local(l);
        let mut st = Statement::new(StatementKind::Assign { dest, value }, span);
        st.region = region;
        st
    };
    let mut entry_init: Vec<Statement> = Vec::new();
    for (&n, &l) in &flags {
        let field = md.ctor_fields.iter().flatten().find(|f| f.1 == n && f.3);
        let v = match field {
            Some(f) => ConstValue::Overridden(f.0),
            None => ConstValue::Bool(entry_sets.contains(n)),
        };
        entry_init.push(set(l, v, b.span, None));
    }
    let old = std::mem::take(&mut b.blocks);
    let unreachable = Terminator::new(TerminatorKind::Unreachable, b.span);
    let mut e = Emit {
        blocks: IdVec::from_elem(
            Block {
                stmts: Vec::new(),
                term: unreachable,
            },
            old.len(),
        ),
        cur: BlockId::ENTRY,
        stmts: std::mem::take(&mut entry_init),
    };
    let mut map: BTreeMap<Point, Point> = BTreeMap::new();
    for (i, block) in old.into_iter().enumerate() {
        let bb = BlockId(i as u32);
        if bb != BlockId::ENTRY {
            e.cur = bb;
        }
        let ups = |q: Point, span, region| -> Vec<Statement> {
            let ups = updates.get(&q).into_iter().flatten();
            ups.map(|&(l, v)| set(l, ConstValue::Bool(v), span, region))
                .collect()
        };
        let n = block.stmts.len();
        for (idx, mut st) in block.stmts.into_iter().enumerate() {
            let q = Point::new(bb, idx);
            map.insert(q, Point::new(e.cur, e.stmts.len()));
            if dead.contains(&q) {
                continue;
            }
            let (span, region) = (st.span, st.region);
            if let Some(trees) = plans.remove(&q) {
                let StatementKind::Drop(pl, _) = st.kind else {
                    unreachable!("a plan is made for a drop")
                };
                e.lower(tcx, &mut b, &flags, pl.local, &trees, &st);
            } else {
                if let Some(&k) = statics.get(&q)
                    && let StatementKind::Assign { dest, value } = &mut st.kind
                {
                    let ty = b.locals[dest.local].ty;
                    let kind = ConstKind::LiteralAddr(k);
                    *value = Rvalue::Use(Operand::Const(Box::new(Constant { kind, ty })));
                }
                e.stmts.push(st);
            }
            e.stmts.extend(ups(q, span, region));
        }
        let tq = Point::new(bb, n);
        map.insert(tq, Point::new(e.cur, e.stmts.len()));
        let mut term = block.term;
        let after = ups(tq, term.span, term.region);
        match &mut term.kind {
            TerminatorKind::Call { next, .. } if next.is_some() && !after.is_empty() => {
                let mut goto =
                    Terminator::new(TerminatorKind::Goto(next.expect("a next")), term.span);
                goto.region = term.region;
                *next = Some(e.blocks.push(Block {
                    stmts: after,
                    term: goto,
                }));
            }
            _ => e.stmts.extend(after),
        }
        e.finish(term);
    }
    b.blocks = e.blocks;
    let remap = |p: &mut Point| *p = map.get(p).copied().unwrap_or(*p);
    b.meta.loops.iter_mut().for_each(|l| remap(&mut l.bind));
    b.meta.records.iter_mut().for_each(|r| remap(&mut r.at));
    b.meta
        .narrowed_uses
        .iter_mut()
        .for_each(|u| remap(&mut u.1));
    b.meta.assign_values.iter_mut().for_each(remap);
    b.literals = literals;
    b.phase = MirPhase::Elaborated;
    b
}

/// The rewrite of one `Drop` of the path `n` at the place `projs`, of type `pt`.
fn decide(
    tcx: &Tcx,
    md: &MoveData,
    projs: Vec<Proj>,
    pt: PlaceTy,
    n: MovePathIdx,
    i: &BitSet<MovePathIdx>,
    u: &BitSet<MovePathIdx>,
) -> Vec<Tree> {
    let sub = md.subtree(n);
    if sub.iter().all(|&m| !i.contains(m)) {
        return Vec::new();
    }
    if sub.iter().all(|&m| !u.contains(m)) {
        return vec![Tree::Glue(projs)];
    }
    let inner = match sub[1..].iter().any(|&m| u.contains(m)) {
        true => ladder(tcx, md, projs, pt, n, i, u),
        false => vec![Tree::Glue(projs)],
    };
    match u.contains(n) {
        true => vec![Tree::Flag(n, inner)],
        false => inner,
    }
}

/// What is left of a partly moved value: its fields in reverse order, behind a
/// `switch` on the tag for an enum or a nullable.
fn ladder(
    tcx: &Tcx,
    md: &MoveData,
    projs: Vec<Proj>,
    pt: PlaceTy,
    n: MovePathIdx,
    i: &BitSet<MovePathIdx>,
    u: &BitSet<MovePathIdx>,
) -> Vec<Tree> {
    let key = md.paths[n].key.clone().expect("a dropped path has a key");
    let field = |variant: Option<VariantIdx>, count: usize| -> Vec<Tree> {
        let mut out = Vec::new();
        for f in (0..count).rev().map(|f| FieldIdx(f as u32)) {
            let (step, mut fp, base) = match variant {
                Some(v) => (
                    MoveStep::VariantField(v, f),
                    vec![Proj::Variant(v)],
                    PlaceTy {
                        ty: pt.ty,
                        variant: Some(v),
                    },
                ),
                None => (MoveStep::Field(f), Vec::new(), pt),
            };
            fp.splice(0..0, projs.iter().copied());
            fp.push(Proj::Field(f));
            let fpt = base.project(tcx, Proj::Field(f)).expect("a field");
            let mut k = key.clone();
            k.steps.push(step);
            match md.by_key.get(&k) {
                Some(&c) => out.extend(decide(tcx, md, fp, fpt, c, i, u)),
                None if tcx.needs_drop(fpt.ty) => out.push(Tree::Glue(fp)),
                None => {}
            }
        }
        out
    };
    match tcx.kind(pt.ty) {
        TyKind::Adt(adt, _) if tcx.adt(adt).is_enum() => {
            let cases = &tcx.adt(adt).as_enum().expect("an enum").variants;
            let arms = (0..cases.len())
                .map(|v| {
                    (
                        VariantIdx(v as u32),
                        field(Some(VariantIdx(v as u32)), cases[v].fields.len()),
                    )
                })
                .filter(|a| !a.1.is_empty())
                .collect();
            vec![Tree::Tag(projs, pt.ty, arms)]
        }
        TyKind::Nullable(_) => {
            let arm = field(Some(VariantIdx::PRESENT), 1);
            vec![Tree::Tag(projs, pt.ty, vec![(VariantIdx::PRESENT, arm)])]
        }
        TyKind::Adt(adt, _) => field(None, tcx.adt(adt).as_class().map_or(0, |c| c.fields.len())),
        TyKind::Tuple(parts) => field(None, tcx.list(parts).len()),
        // An anonymous object: its fields in shape order, as a class's (D4).
        TyKind::Object(s) => field(None, tcx.shape(s).fields.len()),
        _ => vec![Tree::Glue(projs)],
    }
}

fn flags_of(trees: &[Tree], out: &mut BTreeSet<MovePathIdx>) {
    for t in trees {
        match t {
            Tree::Glue(_) => {}
            Tree::Flag(n, inner) => {
                out.insert(*n);
                flags_of(inner, out);
            }
            Tree::Tag(_, _, arms) => arms.iter().for_each(|a| flags_of(&a.1, out)),
        }
    }
}

/// The flag values each point leaves: the last effect on a flagged path's own
/// bit (its own or a parent's init, move or kill).
fn updates(
    b: &Body,
    md: &MoveData,
    init: &InitResults,
    flags: &BTreeMap<MovePathIdx, Local>,
) -> BTreeMap<Point, Vec<(Local, bool)>> {
    let mut out = BTreeMap::new();
    if flags.is_empty() {
        return out;
    }
    init.replay(b, md, |p, _, _| {
        let fx = effects(b, md, p);
        let ups: Vec<(Local, bool)> = flags
            .iter()
            .filter_map(|(&n, &l)| {
                let last = fx.iter().rev().find(|(m, _)| md.is_prefix(*m, n))?;
                Some((l, last.1 == Effect::Init))
            })
            .collect();
        if !ups.is_empty() {
            out.insert(p, ups);
        }
    });
    out
}

/// The blocks being rebuilt: the current one's statements so far.
struct Emit {
    blocks: IdVec<BlockId, Block>,
    cur: BlockId,
    stmts: Vec<Statement>,
}

impl Emit {
    fn finish(&mut self, term: Terminator) {
        let stmts = std::mem::take(&mut self.stmts);
        self.blocks[self.cur] = Block { stmts, term };
    }

    /// Ends the current block with `term` and continues in a new one.
    fn branch(&mut self, term: TerminatorKind, st: &Statement) {
        let mut t = Terminator::new(term, st.span);
        t.region = st.region;
        self.finish(t);
    }

    fn new_block(&mut self, st: &Statement) -> BlockId {
        self.blocks.push(Block {
            stmts: Vec::new(),
            term: Terminator::new(TerminatorKind::Unreachable, st.span),
        })
    }

    fn lower(
        &mut self,
        tcx: &Tcx,
        b: &mut Body,
        flags: &BTreeMap<MovePathIdx, Local>,
        root: Local,
        trees: &[Tree],
        st: &Statement,
    ) {
        for t in trees {
            match t {
                Tree::Glue(projs) => {
                    let place = b.place(root, projs);
                    let mut s = Statement::new(StatementKind::DropGlue(place), st.span);
                    s.region = st.region;
                    self.stmts.push(s);
                }
                Tree::Flag(n, inner) => {
                    let (then, join) = (self.new_block(st), self.new_block(st));
                    let value = Operand::Copy(Place::local(flags[n]));
                    self.branch(
                        TerminatorKind::Switch {
                            value,
                            arms: vec![(0, join)],
                            otherwise: Some(then),
                        },
                        st,
                    );
                    self.cur = then;
                    self.lower(tcx, b, flags, root, inner, st);
                    self.branch(TerminatorKind::Goto(join), st);
                    self.cur = join;
                }
                Tree::Tag(projs, ty, arms) => {
                    let place = b.place(root, projs);
                    let d =
                        b.locals
                            .push(LocalDecl::new(tcx.common().u32, LocalKind::Temp, st.span));
                    let mut s = Statement::new(
                        StatementKind::Assign {
                            dest: Place::local(d),
                            value: Rvalue::Discriminant(place),
                        },
                        st.span,
                    );
                    s.region = st.region;
                    self.stmts.push(s);
                    let join = self.new_block(st);
                    let targets: Vec<BlockId> = arms.iter().map(|_| self.new_block(st)).collect();
                    let tags = arms.iter().zip(&targets);
                    let tags = tags
                        .map(|((v, _), &t)| (tag_value(tcx, *ty, *v), t))
                        .collect();
                    self.branch(
                        TerminatorKind::Switch {
                            value: Operand::Move(Place::local(d)),
                            arms: tags,
                            otherwise: Some(join),
                        },
                        st,
                    );
                    for ((_, inner), t) in arms.iter().zip(targets) {
                        self.cur = t;
                        self.lower(tcx, b, flags, root, inner, st);
                        self.branch(TerminatorKind::Goto(join), st);
                    }
                    self.cur = join;
                }
            }
        }
    }
}

/// Moves the entry block's code to a new block, so that bb0 has no predecessor
/// and the flags' entry values run once.
fn split_entry(b: &mut Body) -> BlockId {
    let entry = std::mem::replace(
        &mut b.blocks[BlockId::ENTRY],
        Block {
            stmts: Vec::new(),
            term: Terminator::new(TerminatorKind::Unreachable, b.span),
        },
    );
    let moved = b.blocks.push(entry);
    for block in b.blocks.iter_mut() {
        for s in block.term.kind.successors_mut() {
            if *s == BlockId::ENTRY {
                *s = moved;
            }
        }
    }
    b.blocks[BlockId::ENTRY].term = Terminator::new(TerminatorKind::Goto(moved), b.span);
    let fix = |x: &mut BlockId| {
        if *x == BlockId::ENTRY {
            *x = moved;
        }
    };
    for l in &mut b.meta.loops {
        fix(&mut l.preheader);
        fix(&mut l.head);
        fix(&mut l.bind.block);
    }
    b.meta.records.iter_mut().for_each(|r| fix(&mut r.at.block));
    b.meta
        .narrowed_uses
        .iter_mut()
        .for_each(|u| fix(&mut u.1.block));
    b.meta.fact_tests.iter_mut().for_each(|t| fix(&mut t.1));
    b.meta
        .assign_values
        .iter_mut()
        .for_each(|p| fix(&mut p.block));
    moved
}

/// The constant literal views nothing writes through, `views`, the `Ref`s whose
/// loan `check` found shared (N4, A:970): each `Ref`'s point and literal number,
/// the points of its temporary's construction, storage and drop, and the
/// literals.
fn literal_statics(
    b: &Body,
    views: &BTreeSet<Point>,
) -> (BTreeMap<Point, u32>, BTreeSet<Point>, Vec<LiteralStatic>) {
    let (mut refs, mut dead, mut literals) = (BTreeMap::new(), BTreeSet::new(), Vec::new());
    for (bb, block) in b.blocks.iter_enumerated() {
        for (idx, st) in block.stmts.iter().enumerate() {
            let q = Point::new(bb, idx);
            let StatementKind::Assign {
                value:
                    Rvalue::Ref {
                        place: t,
                        origin: BorrowOrigin::LiteralView,
                    },
                ..
            } = &st.kind
            else {
                continue;
            };
            let Some((dq, Rvalue::Aggregate(AggregateKind::Fixed(_), ops))) = def_of(b, q, t.local)
            else {
                continue;
            };
            let items: Option<Vec<ConstTree>> = ops
                .iter()
                .map(|o| match o {
                    Operand::Const(c) => match c.kind {
                        ConstKind::Value(v) => Some(ConstTree::Scalar(v)),
                        ConstKind::LiteralAddr(_) => None,
                    },
                    _ => None,
                })
                .collect();
            let (Some(items), true) = (items, t.is_local() && views.contains(&q)) else {
                continue;
            };
            refs.insert(q, literals.len() as u32);
            literals.push(LiteralStatic {
                ty: b.locals[t.local].ty,
                value: ConstTree::Array(items),
            });
            dead.insert(dq);
            for (bb2, block2) in b.blocks.iter_enumerated() {
                for (i2, s2) in block2.stmts.iter().enumerate() {
                    let gone = match s2.kind {
                        StatementKind::StorageLive(l) | StatementKind::StorageDead(l) => {
                            l == t.local
                        }
                        StatementKind::Drop(p, _) => p == *t,
                        _ => false,
                    };
                    if gone {
                        dead.insert(Point::new(bb2, i2));
                    }
                }
            }
        }
    }
    (refs, dead, literals)
}
