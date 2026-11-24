//! The call graph with class nodes and its SCCs (A:1336; M3 plan d.8; owner 2F).
//!
//! A node per function body of the module and per borrowing class of the module.
//! A function's edges go to each callee with a body in the module (a `Virtual`
//! call to the method it names) and, **choice**, to every class node a type of its
//! locals names (not the classes of those classes' fields), for the classes whose
//! flags it reads (rule (e), its through sets, the read-set check); an arrow's
//! edges are its parent's. A flag read through a nested class's field with no
//! edge comes from the memo of an earlier SCC or stays off for this one. A class's
//! edges go to its methods, constructors and destructor with bodies, and to its
//! base. Tarjan's SCCs, nodes and successors in `ItemPath` order, come out callees
//! first.

use std::collections::{BTreeMap, BTreeSet};

use enrang_hir::{self as hir, AdtId, DefId, DefKind, ItemPath, ModuleId, Tcx, TyKind};
use enrang_mir::{Bodies, Body, BodyOwner, Callee, TerminatorKind};

/// A function or a borrowing class's flag.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Node {
    Fn(DefId),
    Class(AdtId),
}

pub fn path(tcx: &Tcx, n: Node) -> &ItemPath {
    match n {
        Node::Fn(d) => &tcx.def(d).path,
        Node::Class(a) => &tcx.def(tcx.adt(a).def).path,
    }
}

/// The definition whose node a body belongs to.
pub fn owner_def(owner: BodyOwner) -> Option<DefId> {
    match owner {
        BodyOwner::Fn(d) | BodyOwner::Arrow(hir::BodyOwner::Fn(d), _) => Some(d),
        _ => None,
    }
}

/// The modules of `bodies`.
pub fn modules(tcx: &Tcx, bodies: &Bodies) -> BTreeSet<ModuleId> {
    bodies
        .keys()
        .filter_map(|o| match o {
            BodyOwner::Statements(m) => Some(*m),
            BodyOwner::Fn(d) | BodyOwner::Test(d) => Some(tcx.def(*d).module),
            _ => None,
        })
        .collect()
}

/// The borrowing classes of `modules`.
pub fn classes(tcx: &Tcx, modules: &BTreeSet<ModuleId>) -> Vec<AdtId> {
    tcx.adts()
        .filter(|(a, adt)| modules.contains(&tcx.def(adt.def).module) && tcx.is_borrowing_class(*a))
        .map(|(a, _)| a)
        .collect()
}

/// The bodies of class `a`: its methods, constructors, destructor, and the arrows
/// nested in them.
pub fn class_bodies<'b>(tcx: &Tcx, bodies: &'b Bodies, a: AdtId) -> Vec<&'b Body> {
    let def = tcx.adt(a).def;
    bodies
        .values()
        .filter(|b| {
            owner_def(b.owner).is_some_and(|d| {
                tcx.def(d).parent == Some(def)
                    && matches!(
                        tcx.def(d).kind,
                        DefKind::Method | DefKind::Ctor | DefKind::Dtor
                    )
            })
        })
        .collect()
}

fn edges(tcx: &Tcx, bodies: &Bodies, nodes: &BTreeSet<Node>, n: Node) -> Vec<Node> {
    let mut out = BTreeSet::new();
    match n {
        Node::Fn(d) => {
            for b in bodies.values().filter(|b| owner_def(b.owner) == Some(d)) {
                for blk in b.blocks.iter() {
                    if let TerminatorKind::Call {
                        callee: Callee::Fn(f) | Callee::Virtual { method: f, .. },
                        ..
                    } = &blk.term.kind
                    {
                        out.insert(Node::Fn(f.def));
                    }
                }
                for l in b.locals.iter() {
                    tcx.any_ty(l.ty, &mut |_, t| {
                        if let TyKind::Adt(a, _) = tcx.kind(t) {
                            out.insert(Node::Class(a));
                        }
                        false
                    });
                }
            }
        }
        Node::Class(a) => {
            for b in class_bodies(tcx, bodies, a) {
                out.extend(owner_def(b.owner).map(Node::Fn));
            }
            if let Some(TyKind::Adt(base, _)) = tcx
                .adt(a)
                .as_class()
                .and_then(|c| c.base)
                .map(|t| tcx.kind(t))
            {
                out.insert(Node::Class(base));
            }
        }
    }
    let mut out: Vec<Node> = out.into_iter().filter(|m| nodes.contains(m)).collect();
    out.sort_by(|x, y| path(tcx, *x).cmp(path(tcx, *y)));
    out
}

/// The SCCs callees first, each in `ItemPath` order.
pub fn sccs(tcx: &Tcx, bodies: &Bodies) -> Vec<Vec<Node>> {
    let mut nodes: Vec<Node> = bodies
        .keys()
        .filter_map(|o| match o {
            BodyOwner::Fn(d) => Some(Node::Fn(*d)),
            _ => None,
        })
        .chain(
            classes(tcx, &modules(tcx, bodies))
                .into_iter()
                .map(Node::Class),
        )
        .collect();
    nodes.sort_by(|x, y| path(tcx, *x).cmp(path(tcx, *y)));
    let set: BTreeSet<Node> = nodes.iter().copied().collect();
    let succ: BTreeMap<Node, Vec<Node>> = nodes
        .iter()
        .map(|&n| (n, edges(tcx, bodies, &set, n)))
        .collect();
    let mut t = Tarjan {
        succ: &succ,
        index: BTreeMap::new(),
        low: BTreeMap::new(),
        stack: Vec::new(),
        on: BTreeSet::new(),
        out: Vec::new(),
    };
    for &n in &nodes {
        if !t.index.contains_key(&n) {
            t.visit(n);
        }
    }
    for scc in &mut t.out {
        scc.sort_by(|x, y| path(tcx, *x).cmp(path(tcx, *y)));
    }
    t.out
}

struct Tarjan<'s> {
    succ: &'s BTreeMap<Node, Vec<Node>>,
    index: BTreeMap<Node, usize>,
    low: BTreeMap<Node, usize>,
    stack: Vec<Node>,
    on: BTreeSet<Node>,
    out: Vec<Vec<Node>>,
}

impl Tarjan<'_> {
    fn visit(&mut self, v: Node) {
        let i = self.index.len();
        self.index.insert(v, i);
        self.low.insert(v, i);
        self.stack.push(v);
        self.on.insert(v);
        for &w in &self.succ[&v] {
            if !self.index.contains_key(&w) {
                self.visit(w);
                let lw = self.low[&w];
                let lv = self.low.get_mut(&v).expect("visited");
                *lv = (*lv).min(lw);
            } else if self.on.contains(&w) {
                let iw = self.index[&w];
                let lv = self.low.get_mut(&v).expect("visited");
                *lv = (*lv).min(iw);
            }
        }
        if self.low[&v] == self.index[&v] {
            let mut scc = Vec::new();
            while let Some(w) = self.stack.pop() {
                self.on.remove(&w);
                scc.push(w);
                if w == v {
                    break;
                }
            }
            self.out.push(scc);
        }
    }
}
