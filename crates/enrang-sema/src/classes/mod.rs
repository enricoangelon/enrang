//! Class rules (plan d.16; SPEC 4.3-4.4; A:896; owner 4D): the declaration checks
//! of user classes and interfaces (`members.rs`), exact satisfaction of interfaces
//! (`satisfy.rs`, the engine EN0416 and 4A's EN0419 share), the typing of field
//! initialisers (`inits.rs`, D6), and the call rules checked on finished bodies
//! (`calls.rs`). Signatures are compared by `sig.rs`. Every site that uses a type
//! as an interface goes through `satisfy.rs`'s one satisfaction routine, which
//! records what each satisfaction relies on.
//!
//! Library declarations are trusted and never checked here (plan choice, as their
//! bodies are never typed at M2, b.11): the stub library has `private` fields with
//! no default and no constructor, which EN0448 would refuse.

pub(crate) mod calls;
pub(crate) mod inits;
pub(crate) mod members;
pub(crate) mod satisfy;
pub(crate) mod sig;

use std::collections::BTreeSet;

use enrang_hir::{AdtId, Ty, TyKind};

use crate::cx::Sema;
use crate::lower::ItemAstKind;
use members::ClassAst;

/// What the class checks keep for later passes: the errors already reported at a
/// class, which every use of the class would otherwise report again (plan d.1: a
/// pass never emits a second diagnostic for a place another pass reported).
#[derive(Clone, Debug, Default)]
pub(crate) struct ClassTables {
    /// Classes whose `extends` names no class, EN0302 or EN0401 reported at it
    /// (lowering), or that lost their base to a reported cycle: what they would
    /// inherit is unknown.
    pub unknown_base: BTreeSet<AdtId>,
    /// `(class, interface)` for each `implements` that failed at the class with
    /// EN0416.
    pub failed_implements: BTreeSet<(AdtId, AdtId)>,
    /// Every member a satisfaction relied on, in the order the one satisfaction
    /// routine recorded them (`satisfy::satisfy`, SPEC 4.4): what the string
    /// clause, and phase 3's contract fitting, run over.
    pub satisfactions: Vec<satisfy::Satisfaction>,
}

impl Sema<'_> {
    /// Whether class `adt`, or a class its base chain reaches, has a base that is
    /// unknown (`ClassTables::unknown_base`), so a member, a constructor or a
    /// conversion its chain would give may be missing because of that one error.
    pub fn base_unknown(&self, adt: AdtId) -> bool {
        self.chain_has(adt, |c| self.classes.unknown_base.contains(&c))
    }

    /// Whether converting `from` to `target`, each a class, enum or interface
    /// behind references, `Box` and `| null`, two different ones, failed only
    /// because of an error already reported at a class: `from`'s class has an
    /// unknown base (`base_unknown`), so it may be a subclass of `target`'s, or
    /// `target` is an interface that `from`'s class, or a class above it, failed to
    /// implement with EN0416. A conversion to a number, or to the class itself, is
    /// reported as any other.
    pub fn conversion_reported(&self, from: Ty, target: Ty) -> bool {
        let (Some(class), Some(other)) = (self.adt_inside(from), self.adt_inside(target)) else {
            return false;
        };
        if class == other {
            return false;
        }
        self.base_unknown(class)
            || self.chain_has(class, |c| {
                self.classes.failed_implements.contains(&(c, other))
            })
    }

    /// Whether `adt` or a class above it passes `test`; a chain longer than the
    /// number of ADTs, which only a cycle could make, is cut.
    fn chain_has(&self, adt: AdtId, test: impl Fn(AdtId) -> bool) -> bool {
        let mut at = adt;
        for _ in 0..=self.tcx.adts().count() {
            if test(at) {
                return true;
            }
            let base = self.tcx.adt(at).as_class().and_then(|c| c.base);
            match base.map(|b| self.tcx.kind(b)) {
                Some(TyKind::Adt(b, _)) => at = b,
                _ => return false,
            }
        }
        false
    }

    /// The ADT of `t` behind references, `Box` and `| null`.
    fn adt_inside(&self, mut t: Ty) -> Option<AdtId> {
        loop {
            match self.tcx.kind(t) {
                TyKind::Ref(inner) | TyKind::Boxed(inner) | TyKind::Nullable(inner) => t = inner,
                TyKind::Adt(adt, _) => return Some(adt),
                _ => return None,
            }
        }
    }
}

/// Every user class's and interface's declaration rules, in collection order, then
/// each user class's field initialisers.
pub(crate) fn check_decls(sema: &mut Sema) {
    let items = sema.decls.items.clone();
    let mut classes = Vec::new();
    for item in &items {
        if sema.tcx.module(item.module).library {
            continue;
        }
        match &item.kind {
            ItemAstKind::Class(adt, decl, members) => {
                let cx = ClassAst {
                    def: item.def,
                    adt: *adt,
                    decl,
                    members,
                };
                members::check_class(sema, &cx);
                satisfy::check_implements(sema, &cx);
                classes.push(cx);
            }
            ItemAstKind::Interface(_, decl, _) => members::check_interface(sema, decl),
            _ => {}
        }
    }
    for cx in &classes {
        inits::check(sema, cx);
    }
}
