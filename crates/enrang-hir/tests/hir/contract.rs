//! What phase 3 and interface files read from the contract crate: contracts that
//! name definitions by stable path, never by `DefId` (A:440, A:1281); the memo
//! tables of the on-demand queries (A:772, A:816-817, A:762); the member a bound
//! call chose (D15) and C17's adjust (D16).

use std::cell::Cell;
use std::sync::Arc;

use enrang_base::{Span, intern};
use enrang_hir::{
    Adjust, Callee, ClassContract, ClassModifier, Contract, DefData, DefKind, FieldIdx, ItemPath,
    ModulePath, Perm, Reason, ResultPerm, RetSources, Vis,
};
use enrang_testkit::Harness;

use crate::support::World;

/// A contract whose result is read-only for `cause`.
fn reading(cause: Reason) -> Contract {
    Contract {
        perms: vec![Perm::Read],
        sources: RetSources::Params(vec![0]),
        result: ResultPerm::ReadOnly(cause),
        through_fields: Vec::new(),
        through_read: Vec::new(),
        stores: Vec::new(),
        moves_or_writes: Vec::new(),
    }
}

pub fn register(h: &mut Harness) {
    h.case(
        "contract/a cause names its definition by path, the same in any load order",
        || {
            // Two programs define the same items in opposite orders, so every
            // `DefId` differs, while the contracts are equal.
            let names = ["COUNTER", "Pad"];
            let mut contracts = Vec::new();
            for order in [[0, 1], [1, 0]] {
                let mut w = World::new();
                let mut paths = [None, None];
                for i in order {
                    let path = ItemPath::item(ModulePath::new("src/main"), intern(names[i]));
                    let def = w.tcx.define_def(DefData::new(
                        path,
                        DefKind::Static,
                        w.module,
                        Span::DUMMY,
                    ));
                    paths[i] = Some(w.tcx.def(def).path.clone());
                }
                let [counter, pad] = paths.map(|p| p.expect("defined"));
                contracts.push((
                    reading(Reason::Static(counter)),
                    reading(Reason::ReadonlyField(pad, FieldIdx(1))),
                ));
            }
            assert_eq!(contracts[0], contracts[1]);
            let static_cause = reading(Reason::Static(ItemPath::item(
                ModulePath::new("src/main"),
                intern("COUNTER"),
            )));
            assert_eq!(contracts[0].0, static_cause);
            assert_ne!(reading(Reason::Declared), reading(Reason::ConstRoot));
        },
    );
    h.case(
        "contract/memo tables compute once, first result wins",
        || {
            let mut w = World::new();
            let (pad, _) = w.class("Pad", ClassModifier::Plain, &[]);
            let f = w.method(pad, "f", &[], w.tcx.common().void, Vis::Public);
            let g = w.method(pad, "g", &[], w.tcx.common().void, Vis::Public);
            let runs = Cell::new(0);
            assert!(w.tcx.contract_memo(f).is_none());
            let first = w.tcx.contract_or_insert_with(f, || {
                runs.set(runs.get() + 1);
                // A query may ask for another contract while it computes.
                let other = w
                    .tcx
                    .contract_or_insert_with(g, || reading(Reason::StringPart));
                assert_eq!(other.result, ResultPerm::ReadOnly(Reason::StringPart));
                reading(Reason::Declared)
            });
            let again = w.tcx.contract_or_insert_with(f, || {
                runs.set(runs.get() + 1);
                reading(Reason::RawDeref)
            });
            assert_eq!(runs.get(), 1);
            assert!(Arc::ptr_eq(&first, &again));
            assert_eq!(
                w.tcx.contract_memo(g).map(|c| c.result.clone()),
                Some(ResultPerm::ReadOnly(Reason::StringPart))
            );
            let flag = ClassContract {
                writes_through_fields: true,
            };
            assert_eq!(w.tcx.class_contract_or_insert_with(pad, || flag), flag);
            let kept = w.tcx.class_contract_or_insert_with(pad, || ClassContract {
                writes_through_fields: false,
            });
            assert_eq!(kept, flag);
            assert_eq!(w.tcx.class_contract_memo(pad), Some(flag));
            let ty = w.tcx.common().i64;
            assert!(w.tcx.layout_memo(ty).is_none());
            let stored = w.tcx.memo_layout(ty, Arc::new(8u64));
            let kept = w.tcx.memo_layout(ty, Arc::new(4u64));
            assert!(Arc::ptr_eq(&stored, &kept));
            assert_eq!(kept.downcast_ref::<u64>(), Some(&8));
        },
    );
    h.case(
        "contract/a bound call names the member chosen on the bound (D15)",
        || {
            let mut w = World::new();
            let (show, _) = w.interface("Show", &[], None);
            let i64 = w.tcx.common().i64;
            let str_ref = w.tcx.mk_ref(w.tcx.common().str);
            let void = w.tcx.common().void;
            let by_int = w.method(show, "m", &[i64], void, Vis::Public);
            let by_str = w.method(show, "m", &[str_ref], void, Vis::Public);
            let (p, _) = w.bounded_param("T", &[show]);
            let args = w.tcx.empty_list();
            let call = |found| Callee::BoundMember {
                param: p,
                member: intern("m"),
                found,
                args,
            };
            assert_ne!(call(by_int), call(by_str), "two overloads, two callees");
            assert_ne!(Adjust::FnToHandler, Adjust::FnToPtr, "C17 has its own step");
        },
    );
}
