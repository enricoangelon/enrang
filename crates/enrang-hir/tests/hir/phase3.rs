//! What M3 adds to the contract crate for phase 3 (M3 plan 0.3, K1-K8): the store's
//! read-set bit and the moves-or-writes bits of a contract, the three new causes of
//! a read-only result and their order, `ConvKind` from the adjust steps, the
//! nullable's case constants, the program's new tables, and the target helper the
//! MIR text parser builds its `Tcx` with.

use std::sync::Arc;

use enrang_base::{SourceMap, Span, intern};
use enrang_hir::{
    Adjust, CheckedProgram, Contract, ConvKind, FieldInits, IntrinsicKind, ItemPath, ModulePath,
    Perm, Reason, ResultPerm, RetSources, Store, Tcx, TopVar, TopVarInfo, VariantIdx,
};
use enrang_testkit::Harness;

use crate::support::World;

fn store(read: bool, read_set_only: bool) -> Store {
    Store {
        from: 1,
        into: 0,
        fields_only: false,
        read,
        read_set_only,
    }
}

pub fn register(h: &mut Harness) {
    h.case(
        "phase3/the read-set bit tells two stores apart (K1)",
        || {
            assert_ne!(store(true, true), store(true, false));
            assert!(store(false, true).read_set_only);
        },
    );
    h.case(
        "phase3/moves-or-writes bits are part of a contract (K2)",
        || {
            let c = |bits: Vec<bool>| Contract {
                perms: vec![Perm::Read],
                sources: RetSources::NoLoans,
                result: ResultPerm::None,
                through_fields: Vec::new(),
                through_read: Vec::new(),
                stores: vec![store(true, false)],
                moves_or_writes: bits,
            };
            assert_ne!(c(vec![true]), c(vec![false]));
            assert_eq!(c(vec![false, true]).moves_or_writes.len(), 2);
        },
    );
    h.case(
        "phase3/the three new causes come after the M2 ones, in their order (K3)",
        || {
            let path = ItemPath::item(ModulePath::new("src/main"), intern("Pad"));
            let mut causes = vec![
                Reason::ConstLiteral,
                Reason::AliasedParts,
                Reason::StoredSource(1),
                Reason::StoredSource(0),
                Reason::ReadonlyField(path, enrang_hir::FieldIdx(0)),
                Reason::Declared,
            ];
            causes.sort();
            assert_eq!(causes[0], Reason::Declared);
            assert!(matches!(causes[1], Reason::ReadonlyField(..)));
            assert_eq!(
                causes[2..],
                [
                    Reason::StoredSource(0),
                    Reason::StoredSource(1),
                    Reason::AliasedParts,
                    Reason::ConstLiteral
                ]
            );
        },
    );
    h.case(
        "phase3/ConvKind is exactly the five conversion steps of Adjust (K4)",
        || {
            let steps = [
                (Adjust::FixedToSlice, Some(ConvKind::FixedToSlice)),
                (Adjust::ArrayToSlice, Some(ConvKind::ArrayToSlice)),
                (Adjust::Upcast, Some(ConvKind::Upcast)),
                (Adjust::BoxToInterface, Some(ConvKind::BoxToInterface)),
                (Adjust::RefToInterface, Some(ConvKind::RefToInterface)),
                (Adjust::AutoBorrow, None),
                (Adjust::WrapNull, None),
                (Adjust::FnToHandler, None),
                (Adjust::LiteralDescriptor, None),
            ];
            for (step, conv) in steps {
                assert_eq!(ConvKind::of_adjust(step), conv, "{step:?}");
            }
        },
    );
    h.case("phase3/a nullable's cases: null 0, present 1 (K5)", || {
        assert_eq!(VariantIdx::NULL, VariantIdx(0));
        assert_eq!(VariantIdx::PRESENT, VariantIdx(1));
        assert_eq!(VariantIdx::PRESENT, VariantIdx::ERR);
    });
    h.case(
        "phase3/an empty program has no satisfactions, hidden arguments or top variables",
        || {
            let p = CheckedProgram::default();
            assert!(p.satisfactions.is_empty());
            assert!(p.hidden_args.is_empty());
            assert!(p.top_vars.is_empty());
        },
    );
    h.case(
        "phase3/field initialisers keep the spans of their `this` (K8)",
        || {
            let mut w = World::new();
            let (pad, _) = w.class("Pad", enrang_hir::ClassModifier::Plain, &[]);
            let inits = FieldInits {
                adt: pad,
                inits: Vec::new(),
                this_spans: vec![Span::DUMMY],
            };
            assert_eq!(inits.clone(), inits);
            let var = TopVarInfo {
                name: intern("args"),
                ty: w.tcx.common().str,
                mutable: false,
                span: Span::DUMMY,
            };
            assert_eq!(var.name.as_str(), "args");
            assert_eq!(TopVar(0).0, 0);
        },
    );
    h.case(
        "phase3/a Tcx for a target by name, None for an unknown one",
        || {
            let map = Arc::new(SourceMap::new());
            let tcx = Tcx::for_target("x86_64-linux", Arc::clone(&map)).expect("a target");
            assert_eq!(tcx.target().layout.ptr_bytes, 8);
            let small = Tcx::for_target("i386-linux", Arc::clone(&map)).expect("a target");
            assert_eq!(small.target().layout.ptr_bytes, 4);
            assert!(Tcx::for_target("no-such-target", map).is_none());
        },
    );
    h.case(
        "phase3/CpuHas by feature name, for readers that cannot name Feature",
        || {
            let k = IntrinsicKind::cpu_has_named("sse2").expect("a feature");
            match k {
                IntrinsicKind::CpuHas(f) => assert_eq!(f.name(), "sse2"),
                other => panic!("{other:?}"),
            }
            assert!(IntrinsicKind::cpu_has_named("sse9").is_none());
        },
    );
}
