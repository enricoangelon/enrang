//! The lang-item and intrinsic tables against the documents: the intrinsic kinds
//! are read from ARCHITECTURE 2.5's `define_intrinsics!` block, in order, and every
//! `@lang("...")` name the documents use is in the lang table.

use std::collections::BTreeSet;
use std::fs;

use enrang_diag::Milestone;
use enrang_hir::{IntrinsicKind, IntrinsicName, LangItem, LangLayer};
use enrang_testkit::{Harness, workspace_root};

fn doc(name: &str) -> String {
    fs::read_to_string(workspace_root().join("docs").join(name)).expect("a document")
}

/// The kinds of the `define_intrinsics!` block, payloads dropped, in order.
fn documented_intrinsics() -> Vec<String> {
    let architecture = doc("ARCHITECTURE.md");
    let block = architecture
        .split("define_intrinsics! {")
        .nth(1)
        .expect("the block")
        .split("\n}")
        .next()
        .expect("its end");
    let mut names = Vec::new();
    for line in block.lines() {
        let code = line.split("//").next().unwrap_or("");
        let mut flat = String::new();
        let mut depth = 0;
        for c in code.chars() {
            match c {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ if depth == 0 => flat.push(c),
                _ => {}
            }
        }
        names.extend(
            flat.split(',')
                .map(str::trim)
                .filter(|n| !n.is_empty())
                .map(str::to_owned),
        );
    }
    names
}

/// Every `@lang("...")` argument the documents write, but the placeholder `name`.
fn documented_lang_names() -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for name in ["SPEC.md", "ARCHITECTURE.md", "TESTING.md"] {
        let text = doc(name);
        for piece in text.split("@lang(\"").skip(1) {
            let arg = piece.split('"').next().unwrap_or("");
            if arg != "name" {
                names.insert(arg.to_owned());
            }
        }
    }
    names
}

pub fn register(h: &mut Harness) {
    h.case(
        "tables/the intrinsic kinds are ARCHITECTURE's, in order",
        || {
            let documented = documented_intrinsics();
            let ours: Vec<&str> = IntrinsicName::ALL.iter().map(|k| k.name()).collect();
            assert_eq!(ours, documented);
        },
    );
    h.case("tables/intrinsic names round-trip", || {
        for &kind in IntrinsicName::ALL {
            assert_eq!(IntrinsicName::from_name(kind.name()), Some(kind));
        }
        assert_eq!(IntrinsicName::from_name("Bogus"), None);
        assert_eq!(
            IntrinsicKind::AtomicAlu(enrang_hir::AluOp::Add).name(),
            IntrinsicName::AtomicAlu
        );
    });
    h.case("tables/safety bits", || {
        let unsafe_kinds = [
            "VolatileRead",
            "VolatileWrite",
            "ReadUnaligned",
            "WriteUnaligned",
            "MemCopy",
            "MemCopyOverlap",
            "MemSet",
            "DivWideU32",
            "SliceFromRaw",
        ];
        for &kind in IntrinsicName::ALL {
            assert_eq!(
                kind.is_safe(),
                !unsafe_kinds.contains(&kind.name()),
                "{}",
                kind.name()
            );
        }
        assert!(
            IntrinsicName::SizeOf.is_safe(),
            "a safe declaration names it (A:535)"
        );
        assert!(
            IntrinsicName::AllocArray.is_safe(),
            "mirbuild emits it in safe code"
        );
    });
    h.case("tables/every documented @lang name is a lang item", || {
        for name in documented_lang_names() {
            assert!(LangItem::from_name(&name).is_some(), "@lang(\"{name}\")");
        }
    });
    h.case(
        "tables/lang items: names unique, round-trip, layers",
        || {
            let mut seen = BTreeSet::new();
            for &item in LangItem::ALL {
                assert!(seen.insert(item.name()), "{} twice", item.name());
                assert_eq!(LangItem::from_name(item.name()), Some(item));
            }
            assert_eq!(LangItem::Str.layer(), LangLayer::Core);
            assert_eq!(LangItem::Array.layer(), LangLayer::Alloc);
            assert_eq!(LangItem::Boxed.layer(), LangLayer::Alloc);
            assert_eq!(
                LangItem::FailureFromDisplay.layer(),
                LangLayer::Alloc,
                "it allocates the text, and `core` has no allocator (A:644, A:944, A:2122)"
            );
            assert_eq!(LangItem::InterruptHandler.layer(), LangLayer::OsNone);
            assert_eq!(LangLayer::OsNone.folder(), "os/none");
        },
    );
    h.case(
        "tables/the compiler-called functions of ARCHITECTURE 10 are lang items",
        || {
            for name in [
                "rt_alloc",
                "rt_dealloc",
                "array_push",
                "array_extend_cloned",
                "failure_from_display",
            ] {
                let item = LangItem::from_name(name).unwrap_or_else(|| panic!("{name}"));
                assert_eq!(
                    item.since(),
                    Milestone::M3,
                    "signature stubs by M3 (A:2012)"
                );
            }
        },
    );
    h.case("tables/the sealed interfaces", || {
        let sealed: Vec<&str> = LangItem::ALL
            .iter()
            .filter(|i| i.is_sealed())
            .map(|i| i.name())
            .collect();
        assert_eq!(
            sealed,
            [
                "int",
                "float",
                "volatile_value",
                "atomic_value",
                "atomic_bits"
            ]
        );
    });
}
