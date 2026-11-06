//! `Symbol` and the global interner. The interner is shared with the other
//! tests of this binary, so nothing here assumes which strings are already in it.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, HashSet};
use std::ptr;

use enrang_base::{Symbol, intern};

const SAMPLES: &[&str] = &[
    "",
    " ",
    "\n",
    "\r\n",
    "\0",
    "a",
    "A",
    "x",
    "foo",
    "foo_bar",
    "fooBar",
    "é",
    "e\u{301}",
    "日本語",
    "😀",
    "\u{10FFFF}",
    "\u{FEFF}",
    "with space",
    "tail ",
    " head",
    "a\0b",
];

#[test]
fn symbol_is_four_bytes() {
    assert_eq!(size_of::<Symbol>(), 4);
}

#[test]
fn same_text_gives_same_symbol() {
    for &text in SAMPLES {
        assert_eq!(intern(text), intern(text), "{text:?}");
    }
}

#[test]
fn same_text_from_different_allocations_gives_same_symbol() {
    for &text in SAMPLES {
        let copy = text.to_owned();
        assert_eq!(intern(&copy), intern(text), "{text:?}");
    }
}

#[test]
fn as_str_round_trips() {
    for &text in SAMPLES {
        assert_eq!(intern(text).as_str(), text);
    }
}

#[test]
fn different_text_gives_different_symbols() {
    let symbols: HashSet<Symbol> = SAMPLES.iter().map(|text| intern(text)).collect();
    assert_eq!(symbols.len(), SAMPLES.len());
}

#[test]
fn near_identical_text_stays_distinct_table() {
    let pairs = [
        ("sym.a", "sym.A"),
        ("sym.a", "sym.a "),
        ("sym.a", "sym.ab"),
        ("sym.ab", "sym.ba"),
        ("sym.é", "sym.e\u{301}"),
        ("sym.a", "sym.a\0"),
        ("", " "),
    ];
    for (a, b) in pairs {
        assert_ne!(intern(a), intern(b), "{a:?} {b:?}");
        assert_eq!(intern(a).as_str(), a);
        assert_eq!(intern(b).as_str(), b);
    }
}

#[test]
fn interned_text_outlives_the_input() {
    let symbol = {
        let owned = String::from("sym.temporary.owned");
        intern(&owned)
    };
    let stored: &'static str = symbol.as_str();
    assert_eq!(stored, "sym.temporary.owned");
    assert_eq!(intern("sym.temporary.owned"), symbol);
}

#[test]
fn as_str_returns_one_stable_allocation() {
    let symbol = intern("sym.stable.pointer");
    let first = symbol.as_str();
    for i in 0..2_000 {
        intern(&format!("sym.stable.filler.{i}"));
    }
    assert!(ptr::eq(first, symbol.as_str()));
    assert!(ptr::eq(first, intern("sym.stable.pointer").as_str()));
    assert_eq!(first, "sym.stable.pointer");
}

#[test]
fn identity_is_stable_as_the_table_grows() {
    let names: Vec<String> = (0..3_000).map(|i| format!("sym.grow.{i}")).collect();
    let first: Vec<Symbol> = names.iter().map(|n| intern(n)).collect();
    let unique: HashSet<Symbol> = first.iter().copied().collect();
    assert_eq!(unique.len(), names.len());
    for (name, symbol) in names.iter().zip(&first).rev() {
        assert_eq!(intern(name), *symbol);
        assert_eq!(symbol.as_str(), name);
    }
}

#[test]
fn long_text_interns_whole() {
    let long = "x".repeat(100_000);
    let longer = "x".repeat(100_001);
    assert_ne!(intern(&long), intern(&longer));
    assert_eq!(intern(&long).as_str().len(), 100_000);
    assert_eq!(intern(&longer).as_str().len(), 100_001);
}

#[test]
fn threads_agree_on_identity() {
    let names: Vec<String> = (0..500).map(|i| format!("sym.race.{i}")).collect();
    let results: Vec<Vec<(usize, Symbol)>> = std::thread::scope(|scope| {
        let workers: Vec<_> = (0..8)
            .map(|worker| {
                let names = &names;
                scope.spawn(move || {
                    // Each thread interns in a different order, racing to be first.
                    let mut seen: Vec<(usize, Symbol)> = (0..names.len())
                        .map(|i| (i * (2 * worker + 1) + worker) % names.len())
                        .map(|i| (i, intern(&names[i])))
                        .collect();
                    seen.sort_by_key(|&(i, _)| i);
                    seen
                })
            })
            .collect();
        workers.into_iter().map(|w| w.join().unwrap()).collect()
    });
    for result in &results {
        assert_eq!(result.len(), names.len());
        for &(i, symbol) in result {
            assert_eq!(symbol, intern(&names[i]));
            assert_eq!(symbol.as_str(), names[i]);
        }
    }
    let unique: HashSet<Symbol> = names.iter().map(|n| intern(n)).collect();
    assert_eq!(unique.len(), names.len());
}

#[test]
fn symbols_cross_threads() {
    let symbol = intern("sym.cross.thread");
    let text = std::thread::spawn(move || symbol.as_str()).join().unwrap();
    assert!(ptr::eq(text, symbol.as_str()));
}

#[test]
fn order_is_lexical_whichever_was_interned_first() {
    // Fresh strings, so both interning orders really happen. An order by id
    // would get one of these two pairs backwards.
    let later_first = intern("sym.order.z1");
    let earlier_second = intern("sym.order.a1");
    assert!(earlier_second < later_first);
    let earlier_first = intern("sym.order.a2");
    let later_second = intern("sym.order.z2");
    assert!(earlier_first < later_second);
    assert!(later_first > earlier_second);
    assert!(later_second > earlier_first);
}

#[test]
fn sorting_is_lexical() {
    let texts = [
        "sym.sort.m",
        "sym.sort.c",
        "sym.sort.x",
        "sym.sort.a",
        "sym.sort.é",
    ];
    let mut symbols: Vec<Symbol> = texts.iter().map(|t| intern(t)).collect();
    symbols.sort();
    let sorted: Vec<&str> = symbols.iter().map(|s| s.as_str()).collect();
    let mut expected = texts.to_vec();
    expected.sort();
    assert_eq!(sorted, expected);
}

#[test]
fn order_agrees_with_equality() {
    for &a in SAMPLES {
        for &b in SAMPLES {
            let (x, y) = (intern(a), intern(b));
            assert_eq!(x.cmp(&y), a.cmp(b), "{a:?} {b:?}");
            assert_eq!(x.partial_cmp(&y), Some(a.cmp(b)), "{a:?} {b:?}");
            assert_eq!(x == y, a == b, "{a:?} {b:?}");
        }
    }
}

#[test]
fn btree_map_of_symbols_iterates_in_text_order() {
    let mut map = BTreeMap::new();
    for text in ["sym.map.q", "sym.map.b", "sym.map.y", "sym.map.d"] {
        map.insert(intern(text), text);
    }
    let keys: Vec<&str> = map.keys().map(|k| k.as_str()).collect();
    assert_eq!(keys, ["sym.map.b", "sym.map.d", "sym.map.q", "sym.map.y"]);
}

#[test]
fn display_prints_the_text() {
    assert_eq!(intern("sym.display").to_string(), "sym.display");
    assert_eq!(intern("").to_string(), "");
    assert_eq!(intern("日本語").to_string(), "日本語");
}

#[test]
fn display_honours_width() {
    assert_eq!(format!("{:>5}", intern("ab")), "   ab");
    assert_eq!(format!("{:<5}|", intern("ab")), "ab   |");
}

#[test]
fn debug_prints_the_text_and_no_id() {
    assert_eq!(
        format!("{:?}", intern("sym.debug")),
        "Symbol(\"sym.debug\")"
    );
    assert_eq!(format!("{:?}", intern("a\nb")), "Symbol(\"a\\nb\")");
}
