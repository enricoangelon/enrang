//! `BitSet`, concentrating on word boundaries.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;
use std::panic::{AssertUnwindSafe, catch_unwind};

use enrang_base::{BitSet, Idx};

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
struct Ix(u32);

impl Idx for Ix {
    fn new(i: usize) -> Self {
        Ix(u32::try_from(i).expect("index fits u32"))
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

type Set = BitSet<Ix>;

fn ix(i: usize) -> Ix {
    Ix::new(i)
}

/// Domain sizes around each interesting word boundary.
const DOMAINS: &[usize] = &[1, 2, 63, 64, 65, 127, 128, 129, 191, 192, 193, 256, 1000];

/// Domain, the two operands, the expected members and whether the left operand changes.
type BinaryCase = (
    usize,
    &'static [usize],
    &'static [usize],
    &'static [usize],
    bool,
);

/// Domain, the two operands and the expected answer.
type PredicateCase = (usize, &'static [usize], &'static [usize], bool);

/// The bits worth testing in `domain`: both sides of every word boundary.
fn edge_bits(domain: usize) -> Vec<usize> {
    let candidates = [
        0,
        1,
        62,
        63,
        64,
        65,
        126,
        127,
        128,
        129,
        191,
        192,
        255,
        domain - 1,
    ];
    let unique: BTreeSet<usize> = candidates.into_iter().filter(|&b| b < domain).collect();
    unique.into_iter().collect()
}

fn set_of(domain: usize, bits: &[usize]) -> Set {
    let mut set = Set::new(domain);
    for &bit in bits {
        set.insert(ix(bit));
    }
    set
}

fn members(set: &Set) -> Vec<usize> {
    set.iter().map(Ix::index).collect()
}

fn panics(f: impl FnOnce()) -> bool {
    catch_unwind(AssertUnwindSafe(f)).is_err()
}

#[test]
fn new_is_empty_table() {
    for &domain in DOMAINS {
        let set = Set::new(domain);
        assert_eq!(set.domain_size(), domain);
        assert_eq!(set.count(), 0, "domain {domain}");
        assert!(set.is_empty(), "domain {domain}");
        assert_eq!(set.iter().count(), 0, "domain {domain}");
        assert!((0..domain).all(|i| !set.contains(ix(i))), "domain {domain}");
    }
}

#[test]
fn empty_domain_holds_nothing() {
    let mut set = Set::new(0);
    assert_eq!(set.domain_size(), 0);
    assert!(set.is_empty());
    assert_eq!(set.count(), 0);
    set.insert_all();
    assert!(set.is_empty());
    assert_eq!(Set::full(0), Set::new(0));
    assert!(!set.union(&Set::full(0)));
    assert!(set.is_subset(&Set::new(0)));
    assert!(set.is_disjoint(&Set::new(0)));
    assert!(panics(|| {
        set.contains(ix(0));
    }));
}

#[test]
fn insert_reports_change_at_edges() {
    for &domain in DOMAINS {
        let mut set = Set::new(domain);
        for bit in edge_bits(domain) {
            assert!(set.insert(ix(bit)), "first insert {bit} in {domain}");
            assert!(!set.insert(ix(bit)), "second insert {bit} in {domain}");
        }
    }
}

#[test]
fn remove_reports_change_at_edges() {
    for &domain in DOMAINS {
        let mut set = Set::new(domain);
        for bit in edge_bits(domain) {
            assert!(!set.remove(ix(bit)), "remove of absent {bit} in {domain}");
            set.insert(ix(bit));
            assert!(set.remove(ix(bit)), "remove of present {bit} in {domain}");
            assert!(!set.contains(ix(bit)));
            assert!(!set.remove(ix(bit)), "second remove {bit} in {domain}");
        }
        assert!(set.is_empty());
    }
}

#[test]
fn a_single_bit_touches_only_itself() {
    for &domain in DOMAINS {
        for bit in edge_bits(domain) {
            let set = set_of(domain, &[bit]);
            assert_eq!(set.count(), 1, "{bit} in {domain}");
            assert_eq!(members(&set), [bit], "{bit} in {domain}");
            for other in 0..domain {
                assert_eq!(set.contains(ix(other)), other == bit, "{other} after {bit}");
            }
        }
    }
}

#[test]
fn removing_one_bit_leaves_the_rest() {
    for &domain in DOMAINS {
        for bit in edge_bits(domain) {
            let mut set = Set::full(domain);
            set.remove(ix(bit));
            assert_eq!(set.count(), domain - 1, "{bit} in {domain}");
            for other in 0..domain {
                assert_eq!(set.contains(ix(other)), other != bit, "{other} after {bit}");
            }
        }
    }
}

#[test]
fn indices_at_or_past_the_domain_panic() {
    for &domain in DOMAINS {
        // A bit past the domain may still fall in the last word: 63 of domain 63.
        for bit in [domain, domain + 1, domain.next_multiple_of(64), domain + 64] {
            let mut set = Set::new(domain);
            assert!(
                panics(|| {
                    set.contains(ix(bit));
                }),
                "contains {bit} of {domain}"
            );
            assert!(
                panics(|| {
                    set.insert(ix(bit));
                }),
                "insert {bit} of {domain}"
            );
            assert!(
                panics(|| {
                    set.remove(ix(bit));
                }),
                "remove {bit} of {domain}"
            );
            assert!(set.is_empty(), "a failed insert must not set a bit");
        }
    }
}

#[test]
fn the_message_names_the_bit_and_the_domain() {
    let set = Set::new(65);
    let payload = catch_unwind(AssertUnwindSafe(|| {
        set.contains(ix(70));
    }))
    .unwrap_err();
    let message = payload
        .downcast_ref::<String>()
        .expect("a formatted message");
    assert_eq!(message, "bit 70 out of domain 65");
}

#[test]
fn full_holds_exactly_the_domain() {
    for &domain in DOMAINS {
        let set = Set::full(domain);
        assert_eq!(set.count(), domain, "count of full({domain})");
        assert_eq!(members(&set), (0..domain).collect::<Vec<_>>());
        assert!(!set.is_empty());
    }
}

#[test]
fn full_equals_inserting_every_bit() {
    // Stray bits past the domain in the last word would break this equality.
    for &domain in DOMAINS {
        let mut built = Set::new(domain);
        for i in 0..domain {
            built.insert(ix(i));
        }
        assert_eq!(built, Set::full(domain), "domain {domain}");
    }
}

#[test]
fn insert_all_fills_a_partial_set() {
    for &domain in DOMAINS {
        let mut set = set_of(domain, &edge_bits(domain));
        set.insert_all();
        assert_eq!(set, Set::full(domain), "domain {domain}");
    }
}

#[test]
fn clear_empties_table() {
    for &domain in DOMAINS {
        let mut set = Set::full(domain);
        set.clear();
        assert!(set.is_empty(), "domain {domain}");
        assert_eq!(set, Set::new(domain), "domain {domain}");
        assert_eq!(set.domain_size(), domain);
    }
}

#[test]
fn is_empty_sees_every_word() {
    for &domain in DOMAINS {
        for bit in edge_bits(domain) {
            assert!(!set_of(domain, &[bit]).is_empty(), "{bit} in {domain}");
        }
    }
}

#[test]
fn iter_is_ascending_across_words() {
    let bits = [0, 1, 63, 64, 65, 127, 128, 200, 255, 256, 999];
    let shuffled = [256, 64, 0, 999, 127, 1, 200, 63, 255, 128, 65];
    let set = set_of(1000, &shuffled);
    assert_eq!(members(&set), bits);
}

#[test]
fn iter_borrows_without_consuming() {
    let set = set_of(70, &[3, 66]);
    assert_eq!(members(&set), [3, 66]);
    assert_eq!(members(&set), [3, 66]);
}

#[test]
fn union_table() {
    let cases: &[BinaryCase] = &[
        (64, &[], &[], &[], false),
        (64, &[63], &[], &[63], false),
        (64, &[], &[63], &[63], true),
        (64, &[63], &[63], &[63], false),
        (65, &[63], &[64], &[63, 64], true),
        (65, &[64], &[64], &[64], false),
        (65, &[64], &[63], &[63, 64], true),
        (128, &[0], &[127], &[0, 127], true),
        (129, &[0, 64], &[128], &[0, 64, 128], true),
        (129, &[128], &[0, 64], &[0, 64, 128], true),
        (129, &[0, 64, 128], &[64], &[0, 64, 128], false),
    ];
    for &(domain, a, b, expected, changed) in cases {
        let mut set = set_of(domain, a);
        assert_eq!(set.union(&set_of(domain, b)), changed, "{a:?} | {b:?}");
        assert_eq!(members(&set), expected, "{a:?} | {b:?}");
    }
}

#[test]
fn intersect_table() {
    let cases: &[BinaryCase] = &[
        (64, &[], &[], &[], false),
        (64, &[63], &[63], &[63], false),
        (64, &[63], &[], &[], true),
        (64, &[], &[63], &[], false),
        (65, &[63, 64], &[64], &[64], true),
        (65, &[63, 64], &[63], &[63], true),
        (65, &[63], &[64], &[], true),
        (129, &[0, 64, 128], &[64, 128], &[64, 128], true),
        (129, &[64], &[0, 64, 128], &[64], false),
    ];
    for &(domain, a, b, expected, changed) in cases {
        let mut set = set_of(domain, a);
        assert_eq!(set.intersect(&set_of(domain, b)), changed, "{a:?} & {b:?}");
        assert_eq!(members(&set), expected, "{a:?} & {b:?}");
    }
}

#[test]
fn subtract_table() {
    let cases: &[BinaryCase] = &[
        (64, &[], &[], &[], false),
        (64, &[63], &[63], &[], true),
        (64, &[63], &[0], &[63], false),
        (64, &[], &[63], &[], false),
        (65, &[63, 64], &[64], &[63], true),
        (65, &[63, 64], &[63], &[64], true),
        (65, &[63], &[64], &[63], false),
        (129, &[0, 64, 128], &[0, 128], &[64], true),
        (129, &[64], &[0, 128], &[64], false),
    ];
    for &(domain, a, b, expected, changed) in cases {
        let mut set = set_of(domain, a);
        assert_eq!(set.subtract(&set_of(domain, b)), changed, "{a:?} - {b:?}");
        assert_eq!(members(&set), expected, "{a:?} - {b:?}");
    }
}

#[test]
fn is_subset_table() {
    let cases: &[PredicateCase] = &[
        (64, &[], &[], true),
        (64, &[], &[63], true),
        (64, &[63], &[], false),
        (64, &[63], &[63], true),
        (65, &[63], &[63, 64], true),
        (65, &[63, 64], &[63], false),
        (65, &[63, 64], &[64], false),
        (129, &[128], &[0, 64, 128], true),
        (129, &[0, 128], &[0, 64], false),
        (129, &[0, 64], &[64, 128], false),
    ];
    for &(domain, a, b, expected) in cases {
        let got = set_of(domain, a).is_subset(&set_of(domain, b));
        assert_eq!(got, expected, "{a:?} <= {b:?}");
    }
}

#[test]
fn is_disjoint_table() {
    let cases: &[PredicateCase] = &[
        (64, &[], &[], true),
        (64, &[63], &[], true),
        (64, &[63], &[63], false),
        (65, &[63], &[64], true),
        (65, &[64], &[64], false),
        (129, &[0, 128], &[64], true),
        (129, &[0, 128], &[64, 128], false),
        (129, &[0, 64, 128], &[0], false),
    ];
    for &(domain, a, b, expected) in cases {
        let (a_set, b_set) = (set_of(domain, a), set_of(domain, b));
        assert_eq!(a_set.is_disjoint(&b_set), expected, "{a:?} {b:?}");
        assert_eq!(b_set.is_disjoint(&a_set), expected, "{b:?} {a:?}");
    }
}

#[test]
fn set_operations_panic_on_differing_domains() {
    // 64 and 63 use the same number of words, so only a domain check catches them.
    for (x, y) in [(64, 63), (63, 64), (65, 64), (128, 129), (0, 1)] {
        let b = Set::new(y);
        assert!(
            panics(|| {
                Set::new(x).union(&b);
            }),
            "union {x} {y}"
        );
        assert!(
            panics(|| {
                Set::new(x).intersect(&b);
            }),
            "intersect {x} {y}"
        );
        assert!(
            panics(|| {
                Set::new(x).subtract(&b);
            }),
            "subtract {x} {y}"
        );
        assert!(
            panics(|| {
                Set::new(x).is_subset(&b);
            }),
            "is_subset {x} {y}"
        );
        assert!(
            panics(|| {
                Set::new(x).is_disjoint(&b);
            }),
            "is_disjoint {x} {y}"
        );
    }
}

#[test]
fn equality_requires_the_same_domain() {
    assert_ne!(Set::new(63), Set::new(64));
    assert_ne!(Set::new(64), Set::new(65));
    assert_eq!(Set::new(64), Set::new(64));
    assert_ne!(set_of(64, &[1]), set_of(64, &[2]));
    assert_eq!(set_of(65, &[64, 0]), set_of(65, &[0, 64]));
    assert_ne!(set_of(65, &[64]), set_of(65, &[0]));
}

#[test]
fn clone_is_independent() {
    let original = set_of(65, &[64]);
    let mut copy = original.clone();
    copy.insert(ix(0));
    copy.remove(ix(64));
    assert_eq!(members(&original), [64]);
    assert_eq!(members(&copy), [0]);
}

#[test]
fn debug_lists_the_members() {
    assert_eq!(format!("{:?}", set_of(70, &[65, 0])), "{0, 65}");
    assert_eq!(format!("{:?}", Set::new(70)), "{}");
}

#[test]
fn operations_agree_with_a_btree_model() {
    let mut state = 0x2545_F491_4F6C_DD1Du64;
    let mut next = move |n: usize| {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        (state % n as u64) as usize
    };
    for &domain in DOMAINS {
        let mut set = Set::new(domain);
        let mut model: BTreeSet<usize> = BTreeSet::new();
        for step in 0..2_000 {
            let bit = next(domain);
            let context = format!("step {step} bit {bit} domain {domain}");
            match next(9) {
                0 | 1 => assert_eq!(set.insert(ix(bit)), model.insert(bit), "{context}"),
                2 => assert_eq!(set.remove(ix(bit)), model.remove(&bit), "{context}"),
                3 => assert_eq!(set.contains(ix(bit)), model.contains(&bit), "{context}"),
                op => {
                    let bits: BTreeSet<usize> = (0..next(8)).map(|_| next(domain)).collect();
                    let other = set_of(domain, &bits.iter().copied().collect::<Vec<_>>());
                    assert_eq!(set.is_subset(&other), model.is_subset(&bits), "{context}");
                    assert_eq!(
                        set.is_disjoint(&other),
                        model.is_disjoint(&bits),
                        "{context}"
                    );
                    let result: BTreeSet<usize> = match op {
                        4 | 5 => model.union(&bits).copied().collect(),
                        6 => model.intersection(&bits).copied().collect(),
                        _ => model.difference(&bits).copied().collect(),
                    };
                    let changed = match op {
                        4 | 5 => set.union(&other),
                        6 => set.intersect(&other),
                        _ => set.subtract(&other),
                    };
                    assert_eq!(changed, result != model, "{context}");
                    model = result;
                }
            }
            assert_eq!(set.count(), model.len(), "{context}");
            assert_eq!(set.is_empty(), model.is_empty(), "{context}");
        }
        assert_eq!(members(&set), model.iter().copied().collect::<Vec<_>>());
    }
}
