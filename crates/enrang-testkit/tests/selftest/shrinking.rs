//! The shrinker on known failing inputs.

use std::cell::Cell;
use std::collections::BTreeSet;
use std::fmt::Debug;
use std::iter;

use enrang_testkit::{
    Harness, Rng, SHRINK_ATTEMPTS, Shrink, rng_for, scaled, shrink, shrink_within,
};

/// A user type: a program with an instruction list and a flag.
#[derive(Clone, Eq, PartialEq, Debug)]
struct Program {
    instructions: Vec<u32>,
    optimised: bool,
}

impl Shrink for Program {
    fn candidates(&self) -> Box<dyn Iterator<Item = Program> + '_> {
        let by_instructions = self.instructions.candidates().map(|instructions| Program {
            instructions,
            optimised: self.optimised,
        });
        let by_flag = self.optimised.candidates().map(|optimised| Program {
            instructions: self.instructions.clone(),
            optimised,
        });
        Box::new(by_instructions.chain(by_flag))
    }
}

/// A broken impl: its only candidate is itself.
#[derive(Clone, Eq, PartialEq, Debug)]
struct Stuck(u32);

impl Shrink for Stuck {
    fn candidates(&self) -> Box<dyn Iterator<Item = Stuck> + '_> {
        Box::new(iter::once(self.clone()))
    }
}

/// A broken impl: its candidates never run out.
#[derive(Clone, Eq, PartialEq, Debug)]
struct Endless(u64);

impl Shrink for Endless {
    fn candidates(&self) -> Box<dyn Iterator<Item = Endless> + '_> {
        let start = self.0;
        Box::new((0..).map(move |offset| Endless(start.wrapping_add(offset))))
    }
}

/// A sort with a real bug: it drops duplicates.
fn buggy_sort(input: &[u32]) -> Vec<u32> {
    input
        .iter()
        .copied()
        .collect::<BTreeSet<u32>>()
        .into_iter()
        .collect()
}

fn sum_overflows_u8(input: &[u8]) -> bool {
    input
        .iter()
        .try_fold(0u8, |sum, &x| sum.checked_add(x))
        .is_none()
}

fn case_threshold<T>(h: &mut Harness, name: String, start: T, threshold: T)
where
    T: Shrink + Copy + Ord + Debug + Send + 'static,
{
    h.case(name, move || {
        assert_eq!(shrink(start, |&x| x >= threshold), threshold);
    });
}

fn case_negative_threshold<T>(h: &mut Harness, name: String, start: T, threshold: T)
where
    T: Shrink + Copy + Ord + Debug + Send + 'static,
{
    h.case(name, move || {
        assert_eq!(shrink(start, |&x| x <= threshold), threshold);
    });
}

fn case_candidates<T>(h: &mut Harness, name: String, value: T)
where
    T: Shrink + Clone + Eq + Debug + Send + 'static,
{
    h.case(name, move || {
        for candidate in value.candidates().take(10_000) {
            assert_ne!(candidate, value, "a candidate must differ from its source");
        }
    });
}

pub fn register(h: &mut Harness) {
    register_integers(h);
    register_compound(h);
    register_known_bugs(h);
    register_bounds(h);
}

fn register_integers(h: &mut Harness) {
    let thresholds: [(u64, u64); 12] = [
        (1, 1),
        (2, 1),
        (2, 2),
        (100, 1),
        (100, 99),
        (100, 100),
        (1000, 3),
        (1 << 20, 1 << 10),
        (123_456_789, 1000),
        (u64::MAX, 1),
        (u64::MAX, 1 << 63),
        (u64::MAX, u64::MAX),
    ];
    for (start, threshold) in thresholds {
        case_threshold(
            h,
            format!("shrink::u64::{start}>={threshold}"),
            start,
            threshold,
        );
    }
    case_threshold(h, "shrink::u8::255>=17".into(), 255u8, 17);
    case_threshold(h, "shrink::u16::65535>=256".into(), 65535u16, 256);
    case_threshold(h, "shrink::u32::max>=65536".into(), u32::MAX, 65536);
    case_threshold(h, "shrink::u128::max>=2^64".into(), u128::MAX, 1 << 64);
    case_threshold(h, "shrink::usize::4096>=513".into(), 4096usize, 513);
    case_threshold(h, "shrink::i32::positive".into(), 1 << 30, 12_345);
    case_threshold(h, "shrink::i64::positive".into(), i64::MAX, 1 << 40);

    let negatives: [(i64, i64); 8] = [
        (-1, -1),
        (-2, -1),
        (-100, -17),
        (-100, -100),
        (i64::MIN, -1),
        (i64::MIN, -1000),
        (i64::MIN, i64::MIN),
        (i64::MIN, i64::MIN + 1),
    ];
    for (start, threshold) in negatives {
        case_negative_threshold(
            h,
            format!("shrink::i64::{start}<={threshold}"),
            start,
            threshold,
        );
    }
    case_negative_threshold(h, "shrink::i8::min<=-5".into(), i8::MIN, -5);
    case_negative_threshold(h, "shrink::i8::min<=min".into(), i8::MIN, i8::MIN);
    case_negative_threshold(h, "shrink::i16::min<=-300".into(), i16::MIN, -300);
    case_negative_threshold(h, "shrink::i32::min<=-70000".into(), i32::MIN, -70_000);
    case_negative_threshold(h, "shrink::i128::min<=-2^70".into(), i128::MIN, -(1 << 70));
    case_negative_threshold(h, "shrink::isize::min<=-9".into(), isize::MIN, -9);

    h.case("shrink::zero_has_no_candidates", || {
        assert_eq!(0u64.candidates().count(), 0);
        assert_eq!(0i64.candidates().count(), 0);
    });
    h.case("shrink::a_failure_at_any_value_goes_to_zero", || {
        assert_eq!(shrink(987_654u64, |_| true), 0);
        assert_eq!(shrink(-987_654i64, |_| true), 0);
    });
    h.case("shrink::a_negative_tries_its_positive_twin", || {
        assert_eq!(shrink(-40i64, |&x| x != 0), 1);
        assert_eq!(shrink(-40i64, |&x| x.abs() >= 7), 7);
    });
    h.case(
        "shrink::i64_min_has_no_positive_twin_and_does_not_overflow",
        || {
            let candidates: Vec<i64> = i64::MIN.candidates().collect();
            assert!(candidates.contains(&0));
            assert!(candidates.contains(&(i64::MIN / 2)));
            assert!(candidates.contains(&(i64::MIN + 1)));
        },
    );
    let nonzero_unsigned = [1u64, 2, 3, 7, 8, 255, 256, 1 << 40, u64::MAX];
    for value in nonzero_unsigned {
        case_candidates(h, format!("shrink::candidates::u64::{value}"), value);
        h.case(
            format!("shrink::candidates::u64_stays_below::{value}"),
            move || {
                assert!(value.candidates().all(|candidate| candidate < value));
                assert_eq!(value.candidates().next(), Some(0));
            },
        );
    }
    for value in [1i64, -1, 2, -2, 100, -100, i64::MAX, i64::MIN] {
        case_candidates(h, format!("shrink::candidates::i64::{value}"), value);
    }
}

fn register_compound(h: &mut Harness) {
    h.case("shrink::bool::true_to_false", || {
        assert!(!shrink(true, |_| true));
        assert!(shrink(true, |&x| x));
        assert_eq!(false.candidates().count(), 0);
    });
    h.case("shrink::char::to_a", || {
        assert_eq!(shrink('z', |_| true), 'a');
        assert_eq!(shrink('z', |&c| c == 'z'), 'z');
        assert_eq!('a'.candidates().count(), 0);
    });
    h.case("shrink::option::to_none", || {
        assert_eq!(shrink(Some(5u8), |_| true), None);
    });
    h.case("shrink::option::keeps_a_needed_some", || {
        assert_eq!(shrink(Some(50u8), |x| x.is_some_and(|v| v >= 3)), Some(3));
    });
    h.case("shrink::vec::to_empty", || {
        assert_eq!(shrink(vec![1u8, 2, 3], |_| true), Vec::<u8>::new());
    });
    let vec_rows: &[(&str, &[u64], fn(&Vec<u64>) -> bool, &[u64])] = &[
        (
            "contains_big",
            &[1, 2, 300, 4, 500],
            |v| v.iter().any(|&x| x >= 10),
            &[10],
        ),
        (
            "long_enough",
            &[9, 9, 9, 9, 9],
            |v| v.len() >= 3,
            &[0, 0, 0],
        ),
        (
            "sum",
            &[50, 60, 70],
            |v| v.iter().sum::<u64>() >= 100,
            &[30, 70],
        ),
        (
            "two_far_apart",
            &[5, 3, 1, 1, 1, 1, 1, 8, 1],
            |v| v.contains(&3) && v.contains(&8),
            &[3, 8],
        ),
        (
            "ordered_pair",
            &[7, 1, 9, 2, 8],
            |v| v.windows(2).any(|w| w[0] > w[1]),
            &[1, 0],
        ),
        (
            "first_is_big",
            &[40, 1, 1],
            |v| v.first().is_some_and(|&x| x >= 40),
            &[40],
        ),
        (
            "last_is_big",
            &[1, 1, 40],
            |v| v.last().is_some_and(|&x| x >= 40),
            &[40],
        ),
        (
            "only_the_original",
            &[3, 2, 1],
            |v| *v == [3, 2, 1],
            &[3, 2, 1],
        ),
    ];
    for &(name, start, fails, expected) in vec_rows {
        h.case(format!("shrink::vec::{name}"), move || {
            assert_eq!(shrink(start.to_vec(), fails), expected);
        });
    }
    let string_rows: &[(&str, &str, fn(&String) -> bool, &str)] = &[
        ("to_empty", "hello", |_| true, ""),
        ("substring", "xxabxx", |s| s.contains("ab"), "ab"),
        ("needs_length", "qqqqqq", |s| s.len() >= 2, "aa"),
        ("char_kept", "12z34", |s| s.contains('z'), "z"),
        ("multibyte", "α→β", |s| s.contains('→'), "→"),
        ("multibyte_to_a", "αβ", |s| s.chars().count() == 2, "aa"),
        ("only_the_original", "ok", |s| s == "ok", "ok"),
    ];
    for &(name, start, fails, expected) in string_rows {
        h.case(format!("shrink::string::{name}"), move || {
            assert_eq!(shrink(start.to_owned(), fails), expected);
        });
    }
    h.case("shrink::tuple2::sum", || {
        let (a, b) = shrink((30u32, 40u32), |&(a, b)| a + b >= 10);
        assert_eq!(a + b, 10, "({a}, {b})");
    });
    h.case("shrink::tuple2::each_side_independently", || {
        assert_eq!(shrink((30u32, 40u32), |&(a, b)| a >= 3 && b >= 4), (3, 4));
    });
    h.case("shrink::tuple3::each_side_independently", || {
        let found = shrink((30u32, 40u8, 50i64), |&(a, b, c)| {
            a >= 3 && b >= 4 && c >= 5
        });
        assert_eq!(found, (3, 4, 5));
    });
    h.case("shrink::tuple::mixed_types", || {
        let found = shrink((vec![1u8, 2, 3], String::from("abc")), |(v, s)| {
            v.contains(&2) && s.contains('c')
        });
        assert_eq!(found, (vec![2], String::from("c")));
    });
    h.case("shrink::nested::vec_of_options", || {
        let start = vec![None, Some(9u8), None, Some(200)];
        let found = shrink(start, |v| v.iter().flatten().any(|&x| x >= 100));
        assert_eq!(found, vec![Some(100)]);
    });
    h.case("shrink::nested::vec_of_strings", || {
        let start = vec!["keep me".to_owned(), "drop".to_owned(), "x".to_owned()];
        let found = shrink(start, |v| {
            v.iter().any(|s| s.contains('p') && s.contains('k'))
        });
        assert_eq!(found, vec!["kp".to_owned()]);
    });
    h.case("shrink::user_type", || {
        let start = Program {
            instructions: vec![1, 2, 3, 4, 5, 6],
            optimised: true,
        };
        let found = shrink(start, |p| p.optimised && p.instructions.contains(&4));
        let expected = Program {
            instructions: vec![4],
            optimised: true,
        };
        assert_eq!(found, expected);
    });
    h.case(
        "shrink::user_type_drops_a_flag_that_does_not_matter",
        || {
            let start = Program {
                instructions: vec![9, 9],
                optimised: true,
            };
            let found = shrink(start, |p| p.instructions.len() == 2);
            let expected = Program {
                instructions: vec![0, 0],
                optimised: false,
            };
            assert_eq!(found, expected);
        },
    );
    case_candidates(h, "shrink::candidates::vec".into(), vec![1u8, 2, 3, 0, 9]);
    case_candidates(
        h,
        "shrink::candidates::string".into(),
        String::from("hello"),
    );
    case_candidates(h, "shrink::candidates::option".into(), Some(3u8));
    case_candidates(h, "shrink::candidates::tuple".into(), (1u8, true));
    case_candidates(h, "shrink::candidates::tuple3".into(), (1u8, true, 'x'));
    h.case("shrink::candidates::vec_tries_the_empty_vec_first", || {
        let first = vec![1u8, 2, 3].candidates().next();
        assert_eq!(first, Some(Vec::new()));
    });
    h.case(
        "shrink::candidates::vec_removals_cover_every_element",
        || {
            let source = vec![10u8, 20, 30, 40, 50, 60, 70];
            for missing in &source {
                let expected: Vec<u8> = source.iter().copied().filter(|x| x != missing).collect();
                assert!(
                    source.candidates().any(|candidate| candidate == expected),
                    "no candidate removes just {missing}"
                );
            }
        },
    );
    h.case("shrink::candidates::are_lazy_on_large_input", || {
        // Building these eagerly would need about 80 GB.
        let large = vec![1u64; 100_000];
        let mut taken = large.candidates();
        assert_eq!(taken.next().map(|v| v.len()), Some(0));
        assert_eq!(taken.next().map(|v| v.len()), Some(50_000));
    });
}

fn register_known_bugs(h: &mut Harness) {
    h.case("shrink::bug::sort_that_drops_duplicates", || {
        let start = vec![5, 3, 8, 3, 9, 1, 7, 7, 2];
        let found = shrink(start, |v| buggy_sort(v).len() != v.len());
        assert_eq!(
            found,
            vec![7, 7],
            "two equal elements, and neither alone can change"
        );
    });
    h.case("shrink::bug::u8_sum_overflow", || {
        let start = vec![200u8, 100, 100, 50];
        let found = shrink(start, |v| sum_overflows_u8(v));
        assert_eq!(
            found.iter().map(|&x| u32::from(x)).sum::<u32>(),
            256,
            "{found:?}"
        );
        assert!(found.len() <= 2, "{found:?}");
    });
    h.case("shrink::bug::parser_rejects_a_nested_bracket", || {
        let found = shrink("let x = [1, [2], 3];".to_owned(), |s| {
            let mut depth = 0;
            s.chars().any(|c| {
                depth += i32::from(c == '[') - i32::from(c == ']');
                depth >= 2
            })
        });
        assert_eq!(found, "[[");
    });
    h.case("shrink::bug::one_bad_byte_in_a_large_input", || {
        let mut start = vec![0u8; 20_000];
        start[12_345] = 0xFF;
        let calls = Cell::new(0);
        let found = shrink(start, |v: &Vec<u8>| {
            calls.set(calls.get() + 1);
            v.contains(&0xFF)
        });
        assert_eq!(found, vec![0xFF]);
        assert!(calls.get() < 200, "{} calls for one bad byte", calls.get());
    });
    h.case(
        "shrink::bug::generated_inputs_shrink_to_the_same_minimum",
        || {
            let mut rng = rng_for("shrink-generated");
            for _ in 0..scaled(50) {
                let length = rng.below(40) + 2;
                let mut start: Vec<u64> = (0..length).map(|_| rng.below(100)).collect();
                start[0] = 1000 + rng.below(1000);
                let found = shrink(start, |v| v.iter().any(|&x| x >= 1000));
                assert_eq!(found, vec![1000]);
            }
        },
    );
    h.case("shrink::is_deterministic", || {
        let start: Vec<u32> = (0..64).map(|x| x * 7 % 31).collect();
        let fails = |v: &Vec<u32>| v.iter().filter(|&&x| x > 20).count() >= 3;
        assert_eq!(shrink(start.clone(), fails), shrink(start, fails));
    });
    h.case("shrink::every_step_still_fails", || {
        let start: Vec<u32> = (0..32).collect();
        let accepted = Cell::new(0);
        let fails = |v: &Vec<u32>| {
            let failing = v.iter().sum::<u32>() >= 50;
            accepted.set(accepted.get() + u32::from(failing));
            failing
        };
        let found = shrink(start, fails);
        assert!(found.iter().sum::<u32>() >= 50, "{found:?}");
        assert!(accepted.get() > 0);
    });
    h.case("shrink::a_local_minimum_has_no_failing_candidate", || {
        let fails = |v: &Vec<u32>| v.iter().map(|&x| x % 7).sum::<u32>() >= 9;
        let found = shrink(vec![6, 5, 4, 3, 2, 1], fails);
        assert!(fails(&found), "{found:?}");
        assert!(
            found.candidates().all(|candidate| !fails(&candidate)),
            "{found:?}"
        );
    });
    h.case("shrink::keeps_the_input_if_nothing_simpler_fails", || {
        assert_eq!(shrink(77u32, |_| false), 77);
        assert_eq!(shrink(vec![1u8, 2], |_| false), vec![1, 2]);
    });
}

fn register_bounds(h: &mut Harness) {
    h.case(
        "shrink::bound::a_candidate_equal_to_its_source_cannot_hang",
        || {
            let calls = Cell::new(0usize);
            let found = shrink(Stuck(4), |_| {
                calls.set(calls.get() + 1);
                true
            });
            assert_eq!(found, Stuck(4));
            assert_eq!(calls.get(), SHRINK_ATTEMPTS);
        },
    );
    h.case("shrink::bound::endless_candidates_cannot_hang", || {
        let calls = Cell::new(0usize);
        let found = shrink_within(Endless(0), 500, |_| {
            calls.set(calls.get() + 1);
            false
        });
        assert_eq!(found, Endless(0));
        assert_eq!(calls.get(), 500);
    });
    for limit in [0, 1, 2, 3, 10] {
        h.case(
            format!("shrink::bound::respects_a_limit_of_{limit}"),
            move || {
                let calls = Cell::new(0usize);
                shrink_within(1_000_000u64, limit, |_| {
                    calls.set(calls.get() + 1);
                    false
                });
                assert_eq!(calls.get(), limit);
            },
        );
    }
    h.case("shrink::bound::a_limit_of_zero_returns_the_input", || {
        assert_eq!(shrink_within(55u8, 0, |_| true), 55);
    });
    h.case("shrink::bound::integers_take_few_attempts", || {
        for start in [1u64 << 16, 1 << 32, 1 << 48, u64::MAX] {
            let calls = Cell::new(0usize);
            let found = shrink(start, |&x| {
                calls.set(calls.get() + 1);
                x >= 12_345
            });
            assert_eq!(found, 12_345);
            assert!(
                calls.get() < 64 * 64,
                "{} attempts from {start}",
                calls.get()
            );
        }
    });
}
