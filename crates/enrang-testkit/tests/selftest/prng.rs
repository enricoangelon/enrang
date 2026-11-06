//! The generators: pinned answers, uniformity, absence of modulo bias, boundary
//! values, and the seed and scale knobs.

use std::collections::BTreeSet;
use std::sync::OnceLock;
use std::time::Duration;

use enrang_testkit::{
    DEFAULT_SEED, Harness, Rng, SplitMix64, Xoshiro256, catch_panic, parse_scale, parse_seed,
    rng_for, scaled, speed_budget,
};

use crate::support::{child, read_doc};

/// TESTING 14, repeated so that the pins hold even if the document's are reformatted.
const SPLITMIX_PINS: [u64; 3] = [
    0xE220_A839_7B1D_CDAF,
    0x6E78_9E6A_A1B9_65F4,
    0x06C4_5D18_8009_454F,
];
const XOSHIRO_PINS: [u64; 3] = [
    0x99EC_5F36_CB75_F2B4,
    0xBF6E_1F78_4956_452A,
    0x1A5F_849D_4933_E6E0,
];

/// SplitMix64 from seed 1234567, the published reference vector.
const SPLITMIX_REFERENCE: [u64; 5] = [
    6_457_827_717_110_365_317,
    3_203_168_211_198_807_973,
    9_817_491_932_198_370_423,
    4_593_380_528_125_082_431,
    16_408_922_859_458_223_821,
];

/// xoshiro256** from state 1, 2, 3, 4, the published reference vector.
const XOSHIRO_REFERENCE: [u64; 4] = [11_520, 0, 1_509_978_240, 1_215_971_899_390_074_240];

/// xoshiro256** seeded through SplitMix64 from 0: its 1000th output.
const XOSHIRO_DRAW_1000: u64 = 8_839_594_410_463_124_783;

/// A source that plays back a script, to observe exactly what a draw consumes.
struct Script {
    values: Vec<u64>,
    consumed: usize,
}

impl Script {
    fn new(values: &[u64]) -> Script {
        Script {
            values: values.to_vec(),
            consumed: 0,
        }
    }
}

impl Rng for Script {
    fn next_u64(&mut self) -> u64 {
        let value = self.values[self.consumed];
        self.consumed += 1;
        value
    }
}

/// Pearson's statistic of bucket counts against a uniform distribution.
fn chi_squared(counts: &[u64]) -> f64 {
    let total: u64 = counts.iter().sum();
    let expected = total as f64 / counts.len() as f64;
    counts
        .iter()
        .map(|&count| {
            let difference = count as f64 - expected;
            difference * difference / expected
        })
        .sum()
}

/// The chi-squared limit for six standard deviations, about one false alarm in
/// 10^9, by the Wilson-Hilferty approximation. It holds for any `ENRANG_SEED`.
fn chi_limit(buckets: usize) -> f64 {
    let degrees = (buckets - 1) as f64;
    let spread = 2.0 / (9.0 * degrees);
    degrees * (1.0 - spread + 6.0 * spread.sqrt()).powi(3)
}

fn assert_uniform(label: &str, counts: &[u64]) {
    let statistic = chi_squared(counts);
    let limit = chi_limit(counts.len());
    assert!(
        statistic < limit,
        "{label}: chi-squared {statistic:.1} over {} buckets is above {limit:.1}: {counts:?}",
        counts.len()
    );
}

fn counts_below(rng: &mut impl Rng, n: u64, draws: usize) -> Vec<u64> {
    let mut counts = vec![0u64; n as usize];
    for _ in 0..draws {
        let value = rng.below(n);
        assert!(value < n, "below({n}) returned {value}");
        counts[value as usize] += 1;
    }
    counts
}

const UNIFORM_MODULI: [u64; 22] = [
    2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 16, 17, 31, 32, 33, 100, 127, 128, 255, 256, 257,
];

/// `k << s` just below `2^64`: moduli where taking `x % n` alone gives some results
/// twice the chance of others, because `2^64` is less than two multiples of `n`.
const LOPSIDED: [(u64, u32); 7] = [
    (3, 62),
    (5, 61),
    (7, 61),
    (9, 60),
    (11, 60),
    (13, 60),
    (15, 60),
];

fn lopsided_counts(
    draw: &mut impl FnMut(u64) -> u64,
    k: u64,
    shift: u32,
    draws: usize,
) -> Vec<u64> {
    let n = k << shift;
    let mut counts = vec![0u64; k as usize];
    for _ in 0..draws {
        let value = draw(n);
        assert!(value < n, "a draw below {n} returned {value}");
        counts[(value >> shift) as usize] += 1;
    }
    counts
}

fn doc_pins(line_start: &str) -> Vec<u64> {
    let doc = read_doc("TESTING.md");
    let line = doc
        .lines()
        .find(|line| line.starts_with(line_start))
        .unwrap_or_else(|| panic!("TESTING 14 has no line starting `{line_start}`"));
    line.split_whitespace()
        .filter_map(|word| word.strip_prefix("0x"))
        .map(|hex| u64::from_str_radix(hex, 16).expect("a pin is hexadecimal"))
        .collect()
}

/// A large shared sample of `edge_u64`, so a case per boundary stays cheap.
fn edge_sample() -> &'static BTreeSet<u64> {
    static SAMPLE: OnceLock<BTreeSet<u64>> = OnceLock::new();
    SAMPLE.get_or_init(|| {
        let mut rng = rng_for("prng::edge_sample");
        (0..400_000).map(|_| rng.edge_u64()).collect()
    })
}

/// Whether a value is a boundary by the definition in `Rng::edge_u64`, written out
/// independently of it.
fn is_boundary(x: u64) -> bool {
    let near_power = |v: u64| {
        [v.wrapping_sub(1), v, v.wrapping_add(1)]
            .iter()
            .any(|w| w.is_power_of_two())
    };
    x <= 4 || x >= u64::MAX - 4 || near_power(x) || near_power(x.wrapping_neg())
}

pub fn register(h: &mut Harness) {
    register_known_answers(h);
    register_streams(h);
    register_below(h);
    register_edges(h);
    register_knobs(h);
}

fn register_known_answers(h: &mut Harness) {
    for (index, pin) in SPLITMIX_PINS.into_iter().enumerate() {
        h.case(format!("prng::pin::splitmix64_seed0[{index}]"), move || {
            let mut rng = SplitMix64::new(0);
            let value = (0..=index).map(|_| rng.next_u64()).last();
            assert_eq!(value, Some(pin));
        });
    }
    for (index, pin) in XOSHIRO_PINS.into_iter().enumerate() {
        h.case(format!("prng::pin::xoshiro256_seed0[{index}]"), move || {
            let mut rng = Xoshiro256::new(0);
            let value = (0..=index).map(|_| rng.next_u64()).last();
            assert_eq!(value, Some(pin));
        });
    }
    h.case("prng::pin::default_seed_spells_enrang", || {
        let bytes = [0, 0, b'E', b'N', b'R', b'A', b'N', b'G'];
        assert_eq!(DEFAULT_SEED, u64::from_be_bytes(bytes));
        assert_eq!(DEFAULT_SEED, 76_202_689_777_223);
    });
    // Computed independently of this crate, from the published algorithms. A pin on
    // a far draw shows that the state is carried, and one on a sum over the derived
    // draws pins the stream a printed seed must reproduce, beyond the values it reaches.
    h.case("prng::pin::xoshiro256_seed0_at_draw_1000", || {
        let mut rng = Xoshiro256::new(0);
        let value = (0..1000).map(|_| rng.next_u64()).last();
        assert_eq!(value, Some(XOSHIRO_DRAW_1000));
    });
    h.case("prng::pin::edge_u64_stream", || {
        let mut rng = Xoshiro256::new(0);
        let sum = (0..1000).fold(0u64, |sum, _| sum.wrapping_add(rng.edge_u64()));
        assert_eq!(sum, 15_525_961_468_281_213_874);
    });
    h.case("prng::pin::below_stream", || {
        let mut rng = Xoshiro256::new(0);
        let sum = (0..1000).fold(0u64, |sum, _| sum + rng.below(1000));
        assert_eq!(sum, 487_880);
    });
    h.case("prng::pin::pins_equal_the_document", || {
        assert_eq!(doc_pins("SplitMix64(seed 0):"), SPLITMIX_PINS);
        assert_eq!(doc_pins("xoshiro256** seeded from above:"), XOSHIRO_PINS);
    });
    h.case("prng::reference::splitmix64_seed_1234567", || {
        let mut rng = SplitMix64::new(1_234_567);
        let values: Vec<u64> = (0..5).map(|_| rng.next_u64()).collect();
        assert_eq!(values, SPLITMIX_REFERENCE);
    });
    h.case("prng::reference::xoshiro256_state_1234", || {
        let mut rng = Xoshiro256::from_state([1, 2, 3, 4]);
        let values: Vec<u64> = (0..4).map(|_| rng.next_u64()).collect();
        assert_eq!(values, XOSHIRO_REFERENCE);
    });
    h.case("prng::xoshiro_state_is_four_splitmix_outputs", || {
        let mut mix = SplitMix64::new(0xABCD);
        let state = [
            mix.next_u64(),
            mix.next_u64(),
            mix.next_u64(),
            mix.next_u64(),
        ];
        let mut from_state = Xoshiro256::from_state(state);
        let mut from_seed = Xoshiro256::new(0xABCD);
        for _ in 0..64 {
            assert_eq!(from_state.next_u64(), from_seed.next_u64());
        }
    });
    h.case("prng::xoshiro_refuses_the_zero_state", || {
        let message = catch_panic(|| Xoshiro256::from_state([0; 4])).expect("it must panic");
        assert!(message.contains("all-zero"), "{message}");
    });
    h.case("prng::xoshiro_accepts_one_set_bit", || {
        let mut rng = Xoshiro256::from_state([0, 0, 0, 1]);
        let distinct: BTreeSet<u64> = (0..16).map(|_| rng.next_u64()).collect();
        assert!(distinct.len() > 8, "{distinct:?}");
    });
}

/// A cheap smoke check, and no evidence that the generator is right: any mixing
/// function passes these. The pins and reference vectors above are what say that.
fn register_streams(h: &mut Harness) {
    for seed in [0, 1, 2, 42, 0xDEAD_BEEF, u64::MAX, u64::MAX / 2] {
        h.case(
            format!("prng::stream::same_seed_same_values::{seed}"),
            move || {
                let (mut a, mut b) = (Xoshiro256::new(seed), Xoshiro256::new(seed));
                let (mut c, mut d) = (SplitMix64::new(seed), SplitMix64::new(seed));
                for _ in 0..256 {
                    assert_eq!(a.next_u64(), b.next_u64());
                    assert_eq!(c.next_u64(), d.next_u64());
                }
            },
        );
        h.case(
            format!("prng::stream::next_seed_differs::{seed}"),
            move || {
                let mut a = Xoshiro256::new(seed);
                let mut b = Xoshiro256::new(seed.wrapping_add(1));
                let same = (0..256).filter(|_| a.next_u64() == b.next_u64()).count();
                assert_eq!(
                    same, 0,
                    "seeds {seed} and its successor share {same} values"
                );
            },
        );
        h.case(format!("prng::stream::no_short_cycle::{seed}"), move || {
            let mut rng = Xoshiro256::new(seed);
            let values: BTreeSet<u64> = (0..4096).map(|_| rng.next_u64()).collect();
            assert_eq!(values.len(), 4096);
        });
    }
    h.case("prng::stream::a_clone_continues_identically", || {
        let mut original = Xoshiro256::new(9);
        original.next_u64();
        let mut copy = original.clone();
        for _ in 0..64 {
            assert_eq!(original.next_u64(), copy.next_u64());
        }
    });
    h.case("prng::stream::draws_work_through_a_trait_object", || {
        let mut concrete = Xoshiro256::new(5);
        let mut boxed: Box<dyn Rng> = Box::new(Xoshiro256::new(5));
        for _ in 0..64 {
            assert_eq!(boxed.below(1000), concrete.below(1000));
            assert_eq!(boxed.edge_u64(), concrete.edge_u64());
        }
    });
}

fn register_below(h: &mut Harness) {
    for n in UNIFORM_MODULI {
        let draws = scaled(20_000.max(n as usize * 100));
        h.case(format!("prng::below::uniform::xoshiro::n={n}"), move || {
            let mut rng = rng_for(&format!("below-xoshiro-{n}"));
            assert_uniform("xoshiro", &counts_below(&mut rng, n, draws));
        });
        h.case(
            format!("prng::below::uniform::splitmix::n={n}"),
            move || {
                let mut rng = SplitMix64::new(rng_for(&format!("below-splitmix-{n}")).next_u64());
                assert_uniform("splitmix", &counts_below(&mut rng, n, draws));
            },
        );
    }
    for n in [2, 3, 4, 5, 6, 7, 8, 10] {
        h.case(
            format!("prng::below::pairs_are_uniform::n={n}"),
            move || {
                let mut rng = rng_for(&format!("below-pairs-{n}"));
                let mut counts = vec![0u64; (n * n) as usize];
                for _ in 0..scaled(40_000) {
                    let (first, second) = (rng.below(n), rng.below(n));
                    counts[(first * n + second) as usize] += 1;
                }
                assert_uniform("consecutive draws", &counts);
            },
        );
    }
    h.case(
        "prng::below::check_catches_a_counter_passed_off_as_pairs",
        || {
            // A source with perfect marginals and no independence, so the pair check
            // above is shown to be able to fail.
            let mut counts = vec![0u64; 16];
            for draw in 0..40_000u64 {
                let (first, second) = (draw % 4, (draw + 1) % 4);
                counts[(first * 4 + second) as usize] += 1;
            }
            assert!(chi_squared(&counts) > chi_limit(16));
        },
    );
    for (k, shift) in LOPSIDED {
        h.case(format!("prng::below::no_modulo_bias::k={k}"), move || {
            let mut rng = rng_for(&format!("below-bias-{k}"));
            let counts = lopsided_counts(&mut |n: u64| rng.below(n), k, shift, scaled(30_000));
            assert_uniform("below", &counts);
        });
        h.case(
            format!("prng::below::naive_modulo_is_caught::k={k}"),
            move || {
                let mut rng = rng_for(&format!("below-naive-{k}"));
                let counts = lopsided_counts(&mut |n: u64| rng.next_u64() % n, k, shift, 30_000);
                let statistic = chi_squared(&counts);
                let limit = chi_limit(counts.len());
                assert!(
                    statistic > limit,
                    "the check cannot see modulo bias: {statistic:.1} is under {limit:.1}"
                );
            },
        );
    }
    // Modulus, the source's script, the value `below` must return, and how many
    // values it must consume. Rejected values are the lowest `2^64 mod n` of the source.
    let rejection: &[(u64, &[u64], u64, usize)] = &[
        (1, &[0], 0, 1),
        (1, &[u64::MAX], 0, 1),
        (2, &[7], 1, 1),
        (3, &[0, 1], 1, 2),
        (3, &[0, 0, 0, 2], 2, 4),
        (10, &[0, 5, 6], 6, 3),
        (10, &[u64::MAX], 5, 1),
        (1 << 63, &[0], 0, 1),
        (1 << 63, &[u64::MAX], (1 << 63) - 1, 1),
        (3 << 62, &[0, (1 << 62) - 1, 1 << 62], 1 << 62, 3),
        (3 << 62, &[u64::MAX], (1 << 62) - 1, 1),
        (u64::MAX, &[0, 1], 1, 2),
        (u64::MAX, &[0, u64::MAX], 0, 2),
    ];
    for (index, &(n, script, expected, consumed)) in rejection.iter().enumerate() {
        h.case(
            format!("prng::below::rejection[{index}]::n={n}"),
            move || {
                let mut source = Script::new(script);
                assert_eq!(source.below(n), expected);
                assert_eq!(source.consumed, consumed);
            },
        );
    }
    for n in [
        1,
        2,
        3,
        1 << 32,
        (1 << 32) + 1,
        1 << 63,
        (1 << 63) + 1,
        u64::MAX - 1,
        u64::MAX,
    ] {
        h.case(format!("prng::below::stays_in_range::n={n}"), move || {
            let mut rng = rng_for("below-range");
            for _ in 0..scaled(5_000) {
                let value = rng.below(n);
                assert!(value < n, "below({n}) returned {value}");
            }
        });
    }
    h.case("prng::below::one_is_always_zero", || {
        let mut rng = rng_for("below-one");
        assert!((0..2_000).all(|_| rng.below(1) == 0));
    });
    h.case("prng::below::zero_panics", || {
        let mut rng = Xoshiro256::new(1);
        let message = catch_panic(|| rng.below(0)).expect("below(0) must panic");
        assert!(message.contains("below(0)"), "{message}");
    });
}

fn register_edges(h: &mut Harness) {
    let mut boundaries: Vec<(String, u64)> = Vec::new();
    for small in 0..=4u64 {
        boundaries.push((format!("{small}"), small));
        boundaries.push((format!("max-{small}"), u64::MAX - small));
    }
    for k in 0..64u32 {
        let power = 1u64 << k;
        boundaries.push((format!("2^{k}"), power));
        boundaries.push((format!("2^{k}-1"), power - 1));
        boundaries.push((format!("2^{k}+1"), power + 1));
        boundaries.push((format!("-2^{k}"), power.wrapping_neg()));
        boundaries.push((format!("-2^{k}-1"), power.wrapping_neg().wrapping_sub(1)));
        boundaries.push((format!("-2^{k}+1"), power.wrapping_neg().wrapping_add(1)));
    }
    let named: [(&str, u64); 14] = [
        ("i8::MIN", i8::MIN as i64 as u64),
        ("i8::MAX", i8::MAX as u64),
        ("u8::MAX", u64::from(u8::MAX)),
        ("i16::MIN", i16::MIN as i64 as u64),
        ("i16::MAX", i16::MAX as u64),
        ("u16::MAX", u64::from(u16::MAX)),
        ("i32::MIN", i32::MIN as i64 as u64),
        ("i32::MAX", i32::MAX as u64),
        ("u32::MAX", u64::from(u32::MAX)),
        ("i64::MIN", i64::MIN as u64),
        ("i64::MAX", i64::MAX as u64),
        ("u64::MAX", u64::MAX),
        ("2^31", 0x8000_0000),
        ("2^32", 0x1_0000_0000),
    ];
    for (name, value) in named {
        boundaries.push((format!("named::{name}"), value));
    }
    for (name, value) in boundaries {
        h.case(format!("prng::edge::reaches::{name}"), move || {
            assert!(edge_sample().contains(&value), "never drew {value:#x}");
        });
    }
    h.case("prng::edge::three_draws_in_four_are_boundaries", || {
        let mut rng = rng_for("edge-fraction");
        let draws = scaled(50_000);
        let hits = (0..draws).filter(|_| is_boundary(rng.edge_u64())).count();
        let fraction = hits as f64 / draws as f64;
        assert!((0.70..0.80).contains(&fraction), "fraction {fraction}");
    });
    h.case(
        "prng::edge::the_boundary_check_rejects_a_plain_stream",
        || {
            let mut rng = rng_for("edge-plain");
            let draws = 50_000;
            let hits = (0..draws).filter(|_| is_boundary(rng.next_u64())).count();
            assert!(
                hits < draws / 100,
                "{hits} of {draws} uniform draws look like boundaries"
            );
        },
    );
    h.case("prng::edge::keeps_a_uniform_share", || {
        let mut rng = rng_for("edge-uniform");
        let draws = scaled(50_000);
        let others: BTreeSet<u64> = (0..draws)
            .map(|_| rng.edge_u64())
            .filter(|&value| !is_boundary(value))
            .collect();
        assert!(
            others.len() > draws / 8,
            "{} distinct non-boundaries",
            others.len()
        );
    });
    h.case("prng::edge::is_deterministic", || {
        let (mut a, mut b) = (Xoshiro256::new(77), Xoshiro256::new(77));
        for _ in 0..1000 {
            assert_eq!(a.edge_u64(), b.edge_u64());
        }
    });
    h.case("prng::edge::splitmix_reaches_the_extremes_too", || {
        let mut rng = SplitMix64::new(3);
        let values: BTreeSet<u64> = (0..50_000).map(|_| rng.edge_u64()).collect();
        for needed in [
            0,
            1,
            u64::MAX,
            1 << 63,
            (1 << 63) - 1,
            1 << 32,
            u64::from(u32::MAX),
        ] {
            assert!(values.contains(&needed), "never drew {needed:#x}");
        }
    });
}

fn register_knobs(h: &mut Harness) {
    let seeds: &[(Option<&str>, Option<u64>)] = &[
        (None, Some(DEFAULT_SEED)),
        (Some("0"), Some(0)),
        (Some("42"), Some(42)),
        (Some(" 7 "), Some(7)),
        (Some("18446744073709551615"), Some(u64::MAX)),
        (Some("0x10"), Some(16)),
        (Some("0XfF"), Some(255)),
        (Some("0xFFFFFFFFFFFFFFFF"), Some(u64::MAX)),
        (Some(""), None),
        (Some("abc"), None),
        (Some("-1"), None),
        (Some("1.5"), None),
        (Some("18446744073709551616"), None),
        (Some("0x"), None),
        (Some("0xZZ"), None),
        (Some("0x1FFFFFFFFFFFFFFFF"), None),
    ];
    for &(input, expected) in seeds {
        h.case(
            format!("prng::knob::parse_seed::{input:?}"),
            move || match (parse_seed(input), expected) {
                (Ok(value), Some(wanted)) => assert_eq!(value, wanted),
                (Err(message), None) => assert!(message.contains("ENRANG_SEED"), "{message}"),
                (got, wanted) => panic!("got {got:?}, wanted {wanted:?}"),
            },
        );
    }
    let scales: &[(Option<&str>, Option<u64>)] = &[
        (None, Some(1)),
        (Some("1"), Some(1)),
        (Some("10"), Some(10)),
        (Some("100"), Some(100)),
        (Some(" 3 "), Some(3)),
        (Some("0"), None),
        (Some("-1"), None),
        (Some(""), None),
        (Some("ten"), None),
        (Some("1.5"), None),
        (Some("99999999999999999999999"), None),
    ];
    for &(input, expected) in scales {
        h.case(
            format!("prng::knob::parse_scale::{input:?}"),
            move || match (parse_scale(input), expected) {
                (Ok(value), Some(wanted)) => assert_eq!(value, wanted),
                (Err(message), None) => assert!(message.contains("ENRANG_SCALE"), "{message}"),
                (got, wanted) => panic!("got {got:?}, wanted {wanted:?}"),
            },
        );
    }
    let budgets: &[(u64, Option<u64>)] = &[
        (1, Some(60)),
        (2, Some(600)),
        (10, Some(600)),
        (11, None),
        (100, None),
        (u64::MAX, None),
    ];
    for &(scale, seconds) in budgets {
        h.case(format!("prng::knob::speed_budget::{scale}"), move || {
            assert_eq!(speed_budget(scale), seconds.map(Duration::from_secs));
        });
    }
    h.case("prng::knob::labels_give_independent_streams", || {
        let mut a = rng_for("one label");
        let mut b = rng_for("another label");
        let same = (0..256).filter(|_| a.next_u64() == b.next_u64()).count();
        assert_eq!(same, 0);
    });
    h.case("prng::knob::a_label_repeats_its_stream", || {
        let (mut a, mut b) = (rng_for("label"), rng_for("label"));
        for _ in 0..64 {
            assert_eq!(a.next_u64(), b.next_u64());
        }
    });
    let run_seed_scale = |vars: &'static [(&'static str, &'static str)]| {
        let output = child("seed_scale", &[], vars);
        assert_eq!(output.code, Some(0), "{}", output.stderr);
        output
            .stdout
            .lines()
            .find(|line| line.starts_with("seed="))
            .expect("the child prints its knobs")
            .to_owned()
    };
    h.case("prng::env::defaults", move || {
        let line = run_seed_scale(&[]);
        assert!(
            line.starts_with(&format!("seed={DEFAULT_SEED} scale=1 scaled=7 rng=")),
            "{line}"
        );
    });
    let env_rows: &[(&[(&str, &str)], &str)] = &[
        (&[("ENRANG_SEED", "123")], "seed=123 scale=1 scaled=7 "),
        (&[("ENRANG_SEED", "0xFF")], "seed=255 scale=1 scaled=7 "),
        (&[("ENRANG_SCALE", "10")], "scale=10 scaled=70 "),
        (&[("ENRANG_SCALE", "100")], "scale=100 scaled=700 "),
        (
            &[("ENRANG_SEED", "9"), ("ENRANG_SCALE", "3")],
            "seed=9 scale=3 scaled=21 ",
        ),
    ];
    for &(vars, expected) in env_rows {
        h.case(format!("prng::env::honoured::{vars:?}"), move || {
            let output = child("seed_scale", &[], vars);
            assert_eq!(output.code, Some(0), "{}", output.stderr);
            assert!(output.stdout.contains(expected), "{}", output.stdout);
        });
    }
    // `rng_for("label")`'s first draw, computed independently of this crate: a seed
    // printed by an older commit must go on reproducing its failure.
    let rng_for_pins: &[(&[(&str, &str)], &str)] = &[
        (&[], "rng=1113009581305904269\n"),
        (&[("ENRANG_SEED", "0")], "rng=12902060715070477779\n"),
    ];
    for &(vars, expected) in rng_for_pins {
        h.case(format!("prng::env::rng_for_pin::{vars:?}"), move || {
            let output = child("seed_scale", &[], vars);
            assert_eq!(output.code, Some(0), "{}", output.stderr);
            assert!(output.stdout.contains(expected), "{}", output.stdout);
        });
    }
    h.case("prng::env::a_huge_scale_saturates", || {
        let vars = [("ENRANG_SCALE", "18446744073709551615")];
        let output = child("seed_scale", &[], &vars);
        assert_eq!(output.code, Some(0), "{}", output.stdout);
        let expected = format!(" scaled={} ", usize::MAX);
        assert!(output.stdout.contains(&expected), "{}", output.stdout);
    });
    h.case("prng::env::the_header_shows_seed_and_scale", || {
        let vars = [("ENRANG_SEED", "123"), ("ENRANG_SCALE", "10")];
        let output = child("seed_scale", &[], &vars);
        assert!(
            output.stdout.contains("seed 123, scale 10"),
            "{}",
            output.stdout
        );
    });
    h.case("prng::env::the_seed_reproduces_rng_for", || {
        let rng_of = |seed: &'static str| {
            let output = child("seed_scale", &[], &[("ENRANG_SEED", seed)]);
            let (_, value) = output
                .stdout
                .split_once(" rng=")
                .expect("the child prints it");
            value.lines().next().unwrap_or("").to_owned()
        };
        assert_eq!(rng_of("5"), rng_of("5"));
        assert_ne!(rng_of("5"), rng_of("6"));
    });
    let invalid: &[(&str, &str)] = &[
        ("ENRANG_SEED", "banana"),
        ("ENRANG_SCALE", "0"),
        ("ENRANG_SCALE", "many"),
    ];
    for &(name, value) in invalid {
        h.case(
            format!("prng::env::invalid_stops_the_run::{name}={value}"),
            move || {
                let output = child("seed_scale", &[], &[(name, value)]);
                assert_eq!(output.code, Some(2));
                assert!(output.stderr.contains(name), "{}", output.stderr);
                assert!(!output.stdout.contains("seed="), "{}", output.stdout);
            },
        );
    }
    h.case("prng::env::seed_panics_on_a_bad_value", || {
        let output = child("seed_direct", &[], &[("ENRANG_SEED", "banana")]);
        assert!(output.stdout.contains("ENRANG_SEED"), "{}", output.stdout);
        assert!(output.stdout.starts_with("Some("), "{}", output.stdout);
    });
    h.case("prng::env::scale_panics_on_a_bad_value", || {
        let output = child("scale_direct", &[], &[("ENRANG_SCALE", "0")]);
        assert!(output.stdout.contains("ENRANG_SCALE"), "{}", output.stdout);
        assert!(output.stdout.starts_with("Some("), "{}", output.stdout);
    });
}
