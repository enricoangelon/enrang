//! Seeded generators and the environment knobs that steer them (TESTING 14).
//!
//! Every generator in the repository draws from these, so a failure is always
//! reproduced by its seed. An unset `ENRANG_SEED` means a fixed default rather
//! than the clock: two runs of the same commit test the same inputs.

use crate::harness::env_value;

/// The seed when `ENRANG_SEED` is unset: "ENRANG" in ASCII.
pub const DEFAULT_SEED: u64 = 0x454E_5241_4E47;

/// A source of 64-bit values. The derived draws are provided, so an
/// implementation only supplies [`Rng::next_u64`].
pub trait Rng {
    fn next_u64(&mut self) -> u64;

    /// A uniform value in `0..n`.
    ///
    /// `x % n` alone favours small results, because `2^64` is rarely a multiple
    /// of `n`. So the lowest `2^64 mod n` values of the source are rejected,
    /// which leaves a range that is an exact multiple of `n`.
    ///
    /// # Panics
    ///
    /// If `n` is zero, since the range is then empty.
    fn below(&mut self, n: u64) -> u64 {
        assert!(n != 0, "Rng::below(0): the range 0..0 is empty");
        let rejected = n.wrapping_neg() % n;
        loop {
            let x = self.next_u64();
            if x >= rejected {
                return x % n;
            }
        }
    }

    /// A value weighted towards the boundaries where integer code breaks: three
    /// draws in four are a boundary, one in four is uniform.
    ///
    /// The boundaries are the values next to 0 and `u64::MAX`, every `2^k` and
    /// its neighbours, and every `-(2^k)` and its neighbours. Those cover the
    /// limits of all narrower signed and unsigned types, zero- and sign-extended.
    fn edge_u64(&mut self) -> u64 {
        match self.below(8) {
            0 => self.below(5),
            1 => u64::MAX - self.below(5),
            2 => 1 << self.below(64),
            3 => (1u64 << self.below(64)) - 1,
            4 => (1u64 << self.below(64)) + 1,
            5 => (u64::MAX << self.below(64))
                .wrapping_add(self.below(3))
                .wrapping_sub(1),
            _ => self.next_u64(),
        }
    }
}

/// SplitMix64: seeds [`Xoshiro256`] and turns any `u64` into a usable state.
#[derive(Clone, Debug)]
pub struct SplitMix64(u64);

impl SplitMix64 {
    pub fn new(seed: u64) -> SplitMix64 {
        SplitMix64(seed)
    }
}

impl Rng for SplitMix64 {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

/// xoshiro256**, the generator the suites draw from.
#[derive(Clone, Debug)]
pub struct Xoshiro256([u64; 4]);

impl Xoshiro256 {
    /// The state is the first four outputs of `SplitMix64(seed)`.
    pub fn new(seed: u64) -> Xoshiro256 {
        let mut mix = SplitMix64::new(seed);
        Xoshiro256([
            mix.next_u64(),
            mix.next_u64(),
            mix.next_u64(),
            mix.next_u64(),
        ])
    }

    /// Resumes from a state, such as the reference vectors of the algorithm.
    ///
    /// # Panics
    ///
    /// If the state is all zero, the one state the generator never leaves.
    pub fn from_state(state: [u64; 4]) -> Xoshiro256 {
        assert!(
            state != [0; 4],
            "Xoshiro256::from_state: an all-zero state only ever yields zero"
        );
        Xoshiro256(state)
    }
}

impl Rng for Xoshiro256 {
    fn next_u64(&mut self) -> u64 {
        let [s0, s1, s2, s3] = &mut self.0;
        let result = s1.wrapping_mul(5).rotate_left(7).wrapping_mul(9);
        let t = *s1 << 17;
        *s2 ^= *s0;
        *s3 ^= *s1;
        *s1 ^= *s2;
        *s0 ^= *s3;
        *s2 ^= t;
        *s3 = s3.rotate_left(45);
        result
    }
}

/// Parses an `ENRANG_SEED` value, decimal or `0x` hexadecimal. `None` is the
/// default seed.
pub fn parse_seed(value: Option<&str>) -> Result<u64, String> {
    let Some(text) = value else {
        return Ok(DEFAULT_SEED);
    };
    let digits = text.trim();
    let parsed = match digits
        .strip_prefix("0x")
        .or_else(|| digits.strip_prefix("0X"))
    {
        Some(hex) => u64::from_str_radix(hex, 16),
        None => digits.parse(),
    };
    parsed.map_err(|_| {
        format!("ENRANG_SEED={text:?} is not a 64-bit integer, decimal or 0x hexadecimal")
    })
}

/// Parses an `ENRANG_SCALE` value, a positive integer. `None` is 1, a tenth of
/// the full volume (TESTING 14). Zero is refused, since it would turn every
/// generated suite into one that tests nothing and still passes.
pub fn parse_scale(value: Option<&str>) -> Result<u64, String> {
    let Some(text) = value else {
        return Ok(1);
    };
    match text.trim().parse() {
        Ok(0) | Err(_) => Err(format!("ENRANG_SCALE={text:?} is not a positive integer")),
        Ok(n) => Ok(n),
    }
}

/// The seed of this run.
///
/// # Panics
///
/// If `ENRANG_SEED` is set but not a number. Running on some other seed instead
/// would look like a reproduction and not be one.
pub fn seed() -> u64 {
    parse_seed(env_value("ENRANG_SEED").as_deref()).unwrap_or_else(|message| panic!("{message}"))
}

/// The volume multiplier of this run.
///
/// # Panics
///
/// If `ENRANG_SCALE` is set but not a positive integer.
pub fn scale() -> u64 {
    parse_scale(env_value("ENRANG_SCALE").as_deref()).unwrap_or_else(|message| panic!("{message}"))
}

/// `base`, the volume at scale 1, multiplied by this run's scale.
pub fn scaled(base: usize) -> usize {
    let factor = usize::try_from(scale()).unwrap_or(usize::MAX);
    base.saturating_mul(factor)
}

/// The generator for one named stream of this run: independent of every other
/// label, and reproduced by the same `ENRANG_SEED` and label.
pub fn rng_for(label: &str) -> Xoshiro256 {
    Xoshiro256::new(seed() ^ fnv1a(label))
}

fn fnv1a(text: &str) -> u64 {
    let mut hash = 0xCBF2_9CE4_8422_2325_u64;
    for byte in text.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01B3);
    }
    hash
}
