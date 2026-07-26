//! Dependency-free deterministic PRNG (SplitMix64, Vigna's public-domain
//! construction).
//!
//! A fuzzer's whole value proposition is reproducibility: a discrepancy found
//! at seed `N` must regenerate byte-for-byte from `N` alone, years later, with
//! no dependency-version drift in the way. That rules out pulling in the
//! `rand` crate (its output stream can change between minor versions), so we
//! ship a tiny fixed algorithm whose only contract is "same seed, same
//! sequence, forever".

#[derive(Debug, Clone)]
pub struct Rng {
    state: u64,
}

impl Rng {
    pub fn new(seed: u64) -> Self {
        // Golden-ratio constant decorrelates nearby seeds and avoids the
        // degenerate all-zero state.
        Rng {
            state: seed ^ 0x9E37_79B9_7F4A_7C15,
        }
    }

    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Uniform integer in `[0, bound)`. Panics if `bound == 0`.
    pub fn below(&mut self, bound: u64) -> u64 {
        assert!(bound > 0, "Rng::below: bound must be positive");
        self.next_u64() % bound
    }

    /// Uniform `i64` in `[lo, hi_inclusive]`.
    pub fn range_i64(&mut self, lo: i64, hi_inclusive: i64) -> i64 {
        assert!(
            hi_inclusive >= lo,
            "Rng::range_i64: empty range lo={lo} hi={hi_inclusive}"
        );
        let span = (hi_inclusive - lo) as u64 + 1;
        lo + self.below(span) as i64
    }

    /// Uniform `u32` in `[lo, hi_inclusive]`.
    pub fn range_u32(&mut self, lo: u32, hi_inclusive: u32) -> u32 {
        lo + self.below((hi_inclusive - lo) as u64 + 1) as u32
    }

    /// True with probability `numerator / denominator`.
    pub fn chance(&mut self, numerator: u64, denominator: u64) -> bool {
        self.below(denominator) < numerator
    }

    /// Uniform index into `[0, len)`. Panics if `len == 0`.
    pub fn index(&mut self, len: usize) -> usize {
        assert!(len > 0, "Rng::index: len must be positive");
        self.below(len as u64) as usize
    }

    /// Pick a random element from a non-empty slice.
    pub fn pick<'a, T>(&mut self, slice: &'a [T]) -> &'a T {
        &slice[self.index(slice.len())]
    }

    /// One Bernoulli(1/2) sample.
    pub fn coin(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn same_seed_same_sequence() {
        let mut a = Rng::new(123456);
        let mut b = Rng::new(123456);
        for _ in 0..1000 {
            assert_eq!(a.next_u64(), b.next_u64());
        }
    }

    #[test]
    fn different_seeds_differ() {
        assert_ne!(
            Rng::new(1).next_u64(),
            Rng::new(2).next_u64(),
            "seeds 1 and 2 must not collide"
        );
    }

    #[test]
    fn range_stays_in_bounds() {
        let mut rng = Rng::new(7);
        for _ in 0..10_000 {
            let v = rng.range_i64(-3, 6);
            assert!((-3..=6).contains(&v));
        }
    }

    #[test]
    fn below_never_returns_bound() {
        let mut rng = Rng::new(99);
        for _ in 0..10_000 {
            assert!(rng.below(5) < 5);
        }
    }
}
