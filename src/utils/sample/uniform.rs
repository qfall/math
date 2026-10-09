// Copyright 2025 Jan Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes core functionality to sample according to the
//! uniform random distribution.

use crate::{error::MathError, integer::Z};
use flint3_sys::{fmpz_addmul_ui, fmpz_set_ui};
use rand::{
    Rng, SeedableRng, TryCryptoRng, TryRng,
    rngs::{StdRng, ThreadRng},
};
use std::{cell::RefCell, convert::Infallible, rc::Rc};

/// Defines the source of randomness used by the samplers in this module.
///
/// A [`ThreadRng`] can not be seeded explicitly, as it is a handle to a
/// thread-local generator that is seeded and periodically reseeded by the OS.
/// Hence, seeded samplers use a [`StdRng`] instead, which uses the same
/// algorithm (ChaCha with 12 rounds) as [`ThreadRng`], but it's never reseeded.
///
/// Cloning a [`SamplerRng`] returns a handle to the same generator for both variants,
/// i.e. a clone and its original draw from one shared stream of randomness.
///
/// Variants:
/// - `Thread`: a handle to the [`ThreadRng`] of the current thread
/// - `Seeded`: a shared [`StdRng`] that was explicitly seeded
#[derive(Debug, Clone)]
pub(crate) enum SamplerRng {
    Thread(ThreadRng),
    Seeded(Rc<RefCell<StdRng>>),
}

impl SamplerRng {
    /// Returns a [`SamplerRng`] containing a [`StdRng`] seeded with `seed`
    /// if a seed is provided, and the [`ThreadRng`] of the current thread otherwise.
    ///
    /// Parameters:
    /// - `seed`: specifies the optional 256-bit seed for the [`StdRng`]
    pub(crate) fn new(seed: Option<[u8; 32]>) -> Self {
        match seed {
            Some(seed) => Self::Seeded(Rc::new(RefCell::new(StdRng::from_seed(seed)))),
            None => Self::Thread(rand::rng()),
        }
    }
}

impl Default for SamplerRng {
    /// Returns a [`SamplerRng`] containing the [`ThreadRng`] of the current thread.
    fn default() -> Self {
        Self::new(None)
    }
}

impl TryRng for SamplerRng {
    type Error = Infallible;

    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        match self {
            Self::Thread(rng) => rng.try_next_u32(),
            Self::Seeded(rng) => rng.borrow_mut().try_next_u32(),
        }
    }

    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        match self {
            Self::Thread(rng) => rng.try_next_u64(),
            Self::Seeded(rng) => rng.borrow_mut().try_next_u64(),
        }
    }

    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Self::Error> {
        match self {
            Self::Thread(rng) => rng.try_fill_bytes(dst),
            Self::Seeded(rng) => rng.borrow_mut().try_fill_bytes(dst),
        }
    }
}

// Both [`ThreadRng`] and [`StdRng`] are claimed to be cryptographically secure.
impl TryCryptoRng for SamplerRng {}

/// Enables uniformly random sampling a [`Z`] in `[0, interval_size)`.
///
/// Attributes:
/// - `interval_size`: defines the interval [0, interval_size), which we sample from
/// - `two_pow_32`: is a helper to shift bits by 32-bits left by multiplication
/// - `nr_iterations`: defines how many full samples of u32 are required
/// - `upper_modulo`: is a power of two to remove superfluously sampled bits to increase
///   the probability of accepting a sample to at least 1/2
/// - `rng`: defines the [`ThreadRng`] or seeded [`StdRng`] that's used to sample uniform [u32] integers
///
/// # Examples
/// ```
/// use qfall_math::{utils::sample::uniform::UniformIntegerSampler, integer::Z};
/// let interval_size = Z::from(20);
///
/// let mut uis = UniformIntegerSampler::init(&interval_size, None).unwrap();
///
/// let sample = uis.sample();
///
/// assert!(Z::ZERO <= sample);
/// assert!(sample < interval_size);
/// ```
pub struct UniformIntegerSampler {
    interval_size: Z,
    two_pow_32: u64,
    nr_iterations: u32,
    upper_modulo: u32,
    rng: SamplerRng,
}

impl UniformIntegerSampler {
    /// Initializes the [`UniformIntegerSampler`] with
    /// - `interval_size` as `interval_size`,
    /// - `two_pow_32` as a [u64] containing 2^32
    /// - `nr_iterations` as `(interval_size - 1).bits() / 32` floored
    /// - `upper_modulo` as 2^{(interval_size - 1).bits() mod 32}
    /// - `rng` as a [`StdRng`] seeded with `seed` if `seed` is provided,
    ///   and as a fresh [`ThreadRng`] otherwise
    ///
    /// Parameters:
    /// - `interval_size`: specifies the interval `[0, interval_size)`
    ///   from which the samples are drawn
    /// - `seed`: specifies an optional 256-bit seed for the internal [`StdRng`].
    ///   If `None` is provided, a fresh [`ThreadRng`] is used instead.
    ///
    /// Returns a [`UniformIntegerSampler`] or a [`MathError`],
    /// if the interval size is chosen smaller than or equal to `1`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{utils::sample::uniform::UniformIntegerSampler, integer::Z};
    /// let interval_size = Z::from(20);
    ///
    /// let mut uis = UniformIntegerSampler::init(&interval_size, None).unwrap();
    ///
    /// let mut uis_seeded_0 = UniformIntegerSampler::init(&interval_size, Some([42; 32])).unwrap();
    /// let mut uis_seeded_1 = UniformIntegerSampler::init(&interval_size, Some([42; 32])).unwrap();
    /// assert_eq!(uis_seeded_0.sample(), uis_seeded_1.sample());
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
    ///   if the interval is chosen smaller than `1`.
    pub fn init(interval_size: &Z, seed: Option<[u8; 32]>) -> Result<Self, MathError> {
        Self::init_with_rng(interval_size, SamplerRng::new(seed))
    }

    /// Initializes the [`UniformIntegerSampler`] as described in [`UniformIntegerSampler::init`]
    /// with `rng` as the source of randomness.
    ///
    /// Parameters:
    /// - `interval_size`: specifies the interval `[0, interval_size)`
    ///   from which the samples are drawn
    /// - `rng`: specifies the random number generator used as the source of randomness
    ///
    /// Returns a [`UniformIntegerSampler`] or a [`MathError`],
    /// if the interval size is chosen smaller than or equal to `1`.
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
    ///   if the interval is chosen smaller than `1`.
    pub(crate) fn init_with_rng(interval_size: &Z, rng: SamplerRng) -> Result<Self, MathError> {
        if interval_size < &Z::ONE {
            return Err(MathError::InvalidInterval(format!(
                "An invalid interval size {interval_size} was provided."
            )));
        }

        // Compute 2^32 to be able to shift bits to the left
        // by 32 bits using multiplication
        let two_pow_32 = u32::MAX as u64 + 1;

        let bit_size = (interval_size - Z::ONE).bits() as u32;

        // div rounds towards 0, i.e. div_floor in this case, i.e. this is
        // perfect for sampling the top one first and then iterating
        // nr_iterations-many times
        let nr_iterations = bit_size / 32;

        // Set upper_modulo to 2^{bit_size mod 32}
        // defines how many bits will be discarded / have been sampled too much
        let upper_modulo = 2_u32.pow(bit_size % 32);

        Ok(Self {
            interval_size: interval_size.clone(),
            two_pow_32,
            nr_iterations,
            upper_modulo,
            rng,
        })
    }

    /// Computes a uniformly chosen [`Z`] sample in `[0, interval_size)`
    /// using rejection sampling that accepts samples with probability at least 1/2.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{utils::sample::uniform::UniformIntegerSampler, integer::Z};
    /// let interval_size = Z::from(20);
    ///
    /// let mut uis = UniformIntegerSampler::init(&interval_size, None).unwrap();
    ///
    /// let sample = uis.sample();
    ///
    /// assert!(Z::ZERO <= sample);
    /// assert!(sample < interval_size);
    /// ```
    pub fn sample(&mut self) -> Z {
        if self.interval_size.is_one() {
            return Z::ZERO;
        }

        let mut sample = self.sample_bits_uniform();
        while sample >= self.interval_size {
            sample = self.sample_bits_uniform();
        }

        sample
    }

    /// Computes `self.nr_iterations * 32 + upper_modulo` many uniformly chosen bits.
    ///
    /// Returns a [`Z`] containing `self.nr_iterations * 32 + upper_modulo`-many uniformly
    /// chosen bits.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{utils::sample::uniform::UniformIntegerSampler, integer::Z};
    /// let interval = Z::from(u16::MAX) + 1;
    ///
    /// let mut uis = UniformIntegerSampler::init(&interval, None).unwrap();
    ///
    /// let sample = uis.sample_bits_uniform();
    ///
    /// assert!(Z::ZERO <= sample);
    /// assert!(sample < interval);
    /// ```
    pub fn sample_bits_uniform(&mut self) -> Z {
        // remove superfluously sampled bits to increase chance of acception to at lest 1/2
        let mut value = Z::from(self.rng.next_u32() % self.upper_modulo);

        for _ in 0..self.nr_iterations {
            let sample = self.rng.next_u32();

            let mut res = Z::default();
            unsafe {
                fmpz_set_ui(&mut res.value, sample as u64);
                // Sets res = res + value * 2^32 reusing the memory allocated of res
                // could be optimized by shifting bits left by 32 bits once lshift is part of flint-sys
                fmpz_addmul_ui(&mut res.value, &value.value, self.two_pow_32);
            };
            value = res;
        }

        value
    }
}

#[cfg(test)]
mod test_uis {
    use super::{UniformIntegerSampler, Z};
    use std::collections::HashSet;

    /// Checks whether sampling works fine for small interval sizes.
    #[test]
    fn small_interval() {
        let size_2 = Z::from(2);
        let size_7 = Z::from(7);

        let mut uis_2 = UniformIntegerSampler::init(&size_2, None).unwrap();
        let mut uis_7 = UniformIntegerSampler::init(&size_7, None).unwrap();

        for _ in 0..3 {
            let sample_2 = uis_2.sample();
            let sample_7 = uis_7.sample();

            assert!(Z::ZERO <= sample_2);
            assert!(sample_2 < size_2);
            assert!(Z::ZERO <= sample_7);
            assert!(sample_7 < size_7)
        }
    }

    /// Checks whether sampling works fine for large interval sizes.
    #[test]
    fn large_interval() {
        let size_0 = Z::from(u64::MAX);
        let size_1 = Z::from(u64::MAX) * 2 + 1;

        let mut uis_0 = UniformIntegerSampler::init(&size_0, None).unwrap();
        let mut uis_1 = UniformIntegerSampler::init(&size_1, None).unwrap();

        for _i in 0..u8::MAX {
            let sample_0 = uis_0.sample();
            let sample_1 = uis_1.sample();

            assert!(Z::ZERO <= sample_0);
            assert!(sample_0 < size_0);
            assert!(Z::ZERO <= sample_1);
            assert!(sample_1 < size_1);
        }
    }

    /// Checks whether it samples from the entire interval.
    #[test]
    fn entire_interval() {
        let interval_sizes = vec![6, 7, 16];

        for interval_size in interval_sizes {
            let interval = Z::from(interval_size);

            let mut uis = UniformIntegerSampler::init(&interval, None).unwrap();

            let mut samples = HashSet::new();
            for _ in 0..2_u32.pow(interval_size) {
                samples.insert(uis.sample());
            }
            // if len(samples) == interval_size, then every element in [0, interval_size)
            // needs to be represented in samples
            assert_eq!(
                interval_size,
                samples.len() as u32,
                "This test may fail with low probability."
            );
        }
    }

    /// Checks whether interval sizes smaller than 2 result in an error.
    #[test]
    fn invalid_interval() {
        assert!(UniformIntegerSampler::init(&Z::ZERO, None).is_err());
        assert!(UniformIntegerSampler::init(&Z::MINUS_ONE, None).is_err());
    }

    /// Checks whether random bit sampling doesn't fill more bits than required.
    #[test]
    fn sample_bits_uniform_necessary_nr_bytes() {
        let size_0 = Z::from(8);
        let size_1 = Z::from(256);
        let size_2 = Z::from(u32::MAX) + Z::ONE;

        let mut uis_0 = UniformIntegerSampler::init(&size_0, None).unwrap();
        let mut uis_1 = UniformIntegerSampler::init(&size_1, None).unwrap();
        let mut uis_2 = UniformIntegerSampler::init(&size_2, None).unwrap();

        for _ in 0..u8::MAX {
            let sample_0 = uis_0.sample_bits_uniform();
            let sample_1 = uis_1.sample_bits_uniform();
            let sample_2 = uis_2.sample_bits_uniform();

            assert!(Z::ZERO <= sample_0);
            assert!(sample_0 < size_0);
            assert!(Z::ZERO <= sample_1);
            assert!(sample_1 < size_1);
            assert!(Z::ZERO <= sample_2);
            assert!(sample_2 < size_2);
        }
    }
}

#[cfg(test)]
mod test_uis_seeded {
    use super::{UniformIntegerSampler, Z};

    /// Checks whether two samplers with the same seed output the same samples
    /// for small and large interval sizes.
    #[test]
    fn same_seed_same_samples() {
        let interval_sizes = [Z::from(2), Z::from(7), Z::from(u64::MAX) * 2 + 1];

        for interval_size in interval_sizes {
            let mut uis_0 = UniformIntegerSampler::init(&interval_size, Some([42; 32])).unwrap();
            let mut uis_1 = UniformIntegerSampler::init(&interval_size, Some([42; 32])).unwrap();

            for _ in 0..u8::MAX {
                assert_eq!(uis_0.sample(), uis_1.sample());
            }
        }
    }

    /// Checks whether two samplers with different seeds output different samples.
    #[test]
    fn different_seed_different_samples() {
        let interval_size = Z::from(u64::MAX);

        let mut uis_0 = UniformIntegerSampler::init(&interval_size, Some([0; 32])).unwrap();
        let mut uis_1 = UniformIntegerSampler::init(&interval_size, Some([1; 32])).unwrap();

        let samples_0: Vec<Z> = (0..16).map(|_| uis_0.sample()).collect();
        let samples_1: Vec<Z> = (0..16).map(|_| uis_1.sample()).collect();

        assert_ne!(samples_0, samples_1);
    }

    /// Checks whether seeded samples are kept in the interval.
    #[test]
    fn keeps_range() {
        let interval_size = Z::from(7);
        let mut uis = UniformIntegerSampler::init(&interval_size, Some([42; 32])).unwrap();

        for _ in 0..u8::MAX {
            let sample = uis.sample();

            assert!(Z::ZERO <= sample);
            assert!(sample < interval_size);
        }
    }

    /// Checks whether interval sizes smaller than 1 result in an error.
    #[test]
    fn invalid_interval() {
        assert!(UniformIntegerSampler::init(&Z::ZERO, Some([42; 32])).is_err());
        assert!(UniformIntegerSampler::init(&Z::MINUS_ONE, Some([42; 32])).is_err());
    }
}
