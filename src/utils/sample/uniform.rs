// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes core functionality to sample according to the
//! uniform random distribution.

use crate::{error::MathError, integer::Z};
use flint_sys::fmpz::{fmpz, fmpz_addmul_ui, fmpz_set_ui};
use rand::{rngs::ThreadRng, RngCore, TryRngCore};

/// Enables uniformly random sampling a [`Z`] in `[0, interval_size)`.
///
/// Attributes:
/// - `interval_size`: defines the interval [0, interval_size), which we sample from
/// - `two_pow_32`: is a helper to shift bits by 32-bits left by multiplication
/// - `nr_iterations`: defines how many full samples of u32 are required
/// - `upper_modulo`: is a power of two to remove superfluously sampled bits to increase
///     the probability of accepting a sample to at least 1/2
/// - `rng`: defines the [`ThreadRng`] that's used to sample uniform [u32] integers
///
/// # Examples
/// ```
/// use qfall_math::{utils::sample::uniform::UniformIntegerSampler, integer::Z};
/// let interval_size = Z::from(20);
///
/// let mut uis = UniformIntegerSampler::init(&interval_size).unwrap();
///
/// let sample = uis.sample();
///
/// assert!(Z::ZERO <= sample);
/// assert!(sample < interval_size);
/// ```
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
///     if the interval is chosen smaller than or equal to `1`.
pub struct UniformIntegerSampler {
    interval_size: Z,
    two_pow_32: u64,
    nr_iterations: u32,
    upper_modulo: u32,
    rng: ThreadRng,
}

impl UniformIntegerSampler {
    /// Initializes the [`UniformIntegerSampler`] with
    /// - `interval_size` as `interval_size`,
    /// - `two_pow_32` as a [u64] containing 2^32
    /// - `nr_iterations` as `(interval_size - 1).bits() / 32` floored
    /// - `upper_modulo` as 2^{(interval_size - 1).bits() mod 32}
    /// - `rng` as a fresh [`ThreadRng`]
    ///
    /// Parameters:
    /// - `interval_size`: specifies the interval `[0, interval_size)`
    ///     from which the samples are drawn
    ///
    /// Returns a [`UniformIntegerSampler`] or a [`MathError`],
    /// if the interval size is chosen smaller than or equal to `1`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{utils::sample::uniform::UniformIntegerSampler, integer::Z};
    /// let interval_size = Z::from(20);
    ///
    /// let mut uis = UniformIntegerSampler::init(&interval_size).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
    ///     if the interval is chosen smaller than or equal to `1`.
    pub fn init(interval_size: &Z) -> Result<Self, MathError> {
        if interval_size <= &Z::ONE {
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

        let rng = rand::rng();

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
    /// let mut uis = UniformIntegerSampler::init(&interval_size).unwrap();
    ///
    /// let sample = uis.sample();
    ///
    /// assert!(Z::ZERO <= sample);
    /// assert!(sample < interval_size);
    /// ```
    pub fn sample(&mut self) -> Z {
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
    /// let mut uis = UniformIntegerSampler::init(&interval).unwrap();
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

            let mut res = Z { value: fmpz(0) };
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

/// Computes a uniform at random chosen [`Z`] sample in `[0, interval_size)`.
///
/// Parameters:
/// - `interval_size`: specifies the size of the interval
///     over which the samples are drawn
///
/// Returns a uniform at random chosen [`Z`] instance in `[0, interval_size)` or a [`MathError`],
/// if the interval size is chosen smaller than or equal to `1`.
///
/// # Examples
/// ```compile_fail
/// use qfall_math::utils::sample::sample_uniform_rejection;
/// use qfall_math::integer::Z;
/// let interval_size = Z::from(20);
///
/// let sample = sample_uniform_rejection(&interval_size).unwrap();
///
/// assert!(Z::ZERO <= sample);
/// assert!(sample < interval_size);
/// ```
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
///     if the interval is chosen smaller than or equal to `1`.
pub(crate) fn sample_uniform_rejection(interval_size: &Z) -> Result<Z, MathError> {
    if interval_size <= &Z::ONE {
        return Err(MathError::InvalidInterval(format!(
            "An invalid interval size {interval_size} was provided."
        )));
    }

    let bit_size = interval_size.bits() as usize;

    let mut random = Z::from(&sample_bits_uniform(bit_size));
    while &random >= interval_size {
        random = Z::from(&sample_bits_uniform(bit_size));
    }
    Ok(random)
}

/// Computes `nr_bits` many uniform at random chosen bits.
///
/// Parameters:
/// - `nr_bits`: specifies the number of bits to be chosen uniform at random
///
/// Returns a [`Vec<u8>`] including `nr_bits` many uniform at random chosen bits,
/// filled with `0` bits if needed for the last byte resp. [`u8`].
///
/// # Examples
/// ```compile_fail
/// use qfall_math::utils::sample::sample_bits_uniform;
/// let nr_bits = 14;
///
/// let byte_vector = sample_bits_uniform(nr_bits);
///
/// assert_eq!(byte_vector[1] < 64);
/// assert_eq!(2, byte_vector.len());
/// ```
fn sample_bits_uniform(nr_bits: usize) -> Vec<u8> {
    let mut rng = rand::rng();

    // sample ⌈ nr_bits / 8 ⌉ bytes
    let mut byte_vector;
    if nr_bits % 8 == 0 {
        byte_vector = vec![0u8; nr_bits / 8];
    } else {
        byte_vector = vec![0u8; nr_bits / 8 + 1];
    }
    let mut res = rng.try_fill_bytes(&mut byte_vector);
    while res.is_err() {
        // Continue filling bytes at first zero byte found by binary search.
        // This may potentially discard previously sampled values, but stays uniform in the distribution
        let first_unfilled_byte = find_first_unfilled_byte(&byte_vector);
        res = rng.try_fill_bytes(&mut byte_vector[first_unfilled_byte..]);
    }

    // set superfluous bits at the end to `0`
    if nr_bits % 8 != 0 {
        let last_index = byte_vector.len() - 1;
        byte_vector[last_index] %= 2u8.pow(nr_bits as u32 % 8);
    }

    byte_vector
}

/// Binary search to find the first zero byte.
///
/// As we do not mark the filled bytes, the first zero byte is our
/// best guess to identify a not yet randomly/ unfilled byte.
///
/// Parameters:
/// - `byte_arr`: specifies the slice whose first zero byte is looked for
///
/// Returns the position of the first zero byte acc. to binary search.
/// If no zero byte exists, the length of the slice is returned.
///
/// # Examples
/// ```compile_fail
/// use qfall_math::utils::sample::{find_first_unfilled_byte, sample_bits_uniform};
/// let nr_bits = 256;
/// let byte_vector = sample_bits_uniform(nr_bits);
///
/// let first_zero_byte = find_first_unfilled_byte(&byte_vector);
/// ```
fn find_first_unfilled_byte(byte_arr: &[u8]) -> usize {
    let mut lower_bound = 0;
    let mut upper_bound = byte_arr.len();
    while upper_bound - lower_bound > 1 {
        let index = lower_bound + (upper_bound - lower_bound) / 2;
        if byte_arr[index] == 0x0 {
            upper_bound = index;
        } else {
            lower_bound = index;
        }
    }
    if byte_arr[lower_bound] == 0x0 {
        lower_bound
    } else {
        upper_bound
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

        let mut uis_2 = UniformIntegerSampler::init(&size_2).unwrap();
        let mut uis_7 = UniformIntegerSampler::init(&size_7).unwrap();

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

        let mut uis_0 = UniformIntegerSampler::init(&size_0).unwrap();
        let mut uis_1 = UniformIntegerSampler::init(&size_1).unwrap();

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

            let mut uis = UniformIntegerSampler::init(&interval).unwrap();

            let mut samples = HashSet::new();
            for _ in 0..2_u32.pow(interval_size) {
                samples.insert(uis.sample());
            }
            // if len(samples) == interval_size, then every element in [0, interval_size)
            // needs to be represented in samples
            assert_eq!(interval_size, samples.len() as u32);
        }
    }

    /// Checks whether interval sizes smaller than 2 result in an error.
    #[test]
    fn invalid_interval() {
        assert!(UniformIntegerSampler::init(&Z::ONE).is_err());
        assert!(UniformIntegerSampler::init(&Z::ZERO).is_err());
        assert!(UniformIntegerSampler::init(&Z::MINUS_ONE).is_err());
    }

    /// Checks whether random bit sampling doesn't fill more bits than required.
    #[test]
    fn sample_bits_uniform_necessary_nr_bytes() {
        let size_0 = Z::from(8);
        let size_1 = Z::from(256);
        let size_2 = Z::from(u32::MAX) + Z::ONE;

        let mut uis_0 = UniformIntegerSampler::init(&size_0).unwrap();
        let mut uis_1 = UniformIntegerSampler::init(&size_1).unwrap();
        let mut uis_2 = UniformIntegerSampler::init(&size_2).unwrap();

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
