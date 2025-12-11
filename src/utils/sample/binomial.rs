// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes core functionality to sample according to the
//! binomial distribution.

use crate::{error::MathError, integer::Z, rational::Q};
use rand::rngs::ThreadRng;
use rand_distr::{Binomial, Distribution};

/// Enables sampling a [`Z`] according to the binomial distribution `Bin(n, p)`.
///
/// Attributes:
/// - `distr`: defines the binomial distribution with parameters `n` and `p` to sample from
/// - `rng`: defines the [`ThreadRng`] that's used to sample from `distr`
///
/// # Examples
/// ```
/// use qfall_math::utils::sample::binomial::BinomialSampler;
/// let n = 2;
/// let p = 0.5;
///
/// let mut bin_sampler = BinomialSampler::init(n, p).unwrap();
///
/// let sample = bin_sampler.sample();
///
/// assert!(0 <= sample);
/// assert!(sample <= n);
/// ```
pub struct BinomialSampler {
    distr: Binomial,
    rng: ThreadRng,
}

impl BinomialSampler {
    /// Initializes the [`BinomialSampler`] with
    /// - `distr` as the binomial distribution with `n` tries and success probability `p` for each try, and
    /// - `rng` as a fresh [`ThreadRng`].
    ///
    /// Parameters:
    /// - `n`: specifies the number of tries
    /// - `p`: specifies the success probability
    ///
    /// Returns a [`BinomialSampler`] or a [`MathError`] if `n < 0`,
    /// `p ∉ (0,1)`, or `n` does not fit into an [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::utils::sample::binomial::BinomialSampler;
    /// let n = 2;
    /// let p = 0.5;
    ///
    /// let mut bin_sampler = BinomialSampler::init(n, p).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    ///   if `n < 0`.
    /// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
    ///   if `p ∉ (0,1)`.
    /// - Returns a [`MathError`] of type [`ConversionError`](MathError::ConversionError)
    ///   if `n` does not fit into an [`i64`].
    pub fn init(n: impl Into<Z>, p: impl Into<Q>) -> Result<Self, MathError> {
        let n = n.into();
        let p = p.into();

        if p <= Q::ZERO || p >= Q::ONE {
            return Err(MathError::InvalidInterval(format!(
                "p (the probability of success for binomial sampling) must be chosen between 0 and 1. \
                Currently it is {p}. \
                Hence, the interval to sample from is invalid and contains only exactly one number."
            )));
        }
        if n < Z::ZERO {
            return Err(MathError::InvalidIntegerInput(format!(
                "n (the number of trials for binomial sampling) must be no smaller than 0. Currently it is {n}."
            )));
        }

        let n = i64::try_from(n)? as u64;
        let p = f64::from(&p);

        let distr = Binomial::new(n, p).unwrap();
        let rng = rand::rng();

        Ok(Self { distr, rng })
    }

    /// Samples a [`Z`] according to the binomial distribution `Bin(n, p)`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::utils::sample::binomial::BinomialSampler;
    /// let n = 2;
    /// let p = 0.5;
    ///
    /// let mut bin_sampler = BinomialSampler::init(n, p).unwrap();
    ///
    /// let sample = bin_sampler.sample();
    ///
    /// assert!(0 <= sample);
    /// assert!(sample <= n);
    /// ```
    pub fn sample(&mut self) -> Z {
        Z::from(self.distr.sample(&mut self.rng))
    }
}

#[cfg(test)]
mod test_binomial_sampler {
    use super::{BinomialSampler, Q, Z};

    /// Checks whether the range is kept,
    /// i.e. if any result is at least 0 and smaller than or equal to `n`.
    #[test]
    fn keeps_range() {
        let n = 16;
        let p = 0.5;
        let mut bin_sampler = BinomialSampler::init(n, p).unwrap();

        for _ in 0..16 {
            let sample = bin_sampler.sample();
            // sample >= 0 check is not required as sample is a u64
            assert!(sample <= n);
        }
    }

    /// Roughly checks that the collected samples are distributed according to the binomial distribution.
    #[test]
    fn distribution() {
        let n = 2;
        let p = 0.5;
        let mut bin_sampler = BinomialSampler::init(n, p).unwrap();

        let mut counts = [0; 3];
        // count sampled instances
        for _ in 0..1000 {
            let sample = u64::try_from(bin_sampler.sample()).unwrap() as usize;
            counts[sample] += 1;
        }

        let expl_text = String::from("This test can fail with probability close to 0. 
        It fails if the sampled occurrences do not look like a typical binomial random distribution. 
        If this happens, rerun the tests several times and check whether this issue comes up again.");

        // Check that the sampled occurrences roughly look
        // like a binomial distribution
        assert!(counts[0] > 100, "{expl_text}");
        assert!(counts[0] < 400, "{expl_text}");
        assert!(counts[1] > 300, "{expl_text}");
        assert!(counts[1] < 700, "{expl_text}");
        assert!(counts[2] > 100, "{expl_text}");
        assert!(counts[2] < 400, "{expl_text}");
    }

    /// Checks whether invalid choices for n result in an error.
    #[test]
    fn invalid_n() {
        let p = 0.5;

        assert!(BinomialSampler::init(&Z::MINUS_ONE, p).is_err());
        assert!(BinomialSampler::init(&Z::from(i64::MIN), p).is_err());
    }

    /// Checks whether invalid choices for p result in an error.
    #[test]
    fn invalid_p() {
        let n = 2;

        assert!(BinomialSampler::init(n, &Q::MINUS_ONE).is_err());
        assert!(BinomialSampler::init(n, &Q::ZERO).is_err());
        assert!(BinomialSampler::init(n, &Q::ONE).is_err());
        assert!(BinomialSampler::init(n, &Q::from(5)).is_err());
    }
}
