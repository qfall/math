// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling according to the uniform distribution.

use crate::{error::MathError, integer::Z, utils::sample::uniform::sample_uniform_rejection};

impl Z {
    /// Chooses a [`Z`] instance uniformly at random
    /// in `[lower_bound, upper_bound)`.
    ///
    /// The internally used uniform at random chosen bytes are generated
    /// by [`ThreadRng`](rand::rngs::ThreadRng), which uses ChaCha12 and
    /// is considered cryptographically secure.
    ///
    /// Parameters:
    /// - `lower_bound`: specifies the included lower bound of the
    /// interval over which is sampled
    /// - `upper_bound`: specifies the excluded upper bound of the
    /// interval over which is sampled
    ///
    /// Returns a fresh [`Z`] instance with a
    /// uniform random value in `[lower_bound, upper_bound)` or a [`MathError`]
    /// if the provided interval was chosen too small.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let sample = Z::sample_uniform(&17, &26).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
    /// if the given `upper_bound` isn't at least bigger than `lower_bound + 1`,
    /// i.e. the interval size is at most `1`.
    pub fn sample_uniform<T1, T2>(lower_bound: &T1, upper_bound: &T2) -> Result<Self, MathError>
    where
        T1: Into<Z> + Clone,
        T2: Into<Z> + Clone,
    {
        let lower_bound: Z = lower_bound.clone().into();
        let upper_bound: Z = upper_bound.clone().into();

        let interval_size = &upper_bound - &lower_bound;
        let sample = sample_uniform_rejection(&interval_size)?;
        Ok(&lower_bound + sample)
    }
}

#[cfg(test)]
mod test_sample_uniform {
    use crate::{integer::Z, integer_mod_q::Modulus};
    use std::str::FromStr;

    /// Checks whether the boundaries of the interval are kept for small intervals.
    #[test]
    fn boundaries_kept_small() {
        let lower_bound = Z::from(17);
        let upper_bound = Z::from(32);
        for _ in 0..32 {
            let sample = Z::sample_uniform(&lower_bound, &upper_bound).unwrap();
            assert!(lower_bound <= sample);
            assert!(sample < upper_bound);
        }
    }

    /// Checks whether the boundaries of the interval are kept for large intervals.
    #[test]
    fn boundaries_kept_large() {
        let lower_bound = Z::from(i64::MIN) - Z::from(u64::MAX);
        let upper_bound = Z::from(i64::MIN);
        for _ in 0..256 {
            let sample = Z::sample_uniform(&lower_bound, &upper_bound).unwrap();
            assert!(lower_bound <= sample);
            assert!(sample < upper_bound);
        }
    }

    /// Checks whether providing an invalid interval results in an error.
    #[test]
    fn invalid_interval() {
        let lb_0 = Z::from(i64::MIN) - Z::ONE;
        let lb_1 = Z::from(i64::MIN);
        let lb_2 = Z::ZERO;
        let upper_bound = Z::from(i64::MIN);

        let res_0 = Z::sample_uniform(&lb_0, &upper_bound);
        let res_1 = Z::sample_uniform(&lb_1, &upper_bound);
        let res_2 = Z::sample_uniform(&lb_2, &upper_bound);

        assert!(res_0.is_err());
        assert!(res_1.is_err());
        assert!(res_2.is_err());
    }

    /// Checks whether `sample_uniform` is available for all types
    /// implementing Into<Z> + Clone, i.e. u8, u16, u32, u64, i8, ...
    #[test]
    fn availability() {
        let modulus = Modulus::from_str("7").unwrap();
        let z = Z::from(7);

        let _ = Z::sample_uniform(&0u16, &7u8);
        let _ = Z::sample_uniform(&0u32, &7u16);
        let _ = Z::sample_uniform(&0u64, &7u32);
        let _ = Z::sample_uniform(&0i8, &7u64);
        let _ = Z::sample_uniform(&0i16, &7i8);
        let _ = Z::sample_uniform(&0i32, &7i16);
        let _ = Z::sample_uniform(&0i64, &7i32);
        let _ = Z::sample_uniform(&Z::ZERO, &7i64);
        let _ = Z::sample_uniform(&0u8, &modulus);
        let _ = Z::sample_uniform(&0, &z);
    }

    /// Roughly checks the uniformity of the distribution.
    /// This test could possibly fail for a truly uniform distribution
    /// with probability smaller than 1/1000.
    #[test]
    fn uniformity() {
        let lower_bound = Z::ZERO;
        let upper_bound = Z::from(5);
        let mut counts = [0; 5];
        // count sampled instances
        for _ in 0..1000 {
            let sample_z = Z::sample_uniform(&lower_bound, &upper_bound).unwrap();
            let sample_int = i64::try_from(&sample_z).unwrap() as usize;
            counts[sample_int] += 1;
        }

        // Check that every sampled integer was sampled roughly the same time
        // this could possibly fail for true uniform randomness with probability
        for count in counts {
            assert!(count > 150, "This test can fail with probability close to 0. 
            It fails if the sampled occurences do not look like a typical uniform random distribution. 
            If this happens, rerun the tests several times and check whether this issue comes up again.");
        }
    }
}
