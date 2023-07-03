// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains sampling algorithms for uniform random sampling.

use crate::{
    error::MathError, integer::Z, integer_mod_q::Zq,
    utils::sample::uniform::sample_uniform_rejection,
};

impl Zq {
    /// Chooses a [`Zq`] instance uniformly at random in `[0, modulus)`.
    ///
    /// The internally used uniform at random chosen bytes are generated
    /// by [`ThreadRng`](rand::rngs::ThreadRng), which uses ChaCha12 and
    /// is considered cryptographically secure.
    ///
    /// Parameters:
    /// - `modulus`: specifies the [`Modulus`](crate::integer_mod_q::Modulus)
    /// of the new [`Zq`] instance and thus the size of the interval over which is sampled
    ///
    /// Returns a new [`Zq`] instance with a value chosen
    /// uniformly at random in `[0, modulus)` or a [`MathError`]
    /// if the provided modulus was too small.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    ///
    /// let sample = Zq::sample_uniform(17).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
    /// if the given modulus is smaller than or equal to `1`.
    pub fn sample_uniform(modulus: impl Into<Z>) -> Result<Self, MathError> {
        let modulus: Z = modulus.into();

        let random = sample_uniform_rejection(&modulus)?;
        Ok(Zq::from((random, modulus)))
    }
}

#[cfg(test)]
mod test_sample_uniform {
    use crate::{
        integer::Z,
        integer_mod_q::{Modulus, Zq},
    };

    /// Checks whether the boundaries of the interval are kept for small moduli.
    /// These should be protected by the sampling algorithm and [`Zq`]s instantiation.
    #[test]
    fn boundaries_kept_small() {
        let modulus = Z::from(17);
        for _ in 0..32 {
            let sample = Zq::sample_uniform(&modulus).unwrap();
            assert!(Z::ZERO <= sample.value);
            assert!(sample.value < modulus);
        }
    }

    /// Checks whether the boundaries of the interval are kept for large moduli.
    /// These should be protected by the sampling algorithm and [`Zq`]s instantiation.
    #[test]
    fn boundaries_kept_large() {
        let modulus = Z::from(u64::MAX);
        for _ in 0..256 {
            let sample = Zq::sample_uniform(&modulus).unwrap();
            assert!(Z::ZERO <= sample.value);
            assert!(sample.value < modulus);
        }
    }

    /// Checks whether providing an invalid interval results in an error.
    #[test]
    fn invalid_interval() {
        let mod_0 = Z::from(i64::MIN);
        let mod_1 = Z::ONE;
        let mod_2 = Z::ZERO;

        let res_0 = Zq::sample_uniform(&mod_0);
        let res_1 = Zq::sample_uniform(&mod_1);
        let res_2 = Zq::sample_uniform(&mod_2);

        assert!(res_0.is_err());
        assert!(res_1.is_err());
        assert!(res_2.is_err());
    }

    /// Checks whether `sample_uniform` is available for all types
    /// implementing [`Into<Z>`] + [`Clone`], i.e. u8, u16, u32, u64, i8, ...
    #[test]
    fn availability() {
        let modulus = Modulus::from(7);
        let z = Z::from(7);

        let _ = Zq::sample_uniform(&7u8);
        let _ = Zq::sample_uniform(&7u16);
        let _ = Zq::sample_uniform(&7u32);
        let _ = Zq::sample_uniform(&7u64);
        let _ = Zq::sample_uniform(&7i8);
        let _ = Zq::sample_uniform(&7i16);
        let _ = Zq::sample_uniform(&7i32);
        let _ = Zq::sample_uniform(&7i64);
        let _ = Zq::sample_uniform(&modulus);
        let _ = Zq::sample_uniform(&z);
    }

    /// Roughly checks the uniformity of the distribution.
    /// This test could possibly fail for a truly uniform distribution
    /// with probability smaller than 1/1000.
    #[test]
    fn uniformity() {
        let modulus = Z::from(5);
        let mut counts = [0; 5];
        // count sampled instances
        for _ in 0..1000 {
            let sample_z = Zq::sample_uniform(&modulus).unwrap();
            let sample_int = i64::try_from(&sample_z.value).unwrap() as usize;
            counts[sample_int] += 1;
        }

        // Check that every sampled integer was sampled roughly the same time
        // this could possibly fail for true uniform randomness with probability
        for count in counts {
            assert!(count > 150, "This test can fail with probability close to 0. 
            It fails if the sampled occurrences do not look like a typical uniform random distribution. 
            If this happens, rerun the tests several times and check whether this issue comes up again.");
        }
    }
}
