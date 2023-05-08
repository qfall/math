// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling according to the discrete Gaussian distribution.

use crate::{error::MathError, integer::Z, rational::Q, utils::sample::discrete_gauss::sample_z};

impl Z {
    /// Chooses a [`Z`] instance chosen according to the discrete Gaussian distribution
    /// in `[center - ⌈s * log_2(n)⌉ , center + ⌊s * log_2(n)⌋ ]`.
    ///
    /// This function samples discrete Gaussians according to the definition of
    /// SampleZ in [GPV08](https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=d9f54077d568784c786f7b1d030b00493eb3ae35).
    ///
    /// Parameters:
    /// - `n`: specifies the range from which is sampled
    /// - `center`: specifies the position of the center with peak probability
    /// - `s`: specifies the Gaussian parameter, which is proportional
    /// to the standard deviation `sigma * sqrt(2 * pi) = s`
    ///
    /// Returns new [`Z`] sample chosen according to the specified discrete Gaussian
    /// distribution or a [`MathError`] if the specified parameters were not chosen
    /// appropriately, i.e. `n > 1` and `s > 0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let sample = Z::sample_discrete_gauss(&128, &0, &1).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    /// if the `n <= 1` or `s <= 0`.
    pub fn sample_discrete_gauss<T1, T2, T3>(n: &T1, center: &T2, s: &T3) -> Result<Self, MathError>
    where
        T1: Into<Z> + Clone,
        T2: Into<Q> + Clone,
        T3: Into<Q> + Clone,
    {
        let n: Z = n.to_owned().into();
        let center: Q = center.to_owned().into();
        let s: Q = s.to_owned().into();

        sample_z(&n, &center, &s)
    }
}

#[cfg(test)]
mod test_sample_discrete_gauss {
    use crate::{integer::Z, rational::Q};

    // Appropriate interval and invalid inputs were tested in
    // utils::sample::discrete_gauss::test_sample_z and are thus omitted here.

    /// Checks whether `sample_discrete_gauss` is available for all types
    /// implementing Into<Z> + Clone, i.e. u8, u16, u32, u64, i8, ...
    /// or Into<Q> + Clone, i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let z = Z::from(2);
        let q = Q::from(2);

        let _ = Z::sample_discrete_gauss(&16u16, &7u8, &1u16);
        let _ = Z::sample_discrete_gauss(&2u32, &7u16, &1u8);
        let _ = Z::sample_discrete_gauss(&2u64, &7u32, &1u32);
        let _ = Z::sample_discrete_gauss(&2i8, &7u64, &1u64);
        let _ = Z::sample_discrete_gauss(&2i16, &7i8, &1i64);
        let _ = Z::sample_discrete_gauss(&2i32, &7i16, &1i32);
        let _ = Z::sample_discrete_gauss(&2i64, &7i32, &1i16);
        let _ = Z::sample_discrete_gauss(&z, &7i64, &1i8);
        let _ = Z::sample_discrete_gauss(&2u8, &q, &1i64);
        let _ = Z::sample_discrete_gauss(&2, &0i8, &z);
        let _ = Z::sample_discrete_gauss(&2, &z, &q);
        let _ = Z::sample_discrete_gauss(&2, &1f32, &1f64);
        let _ = Z::sample_discrete_gauss(&2, &1f64, &1f32);
    }

    /// Roughly checks the collected samples are distributed
    /// according to the discrete Gaussian distribution.
    ///
    /// This test could possibly fail for a truly uniform distribution
    /// with probability smaller than 1/1000.
    #[test]
    fn distribution() {
        let mut counts = [0; 20];
        // count sampled instances
        for _ in 0..200 {
            let sample = Z::sample_discrete_gauss(&1024, &10, &2).unwrap();
            let sample_int = i64::try_from(&sample).unwrap() as usize;
            counts[sample_int] += 1;
        }

        let expl_text = String::from("This test can fail with probability close to 0. 
        It fails if the sampled occurences do not look like a typical discrete Gaussian random distribution. 
        If this happens, rerun the tests several times and check whether this issue comes up again.");

        // Check that the sampled occurences roughly look
        // like a discrete Gaussian distriubtion
        assert!(counts[10] > 70, "{}", expl_text);
        assert!(counts[10] < 130, "{}", expl_text);
        assert!(counts[9] > 20, "{}", expl_text);
        assert!(counts[9] < 70, "{}", expl_text);
        assert!(counts[11] > 20, "{}", expl_text);
        assert!(counts[11] < 70, "{}", expl_text);
        assert!(counts[8] < 20, "{}", expl_text);
        assert!(counts[12] < 20, "{}", expl_text);
        for i in 0..8 {
            assert!(counts[i] < 10, "{}", expl_text);
        }
        for i in 13..20 {
            assert!(counts[i] < 10, "{}", expl_text);
        }
    }
}
