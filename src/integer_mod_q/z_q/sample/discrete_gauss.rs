// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling according to the discrete Gaussian distribution.

use crate::{
    error::MathError, integer::Z, integer_mod_q::Zq, rational::Q,
    utils::sample::discrete_gauss::sample_z,
};

impl Zq {
    /// Chooses a [`Zq`] instance chosen according to the discrete Gaussian distribution
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
    /// - `modulus`: specifies the modulus of the new [`Zq`] element
    ///
    /// Returns new [`Zq`] sample chosen according to the specified discrete Gaussian
    /// distribution or a [`MathError`] if the modulus is chosen smaller than `2` or the
    /// specified parameters were not chosen appropriately, i.e. `n > 1` and `s > 0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    ///
    /// let sample = Zq::sample_discrete_gauss(&128, &0, &1, &17).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    /// if `n <= 1` or `s <= 0`.
    /// - Returns a [`MathError`] of type
    /// [`InvalidIntToModulus`](MathError::InvalidIntToModulus) if the
    /// provided value is not greater than `0`.
    ///
    /// This function implements SampleZ according to:
    /// - \[1\] Gentry, Craig and Peikert, Chris and Vaikuntanathan, Vinod (2008).
    /// Trapdoors for hard lattices and new cryptographic constructions.
    /// In: Proceedings of the fortieth annual ACM symposium on Theory of computing.
    /// <https://dl.acm.org/doi/pdf/10.1145/1374376.1374407>
    pub fn sample_discrete_gauss<T1, T2, T3, T4>(
        n: &T1,
        center: &T2,
        s: &T3,
        modulus: &T4,
    ) -> Result<Self, MathError>
    where
        T1: Into<Z> + Clone,
        T2: Into<Q> + Clone,
        T3: Into<Q> + Clone,
        T4: Into<Z> + Clone,
    {
        let modulus: Z = modulus.to_owned().into();
        let n: Z = n.to_owned().into();
        let center: Q = center.to_owned().into();
        let s: Q = s.to_owned().into();

        let sample = sample_z(&n, &center, &s)?;
        Zq::try_from_z_z(&sample, &modulus)
    }
}

#[cfg(test)]
mod test_sample_discrete_gauss {
    use crate::{integer::Z, integer_mod_q::Zq, rational::Q};

    // Appropriate interval and invalid inputs were tested in
    // utils::sample::discrete_gauss::test_sample_z and are thus omitted here.

    /// Checks whether `sample_discrete_gauss` is available for all types
    /// implementing Into<Z> + Clone, i.e. u8, u16, u32, u64, i8, ...
    /// or Into<Q> + Clone, i.e. u8, i16, f32, Z, Q, ...
    #[test]
    fn availability() {
        let z = Z::from(2);
        let q = Q::from(2);

        let _ = Zq::sample_discrete_gauss(&16u16, &7u8, &1u16, &17u64);
        let _ = Zq::sample_discrete_gauss(&2u32, &7u16, &1u8, &17u16);
        let _ = Zq::sample_discrete_gauss(&2u64, &7u32, &1u32, &17u8);
        let _ = Zq::sample_discrete_gauss(&2i8, &7u64, &1u64, &17u32);
        let _ = Zq::sample_discrete_gauss(&2i16, &7i8, &1i64, &17i16);
        let _ = Zq::sample_discrete_gauss(&2i32, &7i16, &1i32, &17i8);
        let _ = Zq::sample_discrete_gauss(&2i64, &7i32, &1i16, &17i64);
        let _ = Zq::sample_discrete_gauss(&z, &7i64, &1i8, &17i32);
        let _ = Zq::sample_discrete_gauss(&2u8, &q, &1i64, &17);
        let _ = Zq::sample_discrete_gauss(&2, &0i8, &z, &z);
        let _ = Zq::sample_discrete_gauss(&2, &z, &q, &17);
        let _ = Zq::sample_discrete_gauss(&2, &1f32, &1f64, &17);
        let _ = Zq::sample_discrete_gauss(&2, &1f64, &1f32, &17);
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
            let sample = Zq::sample_discrete_gauss(&1024, &0, &2, &20).unwrap();
            let sample_int = i64::try_from(&sample.get_value()).unwrap() as usize;
            counts[sample_int] += 1;
        }

        let expl_text = String::from("This test can fail with probability close to 0. 
        It fails if the sampled occurrences do not look like a typical discrete Gaussian random distribution. 
        If this happens, rerun the tests several times and check whether this issue comes up again.");

        // Check that the sampled occurrences roughly look
        // like a discrete Gaussian distriubtion
        assert!(counts[0] > 70, "{}", expl_text);
        assert!(counts[0] < 130, "{}", expl_text);
        assert!(counts[19] > 20, "{}", expl_text);
        assert!(counts[19] < 70, "{}", expl_text);
        assert!(counts[1] > 20, "{}", expl_text);
        assert!(counts[1] < 70, "{}", expl_text);
        assert!(counts[18] < 20, "{}", expl_text);
        assert!(counts[2] < 20, "{}", expl_text);
        for count in counts.iter().take(18).skip(3) {
            assert!(count < &10, "{}", expl_text);
        }
    }
}
