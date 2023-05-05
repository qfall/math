// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes core functionality to sample according to the
//! discrete gaussian distribution.

use super::uniform::{get_rng, sample_uniform_rejection};
use crate::{error::MathError, integer::Z, rational::Q, traits::Pow};
use rand::RngCore;

#[allow(dead_code)]
/// Chooses a sample according to the discrete Gaussian distribution out of
/// `[center - ⌈s * log_2(n)⌉ , center + ⌊s * log_2(n)⌋ ]`.
///
/// This function implements discrete Gaussian sampling according to the definition of
/// SampleZ in [GPV08](https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=d9f54077d568784c786f7b1d030b00493eb3ae35).
///
/// Parameters:
/// - `n`: specifies the range from which is sampled
/// - `center`: specifies the position of the center with peak probability
/// - `s`: specifies the Gaussian parameter, which is proportional
/// to the standard deviation `sigma * sqrt(2 * pi) = s`
///
/// Returns a sample chosen according to the specified discrete Gaussian distribution or
/// a [`MathError`] if the specified parameters were not chosen appropriately,
/// i.e. `n > 1` and `s > 0`.
///
/// # Examples
/// ```compile_fail
/// use qfall_math::{integer::Z, rational::Q};
/// use qfall_math::utils::sample::discrete_gauss::sample_z;
/// let n = Z::from(1024);
/// let center = Q::ZERO;
/// let gaussian_parameter = Q::ONE;
///
/// let sample = sample_z(&n, &center, &gaussian_parameter).unwrap();
/// ```
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
/// if the `n <= 1` or `s <= 0`.
pub(crate) fn sample_z(n: &Z, center: &Q, s: &Q) -> Result<Z, MathError> {
    // TODO: Change this functions signature to use std_deviation/ sigma and not Gaussian parameter
    if n <= &Z::ONE {
        return Err(MathError::InvalidIntegerInput(format!(
            "The value {} was provided for parameter n of the function sample_z.
            This function expects this input to be bigger than 1.",
            n
        )));
    }
    if s <= &Q::ZERO {
        return Err(MathError::InvalidIntegerInput(format!(
            "The value {} was provided for parameter s of the function sample_z.
            This function expects this input to be bigger than 0.",
            s
        )));
    }

    let lower_bound = (center - s * n.log(&2).unwrap()).ceil();
    let upper_bound = (center + s * n.log(&2).unwrap()).floor();
    let interval_size = &upper_bound - &lower_bound;

    // sample x in [c - s * log_2(n), c + s * log_2(n)]
    let mut sample = &lower_bound + sample_uniform_rejection(&interval_size).unwrap();

    // rejection sample according to GPV08
    // https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=d9f54077d568784c786f7b1d030b00493eb3ae35
    // this eprint version explains in more detail how sample_z works
    let rng = get_rng();
    // TODO: Change to Q::from_f64 once it works appropriately for large scale
    while gaussian_function(&sample, center, s)
        <= Q::try_from((&rng.next_u64(), &u64::MAX)).unwrap()
    {
        sample = &lower_bound + sample_uniform_rejection(&interval_size).unwrap();
    }

    Ok(sample)
}

/// Computes the value of the Gaussian function for `x`.
///
/// **WARNING:** This functions assumes `s != 0`.
///
/// Parameters:
/// - `x`: specifies the value/ sample for which the Gaussian function's value is computed
/// - `c`: specifies the position of the center with peak probability
/// - `s`: specifies the Gaussian parameter, which is proportional
/// to the standard deviation `sigma * sqrt(2 * pi) = s`
///
/// Returns the computed value of the Gaussian function for `x`.
///
/// # Examples
/// ```compile_fail
/// use qfall_math::{integer::Z, rational::Q};
/// use qfall_math::utils::sample::discrete_gauss::gaussian_function;
/// let sample = Z::ONE;
/// let center = Q::ZERO;
/// let gaussian_parameter = Q::ONE;
///
/// let probability = gaussian_function(&sample, &center, &gaussian_parameter);
/// ```
///
/// # Panics ...
/// - if `s = 0`.
fn gaussian_function(x: &Z, c: &Q, s: &Q) -> Q {
    // TODO: Change this functions signature to use std_deviation/ sigma and not Gaussian parameter
    let num = Q::MINUS_ONE * Q::PI * (Q::from(x.to_owned()) - c).pow(2).unwrap();
    let den = s.pow(2).unwrap();
    let res: Q = num / den;
    res.exp_taylor(100u32)
}

#[cfg(test)]
mod test_sample_z {
    use super::{sample_z, Q, Z};

    /// Ensures that the doc tests works correctly
    #[test]
    fn doc_test() {
        let n = Z::from(1024);
        let center = Q::ZERO;
        let gaussian_parameter = Q::ONE;

        let sample = sample_z(&n, &center, &gaussian_parameter).unwrap();

        assert!(Z::from(-10) <= sample);
        assert!(sample <= Z::from(10));
    }

    /// Checks whether samples are kept in correct interval for a small interval
    #[test]
    fn small_interval() {
        let n = Z::from(1024);
        let center = Q::from(15);
        let gaussian_parameter = Q::try_from((&1, &2)).unwrap();

        for _ in 0..64 {
            let sample = sample_z(&n, &center, &gaussian_parameter).unwrap();

            assert!(Z::from(10) <= sample);
            assert!(sample <= Z::from(20));
        }
    }

    /// Checks whether samples are kept in correct interval for a large interval
    #[test]
    fn large_interval() {
        let n = Z::from(i64::MAX as u64 + 1);
        let center = Q::MINUS_ONE;
        let gaussian_parameter = Q::ONE;

        for _ in 0..256 {
            let sample = sample_z(&n, &center, &gaussian_parameter).unwrap();

            assert!(Z::from(-64) <= sample);
            assert!(sample <= Z::from(62));
        }
    }

    /// Checks whether `sample_z` returns an error if the gaussian parameter `s <= 0`
    #[test]
    fn invalid_gaussian_parameter() {
        let n = Z::from(4);
        let center = Q::ZERO;

        assert!(sample_z(&n, &center, &Q::ZERO).is_err());
        assert!(sample_z(&n, &center, &Q::MINUS_ONE).is_err());
        assert!(sample_z(&n, &center, &Q::try_from((&i64::MIN, &1)).unwrap()).is_err());
    }

    /// Checks whether `sample_z` returns an error if `n <= 1`
    #[test]
    fn invalid_n() {
        let center = Q::MINUS_ONE;
        let gaussian_parameter = Q::ONE;

        assert!(sample_z(&Z::ONE, &center, &gaussian_parameter).is_err());
        assert!(sample_z(&Z::ZERO, &center, &gaussian_parameter).is_err());
        assert!(sample_z(&Z::MINUS_ONE, &center, &gaussian_parameter).is_err());
        assert!(sample_z(&Z::from(i64::MIN), &center, &gaussian_parameter).is_err());
    }
}

#[cfg(test)]
mod test_gaussian_function {
    use super::{gaussian_function, Q, Z};
    use crate::traits::Distance;

    /// Ensures that the doc test would run properly
    #[test]
    fn doc_test() {
        let sample = Z::ONE;
        let center = Q::ZERO;
        let gaussian_parameter = Q::ONE;
        // result roughly 0.0432139 computed via WolframAlpha
        let cmp = Q::try_from((&43214, &1_000_000)).unwrap();

        let value = gaussian_function(&sample, &center, &gaussian_parameter);

        assert!(cmp.distance(&value) < Q::try_from((&1, &1_000_000)).unwrap());
    }

    /// Checks whether the values for small values are computed appropriately
    /// and with appropriate precision
    #[test]
    fn small_values() {
        let sample_0 = Z::ZERO;
        let sample_1 = Z::MINUS_ONE;
        let center = Q::MINUS_ONE;
        let gaussian_parameter_0 = Q::try_from((&1, &2)).unwrap();
        let gaussian_parameter_1 = Q::try_from((&3, &2)).unwrap();
        // result roughly 0.00000348734 computed via WolframAlpha
        let cmp_0 = Q::try_from((&349, &100_000_000)).unwrap();
        // result 0.247520 computed via WolframAlpha
        let cmp_1 = Q::try_from((&24752, &100_000)).unwrap();

        let res_0 = gaussian_function(&sample_0, &center, &gaussian_parameter_0);
        let res_1 = gaussian_function(&sample_0, &center, &gaussian_parameter_1);
        let res_2 = gaussian_function(&sample_1, &center, &gaussian_parameter_0);
        let res_3 = gaussian_function(&sample_1, &center, &gaussian_parameter_1);

        assert!(cmp_0.distance(&res_0) < Q::try_from((&3, &1_000_000_000)).unwrap());
        assert!(cmp_1.distance(&res_1) < Q::try_from((&1, &1_000_000)).unwrap());
        assert_eq!(Q::ONE, res_2);
        assert_eq!(Q::ONE, res_3);
    }

    /// Checks whether the values for large values are computed appropriately
    /// and with appropriate precision
    #[test]
    fn large_values() {
        let sample = Z::from(i64::MAX);
        let center = Q::from(i64::MAX as u64 + 1);
        let gaussian_parameter = Q::try_from((&1, &2)).unwrap();
        // result roughly 0.00000348734 computed via WolframAlpha
        let cmp = Q::try_from((&349, &100_000_000)).unwrap();

        let res = gaussian_function(&sample, &center, &gaussian_parameter);

        assert!(cmp.distance(&res) < Q::try_from((&3, &1_000_000_000)).unwrap());
    }

    /// Checks whether `s = 0` results in a panic
    #[test]
    #[should_panic]
    fn invalid_s() {
        let sample = Z::from(i64::MAX);
        let center = Q::from(i64::MAX as u64 + 1);
        let gaussian_parameter = Q::ZERO;

        let _ = gaussian_function(&sample, &center, &gaussian_parameter);
    }
}
