// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes core functionality to sample according to the
//! binomial distribution.

use crate::{error::MathError, integer::Z, rational::Q};
use rand_distr::{Binomial, Distribution};

/// Chooses a sample according to the binomial distribution parameterized by `n` and `p`.
///
/// Parameters:
/// - `n`: specifies the number of trials
/// - `p`: specifies the probability of success
///
/// Returns a sample as a [`u64`] chosen from the specified binomial distribution
/// or a [`MathError`] if `n < 1`, `p ∉ (0,1)`, or `n` does not fit into an [`i64`].
///
/// # Examples
/// ```compile_fail
/// use qfall_math::{integer::Z, rational::Q};
/// use qfall_math::utils::sample::binomial::sample_binomial;
/// let n = Z::from(2);
/// let p = Q::from((1, 4));
///
/// let sample = sample_binomial(&n, &p).unwrap();
/// ```
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
/// if `n < 1`.
/// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
/// if `p ∉ (0,1)`.
/// - Returns a [`MathError`] of type [`ConversionError`](MathError::ConversionError)
/// if `n` does not fit into an [`i64`].
pub(crate) fn sample_binomial(n: &Z, p: &Q) -> Result<u64, MathError> {
    if p <= &Q::ZERO || p >= &Q::ONE {
        return Err(MathError::InvalidInterval(format!(
            "p (the probability of success for binomial sampling) must be chosen between 0 and 1. \
            Currently it is {p}. \
            Hence, the interval to sample from is invalid and contains only exactly one number."
        )));
    }
    if n <= &Z::ZERO {
        return Err(MathError::InvalidIntegerInput(format!(
            "n (the number of trials for binomial sampling) must be larger than 0. Currently it is {n}."
        )));
    }

    let n = i64::try_from(n)? as u64;
    let p = f64::from(p);

    let distr = Binomial::new(n, p).unwrap();
    let mut rng = rand::thread_rng();

    let sample = distr.sample(&mut rng);

    Ok(sample)
}

#[cfg(test)]
mod test_sample_binomial {
    use super::{sample_binomial, Q, Z};

    /// Ensures that the doc tests works correctly.
    #[test]
    fn doc_test() {
        let n = Z::from(2);
        let p = Q::from((1, 4));

        let _ = sample_binomial(&n, &p).unwrap();
    }

    /// Checks whether the range is kept,
    /// i.e. if any result is at least 0 and smaller than or equal to `n`.
    #[test]
    fn keeps_range() {
        let n_u64 = 16;
        let n = Z::from(n_u64);
        let p = Q::from((1, 2));

        for _ in 0..64 {
            let sample = sample_binomial(&n, &p).unwrap();
            assert!(sample > 0);
            assert!(sample < n_u64);
        }
    }

    /// Roughly checks that the collected samples are distributed according to the binomial distribution.
    #[test]
    fn distribution() {
        let n = Z::from(2);
        let p = Q::from((1, 2));

        let mut counts = [0; 3];
        // count sampled instances
        for _ in 0..1000 {
            let sample = sample_binomial(&n, &p).unwrap() as usize;
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
        let p = Q::from((1, 2));

        assert!(sample_binomial(&Z::ZERO, &p).is_err());
        assert!(sample_binomial(&Z::MINUS_ONE, &p).is_err());
        assert!(sample_binomial(&Z::from(i64::MIN), &p).is_err());
    }

    /// Checks whether invalid choices for p result in an error.
    #[test]
    fn invalid_p() {
        let n = Z::from(2);

        assert!(sample_binomial(&n, &Q::MINUS_ONE).is_err());
        assert!(sample_binomial(&n, &Q::ZERO).is_err());
        assert!(sample_binomial(&n, &Q::ONE).is_err());
        assert!(sample_binomial(&n, &Q::from(5)).is_err());
    }
}
