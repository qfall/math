// Copyright © 2023 Sven Moog
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module provides implementations for calculating roots on [`Q`].
//!
//! # Max Error Calculation:
//! Notation:
//! - `a/b` is the "correct" result
//! - `e_a` and `e_b` are the error of `a` and `b` resp.
//! - `p` is the maximum error of a sqrt on [`Z`] values
//!  => `|e_a| <= p` and `|e_b| <= p`
//!
//! ```Q::sqrt(x/y) = (a+e_a)/(b+e_b) = a/b + (e_a*b - a*e_b)/(b*(b+e_b))```
//!
//! The Error is the largest with `e_a = p` and `e_b = -p`:
//! ```|(e_a*b - a*e_b)/(b*(b+e_b))| <= a/b * (b+1) * p/(b-p)```

use crate::{error::MathError, integer::Z, rational::Q};

impl Q {
    /// Calculate the square root with a fixed relative precision.
    ///
    /// The maximum error can be described by:
    /// `Q::sqrt(x/y) = a/b` the maximum error to the true square root result
    /// is limited by `a/b * (b + 1) * 10⁻⁹/(b-10⁻⁹)`
    /// which is less than `2 * a/b * 10^-9`.
    /// The actual result may be more accurate.
    ///
    /// # Examples:
    /// ```
    /// use qfall_math::rational::Q;
    ///
    /// let value = Q::from((9,4));
    /// let root = value.sqrt();
    ///
    /// assert_eq!(&root, &Q::from((3,2)));
    /// ```
    ///
    /// # Panics ...
    /// - if the provided value is negative.
    pub fn sqrt(&self) -> Q {
        let root_numerator = self.get_numerator().sqrt();
        let root_denominator = self.get_denominator().sqrt();

        root_numerator / root_denominator
    }

    /// Calculate the square root with a specified minimum precision.
    ///
    /// Given `Q::sqrt_precision(x/y,precision) = a/b` the maximum error to
    /// the true square root result is `a/b * (b + 1) * p/(b-p)`
    /// with `p = 1/(2*precision)`.
    /// The actual result may be more accurate.
    ///
    /// Parameters:
    /// - `precision` specifies the upper limit of the error.
    ///   The precision must larger than zero.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::rational::Q;
    ///
    /// let precision = Z::from(1000);
    /// let value = Q::from((9,4));
    ///
    /// let root = value.sqrt_precision(&precision).unwrap();
    ///
    /// assert_eq!(&root, &Q::from((3,2)));
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::PrecisionNotPositive`]
    ///   if the precision is not larger than zero.
    /// - Returns a [`MathError`] of type [`MathError::NegativeRootParameter`]
    ///   if the parameter of the square root is negative.
    pub fn sqrt_precision(&self, precision: &Z) -> Result<Q, MathError> {
        let root_numerator = self.get_numerator().sqrt_precision(precision)?;
        let root_denominator = self.get_denominator().sqrt_precision(precision)?;

        Ok(root_numerator / root_denominator)
    }
}

#[cfg(test)]
mod test_sqrt {
    use crate::{integer::Z, rational::Q, traits::Pow};

    /// Assert that sqrt of zero works correctly
    #[test]
    fn zero() {
        let zero = Q::ZERO;

        let res = zero.sqrt();

        assert_eq!(res, Q::ZERO);
    }

    /// Assert that [`Q::sqrt_precision()`] returns an error for negative values.
    #[test]
    fn negative_value() {
        let value = Q::from(-10);

        let res = value.sqrt_precision(&Z::from(10));

        assert!(res.is_err());
    }

    /// Assert that [`Q::sqrt()`] panics for negative values
    #[test]
    #[should_panic]
    fn negative_value_precision() {
        let value = Q::from(-10);

        let _ = value.sqrt();
    }

    /// Assert that [`Q::sqrt`] works correctly for rational numbers with squares in
    /// numerator and denominator.
    #[test]
    fn square_rationals() {
        let values = vec![
            Q::ZERO,
            Q::from((1, 3)),
            Q::from((10, 3)),
            Q::from((100000, 3)),
            Q::from((u64::MAX, 3)),
            Q::from((u64::MAX, u64::MAX - 1)),
        ];

        // Test for all combinations of values and precisions
        for value in values {
            let value_sqr = &value * &value;

            let root = value_sqr.sqrt();

            assert_eq!(value, root);
        }
    }

    /// Calculate the square root of different values with different precisions.
    /// Assert that the result meets the accuracy boundary.
    #[test]
    fn precision_correct() {
        let values = vec![
            Q::from((1, 3)),
            Q::from((10, 3)),
            Q::from((100000, 3)),
            Q::from(u64::MAX),
            Q::from((1, u64::MAX)),
            Q::from((u64::MAX, u64::MAX - 1)) * Q::from(u64::MAX),
        ];
        let precisions = vec![
            Z::from(1),
            Z::from(10),
            Z::from(100000),
            Z::from(u64::MAX),
            Z::from(u64::MAX).pow(5).unwrap(),
        ];

        // Test for all combinations of values and precisions
        for value in values {
            // Calculate the root using f64 for comparison later on.
            let num: f64 = value.get_numerator().to_string().parse().unwrap();
            let den: f64 = value.get_denominator().to_string().parse().unwrap();
            let root_float: f64 = (num / den).sqrt();
            let root_float = Q::from(root_float);

            for precision in &precisions {
                let root = value.sqrt_precision(precision).unwrap();

                // Explanation of the following lines:
                // 1. Naming:
                //   x: value from which the sqrt is taken
                //   p_q and p_z are the maximum possible error of the sqrt for `Q` and `Z` resp.
                //   |e|<= p_q: actual error
                //   sqrt(x) = a/b: true square root result without error, approximated by f64::sqrt(x)
                //   sqrt_precision(x,precision) = root = sqrt(x) + e (true square root result + error)
                //
                // 2. Calculation:
                //   p_q = a/b * (b+1) * p_z/(b-p_z) (See derivation at the top of this file).
                //   We square the the root and subtract the original value so that the comparison
                //   of the precision bounds depends less on the precision of f64::sqrt(x).
                //   => root^2 = x + 2*sqrt(x)*e + e^2
                //   => root^2-x = 2*sqrt(x)*e + e^2 = difference <= 2*sqrt(x)*p_q + p_q^2
                let p_z = Q::from((1, 2 * precision));
                let p_q = &root_float * (root_float.get_denominator() + 1) * &p_z
                    / (root_float.get_denominator() - &p_z);

                let root_squared = &root * &root;
                let error_after_squaring = &root_squared - &value;

                let precision_bound_after_squaring = 2 * &p_q * &root_float + &p_q * &p_q;

                assert!(error_after_squaring > (-1 * &precision_bound_after_squaring));
                assert!(error_after_squaring < precision_bound_after_squaring);
            }
        }
    }
}
