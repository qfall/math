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
//! ```|(e_a*b - a*e_b)/(b*(b+e_b))| <= (a/b + 1) * p/(b-p)```

use crate::{error::MathError, integer::Z, rational::Q};

impl Q {
    /// Calculate the square root with a fixed relative precision.
    ///
    /// The maximum error can be described by:
    /// `Q::sqrt(x/y) = a/b` the maximum error to the true square root result
    /// is limited by `(a/b + 1) * 10⁻⁹/(b-10⁻⁹)`
    /// The actual result may be more accurate.
    ///
    /// # Examples:
    /// ```
    /// use qfall_math::rational::Q;
    ///
    /// let value = Q::try_from((&9,&4)).unwrap();
    /// let root = value.sqrt().unwrap();
    ///
    /// assert_eq!(&root, &Q::try_from((&3,&2)).unwrap());
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
    /// the true square root result is `(a/b + 1) * p/(b-p)`
    /// with `p = 1/(2*precision)`
    /// The actual result may be more accurate.
    ///
    /// Parameters:
    /// - `precision` specifies the upper limit of the error.
    ///
    ///   The precision must larger than zero.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::rational::Q;
    ///
    /// let precision = Z::from(1000);
    /// let value = Q::try_from((&9,&4)).unwrap();
    ///
    /// let root = value.sqrt_precision(&precision).unwrap();
    ///
    /// assert_eq!(&root, &Q::try_from((&3,&2)).unwrap());
    /// ```
    ///
    /// # Errors and Failures
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
    use crate::{integer::Z, rational::Q};

    /// Assert that sqrt of zero works correctly
    #[test]
    fn zero() {
        let zero = Q::ZERO;

        let res = zero.sqrt();

        assert_eq!(res, Q::ZERO);
    }

    /// Assert that the root of a negative number results in an error.
    #[test]
    fn negative_value() {
        let value = Q::from(-10);

        let res = value.sqrt_precision(&Z::from(10));

        assert!(res.is_err());
    }

    // TODO: this test might be correct, but fails because the f64 precision is to low.
    /// Calculate sqrt of different values  with different precisions and
    /// assert that the result meets the accuracy boundary.
    #[test]
    fn precision_correct() {
        // TODO: add dividers
        let values = vec![
            Q::from(1),
            Q::from(10),
            Q::from(100000),
            Q::from(i64::MAX),
            Q::from(i64::MAX) * Q::from(i64::MAX),
        ];
        let precisions = vec![
            Z::from(1),
            Z::from(10),
            Z::from(100000),
            Z::from(i64::MAX),
            // Z::from(i64::MAX) * Z::from(i64::MAX),
        ];

        // Test for all combinations of values and precisions
        for value in values {
            for precision in &precisions {
                let root = value.sqrt_precision(precision).unwrap();

                // Reasoning behind the following lines:
                // v = value, p_q = max_allowed_error = (a/b + 1) * p_z/(b-p_z), r = root, |e|<= p_q (actual error)
                // sqrt_precision(v,precision) = r = sqrt(x) + e
                // => r^2 = x + 2*sqrt(x)*e + e^2
                // => r^2-x = 2*sqrt(x)*e + e^2 = difference <= 2*sqrt(x)*p_q + p_q^2

                let p_z = Q::try_from((&1, precision)).unwrap() / Q::from(2);

                // TODO: clean up once arithmetic between Q and Z is better supported.
                let p_q = (&root + Q::ONE) * &p_z / (Q::from(root.get_denominator()) - &p_z);

                let root_squared = &root * &root;
                let difference = root_squared - Q::from(value.clone());

                // Use the root calculated with floating point numbers as
                // an approximation of sqrt(x).
                let root_from_float = Q::from((i64::MAX as f64).sqrt());
                let precision_cmp = &Q::from(2) * &p_q * root_from_float + &p_q * &p_q;

                println!(
                    "value: {}\n result: {}\n difference: {} \n precision_cmp: {}",
                    value, root, difference, precision_cmp
                );
                assert!(&difference > &(&Q::MINUS_ONE * &precision_cmp));
                assert!(&difference < &precision_cmp);
            }
        }
    }
}
