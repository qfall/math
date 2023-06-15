// Copyright © 2023 Sven Moog
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module provides implementations for calculating roots on [`Z`].

use crate::{error::MathError, integer::Z, rational::Q};
use flint_sys::fmpz::fmpz_sqrtrem;

impl Z {
    /// Calculate the square root with a fixed precision.
    ///
    /// The error of the result is smaller than ±10⁻⁹.
    /// The actual result may be more accurate and is the best approximation
    /// for the resulting denominator.
    ///
    /// Returns the square root with a precision of ±10⁻⁹.
    ///
    /// # Examples:
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let value = Z::from(2);
    /// let root = value.sqrt();
    /// ```
    ///
    /// # Panics ...
    /// - if the provided value is negative.
    pub fn sqrt(&self) -> Q {
        self.sqrt_precision(&Z::from(500000000)).unwrap()
    }

    /// Calculate the square root with a specified minimum precision.
    ///
    /// The actual result may be more accurate and is the best approximation
    /// for the resulting denominator.
    /// The [continued fractions expansion](https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Continued_fraction_expansion)
    /// is used to approximate the square root.
    ///
    /// Parameters:
    /// - `precision` specifies the upper limit of the error as `1/(2*precision)`.
    ///   The precision must be larger than zero.
    ///
    /// Returns the square root with a specified minimum precision.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::rational::Q;
    ///
    /// let value = Z::from(42);
    /// let precision = Z::from(1000);
    ///
    /// let root = value.sqrt_precision(&precision);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::PrecisionNotPositive`]
    ///   if the precision is not larger than zero.
    /// - Returns a [`MathError`] of type [`MathError::NegativeRootParameter`]
    ///   if the parameter of the square root is negative.
    pub fn sqrt_precision(&self, precision: &Z) -> Result<Q, MathError> {
        if self < &Z::ZERO {
            return Err(MathError::NegativeRootParameter(format!("{}", self)));
        }
        if precision <= &Z::ZERO {
            return Err(MathError::PrecisionNotPositive(format!("{}", precision)));
        }

        let mut integer_result = Q::default();
        let remainder = Q::default();

        unsafe {
            // self = integer_result^2 + remainder
            fmpz_sqrtrem(
                &mut integer_result.value.num,
                &remainder.value.num,
                &self.value,
            );
        }

        if remainder == Q::ZERO {
            Ok(integer_result)
        } else {
            // Implementation of the Continued fraction expansion
            // https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Continued_fraction_expansion

            let two_int_res = &integer_result * Q::from(2);
            // cargo clippy 0.1.70 falsely marks this clone as redundant.
            #[allow(clippy::redundant_clone)]
            let mut temp = two_int_res.clone();

            // After the while loop, temp is inverted
            // => numerator becomes denominator
            // => current numerator is current precision
            while &temp.get_numerator() < precision {
                // Calling unwrap here is safe because temp can not be zero.
                // `temp` can not be zero, because it is initialized with a positive
                // number (`2* integer_result`) and after that just positive numbers
                // are added. `integer_result` would only be zero for `sqrt(0)`, in
                // which case `remainder == 0` and therefore, this code would not be
                // executed.
                temp = &two_int_res + &temp.inverse().unwrap() * &remainder;
            }

            Ok(&temp.inverse().unwrap() * &remainder + integer_result)
        }
    }
}

#[cfg(test)]
mod test_sqrt_precision {
    use crate::{error::MathError, integer::Z, rational::Q};
    use std::str::FromStr;

    /// Calculate sqrt of different values  with different precisions and
    /// assert that the result meets the accuracy boundary.
    #[test]
    fn precision_correct() {
        let values = vec![
            Z::from(1),
            Z::from(10),
            Z::from(100000),
            Z::from(i64::MAX),
            Z::from(i64::MAX) * Z::from(i64::MAX),
        ];
        let precisions = vec![
            Z::from(1),
            Z::from(10),
            Z::from(100000),
            Z::from(i64::MAX),
            Z::from(i64::MAX) * Z::from(i64::MAX),
        ];

        // Test for all combinations of values and precisions
        for value in values {
            for precision in &precisions {
                let root = value.sqrt_precision(precision).unwrap();

                // Reasoning behind the following lines:
                // v = value, p = 1/(2*precision), r = root, |e|<= p (actual error)
                // sqrt_precision(v,precision) = r = sqrt(x) + e
                // => r^2 = x + 2*sqrt(x)*e + e^2
                // => r^2-x = 2*sqrt(x)*e + e^2 = difference <= 2*sqrt(x)*p + p^2
                let p = Q::try_from((&1, precision)).unwrap() / Q::from(2);

                let root_squared = &root * &root;
                let difference = root_squared - Q::from(value.clone());

                // Use the root calculated with floating point numbers as
                // an approximation of sqrt(x).
                let root_from_float = Q::from((i64::MAX as f64).sqrt());
                let precision_cmp = &Q::from(2) * &p * root_from_float + &p * &p;

                assert!(difference > (&Q::MINUS_ONE * &precision_cmp));
                assert!(difference < precision_cmp);
            }
        }
    }

    /// Assert that the root of a negative number results in an error.
    #[test]
    fn negative_value() {
        let value = Z::from(-10);

        let res = value.sqrt_precision(&Z::from(10));

        assert!(res.is_err());
    }

    /// Assert that a precision smaller than one return an error.
    #[test]
    fn non_positive_precision() {
        let value = Z::from(42);
        let precisions = vec![Z::from(i64::MIN), Z::from(-10), Z::ZERO];

        for precision in &precisions {
            let root = value.sqrt_precision(precision);

            assert!(root.is_err());
        }
    }

    /// Helper function for tests.
    /// Assert that the sqrt of `value` results in the value in solutions.
    /// The precision is increased from 0 to the precision of the largest solution.
    ///
    /// Parameters:
    /// - `value` square root will be calculated on this value
    /// - `solutions` is a vector containing strings that can be pares as [`Q`] values.
    ///    The values have to be the a sqrt approximation generated by the
    ///    continues fraction expansion, starting with the worst approximation.
    ///
    /// Returns an empty `Ok` if the action could be performed successfully.
    /// Otherwise, a [`MathError`] is returned if a type conversion failed.
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] if a type conversion failed.
    ///
    /// # Panics
    /// - Panics if at any point the calculated solution is not matching
    ///   the given solution.
    fn compare_solutions(value: Z, solutions: Vec<&str>) -> Result<(), MathError> {
        let max_precision = Q::from_str(solutions.last().unwrap())?.get_denominator();
        let max_precision = i64::try_from(&max_precision)?;

        let mut sol_iter = solutions.iter();
        let mut current_solution = Q::from_str(sol_iter.next().unwrap())?;

        for precision in 1..max_precision {
            let precision = Z::from(precision);

            let root = value.sqrt_precision(&precision)?;

            if root != current_solution && precision > current_solution.get_denominator() {
                current_solution = Q::from_str(sol_iter.next().unwrap())?;
            }
            assert_eq!(root, current_solution);
        }
        Ok(())
    }

    /// Checks the sqrt with different precisions against the results from
    /// the wikipedia article <https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Continued_fraction_expansion>
    #[test]
    fn not_too_precise_sqrt_3() {
        let solutions = vec!["2/1", "5/3", "7/4", "19/11", "26/15", "71/41", "97/56"];
        let value = Z::from(3);

        compare_solutions(value, solutions).unwrap();
    }

    /// Checks the sqrt with different precisions against the results from
    /// the wikipedia article <https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Continued_fraction_expansion>
    #[test]
    fn not_too_precise_sqrt_10() {
        let solutions = vec!["19/6", "117/37"];
        let value = Z::from(10);

        compare_solutions(value, solutions).unwrap();
    }

    /// Checks the sqrt with different precisions against the results from
    /// the wikipedia article <https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Continued_fraction_expansion>
    #[test]
    fn not_too_precise_sqrt_2() {
        let solutions = vec!["3/2", "7/5", "17/12", "41/29", "99/70"];
        let value = Z::from(2);

        compare_solutions(value, solutions).unwrap();
    }

    /// Assert that sqrt works correctly for small values and returns the exact
    /// value independent of the precision.
    #[test]
    fn squares_small() {
        let precisions = vec![
            Z::from(1),
            Z::from(10),
            Z::from(100000),
            Z::from(i64::MAX),
            Z::from(i64::MAX) * Z::from(i64::MAX),
        ];
        let value = Z::from(42);
        let square = &value * &value;

        for precision in &precisions {
            let root = square.sqrt_precision(precision).unwrap();

            assert_eq!(Q::from(42), root);
        }
    }

    /// Assert that sqrt works correctly for large values and returns the exact
    /// value independent of the precision.
    #[test]
    fn squares_large() {
        let precisions = vec![
            Z::from(1),
            Z::from(10),
            Z::from(100000),
            Z::from(i64::MAX),
            Z::from(i64::MAX) * Z::from(i64::MAX),
        ];
        let value = Z::from(u64::MAX);
        let square = &value * &value;

        for precision in &precisions {
            let root = square.sqrt_precision(precision).unwrap();

            assert_eq!(Q::from(u64::MAX), root);
        }
    }
}

#[cfg(test)]
mod test_sqrt {
    use crate::{integer::Z, rational::Q};

    /// Assert that sqrt works correctly for small square values.
    #[test]
    fn squares_small() {
        let value = Z::from(24);
        let square = &value * &value;

        let root = square.sqrt();

        assert_eq!(Q::from(value), root);
    }

    /// Assert that sqrt works correctly for a large square values.
    #[test]
    fn squares_large() {
        let value = Z::from(u64::MAX - 1);
        let square = &value * &value;

        let root = square.sqrt();

        assert_eq!(Q::from(value), root);
    }

    /// Assert that sqrt panics with small negative numbers.
    #[test]
    #[should_panic]
    fn negative_small() {
        let value = Z::from(i64::MIN);

        let _ = value.sqrt();
    }

    /// Assert that sqrt panics with large negative numbers.
    #[test]
    #[should_panic]
    fn negative_large() {
        let value = Z::from(i64::MIN);

        let _ = value.sqrt();
    }
}
