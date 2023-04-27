// Copyright © 2023 Sven Moog
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module provides implementations for calculating roots on [`Q`].

use crate::{error::MathError, integer::Z, rational::Q};

impl Q {
    /// Calculate the square root with a fixed relative precision.
    ///
    /// The maximum error can be described by:
    /// `|sqrt_approximated(x/y)-sqrt(x/y) | <= x/y*10⁻⁹` ±?  
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
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::NegativeRootParameter`]
    ///   if the parameter of the square root is negative.
    pub fn sqrt(&self) -> Result<Q, MathError> {
        let root_numerator = self.get_numerator().sqrt()?;
        let root_denominator = self.get_denominator().sqrt()?;

        Ok(root_numerator / root_denominator)
    }

    /// Calculate the square root with a specified minimum precision.
    ///
    /// The actual result may be more accurate.
    ///
    /// Parameters:
    /// - `precision` specifies the upper limit of the error as `1/(2*precision)`.
    ///   A precision of less than one is treated the same as a precision of one.
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
