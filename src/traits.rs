// Copyright © 2023 Marvin Beckmann, Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains basic traits for this library. These include
//! specific traits for matrices and polynomials.

use crate::error::MathError;
use std::fmt::Display;

/// Is implemented by polynomials to evaluate it for a certain input.
pub trait Evaluate<T, U> {
    /// Evaluates the object, e.g. polynomial or a matrix of polynomials,
    /// for a given input value.
    ///
    /// Parameters:
    /// - `value`: The value with which to evaluate the object.
    ///
    /// Returns the evaluation of the object.
    fn evaluate(&self, value: T) -> U;
}

/// Is implemented by polynomials get a coefficient.
pub trait GetCoefficient<T> {
    /// Returns a coefficient of the given object, e.g. a polynomial,
    /// for a given coordinate.
    ///
    /// Parameters:
    /// - `coordinate`: The coordinate of the coefficient
    ///
    /// Returns the coefficient of the polynomial.
    fn get_coeff(&self, coordinate: impl TryInto<i64> + Display + Copy) -> Result<T, MathError>;
}

/// Is implemented by polynomials to set individual coefficients.
pub trait SetCoefficient<T> {
    /// Sets coefficient of the object, e.g. polynomial,
    /// for a given input value and a coordinate.
    ///
    /// Parameters:
    /// - `coordinate` : The coefficient to be set.
    /// - `value`: The value the coefficient is set to.
    fn set_coeff(
        &mut self,
        coordinate: impl TryInto<i64> + Display + Copy,
        value: T,
    ) -> Result<(), MathError>;
}

/// Is implemented by matrices to get the number of rows of the matrix.
pub trait GetNumRows {
    /// Returns the number of rows of a matrix.
    fn get_num_rows(&self) -> i64;
}

/// Is implemented by matrices to get the number of columns of the matrix.
pub trait GetNumColumns {
    /// Returns the number of columns of a matrix.
    fn get_num_columns(&self) -> i64;
}
