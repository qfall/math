//! This module contains basic traits for this library. These include
//! specific traits for matrices and polynomials.

use std::fmt::Display;

use crate::error::MathError;

/// Is implemented by polynomials to evaluate it for a certain input.
pub trait Evaluate<U, V> {
    /// Evaluates the object, e.g. polynomial or a matrix of polynomials,
    /// for a given input value.
    ///
    /// Parameters:
    /// - `value`: The value with which to evaluate the object.
    ///
    /// Returns the evaluation of the object.
    fn evaluate(&self, value: impl Into<U>) -> V;
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
