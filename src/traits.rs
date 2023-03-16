//! This module contains basic traits for this library. These include
//! specific traits for matrices and polynomials.

use crate::error::MathError;
use std::fmt::Display;

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
