//! This module contains this crate's error enum. This enum can hold all sorts of errors occuring in this crate s.t. error propagation is simple for developers of this crate and all sorts of thrown errors and error types can be easily found and accessed by developers using this crate. Furthermore, the actual errors are wrapped s.t. all information about the error can be unwrapped again.

use std::num::ParseIntError;
use thiserror::Error;

/// `MathError` defines this crate's error enum, which can hold all sorts of errors occurring in this crate.
///
/// Possible entries:
/// - `InvalidStringToIntInput` is thrown if an invalid string is given to construct a data type
///
/// # Example
/// ```
/// use math::error::MathError;
///
/// fn parse_string_to_int() -> Result<(), MathError> {
///     let text = "abc".to_owned();
///     let i: i32 = text.parse::<i32>()?;
///     return Ok(());
/// }
/// ```
#[derive(Error, Debug)]
pub enum MathError {
    /// parse string to int error
    #[error("invalid string input to parse to int {0}")]
    InvalidStringToIntInput(#[from] ParseIntError),
    #[error("invalid string input to parse to polynomial {0}\nThe format must be '[#number of coefficients]  [0th coefficient] [1st coefficient] ...'")]
    InvalidStringToPolyInput(String),
    #[error("invalid string input to parse to polynomial mod q {0}\nThe format must be '[#number of coefficients]  [0th coefficient] [1st coefficient] ... mod [modulus]'")]
    InvalidStringToPolyModulusInput(String),
    #[error(
        "invalid string input to parse to a modulus {0}\nThe format must be '[1,...,9][0,1,...,9]*"
    )]
    InvalidStringToModulusInput(String),
}
