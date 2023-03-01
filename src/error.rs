//! This module contains this crate's error enum. This enum can hold all sorts of errors occuring in this crate s.t. error propagation is simple for developers of this crate and all sorts of thrown errors and error types can be easily found and accessed by developers using this crate. Furthermore, the actual errors are wrapped s.t. all information about the error can be unwrapped again.

use std::{ffi::NulError, num::ParseIntError};

use thiserror::Error;

/// [`MathError`] defines this crate's error enum, which can hold all sorts of errors occurring in this crate.
///
/// Possible entries:
/// - `InvalidStringToIntInput` is thrown if an invalid string is given to construct an Int
/// - `InvalidStringToZInput` is thrown if an invalid string is given to construct a [`Z`](crate::integer::Z)
/// - `InvalidStringToCStringInput` is thrown if an invalid string is given to construct a [`CString`](std::ffi::CString)
/// - `InvalidStringToPolyInput` is thrown if an invalid string is given to
/// construct a polynomial
/// - `InvalidStringToPolyMissingWhiteSpace` is thrown if an invalid string
/// is given to construct a polynomial which did not contain two whitespaces
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
    /// parse string to [`Z`](crate::integer::Z) error
    #[error("invalid string input to parse to Z {0}")]
    InvalidStringToZInput(String),
    /// parse string to [`CString`](std::ffi::CString) error
    #[error("invalid string input to parse to CString {0}")]
    InvalidStringToCStringInput(#[from] NulError),
    /// parse string to poly error
    #[error(
        "invalid string input to parse to polynomial {0}\nThe format must 
        be '[#number of coefficients]  [0th coefficient] [1st coefficient] ...'. 
        Note that the after the number of coefficients, there are two 
        whitespaces."
    )]
    InvalidStringToPolyInput(String),
    /// parse string to poly error with missing whitespaces
    #[error(
        "invalid string input to parse to polynomial {0}\n \
        The string did not contain two whitespaces at the start. Please note, 
        that there have to two whitespaces between number of coefficients 
        and the first coefficient"
    )]
    InvalidStringToPolyMissingWhitespace(String),
}
