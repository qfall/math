//! This module contains this crate's error enum. This enum can hold all sorts
//! of errors occurring in this crate s.t. error propagation is simple for
//! developers of this crate and all sorts of thrown errors and error types can
//! be easily found and accessed by developers using this crate. Furthermore,
//! the actual errors are wrapped s.t. all information about the error can be
//! unwrapped again.

use std::{ffi::NulError, num::ParseIntError};
use thiserror::Error;

/// [`MathError`] defines this crate's error enum, which can hold all sorts of
/// errors occurring in this crate.
///
/// Possible entries:
/// - `DivisionByZeroError` is thrown if it is tried to perform a division by `0`
/// - `InvalidInitMatZInput` is thrown if an invalid integer is given to create
/// a [`MatZ`](crate::integer::MatZ)
/// - `InvalidIntToModulus` is thrown if an integer is provided, which is not greater than zero
/// - `InvalidMatrix` is thrown if an invalid string input of a matrix is given
/// - `InvalidStringToCStringInput` is thrown if an invalid string is given to
/// construct a [`CString`](std::ffi::CString)
/// - `InvalidStringToIntInput` is thrown if an invalid string is given to
/// construct an integer.
/// - `InvalidStringToMatZInput` is thrown if an invalid string is given to
/// construct a Matrix of [`MatZ`](crate::integer::MatZ)
/// - `InvalidStringToModulusInput` is thrown if an invalid string is given to
/// construct a modulus.
/// - `InvalidStringToPolyInput` is thrown if an invalid string is given to
/// construct a polynomial
/// - `InvalidStringToPolyMissingWhiteSpace` is thrown if an invalid string
/// is given to construct a polynomial which did not contain two whitespaces
/// - `InvalidStringToPolyModulusInput` is thrown if an invalid string is given
/// to construct a [`PolyOverZq`](crate::integer_mod_q::PolyOverZq), i.e. it is
/// not formatted correctly.
/// - `InvalidStringToQInput` is thrown if an invalid string is given to
/// construct a [`Q`](crate::rational::Q)
/// - `InvalidStringToZInput` is thrown if an invalid string is given to
/// construct a [`Z`](crate::integer::Z)
/// - `OutOfBounds` is thrown if a provided index is not in a desired range
/// - `RegexError` is thrown if an regular expression could not be processed
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
    /// division by zero error
    #[error("the division by zero is not possible {0}")]
    DivisionByZeroError(String),
    /// initialization of [`MatZ`](crate::integer::MatZ) error
    #[error("invalid input for an initialization of a MatZ {0}")]
    InvalidInitMatZInput(String),
    /// parse int to modulus error
    #[error(
        "invalid integer input to parse to a modulus {0}. \
        The value must be larger than 0."
    )]
    InvalidIntToModulus(String),
    /// invalid Matrix input error
    #[error("invalid Matrix. {0}")]
    InvalidMatrix(String),
    /// parse string to [`CString`](std::ffi::CString) error
    #[error("invalid string input to parse to CString {0}")]
    InvalidStringToCStringInput(#[from] NulError),
    /// parse string to int error
    #[error("invalid string input to parse to int {0}")]
    InvalidStringToIntInput(#[from] ParseIntError),
    /// parse string to [`MatZ`](crate::integer::MatZ) error
    #[error("invalid string input to parse to MatZ {0}")]
    InvalidStringToMatZInput(String),
    /// parse string to modulus error
    #[error(
        "invalid string input to parse to a modulus {0}. \
        The format must be '[0-9]+' and not all zeros."
    )]
    InvalidStringToModulusInput(String),
    /// parse string to poly error
    #[error(
        "invalid string input to parse to polynomial {0}\nThe format must 
        be '[#number of coefficients]  [0th coefficient] [1st coefficient] ...'. 
        Note that the after the number of coefficients, there are two 
        whitespace."
    )]
    InvalidStringToPolyInput(String),
    /// parse string to poly error with missing whitespace
    #[error(
        "invalid string input to parse to polynomial {0}
        The string did not contain two whitespace at the start. Please note, 
        that there have to two whitespace between number of coefficients 
        and the first coefficient"
    )]
    InvalidStringToPolyMissingWhitespace(String),
    /// parse string to poly with modulus error
    #[error(
        "invalid string input to parse to polynomial mod q {0}.
        The format must \
        be '[#number of coefficients]  [0th coefficient] [1st coefficient] ... \
        mod [modulus]'. 
        Note that the after the number of coefficients, there are two \
        whitespaces."
    )]
    InvalidStringToPolyModulusInput(String),
    /// parse string to [`Q`](crate::rational::Q) error
    #[error("invalid string input to parse to Q {0}")]
    InvalidStringToQInput(String),
    /// parse string to [`Z`](crate::integer::Z) error
    #[error("invalid string input to parse to Z {0}")]
    InvalidStringToZInput(String),
    /// if a provided index is out of bounds
    #[error(
        "invalid index submitted. The index is out of bounds.
        The index has to {0}, and the provided value is {1}"
    )]
    OutOfBounds(String, String),
    /// Regex error
    #[error("The regular expression could not be processed: {0}")]
    RegexError(String),
}
