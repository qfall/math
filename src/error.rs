// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains this crate's error enum. This enum can hold all sorts
//! of errors occurring in this crate s.t. error propagation is simple for
//! developers of this crate and all sorts of thrown errors and error types can
//! be easily found and accessed by developers using this crate. Furthermore,
//! the actual errors are wrapped s.t. all information about the error can be
//! unwrapped again.
//!
//! **For developers:**
//! - How to add an error to an `enum`? First of all, find a name
//!     that is not too specific for your current case s.t. it could be used in other
//!     contexts afterwards as well. Then, find the spot according to your chosen error
//!     name in a alphanumerically sorted way in the list of supported errors in the doc
//!     comment and inside the `enum` itself.
//!     Afterwards, add the error to the list of implemented error
//!     types in the doc comment of the `enum` with a short description when it is thrown.
//!     Probably use this description for the doc comment above the implementation of
//!     error in the `enum`. Then, add `#[error(<error msg>)]` to define the error message
//!     output once your error is thrown. Below, write down `<error name>(<input>),` to
//!     define the error with its name and possibly some inputs. The input can be of the
//!     form [`String`], but also another error, whose conversion must be declared via
//!     `#[from] OtherError`. It is best to use the existing structure as a guide. For any
//!     further information, check out the here used [`thiserror`]-crate.

use std::ffi::NulError;
use thiserror::Error;

/// [`MathError`] defines this crate's error enum, which can hold all sorts of
/// errors occurring in this crate.
///
/// Implemented error types:
/// -  [`ConversionError`](MathError::ConversionError) is thrown if a conversion
///     between types is not possible.
/// - [`DivisionByZeroError`](MathError::DivisionByZeroError) is thrown if it is
///     tried to perform a division by `0`.
/// - [`InvalidExponent`](MathError::InvalidExponent) is thrown if an invalid
///     exponent is used for a `pow` function.
/// - [`InvalidIntegerInput`](MathError::InvalidIntegerInput) is thrown if an
///     integer input is provided as parameter that does not meet the conditions
///     of that function.
/// - [`InvalidInterval`](MathError::InvalidInterval) is thrown if an invalid
///     interval, e.g. of negative size, is provided.
/// - [`InvalidModulus`](MathError::InvalidModulus) is thrown if an integer is
///     provided, which is not greater than `1`.
/// - [`NulError`](MathError::NulError) is thrown if a [`NulError`] is thrown,
///     which currently only happens if an invalid string is given to construct
///     a [`CString`](std::ffi::CString).
/// - [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension) is
///     thrown if arithmetic is done with matrices of mismatching dimensions.
/// - [`MismatchingModulus`](MathError::MismatchingModulus) is thrown if any
///     function is called on two objects with different modulus where equal
///     modulus is required.
/// - [`NonPositive`](MathError::NonPositive) is thrown if the function expects
///     a positive number, but a number smaller than `1` is provided.
/// - [`NoSquareMatrix`](MathError::NoSquareMatrix) is thrown if a matrix is
///     not square.
/// - [`OutOfBounds`](MathError::OutOfBounds) is thrown if a provided index
///     is not in a desired range.
/// - [`VectorFunctionCalledOnNonVector`](MathError::VectorFunctionCalledOnNonVector)
///     is thrown if a function defined on vectors was called on a matrix instance
///     that is not a vector.
///
/// # Examples
/// ```
/// use qfall_math::{error::MathError, rational::Q};
/// use std::str::FromStr;
///
/// fn parse_string_to_q() -> Result<(), MathError> {
///     let text = "2/0";
///     let q = Q::from_str(text)?;
///     return Ok(());
/// }
/// ```
#[derive(Error, Debug)]
pub enum MathError {
    /// Conversion error.
    #[error("While performing the conversion an error occurred: {0}")]
    ConversionError(String),

    /// Division by zero error.
    #[error("The division by zero is not possible {0}")]
    DivisionByZeroError(String),

    /// Invalid exponent.
    #[error("Invalid exponent given: {0}")]
    InvalidExponent(String),

    /// Invalid integer was input to a specific function.
    #[error("An invalid integer input was given as a parameter: {0}")]
    InvalidIntegerInput(String),

    /// Invalid interval provided.
    #[error("An invalid interval was given: {0}")]
    InvalidInterval(String),

    /// Parse int to modulus error.
    #[error("An invalid value should be parsed as a modulus {0}.")]
    InvalidModulus(String),

    /// Converts a [`NulError`], which currently only happens if an
    /// invalid string is given to construct a [`CString`](std::ffi::CString).
    #[error(
        "A nul error occurred, which usually happens if an invalid \
        string input is parsed to a CString {0}"
    )]
    NulError(#[from] NulError),

    /// Mismatching matrix dimension error.
    #[error("Mismatching matrix dimensions {0}")]
    MismatchingMatrixDimension(String),

    /// Mismatching modulus error.
    #[error("Mismatching modulus.{0}")]
    MismatchingModulus(String),

    /// If an integer is not a positive number.
    #[error(
        "A function that can only be performed on positive values was \
        performed on performed on a non-positive value, which is {0}."
    )]
    NonPositive(String),

    /// If a matrix is not square.
    #[error("The matrix is not square {0}")]
    NoSquareMatrix(String),

    /// If a provided index is out of bounds.
    #[error(
        "Invalid index submitted. The index is out of bounds.
        The index has to {0}, and the provided value is {1}"
    )]
    OutOfBounds(String, String),

    /// Some string to one of our data-types error occurred.
    #[error("{0}")]
    StringConversionError(#[from] StringConversionError),

    /// If a function defined on vectors is called on a matrix that is not a vector.
    #[error(
        "Function named {0} is only defined for vectors and 
        was called on a matrix of dimension {1}x{2}"
    )]
    VectorFunctionCalledOnNonVector(String, i64, i64),
}

/// [`StringConversionError`] defines an error enum,
/// which holds all [`String`] to data-type conversion errors.
///
/// Implemented error types:
/// - [`InvalidMatrix`](StringConversionError::InvalidMatrix) is thrown if an
///     invalid string input of a matrix is given.
/// - [`InvalidStringToPolyInput`](StringConversionError::InvalidStringToPolyInput)
///     is thrown if an invalid string is given to construct a polynomial.
/// - [`InvalidStringToPolyMissingWhitespace`](StringConversionError::InvalidStringToPolyMissingWhitespace)
///     is thrown if an invalid string is given to construct a polynomial which
///     did not contain two whitespaces.
/// - [`InvalidStringToPolyModulusInput`](StringConversionError::InvalidStringToPolyModulusInput)
///     is thrown if an invalid string is given
///     to construct a [`PolyOverZq`](crate::integer_mod_q::PolyOverZq), i.e. it is
///     not formatted correctly.
/// - [`InvalidStringToQInput`](StringConversionError::InvalidStringToQInput)
///     is thrown if an invalid string is given to construct a [`Q`](crate::rational::Q).
/// - [`InvalidStringToZInput`](StringConversionError::InvalidStringToZInput)
///     is thrown if an invalid string is given to construct a [`Z`](crate::integer::Z).
/// - [`InvalidStringToZqInput`](StringConversionError::InvalidStringToZqInput)
///     is thrown if an invalid string is given to construct a [`Zq`](crate::integer_mod_q::Zq).
///
/// # Examples
/// ```
/// use qfall_math::error::StringConversionError;
///
/// fn throws_error() -> Result<(), StringConversionError> {
///     return Err(
///         StringConversionError::InvalidMatrix(String::from(
///             "Some silly mistake was made",
///         )),
///     );
///
///     Ok(())
/// }
/// ```
#[derive(Error, Debug)]
pub enum StringConversionError {
    /// Invalid Matrix input error.
    #[error("invalid Matrix. {0}")]
    InvalidMatrix(String),

    /// Parse string to poly error.
    #[error(
        "Invalid string input to parse to polynomial {0}\nThe format must 
        be '[#number of coefficients]  [0th coefficient] [1st coefficient] ...'. 
        Note that the after the number of coefficients, there are two 
        whitespace."
    )]
    InvalidStringToPolyInput(String),

    /// Parse string to poly error with missing whitespace.
    #[error(
        "Invalid string input to parse to polynomial {0}
        The string did not contain two whitespace at the start. Please note, 
        that there have to two whitespace between number of coefficients 
        and the first coefficient"
    )]
    InvalidStringToPolyMissingWhitespace(String),

    /// Parse string to poly with modulus error.
    #[error(
        "Invalid string input to parse to polynomial mod q {0}.
        The format must \
        be '[#number of coefficients]  [0th coefficient] [1st coefficient] ... \
        mod [modulus]'. 
        Note that the after the number of coefficients, there are two \
        whitespaces."
    )]
    InvalidStringToPolyModulusInput(String),

    /// Parse string to [`Q`](crate::rational::Q) error
    #[error("Invalid string input to parse to Q {0}")]
    InvalidStringToQInput(String),

    /// Parse string to [`Z`](crate::integer::Z) error.
    #[error("Invalid string input to parse to Z {0}")]
    InvalidStringToZInput(String),

    /// Parse string to [`Zq`](crate::integer_mod_q::Zq) error.
    #[error("Invalid string input to parse to Zq {0}")]
    InvalidStringToZqInput(String),
}
