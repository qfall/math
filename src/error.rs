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

use std::{ffi::NulError, num::ParseIntError};
use thiserror::Error;

/// [`MathError`] defines this crate's error enum, which can hold all sorts of
/// errors occurring in this crate.
///
/// Possible entries:
/// - `DivisionByZeroError` is thrown if it is tried to perform a division by `0`
/// - `InvalidIntToModulus` is thrown if an integer is provided, which is not greater than `0`
/// - `InvalidMatrix` is thrown if an invalid string input of a matrix is given
/// - `InvalidStringToCStringInput` is thrown if an invalid string is given to
/// construct a [`CString`](std::ffi::CString)
/// - `InvalidStringToIntInput` is thrown if an invalid string is given to
/// construct an integer.
/// - `InvalidStringToMatZqInput` is thrown if an invalid string is given to
/// construct a Matrix of [`MatZq`](crate::integer_mod_q::MatZq)
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
/// - `InvalidStringToZqInput` is thrown if an invalid string is given to
/// construct a [`Zq`](crate::integer_mod_q::Zq)
/// - `MismatchingModulus` is thrown if any function is called on two
/// objects with different modulus where equal modulus is required
/// - `MismatchingVectorDimensions` is thrown if an operation of two vectors is
/// called for which their dimensions do not match
/// - `NotPrime` is thrown if a provided integer is not prime
/// - `OutOfBounds` is thrown if a provided index is not in a desired range
/// - `VectorFunctionCalledOnNonVector` is thrown if a function defined
/// on vectors was called on a matrix instance that is not a vector
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

    /// parse string to [`MatZq`](crate::integer_mod_q::MatZq) error
    #[error("invalid string input to parse to MatZq {0}")]
    InvalidStringToMatZqInput(String),

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

    /// parse string to [`Zq`](crate::integer_mod_q::Zq) error
    #[error("invalid string input to parse to Zq {0}")]
    InvalidStringToZqInput(String),

    /// mismatching modulus error
    #[error("mismatching modulus.{0}")]
    MismatchingModulus(String),

    /// mismatching dimensions of vectors
    #[error("mismatching vector dimensions. {0}")]
    MismatchingVectorDimensions(String),

    /// if an integer or modulus is not prime
    #[error("invalid integer. The integer has to be prime and the provided value is {0}")]
    NotPrime(String),

    /// if a provided index is out of bounds
    #[error(
        "invalid index submitted. The index is out of bounds.
        The index has to {0}, and the provided value is {1}"
    )]
    OutOfBounds(String, String),

    /// if a function defined on vectors is called on a matrix that is not a vector
    #[error(
        "Function named {0} is only defined for vectors and 
        was called on a matrix of dimension {1}x{2}"
    )]
    VectorFunctionCalledOnNonVector(String, i64, i64),
}
