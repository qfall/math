//! Implementations of the 'From' trait for [PolyZ].
//!
//! This module contains all options to create a polynomial of type [PolyZ].

use std::{
    ffi::{c_char, CString},
    mem::MaybeUninit,
    str::FromStr,
};

use flint_sys::fmpz_poly::{fmpz_poly_init, fmpz_poly_set_str};

use crate::error::MathError;

use super::PolyZ;

impl PolyZ {
    /// Creates an initialization of a [PolyZ] which can not yet be used. It needs to be assigned coefficients.
    /// This method is used to first construct a [PolyZ] and then later assign the corresponding efficients with methods from FLINT.
    ///
    /// Returns an inititialized [PolyZ].
    fn init() -> Self {
        let mut poly = MaybeUninit::uninit();
        unsafe {
            fmpz_poly_init(poly.as_mut_ptr());
            let poly = poly.assume_init();
            Self { poly }
        }
    }
}

impl FromStr for PolyZ {
    type Err = MathError;

    /// Create a new polynomial with integer coefficients of arbitrary length using a string as input.
    ///
    /// Parameters:
    /// - `s`: the polynomial of form: "[#number of coefficients]  [0th coefficient] [1st coefficient] ..."
    /// Returns a [PolyZ] or an error, if the provided string was not formatted correctly.
    ///
    /// # Example
    /// ```rust
    /// use math::integer::PolyZ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyZ::from_str("4  0 1 2 3").unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [MathError::InvalidStringToPolyInput] if the provided string was not formatted correctly or the number of
    /// coefficients was smaller than the number provided at the start of the provided string.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut res = Self::init();

        let c_string = match CString::new(s) {
            Ok(c_string) => c_string,
            Err(_) => return Err(MathError::InvalidStringToPolyInput(s.to_owned())),
        };
        let p: *const c_char = c_string.as_ptr();

        // -1 is returned if the string is an invalid input
        if -1 == unsafe { fmpz_poly_set_str(&mut res.poly, p) } {
            return Err(MathError::InvalidStringToPolyInput(s.to_owned()));
        }

        Ok(res)
    }
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use crate::integer::poly_z::PolyZ;

    // tests whether a correctly formatted string outputs an instantiation of a polynomial, i.e. does not return an error
    #[test]
    fn from_str_working_example() {
        assert!(PolyZ::from_str("3  1 2 -3").is_ok());
    }

    // tests whether a falsely formatted string (missing double-space) returns an error
    #[test]
    fn from_str_false_format() {
        assert!(PolyZ::from_str("3 1 2 -3").is_err());
    }

    // tests whether a falsely formatted string (wrong number of total coefficients) returns an error
    #[test]
    fn from_str_false_number_of_coefficient() {
        assert!(PolyZ::from_str("4  1 2 -3").is_err());
    }
}
