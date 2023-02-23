//! Implementations of the 'From' trait for [PolyQ].
//!
//! This module contains all options to create a polynomial of type [PolyQ].

use std::{
    ffi::{c_char, CString},
    mem::MaybeUninit,
    str::FromStr,
};

use flint_sys::fmpq_poly::{fmpq_poly_init, fmpq_poly_set_str};

use crate::error::MathError;

use super::PolyQ;

impl PolyQ {
    /// Creates an initialization of a [PolyQ] which can not yet be used. It needs to be assigned coefficients.
    /// This method is used to first construct a [PolyQ] and then later assign the corresponding efficients with methods from FLINT.
    ///
    /// Returns an inititialized [PolyQ].
    fn init() -> Self {
        let mut poly = MaybeUninit::uninit();
        unsafe {
            fmpq_poly_init(poly.as_mut_ptr());
            let poly = poly.assume_init();
            Self { poly }
        }
    }
}

impl FromStr for PolyQ {
    type Err = MathError;

    /// Create a new polynomial with integer coefficients of arbitrary length using a string as input.
    ///
    /// Parameters:
    /// - s: the polynomial of form: "[#number of coefficients]  [0th coefficient] [1st coefficient] ..."
    /// Returns a [PolyQ] or an error, if the provided string was not formatted correctly.
    ///
    /// # Example
    /// ```rust
    /// use math::rational::PolyQ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyQ::from_str("4  0 1/3 2/10 -3/2").unwrap();
    /// ```
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
        if -1 == unsafe { fmpq_poly_set_str(&mut res.poly, p) } {
            return Err(MathError::InvalidStringToPolyInput(s.to_owned()));
        }

        Ok(res)
    }
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use crate::rational::poly_q::PolyQ;

    // tests whether a correctly formatted string outputs an instantiation of a polynomial, i.e. does not return an error
    #[test]
    fn from_str_working_example() {
        assert!(PolyQ::from_str("3  1 2/5 -3/2").is_ok());
    }

    // tests whether a falsely formatted string (missing double-space) returns an error
    #[test]
    fn from_str_false_format() {
        assert!(PolyQ::from_str("3 1 2/5 -3/2").is_err());
    }

    // tests whether a falsely formatted string (wrong number of total coefficients) returns an error
    #[test]
    fn from_str_false_number_of_coefficient() {
        assert!(PolyQ::from_str("4  1 2/5 -3/2").is_err());
    }
}
