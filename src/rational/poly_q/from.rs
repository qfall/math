//! Implementations to create a [`PolyQ`] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//!
//! The explicit functions contain the documentation.

use super::PolyQ;
use crate::error::MathError;
use flint_sys::fmpq_poly::{fmpq_poly_init, fmpq_poly_set_str};
use std::{ffi::CString, mem::MaybeUninit, str::FromStr};

impl PolyQ {
    /// Initializes a [`PolyQ`].
    /// This method is used to initialize a [`PolyQ`] internally.
    ///
    /// Returns an initialized [`PolyQ`].
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

    // TODO: the second whitespace is not shown in the Rust-documentation
    /// Create a new polynomial with arbitrarily many coefficients of type
    /// [`Q`](crate::rational::q::Q).
    ///
    /// Parameters:
    /// - `s`: the polynomial of form: "`[#number of coefficients]  [0th coefficient] [1st coefficient] ...`"
    /// Note that the `[#number of coefficients]` and `[0th coefficient]`
    /// are divided by two spaces.
    ///
    /// Returns a [`PolyQ`] or an error, if the provided string was not formatted
    /// correctly.
    ///
    /// # Example
    /// ```rust
    /// use math::rational::PolyQ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyQ::from_str("5  0 1/3 2/10 -3/2 1").unwrap();
    /// ```
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidStringToPolyInput`](MathError::InvalidStringToPolyInput)
    /// if the provided string was not formatted correctly or the number of
    /// coefficients was smaller than the number provided at the start of the
    /// provided string.
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToPolyMissingWhitespace`](`MathError::InvalidStringToPolyMissingWhitespace`)
    /// if the provided value did not contain two whitespaces.
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToCStringInput`](MathError::InvalidStringToCStringInput)
    /// if the provided string contains a Null Byte.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut res = Self::init();

        let c_string = CString::new(s)?;

        // 0 is returned if the string is a valid input
        // additionally if it was not successfully, test if the provided value 's' actually
        // contains two whitespaces, since this might be a common error
        match unsafe { fmpq_poly_set_str(&mut res.poly, c_string.as_ptr()) } {
            0 => Ok(res),
            _ if !s.contains("  ") => Err(MathError::InvalidStringToPolyMissingWhitespace(
                s.to_owned(),
            )),
            _ => Err(MathError::InvalidStringToPolyInput(s.to_owned())),
        }
    }
}

#[cfg(test)]
mod test_from_str {
    use std::str::FromStr;

    use super::PolyQ;

    // tests whether a correctly formatted string outputs an instantiation of a
    // polynomial, i.e. does not return an error
    #[test]
    fn working_example() {
        assert!(PolyQ::from_str("3  1 2/5 -3/2").is_ok());
    }

    // tests whether a falsely formatted string (missing double-space) returns
    // an error
    #[test]
    fn missing_whitespace() {
        assert!(PolyQ::from_str("3 1 2/5 -3/2").is_err());
    }

    // tests whether a falsely formatted string (too many whitespaces) returns
    // an error
    #[test]
    fn too_many_whitespaces() {
        assert!(PolyQ::from_str("3  1  2/5  -3/2").is_err());
    }

    // tests whether a falsely formatted string (wrong number of total
    // coefficients) returns an error
    #[test]
    fn false_number_of_coefficient() {
        assert!(PolyQ::from_str("4  1 2/5 -3/2").is_err());
    }

    // tests whether a falsely formatted string (too many divisors) returns
    // an error
    #[test]
    fn too_many_divisors() {
        assert!(PolyQ::from_str("3  1 2/5 -3/2/3").is_err());
    }
}
