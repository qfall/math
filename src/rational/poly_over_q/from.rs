//! Implementations to create a [`PolyOverQ`] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//!
//! The explicit functions contain the documentation.

use super::PolyOverQ;
use crate::error::MathError;
use flint_sys::fmpq_poly::{fmpq_poly_init, fmpq_poly_set_str};
use std::{ffi::CString, mem::MaybeUninit, str::FromStr};

impl Default for PolyOverQ {
    /// Initializes a [`PolyOverQ`].
    /// This method is used to initialize a [`PolyOverQ`].
    ///
    /// Returns an initialized [`PolyOverQ`].
    ///
    /// # Example
    /// ```rust
    /// use math::rational::PolyOverQ;
    ///
    /// let poly_over_zero = PolyOverQ::default(); // initializes a PolyOverQ as "0"
    /// ```
    fn default() -> Self {
        let mut poly = MaybeUninit::uninit();
        unsafe {
            fmpq_poly_init(poly.as_mut_ptr());
            let poly = poly.assume_init();
            Self { poly }
        }
    }
}

impl FromStr for PolyOverQ {
    type Err = MathError;

    /// Create a new polynomial with arbitrarily many coefficients of type
    /// [`Q`](crate::rational::Q).
    ///
    /// Parameters:
    /// - `s`: the polynomial of form: "`[#number of coefficients]⌴⌴[0th coefficient]⌴[1st coefficient]⌴...`"
    /// Note that the `[#number of coefficients]` and `[0th coefficient]`
    /// are divided by two spaces.
    ///
    /// Returns a [`PolyOverQ`] or an error, if the provided string was not formatted
    /// correctly.
    ///
    /// # Example
    /// ```rust
    /// use math::rational::PolyOverQ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverQ::from_str("5  0 1/3 2/10 -3/2 1").unwrap();
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
        let mut res = Self::default();

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

    use super::PolyOverQ;

    /// tests whether a correctly formatted string outputs an instantiation of a
    /// polynomial, i.e. does not return an error
    #[test]
    fn working_example() {
        assert!(PolyOverQ::from_str("3  1 2/5 -3/2").is_ok());
    }

    /// tests whether a falsely formatted string (missing double-space) returns
    /// an error
    #[test]
    fn missing_whitespace() {
        assert!(PolyOverQ::from_str("3 1 2/5 -3/2").is_err());
    }

    /// tests whether a falsely formatted string (too many whitespaces) returns
    /// an error
    #[test]
    fn too_many_whitespaces() {
        assert!(PolyOverQ::from_str("3  1  2/5  -3/2").is_err());
    }

    /// tests whether a falsely formatted string (wrong number of total
    /// coefficients) returns an error
    #[test]
    fn false_number_of_coefficient() {
        assert!(PolyOverQ::from_str("4  1 2/5 -3/2").is_err());
    }

    /// tests whether a falsely formatted string (too many divisors) returns
    /// an error
    #[test]
    fn too_many_divisors() {
        assert!(PolyOverQ::from_str("3  1 2/5 -3/2/3").is_err());
    }
}

// ensure that init initializes an empty polynomial
#[cfg(test)]
mod test_init {

    use crate::rational::PolyOverQ;

    /// Ensure that [`Default`] initializes the zero polynomial appropriately
    #[test]
    fn init_zero() {
        let poly_over_zero = PolyOverQ::default();

        assert_eq!("0", poly_over_zero.to_string())
    }
}
