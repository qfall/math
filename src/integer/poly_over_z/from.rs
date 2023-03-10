//! Implementations to create a [`PolyOverZ`] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//!
//! The explicit functions contain the documentation.

use super::PolyOverZ;
use crate::error::MathError;
use flint_sys::fmpz_poly::{fmpz_poly_init, fmpz_poly_set_str};
use std::{ffi::CString, mem::MaybeUninit, str::FromStr};

impl Default for PolyOverZ {
    /// Initializes a [`PolyOverZ`].
    /// This method is used to initialize a [`PolyOverZ`].
    ///
    /// Returns an initialized [`PolyOverZ`].
    ///
    /// # Example
    /// ```rust
    /// use math::integer::PolyOverZ;
    ///
    /// let poly_over_zero = PolyOverZ::default(); // initializes a PolyOverZ as "0"
    /// ```
    fn default() -> Self {
        let mut poly = MaybeUninit::uninit();
        unsafe {
            fmpz_poly_init(poly.as_mut_ptr());

            Self {
                poly: poly.assume_init(),
            }
        }
    }
}

impl FromStr for PolyOverZ {
    type Err = MathError;

    // TODO: the second whitespace is not shown in the Rust-documentation
    /// Create a new polynomial with arbitrarily many coefficients of type
    /// [`Z`](crate::integer::Z).
    ///
    /// Parameters:
    /// - `s`: the polynomial of form: `"[#number of coefficients]⌴⌴[0th coefficient]⌴[1st coefficient]⌴..."`.
    ///  Note that the `[#number of coefficients]` and `[0th coefficient]`
    ///  are divided by two spaces.
    ///
    /// Returns a [`PolyOverZ`] or an error, if the provided string was not formatted
    /// correctly.
    ///
    /// # Example
    /// ```rust
    /// use math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZ::from_str("4  0 1 2 3").unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::InvalidStringToPolyInput`]
    /// if the provided string was not formatted correctly or the number of
    /// coefficients was smaller than the number provided at the start of the
    /// provided string.
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToPolyMissingWhitespace`](MathError::InvalidStringToPolyMissingWhitespace)
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
        match unsafe { fmpz_poly_set_str(&mut res.poly, c_string.as_ptr()) } {
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

    use super::PolyOverZ;

    /// tests whether a correctly formatted string outputs an instantiation of a
    /// polynomial, i.e. does not return an error
    #[test]
    fn working_example() {
        assert!(PolyOverZ::from_str("3  1 2 -3").is_ok());
    }

    /// tests whether a falsely formatted string (missing double-space) returns
    /// an error
    #[test]
    fn missing_whitespace() {
        assert!(PolyOverZ::from_str("3 1 2 -3").is_err());
    }

    /// tests whether a falsely formatted string (too many whitespaces) returns
    /// an error
    #[test]
    fn too_many_whitespaces() {
        assert!(PolyOverZ::from_str("3  1  2  -3").is_err());
    }

    /// tests whether a falsely formatted string (wrong number of total
    /// coefficients) returns an error
    #[test]
    fn false_number_of_coefficient() {
        assert!(PolyOverZ::from_str("4  1 2 -3").is_err());
    }
}

// ensure that init initializes an empty polynomial
#[cfg(test)]
mod test_init {
    use std::str::FromStr;

    use crate::integer::PolyOverZ;

    /// Check if [`Default`] initializes the zero polynomial appropriately
    #[test]
    fn init_zero() {
        let poly_over_zero = PolyOverZ::default();

        assert_eq!(PolyOverZ::from_str("0").unwrap(), poly_over_zero)
    }
}
