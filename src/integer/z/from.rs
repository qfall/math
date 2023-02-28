//! Implementations to create a [Z] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [From] trait should be implemented.
//!
//! The explicit functions contain the documentation.

use flint_sys::fmpz::{fmpz, fmpz_init_set_si, fmpz_set_str};

use super::Z;
use crate::{error::MathError, macros};
use std::{
    ffi::{c_char, CString},
    str::FromStr,
};

impl Z {
    /// Create a new Integer that can grow arbitrary large.
    ///
    /// Input parameters:
    /// * initial: the initial value the integer should have
    ///
    /// Output:
    /// * The new integer
    ///
    /// # Example
    /// ```rust
    /// use math::integer::Z;
    ///
    /// let a: Z = Z::from_i64(42);
    /// ```
    pub fn from_i64(initial: i64) -> Self {
        let mut ret_value = fmpz(0);
        unsafe { fmpz_init_set_si(&mut ret_value, initial) }
        Z { value: ret_value }
    }
}

macros::from_trait!(i64, Z, Z::from_i64);

impl FromStr for Z {
    type Err = MathError;

    /// Create a [Z] integer from a string
    ///
    /// Parameters:
    /// - `s`: the integer
    /// Returns a [Z] or an error, if the provided string was not formatted
    /// correctly.
    ///
    /// # Example:
    /// ```rust
    /// use std::str::FromStr;
    /// use math::integer::z::Z;
    ///  
    /// let a: Z = "100".parse().unwrap();
    /// let b: Z = Z::from_str("100").unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [MathError::InvalidStringToIntInput]
    /// if the provided string was not formatted correctly.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut value: fmpz = fmpz(0);

        let c_string = CString::new(s)?;

        let p: *const c_char = c_string.as_ptr();

        // -1 is returned if the string is an invalid input.
        if -1 == unsafe { fmpz_set_str(&mut value, p, 10) } {
            return Err(MathError::InvalidStringToZInput(s.to_owned()));
        }

        Ok(Z { value })
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use super::Z;

    // Ensure that initialization with large numbers works.
    // Numbers larger than 2^62 bits are represented differently in Flint.
    #[test]
    fn from_i64_max_positive() {
        Z::from_i64(i64::MAX);
    }

    // Ensure that initialization with large negative numbers works.
    // Numbers smaller than -2^62 bits are represented differently in Flint.
    #[test]
    fn from_i64_max_negative() {
        Z::from_i64(i64::MIN);
    }

    // Ensure that the from trait is available for i64 values
    #[test]
    fn from_i64_trait() {
        let _ = Z::from(-10i64);
    }

    // Ensure that initialization with large numbers works.
    #[test]
    fn from_str_max_positive() {
        let _ = Z::from_str(&(i64::MAX).to_string()).unwrap();
    }

    // Ensure that initialization with large numbers (larger than i64) works.
    #[test]
    fn from_str_big_positive() {
        let _ = Z::from_str("10000000000000000000000000000000").unwrap();
    }

    // Ensure that initialization with large negative numbers works.
    #[test]
    fn from_str_min_positive() {
        let _ = Z::from_str(&(i64::MIN).to_string()).unwrap();
    }

    // Ensure that initialization with large negative numbers (larger than i64) works.
    #[test]
    fn from_str_small_positive() {
        let _ = Z::from_str("-10000000000000000000000000000000").unwrap();
    }

    // Ensure that wrong initialization yields an Error.
    #[test]
    fn from_str_error1() {
        assert!(Z::from_str("hbrkt35itu3gg").is_err());
    }

    // Ensure that wrong initialization yields an Error.
    #[test]
    fn from_str_error2() {
        assert!(Z::from_str("3-2").is_err());
    }

    // Ensure that wrong initialization yields an Error.
    #[test]
    fn from_str_error3() {
        assert!(Z::from_str("876/543").is_err());
    }
}
