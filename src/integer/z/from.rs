//! Implementations to create a [Z] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [From] trait should be implemented.
//!
//! The explicit functions contain the documentation.

use flint_sys::fmpz::{fmpz, fmpz_init_set_si, fmpz_init_set_ui, fmpz_set_str};

use super::Z;
use crate::{error::MathError, macros};
use std::{ffi::CString, str::FromStr};

impl Z {
    /// Create a new Integer that can grow arbitrary large.
    ///
    /// Parameters:
    /// - value: the initial value the integer should have
    /// Returns the new integer.
    ///
    /// # Example
    /// ```rust
    /// use math::integer::Z;
    ///
    /// let a: Z = Z::from_i64(42);
    /// ```
    pub fn from_i64(value: i64) -> Self {
        let mut ret_value = fmpz(0);
        unsafe { fmpz_init_set_si(&mut ret_value, value) }
        Z { value: ret_value }
    }

    /// Create a new Integer that can grow arbitrary large.
    ///
    /// Parameters:
    /// - value: the initial value the integer should have
    /// Returns the new integer.
    ///
    /// # Example
    /// ```rust
    /// use math::integer::Z;
    ///
    /// let a: Z = Z::from_u64(42);
    /// ```
    pub fn from_u64(value: u64) -> Self {
        let mut ret_value = fmpz(0);
        unsafe { fmpz_init_set_ui(&mut ret_value, value) }
        Z { value: ret_value }
    }

    // Generate from_<type> functions for singed and unsigned source types.
    macros::from_type!(i32, i64, Z, Z::from_i64);
    macros::from_type!(i16, i64, Z, Z::from_i64);
    macros::from_type!(i8, i64, Z, Z::from_i64);

    macros::from_type!(u32, u64, Z, Z::from_u64);
    macros::from_type!(u16, u64, Z, Z::from_u64);
    macros::from_type!(u8, u64, Z, Z::from_u64);
}

// Generate [From] trait for the different types.
macros::from_trait!(i64, Z, Z::from_i64);
macros::from_trait!(i32, Z, Z::from_i32);
macros::from_trait!(i16, Z, Z::from_i16);
macros::from_trait!(i8, Z, Z::from_i8);

macros::from_trait!(u64, Z, Z::from_u64);
macros::from_trait!(u32, Z, Z::from_u32);
macros::from_trait!(u16, Z, Z::from_u16);
macros::from_trait!(u8, Z, Z::from_u8);

impl FromStr for Z {
    type Err = MathError;

    /// Create a [`Z`] integer from a [`String`]
    /// The format of that string looks like this `(-)12` for the number 12 or -12
    ///
    /// Parameters:
    /// - `s`: the integer value
    ///
    /// Returns a [`Z`] or an error, if the provided string was not formatted
    /// correctly.
    ///
    /// # Example:
    /// ```rust
    /// use std::str::FromStr;
    /// use math::integer::Z;
    ///  
    /// let a: Z = "100".parse().unwrap();
    /// let b: Z = Z::from_str("100").unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [InvalidStringToCStringInput](MathError::InvalidStringToCStringInput)
    /// if the provided string contains a Nul byte.
    /// - Returns a [`MathError`] of type
    /// [InvalidStringToZInput](MathError::InvalidStringToZInput)
    /// if the provided string was not formatted correctly.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.contains(char::is_whitespace) {
            return Err(MathError::InvalidStringToZInput(s.to_owned()));
        }

        // since |value| = |0| < 62 bits, we do not need to free the allocated space manually
        let mut value: fmpz = fmpz(0);

        let c_string = CString::new(s)?;

        // -1 is returned if the string is an invalid input.
        // Given the documentation `c_string.as_ptr()` is freed once c_string is deallocated
        // 'The pointer will be valid for as long as `self` is'
        // For reading more look at the documentation of `.as_ptr()`.
        match unsafe { fmpz_set_str(&mut value, c_string.as_ptr(), 10) } {
            0 => Ok(Z { value }),
            _ => Err(MathError::InvalidStringToZInput(s.to_owned())),
        }
    }
}

#[cfg(test)]
mod tests_from_int {
    use super::Z;

    // Ensure that initialization with large numbers works.
    // Numbers larger than 2^62 bits are represented differently in FLINT.
    #[test]
    fn from_i64_max_positive() {
        Z::from_i64(i64::MAX);
    }

    // Ensure that initialization with large negative numbers works.
    // Numbers smaller than -2^62 bits are represented differently in FLINT.
    #[test]
    fn from_i64_max_negative() {
        Z::from_i64(i64::MIN);
    }

    // Ensure that the [From] trait is available for i64 values
    #[test]
    fn from_i64_trait() {
        let _ = Z::from(-10i64);
    }

    // Ensure that the `from_<type_name>` functions are available for
    // singed and unsigned integers of 8, 16, 32, and 64 bit length.
    // Tested with their maximum value.
    #[test]
    fn from_functions_max() {
        // signed
        let _ = Z::from_i8(i8::MAX);
        let _ = Z::from_i16(i16::MAX);
        let _ = Z::from_i32(i32::MAX);
        let _ = Z::from_i64(i64::MAX);

        // unsigned
        let _ = Z::from_u8(u8::MAX);
        let _ = Z::from_u16(u16::MAX);
        let _ = Z::from_u32(u32::MAX);
        let _ = Z::from_u64(u64::MAX);
    }

    // Ensure that the [From] trait is available for singed and unsigned integers
    // of 8, 16, 32, and 64 bit length. Tested with their maximum value.
    #[test]
    fn from_trait_max() {
        // signed
        let _ = Z::from(i8::MAX);
        let _ = Z::from(i16::MAX);
        let _ = Z::from(i32::MAX);
        let _ = Z::from(i64::MAX);

        // unsigned
        let _ = Z::from(u8::MAX);
        let _ = Z::from(u16::MAX);
        let _ = Z::from(u32::MAX);
        let _ = Z::from(u64::MAX);
    }

    // Ensure that the [From] trait is available for singed and unsigned integers
    // of 8, 16, 32, and 64 bit length. Tested with their minimum value.
    #[test]
    fn from_trait_min() {
        // signed
        let _ = Z::from(i8::MIN);
        let _ = Z::from(i16::MIN);
        let _ = Z::from(i32::MIN);
        let _ = Z::from(i64::MIN);

        // unsigned
        let _ = Z::from(u8::MIN);
        let _ = Z::from(u16::MIN);
        let _ = Z::from(u32::MIN);
        let _ = Z::from(u64::MIN);
    }
}

#[cfg(test)]
mod tests_from_str {
    use std::str::FromStr;

    use crate::integer::Z;

    // Ensure that initialization with large numbers works.
    #[test]
    fn max_int_positive() {
        assert!(Z::from_str(&(i64::MAX).to_string()).is_ok());
    }

    // Ensure that initialization with large numbers (larger than i64) works.
    #[test]
    fn big_positive() {
        assert!(Z::from_str(&"1".repeat(65)).is_ok());
    }

    // Ensure that initialization with large negative numbers works.
    #[test]
    fn max_int_negative() {
        assert!(Z::from_str(&(i64::MIN).to_string()).is_ok());
    }

    // Ensure that initialization with large negative numbers (larger than i64) works.
    #[test]
    fn big_negative() {
        let mut s = "-".to_string();
        s.push_str(&"1".repeat(65));

        assert!(Z::from_str(&s).is_ok());
    }

    // Ensure that wrong initialization yields an Error.
    #[test]
    fn error_wrong_letters() {
        assert!(Z::from_str("hbrkt35itu3gg").is_err());
    }

    // Ensure that wrong initialization yields an Error.
    #[test]
    fn error_wrong_order() {
        assert!(Z::from_str("3-2").is_err());
    }

    // Ensure that wrong initialization yields an Error.
    #[test]
    fn error_rational() {
        assert!(Z::from_str("876/543").is_err());
    }

    // Ensure that wrong initialization yields an Error.
    #[test]
    fn whitespace_mid() {
        assert!(Z::from_str("876 543").is_err());
    }

    // Ensure that wrong initialization yields an Error.
    #[test]
    fn whitespace_start() {
        assert!(Z::from_str(" 876543").is_err());
    }

    // Ensure that wrong initialization yields an Error.
    #[test]
    fn whitespace_end() {
        assert!(Z::from_str("876543 ").is_err());
    }

    // Ensure that wrong initialization yields an Error.
    #[test]
    fn whitespace_minus() {
        assert!(Z::from_str("- 876543").is_err());
    }
}
