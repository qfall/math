use std::{ffi::CString, str::FromStr};

use flint_sys::{
    fmpq::{fmpq, fmpq_clear, fmpq_set_str},
    fmpz::fmpz_is_zero,
};

use crate::error::MathError;

use super::Q;

impl FromStr for Q {
    type Err = MathError;

    /// Create a [`Q`] integer from a [`String`]
    /// The format of that string looks like this `-12/53`
    ///
    /// Parameters:
    /// - `s`: the rational value
    ///
    /// Returns a [`Q`] or an error, if the provided string was not formatted
    /// correctly.
    ///
    /// # Example 1:
    /// ```rust
    /// use std::str::FromStr;
    /// use math::rational::Q;
    ///  
    /// let a: Q = "100/3".parse().unwrap();
    /// let b: Q = Q::from_str("100/3").unwrap();
    /// ```
    ///
    /// # Example 2:
    /// ```rust
    /// use std::str::FromStr;
    /// use math::rational::Q;
    ///  
    /// let q: Q = Q::from_str("-10/3").unwrap();
    /// let b: Q = Q::from_str("10/-3").unwrap();
    /// ```
    ///
    /// # Example 3:
    /// ```rust
    /// use std::str::FromStr;
    /// use math::rational::Q;
    ///  
    /// let q: Q = Q::from_str("-10").unwrap();
    /// let b: Q = Q::from_str("10").unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [InvalidStringToQInput](MathError::InvalidStringToQInput)
    /// if the provided string was not formatted correctly.
    fn from_str(s: &str) -> Result<Self, MathError> {
        if s.contains(char::is_whitespace) {
            return Err(MathError::InvalidStringToQInput(s.to_owned()));
        }

        let mut value = fmpq::default();

        let c_string = CString::new(s)?;

        // -1 is returned if the string is an invalid input.
        //
        // Given the documentation `c_string.as_ptr()` is freed once c_string is deallocated
        // 'The pointer will be valid for as long as `self` is'
        // For reading more look at the documentation of `.as_ptr()`.
        //
        // since value is set to `0`, if an error occurs, we do not need to free the allocated space manually
        if -1 == unsafe { fmpq_set_str(&mut value, c_string.as_ptr(), 10) } {
            return Err(MathError::InvalidStringToQInput(s.to_owned()));
        };

        // since `value.num` is not set to `0`, if an error occurs, we do need to free the allocated space manually
        match unsafe { fmpz_is_zero(&value.den) } {
            0 => Ok(Q { value }),
            _ => {
                unsafe {
                    fmpq_clear(&mut value);
                }
                Err(MathError::InvalidStringToQInput(s.to_owned()))
            }
        }
    }
}

#[cfg(test)]
mod tests_from_str {
    use std::str::FromStr;

    use crate::rational::Q;

    // Ensure that initialization with large numbers works.
    #[test]
    fn max_int_positive() {
        let mut s1 = (i64::MAX).to_string();
        s1.push('/');
        s1.push_str(&(i64::MAX).to_string());

        let mut s2 = ("1/").to_string();
        s2.push_str(&(i64::MAX).to_string());

        assert!(Q::from_str(&(i64::MAX).to_string()).is_ok());
        assert!(Q::from_str(&s1).is_ok());
        assert!(Q::from_str(&s2).is_ok());
    }

    // Ensure that initialization with large numbers (larger than i64) works.
    #[test]
    fn big_positive() {
        let mut s1 = "1".repeat(65);
        s1.push('/');
        s1.push_str(&"1".repeat(65));

        let mut s2 = ("1/").to_string();
        s2.push_str(&"1".repeat(65));

        assert!(Q::from_str(&"1".repeat(65)).is_ok());
        assert!(Q::from_str(&s1).is_ok());
        assert!(Q::from_str(&s2).is_ok());
    }

    // Ensure that initialization with large negative numbers works.
    #[test]
    fn max_int_negative() {
        let mut s1 = (i64::MIN).to_string();
        s1.push('/');
        s1.push_str(&(i64::MIN).to_string());

        let mut s2 = ("1/").to_string();
        s2.push_str(&(i64::MIN).to_string());

        assert!(Q::from_str(&(i64::MIN).to_string()).is_ok());
        assert!(Q::from_str(&s1).is_ok());
        assert!(Q::from_str(&s2).is_ok());
    }

    // Ensure that initialization with large negative numbers (larger than i64) works.
    #[test]
    fn big_negative() {
        let mut s1 = "-".to_string();
        s1.push_str(&"1".repeat(65));
        s1.push('/');
        s1.push_str(&"1".repeat(65));

        let mut s2 = ("-1/").to_string();
        s2.push_str(&"1".repeat(65));

        assert!(Q::from_str(&"1".repeat(65)).is_ok());
        assert!(Q::from_str(&s1).is_ok());
        assert!(Q::from_str(&s2).is_ok());
    }

    // Ensure that wrong initialization yields an Error.
    #[test]
    fn error_wrong_letters() {
        assert!(Q::from_str("hbrkt35itu3gg").is_err());
    }

    // Ensure that wrong initialization yields an Error.
    #[test]
    fn error_wrong_order() {
        assert!(Q::from_str("3/2-").is_err());
    }

    // Ensure that wrong initialization yields an Error.
    #[test]
    fn whitespace_mid() {
        assert!(Q::from_str("876/ 543").is_err());
    }

    // Ensure that wrong initialization yields an Error.
    #[test]
    fn whitespace_start() {
        assert!(Q::from_str(" 876543").is_err());
    }

    // Ensure that wrong initialization yields an Error.
    #[test]
    fn whitespace_end() {
        assert!(Q::from_str("876543 ").is_err());
    }

    // Ensure that wrong initialization yields an Error.
    #[test]
    fn whitespace_minus() {
        assert!(Q::from_str("- 876543").is_err());
    }
}
