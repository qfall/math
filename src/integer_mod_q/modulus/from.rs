//! Implementations to create a [Modulus] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [From] trait should be implemented.
//!
//! The explicit functions contain the documentation.

use std::{ffi::CString, mem::MaybeUninit, str::FromStr};

use flint_sys::{
    fmpz::{fmpz, fmpz_clear, fmpz_cmp, fmpz_set_str},
    fmpz_mod::{fmpz_mod_ctx, fmpz_mod_ctx_init},
};

use crate::error::MathError;

use super::Modulus;

impl FromStr for Modulus {
    type Err = MathError;

    /// Create a [Modulus] from a string with a decimal number.
    ///
    /// Parameters:
    /// - `s`: the polynomial of form: "[0-9]+" and not all zeros
    /// Returns a [Modulus] or an error, if the provided string was not
    /// formatted correctly.
    ///
    /// # Example
    /// ```rust
    /// use math::integer_mod_q::Modulus;
    /// use std::str::FromStr;
    ///
    /// let modulus = Modulus::from_str("42").unwrap();
    /// ```
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [MathError::InvalidStringToModulusInput] if the provided string was not
    /// formatted correctly, e.g., not a number or not greater zero.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // TODO: first create a Z, and then use the fmpz value from Z
        if s.contains(char::is_whitespace) {
            return Err(MathError::InvalidStringToModulusInput(s.to_owned()));
        }
        let mut modulus_fmpz = fmpz(0);
        let c_string = match CString::new(s) {
            Ok(c_string) => c_string,
            Err(_) => return Err(MathError::InvalidStringToModulusInput(s.to_owned())),
        };
        if -1 == unsafe { fmpz_set_str(&mut modulus_fmpz, c_string.as_ptr(), 10) } {
            // fmpz value does not have to be cleared, since it is only 0, if
            // the set string did not work
            return Err(MathError::InvalidStringToModulusInput(s.to_owned()));
        }

        let modulus = ctx_init(&modulus_fmpz);
        // we have to clear the modulus, since the value is not stored in a [Z]
        unsafe { fmpz_clear(&mut modulus_fmpz) };
        Ok(Self { modulus: modulus? })
    }
}

/// Inititializes the FLINT-context object using a [fmpz]-value as input
///
/// Parameters:
/// - `s`: the value the modulus should have as [fmpz]
/// Returns an inititialized context object [fmpz_mod_ctx] or an error, if the
/// provided value was not greater than zero.
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [MathError::InvalidIntToModulus]
/// if the provided value is not greater than 0.
fn ctx_init(n: &fmpz) -> Result<fmpz_mod_ctx, MathError> {
    if unsafe { fmpz_cmp(n, &fmpz(0)) <= 0 } {
        // TODO: include the string representation of the input value in the error
        return Err(MathError::InvalidIntToModulus(
            ".The provided value was not greater than 0".to_owned(),
        ));
    }
    let mut ctx = MaybeUninit::uninit();
    unsafe {
        fmpz_mod_ctx_init(ctx.as_mut_ptr(), n);
        Ok(ctx.assume_init())
    }
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use crate::integer_mod_q::modulus::Modulus;

    // tests whether a correctly formatted string outputs an instantiation of a
    // Modulus, i.e. does not return an error
    #[test]
    fn from_str_working_example() {
        assert!(Modulus::from_str("42").is_ok());
    }

    // tests whether a falsely formatted string (wrong whitespaces) returns an
    // error
    #[test]
    fn from_str_false_format_whitespaces() {
        assert!(Modulus::from_str("4 2").is_err());
    }

    // tests whether a falsely formatted string (wrong symbols) returns an error
    #[test]
    fn from_str_false_format_symbols() {
        assert!(Modulus::from_str("b a").is_err());
    }

    // tests whether a false string (negative) returns an error
    #[test]
    fn from_str_false_sign() {
        assert!(Modulus::from_str("-42").is_err());
    }
}
