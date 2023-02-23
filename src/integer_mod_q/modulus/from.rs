//! Implementations of the 'From' trait for [Modulus].
//!
//! This module contains all options to create a modulus of type [Modulus].

use std::{
    ffi::{c_char, CString},
    mem::MaybeUninit,
    str::FromStr,
};

use flint_sys::{
    fmpz::{fmpz, fmpz_cmp, fmpz_init, fmpz_set_str},
    fmpz_mod::{fmpz_mod_ctx, fmpz_mod_ctx_init},
};

use crate::error::MathError;

use super::Modulus;

impl FromStr for Modulus {
    type Err = MathError;

    /// Create a modulus, which corresponds to a positive nonnegative integer
    /// using a string as input.
    ///
    /// Parameters:
    /// - `s`: the polynomial of form: "[1,...,9][0,1,...,9]*"
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
    /// formatted correctly or the value was not greater than 0.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // TODO: first create a Z, and then use the fmpz value from Z
        if s.contains(char::is_whitespace) {
            return Err(MathError::InvalidStringToModulusInput(s.to_owned()));
        }
        let mut modulus_fmpz = MaybeUninit::uninit();
        let c_string = match CString::new(s) {
            Ok(c_string) => c_string,
            Err(_) => return Err(MathError::InvalidStringToModulusInput(s.to_owned())),
        };
        let p: *const c_char = c_string.as_ptr();
        unsafe {
            fmpz_init(modulus_fmpz.as_mut_ptr());
        }
        let mut modulus_fmpz = unsafe { modulus_fmpz.assume_init() };
        if -1 == unsafe { fmpz_set_str(&mut modulus_fmpz, p, 10) } {
            return Err(MathError::InvalidStringToModulusInput(s.to_owned()));
        }

        match ctx_init(modulus_fmpz) {
            Ok(modulus) => Ok(Self { modulus }),
            Err(e) => Err(e),
        }
    }
}

/// Inititializes the FLINT-context object using a [fmpz]-value as input
///
/// Parameters:
/// - `s`: the value the modulus should have as [fmpz]
/// Returns an inititialized context object [fmpz_mod_ctx] or an error, if the
/// provided value was not greater than 0.
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [MathError::InvalidStringToModulusInput]
/// if the provided value is not greater than 0.
fn ctx_init(n: fmpz) -> Result<fmpz_mod_ctx, MathError> {
    if unsafe { fmpz_cmp(&n, &fmpz(0)) <= 0 } {
        return Err(MathError::InvalidStringToModulusInput(
            "(The provided value was not greater than 0)".to_owned(),
        ));
    }
    let mut ctx = MaybeUninit::uninit();
    unsafe {
        fmpz_mod_ctx_init(ctx.as_mut_ptr(), &n);
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
