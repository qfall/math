//! Implementations to create a [`Modulus`] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//!
//! The explicit functions contain the documentation.

use super::Modulus;
use crate::{error::MathError, integer::Z};
use flint_sys::{
    fmpz::{fmpz, fmpz_clear, fmpz_cmp, fmpz_set_str},
    fmpz_mod::{fmpz_mod_ctx, fmpz_mod_ctx_init},
};
use std::{ffi::CString, mem::MaybeUninit, rc::Rc, str::FromStr};

impl Modulus {
    /// Create a [`Modulus`] from [`Z`].
    ///
    /// Parameters:
    /// - `value`: the value of the modulus
    ///
    /// Returns a [`Modulus`] or a [`MathError`]
    ///
    /// # Example
    /// ```
    /// use math::integer_mod_q::Modulus;
    /// use std::str::FromStr;
    ///
    /// let modulus = Modulus::from_str("42").unwrap();
    /// ```
    /// # Errors and Failures
    ///
    /// - Returns a [`MathError`] of type [`InvalidIntToModulus`](MathError::InvalidIntToModulus)
    /// if the provided value is not greater than zero.
    pub fn try_from_z(value: &Z) -> Result<Self, MathError> {
        let modulus = ctx_init(&value.value);
        Ok(Self {
            modulus: Rc::new(modulus?),
        })
    }
}

// TODO: write macro to generate [`TryFrom`] trait.
impl TryFrom<&Z> for Modulus {
    type Error = MathError;
    /// Create [`Modulus`] from [`Z`] reference using [`try_from_z`](Modulus::try_from_z)
    fn try_from(value: &Z) -> Result<Self, Self::Error> {
        Modulus::try_from_z(value)
    }
}

impl FromStr for Modulus {
    type Err = MathError;

    /// Create a [`Modulus`] from a string with a decimal number.
    ///
    /// Parameters:
    /// - `s`: the modulus of form: "[0-9]+" and not all zeros
    ///
    /// Returns a [`Modulus`] or an [`MathError`], if the provided string is not
    /// a valid modulus.
    ///
    /// # Example
    /// ```
    /// use math::integer_mod_q::Modulus;
    /// use std::str::FromStr;
    ///
    /// let modulus = Modulus::from_str("42").unwrap();
    /// ```
    /// # Errors and Failures
    ///
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToModulusInput`](MathError::InvalidStringToModulusInput) if the provided string was not
    /// formatted correctly, e.g., not a number or not greater zero.
    /// - Returns a [`MathError`] of type [`InvalidIntToModulus`](MathError::InvalidIntToModulus)
    /// if the provided value is not greater than zero.
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
            // `modulus_fmpz` stays 0, if the set string did not work. Therefore, FLINT
            // is not using pointers here and  explicitly freeing it is not necessary.
            return Err(MathError::InvalidStringToModulusInput(s.to_owned()));
        }

        let modulus = ctx_init(&modulus_fmpz);
        // we have to clear the modulus, since the value is not stored in a [Z]
        unsafe { fmpz_clear(&mut modulus_fmpz) };
        Ok(Self {
            modulus: Rc::new(modulus?),
        })
    }
}

/// Initializes the FLINT-context object using a [`fmpz`]-value as input
///
/// Parameters:
/// - `s`: the value the modulus should have as [`fmpz`]
///
/// Returns an initialized context object [`fmpz_mod_ctx`] or an error, if the
/// provided value was not greater than zero.
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`InvalidIntToModulus`](MathError::InvalidIntToModulus)
/// if the provided value is not greater than zero.
fn ctx_init(n: &fmpz) -> Result<fmpz_mod_ctx, MathError> {
    if unsafe { fmpz_cmp(n, &fmpz(0)) <= 0 } {
        // TODO: include the string representation of the input value in the error
        return Err(MathError::InvalidIntToModulus(
            ".The provided value was not greater than zero".to_owned(),
        ));
    }
    let mut ctx = MaybeUninit::uninit();
    unsafe {
        fmpz_mod_ctx_init(ctx.as_mut_ptr(), n);
        Ok(ctx.assume_init())
    }
}

#[cfg(test)]
mod test_try_from_z {
    use super::Modulus;
    use crate::integer::Z;

    /// Demonstrate different ways to create a [`Modulus`] from a [`Z`] reference.
    #[test]
    fn z_to_modulus_reference() {
        let value = Z::from(10);

        let _: Modulus = (&value).try_into().unwrap();
        let _: Modulus = <&Z>::try_into(&value).unwrap();
        assert!(Modulus::try_from_z(&value).is_ok());
        assert!(Modulus::try_from(&value).is_ok());
    }

    /// Test [`Modulus`] creation with small positive [`Z`] (valid).
    #[test]
    fn z_valid_small() {
        let z = Z::from(10);

        assert!(Modulus::try_from_z(&z).is_ok());
    }

    /// Test [`Modulus`] creation with large [`Z`] (valid).
    /// (uses FLINT's pointer representation)
    #[test]
    fn z_valid_large() {
        let z = Z::from(u64::MAX);

        assert!(Modulus::try_from_z(&z).is_ok());
    }

    /// Test [`Modulus`] creation with small negative [`Z`] (invalid).
    #[test]
    fn z_negative_small() {
        let z = Z::from(-10);

        assert!(Modulus::try_from_z(&z).is_err());
    }

    /// Test [`Modulus`] creation with large negative [`Z`] (invalid).
    /// (uses FLINT's pointer representation)
    #[test]
    fn z_negative_large() {
        let z = Z::from(i64::MIN);

        assert!(Modulus::try_from_z(&z).is_err());
    }
}

#[cfg(test)]
mod test_ctx_init {
    use std::ffi::CString;

    use flint_sys::{
        fmpz::{fmpz, fmpz_clear, fmpz_set_str},
        fmpz_mod::fmpz_mod_ctx_clear,
    };

    use super::ctx_init;

    /// tests whether a small modulus ist instantiated correctly
    #[test]
    fn working_example() {
        // fmpz(100) does not have to be manually cleared, since it is smaller
        // than 62 bits
        assert!(ctx_init(&fmpz(100)).is_ok())
    }

    /// tests whether a large modulus (> 64 bits) is instantiated correctly
    #[test]
    fn large_modulus() {
        let mut value = fmpz(0);
        let c_string = CString::new("1".repeat(65)).unwrap();
        unsafe {
            fmpz_set_str(&mut value, c_string.as_ptr(), 10);
        }

        let ctx = ctx_init(&value);

        assert!(ctx.is_ok());

        // now we have to clear ctx and value
        unsafe {
            fmpz_clear(&mut value);
            fmpz_mod_ctx_clear(&mut ctx.unwrap());
        }
    }

    /// tests whether a negative input value returns an error
    #[test]
    fn negative_modulus() {
        // fmpz(-42) does not have to be manually cleared, since it is smaller
        // than 62 bits
        assert!(ctx_init(&fmpz(-42)).is_err())
    }

    /// tests whether a zero as input value returns an error
    #[test]
    fn zero_modulus() {
        // fmpz(0) does not have to be manually cleared, since it is smaller
        // than 62 bits
        assert!(ctx_init(&fmpz(0)).is_err())
    }
}

#[cfg(test)]
mod test_from_str {

    use super::Modulus;
    use std::str::FromStr;

    /// tests whether a correctly formatted string outputs an instantiation of a
    /// Modulus, i.e. does not return an error
    #[test]
    fn working_example() {
        assert!(Modulus::from_str("42").is_ok());
    }

    /// tests whether a large value (> 64 bits) is instantiated correctly
    #[test]
    fn large_value() {
        assert!(Modulus::from_str(&"1".repeat(65)).is_ok())
    }

    /// tests whether a falsely formatted string (wrong whitespaces) returns an
    /// error
    #[test]
    fn false_format_whitespaces() {
        assert!(Modulus::from_str("4 2").is_err());
    }

    /// tests whether a falsely formatted string (wrong symbols) returns an error
    #[test]
    fn false_format_symbols() {
        assert!(Modulus::from_str("b a").is_err());
    }

    /// tests whether a false string (negative) returns an error
    #[test]
    fn false_sign() {
        assert!(Modulus::from_str("-42").is_err());
    }
}
