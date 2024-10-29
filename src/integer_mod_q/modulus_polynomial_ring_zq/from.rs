// Copyright © 2023 Marcel Luca Schmidt, Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`ModulusPolynomialRingZq`] value from other types.
//!
//! The explicit functions contain the documentation.

use super::ModulusPolynomialRingZq;
use crate::{
    error::MathError,
    integer::{PolyOverZ, Z},
    integer_mod_q::{Modulus, PolyOverZq, Zq},
    macros::for_others::implement_for_owned,
};
use flint_sys::fq::fq_ctx_init_modulus;
use std::{ffi::CString, mem::MaybeUninit, rc::Rc, str::FromStr};

impl From<&Zq> for ModulusPolynomialRingZq {
    /// Creates a constant [`ModulusPolynomialRingZq`], i.e. the polynomial `x mod q`,
    /// where `x` is the value of the given [`Zq`] value and `q` its modulus.
    ///
    /// Parameters:
    /// - `value`: the constant value the polynomial will have.
    ///   
    /// Returns a new constant [`ModulusPolynomialRingZq`] with the specified
    /// `value` and `modulus` of the [`Zq`] value.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer_mod_q::*, traits::*};
    ///
    /// let zq = Zq::from((2, 10));
    ///
    /// let mod_poly = ModulusPolynomialRingZq::from(&zq);
    /// ```
    fn from(value: &Zq) -> Self {
        let poly_zq = PolyOverZq::from(value);

        Self::from(poly_zq)
    }
}

implement_for_owned!(Zq, ModulusPolynomialRingZq, From);

impl<Mod: Into<Modulus>> From<(&PolyOverZ, Mod)> for ModulusPolynomialRingZq {
    /// Creates a [`ModulusPolynomialRingZq`] from a [`PolyOverZ`] and a value that implements [`Into<Modulus>`].
    ///
    /// Parameters:
    /// - `poly`: the coefficients of the polynomial.
    /// - `modulus`: the modulus by which each entry is reduced.
    ///
    /// Returns a new [`ModulusPolynomialRingZq`] with the coefficients from the
    /// [`PolyOverZ`] instance under the specified [`Modulus`] value.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{ModulusPolynomialRingZq, Modulus};
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZ::from_str("4  0 1 102 3").unwrap();
    ///
    /// let mod_poly = ModulusPolynomialRingZq::from((&poly, 100));
    ///
    /// let poly_cmp = ModulusPolynomialRingZq::from_str("4  0 1 2 3 mod 100").unwrap();
    /// assert_eq!(poly_cmp, mod_poly);
    /// ```
    ///
    /// # Panics ...
    /// - if `modulus` is smaller than `2`, or
    /// - if the modulus polynomial is `0`.
    fn from((poly, modulus): (&PolyOverZ, Mod)) -> Self {
        let poly_zq = PolyOverZq::from((poly, modulus));

        check_poly_mod(&poly_zq).unwrap();

        Self::from(poly_zq)
    }
}

impl<Mod: Into<Modulus>> From<(PolyOverZ, Mod)> for ModulusPolynomialRingZq {
    /// Creates a [`ModulusPolynomialRingZq`] from a [`PolyOverZ`] and a value that implements [`Into<Modulus>`].
    ///
    /// Parameters:
    /// - `poly`: the coefficients of the polynomial.
    /// - `modulus`: the modulus by which each entry is reduced.
    ///
    /// Returns a new [`ModulusPolynomialRingZq`] with the coefficients from the
    /// [`PolyOverZ`] instance under the specified [`Modulus`] value.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZ::from_str("4  0 1 102 3").unwrap();
    ///
    /// let mod_poly = ModulusPolynomialRingZq::from((poly, 100));
    ///
    /// let poly_cmp = ModulusPolynomialRingZq::from_str("4  0 1 2 3 mod 100").unwrap();
    /// assert_eq!(poly_cmp, mod_poly);
    /// ```
    ///
    /// # Panics ...
    /// - if `modulus` is smaller than `2`, or
    /// - if the modulus polynomial is `0`.
    fn from((poly, modulus): (PolyOverZ, Mod)) -> Self {
        let poly_zq = PolyOverZq::from((poly, modulus));

        check_poly_mod(&poly_zq).unwrap();

        Self::from(poly_zq)
    }
}

impl<Integer: Into<Z>, Mod: Into<Modulus>> From<(Integer, Mod)> for ModulusPolynomialRingZq {
    /// Creates a [`ModulusPolynomialRingZq`] from any values that implement [`Into<Z>`] and [`Into<Modulus>`],
    /// where the second value must be larger than `1`.
    ///
    /// Parameters:
    /// - `z`: the single, constant coefficient of the polynomial.
    /// - `modulus`: the modulus by which each entry is reduced.
    ///
    /// Returns a new constant [`ModulusPolynomialRingZq`] with the specified `z` and `modulus` value.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let mod_poly = PolyOverZq::from((5, 42));
    ///
    /// let poly_cmp = PolyOverZq::from_str("1  5 mod 42").unwrap();
    /// assert_eq!(poly_cmp, mod_poly);
    /// ```
    ///
    /// # Panics ...
    /// - if `modulus` is smaller than `2`, or
    /// - if the modulus polynomial is `0`.
    fn from((z, modulus): (Integer, Mod)) -> Self {
        let poly_zq = PolyOverZq::from((z, modulus));

        check_poly_mod(&poly_zq).unwrap();

        Self::from(poly_zq)
    }
}

impl From<&PolyOverZq> for ModulusPolynomialRingZq {
    /// Creates a Modulus object of type [`ModulusPolynomialRingZq`]
    /// for [`PolynomialRingZq`](crate::integer_mod_q::PolynomialRingZq)
    ///
    /// Parameters:
    /// - `poly`: the polynomial which is used as the modulus.
    ///
    /// Returns a new [`ModulusPolynomialRingZq`] object with the coefficients
    /// and modulus from the [`PolyOverZq`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZq::from_str("3  1 0 1 mod 17").unwrap();
    /// let mod_poly = ModulusPolynomialRingZq::try_from(&poly).unwrap();
    /// ```
    ///
    /// # Panics ...
    /// - if `modulus` is smaller than `2`, or
    /// - if the modulus polynomial is `0`.
    fn from(poly: &PolyOverZq) -> Self {
        check_poly_mod(poly).unwrap();

        let mut modulus = MaybeUninit::uninit();
        let c_string = CString::new("X").unwrap();
        unsafe {
            fq_ctx_init_modulus(
                modulus.as_mut_ptr(),
                &poly.poly,
                poly.modulus.get_fmpz_mod_ctx_struct(),
                c_string.as_ptr(),
            );
            Self {
                modulus: Rc::new(modulus.assume_init()),
            }
        }
    }
}

implement_for_owned!(PolyOverZq, ModulusPolynomialRingZq, From);

impl From<&ModulusPolynomialRingZq> for ModulusPolynomialRingZq {
    // Only the smart pointer is increased here.

    /// Alias for [`ModulusPolynomialRingZq::clone`].
    fn from(value: &ModulusPolynomialRingZq) -> Self {
        value.clone()
    }
}

impl FromStr for ModulusPolynomialRingZq {
    type Err = MathError;

    /// Creates a Modulus object of type [`ModulusPolynomialRingZq`]
    /// for [`PolynomialRingZq`](crate::integer_mod_q::PolynomialRingZq). This first
    /// converts the provided string into a [`PolyOverZq`] and then into the Modulus object.
    ///
    /// **Warning**: If the input string starts with a correctly formatted
    /// [`PolyOverZ`](crate::integer::PolyOverZ) object, the rest of the string
    /// until the `"mod"` is ignored. This means that the input string
    /// `"4  0 1 2 3 mod 13"` is the same as `"4  0 1 2 3 4 5 6 7 mod 13"`.
    ///
    /// Parameters:
    /// - `s`: has to be a valid string to create a [`PolyOverZq`].
    ///     For further information see [`PolyOverZq::from_str`].
    ///
    /// Returns a [`ModulusPolynomialRingZq`] or an error if the provided string was not
    /// formatted correctly or the modulus was smaller than `2`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let poly_mod = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
    /// ```
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///     [`StringConversionError`](MathError::StringConversionError)
    ///     - if the provided first half of the string was not formatted correctly to
    ///         create a [`PolyOverZ`],
    ///     - if the provided second half of the
    ///         string was not formatted correctly to create a [`Modulus`],
    ///     - if the number of coefficients was smaller than the number provided
    ///         at the start of the provided string, or
    ///     - if the provided value did not contain two whitespaces.
    ///     - For further information see [`PolyOverZq::from_str`].
    /// - Returns a [`MathError`] of type
    ///     [`InvalidModulus`](MathError::InvalidModulus)
    ///     - if `modulus` is smaller than `2`, or
    ///     - if the modulus polynomial is `0`.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let poly_zq = PolyOverZq::from_str(s)?;

        check_poly_mod(&poly_zq)?;

        Ok(Self::from(poly_zq))
    }
}

/// Checks weather a given [`PolyOverZq`] can be used as a [`ModulusPolynomialRingZq`].
///
/// Parameters:
/// - `poly_zq`: the [`PolyOverZq`] value that should be checked.
///
/// Returns an empty `Ok`, or an [`MathError`] if the polynomial is no valid modulus polynomial.
///
/// # Examples
/// ```compile_fail
/// use qfall_math::integer_mod_q::PolyOverZq;
/// use std::str::FromStr;
///
/// let poly_zq = PolyOverZq::from_str("2  1 2 mod 17").unwrap();
///
/// check_poly_mod(&poly_zq)?
/// ```
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type
///     [`InvalidModulus`](MathError::InvalidModulus)
///     if the modulus polynomial is `0`.
pub(crate) fn check_poly_mod(poly_zq: &PolyOverZq) -> Result<(), MathError> {
    if poly_zq == &PolyOverZq::from((0, &poly_zq.modulus)) {
        return Err(MathError::InvalidModulus(poly_zq.to_string()));
    }

    Ok(())
}

/// Most tests with specific values are covered in [`PolyOverZq`](crate::integer_mod_q::PolyOverZq)
/// since the format is reused, we omit some tests
#[cfg(test)]
mod test_availability {
    use super::*;
    use crate::{integer::Z, integer_mod_q::Zq};
    use crate::{integer_mod_q::ModulusPolynomialRingZq, integer_mod_q::PolyOverZq};
    use std::str::FromStr;

    /// Ensure that the from function can be called with several types.
    #[test]
    fn availability() {
        let z = Z::from(4);
        let modulus = Modulus::from(3);
        let zq = Zq::from((2, 3));
        let poly = PolyOverZ::from_str("2  1 1").unwrap();
        let poly_zq = PolyOverZq::from_str("4  1 0 0 1 mod 17").unwrap();

        let _ = ModulusPolynomialRingZq::from(&zq);
        let _ = ModulusPolynomialRingZq::from(zq.clone());

        let _ = ModulusPolynomialRingZq::from((2, 5));
        let _ = ModulusPolynomialRingZq::from((&z, 5));
        let _ = ModulusPolynomialRingZq::from((z.clone(), 5));
        let _ = ModulusPolynomialRingZq::from((&modulus, 5));
        let _ = ModulusPolynomialRingZq::from((modulus.clone(), 5));
        let _ = ModulusPolynomialRingZq::from((&poly, 5));
        let _ = ModulusPolynomialRingZq::from((poly.clone(), 5));
        let _ = ModulusPolynomialRingZq::from((3, &z));
        let _ = ModulusPolynomialRingZq::from((3, z.clone()));
        let _ = ModulusPolynomialRingZq::from((2, &modulus));
        let _ = ModulusPolynomialRingZq::from((2, modulus));

        let _ = ModulusPolynomialRingZq::from(&poly_zq);
        let _ = ModulusPolynomialRingZq::from(poly_zq);
    }
}

/// Most tests with specific values are covered in [`PolyOverZq`](crate::integer_mod_q::PolyOverZq)
/// since the format is reused, we omit some tests
#[cfg(test)]
mod test_try_from_poly_z {
    use crate::{integer::PolyOverZ, integer_mod_q::ModulusPolynomialRingZq};
    use std::str::FromStr;

    /// Ensure that primes and non-primes work as modulus
    #[test]
    fn poly_z_primes() {
        let poly_z = PolyOverZ::from_str("2  2 2").unwrap();

        let _ = ModulusPolynomialRingZq::from((&poly_z, 10));
        let _ = ModulusPolynomialRingZq::from((poly_z, 11));
    }

    /// Ensure that the function panics if the modulus polynomial is 0
    #[test]
    #[should_panic]
    fn panic_0() {
        let poly = PolyOverZ::from(0);

        let _ = ModulusPolynomialRingZq::from((poly, 17));
    }
}

/// Most tests with specific values are covered in [`PolyOverZq`](crate::integer_mod_q::PolyOverZq)
/// since the format is reused, we omit some tests
#[cfg(test)]
mod test_try_from_integer_mod {
    use crate::integer_mod_q::ModulusPolynomialRingZq;

    /// Ensure that primes and non-primes work as modulus
    #[test]
    fn mod_primes() {
        let _ = ModulusPolynomialRingZq::from((5, 10));
        let _ = ModulusPolynomialRingZq::from((5, 11));
    }

    /// Ensure that the function panics if the modulus polynomial is 0
    #[test]
    #[should_panic]
    fn panic_0() {
        let _ = ModulusPolynomialRingZq::from((0, 17));
    }
}

/// Most tests with specific values are covered in [`PolyOverZq`](crate::integer_mod_q::PolyOverZq)
/// since the format is reused, we omit some tests
#[cfg(test)]
mod test_try_from_poly_zq {
    use crate::{integer_mod_q::ModulusPolynomialRingZq, integer_mod_q::PolyOverZq};
    use std::str::FromStr;

    /// Ensure that it works with large coefficients
    #[test]
    fn working_large_entries() {
        let poly_mod =
            PolyOverZq::from_str(&format!("4  0 1 -2 {} mod {}", u64::MAX, 2_i32.pow(16) + 1))
                .unwrap();
        let _ = ModulusPolynomialRingZq::from(&poly_mod);
    }

    /// Ensure that large entries work
    #[test]
    fn poly_zq_unchanged() {
        let in_str = format!("4  0 1 3 {} mod {}", u64::MAX, 2_i32.pow(16) + 1);
        let cmp_str = "3  0 1 3 mod 65537";
        let poly_zq = PolyOverZq::from_str(&in_str).unwrap();
        let _ = ModulusPolynomialRingZq::from(&poly_zq);
        assert_eq!(cmp_str, poly_zq.to_string());
    }

    /// Ensure that primes and non-primes work as modulus
    #[test]
    fn poly_zq_primes() {
        let poly_zq_1 = PolyOverZq::from_str("2  1 1 mod 10").unwrap();
        let poly_zq_2 = PolyOverZq::from_str("2  1 1 mod 11").unwrap();

        let _ = ModulusPolynomialRingZq::from(poly_zq_1);
        let _ = ModulusPolynomialRingZq::from(poly_zq_2);
    }

    /// Ensure that the function panics if the modulus polynomial is 0
    #[test]
    #[should_panic]
    fn panic_0() {
        let poly = PolyOverZq::from((0, 17));

        let _ = ModulusPolynomialRingZq::from(poly);
    }
}

/// most tests with specific values are covered in [`PolyOverZq`](crate::integer_mod_q::PolyOverZq)
/// since the format is reused, we omit some tests
#[cfg(test)]
mod test_from_str {
    use crate::integer_mod_q::ModulusPolynomialRingZq;
    use std::str::FromStr;

    /// Ensure that at input of a wrong format an error is returned
    #[test]
    fn wrong_modulus_fmt() {
        assert!(ModulusPolynomialRingZq::from_str("3  4 0 1 mod -17").is_err());
        assert!(ModulusPolynomialRingZq::from_str("3  4 0 1 mod 17 mod 42").is_err());
        assert!(ModulusPolynomialRingZq::from_str("3  4 0 1 mod 0").is_err());
        assert!(ModulusPolynomialRingZq::from_str("3  4 0 1 mod 1 7").is_err());
        assert!(ModulusPolynomialRingZq::from_str("3  4 0 1 mod ba").is_err());
    }

    /// Ensure that large coefficients work
    #[test]
    fn working_large_entries() {
        assert!(ModulusPolynomialRingZq::from_str(&format!(
            "4  0 1 3 {} mod {}",
            u64::MAX,
            2_i32.pow(16) + 1
        ))
        .is_ok());
    }

    /// Ensure that primes and non-primes work as modulus
    #[test]
    fn poly_zq_primes() {
        assert!(ModulusPolynomialRingZq::from_str("4  0 1 3 2 mod 10").is_ok());
        assert!(ModulusPolynomialRingZq::from_str("4  0 1 3 2 mod 11").is_ok());
    }
}
