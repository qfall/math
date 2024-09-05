// Copyright © 2023 Marvin Beckmann
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
use crate::{error::MathError, integer_mod_q::PolyOverZq};
use flint_sys::fq::fq_ctx_init_modulus;
use std::{ffi::CString, mem::MaybeUninit, rc::Rc, str::FromStr};

impl From<&PolyOverZq> for ModulusPolynomialRingZq {
    /// Create a new Modulus object of type [`ModulusPolynomialRingZq`]
    /// for [`PolynomialRingZq`](crate::integer_mod_q::PolynomialRingZq)
    ///
    /// Parameters:
    /// - `modulus_poly`: the polynomial which is used as the modulus
    ///
    /// Returns the new modulus object.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let poly_mod = PolyOverZq::from_str("3  1 0 1 mod 17").unwrap();
    /// let modulus = ModulusPolynomialRingZq::try_from(&poly_mod).unwrap();
    /// ```
    fn from(modulus_poly: &PolyOverZq) -> Self {
        let mut modulus = MaybeUninit::uninit();
        let c_string = CString::new("X").unwrap();
        unsafe {
            fq_ctx_init_modulus(
                modulus.as_mut_ptr(),
                &modulus_poly.poly,
                modulus_poly.modulus.get_fmpz_mod_ctx_struct(),
                c_string.as_ptr(),
            );
            Self {
                modulus: Rc::new(modulus.assume_init()),
            }
        }
    }
}

impl From<PolyOverZq> for ModulusPolynomialRingZq {
    /// Create a new Modulus object of type [`ModulusPolynomialRingZq`]
    /// for [`PolynomialRingZq`](crate::integer_mod_q::PolynomialRingZq).
    ///
    /// For extensive documentation see [`ModulusPolynomialRingZq::from`]
    /// (with the reference as parameter).
    fn from(modulus: PolyOverZq) -> Self {
        ModulusPolynomialRingZq::from(&modulus)
    }
}

impl From<&ModulusPolynomialRingZq> for ModulusPolynomialRingZq {
    // Only the smart pointer is increased here.

    /// Alias for [`ModulusPolynomialRingZq::clone`].
    fn from(value: &ModulusPolynomialRingZq) -> Self {
        value.clone()
    }
}

impl FromStr for ModulusPolynomialRingZq {
    type Err = MathError;

    /// Creating a Modulus object of type [`ModulusPolynomialRingZq`]
    /// for [`PolynomialRingZq`](crate::integer_mod_q::PolynomialRingZq). This first
    /// converts the provided string into a [`PolyOverZq`] and then into the Modulus object.
    ///
    /// Parameters:
    /// - `s`: has to be a valid string to create a [`PolyOverZq`] see [`PolyOverZq::from_str`]
    ///
    /// Returns a [`ModulusPolynomialRingZq`] or an error, if the provided string was not
    /// formatted correctly.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let poly_mod = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
    /// ```
    /// # Errors and Failures
    /// - Returns a [`MathError`]. For further details see Errors and Failures of [`PolyOverZq::from_str`]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::from(&PolyOverZq::from_str(s)?))
    }
}

/// most tests with specific values are covered in [`PolyOverZq`](crate::integer_mod_q::PolyOverZq)
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

    /// Ensure that non-primes work
    #[test]
    fn poly_zq_non_prime() {
        let in_str = format!("4  0 1 3 {} mod {}", u64::MAX, 2_i32.pow(16));
        PolyOverZq::from_str(&in_str).unwrap();
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

    /// Ensure that non-primes work
    #[test]
    fn poly_zq_non_prime() {
        assert!(ModulusPolynomialRingZq::from_str(&format!(
            "4  0 1 3 {} mod {}",
            u64::MAX,
            2_i32.pow(16)
        ))
        .is_ok())
    }
}
