//! Implementations to create a [`ModulusPolynomialRingZq`] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//!
//! The explicit functions contain the documentation.

use super::ModulusPolynomialRingZq;
use crate::{error::MathError, integer_mod_q::PolyOverZq};
use flint_sys::fq::fq_ctx_init_modulus;
use std::{ffi::CString, mem::MaybeUninit, rc::Rc, str::FromStr};

impl TryFrom<&PolyOverZq> for ModulusPolynomialRingZq {
    type Error = MathError;
    /// Create a new Modulus object of type [`ModulusPolynomialRingZq`]
    /// for [`PolynomialRingZq`](crate::integer_mod_q::PolynomialRingZq)
    ///
    /// Note: The modulus must be prime.
    ///
    /// Parameters:
    /// - `modulus_poly`: the polynomial which is used as the modulus
    ///
    /// Returns the new modulus object.
    ///
    /// # Example
    /// ```
    /// use math::integer_mod_q::ModulusPolynomialRingZq;
    /// use math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// // initialize X^2 + 1 mod 17, i.e. a polynomial with prime modulus
    /// let poly_mod = PolyOverZq::from_str("3  1 0 1 mod 17").unwrap();
    /// let modulus = ModulusPolynomialRingZq::from(&poly_mod);
    /// ```
    fn try_from(modulus_poly: &PolyOverZq) -> Result<Self, MathError> {
        if !modulus_poly.modulus.is_prime() {
            return Err(MathError::DivisionByZeroError("".to_owned()));
        }
        let mut modulus = MaybeUninit::uninit();
        let c_string = CString::new("X").unwrap();
        unsafe {
            fq_ctx_init_modulus(
                modulus.as_mut_ptr(),
                &modulus_poly.poly,
                modulus_poly.modulus.get_fmpz_mod_ctx_struct(),
                c_string.as_ptr(),
            );
            Ok(Self {
                modulus: Rc::new(modulus.assume_init()),
            })
        }
    }
}

impl FromStr for ModulusPolynomialRingZq {
    type Err = MathError;

    /// Creating a Modulus object of type [`ModulusPolynomialRingZq`]
    /// for [`PolynomialRingZq`](crate::integer_mod_q::PolynomialRingZq). This first
    /// converts the provided string into a [`PolyOverZq`] and then into the Modulus object.
    ///
    /// Note: The modulus must be prime.
    ///
    /// Parameters:
    /// - `s`: has to be a valid string to create a [`PolyOverZq`] see [`PolyOverZq::from_str`]
    ///
    /// Returns a [`ModulusPolynomialRingZq`] or an error, if the provided string was not
    /// formatted correctly.
    ///
    /// # Example
    /// ```rust
    /// use math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// // initialize X^2 + 1 mod 17, i.e. an irreducible polynomial with prime modulus
    /// let poly_mod = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
    /// ```
    /// # Errors and Failures
    /// - Throws a [`MathError`]. For further details see Errors and Failures of [`PolyOverZq::from_str`]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        ModulusPolynomialRingZq::try_from(&PolyOverZq::from_str(s)?)
    }
}

/// most tests with specific values are covered in [`PolyOverZq`](crate::integer_mod_q::PolyOverZq)
/// since the format is reused, we omit some tests
#[cfg(test)]
mod test_try_from_poly_zq {
    use crate::{integer_mod_q::ModulusPolynomialRingZq, integer_mod_q::PolyOverZq};
    use std::str::FromStr;

    /// ensure that we have a basic working example
    #[test]
    fn working_example() {
        let poly_mod = PolyOverZq::from_str("3  4 0 1 mod 17").unwrap();
        let _ = ModulusPolynomialRingZq::try_from(&poly_mod).unwrap();
    }

    /// ensure that it works with large coefficients
    #[test]
    fn working_large_entries() {
        let poly_mod =
            PolyOverZq::from_str(&format!("4  0 1 -2 {} mod {}", u64::MAX, 2_i32.pow(16) + 1))
                .unwrap();
        let _ = ModulusPolynomialRingZq::try_from(&poly_mod).unwrap();
    }

    /// ensure that large entries work
    #[test]
    fn poly_zq_unchanged() {
        let in_str = format!("4  0 1 3 {} mod {}", u64::MAX, 2_i32.pow(16) + 1);
        let cmp_str = "3  0 1 3 mod 65537";
        let poly_zq = PolyOverZq::from_str(&in_str).unwrap();
        let _ = ModulusPolynomialRingZq::try_from(&poly_zq).unwrap();
        assert_eq!(cmp_str, poly_zq.to_string())
    }

    /// ensure that non-primes yields an error
    #[test]
    fn poly_zq_non_prime() {
        let in_str = format!("4  0 1 3 {} mod {}", u64::MAX, 2_i32.pow(16));
        let poly_zq = PolyOverZq::from_str(&in_str).unwrap();
        assert!(ModulusPolynomialRingZq::try_from(&poly_zq).is_err())
    }
}

/// most tests with specific values are covered in [`PolyOverZq`](crate::integer_mod_q::PolyOverZq)
/// since the format is reused, we omit some tests
#[cfg(test)]
mod test_from_str {
    use crate::integer_mod_q::ModulusPolynomialRingZq;
    use std::str::FromStr;

    /// ensure that we have a basic working example
    #[test]
    fn working_example() {
        let poly = ModulusPolynomialRingZq::from_str("3  4 0 1 mod 17");
        assert!(poly.is_ok())
    }

    /// ensure that at input of a wrong format an error is returned
    #[test]
    fn wrong_modulus_fmt() {
        assert!(ModulusPolynomialRingZq::from_str("3  4 0 1 mod -17").is_err());
        assert!(ModulusPolynomialRingZq::from_str("3  4 0 1 mod 17 mod 42").is_err());
        assert!(ModulusPolynomialRingZq::from_str("3  4 0 1 mod 0").is_err());
        assert!(ModulusPolynomialRingZq::from_str("3  4 0 1 mod 1 7").is_err());
        assert!(ModulusPolynomialRingZq::from_str("3  4 0 1 mod ba").is_err());
    }

    /// ensure that large coefficients work
    #[test]
    fn working_large_entries() {
        assert!(ModulusPolynomialRingZq::from_str(&format!(
            "4  0 1 3 {} mod {}",
            u64::MAX,
            2_i32.pow(16) + 1
        ))
        .is_ok());
    }

    /// ensure that non-primes yields an error
    #[test]
    fn poly_zq_non_prime() {
        assert!(ModulusPolynomialRingZq::from_str(&format!(
            "4  0 1 3 {} mod {}",
            u64::MAX,
            2_i32.pow(16)
        ))
        .is_err())
    }
}
