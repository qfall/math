//! Implementations to create a [`ModulusPolynomialRingZq`] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//!
//! The explicit functions contain the documentation.

use super::ModulusPolynomialRingZq;
use crate::{error::MathError, integer_mod_q::PolyOverZq};
use flint_sys::fq::fq_ctx_init_modulus;
use std::{ffi::CString, mem::MaybeUninit, str::FromStr};

impl From<&PolyOverZq> for ModulusPolynomialRingZq {
    // TODO: Add check for irreducible and prime?
    // irreducible: fmpz_mod_poly_is_irreducible can be called
    // prime: fmpz_is_prime
    /// Create a new Modulus object of type [`ModulusPolynomialRingZq`]
    /// for [`PolynomialRingZq`](crate::finite_fields::PolynomialRingZq)
    ///
    /// Note that this function does not check whether the modulus is irreducible over Fq and whether q is prime.
    ///
    /// Parameters:
    /// - `modulus_poly`: the polynomial which is used as the modulus
    ///
    /// Returns the new modulus object.
    ///
    /// # Example
    /// ```rust
    /// use math::finite_fields::ModulusPolynomialRingZq;
    /// use math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// // initialize X^2 + 1 mod 17, i.e. an irreducible polynomial with prime modulus
    /// let poly_mod = PolyOverZq::from_str("3  1 0 1 mod 17").unwrap();
    /// let modulus = ModulusPolynomialRingZq::from(&poly_mod);
    /// ```
    fn from(modulus_poly: &PolyOverZq) -> Self {
        let mut modulus = MaybeUninit::uninit();
        let c_string = CString::new("X").unwrap();
        unsafe {
            fq_ctx_init_modulus(
                modulus.as_mut_ptr(),
                &modulus_poly.poly,
                &modulus_poly.modulus.modulus,
                c_string.as_ptr(),
            );

            Self {
                modulus: modulus.assume_init(),
            }
        }
    }
}

impl FromStr for ModulusPolynomialRingZq {
    type Err = MathError;

    // TODO: Add check for irreducible and prime?
    // irreducible: fmpz_mod_poly_is_irreducible can be called
    // prime: fmpz_is_prime
    /// Creating a Modulus object of type [`ModulusPolynomialRingZq`]
    /// for [`PolynomialRingZq`](crate::finite_fields::PolynomialRingZq). This first
    /// converts the provided string into a [`PolyOverZq`] and then into the Modulus object.
    ///
    /// Note that this function does not check whether the modulus is irreducible over Fq and whether q is prime.
    ///
    /// Parameters:
    /// - `s`: has to be a valid string to create a [`PolyOverZq`] see [`PolyOverZq::from_str`]
    ///
    /// Returns a [`ModulusPolynomialRingZq`] or an error, if the provided string was not
    /// formatted correctly.
    ///
    /// # Example
    /// ```rust
    /// use math::finite_fields::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// // initialize X^2 + 1 mod 17, i.e. an irreducible polynomial with prime modulus
    /// let poly_mod = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
    /// ```
    /// # Errors and Failures
    /// - Throws a [`MathError`]. For further details see Errors and Failures of [`PolyOverZq::from_str`]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(ModulusPolynomialRingZq::from(&PolyOverZq::from_str(s)?))
    }
}

/// most tests with specific values are covered in [`PolyOverZq`](crate::integer_mod_q::PolyOverZq)
/// since the format is reused, we omit some tests
#[cfg(test)]
mod test_from_poly_zq {
    use crate::{finite_fields::ModulusPolynomialRingZq, integer_mod_q::PolyOverZq};
    use std::str::FromStr;

    /// ensure that we have a basic working example
    #[test]
    fn working_example() {
        let poly_mod = PolyOverZq::from_str("3  4 0 1 mod 17").unwrap();
        let _ = ModulusPolynomialRingZq::from(&poly_mod);
    }

    /// ensure that it works with large integers
    #[test]
    fn working_large_entries() {
        let poly_mod =
            PolyOverZq::from_str(&format!("4  0 1 -2 {} mod {}", u64::MAX, 2_i32.pow(16) + 1))
                .unwrap();
        let _ = ModulusPolynomialRingZq::from(&poly_mod);
    }

    /// ensure that large entries work
    #[test]
    fn poly_zq_unchanged() {
        let in_str = format!("4  0 1 3 {} mod {}", u64::MAX, 2_i32.pow(16) + 1);
        let cmp_str = "3  0 1 3 mod 65537";
        let poly_zq = PolyOverZq::from_str(&in_str).unwrap();
        let _ = ModulusPolynomialRingZq::from(&poly_zq);
        assert_eq!(cmp_str, poly_zq.to_string())
    }
}

/// most tests with specific values are covered in [`PolyOverZq`](crate::integer_mod_q::PolyOverZq)
/// since the format is reused, we omit some tests
#[cfg(test)]
mod test_from_str {
    use crate::finite_fields::ModulusPolynomialRingZq;
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

    /// ensure that large entries work
    #[test]
    fn working_large_entries() {
        assert!(ModulusPolynomialRingZq::from_str(&format!(
            "4  0 1 3 {} mod {}",
            u64::MAX,
            2_i32.pow(16) + 1
        ))
        .is_ok());
    }
}
