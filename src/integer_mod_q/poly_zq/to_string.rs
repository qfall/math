//! This module contains all options to convert a modulus of type
//! [`PolyZq`](super::PolyZq) into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use super::PolyZq;
use crate::integer::PolyZ;
use flint_sys::fmpz_mod_poly::fmpz_mod_poly_get_fmpz_poly;
use std::fmt;

impl fmt::Display for PolyZq {
    /// Allows to convert a [`PolyZq`] into a [`String`].
    ///
    /// # Example 1
    /// ```rust
    /// use math::integer_mod_q::PolyZq;
    /// use std::str::FromStr;
    /// use core::fmt;
    ///
    /// let poly = PolyZq::from_str("4  0 1 2 3 mod 5").unwrap();
    /// println!("{}", poly);
    /// ```
    ///
    /// # Example 2
    /// ```rust
    /// use math::integer_mod_q::PolyZq;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyZq::from_str("4  0 1 2 3 mod 5").unwrap();
    /// let poly_string = poly.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // there is no dedicated method to create a string from a fmpz_mod_poly
        // hence we convert it to a fmpz_poly first to use the dedicated method

        let mut poly_z = PolyZ::default();
        unsafe { fmpz_mod_poly_get_fmpz_poly(&mut poly_z.poly, &self.poly, &self.modulus.modulus) };
        write!(f, "{} mod {}", poly_z, self.modulus)
    }
}

#[cfg(test)]
mod test_to_string {

    use super::PolyZq;
    use std::str::FromStr;

    // tests whether a polynomial that is created using a string, returns the
    // same string, when it is converted back to a string
    #[test]
    fn working_keeps_same_string() {
        let cmp_string = "3  1 2 2 mod 5";
        let cmp = PolyZq::from_str(cmp_string).unwrap();

        assert_eq!(cmp_string, cmp.to_string())
    }

    // tests whether a polynomial that is created using a string, returns a
    // string that can be used to create a polynomial
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp_string = "3  1 2 2 mod 5";
        let cmp = PolyZq::from_str(cmp_string).unwrap();

        let cmp_string2 = cmp.to_string();

        assert!(PolyZq::from_str(&cmp_string2).is_ok())
    }

    // test applied modulus if initialized with negative values
    #[test]
    fn initialized_neg() {
        let cmp_string = "3  -1 -2 -3 mod 5";
        let cmp = PolyZq::from_str(cmp_string).unwrap();

        assert_eq!("3  4 3 2 mod 5", cmp.to_string())
    }

    // tests that large entries and large moduli work with to_string()
    #[test]
    fn large_entries_modulus() {
        let cmp_string = format!("3  1 2 {} mod 1{}", u64::MAX, u64::MAX);
        let cmp = PolyZq::from_str(&cmp_string).unwrap();

        assert_eq!(cmp_string, cmp.to_string())
    }
}
