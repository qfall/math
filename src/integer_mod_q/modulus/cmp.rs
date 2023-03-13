//! This module contains implementations of functions
//! important for comparison such as the [`PartialEq`] trait.
//!
//! The explicit functions contain the documentation.

use super::Modulus;

impl PartialEq for Modulus {
    /// Compares the two given [`fmpz`](flint_sys::fmpz::fmpz) structs
    /// to check whether the given [`Modulus`] instances have the same value.
    ///
    /// Parameters:
    /// - `other`: holds another [`Modulus`] object which `self` is compared to
    ///
    /// # Example
    /// ```
    /// use math::integer_mod_q::Modulus;
    /// use std::str::FromStr;
    ///
    /// let a = Modulus::from_str("3").unwrap();
    /// let b = Modulus::from_str("3").unwrap();
    /// let c = Modulus::from_str("4").unwrap();
    ///
    /// assert_eq!(a, b);
    /// assert_ne!(a, c);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            1 == flint_sys::fmpz::fmpz_equal(
                &self.get_fmpz_mod_ctx_struct().to_owned().n[0],
                &other.get_fmpz_mod_ctx_struct().to_owned().n[0],
            )
        }
    }
}

#[cfg(test)]
mod test_eq {
    use super::Modulus;
    use crate::integer::Z;
    use std::str::FromStr;

    #[test]
    fn equal_large() {
        let a = Modulus::from_str(&"1".repeat(65)).unwrap();
        let b = Modulus::try_from_z(&Z::from_str(&"1".repeat(65)).unwrap()).unwrap();

        assert_eq!(a, b);
    }

    #[test]
    fn equal_small() {
        let a = Modulus::from_str(&"1").unwrap();
        let b = Modulus::try_from_z(&Z::from_str("1").unwrap()).unwrap();

        assert_eq!(a, b);
    }

    #[test]
    fn unequal() {
        let one = Modulus::from_str(&"1").unwrap();
        let two = Modulus::from_str(&"2").unwrap();
        let big = Modulus::from_str(&"1".repeat(65)).unwrap();

        assert_ne!(one, two);
        assert_ne!(one, big);
        assert_ne!(two, big);
    }
}
