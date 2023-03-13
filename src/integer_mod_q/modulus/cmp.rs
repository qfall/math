//! This module contains implementations of functions
//! important for comparison such as the [`PartialEq`] trait.
//!
//! The explicit functions contain the documentation.

use super::Modulus;

impl PartialEq for Modulus {
    /// Compares the two [`fmpz`](flint_sys::fmpz::fmpz) structs hiding behind the 
    /// given [`Modulus`] instances to check whether the given [`Modulus`] instances 
    /// have the same value.
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

    /// Checks whether two equal, large Moduli created with different constructors are equal
    #[test]
    fn equal_large() {
        let a = Modulus::from_str(&"1".repeat(65)).unwrap();
        let b = Modulus::try_from_z(&Z::from_str(&"1".repeat(65)).unwrap()).unwrap();
        let a_clone = a.clone();

        assert_eq!(a, b);
        assert_eq!(a, a_clone);
        assert_eq!(b, a_clone);
    }

    /// Checks whether two equal, small Moduli created with different constructors are equal
    #[test]
    fn equal_small() {
        let a = Modulus::from_str(&"1").unwrap();
        let b = Modulus::try_from_z(&Z::from_str("1").unwrap()).unwrap();
        let b_clone = b.clone();

        assert_eq!(a, b);
        assert_eq!(b, b_clone);
        assert_eq!(a, b_clone);
    }

    /// Checks whether unequal Moduli are unequal
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
