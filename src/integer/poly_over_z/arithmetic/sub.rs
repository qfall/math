//! Implementation of the [`Sub`] trait for [`PolyOverZ`] values.

use super::super::PolyOverZ;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use flint_sys::fmpz_poly::fmpz_poly_sub;
use std::ops::Sub;

impl Sub for &PolyOverZ {
    type Output = PolyOverZ;
    /// Implements the [`Sub`] trait for two [`PolyOverZ`] values.
    /// [`Sub`] is implemented for any combination of [`PolyOverZ`] and borrowed [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to subtract from `self`
    ///
    /// Returns the result of the subtraction of both polynomials as a [`PolyOverZ`].
    ///
    /// # Example
    /// ```
    /// use math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
    /// let b: PolyOverZ = PolyOverZ::from_str("5  1 2 -3 0 8").unwrap();
    ///
    /// let c: PolyOverZ = &a - &b;
    /// let d: PolyOverZ = a - b;
    /// let e: PolyOverZ = &c - d;
    /// let f: PolyOverZ = c - &e;
    /// ```
    fn sub(self, other: Self) -> Self::Output {
        let mut out = PolyOverZ::default();
        unsafe {
            fmpz_poly_sub(&mut out.poly, &self.poly, &other.poly);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, PolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, PolyOverZ);

#[cfg(test)]
mod test_sub {

    use super::PolyOverZ;
    use std::str::FromStr;

    /// testing subtraction for two PolyOverZ
    #[test]
    fn sub() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = a - b;
        assert!(c == PolyOverZ::from_str("5  0 0 -8 -1 -2").unwrap());
    }

    /// testing subtraction for two borrowed PolyOverZ
    #[test]
    fn sub_borrow() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = &a - &b;
        assert!(c == PolyOverZ::from_str("5  0 0 -8 -1 -2").unwrap());
    }

    /// testing subtraction for borrowed PolyOverZ and PolyOverZ
    #[test]
    fn sub_first_borrowed() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = &a - b;
        assert!(c == PolyOverZ::from_str("5  0 0 -8 -1 -2").unwrap());
    }

    /// testing subtraction for PolyOverZ and borrowed PolyOverZ
    #[test]
    fn sub_second_borrowed() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = a - &b;
        assert!(c == PolyOverZ::from_str("5  0 0 -8 -1 -2").unwrap());
    }

    /// testing subtraction for large numbers
    #[test]
    fn sub_large_numbers() {
        let a: PolyOverZ =
            PolyOverZ::from_str("3  102193948124871021 2782013516264 -31222222222222222").unwrap();
        let b: PolyOverZ =
            PolyOverZ::from_str("5  941237471761627464 -1234910294712742 -3 0 401231240958792")
                .unwrap();
        let c: PolyOverZ = a - b;
        assert!(
            c == PolyOverZ::from_str(
                "5  -839043523636756443 1237692308229006 -31222222222222219 0 -401231240958792"
            )
            .unwrap()
        );
    }
}

