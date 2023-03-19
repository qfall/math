//! Implementation of the [`Add`] trait for [`PolyOverZ`] values.

use super::super::PolyOverZ;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use flint_sys::fmpz_poly::fmpz_poly_add;
use std::ops::Add;

impl Add for &PolyOverZ {
    type Output = PolyOverZ;
    /// Implements the [`Add`] trait for two [`PolyOverZ`] values.
    /// [`Add`] is implemented for any combination of [`PolyOverZ`] and borrowed [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both polynomials as a [`PolyOverZ`].
    ///
    /// # Example
    /// ```
    /// use math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
    /// let b: PolyOverZ = PolyOverZ::from_str("5  1 2 -3 0 8").unwrap();
    ///
    /// let c: PolyOverZ = &a + &b;
    /// let d: PolyOverZ = a + b;
    /// let e: PolyOverZ = &c + d;
    /// let f: PolyOverZ = c + &e;
    /// ```
    fn add(self, other: Self) -> Self::Output {
        let mut out = PolyOverZ::default();
        unsafe {
            fmpz_poly_add(&mut out.poly, &self.poly, &other.poly);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, PolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Add, add, PolyOverZ);

#[cfg(test)]
mod test_add {

    use super::PolyOverZ;
    use std::str::FromStr;

    /// testing addition for two PolyOverZ
    #[test]
    fn add() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = a + b;
        assert!(c == PolyOverZ::from_str("5  2 4 2 1 2").unwrap());
    }

    /// testing addition for two borrowed PolyOverZ
    #[test]
    fn add_borrow() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = &a + &b;
        assert!(c == PolyOverZ::from_str("5  2 4 2 1 2").unwrap());
    }

    /// testing addition for borrowed PolyOverZ and PolyOverZ
    #[test]
    fn add_first_borrowed() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = &a + b;
        assert!(c == PolyOverZ::from_str("5  2 4 2 1 2").unwrap());
    }

    /// testing addition for PolyOverZ and borrowed PolyOverZ
    #[test]
    fn add_second_borrowed() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = a + &b;
        assert!(c == PolyOverZ::from_str("5  2 4 2 1 2").unwrap());
    }

    /// testing addition for large numbers
    #[test]
    fn add_large_numbers() {
        let a: PolyOverZ =
            PolyOverZ::from_str("3  102193948124871021 2782013516264 -31222222222222222").unwrap();
        let b: PolyOverZ =
            PolyOverZ::from_str("5  941237471761627464 -1234910294712742 -3 0 401231240958792")
                .unwrap();
        let c: PolyOverZ = a + b;
        assert!(
            c == PolyOverZ::from_str(
                "5  1043431419886498485 -1232128281196478 -31222222222222225 0 401231240958792"
            )
            .unwrap()
        );
    }
}
