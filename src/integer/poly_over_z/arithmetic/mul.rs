//! Implementation of the [`Mul`] trait for [`PolyOverZ`] values.

use super::super::PolyOverZ;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use flint_sys::fmpz_poly::fmpz_poly_mul;
use std::ops::Mul;

impl Mul for &PolyOverZ {
    type Output = PolyOverZ;
    /// Implements the [`Mul`] trait for two [`PolyOverZ`] values.
    /// [`Mul`] is implemented for any combination of [`PolyOverZ`] and borrowed [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of both polynomials as a [`PolyOverZ`].
    ///
    /// # Example
    /// ```
    /// use math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
    /// let b: PolyOverZ = PolyOverZ::from_str("5  1 2 -3 0 8").unwrap();
    ///
    /// let c: PolyOverZ = &a * &b;
    /// let d: PolyOverZ = a * b;
    /// let e: PolyOverZ = &c * d;
    /// let f: PolyOverZ = c * &e;
    /// ```
    fn mul(self, other: Self) -> Self::Output {
        let mut out = PolyOverZ::default();
        unsafe {
            fmpz_poly_mul(&mut out.poly, &self.poly, &other.poly);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Mul, mul, PolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, PolyOverZ);

#[cfg(test)]
mod test_mul {

    use super::PolyOverZ;
    use std::str::FromStr;

    /// testing multiplication for two [`PolyOverZ`]
    #[test]
    fn mul() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = a * b;
        assert!(c == PolyOverZ::from_str("7  1 4 6 5 -11 1 -6").unwrap());
    }

    /// testing multiplication for two borrowed [`PolyOverZ`]
    #[test]
    fn mul_borrow() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = &a * &b;
        assert!(c == PolyOverZ::from_str("7  1 4 6 5 -11 1 -6").unwrap());
    }

    /// testing multiplication for borrowed [`PolyOverZ`] and [`PolyOverZ`]
    #[test]
    fn mul_first_borrowed() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = &a * b;
        assert!(c == PolyOverZ::from_str("7  1 4 6 5 -11 1 -6").unwrap());
    }

    /// testing multiplication for [`PolyOverZ`] and borrowed [`PolyOverZ`]
    #[test]
    fn mul_second_borrowed() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = a * &b;
        assert!(c == PolyOverZ::from_str("7  1 4 6 5 -11 1 -6").unwrap());
    }

    /// testing multiplication for large [`PolyOverZ`]
    #[test]
    fn mul_large_numbers() {
        let a: PolyOverZ = PolyOverZ::from_str("2  102193948124871021 -31222222222222222").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("2  941237471761627464 -1234910294712742").unwrap();
        let c: PolyOverZ = a * b;
        assert!(
            c == PolyOverZ::from_str(
                "3  96188773362392509553720962051320744 -29513725865820889307065724381554590 38556643646031166614464378952724"
            )
            .unwrap()
        );
    }
}
