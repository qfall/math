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

    /// testing subtraction for two [`PolyOverZ`]
    #[test]
    fn sub() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = a - b;
        assert!(c == PolyOverZ::from_str("5  0 0 -8 -1 -2").unwrap());
    }

    /// testing subtraction for two borrowed [`PolyOverZ`]
    #[test]
    fn sub_borrow() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = &a - &b;
        assert!(c == PolyOverZ::from_str("5  0 0 -8 -1 -2").unwrap());
    }

    /// testing subtraction for borrowed [`PolyOverZ`] and [`PolyOverZ`]
    #[test]
    fn sub_first_borrowed() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = &a - b;
        assert!(c == PolyOverZ::from_str("5  0 0 -8 -1 -2").unwrap());
    }

    /// testing subtraction for [`PolyOverZ`] and borrowed [`PolyOverZ`]
    #[test]
    fn sub_second_borrowed() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("5  1 2 5 1 2").unwrap();
        let c: PolyOverZ = a - &b;
        assert!(c == PolyOverZ::from_str("5  0 0 -8 -1 -2").unwrap());
    }

    /// testing subtraction with eliminating coefficients
    #[test]
    fn sub_eliminating_coefficients() {
        let a: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b: PolyOverZ = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let c: PolyOverZ = a - b;
        assert!(c == PolyOverZ::from_str("0").unwrap());
    }

    /// testing subtraction for large [`PolyOverZ`]
    #[test]
    fn sub_large_numbers() {
        let a: PolyOverZ =
            PolyOverZ::from_str(&format!("3  {} {} {}", u32::MAX, i32::MIN, i32::MAX)).unwrap();
        let b: PolyOverZ = PolyOverZ::from_str(&format!("2  {} {}", u32::MAX, i32::MAX)).unwrap();
        let c: PolyOverZ = a - b;
        assert!(
            c == PolyOverZ::from_str(&format!(
                "3  0 {} {}",
                i64::from(i32::MIN) * 2 + 1,
                i32::MAX
            ))
            .unwrap()
        );
    }
}
