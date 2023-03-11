//! Implementation of the [`Mul`] trait for [`Z`] values.

use super::super::Z;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use flint_sys::fmpz::{fmpz, fmpz_mul};
use std::ops::Mul;

impl Mul for &Z {
    type Output = Z;
    /// Implements the [`Mul`] trait for two [`Z`] values.
    /// [`Mul`] is implemented for any combination of [`Z`] and borrowed [`Z`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of both numbers as a [`Z`].
    ///
    /// # Example\n
    /// ```rust
    /// use math::integer::Z;
    ///
    /// let a: Z = Z::from(42);
    /// let b: Z = Z::from(24);
    ///
    /// let c: Z = &a * &b;
    /// let d: Z = a * b;
    /// let e: Z = &c * d;
    /// let f: Z = c * &e;
    /// ```
    fn mul(self, other: Self) -> Self::Output {
        let mut out = Z::default();
        unsafe {
            fmpz_mul(&mut out.value, &self.value, &other.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Mul, mul, Z);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Z);

#[cfg(test)]
mod test_mul {

    use super::Z;

    /// testing multiplication for two [`Z`]
    #[test]
    fn mul() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(4);
        let c: Z = a * b;
        assert!(c == Z::from(168));
    }

    /// testing multiplication for two borrowed Z
    #[test]
    fn mul_borrow() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(4);
        let c: Z = &a * &b;
        assert!(c == Z::from(168));
    }

    /// testing multiplication for borrowed Z and Z
    #[test]
    fn mul_first_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(4);
        let c: Z = &a * b;
        assert!(c == Z::from(168));
    }

    /// testing multiplication for Z and borrowed Z
    #[test]
    fn mul_second_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(4);
        let c: Z = a * &b;
        assert!(c == Z::from(168));
    }

    /// testing multiplication for big numbers
    #[test]
    fn mul_large_numbers() {
        let a: Z = Z::from(i64::MAX);
        let b: Z = Z::from(2);
        let c: Z = Z::from(i32::MIN);
        let d: Z = Z::from(i32::MAX);
        let e: Z = a * b;
        let f: Z = c * d;
        assert!(e == Z::from(u64::MAX - 1));
        assert!(f == Z::from(i64::from(i32::MAX) * i64::from(i32::MIN)));
    }
}
