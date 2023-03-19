//! Implementation of the [`Mul`] trait for [`Q`] values.

use super::super::Q;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned
};
use flint_sys::fmpq::fmpq_mul;
use std::ops::Mul;

impl Mul for &Q {
    type Output = Q;
    /// Implements the [`Mul`] trait for two [`Q`] values.
    /// [`Mul`] is implemented for any combination of [`Q`] and borrowed [`Q`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of both numbers as a [`Q`].
    ///
    /// # Example
    /// ```
    /// use math::rational::Q;
    /// use std::str::FromStr;
    ///
    /// let a: Q = Q::from_str("42").unwrap();
    /// let b: Q = Q::from_str("24").unwrap();
    ///
    /// let c: Q = &a * &b;
    /// let d: Q = a * b;
    /// let e: Q = &c * d;
    /// let f: Q = c * &e;
    /// ```
    fn mul(self, other: Self) -> Self::Output {
        let mut out = Q::default();
        unsafe {
            fmpq_mul(&mut out.value, &self.value, &other.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Mul, mul, Q);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Q);

#[cfg(test)]
mod test_mul {
    use super::Q;
    use std::str::FromStr;

    /// testing multiplication for two [`Q`]
    #[test]
    fn mul() {
        let a: Q = Q::from_str("2").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = a * b;
        assert!(c == Q::from_str("42").unwrap());
    }

    /// testing multiplication for two borrowed [`Q`]
    #[test]
    fn mul_borrow() {
        let a: Q = Q::from_str("2").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = &a * &b;
        assert!(c == Q::from_str("42").unwrap());
    }

    /// testing multiplication for borrowed [`Q`] and [`Q`]
    #[test]
    fn mul_first_borrowed() {
        let a: Q = Q::from_str("4").unwrap();
        let b: Q = Q::from_str("42/10").unwrap();
        let c: Q = &a * b;
        assert!(c == Q::from_str("168/10").unwrap());
    }

    /// testing multiplication for [`Q`] and borrowed [`Q`]
    #[test]
    fn mul_second_borrowed() {
        let a: Q = Q::from_str("2").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = a * &b;
        assert!(c == Q::from_str("42").unwrap());
    }

    #[test]
    /// testing multiplication for large numerators and divisors
    fn mul_large() {
        let a: Q = Q::from_str(&(i64::MAX).to_string()).unwrap();
        let b: Q = Q::from_str("2").unwrap();
        let c: Q = Q::from_str(&format!("1/{}", (i32::MAX))).unwrap();
        let d: Q = Q::from_str(&format!("1/{}", (u32::MAX))).unwrap();
        let e: Q = &a * &b;
        let f: Q = c * d;
        assert!(e == Q::from_str(&(u64::MAX - 1).to_string()).unwrap());
        assert!(
            f == Q::from_str(&format!(
                "1/{}",
                u64::from(u32::MAX) * u64::from((u32::MAX - 1) / 2)
            ))
            .unwrap()
        );
    }
}
