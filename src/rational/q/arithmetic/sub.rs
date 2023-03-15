//! Implementation of the [`Sub`] trait for [`Q`] values.

use flint_sys::fmpq::fmpq_sub;
use std::ops::Sub;

use super::super::Q;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};

impl Sub for &Q {
    type Output = Q;
    /// Implements the [`Sub`] trait for two [`Q`] values.
    /// [`Sub`] is implemented for any combination of [`Q`] and borrowed [`Q`].
    ///
    /// Parameters:
    ///  - `other`: specifies the value to subtract from `self`
    ///
    /// Returns the result of the subtraction as a [`Q`].
    ///
    /// # Example
    /// ```rust
    /// use math::rational::Q;
    /// use std::str::FromStr;
    ///
    /// let a: Q = Q::from_str("42").unwrap();
    /// let b: Q = Q::from_str("-42/2").unwrap();
    ///
    /// let c: Q = &a - &b;
    /// let d: Q = a - b;
    /// let e: Q = &c - d;
    /// let f: Q = c - &e;
    /// ```
    fn sub(self, other: Self) -> Self::Output {
        let mut out = Q::default();
        unsafe {
            fmpq_sub(&mut out.value, &self.value, &other.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Sub, sub, Q);
arithmetic_trait_mixed_borrowed_owned!(Sub, sub, Q);

#[cfg(test)]
mod test_sub {
    use std::str::FromStr;

    use super::Q;

    /// testing subtraction for two Q
    #[test]
    fn sub() {
        let a: Q = Q::from_str("42").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = a - b;
        assert!(c == Q::from_str("21").unwrap());
    }

    /// testing subtraction for two borrowed Q
    #[test]
    fn sub_borrow() {
        let a: Q = Q::from_str("42").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = &a - &b;
        assert!(c == Q::from_str("21").unwrap());
    }

    /// testing subtraction for borrowed Q and Q
    #[test]
    fn sub_first_borrowed() {
        let a: Q = Q::from_str("42/5").unwrap();
        let b: Q = Q::from_str("42/10").unwrap();
        let c: Q = &a - b;
        assert!(c == Q::from_str("21/5").unwrap());
    }

    /// testing subtraction for Q and borrowed Q
    #[test]
    fn sub_second_borrowed() {
        let a: Q = Q::from_str("42").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = a - &b;
        assert!(c == Q::from_str("21").unwrap());
    }

    #[test]
    /// testing subtraction for large numerators and divisors
    fn add_large() {
        let a: Q = Q::from_str(&(i64::MAX).to_string()).unwrap();
        let b: Q = Q::from_str(&(u64::MAX - 1).to_string()).unwrap();
        let c: Q = Q::from_str(&format!("1/{}", (i64::MAX))).unwrap();
        let d: Q = Q::from_str(&format!("1/{}", (u64::MAX))).unwrap();
        let e: Q = &b - &a;
        let f: Q = &c - &d;
        assert!(e == a);
        assert!(
            f == Q::from_str(&format!("-1/{}", (u64::MAX))).unwrap()
                + Q::from_str(&format!("1/{}", (i64::MAX))).unwrap()
        );
    }
}
