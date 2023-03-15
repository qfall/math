//! Implementation of the [`Div`] trait for [`Q`] values.

use super::super::Q;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use flint_sys::fmpq::fmpq_div;
use std::ops::Div;

impl Div for &Q {
    type Output = Q;
    /// Implements the [`Div`] trait for two [`Q`] values.
    /// [`Div`] is implemented for any combination of [`Q`] and borrowed [`Q`].
    ///
    /// Parameters:
    /// - `other`: specifies the value `self` is divided by.
    ///
    /// Returns the result ot the division as a [`Q`].
    ///
    /// # Example
    /// ```
    /// use math::rational::Q;
    /// use std::str::FromStr;
    ///
    /// let a: Q = Q::from_str("42").unwrap();
    /// let b: Q = Q::from_str("24").unwrap();
    ///
    /// let c: Q = &a / &b;
    /// let d: Q = a / b;
    /// let e: Q = &c / d;
    /// let f: Q = c / &e;
    /// ```
    fn div(self, other: Self) -> Self::Output {
        let mut out = Q::default();
        unsafe {
            fmpq_div(&mut out.value, &self.value, &other.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Div, div, Q);
arithmetic_trait_mixed_borrowed_owned!(Div, div, Q);

#[cfg(test)]
mod test_div {
    use std::str::FromStr;

    use super::Q;

    /// testing division for two Q
    #[test]
    fn add() {
        let a: Q = Q::from_str("2").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = a / b;
        assert!(c == Q::from_str("4/42").unwrap());
    }

    /// testing division for two borrowed Q
    #[test]
    fn add_borrow() {
        let a: Q = Q::from_str("2").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = &a / &b;
        assert!(c == Q::from_str("4/42").unwrap());
    }

    /// testing division for borrowed Q and Q
    #[test]
    fn add_first_borrowed() {
        let a: Q = Q::from_str("4").unwrap();
        let b: Q = Q::from_str("42/10").unwrap();
        let c: Q = &a / b;
        assert!(c == Q::from_str("40/42").unwrap());
    }

    /// testing division for Q and borrowed Q
    #[test]
    fn add_second_borrowed() {
        let a: Q = Q::from_str("2").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = a / &b;
        assert!(c == Q::from_str("4/42").unwrap());
    }

    #[test]
    /// testing division for large numerators and divisors
    fn add_large() {
        let a: Q = Q::from_str(&(u64::MAX - 1).to_string()).unwrap();
        let b: Q = Q::from_str("2").unwrap();
        let c: Q = Q::from_str(&format!("1/{}", (i32::MAX))).unwrap();
        let d: Q = Q::from_str(&format!("1/{}", (u32::MAX))).unwrap();
        let e: Q = &a / &b;
        let f: Q = c / d;
        assert!(e == Q::from_str(&(i64::MAX).to_string()).unwrap());
        assert!(
            f == Q::from_str(&format!(
                "{}/{}",
                u64::from(u32::MAX),
                u64::from((u32::MAX - 1) / 2)
            ))
            .unwrap()
        );
    }
}
