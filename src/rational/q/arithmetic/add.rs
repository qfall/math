//! Implementation of the [`Add`] trait for [`Q`] values.

use flint_sys::fmpq::fmpq_add;
use std::ops::Add;

use super::super::Q;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};

impl Add for &Q {
    type Output = Q;

    /// Implements the [`Add`] trait for two [`Q`] values.
    /// [`Add`] is implemented for any combination of [`Q`] and borrowed [`Q`].
    ///
    /// Parameters:
    ///  - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`Q`].
    ///
    /// # Example
    /// ```
    /// use math::rational::Q;
    /// use std::str::FromStr;
    ///
    /// let a: Q = Q::from_str("42").unwrap();
    /// let b: Q = Q::from_str("-42/2").unwrap();
    ///
    /// let c: Q = &a + &b;
    /// let d: Q = a + b;
    /// let e: Q = &c + d;
    /// let f: Q = c + &e;
    /// ```
    fn add(self, other: Self) -> Self::Output {
        let mut out = Q::default();
        unsafe {
            fmpq_add(&mut out.value, &self.value, &other.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, Q);
arithmetic_trait_mixed_borrowed_owned!(Add, add, Q);

#[cfg(test)]
mod test_add {
    use std::str::FromStr;

    use super::Q;

    // testing addition for two Q
    #[test]
    fn add() {
        let a: Q = Q::from_str("42").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = a + b;
        //assert!(c == Q::from_str("63").unwrap());    todo
    }

    // testing addition for two borrowed Q
    #[test]
    fn add_borrow() {
        let a: Q = Q::from_str("42").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = &a + &b;
        //assert!(c == Q::from_str("63").unwrap());    todo
    }

    // testing addition for borrowed Q and Q
    #[test]
    fn add_first_borrowed() {
        let a: Q = Q::from_str("42/5").unwrap();
        let b: Q = Q::from_str("42/10").unwrap();
        let c: Q = &a + b;
        //assert!(c == Q::from_str("63/5").unwrap());    todo
    }

    // testing addition for Q and borrowed Q
    #[test]
    fn add_second_borrowed() {
        let a: Q = Q::from_str("42").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = a + &b;
        //assert!(c == Q::from_str("63").unwrap());    todo
    }

    #[test]
    // testing addition for large numerators and divisors
    fn add_large() {
        //todo
    }
}
