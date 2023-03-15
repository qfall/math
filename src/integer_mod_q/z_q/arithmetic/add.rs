//! Implementation of the [`Add`] trait for [`Zq`] values.

use super::super::Zq;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use flint_sys::fmpz_mod::fmpz_mod_add;
use std::ops::Add;

impl Add for &Zq {
    type Output = Zq;
    /// Implements the [`Add`] trait for two [`Zq`] values.
    /// [`Add`] is implemented for any combination of [`Zq`] and borrowed [`Zq`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`Zq`].
    ///
    /// # Example
    /// ```
    /// use math::integer_mod_q::Zq;
    ///
    /// let a: Zq = Zq::from(42);
    /// let b: Zq = Zq::from(24);
    ///
    /// let c: Zq = &a + &b;
    /// let d: Zq = a + b;
    /// let e: Zq = &c + d;
    /// let f: Zq = c + &e;
    /// ```
    fn add(self, other: Self) -> Self::Output {
        //todo error
        let mut out = Zq::try_from((0, 1)).unwrap();
        unsafe {
            fmpz_mod_add(&mut out.value, &self.value, &other.value, &*self.modulus.modulus);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, Zq);
arithmetic_trait_mixed_borrowed_owned!(Add, add, Zq);

#[cfg(test)]
mod test_add {

    use super::Zq;

    /// testing addition for two Zq
    #[test]
    fn add() {
        let a: Zq = Zq::from(42);
        let b: Zq = Zq::from(24);
        let c: Zq = a + b;
        assert!(c == Zq::from(66));
    }

    /// testing addition for two borrowed Zq
    #[test]
    fn add_borrow() {
        let a: Zq = Zq::from(42);
        let b: Zq = Zq::from(24);
        let c: Zq = &a + &b;
        assert!(c == Zq::from(66));
    }

    /// testing addition for borrowed Zq and Zq
    #[test]
    fn add_first_borrowed() {
        let a: Zq = Zq::from(42);
        let b: Zq = Zq::from(24);
        let c: Zq = &a + b;
        assert!(c == Zq::from(66));
    }

    /// testing addition for Zq and borrowed Zq
    #[test]
    fn add_second_borrowed() {
        let a: Zq = Zq::from(42);
        let b: Zq = Zq::from(24);
        let c: Zq = a + &b;
        assert!(c == Zq::from(66));
    }

    /// testing addition for big numbers
    #[test]
    fn add_large_numbers() {
        let a: Zq = Zq::from(u64::MAX);
        let b: Zq = Zq::from(-221319874);
        let c: Zq = Zq::from(i64::MIN);
        let d: Zq = &a + b;
        let e: Zq = a + c;
        assert!(d == Zq::from(u64::MAX - 221319874));
        assert!(e == Zq::from(i64::MAX));
    }
}
