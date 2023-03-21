//! Implementation of the [`Add`] trait for [`Zq`] values.

use super::super::Zq;
use crate::{macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
}, integer::Z};
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
    /// let a: Zq = Zq::try_from((23, 42));
    /// let b: Zq = Zq::try_from((1, 42));
    ///
    /// let c: Zq = &a + &b;
    /// let d: Zq = a + b;
    /// let e: Zq = &c + d;
    /// let f: Zq = c + &e;
    /// ```
    fn add(self, other: Self) -> Self::Output {
        //todo error
        let mut out = Zq::from_z_modulus(&Z::from(1), &self.modulus);
        unsafe {
            fmpz_mod_add(&mut out.value.value, &self.value.value, &other.value.value, &*self.modulus.modulus);
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
        let a: Zq = Zq::try_from((0, 17)).unwrap();
        let b: Zq = Zq::try_from((0, 17)).unwrap();
        let c: Zq = a + b;
        assert!(c == Zq::try_from((0, 17)).unwrap());
    }

    /// testing addition for two borrowed Zq
    #[test]
    fn add_borrow() {
        let a: Zq = Zq::try_from((0, 1)).unwrap();
        let b: Zq = Zq::try_from((0, 1)).unwrap();
        let c: Zq = &a + &b;
        assert!(c == Zq::try_from((0, 1)).unwrap());
    }

    /// testing addition for borrowed Zq and Zq
    #[test]
    fn add_first_borrowed() {
        let a: Zq = Zq::try_from((0, 1)).unwrap();
        let b: Zq = Zq::try_from((0, 1)).unwrap();
        let c: Zq = &a + b;
        assert!(c == Zq::try_from((0, 1)).unwrap());
    }

    /// testing addition for Zq and borrowed Zq
    #[test]
    fn add_second_borrowed() {
        let a: Zq = Zq::try_from((0, 1)).unwrap();
        let b: Zq = Zq::try_from((0, 1)).unwrap();
        let c: Zq = a + &b;
        assert!(c == Zq::try_from((0, 1)).unwrap());
    }

    /// testing addition for big numbers
    #[test]
    fn add_large_numbers() {
        let a: Zq = Zq::try_from((0, 1)).unwrap();
        let b: Zq = Zq::try_from((0, 1)).unwrap();
        let c: Zq = Zq::try_from((0, 1)).unwrap();
        let d: Zq = &a + b;
        let e: Zq = a + c;
        assert!(d == Zq::try_from((0, 1)).unwrap());
        assert!(e == Zq::try_from((0, 1)).unwrap());
    }
}
