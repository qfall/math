// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Add`] trait for [`Zq`] values.

use super::super::Zq;
use crate::{
    error::MathError,
    integer::Z,
    macros::arithmetics::{
        arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    },
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
    /// use qfall_math::integer_mod_q::Zq;
    ///
    /// let a: Zq = Zq::try_from((23, 42)).unwrap();
    /// let b: Zq = Zq::try_from((1, 42)).unwrap();
    ///
    /// let c: Zq = &a + &b;
    /// let d: Zq = a + b;
    /// let e: Zq = &c + d;
    /// let f: Zq = c + &e;
    /// ```
    ///
    /// # Panics ...
    /// - ... if the moduli of both [`Zq`] mismatch.
    fn add(self, other: Self) -> Self::Output {
        self.add_safe(other).unwrap()
    }
}

impl Zq {
    /// Implements addition for two [`Zq`] values.
    ///
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`Zq`] or an error if the modulus
    /// does mismatch.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    ///
    /// let a: Zq = Zq::try_from((23, 42)).unwrap();
    /// let b: Zq = Zq::try_from((1, 42)).unwrap();
    ///
    /// let c: Zq = a.add_safe(&b).unwrap();
    /// ```
    /// # Errors
    /// Returns a [`MathError`] of type [`MathError::MismatchingModulus`] if the moduli of
    /// both [`Zq`] mismatch.
    pub fn add_safe(&self, other: &Self) -> Result<Zq, MathError> {
        if self.modulus != other.modulus {
            return Err(MathError::MismatchingModulus(format!(
                " Tried to add '{}' and '{}'.
            If the modulus should be ignored please convert into a Z beforehand.",
                self, other
            )));
        }
        let mut out = Zq::from_z_modulus(&Z::from(1), &self.modulus);
        unsafe {
            fmpz_mod_add(
                &mut out.value.value,
                &self.value.value,
                &other.value.value,
                &*self.modulus.modulus,
            );
        }
        Ok(out)
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, Zq, Zq, Zq);
arithmetic_trait_mixed_borrowed_owned!(Add, add, Zq, Zq, Zq);

#[cfg(test)]
mod test_add {

    use super::Zq;

    /// testing addition for two [`Zq`]
    #[test]
    fn add() {
        let a: Zq = Zq::try_from((11, 17)).unwrap();
        let b: Zq = Zq::try_from((12, 17)).unwrap();
        let c: Zq = a + b;
        assert_eq!(c, Zq::try_from((6, 17)).unwrap());
    }

    /// testing addition for two borrowed [`Zq`]
    #[test]
    fn add_borrow() {
        let a: Zq = Zq::try_from((10, 11)).unwrap();
        let b: Zq = Zq::try_from((1, 11)).unwrap();
        let c: Zq = &a + &b;
        assert_eq!(c, Zq::try_from((0, 11)).unwrap());
    }

    /// testing addition for borrowed [`Zq`] and [`Zq`]
    #[test]
    fn add_first_borrowed() {
        let a: Zq = Zq::try_from((2, 11)).unwrap();
        let b: Zq = Zq::try_from((5, 11)).unwrap();
        let c: Zq = &a + b;
        assert_eq!(c, Zq::try_from((7, 11)).unwrap());
    }

    /// testing addition for [`Zq`] and borrowed [`Zq`]
    #[test]
    fn add_second_borrowed() {
        let a: Zq = Zq::try_from((12, 11)).unwrap();
        let b: Zq = Zq::try_from((10, 11)).unwrap();
        let c: Zq = a + &b;
        assert_eq!(c, Zq::try_from((0, 11)).unwrap());
    }

    /// testing addition for big [`Zq`]
    #[test]
    fn add_large_numbers() {
        let a: Zq = Zq::try_from((u32::MAX, u32::MAX - 58)).unwrap();
        let b: Zq = Zq::try_from((i32::MAX, u32::MAX - 58)).unwrap();
        let c: Zq = a + b;
        assert_eq!(
            c,
            Zq::try_from(((u32::MAX - 1) / 2 + 58, u32::MAX - 58)).unwrap()
        );
    }

    /// testing addition for [`Zq`] with different moduli does not work
    #[test]
    #[should_panic]
    fn add_mismatching_modulus() {
        let a: Zq = Zq::try_from((4, 11)).unwrap();
        let b: Zq = Zq::try_from((1, 3)).unwrap();
        let _c: Zq = a + b;
    }

    /// testing whether add_safe throws an error for mismatching moduli
    #[test]
    fn add_safe_is_err() {
        let a: Zq = Zq::try_from((4, 11)).unwrap();
        let b: Zq = Zq::try_from((1, 3)).unwrap();
        assert!(&a.add_safe(&b).is_err());
    }
}
