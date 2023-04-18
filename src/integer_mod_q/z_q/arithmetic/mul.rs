// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Mul`] trait for [`Zq`] values.

use super::super::Zq;
use crate::{
    error::MathError,
    integer::Z,
    macros::arithmetics::{
        arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    },
};
use flint_sys::fmpz_mod::fmpz_mod_mul;
use std::ops::Mul;

impl Mul for &Zq {
    type Output = Zq;
    /// Implements the [`Mul`] trait for two [`Zq`] values.
    /// [`Mul`] is implemented for any combination of [`Zq`] and borrowed [`Zq`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of both numbers as a [`Zq`].
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    ///
    /// let a: Zq = Zq::try_from((23, 42)).unwrap();
    /// let b: Zq = Zq::try_from((1, 42)).unwrap();
    ///
    /// let c: Zq = &a * &b;
    /// let d: Zq = a * b;
    /// let e: Zq = &c * d;
    /// let f: Zq = c * &e;
    /// ```
    ///
    /// # Panics
    /// - Panics if the moduli of both [`Zq`] mismatch.
    fn mul(self, other: Self) -> Self::Output {
        self.mul_safe(other).unwrap()
    }
}

impl Zq {
    /// Implements multiplication for two [`Zq`] values.
    ///
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of both numbers as a [`Zq`] or an error if the moduli
    /// mismatch.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    ///
    /// let a: Zq = Zq::try_from((23, 42)).unwrap();
    /// let b: Zq = Zq::try_from((1, 42)).unwrap();
    ///
    /// let c: Zq = a.mul_safe(&b).unwrap();
    /// ```
    /// # Errors
    /// Returns a [`MathError`] of type [`MathError::MismatchingModulus`] if the moduli of
    /// both [`Zq`] mismatch.
    pub fn mul_safe(&self, other: &Self) -> Result<Zq, MathError> {
        if self.modulus != other.modulus {
            return Err(MathError::MismatchingModulus(format!(
                " Tried to multiply '{}' and '{}'.
            If the modulus should be ignored please convert into a Z beforehand.",
                self, other
            )));
        }
        let mut out = Zq::from_z_modulus(&Z::from(1), &self.modulus);
        unsafe {
            fmpz_mod_mul(
                &mut out.value.value,
                &self.value.value,
                &other.value.value,
                &*self.modulus.modulus,
            );
        }
        Ok(out)
    }
}

arithmetic_trait_borrowed_to_owned!(Mul, mul, Zq, Zq, Zq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Zq, Zq, Zq);

#[cfg(test)]
mod test_mul {

    use super::Zq;

    /// testing multiplication for two [`Zq`]
    #[test]
    fn mul() {
        let a: Zq = Zq::try_from((11, 17)).unwrap();
        let b: Zq = Zq::try_from((12, 17)).unwrap();
        let c: Zq = a * b;
        assert_eq!(c, Zq::try_from((13, 17)).unwrap());
    }

    /// testing multiplication for two borrowed [`Zq`]
    #[test]
    fn mul_borrow() {
        let a: Zq = Zq::try_from((10, 11)).unwrap();
        let b: Zq = Zq::try_from((1, 11)).unwrap();
        let c: Zq = &a * &b;
        assert_eq!(c, Zq::try_from((10, 11)).unwrap());
    }

    /// testing multiplication for borrowed [`Zq`] and [`Zq`]
    #[test]
    fn mul_first_borrowed() {
        let a: Zq = Zq::try_from((2, 11)).unwrap();
        let b: Zq = Zq::try_from((5, 11)).unwrap();
        let c: Zq = &a * b;
        assert_eq!(c, Zq::try_from((10, 11)).unwrap());
    }

    /// testing multiplication for [`Zq`] and borrowed [`Zq`]
    #[test]
    fn mul_second_borrowed() {
        let a: Zq = Zq::try_from((12, 11)).unwrap();
        let b: Zq = Zq::try_from((10, 11)).unwrap();
        let c: Zq = a * &b;
        assert_eq!(c, Zq::try_from((-1, 11)).unwrap());
    }

    /// testing multiplication for big [`Zq`]
    #[test]
    fn mul_large_numbers() {
        let a: Zq = Zq::try_from((u32::MAX, u32::MAX - 58)).unwrap();
        let b: Zq = Zq::try_from((i32::MAX, u32::MAX - 58)).unwrap();
        let c: Zq = a * b;
        assert_eq!(
            c,
            Zq::try_from((u64::from((u32::MAX - 1) / 2) * 58, u32::MAX - 58)).unwrap()
        );
    }

    /// testing multiplication for [`Zq`] with different moduli does not work
    #[test]
    #[should_panic]
    fn mul_mismatching_modulus() {
        let a: Zq = Zq::try_from((4, 11)).unwrap();
        let b: Zq = Zq::try_from((1, 3)).unwrap();
        let _c: Zq = a * b;
    }

    /// testing whether mul_safe throws an error for mismatching moduli
    #[test]
    fn mul_safe_is_err() {
        let a: Zq = Zq::try_from((4, 11)).unwrap();
        let b: Zq = Zq::try_from((1, 3)).unwrap();
        assert!(&a.mul_safe(&b).is_err());
    }
}
