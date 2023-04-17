// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module provides an implementation of the [`Pow`] trait for [`Z`].

use crate::{
    error::MathError,
    integer::Z,
    macros::for_others::{implement_for_others, implement_for_owned},
    traits::Pow,
};
use flint_sys::fmpz::fmpz_pow_fmpz;

impl Pow<&Z> for Z {
    type Output = Z;

    /// Raises the value of `self` to the power of an integer `exp`.
    ///
    /// Parameters:
    /// - `exp`: specifies the exponent to which the value is raised
    ///
    /// Returns the value of `self` powered by `exp` as a new [`Z`] instance.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::traits::*;
    ///
    /// let base = Z::from(9);
    /// let exp = Z::from(3);
    ///
    /// let powered_value = base.pow(&exp).unwrap();
    ///
    /// assert_eq!(Z::from(729), powered_value);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidExponent`](MathError::InvalidExponent)
    /// if the provided exponent is negative and the base value of `self` is not invertible.
    fn pow(&self, exp: &Z) -> Result<Self::Output, MathError> {
        let mut out = Z::ZERO;
        if exp < &Z::ZERO {
            return Err(MathError::InvalidExponent(format!(
                "A negative exponent {} was used for the integer value {}. 
                If you want to get the inverse as a rational object in return use `.inv().pow({})`",
                exp,
                self,
                -1 * exp
            )));
        }
        unsafe { fmpz_pow_fmpz(&mut out.value, &self.value, &exp.value) };
        Ok(out)
    }
}

implement_for_owned!(Z, Z, Pow);
implement_for_others!(Z, Z, Pow for u8 u16 u32 u64 i8 i16 i32 i64);

#[cfg(test)]
mod test_pow {
    use super::*;

    /// Ensure that `pow` works for [`Z`] properly for small and zero values
    #[test]
    fn small() {
        let base = Z::from(2);
        let exp_pos = Z::from(4);
        let zero = Z::ZERO;

        let res_0 = base.pow(&exp_pos).unwrap();
        let res_1 = base.pow(&zero).unwrap();
        let res_2 = zero.pow(&zero).unwrap();
        let res_3 = zero.pow(&exp_pos).unwrap();

        assert_eq!(Z::from(16), res_0);
        assert_eq!(Z::from(1), res_1);
        assert_eq!(Z::ONE, res_2);
        assert_eq!(Z::ZERO, res_3);
    }

    /// Ensure that `pow` works for [`Z`] properly for large values
    #[test]
    fn large() {
        let base = Z::from(i64::MIN);
        let exp_pos = Z::from(3);
        let zero = Z::ZERO;
        let cmp = &base * &base * &base;

        let res_0 = base.pow(&exp_pos).unwrap();
        let res_1 = base.pow(&zero).unwrap();

        assert_eq!(cmp, res_0);
        assert_eq!(Z::ONE, res_1);
    }

    /// Ensures that the `pow` trait is available for other types
    #[test]
    fn availability() {
        let base = Z::from(i64::MAX);
        let exp = Z::from(4);

        let _ = base.pow(exp);
        let _ = base.pow(2_i8);
        let _ = base.pow(2_i16);
        let _ = base.pow(2_i32);
        let _ = base.pow(2_i64);
        let _ = base.pow(2_u8);
        let _ = base.pow(2_u16);
        let _ = base.pow(2_u32);
        let _ = base.pow(2_u64);
    }

    /// Ensures that `pow` returns an error if a non-invertible basis is
    /// powered by a negative exponent
    #[test]
    fn non_invertible_detection() {
        let base_0 = Z::from(4);
        let base_1 = Z::from(u64::MAX);

        assert!(base_0.pow(-1).is_err());
        assert!(base_1.pow(-1).is_err());
    }
}
