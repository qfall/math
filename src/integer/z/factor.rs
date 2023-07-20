// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations for Factorizations of [`Z`] values.

use super::Z;
use flint_sys::fmpz_factor::{
    _fmpz_factor_append, fmpz_factor_clear, fmpz_factor_get_fmpz, fmpz_factor_init,
    fmpz_factor_refine, fmpz_factor_struct,
};
use std::{fmt, mem::MaybeUninit};
use string_builder::Builder;

#[derive(Debug)]
pub struct Factorization {
    factors: fmpz_factor_struct,
}

impl fmt::Display for Factorization {
    /// Allows to convert an factorization of type [`Factorization`] into a [`String`].
    ///
    /// Returns the integer in form of a [`String`]. For factorization `2^3 * 5 * 7^2`
    /// the String looks like this `[(2,3),(5,1),(7,2)]`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Factorization;
    /// use qfall_math::integer::Z;
    /// use core::fmt;
    ///
    /// let x = Z::from(1200);
    /// let y = Z::from(20);
    ///
    /// let mut fac = Factorization::from((&x, &y));
    /// fac.refine();
    ///
    /// println!("{}", fac);
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut builder = Builder::default();

        builder.append('[');

        for factor in Vec::<(Z, u64)>::from(self).iter() {
            builder.append(format!("({},{})", factor.0, factor.1));
        }
        builder.append(']');

        write!(
            f,
            "{}",
            builder
                .string()
                .expect("Vector string contains invalid bytes.")
        )
    }
}

impl Drop for Factorization {
    fn drop(&mut self) {
        unsafe { fmpz_factor_clear(&mut self.factors) }
    }
}

impl From<&Z> for Factorization {
    fn from(value: &Z) -> Self {
        let mut out = Self::default();
        unsafe { _fmpz_factor_append(&mut out.factors, &value.value, 2) };
        out
    }
}

impl From<(&Z, &Z)> for Factorization {
    fn from((factor_1, factor_2): (&Z, &Z)) -> Self {
        let mut out = Self::default();
        unsafe { _fmpz_factor_append(&mut out.factors, &factor_1.value, 1) };
        unsafe { _fmpz_factor_append(&mut out.factors, &factor_2.value, 1) };
        out
    }
}

impl Default for Factorization {
    fn default() -> Self {
        let mut factors = MaybeUninit::uninit();

        unsafe {
            fmpz_factor_init(factors.as_mut_ptr());

            Self {
                factors: factors.assume_init(),
            }
        }
    }
}

#[allow(dead_code)]
impl Factorization {
    pub fn refine(&mut self) {
        unsafe { fmpz_factor_refine(&mut self.factors, &self.factors) }
    }
}

impl From<&Factorization> for Vec<(Z, u64)> {
    fn from(factors: &Factorization) -> Self {
        let mut out = Vec::new();
        for i in 0..factors.factors.num {
            let mut factor = Z::default();
            unsafe { fmpz_factor_get_fmpz(&mut factor.value, &factors.factors, i) };

            let exp = unsafe { *factors.factors.exp.offset(i.try_into().unwrap()) };
            out.push((factor, exp));
        }
        out
    }
}

#[cfg(test)]
mod test_factorization {
    use super::{Factorization, Z};

    /// Ensure that factorization works correctly.
    #[test]
    fn equal_call_methods() {
        let x = Z::from(2 * 2 * 3 * 4 * 5 * 5);
        let y = Z::from(2 * 2 * 5);

        let mut fac = Factorization::from((&x, &y));
        fac.refine();

        println!("{}", fac);

        for i in Vec::<(Z, u64)>::from(&fac).iter() {
            println!("{}", i.1);
        }
    }
}
