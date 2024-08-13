// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to evaluate a [`PolyOverZq`].
//! For each reasonable type, an implementation
//! of the [`Evaluate`] trait should be implemented.

use super::PolyOverZq;
use crate::{
    error::MathError, integer::Z, integer_mod_q::Zq, macros::for_others::implement_for_owned,
    traits::Evaluate,
};
use flint_sys::fmpz_mod_poly::fmpz_mod_poly_evaluate_fmpz;

impl<Integer: Into<Z>> Evaluate<Integer, Zq> for PolyOverZq {
    /// Evaluates a [`PolyOverZq`] on a given input of [`Z`].
    ///
    /// Parameters:
    /// - `value`: the value with which to evaluate the polynomial.
    ///
    /// Returns the evaluation of the polynomial as a [`Zq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::traits::*;
    /// use qfall_math::integer::Z;
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZq::from_str("5  0 1 2 -3 1 mod 17").unwrap();
    /// let value = Z::from(3);
    ///
    /// let res = poly.evaluate(&value);
    /// let res_2 = poly.evaluate(3);
    /// ```
    fn evaluate(&self, value: Integer) -> Zq {
        let value: Z = value.into();
        let mut res = Zq::from((0, &self.modulus));

        unsafe {
            fmpz_mod_poly_evaluate_fmpz(
                &mut res.value.value,
                &self.poly,
                &value.value,
                self.modulus.get_fmpz_mod_ctx_struct(),
            )
        };

        res
    }
}

impl Evaluate<&Zq, Zq> for PolyOverZq {
    /// Evaluates a [`PolyOverZq`] on a given input of [`Zq`]. Note that the
    /// [`Zq`] in this case is only a reference. Note that this function will panic if
    /// the modulus of the input and the polynomial mismatch.
    /// Use [`PolyOverZq::evaluate_safe`] if a panic has to be avoided.
    ///
    /// Parameters:
    /// - `value`: the value with which to evaluate the polynomial.
    ///
    /// Returns the evaluation of the polynomial as a [`Zq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::traits::*;
    /// use qfall_math::integer_mod_q::Zq;
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZq::from_str("5  0 1 2 -3 1 mod 17").unwrap();
    /// let value = Zq::from((3, 17));
    /// let res = poly.evaluate(&value);
    /// ```
    ///
    /// # Panics ...
    /// - if the moduli of the polynomial and the input mismatch.
    fn evaluate(&self, value: &Zq) -> Zq {
        self.evaluate_safe(value)
            .expect("The moduli of the provided inputs mismatch")
    }
}

impl PolyOverZq {
    /// Evaluates a [`PolyOverZq`] on a given input of [`Zq`]. Note that the
    /// [`Zq`] in this case is only a reference.
    ///
    /// Parameters:
    /// - `value`: the value with which to evaluate the polynomial.
    ///
    /// Returns the evaluation of the polynomial as a [`Zq`] or an error,
    /// if the moduli mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::traits::*;
    /// use qfall_math::integer_mod_q::Zq;
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZq::from_str("5  0 1 2 -3 1 mod 17").unwrap();
    /// let value = Zq::from((3, 17));
    /// let res = poly.evaluate(&value);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::MismatchingModulus`]
    ///     if the moduli of the polynomial and the input mismatch.
    pub fn evaluate_safe(&self, value: &Zq) -> Result<Zq, MathError> {
        if self.modulus != value.modulus {
            return Err(MathError::MismatchingModulus(format!(
                " The provided moduli are {} and {}",
                self.modulus, value.modulus
            )));
        }
        Ok(self.evaluate(&value.value))
    }
}

implement_for_owned!(Zq, Zq, PolyOverZq, Evaluate);

#[cfg(test)]
mod test_evaluate_z {
    use crate::integer::Z;
    use crate::integer_mod_q::{PolyOverZq, Zq};
    use crate::traits::Evaluate;
    use std::str::FromStr;

    /// Tests if evaluate works for [`Z`] as input
    #[test]
    fn eval_z() {
        let poly = PolyOverZq::from_str("2  1 2 mod 17").unwrap();

        let res = poly.evaluate(Z::from(3));

        assert_eq!(Zq::from((7, 17)), res);
    }

    /// Tests if evaluate with a reference works
    #[test]
    fn eval_z_ref() {
        let poly = PolyOverZq::from_str("2  1 2 mod 17").unwrap();

        let res = poly.evaluate(&Z::from(3));

        assert_eq!(Zq::from((7, 17)), res);
    }

    /// Tests if evaluate works with negative values
    #[test]
    fn eval_z_negative() {
        let poly = PolyOverZq::from_str("2  1 2 mod 17").unwrap();

        let res = poly.evaluate(&Z::from(-5));

        assert_eq!(Zq::from((8, 17)), res);
    }

    /// Tests if evaluate works with large integers
    #[test]
    fn eval_z_large() {
        let poly = PolyOverZq::from_str(&format!("2  3 2 mod {}", u64::MAX)).unwrap();

        let res = poly.evaluate(&Z::from(u64::MAX - 1));

        assert_eq!(Zq::from((1, u64::MAX)), res);
    }

    /// Test if evaluate works with max of [`i64`],[`i32`], ...
    #[test]
    fn eval_max() {
        let poly = PolyOverZq::from_str("2  1 2 mod 17").unwrap();

        // signed
        let _ = poly.evaluate(i64::MAX);
        let _ = poly.evaluate(i32::MAX);
        let _ = poly.evaluate(i16::MAX);
        let _ = poly.evaluate(i8::MAX);

        //unsigned
        let _ = poly.evaluate(u64::MAX);
        let _ = poly.evaluate(u32::MAX);
        let _ = poly.evaluate(u16::MAX);
        let _ = poly.evaluate(u8::MAX);
    }

    /// Test if evaluate works with min of [`i64`],[`i32`], ...
    #[test]
    fn eval_min() {
        let poly = PolyOverZq::from_str("2  1 2 mod 17").unwrap();

        // signed
        let _ = poly.evaluate(i64::MIN);
        let _ = poly.evaluate(i32::MIN);
        let _ = poly.evaluate(i16::MIN);
        let _ = poly.evaluate(i8::MIN);

        // unsigned
        let _ = poly.evaluate(u64::MIN);
        let _ = poly.evaluate(u32::MIN);
        let _ = poly.evaluate(u16::MIN);
        let _ = poly.evaluate(u8::MIN);
    }
}

#[cfg(test)]
mod test_evaluate_zq {
    use crate::{
        integer_mod_q::{PolyOverZq, Zq},
        traits::Evaluate,
    };
    use std::str::FromStr;

    /// Ensures that positive values return expected evaluation
    #[test]
    fn evaluate_positive() {
        let poly = PolyOverZq::from_str("2  1 3 mod 17").unwrap();
        let value = Zq::from((6, 17));

        let res_ref = poly.evaluate(&value);
        let res = poly.evaluate(value);

        assert_eq!(Zq::from((2, 17)), res);
        assert_eq!(res_ref, res);
    }

    /// Ensures that positive large values return expected evaluation
    #[test]
    fn evaluate_large_positive() {
        let poly =
            PolyOverZq::from_str(&format!("2  {} 1 mod {}", (u64::MAX - 1) / 2 + 2, u64::MAX))
                .unwrap();
        let value = Zq::from(((u64::MAX - 1) / 2, u64::MAX));

        let res_ref = poly.evaluate(&value);
        let res = poly.evaluate(value);

        assert_eq!(Zq::from((1, u64::MAX)), res);
        assert_eq!(res_ref, res);
    }

    /// Ensure that evaluate panics if the moduli mismatch
    #[test]
    #[should_panic]
    fn mismatching_modulus_panic() {
        let poly = PolyOverZq::from_str(&format!("2  3 1 mod {}", u64::MAX)).unwrap();
        let value = Zq::from((3, u64::MAX - 1));

        let _ = poly.evaluate(&value);
    }

    /// Ensure that evaluate_safe returns an error if the moduli mismatch
    #[test]
    fn mismatching_modulus_safe() {
        let poly = PolyOverZq::from_str(&format!("2  3 1 mod {}", u64::MAX)).unwrap();
        let value = Zq::from((3, u64::MAX - 1));

        assert!(poly.evaluate_safe(&value).is_err());
    }
}
