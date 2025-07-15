// Copyright © 2025 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of scalar multiplication for [`PolynomialRingZq`].

use super::super::PolynomialRingZq;
use crate::error::MathError;
use crate::integer::Z;
use crate::integer_mod_q::Zq;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    arithmetic_trait_reverse,
};
use crate::macros::for_others::implement_for_others;
use crate::traits::CompareBase;
use std::ops::Mul;

impl Mul<&Z> for &PolynomialRingZq {
    type Output = PolynomialRingZq;
    /// Implements the [`Mul`] trait for a [`PolynomialRingZq`] with a [`Z`] integer.
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    /// [`Mul`] is also implemented for [`Z`] using [`PolynomialRingZq`].
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the polynomial is multiplied
    ///
    /// Returns the product of `self` and `scalar` as a [`PolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolynomialRingZq;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let poly_1 = PolynomialRingZq::from_str("3  1 2 3 / 4  1 2 3 4 mod 17").unwrap();
    /// let integer = Z::from(3);
    ///
    /// let poly_2 = &poly_1 * &integer;
    /// ```
    fn mul(self, scalar: &Z) -> Self::Output {
        let mut out = PolynomialRingZq::from(&self.modulus);

        out.poly = &self.poly * scalar;

        out.reduce();
        out
    }
}

arithmetic_trait_reverse!(Mul, mul, Z, PolynomialRingZq, PolynomialRingZq);

arithmetic_trait_borrowed_to_owned!(Mul, mul, PolynomialRingZq, Z, PolynomialRingZq);
arithmetic_trait_borrowed_to_owned!(Mul, mul, Z, PolynomialRingZq, PolynomialRingZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, PolynomialRingZq, Z, PolynomialRingZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Z, PolynomialRingZq, PolynomialRingZq);

implement_for_others!(Z, PolynomialRingZq, Mul Scalar for i8 i16 i32 i64 u8 u16 u32 u64);

impl Mul<&Zq> for &PolynomialRingZq {
    type Output = PolynomialRingZq;
    /// Implements the [`Mul`] trait for a [`PolynomialRingZq`] with a [`Zq`].
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    /// [`Mul`] is also implemented for [`Zq`] using [`PolynomialRingZq`].
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is multiplied
    ///
    /// Returns the product of `self` and `scalar` as a [`PolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{PolynomialRingZq, Zq};
    /// use std::str::FromStr;
    ///
    /// let poly_1 = PolynomialRingZq::from_str("3  1 2 3 / 4  1 2 3 4 mod 17").unwrap();
    /// let integer = Zq::from((3,17));
    ///
    /// let poly_2 = &poly_1 * &integer;
    /// ```
    ///
    /// # Panics ...
    /// - if the moduli mismatch.
    fn mul(self, scalar: &Zq) -> PolynomialRingZq {
        self.mul_scalar_zq_safe(scalar).unwrap()
    }
}

arithmetic_trait_reverse!(Mul, mul, Zq, PolynomialRingZq, PolynomialRingZq);

arithmetic_trait_borrowed_to_owned!(Mul, mul, PolynomialRingZq, Zq, PolynomialRingZq);
arithmetic_trait_borrowed_to_owned!(Mul, mul, Zq, PolynomialRingZq, PolynomialRingZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, PolynomialRingZq, Zq, PolynomialRingZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Zq, PolynomialRingZq, PolynomialRingZq);

impl PolynomialRingZq {
    /// Implements multiplication for a [`PolynomialRingZq`] with a [`Zq`].
    ///
    /// Parameters:
    /// - `scalar`: Specifies the scalar by which the polynomial is multiplied.
    ///
    /// Returns the product of `self` and `scalar` as a [`PolynomialRingZq`]
    /// or an error if the moduli mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{PolynomialRingZq, Zq};
    /// use std::str::FromStr;
    ///
    /// let poly_1 = PolynomialRingZq::from_str("3  1 2 3 / 4  1 2 3 4 mod 17").unwrap();
    /// let integer = Zq::from((3,17));
    ///
    /// let poly_2 = poly_1.mul_scalar_zq_safe(&integer).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///   [`MathError::MismatchingModulus`] if the moduli mismatch.
    pub fn mul_scalar_zq_safe(&self, scalar: &Zq) -> Result<Self, MathError> {
        if !self.compare_base(scalar) {
            return Err(self.call_compare_base_error(scalar).unwrap());
        }

        let mut out = PolynomialRingZq::from(&self.modulus);

        out.poly = &self.poly * &scalar.value;

        out.reduce();
        Ok(out)
    }
}

#[cfg(test)]
mod test_mul_z {
    use super::PolynomialRingZq;
    use crate::integer::Z;
    use std::str::FromStr;

    /// Checks if polynomial multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let poly_1 = PolynomialRingZq::from_str(&format!(
            "3  1 2 {} / 4  1 2 3 4 mod {}",
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let poly_2 = poly_1.clone();
        let poly_3 = PolynomialRingZq::from_str(&format!(
            "3  2 4 {} / 4  1 2 3 4 mod {}",
            (i64::MAX as u64) * 2,
            u64::MAX
        ))
        .unwrap();
        let integer = Z::from(2);

        let poly_1 = &poly_1 * &integer;
        let poly_2 = &integer * &poly_2;

        assert_eq!(poly_3, poly_1);
        assert_eq!(poly_3, poly_2);
    }

    /// Checks if scalar multiplication works fine for different types
    #[test]
    fn availability() {
        let poly = PolynomialRingZq::from_str("3  1 2 3 / 4  1 2 3 4 mod 17").unwrap();
        let z = Z::from(2);

        _ = poly.clone() * z.clone();
        _ = poly.clone() * 2i8;
        _ = poly.clone() * 2u8;
        _ = poly.clone() * 2i16;
        _ = poly.clone() * 2u16;
        _ = poly.clone() * 2i32;
        _ = poly.clone() * 2u32;
        _ = poly.clone() * 2i64;
        _ = poly.clone() * 2u64;

        _ = z.clone() * poly.clone();
        _ = 2i8 * poly.clone();
        _ = 2u64 * poly.clone();

        _ = &poly * &z;
        _ = &z * &poly;
        _ = &poly * z.clone();
        _ = z.clone() * &poly;
        _ = poly.clone() * &z;
        _ = &z * poly.clone();
        _ = &poly * 2i8;
        _ = 2i8 * &poly;
    }
}

#[cfg(test)]
mod test_mul_zq {
    use super::PolynomialRingZq;
    use crate::integer_mod_q::Zq;
    use std::str::FromStr;

    /// Checks if polynomial multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let poly_1 = PolynomialRingZq::from_str(&format!(
            "3  1 2 {} / 4  1 2 3 4 mod {}",
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let poly_2 = poly_1.clone();
        let poly_3 = PolynomialRingZq::from_str(&format!(
            "3  2 4 {} / 4  1 2 3 4 mod {}",
            (i64::MAX as u64) * 2,
            u64::MAX
        ))
        .unwrap();
        let integer = Zq::from((2, u64::MAX));

        let poly_1 = &poly_1 * &integer;
        let poly_2 = &integer * &poly_2;

        assert_eq!(poly_3, poly_1);
        assert_eq!(poly_3, poly_2);
    }

    /// Checks if scalar multiplication works fine for different types
    #[test]
    fn availability() {
        let poly = PolynomialRingZq::from_str("3  1 2 3 / 4  1 2 3 4 mod 17").unwrap();
        let z = Zq::from((2, 17));

        _ = poly.clone() * z.clone();
        _ = z.clone() * poly.clone();
        _ = &poly * &z;
        _ = &z * &poly;
        _ = &poly * z.clone();
        _ = z.clone() * &poly;
        _ = &z * poly.clone();
        _ = poly.clone() * &z;
    }

    /// Checks if scalar multiplication panics if the moduli mismatch
    #[test]
    #[should_panic]
    fn different_moduli_panic() {
        let poly = PolynomialRingZq::from_str("3  1 2 3 / 4  1 2 3 4 mod 17").unwrap();
        let z = Zq::from((2, 16));

        _ = &poly * &z;
    }

    /// Checks if scalar multiplication panics if the moduli mismatch
    #[test]
    fn different_moduli_error() {
        let poly = PolynomialRingZq::from_str("3  1 2 3 / 4  1 2 3 4 mod 17").unwrap();
        let z = Zq::from((2, 16));

        assert!(poly.mul_scalar_zq_safe(&z).is_err());
    }
}
