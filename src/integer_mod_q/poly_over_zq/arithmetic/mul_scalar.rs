// Copyright © 2025 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of scalar multiplication for [`PolyOverZq`].

use super::super::PolyOverZq;
use crate::error::MathError;
use crate::integer::Z;
use crate::integer_mod_q::Zq;
use crate::macros::arithmetics::{
    arithmetic_assign_between_types, arithmetic_assign_trait_borrowed_to_owned,
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    arithmetic_trait_reverse,
};
use crate::macros::for_others::implement_for_others;
use crate::traits::CompareBase;
use flint_sys::fmpz_mod_poly::{fmpz_mod_poly_scalar_mul_fmpz, fmpz_mod_poly_scalar_mul_ui};
use std::ops::{Mul, MulAssign};

impl Mul<&Z> for &PolyOverZq {
    type Output = PolyOverZq;
    /// Implements the [`Mul`] trait for a [`PolyOverZq`] with a [`Z`] integer.
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    /// [`Mul`] is also implemented for [`Z`] using [`PolyOverZq`].
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the polynomial is multiplied
    ///
    /// Returns the product of `self` and `scalar` as a [`PolyOverZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let poly_1 = PolyOverZq::from_str("4  1 2 3 4 mod 17").unwrap();
    /// let integer = Z::from(3);
    ///
    /// let poly_2 = &poly_1 * &integer;
    /// ```
    fn mul(self, scalar: &Z) -> Self::Output {
        let mut out = PolyOverZq::from(&self.modulus);
        unsafe {
            fmpz_mod_poly_scalar_mul_fmpz(
                &mut out.poly,
                &self.poly,
                &scalar.value,
                self.modulus.get_fmpz_mod_ctx_struct(),
            );
        }
        out
    }
}

arithmetic_trait_reverse!(Mul, mul, Z, PolyOverZq, PolyOverZq);

arithmetic_trait_borrowed_to_owned!(Mul, mul, PolyOverZq, Z, PolyOverZq);
arithmetic_trait_borrowed_to_owned!(Mul, mul, Z, PolyOverZq, PolyOverZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, PolyOverZq, Z, PolyOverZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Z, PolyOverZq, PolyOverZq);

implement_for_others!(Z, PolyOverZq, Mul Scalar for i8 i16 i32 i64 u8 u16 u32 u64);

impl Mul<&Zq> for &PolyOverZq {
    type Output = PolyOverZq;
    /// Implements the [`Mul`] trait for a [`PolyOverZq`] with a [`Zq`].
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    /// [`Mul`] is also implemented for [`Zq`] using [`PolyOverZq`].
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is multiplied
    ///
    /// Returns the product of `self` and `scalar` as a [`PolyOverZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{PolyOverZq, Zq};
    /// use std::str::FromStr;
    ///
    /// let poly_1 = PolyOverZq::from_str("4  1 2 3 4 mod 17").unwrap();
    /// let integer = Zq::from((3,17));
    ///
    /// let poly_2 = &poly_1 * &integer;
    /// ```
    ///
    /// # Panics ...
    /// - if the moduli mismatch.
    fn mul(self, scalar: &Zq) -> PolyOverZq {
        self.mul_scalar_zq_safe(scalar).unwrap()
    }
}

arithmetic_trait_reverse!(Mul, mul, Zq, PolyOverZq, PolyOverZq);

arithmetic_trait_borrowed_to_owned!(Mul, mul, PolyOverZq, Zq, PolyOverZq);
arithmetic_trait_borrowed_to_owned!(Mul, mul, Zq, PolyOverZq, PolyOverZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, PolyOverZq, Zq, PolyOverZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Zq, PolyOverZq, PolyOverZq);

impl PolyOverZq {
    /// Implements multiplication for a [`PolyOverZq`] with a [`Zq`].
    ///
    /// Parameters:
    /// - `scalar`: Specifies the scalar by which the polynomial is multiplied.
    ///
    /// Returns the product of `self` and `scalar` as a [`PolyOverZq`]
    /// or an error if the moduli mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{PolyOverZq, Zq};
    /// use std::str::FromStr;
    ///
    /// let poly_1 = PolyOverZq::from_str("4  1 2 3 4 mod 17").unwrap();
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

        let mut out = PolyOverZq::from(&scalar.modulus);
        unsafe {
            fmpz_mod_poly_scalar_mul_fmpz(
                &mut out.poly,
                &self.poly,
                &scalar.value.value,
                out.modulus.get_fmpz_mod_ctx_struct(),
            )
        }
        Ok(out)
    }
}

impl MulAssign<&Z> for PolyOverZq {
    /// Computes the scalar multiplication of `self` and `other` reusing
    /// the memory of `self`.
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply to `self`
    ///
    /// Returns the scalar of the polynomial as a [`PolyOverZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let mut a = PolyOverZq::from_str("3  1 2 -3 mod 5").unwrap();
    /// let b = Z::from(2);
    ///
    /// a *= &b;
    /// a *= b;
    /// a *= 2;
    /// a *= -2;
    /// ```
    fn mul_assign(&mut self, scalar: &Z) {
        unsafe {
            fmpz_mod_poly_scalar_mul_fmpz(
                &mut self.poly,
                &self.poly,
                &scalar.value,
                self.modulus.get_fmpz_mod_ctx(),
            )
        };
    }
}

impl MulAssign<i64> for PolyOverZq {
    /// Documentation at [`PolyOverZq::mul_assign`].
    fn mul_assign(&mut self, other: i64) {
        let z = Z::from(other);
        unsafe {
            fmpz_mod_poly_scalar_mul_fmpz(
                &mut self.poly,
                &self.poly,
                &z.value,
                self.modulus.get_fmpz_mod_ctx(),
            )
        };
    }
}

impl MulAssign<u64> for PolyOverZq {
    /// Documentation at [`PolyOverZ::mul_assign`].
    fn mul_assign(&mut self, other: u64) {
        unsafe {
            fmpz_mod_poly_scalar_mul_ui(
                &mut self.poly,
                &self.poly,
                other,
                self.modulus.get_fmpz_mod_ctx(),
            )
        };
    }
}

arithmetic_assign_trait_borrowed_to_owned!(MulAssign, mul_assign, PolyOverZq, Z);
arithmetic_assign_between_types!(MulAssign, mul_assign, PolyOverZq, i64, i32 i16 i8);
arithmetic_assign_between_types!(MulAssign, mul_assign, PolyOverZq, u64, u32 u16 u8);

#[cfg(test)]
mod test_mul_z {
    use super::PolyOverZq;
    use crate::integer::Z;
    use std::str::FromStr;

    /// Checks if polynomial multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let poly_1 =
            PolyOverZq::from_str(&format!("3  1 2 {} mod {}", i64::MAX, u64::MAX)).unwrap();
        let poly_2 = poly_1.clone();
        let poly_3 = PolyOverZq::from_str(&format!(
            "3  2 4 {} mod {}",
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
        let poly = PolyOverZq::from_str("3  1 2 3 mod 17").unwrap();
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
    use super::PolyOverZq;
    use crate::integer_mod_q::Zq;
    use std::str::FromStr;

    /// Checks if polynomial multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let poly_1 =
            PolyOverZq::from_str(&format!("3  1 2 {} mod {}", i64::MAX, u64::MAX)).unwrap();
        let poly_2 = poly_1.clone();
        let poly_3 = PolyOverZq::from_str(&format!(
            "3  2 4 {} mod {}",
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
        let poly = PolyOverZq::from_str("3  1 2 3 mod 17").unwrap();
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
        let poly = PolyOverZq::from_str("3  1 2 3 mod 17").unwrap();
        let z = Zq::from((2, 16));

        _ = &poly * &z;
    }

    /// Checks if scalar multiplication panics if the moduli mismatch
    #[test]
    fn different_moduli_error() {
        let poly = PolyOverZq::from_str("3  1 2 3 mod 17").unwrap();
        let z = Zq::from((2, 16));

        assert!(poly.mul_scalar_zq_safe(&z).is_err());
    }
}

#[cfg(test)]
mod test_mul_assign {
    use crate::integer::Z;
    use crate::integer_mod_q::PolyOverZq;
    use std::str::FromStr;

    /// Ensure that `mul_assign` works for small numbers.
    #[test]
    fn correct_small() {
        let mut a = PolyOverZq::from_str("3  1 2 -3 mod 7").unwrap();
        let b = Z::from(2);
        let c = Z::ZERO;

        a *= &b;
        assert_eq!(PolyOverZq::from_str("3  2 4 1 mod 7").unwrap(), a);
        a *= &c;
        assert_eq!(PolyOverZq::from_str("0 mod 7").unwrap(), a);
    }

    /// Ensure that `mul_assign` works for large numbers.
    #[test]
    fn correct_large() {
        let mut a = PolyOverZq::from_str(&format!("2  2 -1 mod {}", u64::MAX - 1)).unwrap();
        let b = i32::MAX;
        let cmp = PolyOverZq::from_str(&format!(
            "2  {} {} mod {}",
            i32::MAX as i64 * 2,
            i32::MAX as i64 * -1,
            u64::MAX - 1
        ))
        .unwrap();

        a *= b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `mul_assign` is available for all types.
    #[test]
    fn availability() {
        let mut a = PolyOverZq::from_str("3  1 2 -3 mod 8").unwrap();
        let b = Z::from(2);

        a *= &b;
        a *= b;
        a *= 1_u8;
        a *= 1_u16;
        a *= 1_u32;
        a *= 1_u64;
        a *= 1_i8;
        a *= 1_i16;
        a *= 1_i32;
        a *= 1_i64;
    }
}
