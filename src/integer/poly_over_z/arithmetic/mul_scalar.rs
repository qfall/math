// Copyright © 2025 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of scalar multiplication for [`PolyOverZ`].

use super::super::PolyOverZ;
use crate::integer::Z;
use crate::integer_mod_q::{PolyOverZq, Zq};
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    arithmetic_trait_reverse,
};
use crate::macros::for_others::implement_for_others;
use crate::rational::{PolyOverQ, Q};
use flint_sys::fmpq_poly::fmpq_poly_scalar_mul_fmpq;
use flint_sys::fmpz_mod_poly::fmpz_mod_poly_scalar_mul_fmpz;
use flint_sys::fmpz_poly::fmpz_poly_scalar_mul_fmpz;
use std::ops::Mul;

impl Mul<&Z> for &PolyOverZ {
    type Output = PolyOverZ;
    /// Implements the [`Mul`] trait for a [`PolyOverZ`] with a [`Z`] integer.
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    /// [`Mul`] is also implemented for [`Z`] using [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the polynomial is multiplied
    ///
    /// Returns the product of `self` and `scalar` as a [`PolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let poly_1 = PolyOverZ::from_str("4  1 2 3 4").unwrap();
    /// let integer = Z::from(3);
    ///
    /// let poly_2 = &poly_1 * &integer;
    /// ```
    fn mul(self, scalar: &Z) -> Self::Output {
        let mut out = PolyOverZ::default();
        unsafe {
            fmpz_poly_scalar_mul_fmpz(&mut out.poly, &self.poly, &scalar.value);
        }
        out
    }
}

arithmetic_trait_reverse!(Mul, mul, Z, PolyOverZ, PolyOverZ);

arithmetic_trait_borrowed_to_owned!(Mul, mul, PolyOverZ, Z, PolyOverZ);
arithmetic_trait_borrowed_to_owned!(Mul, mul, Z, PolyOverZ, PolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, PolyOverZ, Z, PolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Z, PolyOverZ, PolyOverZ);

implement_for_others!(Z, PolyOverZ, Mul Scalar for i8 i16 i32 i64 u8 u16 u32 u64);

impl Mul<&Zq> for &PolyOverZ {
    type Output = PolyOverZq;
    /// Implements the [`Mul`] trait for a [`PolyOverZ`] with a [`Zq`].
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    /// [`Mul`] is also implemented for [`Zq`] using [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is multiplied
    ///
    /// Returns the product of `self` and `scalar` as a [`PolyOverZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use qfall_math::integer_mod_q::{PolyOverZq, Zq};
    /// use std::str::FromStr;
    ///
    /// let poly_1 = PolyOverZ::from_str("4  1 2 3 4").unwrap();
    /// let integer = Zq::from((3,17));
    ///
    /// let poly_2 = &poly_1 * &integer;
    /// ```
    fn mul(self, scalar: &Zq) -> PolyOverZq {
        let mut out = PolyOverZq::from((1, &scalar.modulus));
        unsafe {
            fmpz_mod_poly_scalar_mul_fmpz(
                &mut out.poly,
                &PolyOverZq::from((self, &scalar.modulus)).poly,
                &scalar.value.value,
                out.modulus.get_fmpz_mod_ctx_struct(),
            )
        }
        out
    }
}

arithmetic_trait_reverse!(Mul, mul, Zq, PolyOverZ, PolyOverZq);

arithmetic_trait_borrowed_to_owned!(Mul, mul, PolyOverZ, Zq, PolyOverZq);
arithmetic_trait_borrowed_to_owned!(Mul, mul, Zq, PolyOverZ, PolyOverZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, PolyOverZ, Zq, PolyOverZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Zq, PolyOverZ, PolyOverZq);

impl Mul<&Q> for &PolyOverZ {
    type Output = PolyOverQ;
    /// Implements the [`Mul`] trait for a [`PolyOverZ`] with a [`Q`].
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    /// [`Mul`] is also implemented for [`Q`] using [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the polynomial is multiplied
    ///
    /// Returns the product of `self` and `scalar` as a [`PolyOverQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use qfall_math::rational::Q;
    /// use std::str::FromStr;
    ///
    /// let poly_1 = PolyOverZ::from_str("4  1 2 3 4").unwrap();
    /// let rational = Q::from((3,2));
    ///
    /// let poly_2 = &poly_1 * &rational;
    /// ```
    fn mul(self, scalar: &Q) -> PolyOverQ {
        let mut out = PolyOverQ::default();
        unsafe {
            fmpq_poly_scalar_mul_fmpq(&mut out.poly, &PolyOverQ::from(self).poly, &scalar.value);
        }
        out
    }
}

arithmetic_trait_reverse!(Mul, mul, Q, PolyOverZ, PolyOverQ);

arithmetic_trait_borrowed_to_owned!(Mul, mul, PolyOverZ, Q, PolyOverQ);
arithmetic_trait_borrowed_to_owned!(Mul, mul, Q, PolyOverZ, PolyOverQ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, PolyOverZ, Q, PolyOverQ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Q, PolyOverZ, PolyOverQ);

#[cfg(test)]
mod test_mul_z {
    use super::PolyOverZ;
    use crate::integer::Z;
    use std::str::FromStr;

    /// Checks if polynomial multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let poly_1 = PolyOverZ::from_str(&format!("3  1 2 {}", i64::MAX)).unwrap();
        let poly_2 = poly_1.clone();
        let poly_3 = PolyOverZ::from_str(&format!("3  2 4 {}", (i64::MAX as u64) * 2)).unwrap();
        let integer = Z::from(2);

        let poly_1 = &poly_1 * &integer;
        let poly_2 = &integer * &poly_2;

        assert_eq!(poly_3, poly_1);
        assert_eq!(poly_3, poly_2);
    }

    /// Checks if scalar multiplication works fine for different types
    #[test]
    fn availability() {
        let poly = PolyOverZ::from_str("3  1 2 3").unwrap();
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
        _ = poly.clone() * 2i8;
        _ = poly.clone() * 2u64;

        _ = &poly * &z;
        _ = &z * &poly;
        _ = &poly * z.clone();
        _ = z * &poly;
        _ = &poly * 2i8;
        _ = 2i8 * &poly;
    }
}

#[cfg(test)]
mod test_mul_zq {
    use super::PolyOverZ;
    use crate::integer_mod_q::{PolyOverZq, Zq};
    use std::str::FromStr;

    /// Checks if polynomial multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let poly_1 = PolyOverZ::from_str(&format!("3  1 2 {}", i64::MAX)).unwrap();
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
        let poly = PolyOverZ::from_str("3  1 2 3").unwrap();
        let z = Zq::from((2, 17));

        _ = poly.clone() * z.clone();
        _ = z.clone() * poly.clone();
        _ = &poly * &z;
        _ = &z * &poly;
        _ = &poly * z.clone();
        _ = z * &poly;
    }
}

#[cfg(test)]
mod test_mul_q {
    use super::PolyOverZ;
    use crate::rational::{PolyOverQ, Q};
    use std::str::FromStr;

    /// Checks if polynomial multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let poly_1 = PolyOverZ::from_str(&format!("3  1 2 {}", (i64::MAX as u64) * 2)).unwrap();
        let poly_2 = poly_1.clone();
        let poly_3 = PolyOverQ::from_str(&format!("3  1/2 1 {}", i64::MAX)).unwrap();
        let rational = Q::from((1, 2));

        let poly_1 = &poly_1 * &rational;
        let poly_2 = &rational * &poly_2;

        assert_eq!(poly_3, poly_1);
        assert_eq!(poly_3, poly_2);
    }

    /// Checks if scalar multiplication works fine for different types
    #[test]
    fn availability() {
        let poly = PolyOverZ::from_str("3  1 2 3").unwrap();
        let q = Q::from((1, 2));

        _ = poly.clone() * q.clone();
        _ = q.clone() * poly.clone();
        _ = &poly * &q;
        _ = &q * &poly;
        _ = &poly * q.clone();
        _ = q * &poly;
    }
}
