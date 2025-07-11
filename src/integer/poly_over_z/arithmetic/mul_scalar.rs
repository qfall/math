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
    arithmetic_assign_between_types, arithmetic_assign_trait_borrowed_to_owned,
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    arithmetic_trait_reverse,
};
use crate::macros::for_others::implement_for_others;
use crate::rational::{PolyOverQ, Q};
use flint_sys::fmpq_poly::fmpq_poly_scalar_mul_fmpq;
use flint_sys::fmpz_mod_poly::fmpz_mod_poly_scalar_mul_fmpz;
use flint_sys::fmpz_poly::{
    fmpz_poly_scalar_mul_fmpz, fmpz_poly_scalar_mul_si, fmpz_poly_scalar_mul_ui,
};
use std::ops::{Mul, MulAssign};

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
        let mut out = PolyOverZq::from(&scalar.modulus);
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

impl MulAssign<&Z> for PolyOverZ {
    /// Computes the scalar multiplication of `self` and `other` reusing
    /// the memory of `self`.
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply to `self`
    ///
    /// Returns the scalar of the polynomial as a [`PolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{Z,PolyOverZ};
    /// use std::str::FromStr;
    ///
    /// let mut a = PolyOverZ::from_str("3  1 2 -3").unwrap();
    /// let b = Z::from(2);
    ///
    /// a *= &b;
    /// a *= b;
    /// a *= 2;
    /// a *= -2;
    /// ```
    fn mul_assign(&mut self, scalar: &Z) {
        unsafe { fmpz_poly_scalar_mul_fmpz(&mut self.poly, &self.poly, &scalar.value) };
    }
}

impl MulAssign<i64> for PolyOverZ {
    /// Documentation at [`PolyOverZ::mul_assign`].
    fn mul_assign(&mut self, other: i64) {
        unsafe { fmpz_poly_scalar_mul_si(&mut self.poly, &self.poly, other) };
    }
}

impl MulAssign<u64> for PolyOverZ {
    /// Documentation at [`PolyOverZ::mul_assign`].
    fn mul_assign(&mut self, other: u64) {
        unsafe { fmpz_poly_scalar_mul_ui(&mut self.poly, &self.poly, other) };
    }
}

arithmetic_assign_trait_borrowed_to_owned!(MulAssign, mul_assign, PolyOverZ, Z);
arithmetic_assign_between_types!(MulAssign, mul_assign, PolyOverZ, i64, i32 i16 i8);
arithmetic_assign_between_types!(MulAssign, mul_assign, PolyOverZ, u64, u32 u16 u8);

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
        _ = z.clone() * &poly;
        _ = &z * poly.clone();
        _ = poly.clone() * &z;
    }
}

#[cfg(test)]
mod test_mul_assign {
    use crate::integer::{PolyOverZ, Z};
    use std::str::FromStr;

    /// Ensure that `mul_assign` works for small numbers.
    #[test]
    fn correct_small() {
        let mut a = PolyOverZ::from_str("3  1 2 -3").unwrap();
        let b = Z::from(2);
        let c = Z::ZERO;

        a *= &b;
        assert_eq!(PolyOverZ::from_str("3  2 4 -6").unwrap(), a);
        a *= &c;
        assert_eq!(PolyOverZ::from(0), a);
    }

    /// Ensure that `mul_assign` works for large numbers.
    #[test]
    fn correct_large() {
        let mut a = PolyOverZ::from_str("2  2 -1").unwrap();
        let b = i32::MAX;
        let cmp = PolyOverZ::from_str(&format!(
            "2  {} {}",
            i32::MAX as i64 * 2,
            i32::MAX as i64 * -1
        ))
        .unwrap();

        a *= b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `mul_assign` is available for all types.
    #[test]
    fn availability() {
        let mut a = PolyOverZ::from_str("3  1 2 -3").unwrap();
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
        _ = q.clone() * &poly;
        _ = &q * poly.clone();
        _ = poly.clone() * &q;
    }
}
