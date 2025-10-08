// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of scalar multiplication for [`MatZq`] matrices.

use super::super::MatZq;
use crate::error::MathError;
use crate::integer::Z;
use crate::integer_mod_q::Zq;
use crate::macros::arithmetics::{
    arithmetic_assign_between_types, arithmetic_assign_trait_borrowed_to_owned,
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    arithmetic_trait_reverse,
};
use crate::macros::for_others::implement_for_others;
use crate::traits::{CompareBase, MatrixDimensions};
use flint_sys::fmpz_mod_mat::{
    fmpz_mod_mat_scalar_mul_fmpz, fmpz_mod_mat_scalar_mul_si, fmpz_mod_mat_scalar_mul_ui,
};
use std::ops::{Mul, MulAssign};

impl Mul<&Z> for &MatZq {
    type Output = MatZq;
    /// Implements the [`Mul`] trait for a [`MatZq`] matrix with a [`Z`] integer.
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is multiplied
    ///
    /// Returns the product of `self` and `scalar` as a [`MatZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let mat_1 = MatZq::from_str("[[42, 17],[8, 6]] mod 61").unwrap();
    /// let integer = Z::from(3);
    ///
    /// let mat_2 = &mat_1 * &integer;
    /// ```
    fn mul(self, scalar: &Z) -> Self::Output {
        let mut out = MatZq::new(self.get_num_rows(), self.get_num_columns(), self.get_mod());
        unsafe {
            fmpz_mod_mat_scalar_mul_fmpz(&mut out.matrix, &self.matrix, &scalar.value);
        }
        out
    }
}

arithmetic_trait_reverse!(Mul, mul, Z, MatZq, MatZq);

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatZq, Z, MatZq);
arithmetic_trait_borrowed_to_owned!(Mul, mul, Z, MatZq, MatZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatZq, Z, MatZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Z, MatZq, MatZq);

implement_for_others!(Z, MatZq, Mul Scalar for i8 i16 i32 i64 u8 u16 u32 u64);

impl Mul<&Zq> for &MatZq {
    type Output = MatZq;
    /// Implements the [`Mul`] trait for a [`MatZq`] matrix with a [`Zq`].
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is multiplied
    ///
    /// Returns the product of `self` and `scalar` as a [`MatZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatZq, Zq};
    /// use std::str::FromStr;
    ///
    /// let mat_1 = MatZq::from_str("[[42, 17],[8, 6]] mod 61").unwrap();
    /// let integer = Zq::from((2, 61));
    ///
    /// let mat_2 = &mat_1 * &integer;
    /// ```
    ///
    /// # Panics ...
    /// - if the moduli mismatch.
    fn mul(self, scalar: &Zq) -> Self::Output {
        self.mul_scalar_safe(scalar).unwrap()
    }
}

arithmetic_trait_reverse!(Mul, mul, Zq, MatZq, MatZq);

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatZq, Zq, MatZq);
arithmetic_trait_borrowed_to_owned!(Mul, mul, Zq, MatZq, MatZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatZq, Zq, MatZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Zq, MatZq, MatZq);

impl MatZq {
    /// Implements multiplication for a [`MatZq`] matrix with a [`Zq`].
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is multiplied
    ///
    /// Returns the product of `self` and `scalar` as a [`MatZq`] or
    /// an error if the moduli mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatZq, Zq};
    /// use std::str::FromStr;
    ///
    /// let mat_1 = MatZq::from_str("[[42, 17],[8, 6]] mod 61").unwrap();
    /// let integer = Zq::from((2, 61));
    ///
    /// let mat_2 = &mat_1.mul_scalar_safe(&integer).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///   [`MismatchingModulus`](MathError::MismatchingModulus) if the moduli mismatch.
    pub fn mul_scalar_safe(&self, scalar: &Zq) -> Result<Self, MathError> {
        if !self.compare_base(scalar) {
            return Err(self.call_compare_base_error(scalar).unwrap());
        }

        let mut out = MatZq::new(self.get_num_rows(), self.get_num_columns(), self.get_mod());
        unsafe {
            fmpz_mod_mat_scalar_mul_fmpz(&mut out.matrix, &self.matrix, &scalar.value.value);
        }
        Ok(out)
    }
}

impl MulAssign<&Z> for MatZq {
    /// Computes the scalar multiplication of `self` and `other` reusing
    /// the memory of `self`.
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply to `self`
    ///
    /// Returns the scalar of the matrix as a [`MatZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let mut a = MatZq::from_str("[[2, 1],[1, 2]] mod 61").unwrap();
    /// let b = Z::from(2);
    ///
    /// a *= &b;
    /// a *= b;
    /// a *= 2;
    /// a *= -2;
    /// ```
    fn mul_assign(&mut self, scalar: &Z) {
        unsafe { fmpz_mod_mat_scalar_mul_fmpz(&mut self.matrix, &self.matrix, &scalar.value) };
    }
}

impl MulAssign<&Zq> for MatZq {
    /// Documentation at [`MatZq::mul_assign`]
    ///
    /// # Panics ...
    /// - if the moduli are different.
    fn mul_assign(&mut self, scalar: &Zq) {
        if !self.compare_base(scalar) {
            panic!("{:?}", self.call_compare_base_error(scalar).unwrap())
        }
        unsafe {
            fmpz_mod_mat_scalar_mul_fmpz(&mut self.matrix, &self.matrix, &scalar.value.value)
        };
    }
}

arithmetic_assign_trait_borrowed_to_owned!(MulAssign, mul_assign, MatZq, Zq);

impl MulAssign<i64> for MatZq {
    /// Documentation at [`MatZq::mul_assign`].
    fn mul_assign(&mut self, other: i64) {
        unsafe { fmpz_mod_mat_scalar_mul_si(&mut self.matrix, &self.matrix, other) };
    }
}

impl MulAssign<u64> for MatZq {
    /// Documentation at [`MatZq::mul_assign`].
    fn mul_assign(&mut self, other: u64) {
        unsafe { fmpz_mod_mat_scalar_mul_ui(&mut self.matrix, &self.matrix, other) };
    }
}

arithmetic_assign_trait_borrowed_to_owned!(MulAssign, mul_assign, MatZq, Z);
arithmetic_assign_between_types!(MulAssign, mul_assign, MatZq, i64, i32 i16 i8);
arithmetic_assign_between_types!(MulAssign, mul_assign, MatZq, u64, u32 u16 u8);

#[cfg(test)]
mod test_mul_z {
    use crate::integer::Z;
    use crate::integer_mod_q::MatZq;
    use std::str::FromStr;

    /// Checks if matrix multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let mat_1 = MatZq::from_str("[[42, 17],[8, 6]] mod 61").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = MatZq::from_str("[[84, 34],[16, 12]] mod 61").unwrap();
        let integer = Z::from(2);

        let mat_1 = &mat_1 * &integer;
        let mat_2 = &integer * &mat_2;

        assert_eq!(mat_3, mat_1);
        assert_eq!(mat_3, mat_2);
    }

    /// Checks if scalar multiplication works fine for both owned
    #[test]
    fn owned_correctness() {
        let mat_1 = MatZq::from_str("[[42, 17],[8, 6]] mod 61").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = MatZq::from_str("[[84, 34],[16, 12]] mod 61").unwrap();
        let integer_1 = Z::from(2);
        let integer_2 = Z::from(2);

        let mat_1 = mat_1 * integer_1;
        let mat_2 = integer_2 * mat_2;

        assert_eq!(mat_3, mat_1);
        assert_eq!(mat_3, mat_2);
    }

    /// Checks if scalar multiplication works fine for half owned/borrowed
    #[test]
    fn half_correctness() {
        let mat_1 = MatZq::from_str("[[42, 17],[8, 6]] mod 61").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = mat_1.clone();
        let mat_4 = mat_1.clone();
        let mat_5 = MatZq::from_str("[[84, 34],[16, 12]] mod 61").unwrap();
        let integer_1 = Z::from(2);
        let integer_2 = Z::from(2);

        let mat_1 = mat_1 * &integer_1;
        let mat_2 = &integer_2 * mat_2;
        let mat_3 = &mat_3 * integer_1;
        let mat_4 = integer_2 * &mat_4;

        assert_eq!(mat_5, mat_1);
        assert_eq!(mat_5, mat_2);
        assert_eq!(mat_5, mat_3);
        assert_eq!(mat_5, mat_4);
    }

    /// Checks if scalar multiplication works fine for different scalar types
    #[test]
    #[allow(clippy::erasing_op)]
    fn different_types() {
        let mat_1 = MatZq::from_str("[[42],[0],[2]] mod 61").unwrap();
        let mat_2 = MatZq::from_str("[[2, 6, 5],[4, 42, 3]] mod 61").unwrap();
        let mat_3 = MatZq::from_str("[[23],[0],[4]] mod 61").unwrap();
        let mat_4 = MatZq::from_str("[[0],[0],[0]] mod 61").unwrap();
        let mat_5 = MatZq::from_str("[[-42],[0],[-2]] mod 61").unwrap();
        let mat_6 = MatZq::from_str("[[6, 18, 15],[12, 126, 9]] mod 61").unwrap();

        assert_eq!(mat_3, 2u8 * &mat_1);
        assert_eq!(mat_3, 2i8 * &mat_1);
        assert_eq!(mat_3, 2u16 * &mat_1);
        assert_eq!(mat_3, 2i16 * &mat_1);
        assert_eq!(mat_3, 2u32 * &mat_1);
        assert_eq!(mat_3, 2i32 * &mat_1);
        assert_eq!(mat_3, 2u64 * &mat_1);
        assert_eq!(mat_3, 2i64 * &mat_1);
        assert_eq!(mat_4, 0 * &mat_1);
        assert_eq!(mat_5, -1 * mat_1);
        assert_eq!(mat_6, mat_2 * 3);
    }

    /// Checks if scalar multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat_1 = MatZq::from_str("[[42],[0],[2]] mod 61").unwrap();
        let mat_2 = MatZq::from_str("[[2, 6, 5],[4, 42, 3]] mod 61").unwrap();
        let mat_3 = MatZq::from_str("[[84],[0],[4]] mod 61").unwrap();
        let mat_4 = MatZq::from_str("[[4, 12, 10],[8, 84, 6]] mod 61").unwrap();
        let integer = Z::from(2);

        assert_eq!(mat_3, &integer * mat_1);
        assert_eq!(mat_4, integer * mat_2);
    }

    /// Checks if matrix multiplication works fine for large values
    #[test]
    fn large_entries() {
        let mat_1 = MatZq::from_str(&format!("[[1],[{}],[4]] mod {}", i64::MAX, u64::MAX)).unwrap();
        let mat_2 = MatZq::from_str(&format!("[[3]] mod {}", u64::MAX)).unwrap();
        let mat_3 =
            MatZq::from_str(&format!("[[3],[{}],[12]] mod {}", i64::MAX - 1, u64::MAX)).unwrap();
        let mat_4 = MatZq::from_str(&format!("[[{}]] mod {}", i64::MAX - 1, u64::MAX)).unwrap();
        let integer_1 = Z::from(3);
        let integer_2 = Z::from(i64::MAX);

        assert_eq!(mat_3, integer_1 * mat_1);
        assert_eq!(mat_4, integer_2 * mat_2);
    }
}

#[cfg(test)]
mod test_mul_zq {
    use crate::integer_mod_q::{MatZq, Zq};
    use std::str::FromStr;

    /// Checks if matrix multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let mat_1 = MatZq::from_str("[[42, 17],[8, 6]] mod 61").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = MatZq::from_str("[[84, 34],[16, 12]] mod 61").unwrap();
        let integer = Zq::from((2, 61));

        let mat_1 = &mat_1 * &integer;
        let mat_2 = &integer * &mat_2;

        assert_eq!(mat_3, mat_1);
        assert_eq!(mat_3, mat_2);
    }

    /// Checks if scalar multiplication works fine for both owned
    #[test]
    fn owned_correctness() {
        let mat_1 = MatZq::from_str("[[42, 17],[8, 6]] mod 61").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = MatZq::from_str("[[84, 34],[16, 12]] mod 61").unwrap();
        let integer_1 = Zq::from((2, 61));
        let integer_2 = Zq::from((2, 61));

        let mat_1 = mat_1 * integer_1;
        let mat_2 = integer_2 * mat_2;

        assert_eq!(mat_3, mat_1);
        assert_eq!(mat_3, mat_2);
    }

    /// Checks if scalar multiplication works fine for half owned/borrowed
    #[test]
    fn half_correctness() {
        let mat_1 = MatZq::from_str("[[42, 17],[8, 6]] mod 61").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = mat_1.clone();
        let mat_4 = mat_1.clone();
        let mat_5 = MatZq::from_str("[[84, 34],[16, 12]] mod 61").unwrap();
        let integer_1 = Zq::from((2, 61));
        let integer_2 = Zq::from((2, 61));

        let mat_1 = mat_1 * &integer_1;
        let mat_2 = &integer_2 * mat_2;
        let mat_3 = &mat_3 * integer_1;
        let mat_4 = integer_2 * &mat_4;

        assert_eq!(mat_5, mat_1);
        assert_eq!(mat_5, mat_2);
        assert_eq!(mat_5, mat_3);
        assert_eq!(mat_5, mat_4);
    }

    /// Checks if scalar multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat_1 = MatZq::from_str("[[42],[0],[2]] mod 61").unwrap();
        let mat_2 = MatZq::from_str("[[2, 6, 5],[4, 42, 3]] mod 61").unwrap();
        let mat_3 = MatZq::from_str("[[84],[0],[4]] mod 61").unwrap();
        let mat_4 = MatZq::from_str("[[4, 12, 10],[8, 84, 6]] mod 61").unwrap();
        let integer = Zq::from((2, 61));

        assert_eq!(mat_3, &integer * mat_1);
        assert_eq!(mat_4, integer * mat_2);
    }

    /// Checks if matrix multiplication works fine for large values
    #[test]
    fn large_entries() {
        let mat_1 = MatZq::from_str(&format!("[[1],[{}],[4]] mod {}", i64::MAX, u64::MAX)).unwrap();
        let mat_2 = MatZq::from_str(&format!("[[3]] mod {}", u64::MAX)).unwrap();
        let mat_3 =
            MatZq::from_str(&format!("[[3],[{}],[12]] mod {}", i64::MAX - 1, u64::MAX)).unwrap();
        let mat_4 = MatZq::from_str(&format!("[[{}]] mod {}", i64::MAX - 1, u64::MAX)).unwrap();
        let integer_1 = Zq::from((3, u64::MAX));
        let integer_2 = Zq::from((i64::MAX, u64::MAX));

        assert_eq!(mat_3, integer_1 * mat_1);
        assert_eq!(mat_4, integer_2 * mat_2);
    }

    /// Checks if scalar multiplication panics if the moduli mismatch
    #[test]
    #[should_panic]
    fn different_moduli_error() {
        let mat_1 = MatZq::from_str("[[42],[0],[2]] mod 61").unwrap();
        let integer = Zq::from((2, 3));

        _ = &integer * mat_1;
    }

    /// Checks if scalar multiplication returns an error if the moduli mismatch
    #[test]
    fn different_moduli_error_safe() {
        let mat_1 = MatZq::from_str("[[42],[0],[2]] mod 61").unwrap();
        let integer = Zq::from((2, 3));

        let mat_2 = &mat_1.mul_scalar_safe(&integer);

        assert!(mat_2.is_err());
    }
}

#[cfg(test)]
mod test_mul_assign {
    use crate::integer::Z;
    use crate::integer_mod_q::{MatZq, Zq};
    use std::str::FromStr;

    /// Ensure that `mul_assign` produces same output as normal multiply.
    #[test]
    fn consistency() {
        let mut a = MatZq::from_str(&format!("[[2, 1],[-1, 0]] mod {}", u64::MAX - 1)).unwrap();
        let b = i32::MAX;
        let cmp = &a * b;

        a *= b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `mul_assign` is available for all types.
    #[test]
    fn availability() {
        let mut mat_zq = MatZq::from_str("[[2, 1],[1, 2]] mod 7").unwrap();
        let z = Z::from(2);
        let zq = Zq::from((2, 7));

        mat_zq *= &z;
        mat_zq *= z;
        mat_zq *= &zq;
        mat_zq *= zq;
        mat_zq *= 1_u8;
        mat_zq *= 1_u16;
        mat_zq *= 1_u32;
        mat_zq *= 1_u64;
        mat_zq *= 1_i8;
        mat_zq *= 1_i16;
        mat_zq *= 1_i32;
        mat_zq *= 1_i64;
    }

    /// Ensure that `mul_assign` panics if the moduli mismatch.
    #[test]
    #[should_panic]
    fn mismatching_modulus_zq() {
        let mut mat_zq = MatZq::from_str("[[2, 1],[1, 2]] mod 7").unwrap();

        let zq = Zq::from((2, u64::MAX - 1));

        mat_zq *= &zq;
    }
}
