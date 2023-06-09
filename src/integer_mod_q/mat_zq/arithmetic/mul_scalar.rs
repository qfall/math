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
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    arithmetic_trait_reverse,
};
use crate::macros::for_others::implement_for_others;
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpz_mod_mat::fmpz_mod_mat_scalar_mul_fmpz;
use std::ops::Mul;

impl Mul<&Z> for &MatZq {
    type Output = MatZq;
    /// Implements multiplication for a [`MatZq`] matrix with a [`Z`] integer.
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
    /// let mat1 = MatZq::from_str("[[42, 17],[8, 6]] mod 61").unwrap();
    /// let integer = Z::from(3);
    ///
    /// let mat2 = &mat1 * &integer;
    /// ```
    fn mul(self, scalar: &Z) -> Self::Output {
        let mut out =
            MatZq::new(self.get_num_rows(), self.get_num_columns(), self.get_mod()).unwrap();
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
    /// Implements multiplication for a [`MatZq`] matrix with a [`Zq`].
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
    /// let mat1 = MatZq::from_str("[[42, 17],[8, 6]] mod 61").unwrap();
    /// let integer = Zq::try_from((2, 61)).unwrap();
    ///
    /// let mat2 = &mat1 * &integer;
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
    /// Returns the product of `self` and `scalar` as a [`MatZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatZq, Zq};
    /// use std::str::FromStr;
    ///
    /// let mat1 = MatZq::from_str("[[42, 17],[8, 6]] mod 61").unwrap();
    /// let integer = Zq::try_from((2, 61)).unwrap();
    ///
    /// let mat2 = &mat1.mul_scalar_safe(&integer).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`MismatchingModulus`](MathError::MismatchingModulus) if the moduli mismatch.
    pub fn mul_scalar_safe(&self, scalar: &Zq) -> Result<Self, MathError> {
        if self.get_mod() != scalar.modulus {
            return Err(MathError::MismatchingModulus(format!(
                " Tried to add matrixes with moduli '{}' and '{}'.",
                self.get_mod(),
                scalar.modulus
            )));
        }

        let mut out =
            MatZq::new(self.get_num_rows(), self.get_num_columns(), self.get_mod()).unwrap();
        unsafe {
            fmpz_mod_mat_scalar_mul_fmpz(&mut out.matrix, &self.matrix, &scalar.value.value);
        }
        Ok(out)
    }
}

#[cfg(test)]
mod test_mul_z {
    use crate::integer::Z;
    use crate::integer_mod_q::MatZq;
    use std::str::FromStr;

    /// Checks if matrix multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let mat1 = MatZq::from_str("[[42, 17],[8, 6]] mod 61").unwrap();
        let mat2 = mat1.clone();
        let mat3 = MatZq::from_str("[[84, 34],[16, 12]] mod 61").unwrap();
        let integer = Z::from(2);

        let mat1 = &mat1 * &integer;
        let mat2 = &integer * &mat2;

        assert_eq!(mat3, mat1);
        assert_eq!(mat3, mat2);
    }

    /// Checks if scalar multiplication works fine for both owned
    #[test]
    fn owned_correctness() {
        let mat1 = MatZq::from_str("[[42, 17],[8, 6]] mod 61").unwrap();
        let mat2 = mat1.clone();
        let mat3 = MatZq::from_str("[[84, 34],[16, 12]] mod 61").unwrap();
        let integer1 = Z::from(2);
        let integer2 = Z::from(2);

        let mat1 = mat1 * integer1;
        let mat2 = integer2 * mat2;

        assert_eq!(mat3, mat1);
        assert_eq!(mat3, mat2);
    }

    /// Checks if scalar multiplication works fine for half owned/borrowed
    #[test]
    fn half_correctness() {
        let mat1 = MatZq::from_str("[[42, 17],[8, 6]] mod 61").unwrap();
        let mat2 = mat1.clone();
        let mat3 = mat1.clone();
        let mat4 = mat1.clone();
        let mat5 = MatZq::from_str("[[84, 34],[16, 12]] mod 61").unwrap();
        let integer1 = Z::from(2);
        let integer2 = Z::from(2);

        let mat1 = mat1 * &integer1;
        let mat2 = &integer2 * mat2;
        let mat3 = &mat3 * integer1;
        let mat4 = integer2 * &mat4;

        assert_eq!(mat5, mat1);
        assert_eq!(mat5, mat2);
        assert_eq!(mat5, mat3);
        assert_eq!(mat5, mat4);
    }

    /// Checks if scalar multiplication works fine for different scalar types
    #[test]
    #[allow(clippy::erasing_op)]
    fn different_types() {
        let mat1 = MatZq::from_str("[[42],[0],[2]] mod 61").unwrap();
        let mat2 = MatZq::from_str("[[2, 6, 5],[4, 42, 3]] mod 61").unwrap();
        let mat3 = MatZq::from_str("[[23],[0],[4]] mod 61").unwrap();
        let mat4 = MatZq::from_str("[[0],[0],[0]] mod 61").unwrap();
        let mat5 = MatZq::from_str("[[-42],[0],[-2]] mod 61").unwrap();
        let mat6 = MatZq::from_str("[[6, 18, 15],[12, 126, 9]] mod 61").unwrap();

        assert_eq!(mat3, 2u8 * &mat1);
        assert_eq!(mat3, 2i8 * &mat1);
        assert_eq!(mat3, 2u16 * &mat1);
        assert_eq!(mat3, 2i16 * &mat1);
        assert_eq!(mat3, 2u32 * &mat1);
        assert_eq!(mat3, 2i32 * &mat1);
        assert_eq!(mat3, 2u64 * &mat1);
        assert_eq!(mat3, 2i64 * &mat1);
        assert_eq!(mat4, 0 * &mat1);
        assert_eq!(mat5, -1 * mat1);
        assert_eq!(mat6, mat2 * 3);
    }

    /// Checks if scalar multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat1 = MatZq::from_str("[[42],[0],[2]] mod 61").unwrap();
        let mat2 = MatZq::from_str("[[2, 6, 5],[4, 42, 3]] mod 61").unwrap();
        let mat3 = MatZq::from_str("[[84],[0],[4]] mod 61").unwrap();
        let mat4 = MatZq::from_str("[[4, 12, 10],[8, 84, 6]] mod 61").unwrap();
        let integer = Z::from(2);

        assert_eq!(mat3, &integer * mat1);
        assert_eq!(mat4, integer * mat2);
    }

    /// Checks if matrix multiplication works fine for large values
    #[test]
    fn large_entries() {
        let mat1 = MatZq::from_str(&format!("[[1],[{}],[4]] mod {}", i64::MAX, u64::MAX)).unwrap();
        let mat2 = MatZq::from_str(&format!("[[3]] mod {}", u64::MAX)).unwrap();
        let mat3 =
            MatZq::from_str(&format!("[[3],[{}],[12]] mod {}", i64::MAX - 1, u64::MAX)).unwrap();
        let mat4 = MatZq::from_str(&format!("[[{}]] mod {}", i64::MAX - 1, u64::MAX)).unwrap();
        let integer1 = Z::from(3);
        let integer2 = Z::from(i64::MAX);

        assert_eq!(mat3, integer1 * mat1);
        assert_eq!(mat4, integer2 * mat2);
    }
}

#[cfg(test)]
mod test_mul_zq {
    use crate::integer_mod_q::{MatZq, Zq};
    use std::str::FromStr;

    /// Checks if matrix multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let mat1 = MatZq::from_str("[[42, 17],[8, 6]] mod 61").unwrap();
        let mat2 = mat1.clone();
        let mat3 = MatZq::from_str("[[84, 34],[16, 12]] mod 61").unwrap();
        let integer = Zq::try_from((2, 61)).unwrap();

        let mat1 = &mat1 * &integer;
        let mat2 = &integer * &mat2;

        assert_eq!(mat3, mat1);
        assert_eq!(mat3, mat2);
    }

    /// Checks if scalar multiplication works fine for both owned
    #[test]
    fn owned_correctness() {
        let mat1 = MatZq::from_str("[[42, 17],[8, 6]] mod 61").unwrap();
        let mat2 = mat1.clone();
        let mat3 = MatZq::from_str("[[84, 34],[16, 12]] mod 61").unwrap();
        let integer1 = Zq::try_from((2, 61)).unwrap();
        let integer2 = Zq::try_from((2, 61)).unwrap();

        let mat1 = mat1 * integer1;
        let mat2 = integer2 * mat2;

        assert_eq!(mat3, mat1);
        assert_eq!(mat3, mat2);
    }

    /// Checks if scalar multiplication works fine for half owned/borrowed
    #[test]
    fn half_correctness() {
        let mat1 = MatZq::from_str("[[42, 17],[8, 6]] mod 61").unwrap();
        let mat2 = mat1.clone();
        let mat3 = mat1.clone();
        let mat4 = mat1.clone();
        let mat5 = MatZq::from_str("[[84, 34],[16, 12]] mod 61").unwrap();
        let integer1 = Zq::try_from((2, 61)).unwrap();
        let integer2 = Zq::try_from((2, 61)).unwrap();

        let mat1 = mat1 * &integer1;
        let mat2 = &integer2 * mat2;
        let mat3 = &mat3 * integer1;
        let mat4 = integer2 * &mat4;

        assert_eq!(mat5, mat1);
        assert_eq!(mat5, mat2);
        assert_eq!(mat5, mat3);
        assert_eq!(mat5, mat4);
    }

    /// Checks if scalar multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat1 = MatZq::from_str("[[42],[0],[2]] mod 61").unwrap();
        let mat2 = MatZq::from_str("[[2, 6, 5],[4, 42, 3]] mod 61").unwrap();
        let mat3 = MatZq::from_str("[[84],[0],[4]] mod 61").unwrap();
        let mat4 = MatZq::from_str("[[4, 12, 10],[8, 84, 6]] mod 61").unwrap();
        let integer = Zq::try_from((2, 61)).unwrap();

        assert_eq!(mat3, &integer * mat1);
        assert_eq!(mat4, integer * mat2);
    }

    /// Checks if matrix multiplication works fine for large values
    #[test]
    fn large_entries() {
        let mat1 = MatZq::from_str(&format!("[[1],[{}],[4]] mod {}", i64::MAX, u64::MAX)).unwrap();
        let mat2 = MatZq::from_str(&format!("[[3]] mod {}", u64::MAX)).unwrap();
        let mat3 =
            MatZq::from_str(&format!("[[3],[{}],[12]] mod {}", i64::MAX - 1, u64::MAX)).unwrap();
        let mat4 = MatZq::from_str(&format!("[[{}]] mod {}", i64::MAX - 1, u64::MAX)).unwrap();
        let integer1 = Zq::try_from((3, u64::MAX)).unwrap();
        let integer2 = Zq::try_from((i64::MAX, u64::MAX)).unwrap();

        assert_eq!(mat3, integer1 * mat1);
        assert_eq!(mat4, integer2 * mat2);
    }

    /// Checks if scalar multiplication panics if the moduli mismatch
    #[test]
    #[should_panic]
    fn different_moduli_error() {
        let mat1 = MatZq::from_str("[[42],[0],[2]] mod 61").unwrap();
        let integer = Zq::try_from((2, 3)).unwrap();

        _ = &integer * mat1;
    }

    /// Checks if scalar multiplication panics if the moduli mismatch
    #[test]
    fn different_moduli_error_safe() {
        let mat1 = MatZq::from_str("[[42],[0],[2]] mod 61").unwrap();
        let integer = Zq::try_from((2, 3)).unwrap();

        let mat2 = &mat1.mul_scalar_safe(&integer);

        assert!(mat2.is_err());
    }
}
