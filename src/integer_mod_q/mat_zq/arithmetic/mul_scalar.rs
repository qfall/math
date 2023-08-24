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
    /// let mat_2 = &mat_1.mul_scalar_safe(&integer).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`MismatchingModulus`](MathError::MismatchingModulus) if the moduli mismatch.
    pub fn mul_scalar_safe(&self, scalar: &Zq) -> Result<Self, MathError> {
        if self.modulus != scalar.modulus {
            return Err(MathError::MismatchingModulus(format!(
                "Tried to multiply scalar with modulus '{}' and matrices with modulus '{}'.",
                self.get_mod(),
                scalar.modulus
            )));
        }

        let mut out = MatZq::new(self.get_num_rows(), self.get_num_columns(), self.get_mod());
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

    /// Checks if scalar multiplication panics if the moduli mismatch
    #[test]
    fn different_moduli_error_safe() {
        let mat_1 = MatZq::from_str("[[42],[0],[2]] mod 61").unwrap();
        let integer = Zq::from((2, 3));

        let mat_2 = &mat_1.mul_scalar_safe(&integer);

        assert!(mat_2.is_err());
    }
}
