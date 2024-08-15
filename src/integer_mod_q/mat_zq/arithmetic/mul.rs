// Copyright © 2023 Marcel Luca Schmidt, Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Mul`] trait for [`MatZq`] values.

use super::super::MatZq;
use crate::error::MathError;
use crate::integer::MatZ;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    arithmetic_trait_reverse,
};
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpz_mat::fmpz_mat_mul;
use flint_sys::fmpz_mod_mat::{_fmpz_mod_mat_reduce, fmpz_mod_mat_mul};
use std::ops::Mul;

impl Mul for &MatZq {
    type Output = MatZq;

    /// Implements the [`Mul`] trait for two [`MatZq`] values.
    ///
    /// [`Mul`] is implemented for any combination of owned and borrowed [`MatZq`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of `self` and `other` as a [`MatZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let a = MatZq::from_str("[[2, 1],[1, 2]] mod 3").unwrap();
    /// let b = MatZq::from_str("[[1, 0],[0, 1]] mod 3").unwrap();
    ///
    /// let c = &a * &b;
    /// let d = a * b;
    /// let e = &c * d;
    /// let f = c * &e;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of `self` and `other` do not match for multiplication.
    /// - if the moduli mismatch.
    fn mul(self, other: Self) -> Self::Output {
        self.mul_safe(other).unwrap()
    }
}

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatZq, MatZq, MatZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatZq, MatZq, MatZq);

impl Mul<&MatZ> for &MatZq {
    type Output = MatZq;

    /// Implements the [`Mul`] trait for [`MatZq`] and [`MatZ`].
    ///
    /// [`Mul`] is implemented for any combination of owned and borrowed [`MatZq`] and [`MatZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of `self` and `other` as a [`MatZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let a = MatZq::from_str("[[2, 1],[1, 2]] mod 3").unwrap();
    /// let b = MatZ::identity(2, 2);
    ///
    /// let c = &a * &b;
    /// let d = a * b;
    /// let e = &MatZ::identity(2, 2); * d;
    /// let f = MatZ::identity(2, 2); * &e;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of `self` and `other` do not match for multiplication.
    fn mul(self, other: &MatZ) -> Self::Output {
        assert_eq!(
            self.get_num_columns(),
            other.get_num_rows(),
            "Tried to multiply matrices with mismatching matrix dimensions."
        );

        let mut new = MatZq::new(self.get_num_rows(), other.get_num_columns(), self.get_mod());
        unsafe {
            fmpz_mat_mul(&mut new.matrix.mat[0], &self.matrix.mat[0], &other.matrix);
            _fmpz_mod_mat_reduce(&mut new.matrix)
        }
        new
    }
}

arithmetic_trait_reverse!(Mul, mul, MatZ, MatZq, MatZq);

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatZq, MatZ, MatZq);
arithmetic_trait_borrowed_to_owned!(Mul, mul, MatZ, MatZq, MatZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatZq, MatZ, MatZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatZ, MatZq, MatZq);

impl MatZq {
    /// Implements multiplication for two [`MatZq`] values.
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of `self` and `other` as a [`MatZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let a = MatZq::from_str("[[2, 1],[1, 2]] mod 7").unwrap();
    /// let b = MatZq::from_str("[[1, 0],[0, 1]] mod 7").unwrap();
    ///
    /// let c: MatZq = a.mul_safe(&b).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///     [`MathError::MismatchingMatrixDimension`] if the dimensions of `self`
    ///     and `other` do not match for multiplication.
    /// - Returns a [`MathError`] of type
    ///     [`MathError::MismatchingModulus`] if the moduli mismatch.
    pub fn mul_safe(&self, other: &Self) -> Result<Self, MathError> {
        if self.modulus != other.modulus {
            return Err(MathError::MismatchingModulus(format!(
                "Tried to multiply matrices with moduli '{}' and '{}'.",
                self.get_mod(),
                other.get_mod()
            )));
        }
        if self.get_num_columns() != other.get_num_rows() {
            return Err(MathError::MismatchingMatrixDimension(format!(
                "Tried to multiply a '{}x{}' matrix and a '{}x{}' matrix.",
                self.get_num_rows(),
                self.get_num_columns(),
                other.get_num_rows(),
                other.get_num_columns()
            )));
        }

        let mut new = MatZq::new(self.get_num_rows(), other.get_num_columns(), self.get_mod());
        unsafe { fmpz_mod_mat_mul(&mut new.matrix, &self.matrix, &other.matrix) };
        Ok(new)
    }
}

#[cfg(test)]
mod test_mul {
    use super::MatZq;
    use crate::{integer::Z, traits::SetEntry};
    use std::str::FromStr;

    /// Checks if matrix multiplication works fine for squared matrices
    #[test]
    fn square_correctness() {
        let mat_1 = MatZq::from_str("[[2, 1],[1, 2]] mod 3").unwrap();
        let mat_2 = MatZq::from_str("[[1, 0],[0, 1]] mod 3").unwrap();
        let mat_3 = MatZq::from_str("[[1, 2],[2, 1]] mod 3").unwrap();
        let cmp = MatZq::from_str("[[4, 5],[2, 4]] mod 3").unwrap();

        assert_eq!(mat_1, &mat_1 * &mat_2);
        assert_eq!(cmp, &mat_1 * &mat_3);
    }

    /// Checks if matrix multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat = MatZq::from_str("[[2, 1],[1, 2]] mod 3").unwrap();
        let vec = MatZq::from_str("[[2],[0]] mod 3").unwrap();
        let cmp = MatZq::from_str("[[1],[2]] mod 3").unwrap();

        assert_eq!(cmp, &mat * &vec);
    }

    /// Checks if matrix multiplication works fine for large entries
    #[test]
    fn large_entries() {
        let mat =
            MatZq::from_str(&format!("[[{}, 1],[0, 2]] mod {}", u64::MAX, u64::MAX - 58)).unwrap();
        let vec = MatZq::from_str(&format!("[[{}],[0]] mod {}", u64::MAX, u64::MAX - 58)).unwrap();
        let mut cmp = MatZq::new(2, 1, u64::MAX - 58);
        let max: Z = u64::MAX.into();
        cmp.set_entry(0, 0, &(&max * &max)).unwrap();

        assert_eq!(cmp, mat * vec);
    }

    /// Checks if matrix multiplication with incompatible matrix dimensions
    /// or mismatch moduli throws an error as expected
    #[test]
    fn errors() {
        let mat_1 = MatZq::from_str("[[2, 1],[1, 2]] mod 4").unwrap();
        let mat_2 = MatZq::from_str("[[1, 0],[0, 1],[0, 0]] mod 4").unwrap();
        let mat_3 = MatZq::from_str("[[2, 1],[1, 2]] mod 5").unwrap();
        assert!((mat_1.mul_safe(&mat_2)).is_err());
        assert!((mat_1.mul_safe(&mat_3)).is_err());
    }
}

#[cfg(test)]
mod test_mul_matz {
    use super::MatZq;
    use crate::integer::MatZ;
    use crate::{integer::Z, traits::SetEntry};
    use std::str::FromStr;

    /// Checks if matrix multiplication works fine for squared matrices
    #[test]
    fn square_correctness() {
        let mat_1 = MatZq::from_str("[[2, 1],[1, 2]] mod 3").unwrap();
        let mat_2 = MatZ::identity(2, 2);
        let mat_3 = MatZ::from_str("[[1, 2],[2, 1]]").unwrap();
        let cmp = MatZq::from_str("[[4, 5],[2, 4]] mod 3").unwrap();

        assert_eq!(mat_1, &mat_1 * &mat_2);
        assert_eq!(cmp, &mat_1 * &mat_3);
    }

    /// Checks if matrix multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat = MatZq::from_str("[[2, 1],[1, 2]] mod 3").unwrap();
        let vec = MatZ::from_str("[[2],[0]]").unwrap();
        let cmp = MatZq::from_str("[[1],[2]] mod 3").unwrap();

        assert_eq!(cmp, &mat * &vec);
        assert_eq!(cmp, &vec * &mat);
    }

    /// Checks if matrix multiplication works fine for large entries
    #[test]
    fn large_entries() {
        let mat =
            MatZq::from_str(&format!("[[{}, 1],[0, 2]] mod {}", u64::MAX, u64::MAX - 58)).unwrap();
        let vec = MatZ::from_str(&format!("[[{}],[0]]", u64::MAX)).unwrap();
        let mut cmp = MatZq::new(2, 1, u64::MAX - 58);
        let max: Z = u64::MAX.into();
        cmp.set_entry(0, 0, &(&max * &max)).unwrap();

        assert_eq!(cmp, &mat * &vec);
        assert_eq!(cmp, vec * mat);
    }

    /// Checks if matrix multiplication with incompatible matrix dimensions
    /// throws an error as expected
    #[test]
    #[should_panic]
    fn errors() {
        let mat_1 = MatZq::from_str("[[2, 1],[1, 2]] mod 4").unwrap();
        let mat_2 = MatZ::from_str("[[1, 0],[0, 1],[0, 0]]").unwrap();
        let _ = &mat_1 * &mat_2;
    }
}
