// Copyright © 2023 Niklas Siemer, Phil Milewski, Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Mul`] trait for [`MatZ`] values.

use super::super::MatZ;
use crate::error::MathError;
use crate::integer_mod_q::MatZq;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use crate::rational::MatQ;
use crate::traits::MatrixDimensions;
use flint_sys::fmpq_mat::fmpq_mat_mul_r_fmpz_mat;
use flint_sys::fmpz_mat::fmpz_mat_mul;
use flint_sys::fmpz_mod_mat::_fmpz_mod_mat_reduce;
use std::ops::Mul;

impl Mul for &MatZ {
    type Output = MatZ;

    /// Implements the [`Mul`] trait for two [`MatZ`] values.
    /// [`Mul`] is implemented for any combination of [`MatZ`] and borrowed [`MatZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of `self` and `other` as a [`MatZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let a = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
    /// let b = MatZ::identity(2, 2);
    ///
    /// let c = &a * &b;
    /// let d = a * b;
    /// let e = &c * d;
    /// let f = c * &e;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of `self` and `other` do not match for multiplication.
    fn mul(self, other: Self) -> Self::Output {
        self.mul_safe(other).unwrap()
    }
}

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatZ, MatZ, MatZ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatZ, MatZ, MatZ);

impl Mul<&MatZq> for &MatZ {
    type Output = MatZq;

    /// Implements the [`Mul`] trait for [`MatZ`] and [`MatZq`].
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
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
    /// let a = MatZ::identity(2, 2);
    /// let b = MatZq::from_str("[[2, 1],[1, 2]] mod 3").unwrap();
    ///
    /// let c = &a * &b;
    /// let d = a * b;
    /// let e = &MatZ::identity(2, 2) * d;
    /// let f = MatZ::identity(2, 2) * &e;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of `self` and `other` do not match for multiplication.
    fn mul(self, other: &MatZq) -> Self::Output {
        assert_eq!(
            self.get_num_columns(),
            other.get_num_rows(),
            "Tried to multiply matrices with mismatching matrix dimensions."
        );

        let mut new = MatZq::new(
            self.get_num_rows(),
            other.get_num_columns(),
            other.get_mod(),
        );
        unsafe {
            fmpz_mat_mul(&mut new.matrix.mat[0], &self.matrix, &other.matrix.mat[0]);
            _fmpz_mod_mat_reduce(&mut new.matrix)
        }
        new
    }
}

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatZ, MatZq, MatZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatZ, MatZq, MatZq);

impl Mul<&MatQ> for &MatZ {
    type Output = MatQ;

    /// Implements the [`Mul`] trait for [`MatZ`] and [`MatQ`].
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of `self` and `other` as a [`MatQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let a = MatZ::identity(2, 2);
    /// let b = MatQ::from_str("[[2/3, 1/2],[8/4, 7]]").unwrap();
    ///
    ///
    /// let c = &a * &b;
    /// let d = a * b;
    /// let e = &MatZ::identity(2, 2) * c;
    /// let f = MatZ::identity(2, 2) * &e;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of `self` and `other` do not match for multiplication.
    fn mul(self, other: &MatQ) -> Self::Output {
        assert_eq!(
            self.get_num_columns(),
            other.get_num_rows(),
            "Tried to multiply matrices with mismatching matrix dimensions."
        );

        let mut new = MatQ::new(self.get_num_rows(), other.get_num_columns());
        unsafe { fmpq_mat_mul_r_fmpz_mat(&mut new.matrix, &self.matrix, &other.matrix) };
        new
    }
}

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatZ, MatQ, MatQ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatZ, MatQ, MatQ);

impl MatZ {
    /// Implements multiplication for two [`MatZ`] values.
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of `self` and `other` as a [`MatZ`] or
    /// an error, if the dimensions of `self` and `other` do not match for multiplication.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let a = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
    /// let b = MatZ::identity(2, 2);
    ///
    /// let c: MatZ = a.mul_safe(&b).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///     [`MathError::MismatchingMatrixDimension`] if the dimensions of `self`
    ///     and `other` do not match for multiplication.
    pub fn mul_safe(&self, other: &Self) -> Result<Self, MathError> {
        if self.get_num_columns() != other.get_num_rows() {
            return Err(MathError::MismatchingMatrixDimension(format!(
                "Tried to multiply a '{}x{}' matrix and a '{}x{}' matrix.",
                self.get_num_rows(),
                self.get_num_columns(),
                other.get_num_rows(),
                other.get_num_columns()
            )));
        }

        let mut new = MatZ::new(self.get_num_rows(), other.get_num_columns());
        unsafe { fmpz_mat_mul(&mut new.matrix, &self.matrix, &other.matrix) };
        Ok(new)
    }
}

#[cfg(test)]
mod test_mul {
    use super::MatZ;
    use crate::{integer::Z, traits::SetEntry};
    use std::str::FromStr;

    /// Checks if matrix multiplication works fine for squared matrices
    #[test]
    fn square_correctness() {
        let mat_1 = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
        let mat_2 = MatZ::identity(2, 2);
        let mat_3 = MatZ::from_str("[[1, 2],[2, 1]]").unwrap();
        let cmp = MatZ::from_str("[[4, 5],[5, 4]]").unwrap();

        assert_eq!(mat_1, &mat_1 * &mat_2);
        assert_eq!(cmp, &mat_1 * &mat_3);
    }

    /// Checks if matrix multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
        let vec = MatZ::from_str("[[1],[0]]").unwrap();
        let cmp = MatZ::from_str("[[2],[1]]").unwrap();

        assert_eq!(cmp, &mat * &vec);
    }

    /// Checks if matrix multiplication works fine for large entries
    #[test]
    fn large_entries() {
        let mat = MatZ::from_str(&format!("[[{}, 1],[0, 2]]", i64::MAX)).unwrap();
        let vec = MatZ::from_str(&format!("[[{}],[0]]", i64::MAX)).unwrap();
        let mut cmp = MatZ::new(2, 1);
        let max: Z = i64::MAX.into();
        cmp.set_entry(0, 0, &(&max * &max)).unwrap();

        assert_eq!(cmp, mat * vec);
    }

    /// Checks if matrix multiplication with incompatible matrix dimensions
    /// throws an error as expected
    #[test]
    fn incompatible_dimensions() {
        let mat_1 = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
        let mat_2 = MatZ::from_str("[[1, 0],[0, 1],[0, 0]]").unwrap();

        assert!((mat_1.mul_safe(&mat_2)).is_err());
    }
}

#[cfg(test)]
mod test_mul_matzq {
    use super::MatZq;
    use crate::integer::MatZ;
    use crate::{integer::Z, traits::SetEntry};
    use std::str::FromStr;

    /// Checks if matrix multiplication works fine for squared matrices
    #[test]
    fn square_correctness() {
        let mat_1 = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
        let mat_2 = MatZq::identity(2, 2, 3);
        let mat_3 = MatZq::from_str("[[1, 2],[2, 1]] mod 3").unwrap();
        let cmp = MatZq::from_str("[[4, 5],[2, 4]] mod 3").unwrap();

        assert_eq!(MatZq::from((&mat_1, 3)), &mat_1 * &mat_2);
        assert_eq!(cmp, &mat_1 * &mat_3);
    }

    /// Checks if matrix multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat = MatZq::from_str("[[2, 1],[1, 2]] mod 3").unwrap();
        let vec = MatZ::from_str("[[2, 0]]").unwrap();
        let cmp = MatZq::from_str("[[4, 2]] mod 3").unwrap();

        assert_eq!(cmp, &vec * &mat);
    }

    /// Checks if matrix multiplication works fine for large entries
    #[test]
    fn large_entries() {
        let mat =
            MatZq::from_str(&format!("[[{}, 0],[1, 2]] mod {}", u64::MAX, u64::MAX - 58)).unwrap();
        let vec = MatZ::from_str(&format!("[[{}, 0]]", u64::MAX)).unwrap();
        let mut cmp = MatZq::new(1, 2, u64::MAX - 58);
        let max: Z = u64::MAX.into();
        cmp.set_entry(0, 0, &(&max * &max)).unwrap();

        assert_eq!(cmp, vec * mat);
    }

    /// Checks if matrix multiplication with incompatible matrix dimensions
    /// throws an error as expected
    #[test]
    #[should_panic]
    fn errors() {
        let mat_1 = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
        let mat_2 = MatZq::from_str("[[1, 0],[0, 1],[0, 0]] mod 4").unwrap();
        let _ = &mat_1 * &mat_2;
    }
}

#[cfg(test)]
mod test_mul_matq {
    use super::MatQ;
    use crate::integer::MatZ;
    use crate::rational::Q;
    use crate::traits::SetEntry;
    use std::str::FromStr;

    /// Checks if matrix multiplication works fine for squared matrices
    #[test]
    fn square_correctness() {
        let mat_1 = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();
        let mat_2 = MatZ::identity(2, 2);
        let mat_3 = MatZ::from_str("[[1, 2],[2, 1]]").unwrap();
        let cmp = MatQ::from_str("[[5/3, 5],[11/6, 4]]").unwrap();

        assert_eq!(mat_1, &mat_2 * &mat_1);
        assert_eq!(cmp, &mat_3 * &mat_1);
    }

    /// Checks if matrix multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();
        let vec = MatZ::from_str("[[2, 0]]").unwrap();
        let cmp = MatQ::from_str("[[4/3, 2]]").unwrap();

        assert_eq!(cmp, &vec * &mat);
    }

    /// Checks if matrix multiplication works fine for large entries
    #[test]
    fn large_entries() {
        let mat = MatQ::from_str(&format!("[[{}, 0],[1, 2/{}]]", u64::MAX, u64::MAX)).unwrap();
        let vec = MatZ::from_str(&format!("[[{}, 0]]", u64::MAX)).unwrap();
        let mut cmp = MatQ::new(1, 2);
        let max: Q = u64::MAX.into();
        cmp.set_entry(0, 0, &(&max * &max)).unwrap();

        assert_eq!(cmp, vec * mat);
    }

    /// Checks if matrix multiplication with incompatible matrix dimensions
    /// throws an error as expected
    #[test]
    #[should_panic]
    fn errors() {
        let mat_1 = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
        let mat_2 = MatQ::from_str("[[2/3, 0],[0, 1/2],[0, 0]]").unwrap();
        let _ = &mat_1 * &mat_2;
    }
}
