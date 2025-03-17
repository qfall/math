// Copyright © 2023 Marcel Luca Schmidt, Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Mul`] trait for [`MatQ`] values.

use super::super::MatQ;
use crate::error::MathError;
use crate::integer::MatZ;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use crate::traits::{MatrixDimensions, MatrixSetEntry};
use flint_sys::fmpq_mat::{fmpq_mat_mul, fmpq_mat_mul_fmpz_mat};
use std::ops::Mul;

impl Mul for &MatQ {
    type Output = MatQ;

    /// Implements the [`Mul`] trait for two [`MatQ`] values.
    /// [`Mul`] is implemented for any combination of owned and borrowed [`MatQ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of `self` and `other` as a [`MatQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let a: MatQ = MatQ::from_str("[[1/2, 2/3],[3/4, 5/7]]").unwrap();
    /// let b: MatQ = MatQ::from_str("[[1/4, 9/7],[1, 5]]").unwrap();
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

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatQ, MatQ, MatQ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatQ, MatQ, MatQ);

impl Mul<&MatZ> for &MatQ {
    type Output = MatQ;

    /// Implements the [`Mul`] trait for [`MatQ`] and [`MatZ`].
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
    /// let a = MatQ::from_str("[[2/3, 1/2],[8/4, 7]]").unwrap();
    /// let b = MatZ::identity(2, 2);
    ///
    /// let c = &a * &b;
    /// let d = a * b;
    /// let e = c * &MatZ::identity(2, 2);
    /// let f = &e * MatZ::identity(2, 2);
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

        let mut new = MatQ::new(self.get_num_rows(), other.get_num_columns());
        unsafe { fmpq_mat_mul_fmpz_mat(&mut new.matrix, &self.matrix, &other.matrix) };
        new
    }
}

impl MatQ {
    /// Multiplies the matrices `self` and `other` naively with each other
    /// using their [`f64`] presentation, i.e. with a small loss of precision.
    ///
    /// This function can speed up multiplications of [`MatQ`]'s as it allows for
    /// some loss of precision. The loss of precision depends on the size of the matrices
    /// and how exact the entries could be represented by a [`f64`].
    ///
    /// **WARNING:** This function is less efficient than [`Mul`] for integer values
    /// or entries with small numerators and denominators. This function becomes more
    /// efficient once `self` or `other` has entries with large numerators and denominators
    /// as FLINT's implementation does not allow any loss of precision.
    ///
    /// **WARNING:** Please be aware that the deviation of the representation of the matrices' entries as [`f64`]
    /// will scale with the size of the entries, e.g. an entry within the size of `2^{64}`
    /// might deviate from the original value by a distance of `1_000`. This loss of precision
    /// might be aggravated by this matrix multiplication with a factor of `self.get_num_columns()`
    /// for each entry in the resulting matrix.
    ///
    /// **WARNING:** This function is unchecked, i.e. the user is expected to align matrix
    /// dimensions for multiplication.
    ///  
    /// # Example
    /// ```
    /// use qfall_math::integer::MatZ;
    /// let mat = MatZ::sample_uniform(3, 3, -256, 256).unwrap().inverse().unwrap();
    ///
    /// let mat_inv_sqrd = mat.mul_f64_unchecked(&mat);
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of `self` and `other` do not match for multiplication.
    /// - if any result during the naive computation of matrix multiplication
    ///     is larger than [`f64::MAX`] or smaller than [`f64::MIN`].
    pub fn mul_f64_unchecked(&self, other: &Self) -> MatQ {
        let num_rows = self.get_num_rows() as usize;
        let num_cols = other.get_num_columns() as usize;

        let mat_self = self.collect_entries_f64();
        let mat_other = other.collect_entries_f64();

        let mut mat_out = MatQ::new(num_rows, num_cols);
        for (i, row) in mat_self.iter().enumerate() {
            for j in 0..num_cols {
                let mut entry = 0.0;
                for k in 0..self.get_num_columns() as usize {
                    entry += row[k] * mat_other[k][j];
                }
                mat_out.set_entry(i, j, entry).unwrap();
            }
        }

        mat_out
    }
}

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatQ, MatZ, MatQ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatQ, MatZ, MatQ);

impl MatQ {
    /// Implements multiplication for two [`MatQ`] values.
    ///
    /// Parameters:
    /// - `other`: specifies the value to multiply with `self`
    ///
    /// Returns the product of `self` and `other` as a [`MatQ`] or
    /// an error, if the dimensions of `self` and `other` do not match for multiplication.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let a: MatQ = MatQ::from_str("[[1/2, 2/3],[3/4, 4/5]]").unwrap();
    /// let b: MatQ = MatQ::from_str("[[1/4, 3/7],[1, 0]]").unwrap();
    ///
    /// let c: MatQ = a.mul_safe(&b).unwrap();
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

        let mut new = MatQ::new(self.get_num_rows(), other.get_num_columns());
        unsafe { fmpq_mat_mul(&mut new.matrix, &self.matrix, &other.matrix) };
        Ok(new)
    }
}

#[cfg(test)]
mod test_mul {
    use super::MatQ;
    use crate::{rational::Q, traits::MatrixSetEntry};
    use std::str::FromStr;

    /// Checks if matrix multiplication works fine for squared matrices
    #[test]
    fn square_correctness() {
        let mat_1 = MatQ::from_str("[[2/3, 1/3],[1/3, 2/3]]").unwrap();
        let mat_2 = MatQ::identity(2, 2);
        let mat_3 = MatQ::from_str("[[1/7, 2/7],[2/7, 1/7]]").unwrap();
        let cmp = MatQ::from_str("[[4/21, 5/21],[5/21, 4/21]]").unwrap();

        assert_eq!(mat_1, &mat_1 * &mat_2);
        assert_eq!(cmp, &mat_1 * &mat_3);
    }

    /// Checks if matrix multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat = MatQ::from_str("[[2/3, 1/5],[1/5, 2/19]]").unwrap();
        let vec = MatQ::from_str("[[1/7],[0]]").unwrap();
        let cmp = MatQ::from_str("[[2/21],[1/35]]").unwrap();

        assert_eq!(cmp, &mat * &vec);
    }

    /// Checks if matrix multiplication works fine for large entries
    #[test]
    fn large_entries() {
        let mat = MatQ::from_str(&format!("[[{}, 1],[0, 2]]", i64::MAX)).unwrap();
        let vec = MatQ::from_str(&format!("[[1/{}],[0]]", i64::MAX)).unwrap();
        let mut cmp = MatQ::new(2, 1);
        let max: Q = Q::from(i64::MAX);
        cmp.set_entry(0, 0, &(&max * Q::from((1, i64::MAX))))
            .unwrap();

        assert_eq!(cmp, mat * vec);
    }

    /// Checks if matrix multiplication with incompatible matrix dimensions
    /// throws an error as expected
    #[test]
    fn incompatible_dimensions() {
        let mat_1 = MatQ::from_str("[[2, 1/9],[1/7, 2]]").unwrap();
        let mat_2 = MatQ::from_str("[[1/6, 0],[0, 3/8],[0, 0]]").unwrap();

        assert!((mat_1.mul_safe(&mat_2)).is_err());
    }
}

#[cfg(test)]
mod test_mul_matz {
    use super::MatQ;
    use crate::integer::MatZ;
    use crate::rational::Q;
    use crate::traits::MatrixSetEntry;
    use std::str::FromStr;

    /// Checks if matrix multiplication works fine for squared matrices
    #[test]
    fn square_correctness() {
        let mat_1 = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();
        let mat_2 = MatZ::identity(2, 2);
        let mat_3 = MatZ::from_str("[[1, 2],[2, 1]]").unwrap();
        let cmp = MatQ::from_str("[[8/3, 7/3],[9/2, 3]]").unwrap();

        assert_eq!(mat_1, &mat_1 * &mat_2);
        assert_eq!(cmp, &mat_1 * &mat_3);
    }

    /// Checks if matrix multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();
        let vec = MatZ::from_str("[[2],[0]]").unwrap();
        let cmp = MatQ::from_str("[[4/3],[1]]").unwrap();

        assert_eq!(cmp, &mat * &vec);
    }

    /// Checks if matrix multiplication works fine for large entries
    #[test]
    fn large_entries() {
        let mat = MatQ::from_str(&format!("[[{}, 1],[0, 2/{}]]", u64::MAX, u64::MAX)).unwrap();
        let vec = MatZ::from_str(&format!("[[{}],[0]]", u64::MAX)).unwrap();
        let mut cmp = MatQ::new(2, 1);
        let max: Q = u64::MAX.into();
        cmp.set_entry(0, 0, &(&max * &max)).unwrap();

        assert_eq!(cmp, &mat * &vec);
    }

    /// Checks if matrix multiplication with incompatible matrix dimensions
    /// throws an error as expected
    #[test]
    #[should_panic]
    fn errors() {
        let mat_1 = MatQ::from_str("[[2/3, 1],[1/2, 2]]").unwrap();
        let mat_2 = MatZ::from_str("[[1, 0],[0, 1],[0, 0]]").unwrap();
        let _ = &mat_1 * &mat_2;
    }
}

#[cfg(test)]
mod test_mul_f64_unchecked {
    use crate::{
        rational::{MatQ, Q},
        traits::{Distance, MatrixGetEntry},
    };
    use std::str::FromStr;

    /// Ensures that the result of the multiplication is valid.
    #[test]
    fn correctness() {
        // If the entries of the matrix are changed to fractions that can't be represented
        // exactly by f64, the assertions need to be adapted to check for small losses.
        let mat_0 = MatQ::from_str("[[1,0],[0,1]]").unwrap();
        let mat_1 = MatQ::from_str("[[4,5],[5/10,-4/8],[-3,0]]").unwrap();
        let mat_2 = MatQ::from_str("[[-3/-4],[1/2]]").unwrap();

        assert_eq!(mat_0, mat_0.mul_f64_unchecked(&mat_0));
        assert_eq!(&mat_1 * &mat_0, mat_1.mul_f64_unchecked(&mat_0));
        assert_eq!(&mat_0 * &mat_2, mat_0.mul_f64_unchecked(&mat_2));
    }

    /// Ensures that the loss of precision is reasonable.
    /// This test just showcases / gives an idea that the loss of precision
    /// should be fairly irrelevant for most use-cases. Nevertheless,
    /// the loss of precision depends on the dimensions of the matrices
    /// and the loss of precision due to transforming to [`f64`].
    #[test]
    fn loss_of_precision() {
        let mat = MatQ::from_str(&format!("[[1/{},0],[0,-1/{}]]", u64::MAX, i64::MAX)).unwrap();
        let cmp_0 = Q::from((1, u64::MAX));
        let cmp_1 = Q::from((1, i64::MAX));
        let max_loss = Q::from((1, i64::MAX));

        let res = mat.mul_f64_unchecked(&mat);

        assert!(res.get_entry(0, 0).unwrap().distance(cmp_0) < max_loss);
        assert!(res.get_entry(1, 1).unwrap().distance(cmp_1) < max_loss);
    }

    /// Ensures that the function panics if invalid dimensions are input.
    #[test]
    #[should_panic]
    fn incorrect_dimensions() {
        let mat_0 = MatQ::identity(2, 3);
        let mat_1 = MatQ::new(1, 2);

        let _ = mat_0.mul_f64_unchecked(&mat_1);
    }
}
