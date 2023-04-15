// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the `tensor` product.

use super::MatZq;
use crate::{
    error::MathError,
    traits::{GetNumColumns, GetNumRows, Tensor},
};
use flint_sys::{
    fmpz::{fmpz, fmpz_is_zero},
    fmpz_mat::fmpz_mat_entry,
    fmpz_mod::fmpz_mod_mul,
};

impl Tensor for MatZq {
    /// Computes the tensor product of `self` with `other`
    ///
    /// Parameters:
    /// - `other`: the value with which the tensor product is computed.
    ///
    /// Returns the tensor product of `self` with `other` and panics if the
    /// moduli of the provided matrices mismatch.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use qfall_math::traits::Tensor;
    /// use std::str::FromStr;
    ///
    /// let mat_1 = MatZq::from_str("[[1, 0, 0],[0, 1, 0],[0, 0, 1]] mod 7").unwrap();
    /// let mat_2 = MatZq::from_str("[[1, 2, 1],[3, 4, 1]] mod 7").unwrap();
    ///
    /// let mat_3 = mat_1.tensor(&mat_2);
    /// ```
    ///
    /// # Panics ...
    /// - ... if the moduli of both matrices mismatch.
    fn tensor(&self, other: &Self) -> Self {
        self.tensor_safe(other).unwrap()
    }
}

impl MatZq {
    /// Computes the tensor product of `self` with `other`
    ///
    /// Parameters:
    /// - `other`: the value with which the tensor product is computed.
    ///
    /// Returns the tensor product of `self` with `other` and or an error if the
    /// moduli of the provided matrices mismatch.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let mat_1 = MatZq::from_str("[[1, 0, 0],[0, 1, 0],[0, 0, 1]] mod 7").unwrap();
    /// let mat_2 = MatZq::from_str("[[1, 2, 1],[3, 4, 1]] mod 7").unwrap();
    ///
    /// let mat_3 = mat_1.tensor_safe(&mat_2).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`MismatchingModulus`](MathError::MismatchingModulus) if the
    /// moduli of the provided matrices mismatch.
    pub fn tensor_safe(&self, other: &Self) -> Result<Self, MathError> {
        if self.get_mod() != other.get_mod() {
            return Err(MathError::MismatchingModulus(format!(
                " Tried to compute tensor product of matrixes with moduli '{}' and '{}'.",
                self.get_mod(),
                other.get_mod()
            )));
        }

        // does not have to be mutable, since the pointers themselves
        // do not change, only the content behind the pointers.
        let out = MatZq::new(
            self.get_num_rows() * other.get_num_rows(),
            self.get_num_columns() * other.get_num_columns(),
            self.get_mod(),
        )
        .unwrap();

        for i in 0..self.get_num_rows() {
            for j in 0..self.get_num_columns() {
                let entry = unsafe { fmpz_mat_entry(&self.matrix.mat[0], i, j) };

                if unsafe { 1 != fmpz_is_zero(entry) } {
                    unsafe { set_matrix_window_mul(&out, i, j, entry, other) }
                }
            }
        }

        Ok(out)
    }
}

/// This function sets a specific window of the provided matrix `out`
/// according to the `scalar` multiple of `matrix` reduced by the modulus.
///
/// Sets the entries
/// `[i*rows_other, j*columns_other]` up till `[row_left*(row_other +1), column_upper*(columns_other + 1)]`
///
/// Parameters:
/// - `out`: the matrix in which the result is saved, which also holds the modulus
/// (**Warning**: even though `out` is not mutable, the subpart of the matrix is still
/// set since the content behind the pointers changes but not the pointers themselves.)
/// - `row_left`: defines the leftmost row of the set window
/// - `column_upper`: defines the highest column of the set window
/// - `scalar`: defines the value with which the part of the tensor product
/// is calculated
/// - `matrix`: the matrix with which the scalar is multiplied
/// before setting the entries in `out`
///
/// Implicitly sets the entries of the matrix according to the definition
/// of the tensor product.
unsafe fn set_matrix_window_mul(
    out: &MatZq,
    row_left: i64,
    column_upper: i64,
    scalar: *mut fmpz,
    matrix: &MatZq,
) {
    let columns_other = matrix.get_num_columns();
    let rows_other = matrix.get_num_rows();

    for i_other in 0..rows_other {
        for j_other in 0..columns_other {
            unsafe {
                fmpz_mod_mul(
                    fmpz_mat_entry(
                        &out.matrix.mat[0],
                        row_left * rows_other + i_other,
                        column_upper * columns_other + j_other,
                    ),
                    scalar,
                    fmpz_mat_entry(&matrix.matrix.mat[0], i_other, j_other),
                    out.get_mod().get_fmpz_mod_ctx_struct(),
                )
            }
        }
    }
}

#[cfg(test)]
mod test_tensor {
    use crate::{
        integer_mod_q::MatZq,
        traits::{GetNumColumns, GetNumRows, Tensor},
    };
    use std::str::FromStr;

    /// ensure that the dimensions of the tensor product are taken over correctly.
    #[test]
    fn dimensions_fit() {
        let mat_1 = MatZq::new(17, 13, 13).unwrap();
        let mat_2 = MatZq::new(3, 4, 13).unwrap();

        let mat_3 = mat_1.tensor(&mat_2);
        let mat_3_safe = mat_1.tensor_safe(&mat_2).unwrap();

        assert_eq!(51, mat_3.get_num_rows());
        assert_eq!(52, mat_3.get_num_columns());
        assert_eq!(51, mat_3_safe.get_num_rows());
        assert_eq!(52, mat_3_safe.get_num_columns());
    }

    /// ensure that the tensor works correctly with identity
    #[test]
    fn identity() {
        let identity = MatZq::from_str(&format!("[[1, 0],[0, 1]] mod {}", u128::MAX)).unwrap();
        let mat_1 = MatZq::from_str(&format!(
            "[[1, {}, 1],[0, {}, -1]] mod {}",
            u64::MAX,
            i64::MIN,
            u128::MAX
        ))
        .unwrap();

        let mat_2 = identity.tensor(&mat_1);
        let mat_3 = mat_1.tensor(&identity);
        let mat_2_safe = identity.tensor_safe(&mat_1).unwrap();
        let mat_3_safe = mat_1.tensor_safe(&identity).unwrap();

        let cmp_mat_2 = MatZq::from_str(&format!(
            "[[1, {}, 1, 0, 0, 0],[0, {}, -1, 0, 0, 0],[0, 0, 0, 1, {}, 1],[0, 0, 0, 0, {}, -1]] mod {}",
            u64::MAX,
            i64::MIN,
            u64::MAX,
            i64::MIN,
            u128::MAX
        ))
        .unwrap();
        let cmp_mat_3 = MatZq::from_str(&format!(
            "[[1, 0, {}, 0, 1, 0],[0, 1, 0, {}, 0, 1],[0, 0, {}, 0, -1, 0],[0, 0, 0, {}, 0, -1]] mod {}",
            u64::MAX,
            u64::MAX,
            i64::MIN,
            i64::MIN,
            u128::MAX
        ))
        .unwrap();

        assert_eq!(cmp_mat_2, mat_2);
        assert_eq!(cmp_mat_3, mat_3);
        assert_eq!(cmp_mat_2, mat_2_safe);
        assert_eq!(cmp_mat_3, mat_3_safe);
    }

    /// ensure the tensor product works where one is a vector and the other is a matrix
    #[test]
    fn vector_matrix() {
        let vector = MatZq::from_str(&format!("[[1],[-1]] mod {}", u128::MAX)).unwrap();
        let mat_1 = MatZq::from_str(&format!(
            "[[1, {}, 1],[0, {}, -1]] mod {}",
            u64::MAX,
            i64::MAX,
            u128::MAX
        ))
        .unwrap();

        let mat_2 = vector.tensor(&mat_1);
        let mat_3 = mat_1.tensor(&vector);
        let mat_2_safe = vector.tensor_safe(&mat_1).unwrap();
        let mat_3_safe = mat_1.tensor_safe(&vector).unwrap();

        let cmp_mat_2 = MatZq::from_str(&format!(
            "[[1, {}, 1],[0, {}, -1],[-1, -{}, -1],[0, -{}, 1]] mod {}",
            u64::MAX,
            i64::MAX,
            u64::MAX,
            i64::MAX,
            u128::MAX
        ))
        .unwrap();
        let cmp_mat_3 = MatZq::from_str(&format!(
            "[[1, {}, 1],[-1, -{}, -1],[0, {}, -1],[0, -{}, 1]] mod {}",
            u64::MAX,
            u64::MAX,
            i64::MAX,
            i64::MAX,
            u128::MAX
        ))
        .unwrap();

        assert_eq!(cmp_mat_2, mat_2);
        assert_eq!(cmp_mat_3, mat_3);
        assert_eq!(cmp_mat_2, mat_2_safe);
        assert_eq!(cmp_mat_3, mat_3_safe);
    }

    /// ensure that the tensor product works correctly with two vectors
    #[test]
    fn vector_vector() {
        let vec_1 = MatZq::from_str(&format!("[[2],[1]] mod {}", u128::MAX)).unwrap();
        let vec_2 = MatZq::from_str(&format!(
            "[[{}],[{}]] mod {}",
            (u64::MAX - 1) / 2,
            i64::MIN / 2,
            u128::MAX
        ))
        .unwrap();

        let vec_3 = vec_1.tensor(&vec_2);
        let vec_4 = vec_2.tensor(&vec_1);
        let vec_3_safe = vec_1.tensor_safe(&vec_2).unwrap();
        let vec_4_safe = vec_2.tensor_safe(&vec_1).unwrap();

        let cmp_vec_3 = MatZq::from_str(&format!(
            "[[{}],[{}],[{}],[{}]] mod {}",
            u64::MAX - 1,
            i64::MIN,
            (u64::MAX - 1) / 2,
            i64::MIN / 2,
            u128::MAX
        ))
        .unwrap();
        let cmp_vec_4 = MatZq::from_str(&format!(
            "[[{}],[{}],[{}],[{}]] mod {}",
            u64::MAX - 1,
            (u64::MAX - 1) / 2,
            i64::MIN,
            i64::MIN / 2,
            u128::MAX
        ))
        .unwrap();

        assert_eq!(cmp_vec_3, vec_3);
        assert_eq!(cmp_vec_4, vec_4);
        assert_eq!(cmp_vec_3, vec_3_safe);
        assert_eq!(cmp_vec_4, vec_4_safe);
    }

    /// ensure that entries are reduced by the modulus
    #[test]
    fn entries_reduced() {
        let mat_1 = MatZq::from_str(&format!("[[1, 2],[3, 4]] mod {}", u64::MAX - 58)).unwrap();
        let mat_2 = MatZq::from_str(&format!(
            "[[1, {}],[0, {}]] mod {}",
            u64::MAX,
            u64::MAX - 59,
            u64::MAX - 58
        ))
        .unwrap();

        let mat_3 = mat_1.tensor(&mat_2);
        let mat_3_safe = mat_1.tensor_safe(&mat_2).unwrap();

        let mat_3_cmp = MatZq::from_str(&format!(
            "[[1, 58, 2, 116],[0, {}, 0, {}],[3, 174, 4, 232],[0, {}, 0, {}]] mod {}",
            u64::MAX - 59,
            u64::MAX - 60,
            u64::MAX - 61,
            u64::MAX - 62,
            u64::MAX - 58
        ))
        .unwrap();
        assert_eq!(mat_3_cmp, mat_3);
        assert_eq!(mat_3_cmp, mat_3_safe);
    }

    /// ensure that tensor panics if the moduli mismatch
    #[test]
    #[should_panic]
    fn mismatching_moduli_tensor() {
        let mat_1 = MatZq::new(1, 2, u64::MAX).unwrap();
        let mat_2 = MatZq::new(1, 2, u64::MAX - 58).unwrap();

        let _ = mat_1.tensor(&mat_2);
    }

    /// ensure that tensor_safe returns an error if the moduli mismatch
    #[test]
    fn mismatching_moduli_tensor_safe() {
        let mat_1 = MatZq::new(1, 2, u64::MAX).unwrap();
        let mat_2 = MatZq::new(1, 2, u64::MAX - 58).unwrap();

        assert!(mat_1.tensor_safe(&mat_2).is_err());
        assert!(mat_2.tensor_safe(&mat_1).is_err());
    }
}
