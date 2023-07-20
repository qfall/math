// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the `tensor` product.

use super::MatPolyOverZ;
use crate::{
    integer::PolyOverZ,
    traits::{GetEntry, GetNumColumns, GetNumRows, Tensor},
};
use flint_sys::{fmpz_poly::fmpz_poly_mul, fmpz_poly_mat::fmpz_poly_mat_entry};

impl Tensor for MatPolyOverZ {
    /// Computes the tensor product of `self` with `other`
    ///
    /// Parameters:
    /// - `other`: the value with which the tensor product is computed.
    ///
    /// Returns the tensor product of `self` with `other`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use qfall_math::traits::Tensor;
    /// use std::str::FromStr;
    ///
    /// let mat_a = MatPolyOverZ::from_str("[[1  1, 2  1 1]]").unwrap();
    /// let mat_b = MatPolyOverZ::from_str("[[1  1, 1  2]]").unwrap();
    ///
    /// let mat_ab = mat_a.tensor_product(&mat_b);
    /// let res_ab = "[[1  1, 1  2, 2  1 1, 2  2 2]]";
    /// assert_eq!(mat_ab, MatPolyOverZ::from_str(res_ab).unwrap());
    ///
    /// let mat_ba = mat_b.tensor_product(&mat_a);
    /// let res_ba = "[[1  1, 2  1 1, 1  2, 2  2 2]]";
    /// assert_eq!(mat_ba, MatPolyOverZ::from_str(res_ba).unwrap());
    /// ```
    fn tensor_product(&self, other: &Self) -> Self {
        let mut out = MatPolyOverZ::new(
            self.get_num_rows() * other.get_num_rows(),
            self.get_num_columns() * other.get_num_columns(),
        );

        for i in 0..self.get_num_rows() {
            for j in 0..self.get_num_columns() {
                let entry = self.get_entry(i, j).unwrap();

                if !entry.is_zero() {
                    unsafe { set_matrix_window_mul(&mut out, i, j, entry, other) }
                }
            }
        }

        out
    }
}

/// This function sets a specific window of the provided matrix `out`
/// according to the `scalar` multiple of `matrix`.
///
/// Sets the entries
/// `[i*rows_other, j*columns_other]` up till `[row_left*(row_other +1), column_upper*(columns_other + 1)]`
///
/// Parameters:
/// - `out`: the matrix in which the result is saved
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
    out: &mut MatPolyOverZ,
    row_left: i64,
    column_upper: i64,
    scalar: PolyOverZ,
    matrix: &MatPolyOverZ,
) {
    let columns_other = matrix.get_num_columns();
    let rows_other = matrix.get_num_rows();

    for i_other in 0..rows_other {
        for j_other in 0..columns_other {
            unsafe {
                fmpz_poly_mul(
                    fmpz_poly_mat_entry(
                        &out.matrix,
                        row_left * rows_other + i_other,
                        column_upper * columns_other + j_other,
                    ),
                    &scalar.poly,
                    fmpz_poly_mat_entry(&matrix.matrix, i_other, j_other),
                )
            }
        }
    }
}

#[cfg(test)]
mod test_tensor {
    use crate::{
        integer::MatPolyOverZ,
        traits::{GetNumColumns, GetNumRows, Tensor},
    };
    use std::str::FromStr;

    /// Ensure that the dimensions of the tensor product are taken over correctly.
    #[test]
    fn dimensions_fit() {
        let mat_1 = MatPolyOverZ::new(17, 13);
        let mat_2 = MatPolyOverZ::new(3, 4);

        let mat_3 = mat_1.tensor_product(&mat_2);

        assert_eq!(51, mat_3.get_num_rows());
        assert_eq!(52, mat_3.get_num_columns());
    }

    /// Ensure that the tensor works correctly with identity
    #[test]
    fn identity() {
        let identity = MatPolyOverZ::from_str("[[1  1, 0],[0, 1  1]]").unwrap();
        let mat_1 = MatPolyOverZ::from_str(&format!(
            "[[1  1, 1  {}, 1  1],[0, 1  {}, 1  -1]]",
            u64::MAX,
            i64::MIN
        ))
        .unwrap();

        let mat_2 = identity.tensor_product(&mat_1);
        let mat_3 = mat_1.tensor_product(&identity);

        let cmp_mat_2 = MatPolyOverZ::from_str(&format!(
            "[[1  1, 1  {}, 1  1, 0, 0, 0],[0, 1  {}, 1  -1, 0, 0, 0],[0, 0, 0, 1  1, 1  {}, 1  1],[0, 0, 0, 0, 1  {}, 1  -1]]",
            u64::MAX,
            i64::MIN,
            u64::MAX,
            i64::MIN
        ))
        .unwrap();
        let cmp_mat_3 = MatPolyOverZ::from_str(&format!(
            "[[1  1, 0, 1  {}, 0, 1  1, 0],[0, 1  1, 0, 1  {}, 0, 1  1],[0, 0, 1  {}, 0, 1  -1, 0],[0, 0, 0, 1  {}, 0, 1  -1]]",
            u64::MAX,
            u64::MAX,
            i64::MIN,
            i64::MIN
        ))
        .unwrap();

        assert_eq!(cmp_mat_2, mat_2);
        assert_eq!(cmp_mat_3, mat_3);
    }

    /// Ensure the tensor product works where one is a vector and the other is a matrix
    #[test]
    fn vector_matrix() {
        let vector = MatPolyOverZ::from_str("[[1  1],[1  -1]]").unwrap();
        let mat_1 = MatPolyOverZ::from_str(&format!(
            "[[1  1, 1  {}, 1  1],[0, 1  {}, 1  -1]]",
            u64::MAX,
            i64::MAX
        ))
        .unwrap();

        let mat_2 = vector.tensor_product(&mat_1);
        let mat_3 = mat_1.tensor_product(&vector);

        let cmp_mat_2 = MatPolyOverZ::from_str(&format!(
            "[[1  1, 1  {}, 1  1],[0, 1  {}, 1  -1],[1  -1, 1  -{}, 1  -1],[0, 1  -{}, 1  1]]",
            u64::MAX,
            i64::MAX,
            u64::MAX,
            i64::MAX
        ))
        .unwrap();
        let cmp_mat_3 = MatPolyOverZ::from_str(&format!(
            "[[1  1, 1  {}, 1  1],[1  -1, 1  -{}, 1  -1],[0, 1  {}, 1  -1],[0, 1  -{}, 1  1]]",
            u64::MAX,
            u64::MAX,
            i64::MAX,
            i64::MAX
        ))
        .unwrap();

        assert_eq!(cmp_mat_2, mat_2);
        assert_eq!(cmp_mat_3, mat_3);
    }

    /// Ensure that the tensor product works correctly with two vectors
    #[test]
    fn vector_vector() {
        let vec_1 = MatPolyOverZ::from_str("[[1  2],[1  1]]").unwrap();
        let vec_2 = MatPolyOverZ::from_str(&format!(
            "[[1  {}],[1  {}]]",
            (u64::MAX - 1) / 2,
            i64::MIN / 2
        ))
        .unwrap();

        let vec_3 = vec_1.tensor_product(&vec_2);
        let vec_4 = vec_2.tensor_product(&vec_1);

        let cmp_vec_3 = MatPolyOverZ::from_str(&format!(
            "[[1  {}],[1  {}],[1  {}],[1  {}]]",
            u64::MAX - 1,
            i64::MIN,
            (u64::MAX - 1) / 2,
            i64::MIN / 2
        ))
        .unwrap();
        let cmp_vec_4 = MatPolyOverZ::from_str(&format!(
            "[[1  {}],[1  {}],[1  {}],[1  {}]]",
            u64::MAX - 1,
            (u64::MAX - 1) / 2,
            i64::MIN,
            i64::MIN / 2
        ))
        .unwrap();

        assert_eq!(cmp_vec_3, vec_3);
        assert_eq!(cmp_vec_4, vec_4);
    }

    /// Ensures that the tensor product works for higher degree polynomials.
    #[test]
    fn higher_degree() {
        let higher_degree = MatPolyOverZ::from_str("[[1  1, 2  0 1, 2  1 1]]").unwrap();
        let mat_1 =
            MatPolyOverZ::from_str(&format!("[[1  1, 1  {}, 2  1 {}]]", u64::MAX, i64::MIN))
                .unwrap();

        let mat_2 = higher_degree.tensor_product(&mat_1);

        let cmp_mat_2 = MatPolyOverZ::from_str(&format!(
            "[[1  1, 1  {}, 2  1 {}, 2  0 1, 2  0 {}, 3  0 1 {}, 2  1 1, 2  {} {}, 3  1 {} {}]]",
            u64::MAX,
            i64::MIN,
            u64::MAX,
            i64::MIN,
            u64::MAX,
            u64::MAX,
            i64::MIN + 1,
            i64::MIN,
        ))
        .unwrap();

        assert_eq!(cmp_mat_2, mat_2);
    }
}
