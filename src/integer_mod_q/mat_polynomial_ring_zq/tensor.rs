// Copyright © 2025 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the `tensor` product.

use super::MatPolynomialRingZq;
use crate::{
    error::MathError,
    integer::PolyOverZ,
    traits::{GetEntry, GetNumColumns, GetNumRows, Tensor},
};
use flint_sys::{fmpz_poly_mat::fmpz_poly_mat_entry, fq::fq_mul};

impl Tensor for MatPolynomialRingZq {
    /// Computes the tensor product of `self` with `other`.
    ///
    /// Parameters:
    /// - `other`: the value with which the tensor product is computed.
    ///
    /// Returns the tensor product of `self` with `other`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use qfall_math::traits::Tensor;
    /// use std::str::FromStr;
    ///
    /// let mat_1 = MatPolynomialRingZq::from_str("[[1  1, 2  1 1]] / 3  1 2 3 mod 17").unwrap();
    /// let mat_2 = MatPolynomialRingZq::from_str("[[1  1, 1  2]] / 3  1 2 3 mod 17").unwrap();
    ///
    /// let mat_ab = mat_1.tensor_product(&mat_2);
    /// let mat_ba = mat_2.tensor_product(&mat_1);
    ///
    /// let res_ab = "[[1  1, 1  2, 2  1 1, 2  2 2]] / 3  1 2 3 mod 17";
    /// let res_ba = "[[1  1, 2  1 1, 1  2, 2  2 2]] / 3  1 2 3 mod 17";
    /// assert_eq!(mat_ab, MatPolynomialRingZq::from_str(res_ab).unwrap());
    /// assert_eq!(mat_ba, MatPolynomialRingZq::from_str(res_ba).unwrap());
    /// ```
    ///
    /// # Panics ...
    /// - if the moduli of both matrices mismatch.
    ///     Use [`tensor_product_safe`](crate::integer_mod_q::MatZq::tensor_product_safe) to get an error instead.
    fn tensor_product(&self, other: &Self) -> Self {
        self.tensor_product_safe(other).unwrap()
    }
}

impl MatPolynomialRingZq {
    /// Computes the tensor product of `self` with `other`.
    ///
    /// Parameters:
    /// - `other`: the value with which the tensor product is computed.
    ///
    /// Returns the tensor product of `self` with `other` or an error if the
    /// moduli of the provided matrices mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let mat_1 = MatPolynomialRingZq::from_str("[[1  1, 2  1 1]] / 3  1 2 3 mod 17").unwrap();
    /// let mat_2 = MatPolynomialRingZq::from_str("[[1  1, 1  2]] / 3  1 2 3 mod 17").unwrap();
    ///
    /// let mat_ab = mat_1.tensor_product_safe(&mat_2).unwrap();
    /// let mat_ba = mat_2.tensor_product_safe(&mat_1).unwrap();
    ///
    /// let res_ab = "[[1  1, 1  2, 2  1 1, 2  2 2]] / 3  1 2 3 mod 17";
    /// let res_ba = "[[1  1, 2  1 1, 1  2, 2  2 2]] / 3  1 2 3 mod 17";
    /// assert_eq!(mat_ab, MatPolynomialRingZq::from_str(res_ab).unwrap());
    /// assert_eq!(mat_ba, MatPolynomialRingZq::from_str(res_ba).unwrap());
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///     [`MismatchingModulus`](MathError::MismatchingModulus) if the
    ///     moduli of the provided matrices mismatch.
    pub fn tensor_product_safe(&self, other: &Self) -> Result<Self, MathError> {
        if self.modulus != other.modulus {
            return Err(MathError::MismatchingModulus(format!(
                "Tried to compute tensor product of matrices with moduli '{}' and '{}'.",
                self.get_mod(),
                other.get_mod()
            )));
        }

        let mut out = MatPolynomialRingZq::new(
            self.get_num_rows() * other.get_num_rows(),
            self.get_num_columns() * other.get_num_columns(),
            self.get_mod(),
        );

        for i in 0..self.get_num_rows() {
            for j in 0..self.get_num_columns() {
                let entry: PolyOverZ = unsafe { self.get_entry_unchecked(i, j) };

                if !entry.is_zero() {
                    unsafe { set_matrix_window_mul(&mut out, i, j, entry, other) }
                }
            }
        }

        Ok(out)
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
///     is calculated
/// - `matrix`: the matrix with which the scalar is multiplied
///     before setting the entries in `out`
///
/// Implicitly sets the entries of the matrix according to the definition
/// of the tensor product.
///
/// # Security
/// This function accesses memory directly without checking whether the memory is
/// actually obtained by the matrix out.
/// This means that this function should only be called wisely.
/// If `row_left` or `row_upper` together with the length of the matrix exceeds the
/// range of the matrix other memory could be overwritten.
/// We included asserts to check whether this occurs, but we advise careful usage.
unsafe fn set_matrix_window_mul(
    out: &mut MatPolynomialRingZq,
    row_left: i64,
    column_upper: i64,
    scalar: PolyOverZ,
    matrix: &MatPolynomialRingZq,
) {
    let columns_other = matrix.get_num_columns();
    let rows_other = matrix.get_num_rows();

    assert!(row_left >= 0 && row_left + rows_other <= out.get_num_rows());
    assert!(column_upper >= 0 && column_upper + columns_other <= out.get_num_columns());

    for i_other in 0..rows_other {
        for j_other in 0..columns_other {
            unsafe {
                fq_mul(
                    fmpz_poly_mat_entry(
                        &out.matrix.matrix,
                        row_left * rows_other + i_other,
                        column_upper * columns_other + j_other,
                    ),
                    &scalar.poly,
                    fmpz_poly_mat_entry(&matrix.matrix.matrix, i_other, j_other),
                    matrix.modulus.get_fq_ctx(),
                )
            }
        }
    }
}

#[cfg(test)]
mod test_tensor {
    use crate::{
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
        traits::{GetNumColumns, GetNumRows, Tensor},
    };
    use std::str::FromStr;

    /// Ensure that the dimensions of the tensor product are taken over correctly.
    #[test]
    fn dimensions_fit() {
        let mod_poly = ModulusPolynomialRingZq::from_str("3  1 2 3 mod 17").unwrap();
        let mat_1 = MatPolynomialRingZq::new(17, 13, &mod_poly);
        let mat_2 = MatPolynomialRingZq::new(3, 4, &mod_poly);

        let mat_3 = mat_1.tensor_product(&mat_2);

        assert_eq!(51, mat_3.get_num_rows());
        assert_eq!(52, mat_3.get_num_columns());
    }

    /// Ensure that the tensor works correctly with identity.
    #[test]
    fn identity() {
        let mod_poly =
            ModulusPolynomialRingZq::from_str(&format!("3  1 2 3 mod {}", u64::MAX)).unwrap();
        let identity = MatPolynomialRingZq::identity(2, 2, &mod_poly);
        let mat_1 = MatPolynomialRingZq::from_str(&format!(
            "[[1  1, 1  {}, 1  1],[0, 1  {}, 1  -1]] / 3  1 2 3 mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();

        let mat_2 = identity.tensor_product(&mat_1);
        let mat_3 = mat_1.tensor_product(&identity);

        let cmp_mat_2 = MatPolynomialRingZq::from_str(&format!(
            "[[1  1, 1  {}, 1  1, 0, 0, 0],[0, 1  {}, 1  -1, 0, 0, 0],[0, 0, 0, 1  1, 1  {}, 1  1],[0, 0, 0, 0, 1  {}, 1  -1]] / 3  1 2 3 mod {}",
            i64::MAX,
            i64::MIN,
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        let cmp_mat_3 = MatPolynomialRingZq::from_str(&format!(
            "[[1  1, 0, 1  {}, 0, 1  1, 0],[0, 1  1, 0, 1  {}, 0, 1  1],[0, 0, 1  {}, 0, 1  -1, 0],[0, 0, 0, 1  {}, 0, 1  -1]] / 3  1 2 3 mod {}",
            i64::MAX,
            i64::MAX,
            i64::MIN,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();

        assert_eq!(cmp_mat_2, mat_2);
        assert_eq!(cmp_mat_3, mat_3);
    }

    /// Ensure the tensor product works where one is a vector and the other is a matrix.
    #[test]
    fn vector_matrix() {
        let vector =
            MatPolynomialRingZq::from_str(&format!("[[1  1],[1  -1]] / 3  1 2 3 mod {}", u64::MAX))
                .unwrap();
        let mat_1 = MatPolynomialRingZq::from_str(&format!(
            "[[1  1, 1  {}, 1  1],[0, 1  {}, 1  -1]] / 3  1 2 3 mod {}",
            i64::MAX,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();

        let mat_2 = vector.tensor_product(&mat_1);
        let mat_3 = mat_1.tensor_product(&vector);

        let cmp_mat_2 = MatPolynomialRingZq::from_str(&format!(
            "[[1  1, 1  {}, 1  1],[0, 1  {}, 1  -1],[1  -1, 1  -{}, 1  -1],[0, 1  -{}, 1  1]] / 3  1 2 3 mod {}",
            i64::MAX,
            i64::MAX,
            i64::MAX,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp_mat_3 = MatPolynomialRingZq::from_str(&format!(
            "[[1  1, 1  {}, 1  1],[1  -1, 1  -{}, 1  -1],[0, 1  {}, 1  -1],[0, 1  -{}, 1  1]] / 3  1 2 3 mod {}",
            i64::MAX,
            i64::MAX,
            i64::MAX,
            i64::MAX,
            u64::MAX
        ))
        .unwrap();

        assert_eq!(cmp_mat_2, mat_2);
        assert_eq!(cmp_mat_3, mat_3);
    }

    /// Ensure that the tensor product works correctly with two vectors.
    #[test]
    fn vector_vector() {
        let vec_1 =
            MatPolynomialRingZq::from_str(&format!("[[1  2],[1  1]] / 3  1 2 3 mod {}", u64::MAX))
                .unwrap();
        let vec_2 = MatPolynomialRingZq::from_str(&format!(
            "[[1  {}],[1  {}]] / 3  1 2 3 mod {}",
            (u64::MAX - 1) / 2,
            i64::MIN / 2,
            u64::MAX
        ))
        .unwrap();

        let vec_3 = vec_1.tensor_product(&vec_2);
        let vec_4 = vec_2.tensor_product(&vec_1);

        let cmp_vec_3 = MatPolynomialRingZq::from_str(&format!(
            "[[1  {}],[1  {}],[1  {}],[1  {}]] / 3  1 2 3 mod {}",
            u64::MAX - 1,
            i64::MIN,
            (u64::MAX - 1) / 2,
            i64::MIN / 2,
            u64::MAX
        ))
        .unwrap();
        let cmp_vec_4 = MatPolynomialRingZq::from_str(&format!(
            "[[1  {}],[1  {}],[1  {}],[1  {}]] / 3  1 2 3 mod {}",
            u64::MAX - 1,
            (u64::MAX - 1) / 2,
            i64::MIN,
            i64::MIN / 2,
            u64::MAX
        ))
        .unwrap();

        assert_eq!(cmp_vec_3, vec_3);
        assert_eq!(cmp_vec_4, vec_4);
    }

    /// Ensures that the tensor product works for higher degree polynomials.
    #[test]
    fn higher_degree() {
        let higher_degree = MatPolynomialRingZq::from_str(&format!(
            "[[1  1, 2  0 1, 2  1 1]] / 3  1 2 3 mod {}",
            u64::MAX
        ))
        .unwrap();
        let mat_1 = MatPolynomialRingZq::from_str(&format!(
            "[[1  1, 1  {}, 2  1 {}]] / 3  1 2 3 mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();

        let mat_2 = higher_degree.tensor_product(&mat_1);

        let cmp_mat_2 = MatPolynomialRingZq::from_str(&format!(
            "[[1  1, 1  {}, 2  1 {}, 2  0 1, 2  0 {}, 3  0 1 {}, 2  1 1, 2  {} {}, 3  1 {} {}]] / 3  1 2 3 mod {}",
            i64::MAX,
            i64::MIN,
            i64::MAX,
            i64::MIN,
            i64::MAX,
            i64::MAX,
            i64::MIN + 1,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();

        assert_eq!(cmp_mat_2, mat_2);
    }

    /// Ensure that the tensor product panics, if the moduli mismatch.
    #[test]
    #[should_panic]
    fn moduli_mismatch_panic() {
        let mod_poly_1 = ModulusPolynomialRingZq::from_str("3  1 2 3 mod 17").unwrap();
        let mod_poly_2 = ModulusPolynomialRingZq::from_str("3  1 2 3 mod 16").unwrap();
        let mat_1 = MatPolynomialRingZq::new(17, 13, &mod_poly_1);
        let mat_2 = MatPolynomialRingZq::new(3, 4, &mod_poly_2);

        let _ = mat_1.tensor_product(&mat_2);
    }

    /// Ensure that the safe version of the tensor product returns an error, if the moduli mismatch.
    #[test]
    fn moduli_mismatch_error() {
        let mod_poly_1 = ModulusPolynomialRingZq::from_str("3  1 2 3 mod 17").unwrap();
        let mod_poly_2 = ModulusPolynomialRingZq::from_str("3  1 2 3 mod 16").unwrap();
        let mat_1 = MatPolynomialRingZq::new(17, 13, &mod_poly_1);
        let mat_2 = MatPolynomialRingZq::new(3, 4, &mod_poly_2);

        assert!(mat_1.tensor_product_safe(&mat_2).is_err());
    }
}
