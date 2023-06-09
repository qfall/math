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
use flint_sys::{fmpz_mat::fmpz_mat_kronecker_product, fmpz_mod_mat::_fmpz_mod_mat_reduce};

impl Tensor for MatZq {
    /// Computes the tensor product of `self` with `other`
    ///
    /// Parameters:
    /// - `other`: the value with which the tensor product is computed.
    ///
    /// Returns the tensor product of `self` with `other` and panics if the
    /// moduli of the provided matrices mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use qfall_math::traits::Tensor;
    /// use std::str::FromStr;
    ///
    /// let mat_a = MatZq::from_str("[[1, 1],[2, 2]] mod 7").unwrap();
    /// let mat_b = MatZq::from_str("[[1, 2],[3, 4]] mod 7").unwrap();
    ///
    /// let mat_ab = mat_a.tensor_product(&mat_b);
    /// let res_ab = "[[1, 2, 1, 2],[3, 4, 3, 4],[2, 4, 2, 4],[6, 1, 6, 1]] mod 7";
    /// assert_eq!(mat_ab, MatZq::from_str(res_ab).unwrap());
    ///
    /// let mat_ba = mat_b.tensor_product(&mat_a);
    /// let res_ba = "[[1, 1, 2, 2],[2, 2, 4, 4],[3, 3, 4, 4],[6, 6, 1, 1]] mod 7";
    /// assert_eq!(mat_ba, MatZq::from_str(res_ba).unwrap());
    /// ```
    ///
    /// # Panics ...
    /// - ... if the moduli of both matrices mismatch.
    /// Use [`tensor_product_safe`](crate::integer_mod_q::MatZq::tensor_product_safe) to get an error instead.
    fn tensor_product(&self, other: &Self) -> Self {
        self.tensor_product_safe(other).unwrap()
    }
}

impl MatZq {
    /// Computes the tensor product of `self` with `other`
    ///
    /// Parameters:
    /// - `other`: the value with which the tensor product is computed.
    ///
    /// Returns the tensor product of `self` with `other` or an error if the
    /// moduli of the provided matrices mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let mat_a = MatZq::from_str("[[1, 1],[2, 2]] mod 7").unwrap();
    /// let mat_b = MatZq::from_str("[[1, 2],[3, 4]] mod 7").unwrap();
    ///
    /// let mat_ab = mat_a.tensor_product_safe(&mat_b).unwrap();
    /// let res_ab = "[[1, 2, 1, 2],[3, 4, 3, 4],[2, 4, 2, 4],[6, 1, 6, 1]] mod 7";
    /// assert_eq!(mat_ab, MatZq::from_str(res_ab).unwrap());
    ///
    /// let mat_ba = mat_b.tensor_product_safe(&mat_a).unwrap();
    /// let res_ba = "[[1, 1, 2, 2],[2, 2, 4, 4],[3, 3, 4, 4],[6, 6, 1, 1]] mod 7";
    /// assert_eq!(mat_ba, MatZq::from_str(res_ba).unwrap());
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`MismatchingModulus`](MathError::MismatchingModulus) if the
    /// moduli of the provided matrices mismatch.
    pub fn tensor_product_safe(&self, other: &Self) -> Result<Self, MathError> {
        if self.get_mod() != other.get_mod() {
            return Err(MathError::MismatchingModulus(format!(
                " Tried to compute tensor product of matrixes with moduli '{}' and '{}'.",
                self.get_mod(),
                other.get_mod()
            )));
        }

        let mut out = MatZq::new(
            self.get_num_rows() * other.get_num_rows(),
            self.get_num_columns() * other.get_num_columns(),
            self.get_mod(),
        )
        .unwrap();

        unsafe {
            fmpz_mat_kronecker_product(
                &mut out.matrix.mat[0],
                &self.matrix.mat[0],
                &other.matrix.mat[0],
            )
        };

        unsafe { _fmpz_mod_mat_reduce(&mut out.matrix) }

        Ok(out)
    }
}

#[cfg(test)]
mod test_tensor {
    use crate::{
        integer_mod_q::MatZq,
        traits::{GetNumColumns, GetNumRows, Tensor},
    };
    use std::str::FromStr;

    /// Ensure that the dimensions of the tensor product are taken over correctly.
    #[test]
    fn dimensions_fit() {
        let mat_1 = MatZq::new(17, 13, 13).unwrap();
        let mat_2 = MatZq::new(3, 4, 13).unwrap();

        let mat_3 = mat_1.tensor_product(&mat_2);
        let mat_3_safe = mat_1.tensor_product_safe(&mat_2).unwrap();

        assert_eq!(51, mat_3.get_num_rows());
        assert_eq!(52, mat_3.get_num_columns());
        assert_eq!(&mat_3, &mat_3_safe);
    }

    /// Ensure that the tensor works correctly with identity
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

        let mat_2 = identity.tensor_product(&mat_1);
        let mat_3 = mat_1.tensor_product(&identity);
        let mat_2_safe = identity.tensor_product_safe(&mat_1).unwrap();
        let mat_3_safe = mat_1.tensor_product_safe(&identity).unwrap();

        let cmp_mat_2 = MatZq::from_str(&format!(
            "[[1, {}, 1, 0, 0, 0],\
              [0, {}, -1, 0, 0, 0],\
              [0, 0, 0, 1, {}, 1],\
              [0, 0, 0, 0, {}, -1]] mod {}",
            u64::MAX,
            i64::MIN,
            u64::MAX,
            i64::MIN,
            u128::MAX
        ))
        .unwrap();
        let cmp_mat_3 = MatZq::from_str(&format!(
            "[[1, 0, {}, 0, 1, 0],\
              [0, 1, 0, {}, 0, 1],\
              [0, 0, {}, 0, -1, 0],\
              [0, 0, 0, {}, 0, -1]] mod {}",
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

    /// Ensure the tensor product works where one is a vector and the other is a matrix
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

        let mat_2 = vector.tensor_product(&mat_1);
        let mat_3 = mat_1.tensor_product(&vector);
        let mat_2_safe = vector.tensor_product_safe(&mat_1).unwrap();
        let mat_3_safe = mat_1.tensor_product_safe(&vector).unwrap();

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

    /// Ensure that the tensor product works correctly with two vectors
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

        let vec_3 = vec_1.tensor_product(&vec_2);
        let vec_4 = vec_2.tensor_product(&vec_1);
        let vec_3_safe = vec_1.tensor_product_safe(&vec_2).unwrap();
        let vec_4_safe = vec_2.tensor_product_safe(&vec_1).unwrap();

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

    /// Ensure that entries are reduced by the modulus
    #[test]
    fn entries_reduced() {
        let mat_1 = MatZq::from_str(&format!("[[1, 2],[3, 4]] mod {}", u64::MAX - 58)).unwrap();
        let mat_2 = MatZq::from_str(&format!("[[1, 58],[0, -1]] mod {}", u64::MAX - 58)).unwrap();

        let mat_3 = mat_1.tensor_product(&mat_2);
        let mat_3_safe = mat_1.tensor_product_safe(&mat_2).unwrap();

        let mat_3_cmp = MatZq::from_str(&format!(
            "[[1, 58, 2, 116],[0, -1, 0, -2],[3, 174, 4, 232],[0, -3, 0, -4]] mod {}",
            u64::MAX - 58
        ))
        .unwrap();
        assert_eq!(mat_3_cmp, mat_3);
        assert_eq!(mat_3_cmp, mat_3_safe);
    }

    /// Ensure that tensor panics if the moduli mismatch
    #[test]
    #[should_panic]
    fn mismatching_moduli_tensor_product() {
        let mat_1 = MatZq::new(1, 2, u64::MAX).unwrap();
        let mat_2 = MatZq::new(1, 2, u64::MAX - 58).unwrap();

        let _ = mat_1.tensor_product(&mat_2);
    }

    /// Ensure that tensor_product_safe returns an error if the moduli mismatch
    #[test]
    fn mismatching_moduli_tensor_product_safe() {
        let mat_1 = MatZq::new(1, 2, u64::MAX).unwrap();
        let mat_2 = MatZq::new(1, 2, u64::MAX - 58).unwrap();

        assert!(mat_1.tensor_product_safe(&mat_2).is_err());
        assert!(mat_2.tensor_product_safe(&mat_1).is_err());
    }
}
