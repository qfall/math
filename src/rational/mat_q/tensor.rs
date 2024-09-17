// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the `tensor` product.

use flint_sys::fmpq_mat::fmpq_mat_kronecker_product;

use super::MatQ;
use crate::traits::{GetNumColumns, GetNumRows, Tensor};

impl Tensor for MatQ {
    /// Computes the tensor product of `self` with `other`.
    ///
    /// Parameters:
    /// - `other`:the value with which the tensor product is computed.
    ///
    /// Returns the tensor product of `self` with `other`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use qfall_math::traits::Tensor;
    /// use std::str::FromStr;
    ///
    /// let mat_1 = MatQ::from_str("[[1, 1],[2/3, 2/3]]").unwrap();
    /// let mat_2 = MatQ::from_str("[[1, 2],[3, 4]]").unwrap();
    ///
    /// let mat_12 = mat_1.tensor_product(&mat_2);
    /// let mat_21 = mat_2.tensor_product(&mat_1);
    ///
    /// let res_12 = "[[1, 2, 1, 2],[3, 4, 3, 4],[2/3, 4/3, 2/3, 4/3],[2, 8/3, 2, 8/3]]";
    /// let res_21 = "[[1, 1, 2, 2],[2/3, 2/3, 4/3, 4/3],[3, 3, 4, 4],[2, 2, 8/3, 8/3]]";
    /// assert_eq!(mat_12, MatQ::from_str(res_12).unwrap());
    /// assert_eq!(mat_21, MatQ::from_str(res_21).unwrap());
    /// ```
    fn tensor_product(&self, other: &Self) -> Self {
        let mut out = MatQ::new(
            self.get_num_rows() * other.get_num_rows(),
            self.get_num_columns() * other.get_num_columns(),
        );

        unsafe { fmpq_mat_kronecker_product(&mut out.matrix, &self.matrix, &other.matrix) };

        out
    }
}

#[cfg(test)]
mod test_tensor {
    use crate::{
        rational::MatQ,
        traits::{GetNumColumns, GetNumRows, Tensor},
    };
    use std::str::FromStr;

    /// Ensure that the dimensions of the tensor product are taken over correctly.
    #[test]
    fn dimensions_fit() {
        let mat_1 = MatQ::new(17, 13);
        let mat_2 = MatQ::new(3, 4);

        let mat_3 = mat_1.tensor_product(&mat_2);

        assert_eq!(51, mat_3.get_num_rows());
        assert_eq!(52, mat_3.get_num_columns());
    }

    /// Ensure that the tensor works correctly with identity.
    #[test]
    fn identity() {
        let identity = MatQ::identity(2, 2);
        let mat_1 =
            MatQ::from_str(&format!("[[1, 2/{}, 1],[0, {}, -1]]", u64::MAX, i64::MIN)).unwrap();

        let mat_2 = identity.tensor_product(&mat_1);
        let mat_3 = mat_1.tensor_product(&identity);

        let cmp_mat_2 = MatQ::from_str(&format!(
            "[[1, 2/{}, 1, 0, 0, 0],[0, {}, -1, 0, 0, 0],[0, 0, 0, 1, 2/{}, 1],[0, 0, 0, 0, {}, -1]]",
            u64::MAX,
            i64::MIN,
            u64::MAX,
            i64::MIN
        ))
        .unwrap();
        let cmp_mat_3 = MatQ::from_str(&format!(
            "[[1, 0, 2/{}, 0, 1, 0],[0, 1, 0, 2/{}, 0, 1],[0, 0, {}, 0, -1, 0],[0, 0, 0, {}, 0, -1]]",
            u64::MAX,
            u64::MAX,
            i64::MIN,
            i64::MIN
        ))
        .unwrap();

        assert_eq!(cmp_mat_2, mat_2);
        assert_eq!(cmp_mat_3, mat_3);
    }

    /// Ensure the tensor product works where one is a vector and the other is a matrix.
    #[test]
    fn vector_matrix() {
        let vector = MatQ::from_str("[[1/3],[-1]]").unwrap();
        let mat_1 =
            MatQ::from_str(&format!("[[1, {}, 1],[0, {}, -1]]", u64::MAX, i64::MAX)).unwrap();

        let mat_2 = vector.tensor_product(&mat_1);
        let mat_3 = mat_1.tensor_product(&vector);

        let cmp_mat_2 = MatQ::from_str(&format!(
            "[[1/3, {}/3, 1/3],[0, {}/3, -1/3],[-1, -{}, -1],[0, -{}, 1]]",
            u64::MAX,
            i64::MAX,
            u64::MAX,
            i64::MAX
        ))
        .unwrap();
        let cmp_mat_3 = MatQ::from_str(&format!(
            "[[1/3, {}/3, 1/3],[-1, -{}, -1],[0, {}/3, -1/3],[0, -{}, 1]]",
            u64::MAX,
            u64::MAX,
            i64::MAX,
            i64::MAX
        ))
        .unwrap();

        assert_eq!(cmp_mat_2, mat_2);
        assert_eq!(cmp_mat_3, mat_3);
    }

    /// Ensure that the tensor product works correctly with two vectors.
    #[test]
    fn vector_vector() {
        let vec_1 = MatQ::from_str("[[2],[1]]").unwrap();
        let vec_2 =
            MatQ::from_str(&format!("[[{}],[{}]]", (u64::MAX - 1) / 2, i64::MIN / 2)).unwrap();

        let vec_3 = vec_1.tensor_product(&vec_2);
        let vec_4 = vec_2.tensor_product(&vec_1);

        let cmp_vec_3 = MatQ::from_str(&format!(
            "[[{}],[{}],[{}],[{}]]",
            u64::MAX - 1,
            i64::MIN,
            (u64::MAX - 1) / 2,
            i64::MIN / 2
        ))
        .unwrap();
        let cmp_vec_4 = MatQ::from_str(&format!(
            "[[{}],[{}],[{}],[{}]]",
            u64::MAX - 1,
            (u64::MAX - 1) / 2,
            i64::MIN,
            i64::MIN / 2
        ))
        .unwrap();

        assert_eq!(cmp_vec_3, vec_3);
        assert_eq!(cmp_vec_4, vec_4);
    }
}
