// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the Gram-Schmidt Orthogonalization for ['MatQ'] matrices.

use super::MatQ;
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpq_mat::fmpq_mat_gso;

impl MatQ {
    /// Computes the Gram-Schmidt Orthogonalization of the matrix and returns a [`MatQ`] with the corresponding matrix.
    ///
    /// # Example
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let mat = MatQ::from_str("[[1/2, 1],[2, 5]]").unwrap();
    /// let mat_gso = mat.gso();
    /// ```
    pub fn gso(&self) -> Self {
        let mut out = MatQ::new(self.get_num_rows(), self.get_num_columns()).unwrap();
        unsafe {
            fmpq_mat_gso(&mut out.matrix, &self.matrix);
        }
        out
    }
}

#[cfg(test)]
mod test_gso {

    use crate::rational::{MatQ, Q};
    use std::str::FromStr;

    /// Ensure that the generated vectors of the gso are orthogonal
    #[test]
    fn gso_orthogonal_values_over_z() {
        let mat = MatQ::from_str(
            "[[1,2,3,4,5],[123,235,123,643,123],[124,212,452,12,1],[0,0,0,1,1],[1,2,3,4,1]]",
        )
        .unwrap();

        let mat_gso = mat.gso();

        let cmp = Q::default();
        for i in 0..5 {
            for j in 0..5 {
                if i != j {
                    let vec_i = mat_gso.get_column(i).unwrap();
                    let vec_j = mat_gso.get_column(j).unwrap();
                    assert_eq!(cmp, vec_i.dot_product(&vec_j).unwrap());
                }
            }
        }
    }

    /// Ensure that the generated vectors from the gso are orthogonal
    #[test]
    fn gso_orthogonal_values_over_q() {
        let mat = MatQ::from_str(
        "[[-1,2/7,3/9,4,5/2],[-123/1000,235/5,123,643/7172721,123],[124/8981,212,452/2140,12/5,1],[0,0,0,1,1],[1,2,3,4/3,1]]",
    )
    .unwrap();

        let mat_gso = mat.gso();

        let mat0 = Q::from_str("0/1").unwrap();
        for i in 0..5 {
            for j in 0..5 {
                if i != j {
                    let vec_i = mat_gso.get_column(i).unwrap();
                    let vec_j = mat_gso.get_column(j).unwrap();
                    assert_eq!(mat0, vec_i.dot_product(&vec_j).unwrap());
                }
            }
        }
    }
}
