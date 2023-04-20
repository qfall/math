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
    /// # Examples
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

    use crate::{
        rational::{MatQ, Q},
        traits::GetEntry,
    };
    use std::str::FromStr;

    /// Ensure that the generated vectors from the gso are orthogonal
    #[test]
    fn gso_works() {
        let mat = MatQ::from_str(
        "[[-1,2/7,3/9,4,5/2],[-123/1000,235/5,123,643/7172721,123],[124/8981,212,452/2140,12/5,1],[0,0,0,1,1],[1,2,3,4/3,1]]",
    )
    .unwrap();

        let mat_gso = mat.gso();

        let cmp = Q::ZERO;
        for i in 0..5 {
            let vec_i = mat_gso.get_column(i).unwrap();
            assert_ne!(cmp, vec_i.dot_product(&vec_i).unwrap());
            for j in i + 1..5 {
                let vec_j = mat_gso.get_column(j).unwrap();
                assert_eq!(cmp, vec_i.dot_product(&vec_j).unwrap());
            }
        }
    }

    /// Ensure that the generated vectors have the expected values
    #[test]
    fn gso_correct_values() {
        let mat = MatQ::from_str("[[1,-1,1],[1,0,1],[1,1,2]]").unwrap();

        let mat_gso = mat.gso();

        assert_eq!(
            MatQ::from_str("[[1, -1, 1/6],[1, 0, -1/3],[1, 1, 1/6]]").unwrap(),
            mat_gso
        );
    }

    /// Ensure that gso works with independent vectors (more columns than rows)
    #[test]
    fn gso_dependent_columns() {
        let mat = MatQ::from_str("[[1,2,3,4,4],[1,2,3,4,4]]").unwrap();

        let mat_gso = mat.gso();

        let cmp = Q::ZERO;
        for i in 0..5 {
            let vec_i = mat_gso.get_column(i).unwrap();
            for j in i + 1..5 {
                let vec_j = mat_gso.get_column(j).unwrap();
                assert_eq!(cmp, vec_i.dot_product(&vec_j).unwrap());
            }
        }
        let vec1 = mat_gso.get_column(0).unwrap();
        assert_ne!(cmp, vec1.dot_product(&vec1).unwrap());
    }

    /// Ensure that gso works with more rows than columns
    #[test]
    fn gso_dependent_rows() {
        let mat = MatQ::from_str("[[1,2/7],[1,2/7],[10,-2],[0,4],[0,0]]").unwrap();

        let mat_gso = mat.gso();

        let cmp = Q::ZERO;
        for i in 0..2 {
            let vec_i = mat_gso.get_column(i).unwrap();
            assert_ne!(cmp, vec_i.dot_product(&vec_i).unwrap());
            for j in i + 1..2 {
                let vec_j = mat_gso.get_column(j).unwrap();
                assert_eq!(cmp, vec_i.dot_product(&vec_j).unwrap());
            }
        }
    }

    /// Ensure that gso works with big values
    #[test]
    fn gso_big_values() {
        let mat = MatQ::from_str(&format!(
            "[[1,{}/7,2],[1,2/{},10],[10,-2,8]]",
            i64::MAX,
            i64::MAX
        ))
        .unwrap();

        let mat_gso = mat.gso();

        let cmp = Q::ZERO;
        for i in 0..3 {
            let vec_i = mat_gso.get_column(i).unwrap();
            assert_ne!(cmp, vec_i.dot_product(&vec_i).unwrap());
            for j in i + 1..3 {
                let vec_j = mat_gso.get_column(j).unwrap();
                assert_eq!(cmp, vec_i.dot_product(&vec_j).unwrap());
            }
        }
    }

    /// Ensure that gso works on edge cases
    #[test]
    fn gso_edge_cases() {
        let mat1 = MatQ::from_str("[[1]]").unwrap();
        let mat2 = MatQ::from_str("[[1,2/2,3/7]]").unwrap();
        let mat3 = MatQ::from_str("[[1],[2/2],[3/7]]").unwrap();

        let mat1_gso = mat1.gso();
        let mat2_gso = mat2.gso();
        let mat3_gso = mat3.gso();

        assert_eq!(Q::ONE, mat1_gso.get_entry(0, 0).unwrap());

        let cmp = Q::ZERO;
        for i in 0..3 {
            for j in i + 1..3 {
                let vec_i = mat2_gso.get_column(i).unwrap();
                let vec_j = mat2_gso.get_column(j).unwrap();
                assert_eq!(cmp, vec_i.dot_product(&vec_j).unwrap());
            }
        }
        let vec1 = mat2_gso.get_column(0).unwrap();
        assert_ne!(cmp, vec1.dot_product(&vec1).unwrap());

        assert_eq!(mat3, mat3_gso);
    }
}
