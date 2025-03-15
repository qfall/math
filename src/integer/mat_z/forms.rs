// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This file contains implementations of special forms and transforms of
//! matrices, e.g. (Hermite and Smith) normal forms, echelon form, ...

use super::MatZ;
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpz_mat::{
    fmpz_mat_hnf_transform, fmpz_mat_is_in_hnf, fmpz_mat_is_in_snf, fmpz_mat_snf,
};

impl MatZ {
    /// Computes the Hermite normal form of `self` along with
    /// the transformation matrix `U` s.t. `U * A = H`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    /// let matrix = MatZ::from_str("[[1, 2, 12],[2, 4, 5]]").unwrap();
    /// let h_cmp = MatZ::from_str("[[1, 2, 12],[0, 0, 19]]").unwrap();
    /// let u_cmp = MatZ::from_str("[[1, 0],[2, -1]]").unwrap();
    ///
    /// let (h, u) = matrix.hermite_nf();
    ///
    /// assert_eq!(h_cmp, h);
    /// assert_eq!(u_cmp, u);
    /// ```
    pub fn hermite_nf(&self) -> (MatZ, MatZ) {
        let nr_rows = self.get_num_rows();
        let nr_cols = self.get_num_columns();

        let mut hnf = MatZ::new(nr_rows, nr_cols);
        let mut transform = MatZ::new(nr_rows, nr_rows);

        // FLINT doc-comment
        // Computes an integer matrix H such that H is the unique (row) Hermite normal form of A
        // along with the transformation matrix U such that UA = H.
        // The algorithm used is selected from the implementations in FLINT as per fmpz_mat_hnf.
        unsafe { fmpz_mat_hnf_transform(&mut hnf.matrix, &mut transform.matrix, &self.matrix) };

        (hnf, transform)
    }

    /// Checks if `self` is a matrix in Hermite normal form.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    /// let non_hnf = MatZ::from_str("[[1, 2, 12],[2, 4, 5]]").unwrap();
    /// let hnf = MatZ::from_str("[[1, 2, 12],[0, 0, 19]]").unwrap();
    ///
    /// assert!(!non_hnf.is_in_hermite_nf());
    /// assert!(hnf.is_in_hermite_nf());
    /// ```
    pub fn is_in_hermite_nf(&self) -> bool {
        1 == unsafe { fmpz_mat_is_in_hnf(&self.matrix) }
    }

    /// Computes the unique Smith normal form of the matrix `self`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    /// let matrix = MatZ::from_str("[[1, 2, 12],[2, 4, 5]]").unwrap();
    /// let snf_cmp = MatZ::from_str("[[1, 0, 0],[0, 19, 0]]").unwrap();
    ///
    /// let snf = matrix.smith_nf();
    ///
    /// assert_eq!(snf_cmp, snf);
    /// ```
    pub fn smith_nf(&self) -> Self {
        let mut snf: MatZ = MatZ::new(self.get_num_rows(), self.get_num_columns());

        unsafe { fmpz_mat_snf(&mut snf.matrix, &self.matrix) };

        snf
    }

    /// Checks if `self` is a matrix in Smith normal form.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    /// let non_snf = MatZ::from_str("[[1, 2, 12],[2, 4, 5]]").unwrap();
    /// let snf = MatZ::from_str("[[1, 0, 0],[0, 19, 0]]").unwrap();
    ///
    /// assert!(!non_snf.is_in_smith_nf());
    /// assert!(snf.is_in_smith_nf());
    /// ```
    pub fn is_in_smith_nf(&self) -> bool {
        1 == unsafe { fmpz_mat_is_in_snf(&self.matrix) }
    }
}

#[cfg(test)]
mod test_hermite_nf {
    use super::MatZ;
    use std::str::FromStr;

    /// Ensures that [`MatZ::hermite_nf`] and [`MatZ::is_in_hermite_nf`] works for small entries.
    #[test]
    fn small_entries() {
        let matrix = MatZ::from_str("[[2,3,6,2],[5,6,1,6],[8,3,1,1]]").unwrap();
        let h_cmp = MatZ::from_str("[[1, 0, 50, -11],[0, 3, 28, -2],[0, 0, 61, -13]]").unwrap();
        let u_cmp = MatZ::from_str("[[9, -5, 1],[5, -2, 0],[11, -6, 1]]").unwrap();

        let (h, u) = matrix.hermite_nf();

        assert_eq!(h_cmp, h);
        assert_eq!(u_cmp, u);
        assert_eq!(h, &u * &matrix);

        assert!(!matrix.is_in_hermite_nf());
        assert!(h.is_in_hermite_nf());
        assert!(!u.is_in_hermite_nf());
    }

    /// Ensures that [`MatZ::hermite_nf`] and [`MatZ::is_in_hermite_nf`] works for large entries.
    #[test]
    fn large_entries() {
        let matrix = MatZ::from_str(&format!(
            "[[{}, 0],[{}, {}]]",
            i64::MAX,
            2 * (i64::MAX as u64),
            u64::MAX
        ))
        .unwrap();
        let h_cmp = MatZ::from_str(&format!("[[{}, 0],[0, {}]]", i64::MAX, u64::MAX)).unwrap();
        let u_cmp = MatZ::from_str(&format!("[[1, 0],[-2, 1]]")).unwrap();

        let (h, u) = matrix.hermite_nf();

        assert_eq!(h_cmp, h);
        assert_eq!(u_cmp, u);
        assert_eq!(h, &u * &matrix);

        assert!(!matrix.is_in_hermite_nf());
        assert!(h.is_in_hermite_nf());
        assert!(!u.is_in_hermite_nf());
    }

    /// Ensures that [`MatZ::hermite_nf`] and [`MatZ::is_in_hermite_nf`] work
    /// for any matrix dimensions.
    #[test]
    fn dimensions() {
        let mat_0 = MatZ::sample_uniform(4, 1, 0, 16).unwrap();
        let mat_1 = MatZ::sample_uniform(5, 5, 0, 16).unwrap();
        let mat_2 = MatZ::sample_uniform(2, 4, 0, 16).unwrap();

        let (hnf_0, u_0) = mat_0.hermite_nf();
        let (hnf_1, u_1) = mat_1.hermite_nf();
        let (hnf_2, u_2) = mat_2.hermite_nf();

        assert!(hnf_0.is_in_hermite_nf());
        assert!(hnf_1.is_in_hermite_nf());
        assert!(hnf_2.is_in_hermite_nf());

        assert_eq!(hnf_0, u_0 * mat_0);
        assert_eq!(hnf_1, u_1 * mat_1);
        assert_eq!(hnf_2, u_2 * mat_2);
    }
}

#[cfg(test)]
mod test_smith_nf {
    use super::MatZ;
    use std::str::FromStr;

    /// Ensures that [`MatZ::smith_nf`] and [`MatZ::is_in_smith_nf`] works for small entries.
    #[test]
    fn small_entries() {
        let matrix = MatZ::from_str("[[2,3,6,2],[5,6,1,6],[8,3,1,1]]").unwrap();
        let s_cmp = MatZ::from_str("[[1, 0, 0, 0],[0, 1, 0, 0],[0, 0, 1, 0]]").unwrap();

        let s = matrix.smith_nf();

        assert_eq!(s_cmp, s);

        assert!(!matrix.is_in_smith_nf());
        assert!(s.is_in_smith_nf());
    }

    /// Ensures that [`MatZ::smith_nf`] and [`MatZ::is_in_smith_nf`] works for large entries.
    #[test]
    fn large_entries() {
        let matrix = MatZ::from_str(&format!(
            "[[{}, 0],[{}, {}]]",
            i64::MAX,
            2 * (i64::MAX as u64),
            u64::MAX
        ))
        .unwrap();
        let s_cmp =
            MatZ::from_str("[[1, 0],[0, 170141183460469231704017187605319778305]]").unwrap();

        let s = matrix.smith_nf();

        assert_eq!(s_cmp, s);

        assert!(!matrix.is_in_smith_nf());
        assert!(s.is_in_smith_nf());
    }

    /// Ensures that [`MatZ::smith_nf`] and [`MatZ::is_in_smith_nf`] work
    /// for any matrix dimensions.
    #[test]
    fn dimensions() {
        let mat_0 = MatZ::sample_uniform(4, 1, 0, 16).unwrap();
        let mat_1 = MatZ::sample_uniform(5, 5, 0, 16).unwrap();
        let mat_2 = MatZ::sample_uniform(2, 4, 0, 16).unwrap();

        let snf_0 = mat_0.smith_nf();
        let snf_1 = mat_1.smith_nf();
        let snf_2 = mat_2.smith_nf();

        assert!(snf_0.is_in_smith_nf());
        assert!(snf_1.is_in_smith_nf());
        assert!(snf_2.is_in_smith_nf());
    }
}
