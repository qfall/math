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
use flint_sys::fmpz_mat::fmpz_mat_hnf_transform;

impl MatZ {
    /// Computes the Hermite-normal form of `self` along with
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
    /// let (h, u) = matrix.hnf();
    ///
    /// assert_eq!(h_cmp, h);
    /// assert_eq!(u_cmp, u);
    /// ```
    pub fn hnf(&self) -> (MatZ, MatZ) {
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
}

#[cfg(test)]
mod test_hnf {
    use super::MatZ;
    use std::str::FromStr;

    /// Ensures that [`MatZ::hnf`] works for small entries.
    #[test]
    fn small_entries() {
        let matrix = MatZ::from_str("[[2,3,6,2],[5,6,1,6],[8,3,1,1]]").unwrap();
        let h_cmp = MatZ::from_str("[[1, 0, 50, -11],[0, 3, 28, -2],[0, 0, 61, -13]]").unwrap();
        let u_cmp = MatZ::from_str("[[9, -5, 1],[5, -2, 0],[11, -6, 1]]").unwrap();

        let (h, u) = matrix.hnf();

        assert_eq!(h_cmp, h);
        assert_eq!(u_cmp, u);
    }

    /// Ensures that [`MatZ::hnf`] works for large entries.
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

        let (h, u) = matrix.hnf();

        assert_eq!(h_cmp, h);
        assert_eq!(u_cmp, u);
    }
}
