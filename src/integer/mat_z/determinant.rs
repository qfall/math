// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the implementation of the `determinant` function.

use super::MatZ;
use crate::integer::Z;
use flint_sys::fmpz_mat::fmpz_mat_det;

impl MatZ {
    /// Returns the determinant of the matrix.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatZ::from_str("[[1,2],[3,4]]").unwrap();
    /// let matrix_invert = matrix.det();
    /// ```
    pub fn det(&self) -> Z {
        let mut det = Z::default();
        unsafe {
            fmpz_mat_det(&mut det.value, &self.matrix);
        }
        det
    }
}

#[cfg(test)]
mod test_determinant {

    use crate::integer::{MatZ, Z};
    use std::str::FromStr;

    /// Test whether invert correctly calculates an inverse matrix
    #[test]
    fn determinant_works() {
        let mat1 = MatZ::from_str("[[5,2],[2,1]]").unwrap();
        let mat2 = MatZ::from_str("[[2,0],[0,1]]").unwrap();
        let mat3 = MatZ::from_str("[[0,0],[0,1]]").unwrap();

        let det1 = mat1.det();
        let det2 = mat2.det();
        let det3 = mat3.det();
        let cmp1 = Z::ONE;
        let cmp2 = Z::from(2);
        let cmp3 = Z::ZERO;

        assert_eq!(cmp1, det1);
        assert_eq!(cmp2, det2);
        assert_eq!(cmp3, det3);
    }
}
