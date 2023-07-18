// Copyright © 2023 Marcel Luca Schmidt and Sven Moog
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of scalar multiplication for [`MatZ`] matrices.

use super::super::MatZ;
use crate::integer::Z;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use crate::rational::MatQ;
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpq_mat::fmpq_mat_set_fmpz_mat_div_fmpz;
use flint_sys::fmpz_mat::fmpz_mat_scalar_divexact_fmpz;
use std::ops::Div;

impl Div<&Z> for &MatZ {
    type Output = MatQ;
    /// Implements division for a [`MatZ`] matrix by a [`Z`] integer.
    ///
    /// Parameters:
    /// - `divisor`: specifies the divisor by which the matrix is divided
    ///
    /// Returns the quotient of `self` divided by `other` as a [`MatQ`]
    /// or panics if the divisor is `0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{MatZ, Z};
    /// use std::str::FromStr;
    ///
    /// let mat = MatZ::from_str("[[3,5],[9,22]]").unwrap();
    /// let divisor = Z::from(3);
    ///
    /// let mat_q = &mat / &divisor;
    ///
    /// assert_eq!("[[1, 5/3],[3, 22/3]]", mat_q.to_string());
    /// ```
    ///
    /// # Panics ...
    /// - if the divisor is `0`.
    fn div(self, divisor: &Z) -> Self::Output {
        assert!(!divisor.is_zero(), "Tried to divide {self} by zero.");
        let mut out = MatQ::new(self.get_num_rows(), self.get_num_columns());
        unsafe {
            fmpq_mat_set_fmpz_mat_div_fmpz(&mut out.matrix, &self.matrix, &divisor.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Div, div, MatZ, Z, MatQ);
arithmetic_trait_mixed_borrowed_owned!(Div, div, MatZ, Z, MatQ);

impl MatZ {
    /// Implements division for a [`MatZ`] matrix by a [`Z`] integer.
    ///
    /// Parameters:
    /// - `divisor`: specifies the divisor by which the matrix is divided
    ///
    /// Returns the quotient of `self` divided by `other` as a [`MatZ`]
    /// or panics if the divisor is `0`.
    ///
    /// # Safety
    /// The divisor MUST exactly divide each element in the matrix.
    /// If this is not the case, the result can contain arbitrary values
    /// which can depend on the location in memory.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{MatZ, Z};
    /// use std::str::FromStr;
    ///
    /// let mut mat = MatZ::from_str("[[3,6],[9,27]]").unwrap();
    ///
    /// let mat_z = unsafe { mat.div_exact(3) };
    ///
    /// assert_eq!("[[1, 2],[3, 9]]", mat_z.to_string());
    /// ```
    ///
    /// # Panics ...
    /// - if the divisor is `0`.
    pub unsafe fn div_exact(mut self, divisor: impl Into<Z>) -> MatZ {
        let divisor: Z = divisor.into();
        assert!(!divisor.is_zero(), "Tried to divide {self} by zero.");

        fmpz_mat_scalar_divexact_fmpz(&mut self.matrix, &self.matrix, &divisor.value);

        self
    }

    /// Implements division for a [`MatZ`] matrix by a [`Z`] integer.
    ///
    /// Parameters:
    /// - `divisor`: specifies the divisor by which the matrix is divided
    ///
    /// Returns the quotient of `self` divided by `other` as a [`MatZ`]
    /// or panics if the divisor is `0`.
    ///
    /// # Safety
    /// The divisor MUST exactly divide each element in the matrix.
    /// If this is not the case, the result can contain arbitrary values
    /// which can depend on the location in memory.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{MatZ, Z};
    /// use std::str::FromStr;
    ///
    /// let mat = MatZ::from_str("[[3,6],[9,27]]").unwrap();
    ///
    /// let mat_z = unsafe { mat.div_exact_ref(3) };
    ///
    /// assert_eq!("[[1, 2],[3, 9]]", mat_z.to_string());
    /// ```
    ///
    /// # Panics ...
    /// - if the divisor is `0`.
    pub unsafe fn div_exact_ref(&self, divisor: impl Into<Z>) -> MatZ {
        let divisor: Z = divisor.into();
        assert!(!divisor.is_zero(), "Tried to divide {self} by zero.");

        let mut out = MatZ::new(self.get_num_rows(), self.get_num_columns());
        fmpz_mat_scalar_divexact_fmpz(&mut out.matrix, &self.matrix, &divisor.value);

        out
    }
}

#[cfg(test)]
mod test_div_exact {
    use super::*;
    use crate::integer_mod_q::Modulus;
    use std::str::FromStr;

    /// Tests that division is available for other types.
    #[test]
    fn availability() {
        let mat = MatZ::from_str("[[6,3],[3,6]]").unwrap();

        let _ = unsafe { mat.div_exact_ref(3i64) };
        let _ = unsafe { mat.div_exact_ref(3i32) };
        let _ = unsafe { mat.div_exact_ref(3i16) };
        let _ = unsafe { mat.div_exact_ref(3i8) };
        let _ = unsafe { mat.div_exact_ref(3u64) };
        let _ = unsafe { mat.div_exact_ref(3u32) };
        let _ = unsafe { mat.div_exact_ref(3u16) };
        let _ = unsafe { mat.div_exact_ref(3u8) };
        let _ = unsafe { mat.div_exact_ref(Z::from(3)) };
        let _ = unsafe { mat.div_exact_ref(Modulus::from(3)) };
        let _ = unsafe { mat.div_exact_ref(&Z::from(3)) };
        let _ = unsafe { mat.div_exact_ref(&Modulus::from(3)) };

        let _ = unsafe { mat.clone().div_exact(3i64) };
        let _ = unsafe { mat.clone().div_exact(3i32) };
        let _ = unsafe { mat.clone().div_exact(3i16) };
        let _ = unsafe { mat.clone().div_exact(3i8) };
        let _ = unsafe { mat.clone().div_exact(3u64) };
        let _ = unsafe { mat.clone().div_exact(3u32) };
        let _ = unsafe { mat.clone().div_exact(3u16) };
        let _ = unsafe { mat.clone().div_exact(3u8) };
        let _ = unsafe { mat.clone().div_exact(Z::from(3)) };
        let _ = unsafe { mat.clone().div_exact(Modulus::from(3)) };
        let _ = unsafe { mat.clone().div_exact(&Z::from(3)) };
        let _ = unsafe { mat.div_exact(&Modulus::from(3)) };
    }

    /// Checks if matrix division works correctly.
    #[test]
    fn division_correctness() {
        let mat = MatZ::from_str("[[6,3],[3,6]]").unwrap();

        let mat_divided_1 = unsafe { mat.div_exact_ref(3) };
        let mat_divided_2 = unsafe { mat.div_exact(3) };

        let mat_cmp = MatZ::from_str("[[2,1],[1,2]]").unwrap();
        assert_eq!(mat_cmp, mat_divided_1);
        assert_eq!(mat_cmp, mat_divided_2);
    }

    /// Checks if matrix division works for negative numbers.
    #[test]
    fn negative_correctness() {
        let mat = MatZ::from_str("[[6,-3],[3,-6]]").unwrap();

        let mat_divided_1 = unsafe { mat.div_exact_ref(3) };
        let mat_divided_2 = unsafe { mat.div_exact_ref(-3) };

        let mat_cmp1 = MatZ::from_str("[[2,-1],[1,-2]]").unwrap();
        let mat_cmp2 = MatZ::from_str("[[-2,1],[-1,2]]").unwrap();
        assert_eq!(mat_cmp1, mat_divided_1);
        assert_eq!(mat_cmp2, mat_divided_2);
    }

    /// Checks if matrix division works fine for matrices of different dimensions.
    #[test]
    fn different_dimensions_correctness() {
        let mat1 = MatZ::from_str("[[-3],[0],[12]]").unwrap();
        let mat2 = MatZ::from_str("[[6,15,18],[3,-9,3]]").unwrap();

        let mat_cmp1 = MatZ::from_str("[[-1],[0],[4]]").unwrap();
        let mat_cmp2 = MatZ::from_str("[[2,5,6],[1,-3,1]]").unwrap();
        assert_eq!(mat_cmp1, unsafe { mat1.div_exact_ref(3) });
        assert_eq!(mat_cmp2, unsafe { mat2.div_exact_ref(3) });
        assert_eq!(mat_cmp1, unsafe { mat1.div_exact(3) });
        assert_eq!(mat_cmp2, unsafe { mat2.div_exact(3) });
    }

    /// Checks if matrix division works fine for large values.
    #[test]
    fn large_entries() {
        let mat1 = MatZ::from_str(&format!("[[6],[{}],[{}]]", i64::MAX / 3, i64::MIN / 3)).unwrap();
        let mat2 = MatZ::from_str(&format!("[[{}]]", i64::MAX)).unwrap();
        let mat3 = MatZ::from_str(&format!("[[{}]]", i64::MIN)).unwrap();

        let mat_cmp1 =
            MatZ::from_str(&format!("[[3],[{}],[{}]]", (i64::MAX / 6), (i64::MIN / 6))).unwrap();
        let mat_cmp2 = MatZ::from_str("[[1]]").unwrap();
        assert_eq!(mat_cmp1, unsafe { mat1.div_exact_ref(2) });
        assert_eq!(mat_cmp2, unsafe { mat2.div_exact_ref(i64::MAX) });
        assert_eq!(mat_cmp2, unsafe { mat3.div_exact_ref(i64::MIN) });
        assert_eq!(mat_cmp1, unsafe { mat1.div_exact(2) });
        assert_eq!(mat_cmp2, unsafe { mat2.div_exact(i64::MAX) });
        assert_eq!(mat_cmp2, unsafe { mat3.div_exact(i64::MIN) });
    }

    /// Checks if matrix division panics on division by 0.
    #[test]
    #[should_panic]
    fn div_by_0_error() {
        let mat = MatZ::from_str("[[6,2],[3,10]]").unwrap();

        let _mat = unsafe { mat.div_exact(0) };
    }

    /// Checks if matrix division panics on division by 0.
    #[test]
    #[should_panic]
    fn div_by_0_error_ref() {
        let mat = MatZ::from_str("[[6,2],[3,10]]").unwrap();

        let _mat = unsafe { mat.div_exact_ref(0) };
    }
}

#[cfg(test)]
mod test_div {
    use super::*;
    use std::str::FromStr;

    /// Tests that division is available for other types.
    #[test]
    fn availability() {
        let mat = MatZ::from_str("[[6,5],[2,6]]").unwrap();
        let divisor = Z::from(3);

        let _ = &mat / &divisor;
        let _ = mat.clone() / &divisor;
        let _ = &mat / divisor.clone();
        let _ = mat / divisor;
    }

    /// Checks if matrix division works correctly.
    #[test]
    fn division_correctness() {
        let mat = MatZ::from_str("[[6,5],[2,6]]").unwrap();
        let divisor = Z::from(3);

        let mat_q = &mat / &divisor;

        let mat_cmp = MatQ::from_str("[[2,5/3],[2/3,2]]").unwrap();
        assert_eq!(mat_cmp, mat_q);
    }

    /// Checks if matrix division works fine for matrices of different dimensions.
    #[test]
    fn different_dimensions_correctness() {
        let mat1 = MatZ::from_str("[[4],[0],[12]]").unwrap();
        let mat2 = MatZ::from_str("[[6,15,18],[3,10,3]]").unwrap();
        let divisor = Z::from(3);

        let mat_cmp1 = MatQ::from_str("[[4/3],[0],[4]]").unwrap();
        let mat_cmp2 = MatQ::from_str("[[2,5,6],[1,10/3,1]]").unwrap();
        assert_eq!(mat_cmp1, mat1 / &divisor);
        assert_eq!(mat_cmp2, mat2 / divisor);
    }

    /// Checks if matrix division works fine for large values.
    #[test]
    fn large_entries() {
        let mat1 = MatZ::from_str(&format!("[[6],[{}],[{}]]", i64::MAX / 3, i64::MIN / 3)).unwrap();
        let mat2 = MatZ::from_str(&format!("[[{}]]", i64::MAX)).unwrap();
        let mat3 = MatZ::from_str(&format!("[[{}]]", i64::MIN)).unwrap();
        let divisor1 = Z::from(2);
        let divisor2 = Z::from(i64::MAX);
        let divisor3 = Z::from(i64::MIN);

        let mat_cmp1 =
            MatQ::from_str(&format!("[[3],[{}],[{}]]", (i64::MAX / 6), (i64::MIN / 6))).unwrap();
        let mat_cmp2 = MatQ::from_str("[[1]]").unwrap();
        assert_eq!(mat_cmp1, mat1 / divisor1);
        assert_eq!(mat_cmp2, mat2 / divisor2);
        assert_eq!(mat_cmp2, mat3 / divisor3);
    }

    /// Checks if matrix division panics on division by 0.
    #[test]
    #[should_panic]
    fn div_by_0_error() {
        let mat = MatZ::from_str("[[6,2],[3,10]]").unwrap();
        let divisor = Z::ZERO;

        let _mat = mat / divisor;
    }

    /// Checks if the doctest works.
    #[test]
    fn doctest_correct() {
        let mat = MatZ::from_str("[[3,5],[9,22]]").unwrap();
        let divisor = Z::from(3);

        let mat_q = &mat / &divisor;

        assert_eq!("[[1, 5/3],[3, 22/3]]", mat_q.to_string());
    }
}
