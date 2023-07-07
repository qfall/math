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
    /// Returns the product of `self` and `other` as a [`MatQ`] or panics if
    /// the divisor is 0.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{MatZ, Z};
    /// use std::str::FromStr;
    ///
    /// let mat1 = MatZ::from_str("[[3,6],[9,27]]").unwrap();
    /// let integer = Z::from(3);
    ///
    /// let mat2 = &mat1 / &integer;
    /// ```
    ///
    /// # Panics ...
    /// - if the divisor is `0`.
    fn div(self, divisor: &Z) -> Self::Output {
        if divisor == &Z::ZERO {
            panic!("DivisionByZero: tried to divide {} by zero", self);
        }

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
    /// Returns the product of `self` and `other` as a [`MatZ`] or panics if
    /// the divisor is 0.
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
    /// let mut mat1 = MatZ::from_str("[[3,6],[9,27]]").unwrap();
    /// let integer = Z::from(3);
    ///
    /// let mat2 = unsafe{ mat1.div_exact(&integer)};
    /// ```
    pub unsafe fn div_exact(mut self, divisor: impl Into<Z>) -> MatZ {
        let divisor: Z = divisor.into();

        fmpz_mat_scalar_divexact_fmpz(&mut self.matrix, &self.matrix, &divisor.value);

        self
    }

    /// Implements division for a [`MatZ`] matrix by a [`Z`] integer.
    ///
    /// Parameters:
    /// - `divisor`: specifies the divisor by which the matrix is divided
    ///
    /// Returns the product of `self` and `other` as a [`MatZ`] or panics if
    /// the divisor is 0.
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
    /// let mat1 = MatZ::from_str("[[3,6],[9,27]]").unwrap();
    /// let integer = Z::from(3);
    ///
    /// let mat2 = unsafe{&mat1.div_exact_ref(&integer)};
    /// ```
    #[allow(clippy::missing_safety_doc)]
    pub unsafe fn div_exact_ref(&self, divisor: impl Into<Z>) -> MatZ {
        let divisor: Z = divisor.into();

        let mut out = MatZ::new(self.get_num_rows(), self.get_num_columns());
        fmpz_mat_scalar_divexact_fmpz(&mut out.matrix, &self.matrix, &divisor.value);

        out
    }
}

#[cfg(test)]
mod test_div_exact {
    use super::*;
    use std::str::FromStr;

    /// Checks if matrix division works fine for both borrowed.
    #[test]
    fn borrowed_correctness() {
        let mat1 = MatZ::from_str("[[6,3],[3,6]]").unwrap();
        let mat2 = mat1.clone();
        let integer = Z::from(3);

        let mat1 = unsafe { mat1.div_exact_ref(&integer) };
        let mat2 = unsafe { mat2.div_exact(&integer) };

        let mat3 = MatZ::from_str("[[2,1],[1,2]]").unwrap();

        assert_eq!(mat3, mat1);
        assert_eq!(mat3, mat2);
    }

    /// Checks if matrix division works fine for both owned.
    #[test]
    fn owned_correctness() {
        let mat1 = MatZ::from_str("[[6,3],[3,6]]").unwrap();
        let mat2 = mat1.clone();
        let integer1 = Z::from(3);
        let integer2 = Z::from(3);

        let mat1 = unsafe { mat1.div_exact_ref(integer1) };
        let mat2 = unsafe { mat2.div_exact(integer2) };

        let mat3 = MatZ::from_str("[[2,1],[1,2]]").unwrap();

        assert_eq!(mat3, mat1);
        assert_eq!(mat3, mat2);
    }

    /// Checks if matrix division works fine for matrices of different dimensions.
    #[test]
    fn different_dimensions_correctness() {
        let mat1 = MatZ::from_str("[[3],[0],[12]]").unwrap();
        let mat2 = MatZ::from_str("[[6,15,18],[3,9,3]]").unwrap();
        let integer = Z::from(3);

        let mat3 = MatZ::from_str("[[1],[0],[4]]").unwrap();
        let mat4 = MatZ::from_str("[[2,5,6],[1,3,1]]").unwrap();

        assert_eq!(mat3, unsafe { mat1.div_exact_ref(&integer) });
        assert_eq!(mat4, unsafe { mat2.div_exact_ref(&integer) });
        assert_eq!(mat3, unsafe { mat1.div_exact(&integer) });
        assert_eq!(mat4, unsafe { mat2.div_exact(&integer) });
    }

    /// Checks if matrix division works fine for large values.
    #[test]
    fn large_entries() {
        let mat1 = MatZ::from_str(&format!("[[6],[{}],[2]]", i64::MAX / 3)).unwrap();
        let mat2 = MatZ::from_str(&format!("[[{}]]", i64::MAX)).unwrap();
        let integer1 = Z::from(2);
        let integer2 = Z::from(i64::MAX);

        let mat3 = MatZ::from_str(&format!("[[3],[{}],[1]]", (i64::MAX / 6))).unwrap();
        let mat4 = MatZ::from_str("[[1]]").unwrap();

        assert_eq!(mat3, unsafe { mat1.div_exact_ref(&integer1) });
        assert_eq!(mat4, unsafe { mat2.div_exact_ref(&integer2) });
        assert_eq!(mat3, unsafe { mat1.div_exact(&integer1) });
        assert_eq!(mat4, unsafe { mat2.div_exact(&integer2) });
    }
}

#[cfg(test)]
mod test_div {
    use super::*;
    use std::str::FromStr;

    /// Checks if matrix division works fine for both borrowed.
    #[test]
    fn borrowed_correctness() {
        let mat1 = MatZ::from_str("[[6,3],[3,6]]").unwrap();
        let integer = Z::from(3);

        let mat1 = &mat1 / &integer;

        let mat2 = MatQ::from_str("[[2,1],[1,2]]").unwrap();

        assert_eq!(mat2, mat1);
    }

    /// Checks if matrix division works fine for both owned.
    #[test]
    fn owned_correctness() {
        let mat1 = MatZ::from_str("[[6,3],[3,6]]").unwrap();
        let integer = Z::from(3);

        let mat1 = mat1 / integer;

        let mat2 = MatQ::from_str("[[2,1],[1,2]]").unwrap();

        assert_eq!(mat2, mat1);
    }

    /// Checks if matrix division works fine for half owned/borrowed.
    #[test]
    fn half_correctness() {
        let mat1 = MatZ::from_str("[[6,3],[3,6]]").unwrap();
        let mat2 = mat1.clone();
        let integer1 = Z::from(3);

        let mat1 = mat1 / &integer1;
        let mat2 = &mat2 / integer1;

        let mat3 = MatQ::from_str("[[2,1],[1,2]]").unwrap();

        assert_eq!(mat3, mat1);
        assert_eq!(mat3, mat2);
    }

    /// Checks if matrix division works with not dividable entries.
    #[test]
    fn not_dividable_error() {
        let mat1 = MatZ::from_str("[[6,2],[3,10]]").unwrap();
        let integer = Z::from(3);

        let _mat1 = &mat1 / &integer;
    }

    /// Checks if matrix division works fine for matrices of different dimensions.
    #[test]
    fn different_dimensions_correctness() {
        let mat1 = MatZ::from_str("[[4],[0],[12]]").unwrap();
        let mat2 = MatZ::from_str("[[6,15,18],[3,10,3]]").unwrap();
        let integer = Z::from(3);

        let mat3 = MatQ::from_str("[[4/3],[0],[4]]").unwrap();
        let mat4 = MatQ::from_str("[[2,5,6],[1,10/3,1]]").unwrap();

        assert_eq!(mat3, mat1 / &integer);
        assert_eq!(mat4, mat2 / integer);
    }

    /// Checks if matrix division works fine for large values.
    #[test]
    fn large_entries() {
        let mat1 = MatZ::from_str(&format!("[[6],[{}],[2]]", i64::MAX / 3)).unwrap();
        let mat2 = MatZ::from_str(&format!("[[{}]]", i64::MAX)).unwrap();
        let integer1 = Z::from(2);
        let integer2 = Z::from(i64::MAX);

        let mat3 = MatQ::from_str(&format!("[[3],[{}],[1]]", (i64::MAX / 6))).unwrap();
        let mat4 = MatQ::from_str("[[1]]").unwrap();

        assert_eq!(mat3, mat1 / integer1);
        assert_eq!(mat4, mat2 / integer2);
    }

    /// Checks if the doctest works.
    #[test]
    fn doctest_correct() {
        let mat1 = MatZ::from_str("[[3,6],[9,27]]").unwrap();
        let integer = Z::from(3);

        let _ = &mat1 / &integer;
    }
}
