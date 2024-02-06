// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Add`] trait for [`MatZ`] values.

use super::super::MatZ;
use crate::integer::mat_z::MatZSubmatrix;
use crate::{error::MathError, traits::AsMatZ};
use flint_sys::fmpz_mat::{fmpz_mat_add, fmpz_mat_struct};
use std::ops::Add;

impl<Other: AsMatZ> Add<Other> for &MatZ {
    type Output = MatZ;
    /// Implements the [`Add`] trait for two [`MatZ`] values.
    /// [`Add`] is implemented for all [`MatZ`]-like objects and borrowed [`MatZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`MatZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let a: MatZ = MatZ::from_str("[[1, 2, 3],[3, 4, 5]]").unwrap();
    /// let b: MatZ = MatZ::from_str("[[1, 9, 3],[1, 0, 5]]").unwrap();
    ///
    /// let c: MatZ = &a + &b;
    /// let d: MatZ = a + b;
    /// let e: MatZ = &c + d;
    /// let f: MatZ = c + &e;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of both matrices mismatch.
    fn add(self, rhs: Other) -> Self::Output {
        unsafe {
            add_fmpz_mat_struct(
                self.get_fmpz_mat_struct_ref(),
                rhs.get_fmpz_mat_struct_ref(),
            )
            .unwrap()
        }
    }
}

impl<Other: AsMatZ> Add<Other> for MatZ {
    type Output = MatZ;

    fn add(self, rhs: Other) -> Self::Output {
        (&self).add(rhs)
    }
}

impl<Other: AsMatZ> Add<Other> for &MatZSubmatrix<'_> {
    type Output = MatZ;

    fn add(self, rhs: Other) -> Self::Output {
        unsafe {
            add_fmpz_mat_struct(
                self.get_fmpz_mat_struct_ref(),
                rhs.get_fmpz_mat_struct_ref(),
            )
            .unwrap()
        }
    }
}

impl<Other: AsMatZ> Add<Other> for MatZSubmatrix<'_> {
    type Output = MatZ;

    fn add(self, rhs: Other) -> Self::Output {
        (&self).add(rhs)
    }
}

impl MatZ {
    /// Implements addition for two [`MatZ`] matrices.
    ///
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both matrices as a [`MatZ`] or an
    /// error if the matrix dimensions mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let a: MatZ = MatZ::from_str("[[1, 2, 3],[3, 4, 5]]").unwrap();
    /// let b: MatZ = MatZ::from_str("[[1, 9, 3],[1, 0, 5]]").unwrap();
    ///
    /// let c: MatZ = a.add_safe(&b).unwrap();
    /// ```
    /// # Errors
    /// Returns a [`MathError`] of type
    /// [`MathError::MismatchingMatrixDimension`] if the matrix dimensions
    /// mismatch.
    pub fn add_safe(&self, other: &Self) -> Result<MatZ, MathError> {
        unsafe {
            add_fmpz_mat_struct(
                self.get_fmpz_mat_struct_ref(),
                other.get_fmpz_mat_struct_ref(),
            )
        }
    }
}

/// Return a [`MatZ`] representing the entrywise addition of the two matrices.
/// If the dimensions do not match, then an error is returned.
///
/// # Errors
/// Returns a [`MathError`] of type
/// [`MathError::MismatchingMatrixDimension`] if the matrix dimensions
/// mismatch.
///
/// # Safety
/// The caller has to ensure that the [`fmpz_mat_struct`]'s contain data.
unsafe fn add_fmpz_mat_struct(
    val1: &fmpz_mat_struct,
    val2: &fmpz_mat_struct,
) -> Result<MatZ, MathError> {
    if val1.r != val2.r || val1.c != val2.c {
        return Err(MathError::MismatchingMatrixDimension(format!(
            "Tried to add a '{}x{}' matrix and a '{}x{}' matrix.",
            val1.r, val2.r, val1.c, val2.c
        )));
    }
    let mut out = MatZ::new(val1.r, val1.c);
    unsafe {
        fmpz_mat_add(&mut out.matrix, val1, val2);
    }
    Ok(out)
}

#[cfg(test)]
mod test_add {
    use super::MatZ;
    use std::str::FromStr;

    /// Testing addition for two [`MatZ`]
    #[test]
    fn add() {
        let a: MatZ = MatZ::from_str("[[1, 2, 3],[3, 4, 5]]").unwrap();
        let b: MatZ = MatZ::from_str("[[1, 2, 3],[3, -4, 5]]").unwrap();
        let c: MatZ = a + b;
        assert_eq!(c, MatZ::from_str("[[2, 4, 6],[6, 0, 10]]").unwrap());
    }

    /// Testing addition for two borrowed [`MatZ`]
    #[test]
    fn add_borrow() {
        let a: MatZ = MatZ::from_str("[[1, 2, 3],[3, 4, 5]]").unwrap();
        let b: MatZ = MatZ::from_str("[[1, 2, 3],[3, -4, 5]]").unwrap();
        let c: MatZ = &a + &b;
        assert_eq!(c, MatZ::from_str("[[2, 4, 6],[6, 0, 10]]").unwrap());
    }

    /// Testing addition for borrowed [`MatZ`] and [`MatZ`]
    #[test]
    fn add_first_borrowed() {
        let a: MatZ = MatZ::from_str("[[1, 2, 3],[3, 4, 5]]").unwrap();
        let b: MatZ = MatZ::from_str("[[1, 2, 3],[3, -4, 5]]").unwrap();
        let c: MatZ = &a + b;
        assert_eq!(c, MatZ::from_str("[[2, 4, 6],[6, 0, 10]]").unwrap());
    }

    /// Testing addition for [`MatZ`] and borrowed [`MatZ`]
    #[test]
    fn add_second_borrowed() {
        let a: MatZ = MatZ::from_str("[[1, 2, 3],[3, 4, 5]]").unwrap();
        let b: MatZ = MatZ::from_str("[[1, 2, 3],[3, -4, 5]]").unwrap();
        let c: MatZ = a + &b;
        assert_eq!(c, MatZ::from_str("[[2, 4, 6],[6, 0, 10]]").unwrap());
    }

    /// Testing addition for large numbers
    #[test]
    fn add_large_numbers() {
        let a: MatZ =
            MatZ::from_str(&format!("[[1, 2, {}],[3, -4, {}]]", i64::MIN, i128::MAX)).unwrap();
        let b: MatZ =
            MatZ::from_str(&format!("[[1, 2, {}],[3, 9, {}]]", i64::MIN + 1, i128::MAX)).unwrap();
        let c: MatZ = a + &b;
        assert_eq!(
            c,
            MatZ::from_str(&format!(
                "[[2, 4, -{}],[6, 5, {}]]",
                u64::MAX,
                u128::MAX - 1
            ))
            .unwrap()
        );
    }

    /// Testing add_safe
    #[test]
    fn add_safe() {
        let a: MatZ = MatZ::from_str("[[1, 2, 3],[3, 4, 5]]").unwrap();
        let b: MatZ = MatZ::from_str("[[1, 2, 3],[3, -4, 5]]").unwrap();
        let c = a.add_safe(&b);
        assert_eq!(
            c.unwrap(),
            MatZ::from_str("[[2, 4, 6],[6, 0, 10]]").unwrap()
        );
    }

    /// Testing add_safe throws error
    #[test]
    fn add_safe_is_err() {
        let a: MatZ = MatZ::from_str("[[1, 2],[3, 4]]").unwrap();
        let b: MatZ = MatZ::from_str("[[1, 2, 3],[3, -4, 5]]").unwrap();
        let c: MatZ = MatZ::from_str("[[1, 2, 3]]").unwrap();
        assert!(a.add_safe(&b).is_err());
        assert!(c.add_safe(&b).is_err());
    }

    // Addition using submatrices
    #[test]
    fn add_submatrix() {
        let a = MatZ::from_str("[[1, 2, 3],[3, 4, 5]]").unwrap();
        let b = a.get_submatrix(0, 1, 0, 1).unwrap();
        let c = MatZ::from_str("[[2, 3],[4, 5]]").unwrap();

        let res = MatZ::from_str("[[3, 5],[7, 9]]").unwrap();
        assert_eq!(res, &b + &c);
        assert_eq!(res, &c + &b);
        assert_eq!(res, c + &b);

        let res_ref = MatZ::from_str("[[2, 4],[6, 8]]").unwrap();
        assert_eq!(res_ref, &b + &b);
        println!("{a}")
    }
}
