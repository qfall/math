// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Add`] trait for [`MatZ`] values.

use super::super::MatZ;
use crate::error::MathError;
use crate::macros::arithmetics::{
    arithmetic_assign_trait_borrowed_to_owned, arithmetic_trait_borrowed_to_owned,
    arithmetic_trait_mixed_borrowed_owned,
};
use crate::traits::MatrixDimensions;
use flint_sys::fmpz_mat::fmpz_mat_add;
use std::ops::{Add, AddAssign};

impl AddAssign<&MatZ> for MatZ {
    /// Computes the addition of `self` and `other` reusing
    /// the memory of `self`.
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// let mut a = MatZ::identity(2, 2);
    /// let b = MatZ::new(2, 2);
    ///
    /// a += &b;
    /// a += b;
    /// ```
    ///
    /// # Panics ...
    /// - if the matrix dimensions mismatch.
    fn add_assign(&mut self, other: &Self) {
        if self.get_num_rows() != other.get_num_rows()
            || self.get_num_columns() != other.get_num_columns()
        {
            panic!(
                "Tried to add a '{}x{}' matrix and a '{}x{}' matrix.",
                self.get_num_rows(),
                self.get_num_columns(),
                other.get_num_rows(),
                other.get_num_columns()
            );
        }

        unsafe { fmpz_mat_add(&mut self.matrix, &self.matrix, &other.matrix) };
    }
}

arithmetic_assign_trait_borrowed_to_owned!(AddAssign, add_assign, MatZ, MatZ);

impl Add for &MatZ {
    type Output = MatZ;
    /// Implements the [`Add`] trait for two [`MatZ`] values.
    /// [`Add`] is implemented for any combination of [`MatZ`] and borrowed [`MatZ`].
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
    fn add(self, other: Self) -> Self::Output {
        self.add_safe(other).unwrap()
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
    /// - Returns a [`MathError`] of type
    ///   [`MathError::MismatchingMatrixDimension`] if the matrix dimensions
    ///   mismatch.
    pub fn add_safe(&self, other: &Self) -> Result<MatZ, MathError> {
        if self.get_num_rows() != other.get_num_rows()
            || self.get_num_columns() != other.get_num_columns()
        {
            return Err(MathError::MismatchingMatrixDimension(format!(
                "Tried to add a '{}x{}' matrix and a '{}x{}' matrix.",
                self.get_num_rows(),
                self.get_num_columns(),
                other.get_num_rows(),
                other.get_num_columns()
            )));
        }
        let mut out = MatZ::new(self.get_num_rows(), self.get_num_columns());
        unsafe {
            fmpz_mat_add(&mut out.matrix, &self.matrix, &other.matrix);
        }
        Ok(out)
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, MatZ, MatZ, MatZ);
arithmetic_trait_mixed_borrowed_owned!(Add, add, MatZ, MatZ, MatZ);

#[cfg(test)]
mod test_add_assign {
    use crate::integer::MatZ;
    use std::str::FromStr;

    /// Ensure that `add_assign` works for small numbers.
    #[test]
    fn correct_small() {
        let mut a = MatZ::identity(2, 2);
        let b = MatZ::from_str("[[4, 5],[-6, -1]]").unwrap();
        let cmp = MatZ::from_str("[[5, 5],[-6, 0]]").unwrap();

        a += b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `add_assign` works for large numbers.
    #[test]
    fn correct_large() {
        let mut a = MatZ::from_str(&format!("[[{}, 5],[{}, -1]]", i64::MAX, i64::MIN)).unwrap();
        let b = MatZ::from_str(&format!("[[{}, -6],[6, -1]]", i64::MAX)).unwrap();
        let cmp = MatZ::from_str(&format!(
            "[[{}, -1],[{}, -2]]",
            2 * (i64::MAX as u64),
            i64::MIN + 6
        ))
        .unwrap();

        a += b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `add_assign` works for different matrix dimensions.
    #[test]
    fn matrix_dimensions() {
        let dimensions = [(3, 3), (5, 1), (1, 4)];

        for (nr_rows, nr_cols) in dimensions {
            let mut a = MatZ::new(nr_rows, nr_cols);
            let b = MatZ::identity(nr_rows, nr_cols);

            a += b;

            assert_eq!(MatZ::identity(nr_rows, nr_cols), a);
        }
    }

    /// Ensure that `add_assign` is available for all types.
    #[test]
    fn availability() {
        let mut a = MatZ::new(2, 2);
        let b = MatZ::new(2, 2);

        a += &b;
        a += b;
    }
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
}
