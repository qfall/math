// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get information about a [`MatPolynomialRingZq`] matrix.

use super::MatPolynomialRingZq;
use crate::{
    error::MathError,
    integer::PolyOverZ,
    integer_mod_q::{ModulusPolynomialRingZq, PolynomialRingZq},
    traits::{GetEntry, GetNumColumns, GetNumRows},
    utils::index::evaluate_index,
};
use flint_sys::{fmpz_poly::fmpz_poly_struct, fmpz_poly_mat::fmpz_poly_mat_entry};
use std::fmt::Display;

impl MatPolynomialRingZq {
    /// Returns the modulus of the matrix as a [`ModulusPolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
    ///
    /// let modulus = poly_ring_mat.get_mod();
    /// ```
    pub fn get_mod(&self) -> ModulusPolynomialRingZq {
        self.modulus.clone()
    }
}

impl GetNumRows for MatPolynomialRingZq {
    /// Returns the number of rows of the matrix as an [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use qfall_math::integer::MatPolyOverZ;
    /// use qfall_math::traits::*;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
    ///
    /// let rows = poly_ring_mat.get_num_rows();
    /// ```
    fn get_num_rows(&self) -> i64 {
        self.matrix.get_num_rows()
    }
}

impl GetNumColumns for MatPolynomialRingZq {
    /// Returns the number of columns of the matrix as an [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use qfall_math::integer::MatPolyOverZ;
    /// use qfall_math::traits::*;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
    ///
    /// let rows = poly_ring_mat.get_num_columns();
    /// ```
    fn get_num_columns(&self) -> i64 {
        self.matrix.get_num_columns()
    }
}

impl GetEntry<PolyOverZ> for MatPolynomialRingZq {
    /// Outputs the [`PolyOverZ`] value of a specific matrix entry.
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    ///
    /// Negative indices can be used to index from the back, e.g., `-1` for
    /// the last element.
    ///
    /// Returns the [`PolyOverZ`] value of the matrix at the position of the given
    /// row and column or an error, if the number of rows or columns is
    /// greater than the matrix or negative.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use qfall_math::integer::{MatPolyOverZ, PolyOverZ};
    /// use qfall_math::traits::*;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 50").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
    ///
    /// let entry_1: PolyOverZ = poly_ring_mat.get_entry(1, 0).unwrap();
    /// let entry_2: PolyOverZ = poly_ring_mat.get_entry(-2, -1).unwrap();
    ///
    ///
    /// assert_eq!(entry_1, PolyOverZ::from(0));
    /// assert_eq!(entry_2, PolyOverZ::from(42));
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if `row` or `column` are greater than the matrix size.
    fn get_entry(
        &self,
        row: impl TryInto<i64> + Display,
        column: impl TryInto<i64> + Display,
    ) -> Result<PolyOverZ, MathError> {
        self.matrix.get_entry(row, column)
    }
}

impl GetEntry<PolynomialRingZq> for MatPolynomialRingZq {
    /// Outputs the [`PolynomialRingZq`] value of a specific matrix entry.
    ///
    /// Parameters:
    /// - `row`: specifies the row in which the entry is located
    /// - `column`: specifies the column in which the entry is located
    ///
    /// Negative indices can be used to index from the back, e.g., `-1` for
    /// the last element.
    ///
    /// Returns the [`PolynomialRingZq`] value of the matrix at the position of the given
    /// row and column or an error, if the number of rows or columns is
    /// greater than the matrix or negative.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq, PolynomialRingZq};
    /// use qfall_math::integer::{MatPolyOverZ, PolyOverZ};
    /// use qfall_math::traits::*;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 50").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
    ///
    /// let entry_1: PolynomialRingZq = poly_ring_mat.get_entry(0, 1).unwrap();
    /// let entry_2: PolynomialRingZq = poly_ring_mat.get_entry(-2, -1).unwrap();
    ///
    /// let value_cmp = PolynomialRingZq::from((&PolyOverZ::from(42), &modulus));
    /// assert_eq!(entry_1, value_cmp);
    /// assert_eq!(entry_1, entry_2);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if `row` or `column` are greater than the matrix size.
    fn get_entry(
        &self,
        row: impl TryInto<i64> + Display,
        column: impl TryInto<i64> + Display,
    ) -> Result<PolynomialRingZq, MathError> {
        Ok(PolynomialRingZq {
            poly: self.matrix.get_entry(row, column)?,
            modulus: self.get_mod(),
        })
    }
}

impl MatPolynomialRingZq {
    /// Outputs the row vector of the specified row.
    ///
    /// Parameters:
    /// - `row`: specifies the row of the matrix
    ///
    /// Returns a row vector of the matrix at the position of the given
    /// row or an error, if the number of rows is
    /// greater than the matrix or negative.
    ///
    /// # Examples
    /// ```rust
    /// use qfall_math::integer::MatPolyOverZ;
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();();
    /// let mat_poly = MatPolyOverZ::identity(3,3);
    /// let matrix = MatPolynomialRingZq::from((&mat_poly, &modulus));
    ///
    /// let row0 = matrix.get_row(0).unwrap(); // first row
    /// let row1 = matrix.get_row(1).unwrap(); // second row
    /// let row2 = matrix.get_row(2).unwrap(); // third row
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of the row is greater than the matrix or negative.
    pub fn get_row(&self, row: impl TryInto<i64> + Display) -> Result<Self, MathError> {
        let row_i64 = evaluate_index(row)?;

        if self.get_num_rows() <= row_i64 {
            return Err(MathError::OutOfBounds(
                format!("be smaller than {}", self.get_num_rows()),
                format!("{row_i64}"),
            ));
        }

        self.get_submatrix(row_i64, row_i64, 0, self.get_num_columns() - 1)
    }

    /// Outputs a column vector of the specified column.
    ///
    /// Input parameters:
    /// * `column`: specifies the column of the matrix
    ///
    /// Returns a column vector of the matrix at the position of the given
    /// column or an error, if the number of columns is
    /// greater than the matrix or negative.
    ///
    /// # Examples
    /// ```rust
    /// use qfall_math::integer::MatPolyOverZ;
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();();
    /// let mat_poly = MatPolyOverZ::identity(3,3);
    /// let matrix = MatPolynomialRingZq::from((&mat_poly, &modulus));
    ///
    /// let col0 = matrix.get_column(0).unwrap(); // first column
    /// let col1 = matrix.get_column(1).unwrap(); // second column
    /// let col1 = matrix.get_column(2).unwrap(); // third column
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of the column is greater than the matrix or negative.
    pub fn get_column(&self, column: impl TryInto<i64> + Display) -> Result<Self, MathError> {
        let column_i64 = evaluate_index(column)?;

        if self.get_num_columns() <= column_i64 {
            return Err(MathError::OutOfBounds(
                format!("be smaller than {}", self.get_num_columns()),
                format!("{column_i64}"),
            ));
        }

        self.get_submatrix(0, self.get_num_rows() - 1, column_i64, column_i64)
    }

    /// Returns a deep copy of the submatrix defined by the given parameters.
    /// All entries starting from `(row1, col1)` to `(row2, col2)`(inclusively) are collected in
    /// a new matrix.
    /// Note that `row1 >= row2` and `col1 >= col2` must hold. Otherwise the function will panic.
    ///
    /// Parameters:
    /// `row1`: The starting row of the submatrix
    /// `row2`: The ending row of the submatrix
    /// `col1`: The starting column of the submatrix
    /// `col2`: The ending column of the submatrix
    ///
    /// Returns the submatrix from `(row1, col1)` to `(row2, col2)`(inclusively).
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();();
    /// let mat = MatPolyOverZ::identity(3,3);
    /// let poly_ring_mat = MatPolynomialRingZq::from((&mat, &modulus));
    ///
    /// let sub_mat = poly_ring_mat.get_submatrix(0, 2, 1, 1).unwrap();
    ///
    /// let e2 = MatPolyOverZ::from_str("[[0],[1  1],[0]]").unwrap();
    /// let e2 = MatPolynomialRingZq::from((&e2, &modulus));
    /// assert_eq!(e2, sub_mat)
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
    /// if any provided row or column is greater than the matrix or negative.
    ///
    /// # Panics ...
    /// - if `col1 > col2` or `row1 > row2`.
    pub fn get_submatrix(
        &self,
        row1: impl TryInto<i64> + Display,
        row2: impl TryInto<i64> + Display,
        col1: impl TryInto<i64> + Display,
        col2: impl TryInto<i64> + Display,
    ) -> Result<Self, MathError> {
        Ok(MatPolynomialRingZq {
            matrix: self.matrix.get_submatrix(row1, row2, col1, col2)?,
            modulus: self.get_mod(),
        })
    }

    /// Efficiently collects all [`fmpz_poly_struct`]s in a [`MatPolynomialRingZq`] without cloning them.
    ///
    /// Hence, the values on the returned [`Vec`] are intended for short-term use
    /// as the access to [`fmpz_poly_struct`] values could lead to memory leaks or modified values
    /// once the [`MatPolynomialRingZq`] instance was modified or dropped.
    ///
    /// # Examples
    /// ```compile_fail
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[2  1 2, 3  1 1 1]]").unwrap();
    /// let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
    ///
    /// let fmpz_entries = poly_ring_mat.collect_entries();
    /// ```
    #[allow(dead_code)]
    pub(crate) fn collect_entries(&self) -> Vec<fmpz_poly_struct> {
        let mut entries: Vec<fmpz_poly_struct> = vec![];

        for row in 0..self.get_num_rows() {
            for col in 0..self.get_num_columns() {
                // efficiently get entry without cloning the entry itself
                let entry = unsafe { *fmpz_poly_mat_entry(&self.matrix.matrix, row, col) };
                entries.push(entry);
            }
        }

        entries
    }
}

#[cfg(test)]
mod test_get_entry {
    use crate::integer::{MatPolyOverZ, PolyOverZ};
    use crate::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq, PolynomialRingZq};
    use crate::traits::GetEntry;
    use std::str::FromStr;

    const LARGE_PRIME: u64 = u64::MAX - 58;

    /// Ensure that getting entries works on the edge.
    #[test]
    fn get_edges() {
        let modulus = ModulusPolynomialRingZq::from_str("2  42 17 mod 89").unwrap();
        let matrix = MatPolynomialRingZq::new(5, 10, &modulus);

        let entry1 = matrix.get_entry(0, 0).unwrap();
        let entry2 = matrix.get_entry(4, 9).unwrap();

        assert_eq!(PolyOverZ::default(), entry1);
        assert_eq!(PolyOverZ::default(), entry2);
    }

    /// Ensure that getting entries works with large numbers.
    #[test]
    fn big_positive() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("5  42 17 1 2 3 mod {LARGE_PRIME}"))
                .unwrap();
        let poly_mat =
            MatPolyOverZ::from_str(&format!("[[4  1 0 {} 1, 1  42],[0, 2  1 2]]", i64::MAX))
                .unwrap();
        let matrix = MatPolynomialRingZq::from((&poly_mat, &modulus));

        let entry = matrix.get_entry(0, 0).unwrap();

        assert_eq!(
            PolyOverZ::from_str(&format!("4  1 0 {} 1", i64::MAX)).unwrap(),
            entry
        );
    }

    /// Ensure that a wrong number of rows yields an Error.
    #[test]
    fn error_wrong_row() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("5  42 17 1 2 3 mod {LARGE_PRIME}"))
                .unwrap();
        let matrix = MatPolynomialRingZq::new(5, 10, &modulus);

        assert!(GetEntry::<PolynomialRingZq>::get_entry(&matrix, 5, 1).is_err());
        assert!(GetEntry::<PolynomialRingZq>::get_entry(&matrix, -6, 1).is_err());
        assert!(GetEntry::<PolyOverZ>::get_entry(&matrix, 5, 1).is_err());
        assert!(GetEntry::<PolyOverZ>::get_entry(&matrix, -6, 1).is_err());
    }

    /// Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("5  42 17 1 2 3 mod {LARGE_PRIME}"))
                .unwrap();
        let matrix = MatPolynomialRingZq::new(5, 10, &modulus);

        assert!(GetEntry::<PolynomialRingZq>::get_entry(&matrix, 1, 10).is_err());
        assert!(GetEntry::<PolynomialRingZq>::get_entry(&matrix, 1, -11).is_err());
        assert!(GetEntry::<PolyOverZ>::get_entry(&matrix, 1, 10).is_err());
        assert!(GetEntry::<PolyOverZ>::get_entry(&matrix, 1, -11).is_err());
    }

    /// Ensure that getting entries works with different types.
    #[test]
    fn diff_types() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("5  42 17 1 2 3 mod {LARGE_PRIME}"))
                .unwrap();
        let matrix = MatPolynomialRingZq::new(5, 10, &modulus);

        let _: PolyOverZ = matrix.get_entry(0, 0).unwrap();
        let _: PolynomialRingZq = matrix.get_entry(0, 0).unwrap();
    }
}

#[cfg(test)]
mod test_get_num {
    use crate::{
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
        traits::{GetNumColumns, GetNumRows},
    };
    use std::str::FromStr;

    /// Ensure that the getter for number of rows works correctly.
    #[test]
    fn num_rows() {
        let modulus = ModulusPolynomialRingZq::from_str("2  42 17 mod 89").unwrap();
        let matrix = MatPolynomialRingZq::new(5, 10, &modulus);

        assert_eq!(matrix.get_num_rows(), 5);
    }

    /// Ensure that the getter for number of columns works correctly.
    #[test]
    fn num_columns() {
        let modulus = ModulusPolynomialRingZq::from_str("2  42 17 mod 89").unwrap();
        let matrix = MatPolynomialRingZq::new(5, 10, &modulus);

        assert_eq!(matrix.get_num_columns(), 10);
    }
}

#[cfg(test)]
mod test_mod {
    use crate::{
        integer::MatPolyOverZ,
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
    };
    use std::str::FromStr;

    const LARGE_PRIME: u64 = u64::MAX - 58;

    /// Ensure that the getter for modulus works correctly.
    #[test]
    fn get_mod() {
        let modulus = ModulusPolynomialRingZq::from_str("2  42 17 mod 89").unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let matrix = MatPolynomialRingZq::from((&poly_mat, &modulus));

        assert_eq!(
            matrix.get_mod(),
            ModulusPolynomialRingZq::from_str("2  42 17 mod 89").unwrap()
        );
    }

    /// Ensure that the getter for modulus works with large numbers.
    #[test]
    fn get_mod_large() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("2  42 17 mod {LARGE_PRIME}")).unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let matrix = MatPolynomialRingZq::from((&poly_mat, &modulus));

        assert_eq!(
            matrix.get_mod(),
            ModulusPolynomialRingZq::from_str(&format!("2  42 17 mod {LARGE_PRIME}")).unwrap()
        );
    }

    /// Ensure that no memory leak occurs in get_mod.
    #[test]
    fn get_mod_memory() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("2  42 17 mod {LARGE_PRIME}")).unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let matrix = MatPolynomialRingZq::from((&poly_mat, &modulus));
        let _ = matrix.get_mod();
        let _ = ModulusPolynomialRingZq::from_str(&format!("2  42 17 mod {LARGE_PRIME}")).unwrap();

        let modulus = matrix.get_mod();

        assert_eq!(
            modulus,
            ModulusPolynomialRingZq::from_str(&format!("2  42 17 mod {LARGE_PRIME}")).unwrap()
        );
    }
}

#[cfg(test)]
mod test_get_vec {
    use crate::{
        integer::MatPolyOverZ,
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
    };
    use std::str::FromStr;

    /// Ensure that getting a row works.
    #[test]
    fn get_row_works() {
        let matrix = MatPolyOverZ::from_str(&format!(
            "[[0,0,0],[1  42,1  {},1  {}]]",
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();
        let matrix = MatPolynomialRingZq::from((&matrix, &modulus));

        let row1 = matrix.get_row(0).unwrap();
        let row2 = matrix.get_row(1).unwrap();

        let cmp1 = MatPolyOverZ::from_str("[[0,0,0]]").unwrap();
        let cmp2 =
            MatPolyOverZ::from_str(&format!("[[1  42,1  {},1  {}]]", i64::MAX, i64::MIN)).unwrap();
        let cmp1 = MatPolynomialRingZq::from((&cmp1, &modulus));
        let cmp2 = MatPolynomialRingZq::from((&cmp2, &modulus));
        assert_eq!(cmp1, row1);
        assert_eq!(cmp2, row2);
    }

    /// Ensure that getting a column works.
    #[test]
    fn get_column_works() {
        let matrix = MatPolyOverZ::from_str(&format!(
            "[[1  42,0,2  17 42],[1  {},0,2  17 42],[1  {},0,2  17 42]]",
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();
        let matrix = MatPolynomialRingZq::from((&matrix, &modulus));

        let column1 = matrix.get_column(0).unwrap();
        let column2 = matrix.get_column(1).unwrap();
        let column3 = matrix.get_column(2).unwrap();

        let cmp1 =
            MatPolyOverZ::from_str(&format!("[[1  42],[1  {}],[1  {}]]", i64::MAX, i64::MIN))
                .unwrap();
        let cmp2 = MatPolyOverZ::from_str("[[0],[0],[0]]").unwrap();
        let cmp3 = MatPolyOverZ::from_str("[[2  17 42],[2  17 42],[2  17 42]]").unwrap();
        let cmp1 = MatPolynomialRingZq::from((&cmp1, &modulus));
        let cmp2 = MatPolynomialRingZq::from((&cmp2, &modulus));
        let cmp3 = MatPolynomialRingZq::from((&cmp3, &modulus));
        assert_eq!(cmp1, column1);
        assert_eq!(cmp2, column2);
        assert_eq!(cmp3, column3);
    }

    /// Ensure that wrong row and column dimensions yields an error.
    #[test]
    fn wrong_dim_error() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();
        let matrix = MatPolyOverZ::from_str(&format!(
            "[[1  17,2  17 42,3  1 1 1],[1  {},1  1,2  2 3],[1  {},1  142,1  1]]",
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let matrix = MatPolynomialRingZq::from((&matrix, &modulus));

        let row1 = matrix.get_row(-1);
        let row2 = matrix.get_row(4);
        let column1 = matrix.get_column(-1);
        let column2 = matrix.get_column(4);

        assert!(row1.is_err());
        assert!(row2.is_err());
        assert!(column1.is_err());
        assert!(column2.is_err());
    }
}

#[cfg(test)]
mod test_get_submatrix {
    use crate::{
        integer::{MatPolyOverZ, Z},
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
        traits::{GetNumColumns, GetNumRows},
    };
    use std::str::FromStr;

    /// Ensures that getting the entire matrix as a submatrix works.
    #[test]
    fn entire_matrix() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();
        let mat = MatPolyOverZ::identity(5, 5);
        let mat = MatPolynomialRingZq::from((&mat, &modulus));

        let sub_mat = mat.get_submatrix(0, 4, 0, 4).unwrap();

        assert_eq!(mat, sub_mat)
    }

    /// Ensures that a single matrix entry can be retrieved.
    #[test]
    fn matrix_single_entry() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();
        let mat = MatPolyOverZ::identity(5, 5);
        let mat = MatPolynomialRingZq::from((&mat, &modulus));

        let sub_mat = mat.get_submatrix(0, 0, 0, 0).unwrap();

        let cmp_mat = MatPolyOverZ::identity(1, 1);
        let cmp_mat = MatPolynomialRingZq::from((&cmp_mat, &modulus));
        assert_eq!(cmp_mat, sub_mat)
    }

    /// Ensures that the dimensions of the submatrix are correct.
    #[test]
    fn correct_dimensions() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();
        let mat = MatPolyOverZ::identity(100, 100);
        let mat = MatPolynomialRingZq::from((&mat, &modulus));

        let sub_mat = mat.get_submatrix(1, 37, 0, 29).unwrap();

        assert_eq!(37, sub_mat.get_num_rows());
        assert_eq!(30, sub_mat.get_num_columns())
    }

    /// Ensures that a submatrix can be correctly retrieved for a matrix with large
    /// entries.
    #[test]
    fn large_entries() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();
        let mat = MatPolyOverZ::from_str(&format!(
            "[[2  -1 {}, 1  2, 1  3],[1  1, 1  {}, 1  3]]",
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let mat = MatPolynomialRingZq::from((&mat, &modulus));

        let sub_mat = mat.get_submatrix(0, 1, 0, 1).unwrap();

        let cmp_mat = MatPolyOverZ::from_str(&format!(
            "[[2  -1 {}, 1  2],[1  1, 1  {}]]",
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let cmp_mat = MatPolynomialRingZq::from((&cmp_mat, &modulus));
        assert_eq!(cmp_mat, sub_mat)
    }

    /// Ensures that an error is returned if coordinates are addressed that are not
    /// within the matrix.
    #[test]
    fn invalid_coordinates() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();
        let mat = MatPolyOverZ::identity(10, 10);
        let mat = MatPolynomialRingZq::from((&mat, &modulus));

        assert!(mat.get_submatrix(0, 0, 0, 10).is_err());
        assert!(mat.get_submatrix(0, 10, 0, 0).is_err());
        assert!(mat.get_submatrix(0, 0, -1, 0).is_err());
        assert!(mat.get_submatrix(-1, 0, 0, 0).is_err());
    }

    /// Ensures that the function panics if no columns of the matrix are addressed.
    #[test]
    #[should_panic]
    fn no_columns() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();
        let mat = MatPolyOverZ::identity(10, 10);
        let mat = MatPolynomialRingZq::from((&mat, &modulus));

        let _ = mat.get_submatrix(0, 0, 6, 5);
    }

    /// Ensures that the function panics if no rows of the matrix are addressed.
    #[test]
    #[should_panic]
    fn no_rows() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();
        let mat = MatPolyOverZ::identity(10, 10);
        let mat = MatPolynomialRingZq::from((&mat, &modulus));

        let _ = mat.get_submatrix(5, 4, 0, 0);
    }

    /// Ensure that the submatrix function can be called with several types.
    #[test]
    fn availability() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();
        let mat = MatPolyOverZ::identity(10, 10);
        let mat = MatPolynomialRingZq::from((&mat, &modulus));

        let _ = mat.get_submatrix(0_i8, 0_i8, 0_i8, 0_i8);
        let _ = mat.get_submatrix(0_i16, 0_i16, 0_i16, 0_i16);
        let _ = mat.get_submatrix(0_i32, 0_i32, 0_i32, 0_i32);
        let _ = mat.get_submatrix(0_i64, 0_i64, 0_i64, 0_i64);
        let _ = mat.get_submatrix(0_u8, 0_u8, 0_u8, 0_u8);
        let _ = mat.get_submatrix(0_u16, 0_i16, 0_u16, 0_u16);
        let _ = mat.get_submatrix(0_u32, 0_i32, 0_u32, 0_u32);
        let _ = mat.get_submatrix(0_u64, 0_i64, 0_u64, 0_u64);
        let _ = mat.get_submatrix(&Z::ZERO, &Z::ZERO, &Z::ZERO, &Z::ZERO);
    }
}

#[cfg(test)]
mod test_collect_entries {
    use crate::integer::{MatPolyOverZ, PolyOverZ};
    use crate::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    use flint_sys::fmpz_poly::fmpz_poly_set;
    use std::str::FromStr;

    const LARGE_PRIME: u64 = u64::MAX - 58;

    /// Ensures that all entries of the polynomial are actually collected in the vector.
    #[test]
    fn all_entries_collected() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {LARGE_PRIME}")).unwrap();
        let poly_mat1 = MatPolyOverZ::from_str(&format!(
            "[[4  -1 0 3 1, 1  {}],[2  1 2, 3  {} 1 1]]",
            i64::MAX,
            i64::MIN + 58,
        ))
        .unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
        let poly_mat2 = MatPolyOverZ::from_str("[[1  42, 2  1 17]]").unwrap();
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus));

        let entries_1 = poly_ring_mat1.collect_entries();
        let entries_2 = poly_ring_mat2.collect_entries();

        let mut entry1 = PolyOverZ::default();
        let mut entry2 = entry1.clone();
        let mut entry3 = entry1.clone();

        unsafe { fmpz_poly_set(&mut entry1.poly, &entries_1[1]) }
        unsafe { fmpz_poly_set(&mut entry2.poly, &entries_1[3]) }
        unsafe { fmpz_poly_set(&mut entry3.poly, &entries_2[0]) }

        assert_eq!(entries_1.len(), 4);
        assert_eq!(
            PolyOverZ::from_str(&format!("1  {}", i64::MAX)).unwrap(),
            entry1
        );
        assert_eq!(
            PolyOverZ::from_str(&format!("3  {} 1 1", i64::MAX)).unwrap(),
            entry2
        );

        assert_eq!(entries_2.len(), 2);
        assert_eq!(PolyOverZ::from_str("1  42").unwrap(), entry3);
    }

    /// Ensure that the doc-test compiles and works correctly.
    #[test]
    fn doc_test() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[2  1 2, 3  1 1 1]]").unwrap();
        let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));

        let _ = poly_ring_mat.collect_entries();
    }
}
