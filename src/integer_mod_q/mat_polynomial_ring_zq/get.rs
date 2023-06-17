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
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
    ///
    /// let entry: PolyOverZ = poly_ring_mat.get_entry(1,0).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is greater than the matrix or negative.
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
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
    ///
    /// let entry: PolynomialRingZq = poly_ring_mat.get_entry(1,0).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds)
    /// if the number of rows or columns is greater than the matrix or negative.
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
    use crate::{error::MathError, traits::GetEntry};
    use std::str::FromStr;

    const BITPRIME64: u64 = u64::MAX - 58;

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
            ModulusPolynomialRingZq::from_str(&format!("5  42 17 1 2 3 mod {}", BITPRIME64))
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
            ModulusPolynomialRingZq::from_str(&format!("5  42 17 1 2 3 mod {}", BITPRIME64))
                .unwrap();
        let matrix = MatPolynomialRingZq::new(5, 10, &modulus);
        let entry1: Result<PolyOverZ, MathError> = matrix.get_entry(5, 1);
        let entry2: Result<PolyOverZ, MathError> = matrix.get_entry(5, 10);

        assert!(entry1.is_err());
        assert!(entry2.is_err());
    }

    /// Ensure that a wrong number of columns yields an Error.
    #[test]
    fn error_wrong_column() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("5  42 17 1 2 3 mod {}", BITPRIME64))
                .unwrap();
        let matrix = MatPolynomialRingZq::new(5, 10, &modulus);
        let entry: Result<PolyOverZ, MathError> = matrix.get_entry(1, 100);

        assert!(entry.is_err());
    }

    /// Ensure that getting entries works with different types.
    #[test]
    fn diff_types() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("5  42 17 1 2 3 mod {}", BITPRIME64))
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

    const BITPRIME64: u64 = u64::MAX - 58;

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
            ModulusPolynomialRingZq::from_str(&format!("2  42 17 mod {}", BITPRIME64)).unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let matrix = MatPolynomialRingZq::from((&poly_mat, &modulus));

        assert_eq!(
            matrix.get_mod(),
            ModulusPolynomialRingZq::from_str(&format!("2  42 17 mod {}", BITPRIME64)).unwrap()
        );
    }

    /// Ensure that no memory leak occurs in get_mod.
    #[test]
    fn get_mod_memory() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("2  42 17 mod {}", BITPRIME64)).unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let matrix = MatPolynomialRingZq::from((&poly_mat, &modulus));
        let _ = matrix.get_mod();
        let _ = ModulusPolynomialRingZq::from_str(&format!("2  42 17 mod {}", BITPRIME64)).unwrap();

        let modulus = matrix.get_mod();

        assert_eq!(
            modulus,
            ModulusPolynomialRingZq::from_str(&format!("2  42 17 mod {}", BITPRIME64)).unwrap()
        );
    }
}

#[cfg(test)]
mod test_collect_entries {
    use crate::integer::{MatPolyOverZ, PolyOverZ};
    use crate::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    use flint_sys::fmpz_poly::fmpz_poly_set;
    use std::str::FromStr;

    const BITPRIME64: u64 = u64::MAX - 58;

    #[test]
    fn all_entries_collected() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", BITPRIME64)).unwrap();
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

    #[test]
    fn doc_test() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[2  1 2, 3  1 1 1]]").unwrap();
        let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));

        let _ = poly_ring_mat.collect_entries();
    }
}
