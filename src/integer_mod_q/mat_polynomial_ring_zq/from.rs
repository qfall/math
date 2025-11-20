// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`MatPolynomialRingZq`] value from other types.
//!
//! The explicit functions contain the documentation.

use super::MatPolynomialRingZq;
use crate::{
    error::{MathError, StringConversionError},
    integer::{MatPolyOverZ, Z},
    integer_mod_q::{
        MatNTTPolynomialRingZq, ModulusPolynomialRingZq, NTTPolynomialRingZq, PolynomialRingZq,
    },
    traits::MatrixSetEntry,
};
use std::str::FromStr;

impl From<&mut MatNTTPolynomialRingZq> for MatPolynomialRingZq {
    /// Creates a polynomial ring matrix of type [`MatPolynomialRingZq`] from
    /// the corresponding [`MatNTTPolynomialRingZq`].
    ///
    /// Parameters:
    /// - `matrix`: the polynomial matrix defining each entry.
    ///
    /// Returns a new [`MatPolynomialRingZq`] with the entries from `matrix`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, MatNTTPolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    /// let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
    /// modulus.set_ntt_unchecked(64);
    /// let mut ntt_mat = MatNTTPolynomialRingZq::sample_uniform(1, 1, &modulus);
    ///
    /// let poly_ring_mat = MatPolynomialRingZq::from(&mut ntt_mat);
    /// ```
    ///
    /// # Panics ...
    /// - if the [`NTTBasisPolynomialRingZq`](crate::integer_mod_q::NTTBasisPolynomialRingZq) in `modulus`
    ///   is not set.
    fn from(matrix: &mut MatNTTPolynomialRingZq) -> Self {
        let height = matrix.nr_rows;
        let width = matrix.nr_columns;

        let mut res = MatPolynomialRingZq::new(height, width, &matrix.modulus);
        for column in (0..width).rev() {
            for row in (0..height).rev() {
                let index = matrix.modulus.get_degree() as usize * row
                    + matrix.modulus.get_degree() as usize * matrix.nr_rows * column;
                let entry = PolynomialRingZq::from(NTTPolynomialRingZq {
                    poly: matrix.matrix.split_off(index).iter().map(Z::from).collect(),
                    modulus: matrix.modulus.clone(),
                });
                unsafe { res.set_entry_unchecked(row as i64, column as i64, entry) };
            }
        }
        res
    }
}

impl FromStr for MatPolynomialRingZq {
    type Err = MathError;

    /// Creates a [`MatPolynomialRingZq`] matrix from a [`String`].
    ///
    /// **Warning**: Each entry is parsed as a [`PolyOverZ`](crate::integer::PolyOverZ::from_str) object.
    /// If an entry string starts with a correctly formatted [`PolyOverZ`](crate::integer::PolyOverZ::from_str) object,
    /// the rest of this entry string is ignored. This means that the entry input
    /// string `"4  0 1 2 3"` is the same as `"4  0 1 2 3 4 5 6 7"`.
    ///
    /// Parameters:
    /// - `string`: the matrix of form: `"[[poly_1, poly_2, poly_3],[poly_4, poly_5, poly_6]] / poly_7 mod 11"`
    ///   for a 2x3 matrix where the first three polynomials are in the first row,
    ///   the second three are in the second row, and the seventh polynomial and 11 form the modulus.
    ///
    /// Note that the strings for entries, the polynomial modulus and the integer modulus are trimmed,
    /// i.e. all whitespaces around all values are ignored.
    ///
    /// Returns a [`MatPolynomialRingZq`] or an error if the matrix is not formatted in a suitable way,
    /// the number of rows or columns is too large (must fit into [`i64`]),
    /// the number of entries in rows is unequal, or if an entry is not formatted correctly.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let matrix = MatPolynomialRingZq::from_str("[[2  2 2, 1  2],[0, 1  3]] / 2  3 3 mod 24").unwrap();
    /// ```
    ///
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let str_1 = "[[2  2 2, 1  2],[0, 1  3]] / 2  3 3 mod 24";
    /// let matrix = MatPolynomialRingZq::from_str(str_1).unwrap();
    /// ```
    ///
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let string = String::from("[[2  2 2, 1  2],[0, 1  3]] / 2  3 3 mod 24");
    /// let matrix = MatPolynomialRingZq::from_str(&string).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::StringConversionError`],
    ///     - if the matrix is not formatted in a suitable way,
    ///     - if the number of rows or columns is too large (must fit into i64),
    ///     - if the number of entries in rows is unequal,
    ///     - if the delimiter `/` and `mod` could not be found,
    ///     - if the modulus is not formatted correctly,
    ///       for further information see [`PolyOverZq::from_str`](crate::integer_mod_q::PolyOverZq::from_str), or
    ///     - if an entry is not formatted correctly.
    ///       For further information see [`PolyOverZ::from_str`](crate::integer::PolyOverZ::from_str).
    /// - Returns a MathError of type InvalidModulus
    ///     - if modulus is smaller than 2, or
    ///     - if the modulus polynomial is 0.
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns are not suited to create a matrix.
    ///   For further information see [`MatPolyOverZ::new`].
    fn from_str(string: &str) -> Result<Self, MathError> {
        let (matrix, modulus) = match string.split_once("/") {
            Some((matrix, modulus)) => (matrix, modulus),
            None => {
                return Err(StringConversionError::InvalidMatrix(format!(
                    "The delimiter '/' could not be found: {string}"
                )))?
            }
        };

        let matrix = MatPolyOverZ::from_str(matrix.trim())?;
        let modulus = ModulusPolynomialRingZq::from_str(modulus.trim())?;

        Ok(Self::from((matrix, modulus)))
    }
}

impl<Matrix: Into<MatPolyOverZ>, Mod: Into<ModulusPolynomialRingZq>> From<(Matrix, Mod)>
    for MatPolynomialRingZq
{
    /// Creates a polynomial ring matrix of type [`MatPolynomialRingZq`] from
    /// a value that implements [`Into<MatPolyOverZ>`] and a value that
    /// implements [`Into<ModulusPolynomialRingZq>`].
    ///
    /// Parameters:
    /// - `matrix`: the polynomial matrix defining each entry.
    /// - `modulus`: the modulus that is applied to each polynomial.
    ///
    /// Returns a new [`MatPolynomialRingZq`] with the entries from `matrix`
    /// under the modulus `modulus`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    ///
    /// let poly_ring_mat = MatPolynomialRingZq::from((poly_mat, modulus));
    /// ```
    fn from((matrix, modulus): (Matrix, Mod)) -> Self {
        let mut out = Self {
            matrix: matrix.into(),
            modulus: modulus.into(),
        };
        out.reduce();
        out
    }
}

impl From<&MatPolynomialRingZq> for MatPolynomialRingZq {
    /// Alias for [`MatPolynomialRingZq::clone`].
    fn from(value: &MatPolynomialRingZq) -> Self {
        value.clone()
    }
}

#[cfg(test)]
mod test_from_str {
    use crate::{integer::PolyOverZ, integer_mod_q::MatPolynomialRingZq, traits::MatrixGetEntry};
    use std::str::FromStr;

    /// Ensure that initialization works.
    #[test]
    fn init_works() {
        let matrix_str_1 = "[[1  2, 0, 1  3],[1  3, 1  4, 1  5]] / 2  1 1 mod 6";

        let matrix: PolyOverZ = MatPolynomialRingZq::from_str(matrix_str_1)
            .unwrap()
            .get_entry(0, 0)
            .unwrap();

        assert_eq!(PolyOverZ::from(2), matrix);
    }

    /// Ensure that entries are correctly reduced.
    #[test]
    fn reduce_works() {
        let matrix_str_1 = "[[1  2, 0, 1  3],[1  3, 2  2 2, 1  5]] / 2  1 1 mod 3";

        let matrix: PolyOverZ = MatPolynomialRingZq::from_str(matrix_str_1)
            .unwrap()
            .get_entry(1, 0)
            .unwrap();

        assert_eq!(PolyOverZ::default(), matrix);
    }

    /// Ensure that initialization with positive numbers that are larger than [`i64`] works.
    #[test]
    fn init_works_large_numbers() {
        let matrix_string = format!(
            "[[1  {}, 0],[1  3, 1  4]] / 2  1 1 mod {}",
            u64::MAX - 1,
            u64::MAX
        );
        let matrix: PolyOverZ = MatPolynomialRingZq::from_str(&matrix_string)
            .unwrap()
            .get_entry(0, 0)
            .unwrap();

        assert_eq!(PolyOverZ::from(u64::MAX - 1), matrix);
    }

    /// Ensure that entries can have leading and trailing whitespaces.
    #[test]
    fn whitespaces_in_entries_works() {
        let matrix_str_1 =
            "[[1  2    ,    0 , 1  3],[   1  3, 1  4, 1  5  ]]   /     2  1 1   mod6  ";

        let matrix: PolyOverZ = MatPolynomialRingZq::from_str(matrix_str_1)
            .unwrap()
            .get_entry(0, 2)
            .unwrap();

        assert_eq!(PolyOverZ::from(3), matrix);
    }

    /// Ensure that a wrong format causes an error.
    #[test]
    fn wrong_format_error() {
        let matrix_str_1 = "[1  2, 0],[1  3, 1  4]] / 2  1 1 mod 6";
        let matrix_str_2 = "[[1  2, 0][1  3, 1  4]] / 2  1 1 mod 6";
        let matrix_str_3 = "[[1  2, 0],1  3, 1  4]] / 2  1 1 mod 6";
        let matrix_str_4 = "[1  2, 0] / 2  1 1 mod 6";
        let matrix_str_5 = "[ [1  2, 0],[1  3, 1  4]] / 2  1 1 mod 6";
        let matrix_str_6 = "[[1  2, 0],[1  3, 1  4]8] / 2  1 1 mod 6";
        let matrix_str_7 = "[[1  2, 0],[1  3, 1  4]] / 2  1 1 mo 6";
        let matrix_str_8 = " / 2  1 1 mod 6";
        let matrix_str_9 = "[[1  2, 0],[1  3, 1  4]]";
        let matrix_str_10 = "[[1  2, 0],[1  3, 1  4]] mod 6";
        let matrix_str_11 = "[[1  2, 0],[1  3, 1  4]] / 6";
        let matrix_str_12 = "";
        let matrix_str_13 = "[] mod 6";
        let matrix_str_14 = "[[]] mod 6";

        assert!(MatPolynomialRingZq::from_str(matrix_str_1).is_err());
        assert!(MatPolynomialRingZq::from_str(matrix_str_2).is_err());
        assert!(MatPolynomialRingZq::from_str(matrix_str_3).is_err());
        assert!(MatPolynomialRingZq::from_str(matrix_str_4).is_err());
        assert!(MatPolynomialRingZq::from_str(matrix_str_5).is_err());
        assert!(MatPolynomialRingZq::from_str(matrix_str_6).is_err());
        assert!(MatPolynomialRingZq::from_str(matrix_str_7).is_err());
        assert!(MatPolynomialRingZq::from_str(matrix_str_8).is_err());
        assert!(MatPolynomialRingZq::from_str(matrix_str_9).is_err());
        assert!(MatPolynomialRingZq::from_str(matrix_str_10).is_err());
        assert!(MatPolynomialRingZq::from_str(matrix_str_11).is_err());
        assert!(MatPolynomialRingZq::from_str(matrix_str_12).is_err());
        assert!(MatPolynomialRingZq::from_str(matrix_str_13).is_err());
        assert!(MatPolynomialRingZq::from_str(matrix_str_14).is_err());
    }
}

#[cfg(test)]
mod test_from {
    use crate::{
        integer::{MatPolyOverZ, MatZ},
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq, PolyOverZq},
    };
    use std::str::FromStr;

    const LARGE_PRIME: u64 = u64::MAX - 58;

    /// Checks whether `from` is available for all types implementing
    /// [`Into<MatPolyOverZ>`] and [`Into<ModulusPolynomialRingZq>`]
    #[test]
    fn availability() {
        let modulus_1 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let modulus_2 = PolyOverZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_mat_2 = MatZ::from_str("[[1, 2, 3],[4, 5, 6]]").unwrap();

        let _ = MatPolynomialRingZq::from((&poly_mat_1, &modulus_1));
        let _ = MatPolynomialRingZq::from((&poly_mat_1, modulus_1.clone()));
        let _ = MatPolynomialRingZq::from((poly_mat_1.clone(), &modulus_1));
        let _ = MatPolynomialRingZq::from((&poly_mat_2, &modulus_2));
        let _ = MatPolynomialRingZq::from((&poly_mat_2, modulus_2.clone()));
        let _ = MatPolynomialRingZq::from((poly_mat_2.clone(), &modulus_2));
        let _ = MatPolynomialRingZq::from((&poly_mat_1, &modulus_2));
        let _ = MatPolynomialRingZq::from((&poly_mat_2, modulus_1));
    }

    /// Ensure that the modulus is applied with a large prime and large coefficients
    #[test]
    fn is_reduced_large() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {LARGE_PRIME}")).unwrap();

        let poly_mat = MatPolyOverZ::from_str(&format!(
            "[[4  {} {} 1 1, 1  42],[0, 2  1 2]]",
            LARGE_PRIME + 2,
            u64::MAX
        ))
        .unwrap();
        let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));

        let cmp_poly_mat = MatPolyOverZ::from_str("[[3  1 58 1, 1  42],[0, 2  1 2]]").unwrap();
        let cmp_poly_ring_mat = MatPolynomialRingZq::from((&cmp_poly_mat, &modulus));

        assert_eq!(poly_ring_mat, cmp_poly_ring_mat);
    }

    /// Ensure that two ring elements that are instantiated the same way are equal
    #[test]
    fn same_instantiation() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {LARGE_PRIME}")).unwrap();
        let poly_mat = MatPolyOverZ::from_str(&format!(
            "[[4  {} {} 1 1, 1  42],[0, 2  1 2]]",
            LARGE_PRIME + 2,
            u64::MAX
        ))
        .unwrap();

        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat, &modulus));
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat, &modulus));

        assert_eq!(poly_ring_mat_1, poly_ring_mat_2);
    }

    /// Ensure that from works for different dimensions
    #[test]
    fn different_dimensions() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("3  1 9 12 mod {LARGE_PRIME}")).unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[2  1 8],[2  1 2]]").unwrap();
        let poly_mat_2 = MatPolyOverZ::from_str("[[2  1 8, 1  42, 0],[0, 2  1 2, 1  17]]").unwrap();
        let poly_mat_3 = MatPolyOverZ::from_str("[[2  1 8]]").unwrap();

        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));
        let poly_ring_mat_3 = MatPolynomialRingZq::from((&poly_mat_3, &modulus));

        assert_eq!(poly_ring_mat_1.matrix, poly_mat_1);
        assert_eq!(poly_ring_mat_2.matrix, poly_mat_2);
        assert_eq!(poly_ring_mat_3.matrix, poly_mat_3);
    }
}
