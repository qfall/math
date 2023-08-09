// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Initialize a [`MatPolynomialRingZq`] with common defaults, e.g., zero and identity.

use super::MatPolynomialRingZq;
use crate::{integer::MatPolyOverZ, integer_mod_q::ModulusPolynomialRingZq};
use std::fmt::Display;

impl MatPolynomialRingZq {
    /// Creates a new matrix with `num_rows` rows, `num_cols` columns,
    /// zeros as entries and `modulus` as the modulus.
    ///
    /// Parameters:
    /// - `num_rows`: number of rows the new matrix should have
    /// - `num_cols`: number of columns the new matrix should have
    /// - `modulus`: the common modulus of the matrix entries
    ///
    /// Returns a new [`MatPolynomialRingZq`] instance of the provided dimensions.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let poly_mod = PolyOverZq::from_str("3  1 0 1 mod 17").unwrap();
    /// let modulus = ModulusPolynomialRingZq::try_from(&poly_mod).unwrap();
    ///
    /// let matrix = MatPolynomialRingZq::new(5, 10, &modulus);
    /// ```
    ///
    /// # Panics ...
    /// - if the number of rows or columns is negative, zero, or does not fit into an [`i64`].
    #[allow(dead_code)]
    pub fn new(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
        modulus: &ModulusPolynomialRingZq,
    ) -> Self {
        let matrix = MatPolyOverZ::new(num_rows, num_cols);

        MatPolynomialRingZq {
            matrix,
            modulus: modulus.clone(),
        }
    }

    /// Generate a `num_rows` times `num_columns` matrix with `1` on the
    /// diagonal and `0` anywhere else with a given modulus.
    ///
    /// Parameters:
    /// - `rum_rows`: the number of rows of the identity matrix
    /// - `num_columns`: the number of columns of the identity matrix
    /// - `modulus`: the polynomial mod q which serves as the modulus of the matrix
    ///
    /// Returns a matrix with `1` across the diagonal and `0` anywhere else.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
    /// let matrix = MatPolynomialRingZq::identity(2, 3, &modulus);
    ///
    /// let identity = MatPolynomialRingZq::identity(10, 10, &modulus);
    /// ```
    ///
    /// # Panics ...
    /// - if the provided number of rows and columns are not suited to create a matrix.
    /// For further information see [`MatPolyOverZ::new`].
    pub fn identity(
        num_rows: impl TryInto<i64> + Display,
        num_cols: impl TryInto<i64> + Display,
        modulus: &ModulusPolynomialRingZq,
    ) -> Self {
        let matrix = MatPolyOverZ::identity(num_rows, num_cols);
        MatPolynomialRingZq::from((&matrix, modulus))
    }
}

#[cfg(test)]
mod test_new {
    use crate::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq, PolyOverZq};
    use std::str::FromStr;

    const LARGE_PRIME: u64 = u64::MAX - 58;

    /// Ensure that initialization works.
    #[test]
    fn initialization() {
        let poly_mod = PolyOverZq::from_str("3  1 0 1 mod 17").unwrap();
        let modulus = ModulusPolynomialRingZq::try_from(&poly_mod).unwrap();

        let _ = MatPolynomialRingZq::new(2, 2, &modulus);
    }

    // TODO: add a test for zero entries

    /// Ensure that a new zero matrix fails with `0` as `num_cols`.
    #[should_panic]
    #[test]
    fn error_zero_num_cols() {
        let poly_mod = PolyOverZq::from_str("3  1 0 1 mod 17").unwrap();
        let modulus = ModulusPolynomialRingZq::try_from(&poly_mod).unwrap();

        let _ = MatPolynomialRingZq::new(1, 0, &modulus);
    }

    /// Ensure that a new zero matrix fails with `0` as `num_rows`.
    #[should_panic]
    #[test]
    fn error_zero_num_rows() {
        let poly_mod = PolyOverZq::from_str("3  1 0 1 mod 17").unwrap();
        let modulus = ModulusPolynomialRingZq::try_from(&poly_mod).unwrap();

        let _ = MatPolynomialRingZq::new(0, 1, &modulus);
    }

    /// Ensure that the modulus can be large.
    #[test]
    fn large_modulus() {
        let poly_mod =
            PolyOverZq::from_str(&format!("3  1 {} 1 mod {LARGE_PRIME}", i64::MAX)).unwrap();
        let modulus = ModulusPolynomialRingZq::try_from(&poly_mod).unwrap();

        let _ = MatPolynomialRingZq::new(2, 2, &modulus);
    }
}

#[cfg(test)]
mod test_identity {
    use crate::{
        integer::PolyOverZ,
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
        traits::{GetEntry, GetNumRows, GetNumColumns},
    };
    use std::str::FromStr;

    /// Tests if an identity matrix is set from a zero matrix.
    #[test]
    fn identity() {
        let modulus = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
        let matrix = MatPolynomialRingZq::identity(10, 10, &modulus);

        for i in 0..matrix.get_num_rows() {
            for j in 0..matrix.get_num_columns() {
                if i != j {
                    assert_eq!(PolyOverZ::default(), matrix.get_entry(i, j).unwrap());
                } else {
                    assert_eq!(
                        PolyOverZ::from_str("1  1").unwrap(),
                        matrix.get_entry(i, j).unwrap()
                    )
                }
            }
        }
    }

    /// Tests if function works for a non-square matrix.
    #[test]
    fn non_square_works() {
        let modulus = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
        let matrix = MatPolynomialRingZq::identity(10, 7, &modulus);

        for i in 0..10 {
            for j in 0..7 {
                if i != j {
                    assert_eq!(PolyOverZ::default(), matrix.get_entry(i, j).unwrap());
                } else {
                    assert_eq!(
                        PolyOverZ::from_str("1  1").unwrap(),
                        matrix.get_entry(i, j).unwrap()
                    )
                }
            }
        }

        let matrix = MatPolynomialRingZq::identity(7, 10, &modulus);

        for i in 0..7 {
            for j in 0..10 {
                if i != j {
                    assert_eq!(PolyOverZ::default(), matrix.get_entry(i, j).unwrap());
                } else {
                    assert_eq!(
                        PolyOverZ::from_str("1  1").unwrap(),
                        matrix.get_entry(i, j).unwrap()
                    )
                }
            }
        }
    }

    /// Tests if an identity matrix can be created using a large modulus.
    #[test]
    fn modulus_large() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 {} 1 mod {}", i64::MAX, u64::MAX))
                .unwrap();
        let matrix = MatPolynomialRingZq::identity(10, 10, &modulus);

        for i in 0..10 {
            for j in 0..10 {
                if i != j {
                    assert_eq!(PolyOverZ::default(), matrix.get_entry(i, j).unwrap());
                } else {
                    assert_eq!(
                        PolyOverZ::from_str("1  1").unwrap(),
                        matrix.get_entry(i, j).unwrap()
                    )
                }
            }
        }
    }

    /// Assert that a number of rows that is not suited to create a matrix is not allowed.
    #[should_panic]
    #[test]
    fn no_rows() {
        let modulus = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
        let _ = MatPolynomialRingZq::identity(0, 7, &modulus);
    }

    /// Assert that a number of columns that is not suited to create a matrix is not allowed.
    #[should_panic]
    #[test]
    fn no_columns() {
        let modulus = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
        let _ = MatPolynomialRingZq::identity(7, 0, &modulus);
    }
}
