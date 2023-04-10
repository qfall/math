// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Add`] trait for [`MatZq`] values.

use super::super::MatZq;
use crate::error::MathError;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
};
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpz_mod_mat::fmpz_mod_mat_add;
use std::ops::Add;

impl Add for &MatZq {
    type Output = MatZq;
    /// Implements the [`Add`] trait for two [`MatZq`] values.
    /// [`Add`] is implemented for any combination of [`MatZq`] and borrowed [`MatZq`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`MatZq`].
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let a: MatZq = MatZq::from_str("[[1, 2, 3],[3, 4, 5]] mod 7").unwrap();
    /// let b: MatZq = MatZq::from_str("[[1, 9, 3],[1, 0, 5]] mod 7").unwrap();
    ///
    /// let c: MatZq = &a + &b;
    /// let d: MatZq = a + b;
    /// let e: MatZq = &c + d;
    /// let f: MatZq = c + &e;
    /// ```
    ///
    /// # Errors and Failures
    /// - Panics if the dimensions of both matrices mismatch
    /// - Panics if the moduli mismatch
    fn add(self, other: Self) -> Self::Output {
        self.add_safe(other).unwrap()
    }
}

impl MatZq {
    /// Implements addition for two [`MatZq`] matrixes.
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both matrixes as a [`MatZq`] or an
    /// error if the matrix dimensions do mismatch.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let a: MatZq = MatZq::from_str("[[1, 2, 3],[3, 4, 5]] mod 7").unwrap();
    /// let b: MatZq = MatZq::from_str("[[1, 9, 3],[1, 0, 5]] mod 7").unwrap();
    ///
    /// let c: MatZq = a.add_safe(&b).unwrap();
    /// ```
    /// # Errors and Failures
    /// Returns a [`MathError`] of type
    /// [`MathError::MismatchingMatrixDimension`] if the matrix dimensions
    /// mismatch.
    /// Returns a [`MathError`] of type
    /// [`MathError::MismatchingModulus`] if the moduli mismatch.
    pub fn add_safe(&self, other: &Self) -> Result<MatZq, MathError> {
        if self.get_mod() != other.get_mod() {
            return Err(MathError::MismatchingModulus(format!(
                " Tried to add matrixes with moduli '{}' and '{}'.",
                self.get_mod(),
                other.get_mod()
            )));
        }
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
        let mut out =
            MatZq::new(self.get_num_rows(), self.get_num_columns(), self.get_mod()).unwrap();
        unsafe {
            fmpz_mod_mat_add(&mut out.matrix, &self.matrix, &other.matrix);
        }
        Ok(out)
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, MatZq, MatZq, MatZq);
arithmetic_trait_mixed_borrowed_owned!(Add, add, MatZq, MatZq, MatZq);

#[cfg(test)]
mod test_add {

    use super::MatZq;
    use std::str::FromStr;

    /// testing addition for two [`MatZq`]
    #[test]
    fn add() {
        let a: MatZq = MatZq::from_str("[[1, 2, 3],[3, 4, 5]] mod 7").unwrap();
        let b: MatZq = MatZq::from_str("[[1, 2, 3],[3, -5, 5]] mod 7").unwrap();
        let c: MatZq = a + b;
        assert_eq!(c, MatZq::from_str("[[2, 4, 6],[6, 6, 3]] mod 7").unwrap());
    }

    /// testing addition for two borrowed [`MatZq`]
    #[test]
    fn add_borrow() {
        let a: MatZq = MatZq::from_str("[[1, 2, 3],[3, 4, 5]] mod 7").unwrap();
        let b: MatZq = MatZq::from_str("[[1, 2, 3],[3, -5, 5]] mod 7").unwrap();
        let c: MatZq = &a + &b;
        assert_eq!(c, MatZq::from_str("[[2, 4, 6],[6, 6, 3]] mod 7").unwrap());
    }

    /// testing addition for borrowed [`MatZq`] and [`MatZq`]
    #[test]
    fn add_first_borrowed() {
        let a: MatZq = MatZq::from_str("[[1, 2, 3],[3, 4, 5]] mod 7").unwrap();
        let b: MatZq = MatZq::from_str("[[1, 2, 3],[3, -5, 5]] mod 7").unwrap();
        let c: MatZq = &a + b;
        assert_eq!(c, MatZq::from_str("[[2, 4, 6],[6, 6, 3]] mod 7").unwrap());
    }

    /// testing addition for [`MatZq`] and borrowed [`MatZq`]
    #[test]
    fn add_second_borrowed() {
        let a: MatZq = MatZq::from_str("[[1, 2, 3],[3, 4, 5]] mod 7").unwrap();
        let b: MatZq = MatZq::from_str("[[1, 2, 3],[3, -5, 5]] mod 7").unwrap();
        let c: MatZq = a + &b;
        assert_eq!(c, MatZq::from_str("[[2, 4, 6],[6, 6, 3]] mod 7").unwrap());
    }

    /// testing addition for big numbers
    #[test]
    fn add_large_numbers() {
        let a: MatZq = MatZq::from_str(&format!(
            "[[1, 2, {}],[3, -4, {}]] mod {}",
            i64::MIN,
            i128::MAX,
            u64::MAX - 58
        ))
        .unwrap();
        let b: MatZq = MatZq::from_str(&format!(
            "[[1, 2, {}],[3, 9, {}]] mod {}",
            i64::MIN + 1,
            i128::MAX,
            u64::MAX - 58
        ))
        .unwrap();
        let c: MatZq = a + &b;
        assert_eq!(
            c,
            MatZq::from_str(&format!(
                "[[2, 4, -{}],[6, 5, {}]] mod {}",
                u64::MAX,
                u128::MAX - 1,
                u64::MAX - 58
            ))
            .unwrap()
        );
    }

    /// testing add_safe
    #[test]
    fn add_safe() {
        let a: MatZq = MatZq::from_str("[[1, 2, 3],[3, 4, 5]] mod 4").unwrap();
        let b: MatZq = MatZq::from_str("[[1, 2, 3],[3, -5, 5]] mod 4").unwrap();
        let c = a.add_safe(&b);
        assert_eq!(
            c.unwrap(),
            MatZq::from_str("[[2, 0, 2],[2, 3, 2]] mod 4").unwrap()
        );
    }

    /// testing add_safe throws errors
    #[test]
    fn add_safe_is_err() {
        let a: MatZq = MatZq::from_str("[[1, 2],[3, 4]] mod 4").unwrap();
        let b: MatZq = MatZq::from_str("[[1, 2, 3],[3, -4, 5]] mod 4").unwrap();
        let c: MatZq = MatZq::from_str("[[1, 2, 3]] mod 4").unwrap();
        let d: MatZq = MatZq::from_str("[[1, 2],[3, 4]] mod 7").unwrap();
        assert!(a.add_safe(&b).is_err());
        assert!(c.add_safe(&b).is_err());
        assert!(a.add_safe(&d).is_err());
    }
}
