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
use crate::integer::MatZ;
use crate::macros::arithmetics::{
    arithmetic_assign_trait_borrowed_to_owned, arithmetic_trait_borrowed_to_owned,
    arithmetic_trait_mixed_borrowed_owned, arithmetic_trait_reverse,
};
use crate::traits::{CompareBase, MatrixDimensions};
use flint_sys::fmpz_mat::fmpz_mat_add;
use flint_sys::fmpz_mod_mat::{_fmpz_mod_mat_reduce, fmpz_mod_mat_add};
use std::ops::{Add, AddAssign};

impl AddAssign<&MatZq> for MatZq {
    /// Computes the addition of `self` and `other` reusing
    /// the memory of `self`.
    /// [`AddAssign`] can be used on [`MatZq`] in combination with
    /// [`MatZq`] and [`MatZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer_mod_q::MatZq, integer::MatZ};
    /// let mut a = MatZq::identity(2, 2, 7);
    /// let b = MatZq::new(2, 2, 7);
    /// let c = MatZ::new(2, 2);
    ///
    /// a += &b;
    /// a += b;
    /// a += &c;
    /// a += c;
    /// ```
    ///
    /// # Panics ...
    /// - if the matrix dimensions mismatch.
    /// - if the moduli of the matrices mismatch.
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
        if !self.compare_base(other) {
            panic!("{}", self.call_compare_base_error(other).unwrap());
        }

        unsafe { fmpz_mod_mat_add(&mut self.matrix, &self.matrix, &other.matrix) };
    }
}
impl AddAssign<&MatZ> for MatZq {
    /// Documentation at [`MatZq::add_assign`].
    fn add_assign(&mut self, other: &MatZ) {
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

        unsafe {
            fmpz_mat_add(&mut self.matrix.mat[0], &self.matrix.mat[0], &other.matrix);
            _fmpz_mod_mat_reduce(&mut self.matrix);
        };
    }
}

arithmetic_assign_trait_borrowed_to_owned!(AddAssign, add_assign, MatZq, MatZq);
arithmetic_assign_trait_borrowed_to_owned!(AddAssign, add_assign, MatZq, MatZ);

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
    /// # Examples
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
    /// # Panics ...
    /// - if the dimensions of both matrices mismatch.
    /// - if the moduli mismatch.
    fn add(self, other: Self) -> Self::Output {
        self.add_safe(other).unwrap()
    }
}

impl Add<&MatZ> for &MatZq {
    type Output = MatZq;

    /// Implements the [`Add`] trait for a [`MatZ`] and a [`MatZq`] matrix.
    /// [`Add`] is implemented for any combination of [`MatZ`] and [`MatZq`] and vice versa.
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`MatZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer::MatZ, integer_mod_q::MatZq};
    /// use std::str::FromStr;
    ///
    /// let a = MatZ::from_str("[[1, 2, 3],[3, 4, 5]]").unwrap();
    /// let b = MatZq::from_str("[[1, 9, 3],[1, 0, 5]] mod 7").unwrap();
    ///
    /// let c = &a + &b;
    /// let d = a.clone() + b.clone();
    /// let e = &b + &a;
    /// let f = b + a;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of both matrices mismatch.
    fn add(self, other: &MatZ) -> Self::Output {
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

        let mut out = MatZq::new(self.get_num_rows(), self.get_num_columns(), self.get_mod());
        unsafe {
            fmpz_mat_add(&mut out.matrix.mat[0], &self.matrix.mat[0], &other.matrix);
            _fmpz_mod_mat_reduce(&mut out.matrix);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, MatZq, MatZ, MatZq);
arithmetic_trait_mixed_borrowed_owned!(Add, add, MatZq, MatZ, MatZq);
arithmetic_trait_reverse!(Add, add, MatZ, MatZq, MatZq);
arithmetic_trait_borrowed_to_owned!(Add, add, MatZ, MatZq, MatZq);
arithmetic_trait_mixed_borrowed_owned!(Add, add, MatZ, MatZq, MatZq);

impl MatZq {
    /// Implements addition for two [`MatZq`] matrices.
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both matrices as a [`MatZq`] or an
    /// error if the matrix dimensions mismatch.
    ///
    /// # Examples
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
    /// - Returns a [`MathError`] of type
    ///   [`MathError::MismatchingMatrixDimension`] if the matrix dimensions
    ///   mismatch.
    /// - Returns a [`MathError`] of type
    ///   [`MathError::MismatchingModulus`] if the moduli mismatch.
    pub fn add_safe(&self, other: &Self) -> Result<MatZq, MathError> {
        if !self.compare_base(other) {
            return Err(self.call_compare_base_error(other).unwrap());
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
        let mut out = MatZq::new(self.get_num_rows(), self.get_num_columns(), self.get_mod());
        unsafe {
            fmpz_mod_mat_add(&mut out.matrix, &self.matrix, &other.matrix);
        }
        Ok(out)
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, MatZq, MatZq, MatZq);
arithmetic_trait_mixed_borrowed_owned!(Add, add, MatZq, MatZq, MatZq);

#[cfg(test)]
mod test_add_assign {
    use crate::{integer::MatZ, integer_mod_q::MatZq};
    use std::str::FromStr;

    /// Ensure that `add_assign` works for small numbers.
    #[test]
    fn correct_small() {
        let mut a = MatZq::identity(2, 2, 7);
        let b = MatZq::from_str("[[4, 5],[-6, 6]] mod 7").unwrap();
        let mut c = a.clone();
        let d = b.get_representative_least_nonnegative_residue();
        let cmp = MatZq::from_str("[[5, 5],[1, 0]] mod 7").unwrap();

        a += b;
        c += d;

        assert_eq!(cmp, a);
        assert_eq!(cmp, c);
    }

    /// Ensure that `add_assign` works for large numbers.
    #[test]
    fn correct_large() {
        let mut a = MatZq::from_str(&format!(
            "[[{}, 5],[{}, -1]] mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        let b = MatZq::from_str(&format!("[[{}, -6],[6, -1]] mod {}", i64::MAX, u64::MAX)).unwrap();
        let cmp = MatZq::from_str(&format!(
            "[[{}, -1],[{}, -2]] mod {}",
            2 * (i64::MAX as u64),
            i64::MIN + 6,
            u64::MAX
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
            let mut a = MatZq::new(nr_rows, nr_cols, 7);
            let b = MatZq::identity(nr_rows, nr_cols, 7);

            a += b;

            assert_eq!(MatZq::identity(nr_rows, nr_cols, 7), a);
        }
    }

    /// Ensures that mismatching moduli will result in a panic.
    #[test]
    #[should_panic]
    fn mismatching_moduli() {
        let mut a = MatZq::new(1, 1, 5);
        let b = MatZq::new(1, 1, 6);

        a += b;
    }

    /// Ensure that `add_assign` is available for all types.
    #[test]
    fn availability() {
        let mut a = MatZq::new(2, 2, 7);
        let b = MatZq::new(2, 2, 7);
        let c = MatZ::new(2, 2);

        a += &b;
        a += b;
        a += &c;
        a += c;
    }
}

#[cfg(test)]
mod test_add {
    use super::MatZq;
    use std::str::FromStr;

    /// Testing addition for two [`MatZq`]
    #[test]
    fn add() {
        let a: MatZq = MatZq::from_str("[[1, 2, 3],[3, 4, 5]] mod 7").unwrap();
        let b: MatZq = MatZq::from_str("[[1, 2, 3],[3, -5, 5]] mod 7").unwrap();
        let c: MatZq = a + b;
        assert_eq!(c, MatZq::from_str("[[2, 4, 6],[6, 6, 3]] mod 7").unwrap());
    }

    /// Testing addition for two borrowed [`MatZq`]
    #[test]
    fn add_borrow() {
        let a: MatZq = MatZq::from_str("[[1, 2, 3],[3, 4, 5]] mod 7").unwrap();
        let b: MatZq = MatZq::from_str("[[1, 2, 3],[3, -5, 5]] mod 7").unwrap();
        let c: MatZq = &a + &b;
        assert_eq!(c, MatZq::from_str("[[2, 4, 6],[6, 6, 3]] mod 7").unwrap());
    }

    /// Testing addition for borrowed [`MatZq`] and [`MatZq`]
    #[test]
    fn add_first_borrowed() {
        let a: MatZq = MatZq::from_str("[[1, 2, 3],[3, 4, 5]] mod 7").unwrap();
        let b: MatZq = MatZq::from_str("[[1, 2, 3],[3, -5, 5]] mod 7").unwrap();
        let c: MatZq = &a + b;
        assert_eq!(c, MatZq::from_str("[[2, 4, 6],[6, 6, 3]] mod 7").unwrap());
    }

    /// Testing addition for [`MatZq`] and borrowed [`MatZq`]
    #[test]
    fn add_second_borrowed() {
        let a: MatZq = MatZq::from_str("[[1, 2, 3],[3, 4, 5]] mod 7").unwrap();
        let b: MatZq = MatZq::from_str("[[1, 2, 3],[3, -5, 5]] mod 7").unwrap();
        let c: MatZq = a + &b;
        assert_eq!(c, MatZq::from_str("[[2, 4, 6],[6, 6, 3]] mod 7").unwrap());
    }

    /// Testing addition for large numbers
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

    /// Testing add_safe
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

    /// Testing add_safe throws errors
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

#[cfg(test)]
mod test_add_matz {
    use super::MatZq;
    use crate::integer::MatZ;
    use std::str::FromStr;

    /// Ensures that addition between [`MatZ`] and [`MatZq`] works properly incl. reduction mod q.
    #[test]
    fn small_numbers() {
        let a = MatZ::from_str("[[1, 2],[3, 4]]").unwrap();
        let b = MatZq::from_str("[[5, 6],[9, 10]] mod 11").unwrap();
        let cmp = MatZq::from_str("[[6, 8],[1, 3]] mod 11").unwrap();

        let res_0 = &a + &b;
        let res_1 = &b + &a;

        assert_eq!(res_0, res_1);
        assert_eq!(cmp, res_0);
    }

    /// Testing addition for large numbers
    #[test]
    fn large_numbers() {
        let a: MatZ =
            MatZ::from_str(&format!("[[1, 2, {}],[3, -4, {}]]", i64::MIN, i128::MAX,)).unwrap();
        let b: MatZq = MatZq::from_str(&format!(
            "[[1, 2, {}],[3, 9, {}]] mod {}",
            i64::MIN + 1,
            i128::MAX,
            u64::MAX - 58
        ))
        .unwrap();

        let c = a + &b;

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

    /// Ensures that addition between [`MatZ`] and [`MatZq`] is available for any combination.
    #[test]
    fn available() {
        let a = MatZ::new(2, 2);
        let b = MatZq::new(2, 2, 7);

        let _ = &b + &a;
        let _ = &b + a.clone();
        let _ = b.clone() + &a;
        let _ = b.clone() + a.clone();
        let _ = &a + &b;
        let _ = &a + b.clone();
        let _ = a.clone() + &b;
    }

    /// Ensures that mismatching rows results in a panic.
    #[test]
    #[should_panic]
    fn mismatching_rows() {
        let a = MatZ::new(3, 2);
        let b = MatZq::new(2, 2, 7);

        let _ = &b + &a;
    }

    /// Ensures that mismatching columns results in a panic.
    #[test]
    #[should_panic]
    fn mismatching_column() {
        let a = MatZ::new(2, 3);
        let b = MatZq::new(2, 2, 7);

        let _ = &b + &a;
    }
}
