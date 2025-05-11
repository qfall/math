// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Add`] trait for [`MatQ`] values.

use super::super::MatQ;
use crate::error::MathError;
use crate::integer::MatZ;
use crate::macros::arithmetics::{
    arithmetic_assign_trait_borrowed_to_owned, arithmetic_trait_borrowed_to_owned,
    arithmetic_trait_mixed_borrowed_owned, arithmetic_trait_reverse,
};
use crate::traits::MatrixDimensions;
use flint_sys::fmpq_mat::fmpq_mat_add;
use std::ops::{Add, AddAssign};

impl AddAssign<&MatQ> for MatQ {
    /// Computes the addition of `self` and `other` reusing
    /// the memory of `self`.
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{rational::MatQ, integer::MatZ};
    /// let mut a = MatQ::identity(2, 2);
    /// let b = MatQ::new(2, 2);
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

        unsafe { fmpq_mat_add(&mut self.matrix, &self.matrix, &other.matrix) };
    }
}
impl AddAssign<&MatZ> for MatQ {
    /// Documentation at [`MatQ::add_assign`].
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

        let other = MatQ::from(other);
        unsafe {
            fmpq_mat_add(&mut self.matrix, &self.matrix, &other.matrix);
        }
    }
}

arithmetic_assign_trait_borrowed_to_owned!(AddAssign, add_assign, MatQ, MatQ);
arithmetic_assign_trait_borrowed_to_owned!(AddAssign, add_assign, MatQ, MatZ);

impl Add for &MatQ {
    type Output = MatQ;
    /// Implements the [`Add`] trait for two [`MatQ`] values.
    /// [`Add`] is implemented for any combination of [`MatQ`] and borrowed [`MatQ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`MatQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let a = MatQ::from_str("[[1/2, 2/3, 3/4],[3/4, 4/5, 5/7]]").unwrap();
    /// let b = MatQ::from_str("[[1/4, 9/7, 3/7],[1, 0, 5]]").unwrap();
    ///
    /// let d: MatQ = &a + &b;
    /// let e: MatQ = &a + b;
    /// let f: MatQ = d + &e;
    /// let g: MatQ = e + f;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of both matrices mismatch.
    fn add(self, other: Self) -> Self::Output {
        self.add_safe(other).unwrap()
    }
}

impl Add<&MatZ> for &MatQ {
    type Output = MatQ;

    /// Implements the [`Add`] trait for two [`MatQ`] values.
    /// [`Add`] is implemented for any combination of [`MatQ`] and [`MatZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`MatQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{rational::MatQ, integer::MatZ};
    /// use std::str::FromStr;
    ///
    /// let a = MatQ::from_str("[[1/2, 2/3, 3/4],[3/4, 4/5, 5/7]]").unwrap();
    /// let b = MatZ::identity(2, 3);
    ///
    /// let d: MatQ = &a + &b;
    /// let e: MatQ = a + &b;
    /// let f: MatQ = &b + d;
    /// let g: MatQ = b + f;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of both matrices mismatch.
    fn add(self, other: &MatZ) -> Self::Output {
        let other = MatQ::from(other);

        self.add_safe(&other).unwrap()
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, MatQ, MatZ, MatQ);
arithmetic_trait_mixed_borrowed_owned!(Add, add, MatQ, MatZ, MatQ);
arithmetic_trait_reverse!(Add, add, MatZ, MatQ, MatQ);
arithmetic_trait_borrowed_to_owned!(Add, add, MatZ, MatQ, MatQ);
arithmetic_trait_mixed_borrowed_owned!(Add, add, MatZ, MatQ, MatQ);

impl MatQ {
    /// Implements addition for two [`MatQ`] matrices.
    ///
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both matrices as a [`MatQ`] or an
    /// error if the matrix dimensions mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let a: MatQ = MatQ::from_str("[[1/2, 2/3, 3/4],[3/4, 4/5, 5/7]]").unwrap();
    /// let b: MatQ = MatQ::from_str("[[1/4, 9/7, 3/7],[1, 0, 5]]").unwrap();
    ///
    /// let c: MatQ = a.add_safe(&b).unwrap();
    /// ```
    /// # Errors
    /// - Returns a [`MathError`] of type
    ///   [`MathError::MismatchingMatrixDimension`] if the matrix dimensions
    ///   mismatch.
    pub fn add_safe(&self, other: &Self) -> Result<MatQ, MathError> {
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
        let mut out = MatQ::new(self.get_num_rows(), self.get_num_columns());
        unsafe {
            fmpq_mat_add(&mut out.matrix, &self.matrix, &other.matrix);
        }
        Ok(out)
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, MatQ, MatQ, MatQ);
arithmetic_trait_mixed_borrowed_owned!(Add, add, MatQ, MatQ, MatQ);

#[cfg(test)]
mod test_add_assign {
    use crate::{integer::MatZ, rational::MatQ};
    use std::str::FromStr;

    /// Ensure that `add_assign` works for small numbers.
    #[test]
    fn correct_small() {
        let mut a = MatQ::identity(2, 2);
        let b = MatQ::from_str("[[4/5, 5],[-6, -1]]").unwrap();
        let mut c = a.clone();
        let d = MatZ::from_str("[[4, 5],[-6, -1]]").unwrap();
        let cmp_0 = MatQ::from_str("[[9/5, 5],[-6, 0]]").unwrap();
        let cmp_1 = MatQ::from_str("[[5, 5],[-6, 0]]").unwrap();

        a += b;
        c += d;

        assert_eq!(cmp_0, a);
        assert_eq!(cmp_1, c);
    }

    /// Ensure that `add_assign` works for large numbers.
    #[test]
    fn correct_large() {
        let mut a = MatQ::from_str(&format!("[[{}/1, 5/2],[{}, -1]]", i64::MAX, i64::MIN)).unwrap();
        let b = MatQ::from_str(&format!("[[{}, -6/2],[6, -1]]", i64::MAX)).unwrap();
        let cmp = MatQ::from_str(&format!(
            "[[{}, -1/2],[{}, -2]]",
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
            let mut a = MatQ::new(nr_rows, nr_cols);
            let b = MatQ::identity(nr_rows, nr_cols);

            a += b;

            assert_eq!(MatQ::identity(nr_rows, nr_cols), a);
        }
    }

    /// Ensure that `add_assign` is available for all types.
    #[test]
    fn availability() {
        let mut a = MatQ::new(2, 2);
        let b = MatQ::new(2, 2);
        let c = MatZ::new(2, 2);

        a += &b;
        a += b;
        a += &c;
        a += c;
    }
}

#[cfg(test)]
mod test_add {
    use super::{MatQ, MatZ};
    use crate::rational::Q;
    use std::str::FromStr;

    /// Ensure that `add` works for small numbers between [`MatZ`] and [`MatQ`].
    #[test]
    fn correct_small() {
        let a = MatZ::identity(2, 2);
        let b = MatQ::from_str("[[4/5, 5],[-6, -1]]").unwrap();
        let c = a.clone();
        let d = MatQ::from_str("[[4, -5/-1],[-6, -1]]").unwrap();
        let cmp_0 = MatQ::from_str("[[9/5, 5],[-6, 0]]").unwrap();
        let cmp_1 = MatQ::from_str("[[5, 5],[-6, 0]]").unwrap();

        let res_0 = a + b;
        println!("{}", res_0);
        let res_1 = c + d;

        assert_eq!(cmp_0, res_0);
        assert_eq!(cmp_1, res_1);
    }

    /// Ensure that `add` works for large numbers between [`MatZ`] and [`MatQ`].
    #[test]
    fn correct_large() {
        let a = MatQ::from_str(&format!("[[{}/1, 5/2],[{}, -1]]", i64::MAX, i64::MIN)).unwrap();
        let b = MatZ::from_str(&format!("[[{}, -3],[6, -1]]", i64::MAX)).unwrap();
        let cmp = MatQ::from_str(&format!(
            "[[{}, -1/2],[{}, -2]]",
            2 * (i64::MAX as u64),
            i64::MIN + 6
        ))
        .unwrap();

        let c = a + b;

        assert_eq!(cmp, c);
    }

    /// Ensure that `add` works for different matrix dimensions between [`MatZ`] and [`MatQ`].
    #[test]
    fn matrix_dimensions() {
        let dimensions = [(3, 3), (5, 1), (1, 4)];

        for (nr_rows, nr_cols) in dimensions {
            let a = MatQ::new(nr_rows, nr_cols);
            let b = MatQ::identity(nr_rows, nr_cols);

            let c = a + b;

            assert_eq!(MatQ::identity(nr_rows, nr_cols), c);
        }
    }

    /// Testing addition for two [`MatQ`]
    #[test]
    fn add() {
        let a: MatQ = MatQ::from_str("[[1/2, 2, 3/2],[3/7, 4/7, 5/7]]").unwrap();
        let b: MatQ = MatQ::from_str("[[1/2, 2, 3/2],[3/7, -4/7, 5/7]]").unwrap();
        let c: MatQ = a + b;
        assert_eq!(c, MatQ::from_str("[[1, 4, 3],[6/7, 0, 10/7]]").unwrap());
    }

    /// Testing addition for two borrowed [`MatQ`]
    #[test]
    fn add_borrow() {
        let a: MatQ = MatQ::from_str("[[1/2, 2, 3/2],[3/7, 4/7, 5/7]]").unwrap();
        let b: MatQ = MatQ::from_str("[[1/2, 2, 3/2],[3/7, -4/7, 5/7]]").unwrap();
        let c: MatQ = &a + &b;
        assert_eq!(c, MatQ::from_str("[[1, 4, 3],[6/7, 0, 10/7]]").unwrap());
    }

    /// Testing addition for borrowed [`MatQ`] and [`MatQ`]
    #[test]
    fn add_first_borrowed() {
        let a: MatQ = MatQ::from_str("[[1/2, 2, 3/2],[3/7, 4/7, 5/7]]").unwrap();
        let b: MatQ = MatQ::from_str("[[1/2, 2, 3/2],[3/7, -4/7, 5/7]]").unwrap();
        let c: MatQ = &a + b;
        assert_eq!(c, MatQ::from_str("[[1, 4, 3],[6/7, 0, 10/7]]").unwrap());
    }

    /// Testing addition for [`MatQ`] and borrowed [`MatQ`]
    #[test]
    fn add_second_borrowed() {
        let a: MatQ = MatQ::from_str("[[1/2, 2, 3/2],[3/7, 4/7, 5/7]]").unwrap();
        let b: MatQ = MatQ::from_str("[[1/2, 2, 3/2],[3/7, -4/7, 5/7]]").unwrap();
        let c: MatQ = a + &b;
        assert_eq!(c, MatQ::from_str("[[1, 4, 3],[6/7, 0, 10/7]]").unwrap());
    }

    /// Testing addition for large numbers
    #[test]
    fn add_large_numbers() {
        let a: MatQ =
            MatQ::from_str(&format!("[[1, 2, {}],[3, -4, {}]]", i64::MIN, i64::MAX)).unwrap();
        let b: MatQ = MatQ::from_str(&format!(
            "[[1, 2, {}],[3, 9, 1/{}]]",
            i64::MIN + 1,
            i64::MAX
        ))
        .unwrap();
        let c: MatQ = a + &b;
        assert_eq!(
            c,
            MatQ::from_str(&format!(
                "[[2, 4, -{}],[6, 5, {}]]",
                u64::MAX,
                Q::from(i64::MAX) + Q::from((1, i64::MAX))
            ))
            .unwrap()
        );
    }

    /// Testing add_safe
    #[test]
    fn add_safe() {
        let a: MatQ = MatQ::from_str("[[1/9, 2/8, 3/4],[3, 4, 5]]").unwrap();
        let b: MatQ = MatQ::from_str("[[1/9, 2/8, 3/4],[3, -4, 5]]").unwrap();
        let c = a.add_safe(&b);
        assert_eq!(
            c.unwrap(),
            MatQ::from_str("[[2/9, 4/8, 6/4],[6, 0, 10]]").unwrap()
        );
    }

    /// Testing add_safe throws error
    #[test]
    fn add_safe_is_err() {
        let a: MatQ = MatQ::from_str("[[1, 2/7],[3/1912, 4]]").unwrap();
        let b: MatQ = MatQ::from_str("[[1, 5/2, 0],[3, -4/6, 7/5]]").unwrap();
        let c: MatQ = MatQ::from_str("[[1, -2/9, 3/7]]").unwrap();
        assert!(a.add_safe(&b).is_err());
        assert!(c.add_safe(&b).is_err());
    }

    /// Ensure that `add` is available for all types between [`MatZ`] and [`MatQ`].
    #[test]
    fn availability() {
        let a = MatQ::new(2, 2);
        let b = MatZ::new(2, 2);
        let c = MatQ::new(2, 2);

        let _ = &a + &b;
        let _ = &a + b.clone();
        let _ = a.clone() + &b;
        let _ = a.clone() + b.clone();
        let _ = &b + &a;
        let _ = &b + a.clone();
        let _ = b.clone() + &a;
        let _ = b.clone() + a.clone();

        let _ = &a + &c;
        let _ = &a + c.clone();
        let _ = a.clone() + &c;
        let _ = a.clone() + c.clone();
        let _ = &c + &a;
        let _ = &c + a.clone();
        let _ = c.clone() + &a;
        let _ = c.clone() + a.clone();
    }
}
