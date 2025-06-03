// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Add`] trait for [`MatPolynomialRingZq`] values.

use super::super::MatPolynomialRingZq;
use crate::{
    error::MathError,
    integer::MatPolyOverZ,
    macros::arithmetics::{
        arithmetic_assign_trait_borrowed_to_owned, arithmetic_trait_borrowed_to_owned,
        arithmetic_trait_mixed_borrowed_owned, arithmetic_trait_reverse,
    },
    traits::{CompareBase, MatrixDimensions},
};
use std::ops::{Add, AddAssign};

impl AddAssign<&MatPolynomialRingZq> for MatPolynomialRingZq {
    /// Computes the addition of `self` and `other` reusing
    /// the memory of `self`.
    /// [`AddAssign`] can be used on [`MatPolynomialRingZq`] in combination with
    /// [`MatPolynomialRingZq`] and [`MatPolyOverZ`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 7").unwrap();
    /// let mut a = MatPolynomialRingZq::identity(2, 2, &modulus);
    /// let b = MatPolynomialRingZq::new(2, 2, &modulus);
    /// let c = MatPolyOverZ::new(2, 2);
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
        if !self.compare_base(other) {
            panic!("{}", self.call_compare_base_error(other).unwrap());
        }

        self.matrix += &other.matrix;

        self.reduce();
    }
}
impl AddAssign<&MatPolyOverZ> for MatPolynomialRingZq {
    /// Documentation at [`MatPolynomialRingZq::add_assign`].
    fn add_assign(&mut self, other: &MatPolyOverZ) {
        self.matrix += other;

        self.reduce();
    }
}

arithmetic_assign_trait_borrowed_to_owned!(
    AddAssign,
    add_assign,
    MatPolynomialRingZq,
    MatPolynomialRingZq
);
arithmetic_assign_trait_borrowed_to_owned!(
    AddAssign,
    add_assign,
    MatPolynomialRingZq,
    MatPolyOverZ
);

impl Add for &MatPolynomialRingZq {
    type Output = MatPolynomialRingZq;
    /// Implements the [`Add`] trait for two [`MatPolynomialRingZq`] values.
    /// [`Add`] is implemented for any combination of [`MatPolynomialRingZq`] and borrowed [`MatPolynomialRingZq`].
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to add to `self`
    ///
    /// Returns the sum of both polynomials as a [`MatPolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
    /// let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
    /// let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));
    ///
    /// let poly_ring_mat_3: MatPolynomialRingZq = &poly_ring_mat_1 + &poly_ring_mat_2;
    /// let poly_ring_mat_4: MatPolynomialRingZq = poly_ring_mat_1 + poly_ring_mat_2;
    /// let poly_ring_mat_5: MatPolynomialRingZq = &poly_ring_mat_3 + poly_ring_mat_4;
    /// let poly_ring_mat_6: MatPolynomialRingZq = poly_ring_mat_3 + &poly_ring_mat_5;
    /// ```
    ///
    /// # Panics ...
    /// - if the moduli of both [`MatPolynomialRingZq`] mismatch.
    /// - if the dimensions of both [`MatPolynomialRingZq`] mismatch.
    fn add(self, other: Self) -> Self::Output {
        self.add_safe(other).unwrap()
    }
}

arithmetic_trait_borrowed_to_owned!(
    Add,
    add,
    MatPolynomialRingZq,
    MatPolynomialRingZq,
    MatPolynomialRingZq
);
arithmetic_trait_mixed_borrowed_owned!(
    Add,
    add,
    MatPolynomialRingZq,
    MatPolynomialRingZq,
    MatPolynomialRingZq
);

impl Add<&MatPolyOverZ> for &MatPolynomialRingZq {
    type Output = MatPolynomialRingZq;
    /// Implements the [`Add`] trait for a [`MatPolynomialRingZq`] matrix with a [`MatPolyOverZ`] matrix.
    /// [`Add`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `other`: specifies the value to add with `self`
    ///
    /// Returns the addition of `self` and `other` as a [`MatPolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let mat_1 = MatPolynomialRingZq::from_str("[[2  1 42, 1  17],[1  8, 2  5 6]] / 3  1 2 3 mod 17").unwrap();
    /// let mat_2 = MatPolyOverZ::from_str("[[2  1 42, 1  17],[1  8, 2  5 6]]").unwrap();
    ///
    /// let mat_3 = &mat_1 + &mat_2;
    /// ```
    ///
    /// # Panics ...
    /// - if the dimensions of `self` and `other` do not match for multiplication.
    fn add(self, other: &MatPolyOverZ) -> Self::Output {
        self.add_mat_poly_over_z_safe(other).unwrap()
    }
}

arithmetic_trait_reverse!(
    Add,
    add,
    MatPolyOverZ,
    MatPolynomialRingZq,
    MatPolynomialRingZq
);

arithmetic_trait_borrowed_to_owned!(
    Add,
    add,
    MatPolynomialRingZq,
    MatPolyOverZ,
    MatPolynomialRingZq
);
arithmetic_trait_borrowed_to_owned!(
    Add,
    add,
    MatPolyOverZ,
    MatPolynomialRingZq,
    MatPolynomialRingZq
);
arithmetic_trait_mixed_borrowed_owned!(
    Add,
    add,
    MatPolynomialRingZq,
    MatPolyOverZ,
    MatPolynomialRingZq
);
arithmetic_trait_mixed_borrowed_owned!(
    Add,
    add,
    MatPolyOverZ,
    MatPolynomialRingZq,
    MatPolynomialRingZq
);

impl MatPolynomialRingZq {
    /// Implements addition for two [`MatPolynomialRingZq`] values.
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to add to `self`
    ///
    /// Returns the sum of both polynomials as a [`MatPolynomialRingZq`] or an error if the moduli
    /// mismatch, or the dimensions of the matrices mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
    /// let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
    /// let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));
    ///
    /// let poly_ring_mat_3: MatPolynomialRingZq = poly_ring_mat_1.add_safe(&poly_ring_mat_2).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::MismatchingModulus`] if the moduli of
    ///   both [`MatPolynomialRingZq`] mismatch.
    /// - Returns a [`MathError`] of type [`MathError::MismatchingMatrixDimension`]
    ///   if the dimensions of both [`MatPolynomialRingZq`] mismatch.
    pub fn add_safe(&self, other: &Self) -> Result<MatPolynomialRingZq, MathError> {
        if !self.compare_base(other) {
            return Err(self.call_compare_base_error(other).unwrap());
        }
        let matrix = self.matrix.add_safe(&other.matrix)?;

        Ok(MatPolynomialRingZq::from((&matrix, &self.modulus)))
    }

    /// Implements addition for a [`MatPolynomialRingZq`] matrix with a [`MatPolyOverZ`] matrix.
    ///
    /// Parameters:
    /// - `other`: specifies the value to add with `self`
    ///
    /// Returns the addition of `self` and `other` as a [`MatPolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let mat_1 = MatPolynomialRingZq::from_str("[[2  1 42, 1  17],[1  8, 2  5 6]] / 3  1 2 3 mod 17").unwrap();
    /// let mat_2 = MatPolyOverZ::from_str("[[2  1 42, 1  17],[1  8, 2  5 6]]").unwrap();
    ///
    /// let mat_3 = &mat_1.add_mat_poly_over_z_safe(&mat_2).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///   [`MathError::MismatchingMatrixDimension`] if the dimensions of `self`
    ///   and `other` do not match for multiplication.
    pub fn add_mat_poly_over_z_safe(&self, other: &MatPolyOverZ) -> Result<Self, MathError> {
        let mut out =
            MatPolynomialRingZq::new(self.get_num_rows(), self.get_num_columns(), self.get_mod());

        out.matrix = self.matrix.add_safe(other)?;
        out.reduce();

        Ok(out)
    }
}

#[cfg(test)]
mod test_add_assign {
    use crate::{
        integer::MatPolyOverZ,
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
    };
    use std::str::FromStr;

    /// Ensure that `add_assign` works for small numbers.
    #[test]
    fn correct_small() {
        let mut a = MatPolynomialRingZq::from_str("[[1  1, 0],[0, 1  1]] / 2  0 1 mod 7").unwrap();
        let b =
            MatPolynomialRingZq::from_str("[[1  4, 1  5],[1  -6, 2  6 1]] / 2  0 1 mod 7").unwrap();
        let cmp = MatPolynomialRingZq::from_str("[[1  5, 1  5],[1  1, 0]] / 2  0 1 mod 7").unwrap();

        a += b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `add_assign` works for large numbers.
    #[test]
    fn correct_large() {
        let mut a = MatPolynomialRingZq::from_str(&format!(
            "[[1  {}, 1  5],[1  {}, 1  -1]] / 2  0 1 mod {}",
            i64::MAX,
            i64::MIN,
            u64::MAX
        ))
        .unwrap();
        let b = MatPolynomialRingZq::from_str(&format!(
            "[[1  {}, 1  -6],[1  6, 1  -1]] / 2  0 1 mod {}",
            i64::MAX,
            u64::MAX
        ))
        .unwrap();
        let cmp = MatPolynomialRingZq::from_str(&format!(
            "[[1  {}, 1  -1],[1  {}, 1  -2]] / 2  0 1 mod {}",
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
        let modulus = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 7").unwrap();
        let dimensions = [(3, 3), (5, 1), (1, 4)];

        for (nr_rows, nr_cols) in dimensions {
            let mut a = MatPolynomialRingZq::new(nr_rows, nr_cols, &modulus);
            let b = MatPolynomialRingZq::identity(nr_rows, nr_cols, &modulus);

            a += b;

            assert_eq!(MatPolynomialRingZq::identity(nr_rows, nr_cols, &modulus), a);
        }
    }

    /// Ensure that mismatching dimensions will result in a panic.
    #[test]
    #[should_panic]
    fn mismatching_dimensions() {
        let modulus = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 7").unwrap();
        let mut a = MatPolynomialRingZq::new(2, 1, &modulus);
        let b = MatPolynomialRingZq::new(1, 1, &modulus);

        a += b;
    }

    /// Ensures that mismatching moduli will result in a panic.
    #[test]
    #[should_panic]
    fn mismatching_moduli() {
        let modulus_0 = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 7").unwrap();
        let modulus_1 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 7").unwrap();
        let mut a = MatPolynomialRingZq::new(1, 1, &modulus_0);
        let b = MatPolynomialRingZq::new(1, 1, &modulus_1);

        a += b;
    }

    /// Ensure that `add_assign` is available for all types.
    #[test]
    fn availability() {
        let modulus = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 7").unwrap();
        let mut a = MatPolynomialRingZq::new(2, 2, &modulus);
        let b = MatPolynomialRingZq::new(2, 2, &modulus);
        let c = MatPolyOverZ::new(2, 2);

        a += &b;
        a += b;
        a += &c;
        a += c;
    }
}

#[cfg(test)]
mod test_add {
    use crate::integer::MatPolyOverZ;
    use crate::integer_mod_q::MatPolynomialRingZq;
    use crate::integer_mod_q::ModulusPolynomialRingZq;
    use std::str::FromStr;

    const LARGE_PRIME: u64 = 18446744073709551557;

    /// Testing addition for two [`MatPolynomialRingZq`]
    #[test]
    fn add() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));
        let poly_mat_cmp = MatPolyOverZ::from_str("[[3  1 0 2, 1  16],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from((&poly_mat_cmp, &modulus));

        let poly_ring_mat_3 = poly_ring_mat_1 + poly_ring_mat_2;

        assert_eq!(poly_ring_mat_3, poly_ring_mat_cmp);
    }

    /// Testing addition for two borrowed [`MatPolynomialRingZq`]
    #[test]
    fn add_borrow() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));
        let poly_mat_cmp = MatPolyOverZ::from_str("[[3  1 0 2, 1  16],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from((&poly_mat_cmp, &modulus));

        let poly_ring_mat_3 = &poly_ring_mat_1 + &poly_ring_mat_2;

        assert_eq!(poly_ring_mat_3, poly_ring_mat_cmp);
    }

    /// Testing addition for borrowed [`MatPolynomialRingZq`] and [`MatPolynomialRingZq`]
    #[test]
    fn add_first_borrowed() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));
        let poly_mat_cmp = MatPolyOverZ::from_str("[[3  1 0 2, 1  16],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from((&poly_mat_cmp, &modulus));

        let poly_ring_mat_3 = &poly_ring_mat_1 + poly_ring_mat_2;

        assert_eq!(poly_ring_mat_3, poly_ring_mat_cmp);
    }

    /// Testing addition for [`MatPolynomialRingZq`] and borrowed [`MatPolynomialRingZq`]
    #[test]
    fn add_second_borrowed() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));
        let poly_mat_cmp = MatPolyOverZ::from_str("[[3  1 0 2, 1  16],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from((&poly_mat_cmp, &modulus));

        let poly_ring_mat_3 = poly_ring_mat_1 + &poly_ring_mat_2;

        assert_eq!(poly_ring_mat_3, poly_ring_mat_cmp);
    }

    /// Testing addition for [`MatPolynomialRingZq`] reduces `0` coefficients
    #[test]
    fn add_reduce() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1]]").unwrap();
        let a = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_mat_2 = MatPolyOverZ::from_str("[[4  2 0 3 -1]]").unwrap();
        let b = MatPolynomialRingZq::from((&poly_mat_2, &modulus));
        let c = a + &b;
        assert_eq!(
            c,
            MatPolynomialRingZq::from((&MatPolyOverZ::from_str("[[3  1 0 4]]").unwrap(), &modulus))
        );
    }

    /// Testing addition for large [`MatPolynomialRingZq`]
    #[test]
    fn add_large_numbers() {
        let modulus = ModulusPolynomialRingZq::from_str(&format!(
            "5  1 1 0 0 {} mod {LARGE_PRIME}",
            i64::MAX
        ))
        .unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str(&format!(
            "[[4  1 {} 1 1, 1  42],[0, 2  {} 2]]",
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus));
        let poly_mat_cmp = MatPolyOverZ::from_str(&format!(
            "[[4  4 {} 2 1, 1  84],[0, 2  {} 2]]",
            i64::MAX,
            i64::MIN + 17
        ))
        .unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from((&poly_mat_cmp, &modulus));

        let poly_ring_mat_3 = poly_ring_mat_1 + poly_ring_mat_2;

        assert_eq!(poly_ring_mat_3, poly_ring_mat_cmp);
    }

    /// Testing addition for [`MatPolynomialRingZq`] with different moduli does not work
    #[test]
    #[should_panic]
    fn add_mismatching_modulus_modulus() {
        let modulus_1 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 11").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus_1));
        let modulus_2 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus_2));

        let _ = poly_ring_mat_1 + poly_ring_mat_2;
    }

    /// Testing addition for [`MatPolynomialRingZq`] with different moduli does not work
    #[test]
    #[should_panic]
    fn add_mismatching_modulus_polynomial() {
        let modulus_1 = ModulusPolynomialRingZq::from_str("4  1 0 0 2 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus_1));
        let modulus_2 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus_2));

        let _ = poly_ring_mat_1 + poly_ring_mat_2;
    }

    /// Testing addition for [`MatPolynomialRingZq`] with different dimensions does not work
    #[test]
    #[should_panic]
    fn add_mismatching_dim() {
        let modulus_1 = ModulusPolynomialRingZq::from_str("4  1 0 0 2 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[1  42],[2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus_1));
        let modulus_2 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42]]").unwrap();
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus_2));

        let _ = poly_ring_mat_1 + poly_ring_mat_2;
    }

    /// Testing whether add_safe throws an error for mismatching moduli
    #[test]
    fn add_safe_is_err_moduli() {
        let modulus_1 = ModulusPolynomialRingZq::from_str("4  1 0 0 2 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus_1));
        let modulus_2 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus_2));

        assert!(&poly_ring_mat_1.add_safe(&poly_ring_mat_2).is_err());
    }

    /// Testing whether add_safe throws an error for different dimensions
    #[test]
    fn add_safe_is_err_dim() {
        let modulus_1 = ModulusPolynomialRingZq::from_str("4  1 0 0 2 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1],[2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus_1));
        let modulus_2 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat_2 = MatPolynomialRingZq::from((&poly_mat_2, &modulus_2));

        assert!(&poly_ring_mat_1.add_safe(&poly_ring_mat_2).is_err());
    }
}

#[cfg(test)]
mod test_mul_mat_poly_over_z {
    use super::MatPolynomialRingZq;
    use crate::{integer::MatPolyOverZ, integer_mod_q::ModulusPolynomialRingZq};
    use std::str::FromStr;

    const LARGE_PRIME: u64 = u64::MAX - 58;

    /// Checks whether addition is available for other types.
    #[test]
    fn availability() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[3  0 1 1, 1  3],[0, 2  1 2]]").unwrap();
        let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));

        let _ = &poly_mat + &poly_ring_mat;
        let _ = &poly_mat + poly_ring_mat.clone();
        let _ = poly_mat.clone() + &poly_ring_mat;
        let _ = poly_mat.clone() + poly_ring_mat.clone();

        let _ = &poly_ring_mat + &poly_mat;
        let _ = &poly_ring_mat + poly_mat.clone();
        let _ = poly_ring_mat.clone() + &poly_mat;
        let _ = poly_ring_mat + poly_mat;
    }

    /// Checks if addition works fine for squared matrices.
    #[test]
    fn square_correctness() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[2  1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_mat_2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();

        let poly_ring_mat_3 = &poly_ring_mat_1 + &poly_mat_2;

        let poly_mat_cmp = MatPolyOverZ::from_str("[[3  4 1 1, 1  84],[0, 2  18 2]]").unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from((&poly_mat_cmp, &modulus));

        assert_eq!(poly_ring_mat_cmp, poly_ring_mat_3);
    }

    /// Checks if addition works fine for large entries.
    #[test]
    fn large_entries() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {LARGE_PRIME}")).unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str(&format!("[[2  3 {}],[1  1]]", u64::MAX)).unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus));
        let poly_mat_2 = MatPolyOverZ::from_str(&format!("[[2  1 {}],[0]]", u64::MAX)).unwrap();

        let poly_ring_mat_3 = &poly_ring_mat_1 + &poly_mat_2;

        let poly_mat_cmp =
            MatPolyOverZ::from_str(&format!("[[2  4 {}],[1  1]]", u128::from(u64::MAX) * 2))
                .unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from((&poly_mat_cmp, &modulus));

        assert_eq!(poly_ring_mat_cmp, poly_ring_mat_3);
    }

    /// Checks if addition with incompatible matrix dimensions
    /// throws an error as expected.
    #[test]
    fn errors() {
        let modulus_1 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[4  -1 0 1 1],[2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus_1));
        let poly_mat_2 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  1],[2  1 2, 1  1]]").unwrap();

        assert!((poly_ring_mat_1.add_mat_poly_over_z_safe(&poly_mat_2)).is_err());
    }

    /// Checks if addition panics if dimensions mismatch.
    #[test]
    #[should_panic]
    fn mul_panic() {
        let modulus_1 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat_1 = MatPolyOverZ::from_str("[[1  3],[2  1 2]]").unwrap();
        let poly_ring_mat_1 = MatPolynomialRingZq::from((&poly_mat_1, &modulus_1));
        let poly_mat_2 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  1],[2  1 2, 1  1]]").unwrap();

        let _ = &poly_ring_mat_1 + &poly_mat_2;
    }
}
