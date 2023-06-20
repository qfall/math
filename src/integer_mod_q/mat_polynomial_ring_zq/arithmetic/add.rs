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
    macros::arithmetics::{
        arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    },
};
use std::ops::Add;

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
    /// let poly_mat1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
    /// let poly_mat2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
    /// let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus));
    ///
    /// let poly_ring_mat3: MatPolynomialRingZq = &poly_ring_mat1 + &poly_ring_mat2;
    /// let poly_ring_mat4: MatPolynomialRingZq = poly_ring_mat1 + poly_ring_mat2;
    /// let poly_ring_mat5: MatPolynomialRingZq = &poly_ring_mat3 + poly_ring_mat4;
    /// let poly_ring_mat6: MatPolynomialRingZq = poly_ring_mat3 + &poly_ring_mat5;
    /// ```
    ///
    /// # Panics ...
    /// - ... if the moduli of both [`MatPolynomialRingZq`] mismatch.
    /// - ... if the dimensions of both [`MatPolynomialRingZq`] mismatch.
    fn add(self, other: Self) -> Self::Output {
        self.add_safe(other).unwrap()
    }
}

impl MatPolynomialRingZq {
    /// Implements addition for two [`MatPolynomialRingZq`] values.
    ///
    /// Parameters:
    /// - `other`: specifies the polynomial to add to `self`
    ///
    /// Returns the sum of both polynomials as a [`MatPolynomialRingZq`] or an error if the moduli
    /// mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatPolynomialRingZq;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
    /// let poly_mat2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
    /// let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus));
    ///
    /// let poly_ring_mat3: MatPolynomialRingZq = poly_ring_mat1.add_safe(&poly_ring_mat2).unwrap();
    /// ```
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`MathError::MismatchingModulus`] if the moduli of
    /// both [`MatPolynomialRingZq`] mismatch.
    /// - Returns a [`MathError`] of type [`MathError::MismatchingMatrixDimension`]
    /// if the dimensions of both [`MatPolynomialRingZq`] mismatch.
    pub fn add_safe(&self, other: &Self) -> Result<MatPolynomialRingZq, MathError> {
        if self.modulus != other.modulus {
            return Err(MathError::MismatchingModulus(format!(
                " Tried to add polynomial with modulus '{}' and polynomial with modulus '{}'.",
                self.modulus, other.modulus
            )));
        }
        let matrix = self.matrix.add_safe(&other.matrix)?;

        Ok(MatPolynomialRingZq::from((&matrix, &self.modulus)))
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
        let poly_mat1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
        let poly_mat2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus));
        let poly_mat_cmp = MatPolyOverZ::from_str("[[3  1 0 2, 1  16],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from((&poly_mat_cmp, &modulus));

        let poly_ring_mat3 = poly_ring_mat1 + poly_ring_mat2;

        assert_eq!(poly_ring_mat3, poly_ring_mat_cmp);
    }

    /// Testing addition for two borrowed [`MatPolynomialRingZq`]
    #[test]
    fn add_borrow() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
        let poly_mat2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus));
        let poly_mat_cmp = MatPolyOverZ::from_str("[[3  1 0 2, 1  16],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from((&poly_mat_cmp, &modulus));

        let poly_ring_mat3 = &poly_ring_mat1 + &poly_ring_mat2;

        assert_eq!(poly_ring_mat3, poly_ring_mat_cmp);
    }

    /// Testing addition for borrowed [`MatPolynomialRingZq`] and [`MatPolynomialRingZq`]
    #[test]
    fn add_first_borrowed() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
        let poly_mat2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus));
        let poly_mat_cmp = MatPolyOverZ::from_str("[[3  1 0 2, 1  16],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from((&poly_mat_cmp, &modulus));

        let poly_ring_mat3 = &poly_ring_mat1 + poly_ring_mat2;

        assert_eq!(poly_ring_mat3, poly_ring_mat_cmp);
    }

    /// Testing addition for [`MatPolynomialRingZq`] and borrowed [`MatPolynomialRingZq`]
    #[test]
    fn add_second_borrowed() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
        let poly_mat2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus));
        let poly_mat_cmp = MatPolyOverZ::from_str("[[3  1 0 2, 1  16],[0, 2  1 2]]").unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from((&poly_mat_cmp, &modulus));

        let poly_ring_mat3 = poly_ring_mat1 + &poly_ring_mat2;

        assert_eq!(poly_ring_mat3, poly_ring_mat_cmp);
    }

    /// Testing addition for [`MatPolynomialRingZq`] reduces `0` coefficients
    #[test]
    fn add_reduce() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[4  -1 0 1 1]]").unwrap();
        let a = MatPolynomialRingZq::from((&poly_mat1, &modulus));
        let poly_mat2 = MatPolyOverZ::from_str("[[4  2 0 3 -1]]").unwrap();
        let b = MatPolynomialRingZq::from((&poly_mat2, &modulus));
        let c = a + &b;
        assert_eq!(
            c,
            MatPolynomialRingZq::from((&MatPolyOverZ::from_str("[[3  1 0 4]]").unwrap(), &modulus))
        );
    }

    /// Testing addition for big [`MatPolynomialRingZq`]
    #[test]
    fn add_large_numbers() {
        let modulus = ModulusPolynomialRingZq::from_str(&format!(
            "5  1 1 0 0 {} mod {}",
            i64::MAX,
            LARGE_PRIME
        ))
        .unwrap();
        let poly_mat1 = MatPolyOverZ::from_str(&format!(
            "[[4  1 {} 1 1, 1  42],[0, 2  {} 2]]",
            i64::MAX,
            i64::MIN
        ))
        .unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
        let poly_mat2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus));
        let poly_mat_cmp = MatPolyOverZ::from_str(&format!(
            "[[4  4 {} 2 1, 1  84],[0, 2  {} 2]]",
            i64::MAX,
            i64::MIN + 17
        ))
        .unwrap();
        let poly_ring_mat_cmp = MatPolynomialRingZq::from((&poly_mat_cmp, &modulus));

        let poly_ring_mat3 = poly_ring_mat1 + poly_ring_mat2;

        assert_eq!(poly_ring_mat3, poly_ring_mat_cmp);
    }

    /// Testing addition for [`MatPolynomialRingZq`] with different moduli does not work
    #[test]
    #[should_panic]
    fn add_mismatching_modulus_modulus() {
        let modulus1 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 11").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus1));
        let modulus2 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus2));

        let _ = poly_ring_mat1 + poly_ring_mat2;
    }

    /// Testing addition for [`MatPolynomialRingZq`] with different moduli does not work
    #[test]
    #[should_panic]
    fn add_mismatching_modulus_polynomial() {
        let modulus1 = ModulusPolynomialRingZq::from_str("4  1 0 0 2 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus1));
        let modulus2 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus2));

        let _ = poly_ring_mat1 + poly_ring_mat2;
    }

    /// Testing addition for [`MatPolynomialRingZq`] with different dimensions does not work
    #[test]
    #[should_panic]
    fn add_mismatching_dim() {
        let modulus1 = ModulusPolynomialRingZq::from_str("4  1 0 0 2 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[1  42],[2  1 2]]").unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus1));
        let modulus2 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42]]").unwrap();
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus2));

        let _ = poly_ring_mat1 + poly_ring_mat2;
    }

    /// Testing whether add_safe throws an error for mismatching moduli
    #[test]
    fn add_safe_is_err_moduli() {
        let modulus1 = ModulusPolynomialRingZq::from_str("4  1 0 0 2 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[4  -1 0 1 1, 1  42],[0, 2  1 2]]").unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus1));
        let modulus2 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus2));

        assert!(&poly_ring_mat1.add_safe(&poly_ring_mat2).is_err());
    }

    /// Testing whether add_safe throws an error for different dimensions
    #[test]
    fn add_safe_is_err_dim() {
        let modulus1 = ModulusPolynomialRingZq::from_str("4  1 0 0 2 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[4  -1 0 1 1],[2  1 2]]").unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus1));
        let modulus2 = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat2 = MatPolyOverZ::from_str("[[3  3 0 1, 1  42],[0, 1  17]]").unwrap();
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus2));

        assert!(&poly_ring_mat1.add_safe(&poly_ring_mat2).is_err());
    }
}
