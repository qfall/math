// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of scalar multiplication for [`MatPolynomialRingZq`] matrices.

use super::super::MatPolynomialRingZq;
use crate::integer::Z;
use crate::integer_mod_q::PolynomialRingZq;
use crate::macros::arithmetics::{
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    arithmetic_trait_reverse,
};
use crate::macros::for_others::implement_for_others;
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpz_poly_mat::{fmpz_poly_mat_scalar_mul_fmpz, fmpz_poly_mat_scalar_mul_fmpz_poly};
use std::ops::Mul;

impl Mul<&Z> for &MatPolynomialRingZq {
    type Output = MatPolynomialRingZq;
    /// Implements multiplication for a [`MatPolynomialRingZq`] matrix with a [`Z`] integer.
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is multiplied
    ///
    /// Returns the product of `self` and `other` as a [`MatPolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use qfall_math::integer::{MatPolyOverZ, Z};
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat1 = MatPolyOverZ::from_str("[[3  0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
    /// let integer = Z::from(3);
    ///
    /// let poly_ring_mat2 = &poly_ring_mat1 * &integer;
    /// ```
    fn mul(self, scalar: &Z) -> Self::Output {
        let mut out =
            MatPolynomialRingZq::new(self.get_num_rows(), self.get_num_columns(), &self.modulus);
        unsafe {
            fmpz_poly_mat_scalar_mul_fmpz(
                &mut out.matrix.matrix,
                &self.matrix.matrix,
                &scalar.value,
            );
        }
        out.reduce();
        out
    }
}

arithmetic_trait_reverse!(Mul, mul, Z, MatPolynomialRingZq, MatPolynomialRingZq);

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatPolynomialRingZq, Z, MatPolynomialRingZq);
arithmetic_trait_borrowed_to_owned!(Mul, mul, Z, MatPolynomialRingZq, MatPolynomialRingZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatPolynomialRingZq, Z, MatPolynomialRingZq);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Z, MatPolynomialRingZq, MatPolynomialRingZq);

implement_for_others!(Z, MatPolynomialRingZq, Mul Scalar for i8 i16 i32 i64 u8 u16 u32 u64);

impl Mul<&PolynomialRingZq> for &MatPolynomialRingZq {
    type Output = MatPolynomialRingZq;
    /// Implements multiplication for a [`MatPolyOverZ`] matrix with a [`PolyOverZ`].
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is multiplied
    ///
    /// Returns the product of `self` and `other` as a [`MatPolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq, PolynomialRingZq};
    /// use qfall_math::integer::{MatPolyOverZ, PolyOverZ, Z};
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat1 = MatPolyOverZ::from_str("[[3  0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
    /// let poly = PolyOverZ::from_str("3  1 0 1").unwrap();
    /// let poly_ring = PolynomialRingZq::from((&poly, &modulus));
    ///
    /// let poly_ring_mat2 = &poly_ring_mat1 * &poly_ring;
    /// ```
    fn mul(self, scalar: &PolynomialRingZq) -> Self::Output {
        let mut out =
            MatPolynomialRingZq::new(self.get_num_rows(), self.get_num_columns(), &self.modulus);
        unsafe {
            fmpz_poly_mat_scalar_mul_fmpz_poly(
                &mut out.matrix.matrix,
                &self.matrix.matrix,
                &scalar.poly.poly,
            );
        }
        out.reduce();
        out
    }
}

arithmetic_trait_reverse!(
    Mul,
    mul,
    PolynomialRingZq,
    MatPolynomialRingZq,
    MatPolynomialRingZq
);

arithmetic_trait_borrowed_to_owned!(
    Mul,
    mul,
    MatPolynomialRingZq,
    PolynomialRingZq,
    MatPolynomialRingZq
);
arithmetic_trait_borrowed_to_owned!(
    Mul,
    mul,
    PolynomialRingZq,
    MatPolynomialRingZq,
    MatPolynomialRingZq
);
arithmetic_trait_mixed_borrowed_owned!(
    Mul,
    mul,
    MatPolynomialRingZq,
    PolynomialRingZq,
    MatPolynomialRingZq
);
arithmetic_trait_mixed_borrowed_owned!(
    Mul,
    mul,
    PolynomialRingZq,
    MatPolynomialRingZq,
    MatPolynomialRingZq
);

#[cfg(test)]
mod test_mul_z {
    use crate::integer::MatPolyOverZ;
    use crate::integer::Z;
    use crate::integer_mod_q::MatPolynomialRingZq;
    use crate::integer_mod_q::ModulusPolynomialRingZq;
    use std::str::FromStr;

    /// Checks whether scalar multiplication is available for other types.
    #[test]
    fn availability() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[3  0 1 1, 1  3],[0, 2  1 2]]").unwrap();
        let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
        let integer = Z::from(3);

        let _ = &poly_ring_mat * 3_u8;
        let _ = &poly_ring_mat * 3_u16;
        let _ = &poly_ring_mat * 3_u32;
        let _ = &poly_ring_mat * 3_u64;
        let _ = &poly_ring_mat * 3_i8;
        let _ = &poly_ring_mat * 3_i16;
        let _ = &poly_ring_mat * 3_i32;
        let _ = &poly_ring_mat * 3_i64;
        let _ = &poly_ring_mat * &integer;
        let _ = &poly_ring_mat * integer.clone();

        let _ = 3_u8 * &poly_ring_mat;
        let _ = 3_u16 * &poly_ring_mat;
        let _ = 3_u32 * &poly_ring_mat;
        let _ = 3_u64 * &poly_ring_mat;
        let _ = 3_i8 * &poly_ring_mat;
        let _ = 3_i16 * &poly_ring_mat;
        let _ = 3_i32 * &poly_ring_mat;
        let _ = 3_i64 * &poly_ring_mat;
        let _ = &integer * &poly_ring_mat;
        let _ = integer * &poly_ring_mat;

        let _ = poly_ring_mat.clone() * 3_u8;
        let _ = 3_u8 * poly_ring_mat;
    }

    /// Checks if scalar multiplication works.
    #[test]
    fn mul_correctness() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[3  0 1 1, 1  3],[0, 2  1 2]]").unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
        let integer = Z::from(3);

        let poly_ring_mat2 = &poly_ring_mat1 * &integer;

        let cmp_poly_mat = MatPolyOverZ::from_str("[[3  0 3 3, 1  9],[0, 2  3 6]]").unwrap();
        let cmp_poly_ring_mat = MatPolynomialRingZq::from((&cmp_poly_mat, &modulus));

        assert_eq!(cmp_poly_ring_mat, poly_ring_mat2);
    }

    /// Checks if scalar multiplication reduction works.
    #[test]
    fn reduction_correct() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[3  0 1 1, 1  10],[0, 2  1 2]]").unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
        let integer = Z::from(3);

        let poly_ring_mat2 = &poly_ring_mat1 * &integer;

        let cmp_poly_mat = MatPolyOverZ::from_str("[[3  0 3 3, 1  13],[0, 2  3 6]]").unwrap();
        let cmp_poly_ring_mat = MatPolynomialRingZq::from((&cmp_poly_mat, &modulus));

        assert_eq!(cmp_poly_ring_mat, poly_ring_mat2);
    }

    /// Checks if scalar multiplication works fine for matrices of different dimensions.
    #[test]
    fn different_dimensions_correctness() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[1  42],[0],[2  1 2]]").unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
        let poly_mat2 = MatPolyOverZ::from_str("[[1  2,1  6,1  5],[1  4,2  17 42,1  3]]").unwrap();
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus));

        let cmp_poly_mat1 = MatPolyOverZ::from_str("[[1  84],[0],[2  2 4]]").unwrap();
        let cmp_poly_ring_mat1 = MatPolynomialRingZq::from((&cmp_poly_mat1, &modulus));
        let cmp_poly_mat2 =
            MatPolyOverZ::from_str("[[1  4,1  12,1  10],[1  8,2  34 84,1  6]]").unwrap();
        let cmp_poly_ring_mat2 = MatPolynomialRingZq::from((&cmp_poly_mat2, &modulus));
        let integer = Z::from(2);

        assert_eq!(cmp_poly_ring_mat1, &poly_ring_mat1 * &integer);
        assert_eq!(cmp_poly_ring_mat2, &poly_ring_mat2 * &integer);
    }

    /// Checks if matrix multiplication works fine for large values.
    #[test]
    fn large_entries() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();
        let poly_mat1 =
            MatPolyOverZ::from_str(&format!("[[1  1],[1  {}],[1  4]]", i64::MAX)).unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
        let poly_mat2 = MatPolyOverZ::from_str("[[1  3]]").unwrap();
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus));
        let integer1 = Z::from(3);
        let integer2 = Z::from(i64::MAX);

        let cmp_poly_mat1 =
            MatPolyOverZ::from_str(&format!("[[1  3],[1  {}],[1  12]]", 3 * i64::MAX as i128))
                .unwrap();
        let cmp_poly_ring_mat1 = MatPolynomialRingZq::from((&cmp_poly_mat1, &modulus));
        let cmp_poly_mat2 =
            MatPolyOverZ::from_str(&format!("[[1  {}]]", 3 * i64::MAX as i128)).unwrap();
        let cmp_poly_ring_mat2 = MatPolynomialRingZq::from((&cmp_poly_mat2, &modulus));

        assert_eq!(cmp_poly_ring_mat1, &poly_ring_mat1 * &integer1);
        assert_eq!(cmp_poly_ring_mat2, &poly_ring_mat2 * &integer2);
    }
}

#[cfg(test)]
mod test_mul_poly_over_z {
    use crate::integer::MatPolyOverZ;
    use crate::integer::PolyOverZ;
    use crate::integer_mod_q::MatPolynomialRingZq;
    use crate::integer_mod_q::ModulusPolynomialRingZq;
    use crate::integer_mod_q::PolynomialRingZq;
    use std::str::FromStr;

    /// Checks whether scalar multiplication is available for other types.
    #[test]
    fn availability() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat = MatPolyOverZ::from_str("[[3  0 1 1, 1  3],[0, 2  1 2]]").unwrap();
        let poly_ring_mat = MatPolynomialRingZq::from((&poly_mat, &modulus));
        let poly = PolyOverZ::from_str("2  1 1").unwrap();
        let poly_ring = PolynomialRingZq::from((&poly, &modulus));

        let _ = &poly_ring_mat * &poly_ring;
        let _ = &poly_ring_mat * poly_ring.clone();
        let _ = poly_ring_mat.clone() * &poly_ring;
        let _ = poly_ring_mat.clone() * poly_ring.clone();

        let _ = &poly_ring * &poly_ring_mat;
        let _ = &poly_ring * poly_ring_mat.clone();
        let _ = poly_ring.clone() * &poly_ring_mat;
        let _ = poly_ring * poly_ring_mat;
    }

    /// Checks if scalar multiplication works.
    #[test]
    fn mul_correctness() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[2  1 1, 1  3],[0, 2  1 2]]").unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
        let poly = PolyOverZ::from_str("2  1 1").unwrap();
        let poly_ring = PolynomialRingZq::from((&poly, &modulus));

        let poly_ring_mat2 = &poly_ring_mat1 * &poly_ring;

        let cmp_poly_mat = MatPolyOverZ::from_str("[[3  1 2 1, 2  3 3],[0, 3  1 3 2]]").unwrap();
        let cmp_poly_ring_mat = MatPolynomialRingZq::from((&cmp_poly_mat, &modulus));

        assert_eq!(cmp_poly_ring_mat, poly_ring_mat2);
    }

    /// Checks if scalar multiplication reduction works.
    #[test]
    fn reduction_correct() {
        let modulus = ModulusPolynomialRingZq::from_str("4  2 0 0 2 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[0, 1  10],[0, 2  1 2]]").unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
        let poly = PolyOverZ::from(2);
        let poly_ring = PolynomialRingZq::from((&poly, &modulus));

        let poly_ring_mat2 = &poly_ring_mat1 * &poly_ring;

        let cmp_poly_mat = MatPolyOverZ::from_str("[[0, 1  3],[0, 2  2 4]]").unwrap();
        let cmp_poly_ring_mat = MatPolynomialRingZq::from((&cmp_poly_mat, &modulus));

        assert_eq!(cmp_poly_ring_mat, poly_ring_mat2);
    }

    /// Checks if scalar multiplication works fine for matrices of different dimensions.
    #[test]
    fn different_dimensions_correctness() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[1  42],[0],[2  1 2]]").unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
        let poly_mat2 = MatPolyOverZ::from_str("[[1  2,1  6,1  5],[1  4,2  17 42,1  3]]").unwrap();
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus));

        let cmp_poly_mat1 = MatPolyOverZ::from_str("[[1  84],[0],[2  2 4]]").unwrap();
        let cmp_poly_ring_mat1 = MatPolynomialRingZq::from((&cmp_poly_mat1, &modulus));
        let cmp_poly_mat2 =
            MatPolyOverZ::from_str("[[1  4,1  12,1  10],[1  8,2  34 84,1  6]]").unwrap();
        let cmp_poly_ring_mat2 = MatPolynomialRingZq::from((&cmp_poly_mat2, &modulus));
        let poly = PolyOverZ::from(2);
        let poly_ring = PolynomialRingZq::from((&poly, &modulus));

        assert_eq!(cmp_poly_ring_mat1, &poly_ring_mat1 * &poly_ring);
        assert_eq!(cmp_poly_ring_mat2, &poly_ring_mat2 * &poly_ring);
    }

    /// Checks if matrix multiplication works fine for large values.
    #[test]
    fn large_entries() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();
        let poly_mat1 =
            MatPolyOverZ::from_str(&format!("[[1  1],[1  {}],[1  4]]", i64::MAX)).unwrap();
        let poly_ring_mat1 = MatPolynomialRingZq::from((&poly_mat1, &modulus));
        let poly_mat2 = MatPolyOverZ::from_str("[[1  3]]").unwrap();
        let poly_ring_mat2 = MatPolynomialRingZq::from((&poly_mat2, &modulus));
        let poly1 = PolyOverZ::from(3);
        let poly_ring1 = PolynomialRingZq::from((&poly1, &modulus));
        let poly2 = PolyOverZ::from(i64::MAX);
        let poly_ring2 = PolynomialRingZq::from((&poly2, &modulus));

        let cmp_poly_mat1 =
            MatPolyOverZ::from_str(&format!("[[1  3],[1  {}],[1  12]]", 3 * i64::MAX as i128))
                .unwrap();
        let cmp_poly_ring_mat1 = MatPolynomialRingZq::from((&cmp_poly_mat1, &modulus));
        let cmp_poly_mat2 =
            MatPolyOverZ::from_str(&format!("[[1  {}]]", 3 * i64::MAX as i128)).unwrap();
        let cmp_poly_ring_mat2 = MatPolynomialRingZq::from((&cmp_poly_mat2, &modulus));

        assert_eq!(cmp_poly_ring_mat1, &poly_ring_mat1 * &poly_ring1);
        assert_eq!(cmp_poly_ring_mat2, &poly_ring_mat2 * &poly_ring2);
    }
}
