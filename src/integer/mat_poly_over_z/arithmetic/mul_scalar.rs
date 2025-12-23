// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of scalar multiplication for [`MatPolyOverZ`] matrices.

use super::super::MatPolyOverZ;
use crate::integer::{PolyOverZ, Z};
use crate::integer_mod_q::{MatPolynomialRingZq, PolynomialRingZq};
use crate::macros::arithmetics::{
    arithmetic_assign_between_types, arithmetic_assign_trait_borrowed_to_owned,
    arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    arithmetic_trait_reverse,
};
use crate::macros::for_others::implement_for_others;
use crate::traits::MatrixDimensions;
use flint_sys::fmpz_poly_mat::{fmpz_poly_mat_scalar_mul_fmpz, fmpz_poly_mat_scalar_mul_fmpz_poly};
use std::ops::{Mul, MulAssign};

impl Mul<&Z> for &MatPolyOverZ {
    type Output = MatPolyOverZ;
    /// Implements the [`Mul`] trait for a [`MatPolyOverZ`] matrix with a [`Z`] integer.
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is multiplied
    ///
    /// Returns the product of `self` and `scalar` as a [`MatPolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let mat_1 = MatPolyOverZ::from_str("[[2  1 42, 1  17],[1  8, 2  5 6]]").unwrap();
    /// let integer = Z::from(3);
    ///
    /// let mat_2 = &mat_1 * &integer;
    /// ```
    fn mul(self, scalar: &Z) -> Self::Output {
        let mut out = MatPolyOverZ::new(self.get_num_rows(), self.get_num_columns());
        unsafe {
            fmpz_poly_mat_scalar_mul_fmpz(&mut out.matrix, &self.matrix, &scalar.value);
        }
        out
    }
}

arithmetic_trait_reverse!(Mul, mul, Z, MatPolyOverZ, MatPolyOverZ);

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatPolyOverZ, Z, MatPolyOverZ);
arithmetic_trait_borrowed_to_owned!(Mul, mul, Z, MatPolyOverZ, MatPolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatPolyOverZ, Z, MatPolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, Z, MatPolyOverZ, MatPolyOverZ);

implement_for_others!(Z, MatPolyOverZ, MatPolyOverZ, Mul Scalar for i8 i16 i32 i64 u8 u16 u32 u64);

impl Mul<&PolyOverZ> for &MatPolyOverZ {
    type Output = MatPolyOverZ;
    /// Implements the [`Mul`] trait for a [`MatPolyOverZ`] matrix with a [`PolyOverZ`].
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `scalar`: specifies the scalar by which the matrix is multiplied
    ///
    /// Returns the product of `self` and `scalar` as a [`MatPolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let mat_1 = MatPolyOverZ::from_str("[[2  1 42, 1  17],[1  8, 2  5 6]]").unwrap();
    /// let poly = PolyOverZ::from_str("3  1 2 3").unwrap();
    ///
    /// let mat_2 = &mat_1 * &poly;
    /// ```
    fn mul(self, scalar: &PolyOverZ) -> Self::Output {
        let mut out = MatPolyOverZ::new(self.get_num_rows(), self.get_num_columns());
        unsafe {
            fmpz_poly_mat_scalar_mul_fmpz_poly(&mut out.matrix, &self.matrix, &scalar.poly);
        }
        out
    }
}

arithmetic_trait_reverse!(Mul, mul, PolyOverZ, MatPolyOverZ, MatPolyOverZ);

arithmetic_trait_borrowed_to_owned!(Mul, mul, MatPolyOverZ, PolyOverZ, MatPolyOverZ);
arithmetic_trait_borrowed_to_owned!(Mul, mul, PolyOverZ, MatPolyOverZ, MatPolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, MatPolyOverZ, PolyOverZ, MatPolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Mul, mul, PolyOverZ, MatPolyOverZ, MatPolyOverZ);

impl Mul<&PolynomialRingZq> for &MatPolyOverZ {
    type Output = MatPolynomialRingZq;
    /// Implements the [`Mul`] trait for a [`MatPolyOverZ`] matrix with a [`PolynomialRingZq`].
    /// [`Mul`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    /// - `scalar`: Specifies the scalar by which the matrix is multiplied.
    ///
    /// Returns the product of `self` and `scalar` as a [`MatPolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{ModulusPolynomialRingZq, PolynomialRingZq};
    /// use qfall_math::integer::{MatPolyOverZ, PolyOverZ};
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat1 = MatPolyOverZ::from_str("[[3  0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let poly = PolyOverZ::from_str("3  1 0 1").unwrap();
    /// let poly_ring = PolynomialRingZq::from((&poly, &modulus));
    ///
    /// let poly_ring_mat1 = &poly_mat1 * &poly_ring;
    /// ```
    fn mul(self, scalar: &PolynomialRingZq) -> Self::Output {
        let mut out =
            MatPolynomialRingZq::new(self.get_num_rows(), self.get_num_columns(), &scalar.modulus);
        out.matrix = self * &scalar.poly;
        out.reduce();

        out
    }
}

arithmetic_trait_reverse!(
    Mul,
    mul,
    PolynomialRingZq,
    MatPolyOverZ,
    MatPolynomialRingZq
);

arithmetic_trait_borrowed_to_owned!(
    Mul,
    mul,
    MatPolyOverZ,
    PolynomialRingZq,
    MatPolynomialRingZq
);
arithmetic_trait_borrowed_to_owned!(
    Mul,
    mul,
    PolynomialRingZq,
    MatPolyOverZ,
    MatPolynomialRingZq
);
arithmetic_trait_mixed_borrowed_owned!(
    Mul,
    mul,
    MatPolyOverZ,
    PolynomialRingZq,
    MatPolynomialRingZq
);
arithmetic_trait_mixed_borrowed_owned!(
    Mul,
    mul,
    PolynomialRingZq,
    MatPolyOverZ,
    MatPolynomialRingZq
);

impl MulAssign<&Z> for MatPolyOverZ {
    /// Computes the scalar multiplication of `self` and `scalar` reusing
    /// the memory of `self`.
    ///
    /// Parameters:
    /// - `scalar`: specifies the value to multiply to `self`
    ///
    /// Returns the scalar of the matrix as a [`MatPolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::{Z,PolyOverZ,MatPolyOverZ};
    /// use std::str::FromStr;
    ///
    /// let mut a = MatPolyOverZ::from_str("[[3  0 1 1, 1  42],[0, 2  1 2]]").unwrap();
    /// let b = Z::from(2);
    /// let c = PolyOverZ::from_str("2  1 -3").unwrap();
    ///
    /// a *= &b;
    /// a *= b;
    /// a *= &c;
    /// a *= c;
    /// a *= 2;
    /// a *= -2;
    /// ```
    fn mul_assign(&mut self, scalar: &Z) {
        unsafe { fmpz_poly_mat_scalar_mul_fmpz(&mut self.matrix, &self.matrix, &scalar.value) };
    }
}

impl MulAssign<&PolyOverZ> for MatPolyOverZ {
    /// Documentation at [`MatPolyOverZ::mul_assign`].
    fn mul_assign(&mut self, scalar: &PolyOverZ) {
        unsafe { fmpz_poly_mat_scalar_mul_fmpz_poly(&mut self.matrix, &self.matrix, &scalar.poly) };
    }
}

impl MulAssign<i64> for MatPolyOverZ {
    /// Documentation at [`MatPolyOverZ::mul_assign`].
    fn mul_assign(&mut self, scalar: i64) {
        let scalar = Z::from(scalar);
        unsafe { fmpz_poly_mat_scalar_mul_fmpz(&mut self.matrix, &self.matrix, &scalar.value) };
    }
}

impl MulAssign<u64> for MatPolyOverZ {
    /// Documentation at [`MatPolyOverZ::mul_assign`].
    fn mul_assign(&mut self, scalar: u64) {
        let scalar = Z::from(scalar);
        unsafe { fmpz_poly_mat_scalar_mul_fmpz(&mut self.matrix, &self.matrix, &scalar.value) };
    }
}

arithmetic_assign_trait_borrowed_to_owned!(MulAssign, mul_assign, MatPolyOverZ, Z);
arithmetic_assign_trait_borrowed_to_owned!(MulAssign, mul_assign, MatPolyOverZ, PolyOverZ);
arithmetic_assign_between_types!(MulAssign, mul_assign, MatPolyOverZ, i64, i32 i16 i8);
arithmetic_assign_between_types!(MulAssign, mul_assign, MatPolyOverZ, u64, u32 u16 u8);

#[cfg(test)]
mod test_mul_z {
    use crate::integer::MatPolyOverZ;
    use crate::integer::Z;
    use std::str::FromStr;

    /// Checks if scalar multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let mat_1 = MatPolyOverZ::from_str("[[2  1 42, 1  17],[1  8, 2  1 2]]").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = MatPolyOverZ::from_str("[[2  2 84, 1  34],[1  16, 2  2 4]]").unwrap();
        let integer = Z::from(2);

        let mat_1 = &mat_1 * &integer;
        let mat_2 = &integer * &mat_2;

        assert_eq!(mat_3, mat_1);
        assert_eq!(mat_3, mat_2);
    }

    /// Checks if scalar multiplication works fine for both owned
    #[test]
    fn owned_correctness() {
        let mat_1 = MatPolyOverZ::from_str("[[2  1 42, 1  17],[1  8, 2  1 2]]").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = MatPolyOverZ::from_str("[[2  2 84, 1  34],[1  16, 2  2 4]]").unwrap();
        let integer_1 = Z::from(2);
        let integer_2 = Z::from(2);

        let mat_1 = mat_1 * integer_1;
        let mat_2 = integer_2 * mat_2;

        assert_eq!(mat_3, mat_1);
        assert_eq!(mat_3, mat_2);
    }

    /// Checks if scalar multiplication works fine for half owned/borrowed
    #[test]
    fn half_correctness() {
        let mat_1 = MatPolyOverZ::from_str("[[2  1 42, 1  17],[1  8, 2  1 2]]").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = mat_1.clone();
        let mat_4 = mat_1.clone();
        let mat_5 = MatPolyOverZ::from_str("[[2  2 84, 1  34],[1  16, 2  2 4]]").unwrap();
        let integer_1 = Z::from(2);
        let integer_2 = Z::from(2);

        let mat_1 = mat_1 * &integer_1;
        let mat_2 = &integer_2 * mat_2;
        let mat_3 = &mat_3 * integer_1;
        let mat_4 = integer_2 * &mat_4;

        assert_eq!(mat_5, mat_1);
        assert_eq!(mat_5, mat_2);
        assert_eq!(mat_5, mat_3);
        assert_eq!(mat_5, mat_4);
    }

    /// Checks if scalar multiplication works fine for different scalar types
    #[test]
    #[allow(clippy::erasing_op)]
    fn different_types() {
        let mat_1 = MatPolyOverZ::from_str("[[1  42],[0],[2  1 2]]").unwrap();
        let mat_2 = MatPolyOverZ::from_str("[[1  2, 1  6, 1  5],[1  4, 2  17 42, 1  3]]").unwrap();
        let mat_3 = MatPolyOverZ::from_str("[[1  84],[0],[2  2 4]]").unwrap();
        let mat_4 = MatPolyOverZ::from_str("[[0],[0],[0]]").unwrap();
        let mat_5 = MatPolyOverZ::from_str("[[1  -42],[0],[2  -1 -2]]").unwrap();
        let mat_6 =
            MatPolyOverZ::from_str("[[1  4, 1  12, 1  10],[1  8, 2  34 84, 1  6]]").unwrap();

        assert_eq!(mat_3, 2 * &mat_1);
        assert_eq!(mat_4, 0 * &mat_1);
        assert_eq!(mat_5, -1 * mat_1);
        assert_eq!(mat_6, mat_2 * 2);
    }

    /// Checks if scalar multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat_1 = MatPolyOverZ::from_str("[[1  42],[0],[2  1 2]]").unwrap();
        let mat_2 = MatPolyOverZ::from_str("[[1  2, 1  6, 1  5],[1  4, 2  17 42, 1  3]]").unwrap();
        let mat_3 = MatPolyOverZ::from_str("[[1  84],[0],[2  2 4]]").unwrap();
        let mat_4 =
            MatPolyOverZ::from_str("[[1  4, 1  12, 1  10],[1  8, 2  34 84, 1  6]]").unwrap();
        let integer = Z::from(2);

        assert_eq!(mat_3, &integer * mat_1);
        assert_eq!(mat_4, integer * mat_2);
    }

    /// Checks if scalar multiplication works fine for large values
    #[test]
    fn large_entries() {
        let mat_1 = MatPolyOverZ::from_str(&format!("[[1  1],[1  {}],[1  4]]", i64::MAX)).unwrap();
        let mat_2 = MatPolyOverZ::from_str("[[1  3]]").unwrap();
        let mat_3 =
            MatPolyOverZ::from_str(&format!("[[1  3],[1  {}],[1  12]]", 3 * i64::MAX as i128))
                .unwrap();
        let mat_4 = MatPolyOverZ::from_str(&format!("[[1  {}]]", 3 * i64::MAX as i128)).unwrap();
        let integer_1 = Z::from(3);
        let integer_2 = Z::from(i64::MAX);

        assert_eq!(mat_3, integer_1 * mat_1);
        assert_eq!(mat_4, integer_2 * mat_2);
    }
}

#[cfg(test)]
mod test_mul_poly_over_z {
    use crate::integer::MatPolyOverZ;
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// Checks if scalar multiplication works fine for both borrowed
    #[test]
    fn borrowed_correctness() {
        let mat_1 = MatPolyOverZ::from_str("[[2  1 42, 1  17],[1  8, 2  1 2]]").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = MatPolyOverZ::from_str("[[2  2 84, 1  34],[1  16, 2  2 4]]").unwrap();
        let scalar = PolyOverZ::from(2);

        let mat_1 = &mat_1 * &scalar;
        let mat_2 = &scalar * &mat_2;

        assert_eq!(mat_3, mat_1);
        assert_eq!(mat_3, mat_2);
    }

    /// Checks if scalar multiplication works fine for both owned
    #[test]
    fn owned_correctness() {
        let mat_1 = MatPolyOverZ::from_str("[[2  1 42, 1  17],[1  8, 2  1 2]]").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = MatPolyOverZ::from_str("[[2  2 84, 1  34],[1  16, 2  2 4]]").unwrap();
        let scalar_1 = PolyOverZ::from(2);
        let scalar_2 = PolyOverZ::from(2);

        let mat_1 = mat_1 * scalar_1;
        let mat_2 = scalar_2 * mat_2;

        assert_eq!(mat_3, mat_1);
        assert_eq!(mat_3, mat_2);
    }

    /// Checks if scalar multiplication works fine for half owned/borrowed
    #[test]
    fn half_correctness() {
        let mat_1 = MatPolyOverZ::from_str("[[2  1 42, 1  17],[1  8, 2  1 2]]").unwrap();
        let mat_2 = mat_1.clone();
        let mat_3 = mat_1.clone();
        let mat_4 = mat_1.clone();
        let mat_5 = MatPolyOverZ::from_str("[[2  2 84, 1  34],[1  16, 2  2 4]]").unwrap();
        let scalar_1 = PolyOverZ::from(2);
        let scalar_2 = PolyOverZ::from(2);

        let mat_1 = mat_1 * &scalar_1;
        let mat_2 = &scalar_2 * mat_2;
        let mat_3 = &mat_3 * scalar_1;
        let mat_4 = scalar_2 * &mat_4;

        assert_eq!(mat_5, mat_1);
        assert_eq!(mat_5, mat_2);
        assert_eq!(mat_5, mat_3);
        assert_eq!(mat_5, mat_4);
    }

    /// Checks if scalar multiplication works fine for matrices of different dimensions
    #[test]
    fn different_dimensions_correctness() {
        let mat_1 = MatPolyOverZ::from_str("[[1  42],[0],[2  1 2]]").unwrap();
        let mat_2 = MatPolyOverZ::from_str("[[1  2, 1  6, 1  5],[1  4, 2  17 42, 1  3]]").unwrap();
        let mat_3 = MatPolyOverZ::from_str("[[1  84],[0],[2  2 4]]").unwrap();
        let mat_4 =
            MatPolyOverZ::from_str("[[1  4, 1  12, 1  10],[1  8, 2  34 84, 1  6]]").unwrap();
        let scalar = PolyOverZ::from(2);

        assert_eq!(mat_3, &scalar * mat_1);
        assert_eq!(mat_4, scalar * mat_2);
    }

    /// Checks if scalar multiplication works fine for large values
    #[test]
    fn large_entries() {
        let mat_1 = MatPolyOverZ::from_str(&format!("[[1  1],[1  {}],[1  4]]", i64::MAX)).unwrap();
        let mat_2 = MatPolyOverZ::from_str("[[1  3]]").unwrap();
        let mat_3 =
            MatPolyOverZ::from_str(&format!("[[1  3],[1  {}],[1  12]]", 3 * i64::MAX as i128))
                .unwrap();
        let mat_4 = MatPolyOverZ::from_str(&format!("[[1  {}]]", 3 * i64::MAX as i128)).unwrap();
        let scalar_1 = PolyOverZ::from(3);
        let scalar_2 = PolyOverZ::from(i64::MAX);

        assert_eq!(mat_3, scalar_1 * mat_1);
        assert_eq!(mat_4, scalar_2 * mat_2);
    }
}

#[cfg(test)]
mod test_mul_poly_ring_zq {
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
        let poly = PolyOverZ::from_str("2  1 1").unwrap();
        let poly_ring = PolynomialRingZq::from((&poly, &modulus));

        let _ = &poly_mat * &poly_ring;
        let _ = &poly_mat * poly_ring.clone();
        let _ = poly_mat.clone() * &poly_ring;
        let _ = poly_mat.clone() * poly_ring.clone();

        let _ = &poly_ring * &poly_mat;
        let _ = &poly_ring * poly_mat.clone();
        let _ = poly_ring.clone() * &poly_mat;
        let _ = poly_ring * poly_mat;
    }

    /// Checks if scalar multiplication works.
    #[test]
    fn mul_correctness() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[2  1 1, 1  3],[0, 2  1 2]]").unwrap();
        let poly = PolyOverZ::from_str("2  1 1").unwrap();
        let poly_ring = PolynomialRingZq::from((&poly, &modulus));

        let poly_ring_mat2 = &poly_mat1 * &poly_ring;

        let cmp_poly_mat = MatPolyOverZ::from_str("[[3  1 2 1, 2  3 3],[0, 3  1 3 2]]").unwrap();
        let cmp_poly_ring_mat = MatPolynomialRingZq::from((&cmp_poly_mat, &modulus));

        assert_eq!(cmp_poly_ring_mat, poly_ring_mat2);
    }

    /// Checks if scalar multiplication reduction works.
    #[test]
    fn reduction_correct() {
        let modulus = ModulusPolynomialRingZq::from_str("4  2 0 0 2 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[0, 1  10],[0, 2  1 2]]").unwrap();
        let poly = PolyOverZ::from(2);
        let poly_ring = PolynomialRingZq::from((&poly, &modulus));

        let poly_ring_mat2 = &poly_mat1 * &poly_ring;

        let cmp_poly_mat = MatPolyOverZ::from_str("[[0, 1  3],[0, 2  2 4]]").unwrap();
        let cmp_poly_ring_mat = MatPolynomialRingZq::from((&cmp_poly_mat, &modulus));

        assert_eq!(cmp_poly_ring_mat, poly_ring_mat2);
    }

    /// Checks if scalar multiplication works fine for matrices of different dimensions.
    #[test]
    fn different_dimensions_correctness() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let poly_mat1 = MatPolyOverZ::from_str("[[1  42],[0],[2  1 2]]").unwrap();
        let poly_mat2 = MatPolyOverZ::from_str("[[1  2,1  6,1  5],[1  4,2  17 42,1  3]]").unwrap();

        let cmp_poly_mat1 = MatPolyOverZ::from_str("[[1  84],[0],[2  2 4]]").unwrap();
        let cmp_poly_ring_mat1 = MatPolynomialRingZq::from((&cmp_poly_mat1, &modulus));
        let cmp_poly_mat2 =
            MatPolyOverZ::from_str("[[1  4,1  12,1  10],[1  8,2  34 84,1  6]]").unwrap();
        let cmp_poly_ring_mat2 = MatPolynomialRingZq::from((&cmp_poly_mat2, &modulus));
        let poly = PolyOverZ::from(2);
        let poly_ring = PolynomialRingZq::from((&poly, &modulus));

        assert_eq!(cmp_poly_ring_mat1, &poly_mat1 * &poly_ring);
        assert_eq!(cmp_poly_ring_mat2, &poly_mat2 * &poly_ring);
    }

    /// Checks if scalar multiplication works fine for large values.
    #[test]
    fn large_entries() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();
        let poly_mat1 =
            MatPolyOverZ::from_str(&format!("[[1  1],[1  {}],[1  4]]", i64::MAX)).unwrap();
        let poly_mat2 = MatPolyOverZ::from_str("[[1  3]]").unwrap();
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

        assert_eq!(cmp_poly_ring_mat1, &poly_mat1 * &poly_ring1);
        assert_eq!(cmp_poly_ring_mat2, &poly_mat2 * &poly_ring2);
    }
}

#[cfg(test)]
mod test_mul_assign {
    use crate::integer::{MatPolyOverZ, PolyOverZ, Z};
    use std::str::FromStr;

    /// Ensure that `mul_assign` produces same output as normal multiplication.
    #[test]
    fn consistency() {
        let mut a = MatPolyOverZ::from_str("[[2  2 1, 1  -2],[0, 2  2 -1]]").unwrap();
        let b = i32::MAX;
        let cmp = &a * b;

        a *= b;

        assert_eq!(cmp, a);
    }

    /// Ensure that `mul_assign` is available for all types.
    #[test]
    fn availability() {
        let mut a = MatPolyOverZ::from_str("[[2  2 1, 1  -3],[0, 2  3 1]]").unwrap();
        let b = Z::from(2);
        let c = PolyOverZ::from_str("2  3 1").unwrap();

        a *= &b;
        a *= b;
        a *= &c;
        a *= c;
        a *= 1_u8;
        a *= 1_u16;
        a *= 1_u32;
        a *= 1_u64;
        a *= 1_i8;
        a *= 1_i16;
        a *= 1_i32;
        a *= 1_i64;
    }
}
