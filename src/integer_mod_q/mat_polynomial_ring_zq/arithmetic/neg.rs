// Copyright 2026 Jan Niklas Siemer
//
// This file is part of qFALL-math
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Neg`] trait for [`MatPolynomialRingZq`] values.

use super::super::MatPolynomialRingZq;
use flint3_sys::fmpz_poly_mat_neg;
use std::ops::Neg;

impl Neg for MatPolynomialRingZq {
    type Output = MatPolynomialRingZq;

    /// Implements the [`Neg`] trait for [`MatPolynomialRingZq`] values.
    /// [`Neg`] is implemented for both borrowed and owned [`MatPolynomialRingZq`].
    ///
    /// When called on owned [`MatPolynomialRingZq`] it will reuse the memory of `self`.
    ///
    /// Returns the additive inverse of `self` as a [`MatPolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq};
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly_mat = MatPolyOverZ::from_str("[[2  1 2, 0],[1  42, 3  1 2 3]]").unwrap();
    /// let a: MatPolynomialRingZq = MatPolynomialRingZq::from((&poly_mat, &modulus));
    ///
    /// let b: MatPolynomialRingZq = -&a;
    /// let c: MatPolynomialRingZq = -a;
    /// ```
    fn neg(mut self) -> Self::Output {
        unsafe { fmpz_poly_mat_neg(&mut self.matrix.matrix, &self.matrix.matrix) };
        self.reduce();
        self
    }
}

impl Neg for &MatPolynomialRingZq {
    type Output = MatPolynomialRingZq;

    /// Documentation at [`MatPolynomialRingZq::neg`].
    fn neg(self) -> Self::Output {
        let mut out = MatPolynomialRingZq {
            matrix: -&self.matrix,
            modulus: self.modulus.clone(),
        };
        out.reduce();
        out
    }
}

#[cfg(test)]
mod test_neg {
    use super::MatPolynomialRingZq;
    use crate::integer::MatPolyOverZ;
    use crate::integer_mod_q::ModulusPolynomialRingZq;
    use std::str::FromStr;

    /// Ensure that `neg` works for small coefficients.
    #[test]
    fn correct_small() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let mat_a = MatPolyOverZ::from_str("[[2  1 -2, 0],[1  -3, 3  1 0 4]]").unwrap();
        let mat_b = MatPolyOverZ::from_str("[[2  -1 2, 0],[1  3, 3  -1 0 -4]]").unwrap();
        let a = MatPolynomialRingZq::from((&mat_a, &modulus));
        let b = MatPolynomialRingZq::from((&mat_b, &modulus));
        let c = MatPolynomialRingZq::new(2, 2, &modulus);

        assert_eq!(a, -(-&a));
        assert_eq!(a, -&b);
        assert_eq!(b, -&a);
        assert_eq!(a, -b.clone());
        assert_eq!(b, -a);
        assert_eq!(c, -&c);
        assert_eq!(c.clone(), -c);
    }

    /// Ensure that `neg` works for large coefficients and moduli.
    #[test]
    fn correct_large() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();
        let mat_a = MatPolyOverZ::from_str(&format!("[[2  {} 1],[0]]", i64::MAX)).unwrap();
        let mat_b = MatPolyOverZ::from_str(&format!("[[2  -{} -1],[0]]", i64::MAX)).unwrap();
        let a = MatPolynomialRingZq::from((&mat_a, &modulus));
        let b = MatPolynomialRingZq::from((&mat_b, &modulus));

        assert_eq!(a, -(-&a));
        assert_eq!(b, -&a);
        assert_eq!(b, -a);
    }

    /// Ensure that the result is reduced to the least non-negative residues
    /// and that the modulus is kept.
    #[test]
    fn reduced() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let mat_a = MatPolyOverZ::from_str("[[2  1 16, 0],[1  8, 3  1 0 4]]").unwrap();
        let a = MatPolynomialRingZq::from((&mat_a, &modulus));
        let cmp = MatPolyOverZ::from_str("[[2  16 1, 0],[1  9, 3  16 0 13]]").unwrap();

        let neg_a = -&a;

        assert_eq!(cmp, neg_a.get_representative_least_nonnegative_residue());
        assert_eq!(cmp, (-a).get_representative_least_nonnegative_residue());
        assert_eq!(modulus, neg_a.get_mod());
    }
}
