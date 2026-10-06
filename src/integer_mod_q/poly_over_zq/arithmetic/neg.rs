// Copyright 2026 Jan Niklas Siemer
//
// This file is part of qFALL-math
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Neg`] trait for [`PolyOverZq`] values.

use super::super::PolyOverZq;
use flint3_sys::fmpz_mod_poly_neg;
use std::ops::Neg;

impl Neg for PolyOverZq {
    type Output = PolyOverZq;

    /// Implements the [`Neg`] trait for [`PolyOverZq`] values.
    /// [`Neg`] is implemented for both borrowed and owned [`PolyOverZq`].
    ///
    /// When called on owned [`PolyOverZq`] it will reuse the memory of `self`.
    ///
    /// Returns the additive inverse of `self` as a [`PolyOverZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverZq = PolyOverZq::from_str("3  1 2 42 mod 17").unwrap();
    ///
    /// let b: PolyOverZq = -&a;
    /// let c: PolyOverZq = -a;
    /// ```
    fn neg(mut self) -> Self::Output {
        unsafe {
            fmpz_mod_poly_neg(
                &mut self.poly,
                &self.poly,
                self.modulus.get_fmpz_mod_ctx_struct(),
            )
        };
        self
    }
}

impl Neg for &PolyOverZq {
    type Output = PolyOverZq;

    /// Documentation at [`PolyOverZq::neg`].
    fn neg(self) -> Self::Output {
        let mut out = PolyOverZq::from(&self.modulus);
        unsafe {
            fmpz_mod_poly_neg(
                &mut out.poly,
                &self.poly,
                self.modulus.get_fmpz_mod_ctx_struct(),
            )
        };
        out
    }
}

#[cfg(test)]
mod test_neg {
    use super::PolyOverZq;
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// Ensure that `neg` works for small coefficients.
    #[test]
    fn correct_small() {
        let a = PolyOverZq::from_str("4  1 -2 0 3 mod 17").unwrap();
        let b = PolyOverZq::from_str("4  -1 2 0 -3 mod 17").unwrap();
        let c = PolyOverZq::from_str("0 mod 17").unwrap();

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
        let a = PolyOverZq::from_str(&format!("3  {} 0 1 mod {}", i64::MAX, u64::MAX)).unwrap();
        let b = PolyOverZq::from_str(&format!("3  -{} 0 -1 mod {}", i64::MAX, u64::MAX)).unwrap();

        assert_eq!(a, -(-&a));
        assert_eq!(b, -&a);
        assert_eq!(b, -a);
    }

    /// Ensure that the result is reduced to the least non-negative residues
    /// and that the modulus is kept.
    #[test]
    fn reduced() {
        let a = PolyOverZq::from_str("4  1 16 0 8 mod 17").unwrap();
        let cmp = PolyOverZ::from_str("4  16 1 0 9").unwrap();

        let neg_a = -&a;

        assert_eq!(cmp, neg_a.get_representative_least_nonnegative_residue());
        assert_eq!(cmp, (-a).get_representative_least_nonnegative_residue());
        assert_eq!(17, neg_a.get_mod());
    }
}
