// Copyright 2026 Jan Niklas Siemer
//
// This file is part of qFALL-math
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Neg`] trait for [`PolynomialRingZq`] values.

use super::super::PolynomialRingZq;
use flint3_sys::fmpz_poly_neg;
use std::ops::Neg;

impl Neg for PolynomialRingZq {
    type Output = PolynomialRingZq;

    /// Implements the [`Neg`] trait for [`PolynomialRingZq`] values.
    /// [`Neg`] is implemented for both borrowed and owned [`PolynomialRingZq`].
    ///
    /// When called on owned [`PolynomialRingZq`] it will reuse the memory of `self`.
    ///
    /// Returns the additive inverse of `self` as a [`PolynomialRingZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::{ModulusPolynomialRingZq, PolynomialRingZq};
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly = PolyOverZ::from_str("3  1 2 42").unwrap();
    /// let a: PolynomialRingZq = PolynomialRingZq::from((&poly, &modulus));
    ///
    /// let b: PolynomialRingZq = -&a;
    /// let c: PolynomialRingZq = -a;
    /// ```
    fn neg(mut self) -> Self::Output {
        unsafe { fmpz_poly_neg(&mut self.poly.poly, &self.poly.poly) };
        self.reduce();
        self
    }
}

impl Neg for &PolynomialRingZq {
    type Output = PolynomialRingZq;

    /// Documentation at [`PolynomialRingZq::neg`].
    fn neg(self) -> Self::Output {
        let mut out = PolynomialRingZq {
            poly: -&self.poly,
            modulus: self.modulus.clone(),
        };
        out.reduce();
        out
    }
}

#[cfg(test)]
mod test_neg {
    use super::PolynomialRingZq;
    use crate::integer::PolyOverZ;
    use crate::integer_mod_q::ModulusPolynomialRingZq;
    use std::str::FromStr;

    /// Ensure that `neg` works for small coefficients.
    #[test]
    fn correct_small() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let a = PolynomialRingZq::from((&PolyOverZ::from_str("3  1 -2 3").unwrap(), &modulus));
        let b = PolynomialRingZq::from((&PolyOverZ::from_str("3  -1 2 -3").unwrap(), &modulus));
        let c = PolynomialRingZq::from((&PolyOverZ::default(), &modulus));

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
        let a = PolynomialRingZq::from((
            &PolyOverZ::from_str(&format!("3  {} 0 1", i64::MAX)).unwrap(),
            &modulus,
        ));
        let b = PolynomialRingZq::from((
            &PolyOverZ::from_str(&format!("3  -{} 0 -1", i64::MAX)).unwrap(),
            &modulus,
        ));

        assert_eq!(a, -(-&a));
        assert_eq!(b, -&a);
        assert_eq!(b, -a);
    }

    /// Ensure that the result is reduced to the least non-negative residues
    /// and that the modulus is kept.
    #[test]
    fn reduced() {
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
        let a = PolynomialRingZq::from((&PolyOverZ::from_str("3  1 16 8").unwrap(), &modulus));
        let cmp = PolyOverZ::from_str("3  16 1 9").unwrap();

        let neg_a = -&a;

        assert_eq!(cmp, neg_a.get_representative_least_nonnegative_residue());
        assert_eq!(cmp, (-a).get_representative_least_nonnegative_residue());
        assert_eq!(modulus, neg_a.get_mod());
    }
}
