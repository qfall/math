// Copyright 2026 Jan Niklas Siemer
//
// This file is part of qFALL-math
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Neg`] trait for [`PolyOverZ`] values.

use super::super::PolyOverZ;
use flint3_sys::fmpz_poly_neg;
use std::ops::Neg;

impl Neg for PolyOverZ {
    type Output = PolyOverZ;

    /// Implements the [`Neg`] trait for [`PolyOverZ`] values.
    /// [`Neg`] is implemented for both borrowed and owned [`PolyOverZ`].
    ///
    /// When called on owned [`PolyOverZ`] it will reuse the memory of `self`.
    ///
    /// Returns the additive inverse of `self` as a [`PolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverZ = PolyOverZ::from_str("3  1 -2 42").unwrap();
    ///
    /// let b: PolyOverZ = -&a;
    /// let c: PolyOverZ = -a;
    /// ```
    fn neg(mut self) -> Self::Output {
        unsafe { fmpz_poly_neg(&mut self.poly, &self.poly) };
        self
    }
}

impl Neg for &PolyOverZ {
    type Output = PolyOverZ;

    /// Documentation at [`PolyOverZ::neg`].
    fn neg(self) -> Self::Output {
        let mut out = PolyOverZ::default();
        unsafe { fmpz_poly_neg(&mut out.poly, &self.poly) };
        out
    }
}

#[cfg(test)]
mod test_neg {
    use super::PolyOverZ;
    use std::str::FromStr;

    /// Ensure that `neg` works for small coefficients.
    #[test]
    fn correct_small() {
        let a = PolyOverZ::from_str("4  1 -2 0 3").unwrap();
        let b = PolyOverZ::from_str("4  -1 2 0 -3").unwrap();
        let c = PolyOverZ::default();

        assert_eq!(a, -(-&a));
        assert_eq!(a, -&b);
        assert_eq!(b, -&a);
        assert_eq!(a, -b.clone());
        assert_eq!(b, -a);
        assert_eq!(c, -&c);
        assert_eq!(c.clone(), -c);
    }

    /// Ensure that `neg` works for large coefficients.
    #[test]
    fn correct_large() {
        let a = PolyOverZ::from_str(&format!("3  {} 0 {}", u64::MAX, i64::MIN)).unwrap();
        let b =
            PolyOverZ::from_str(&format!("3  -{} 0 {}", u64::MAX, i64::MAX as u64 + 1)).unwrap();

        assert_eq!(a, -(-&a));
        assert_eq!(b, -&a);
        assert_eq!(b, -a);
    }
}
