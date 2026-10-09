// Copyright 2026 Jan Niklas Siemer
//
// This file is part of qFALL-math
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Neg`] trait for [`PolyOverQ`] values.

use super::super::PolyOverQ;
use flint3_sys::fmpq_poly_neg;
use std::ops::Neg;

impl Neg for PolyOverQ {
    type Output = PolyOverQ;

    /// Implements the [`Neg`] trait for [`PolyOverQ`] values.
    /// [`Neg`] is implemented for both borrowed and owned [`PolyOverQ`].
    ///
    /// When called on owned [`PolyOverQ`] it will reuse the memory of `self`.
    ///
    /// Returns the additive inverse of `self` as a [`PolyOverQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::PolyOverQ;
    /// use std::str::FromStr;
    ///
    /// let a: PolyOverQ = PolyOverQ::from_str("3  1/2 -2 42").unwrap();
    ///
    /// let b: PolyOverQ = -&a;
    /// let c: PolyOverQ = -a;
    /// ```
    fn neg(mut self) -> Self::Output {
        unsafe { fmpq_poly_neg(&mut self.poly, &self.poly) };
        self
    }
}

impl Neg for &PolyOverQ {
    type Output = PolyOverQ;

    /// Documentation at [`PolyOverQ::neg`].
    fn neg(self) -> Self::Output {
        let mut out = PolyOverQ::default();
        unsafe { fmpq_poly_neg(&mut out.poly, &self.poly) };
        out
    }
}

#[cfg(test)]
mod test_neg {
    use super::PolyOverQ;
    use std::str::FromStr;

    /// Ensure that `neg` works for small coefficients.
    #[test]
    fn correct_small() {
        let a = PolyOverQ::from_str("4  1/2 -2 0 3/7").unwrap();
        let b = PolyOverQ::from_str("4  -1/2 2 0 -3/7").unwrap();
        let c = PolyOverQ::default();

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
        let a = PolyOverQ::from_str(&format!("3  {} 0 1/{}", u64::MAX, i64::MAX)).unwrap();
        let b = PolyOverQ::from_str(&format!("3  -{} 0 -1/{}", u64::MAX, i64::MAX)).unwrap();

        assert_eq!(a, -(-&a));
        assert_eq!(b, -&a);
        assert_eq!(b, -a);
    }
}
