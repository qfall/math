// Copyright 2026 Joshua Limbrey
//
// This file is part of qFALL-math
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Neg`] trait for [`Z`] values.

use super::super::Z;
use flint3_sys::fmpz_neg;
use std::ops::Neg;

impl Neg for Z {
    type Output = Z;

    /// Implements the [`Neg`] trait for [`Z`] values.
    /// [`Neg`] is implemented for both borrowed and owned [`Z`].
    ///
    /// When called on owned [`Z`] it will reuse the memory of `self`.
    ///
    /// Returns the additive inverse of `self` as a [`Z`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let a: Z = Z::from(42);
    ///
    /// let b: Z = -&a;
    /// let c: Z = -a;
    /// ```
    fn neg(mut self) -> Self::Output {
        unsafe { fmpz_neg(&mut self.value, &self.value) };
        self
    }
}

impl Neg for &Z {
    type Output = Z;

    /// Documentation at [`Z::neg`].
    fn neg(self) -> Self::Output {
        let mut out = Z::default();
        unsafe { fmpz_neg(&mut out.value, &self.value) };
        out
    }
}

#[cfg(test)]
mod test_neg {
    use super::Z;

    /// Ensure that `neg` works for small numbers.
    #[test]
    fn correct_small() {
        let a: Z = Z::ONE;
        let b: Z = Z::MINUS_ONE;
        let c: Z = Z::ZERO;

        assert_eq!(a, -(-&a));
        assert_eq!(a, -&b);
        assert_eq!(b, -&a);
        assert_eq!(a, -b.clone());
        assert_eq!(b, -a);
        assert_eq!(c, -&c);
        assert_eq!(c.clone(), -c);
    }

    /// Ensure that `neg` works for large numbers.
    #[test]
    fn correct_large() {
        let a: Z = Z::from(u64::MAX);
        let b: Z = Z::from(i64::MAX);

        assert_eq!(a, -(-&a));
        assert_eq!(b, -(-&b));
    }
}
