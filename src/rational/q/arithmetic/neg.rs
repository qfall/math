// Copyright 2026 Joshua Limbrey
//
// This file is part of qFALL-math
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Neg`] trait for [`Q`] values.

use super::super::Q;
use flint3_sys::fmpq_neg;
use std::ops::Neg;

impl Neg for Q {
    type Output = Q;

    /// Implements the [`Neg`] trait for [`Q`] values.
    /// [`Neg`] is implements for both borrowed and owned [`Q`].
    ///
    /// When called on owned [`Q`] it will reuse the memory of `self`.
    ///
    /// Returns the additive inverse of `self` as a [`Q`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    ///
    /// let a: Q = Q::from((1, 42));
    ///
    /// let b: Q = -&a;
    /// let c: Q = -a;
    /// ```
    fn neg(mut self) -> Self::Output {
        unsafe { fmpq_neg(&mut self.value, &self.value) };
        self
    }
}

impl Neg for &Q {
    type Output = Q;

    /// Documentation at [`Q::neg`].
    fn neg(self) -> Self::Output {
        let mut out = Q::default();
        unsafe { fmpq_neg(&mut out.value, &self.value) };
        out
    }
}

#[cfg(test)]
mod test_neg {
    use super::Q;

    /// Ensure that `neg` works for small numbers.
    #[test]
    fn correct_small() {
        let a: Q = Q::ONE;
        let b: Q = Q::MINUS_ONE;
        let c: Q = Q::ZERO;

        let d: Q = Q::from((1, 42));

        assert_eq!(a, -(-&a));
        assert_eq!(a, -&b);
        assert_eq!(b, -&a);
        assert_eq!(a, -b.clone());
        assert_eq!(b, -a);
        assert_eq!(c, -&c);
        assert_eq!(c.clone(), -c);
        assert_eq!(d, -(-&d));
        assert_eq!(d.clone(), -(-d));
    }

    /// Ensure that `neg` works for large numbers.
    #[test]
    fn correct_large() {
        let a: Q = Q::from(u64::MAX);
        let b: Q = Q::from(i64::MAX);

        assert_eq!(a, -(-&a));
        assert_eq!(b, -(-&b));
    }
}
