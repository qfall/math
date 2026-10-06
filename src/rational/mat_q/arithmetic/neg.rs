// Copyright 2026 Jan Niklas Siemer
//
// This file is part of qFALL-math
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Neg`] trait for [`MatQ`] values.

use super::super::MatQ;
use crate::traits::MatrixDimensions;
use flint3_sys::fmpq_mat_neg;
use std::ops::Neg;

impl Neg for MatQ {
    type Output = MatQ;

    /// Implements the [`Neg`] trait for [`MatQ`] values.
    /// [`Neg`] is implemented for both borrowed and owned [`MatQ`].
    ///
    /// When called on owned [`MatQ`] it will reuse the memory of `self`.
    ///
    /// Returns the additive inverse of `self` as a [`MatQ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let a: MatQ = MatQ::from_str("[[1/2, -2],[3, 1/42]]").unwrap();
    ///
    /// let b: MatQ = -&a;
    /// let c: MatQ = -a;
    /// ```
    fn neg(mut self) -> Self::Output {
        unsafe { fmpq_mat_neg(&mut self.matrix, &self.matrix) };
        self
    }
}

impl Neg for &MatQ {
    type Output = MatQ;

    /// Documentation at [`MatQ::neg`].
    fn neg(self) -> Self::Output {
        let mut out = MatQ::new(self.get_num_rows(), self.get_num_columns());
        unsafe { fmpq_mat_neg(&mut out.matrix, &self.matrix) };
        out
    }
}

#[cfg(test)]
mod test_neg {
    use super::MatQ;
    use std::str::FromStr;

    /// Ensure that `neg` works for small entries.
    #[test]
    fn correct_small() {
        let a = MatQ::from_str("[[1/2, -2, 0],[3, 4/7, -5]]").unwrap();
        let b = MatQ::from_str("[[-1/2, 2, 0],[-3, -4/7, 5]]").unwrap();
        let c = MatQ::new(2, 3);

        assert_eq!(a, -(-&a));
        assert_eq!(a, -&b);
        assert_eq!(b, -&a);
        assert_eq!(a, -b.clone());
        assert_eq!(b, -a);
        assert_eq!(c, -&c);
        assert_eq!(c.clone(), -c);
    }

    /// Ensure that `neg` works for large entries.
    #[test]
    fn correct_large() {
        let a = MatQ::from_str(&format!("[[{}, 1/{}],[1, 2]]", u64::MAX, i64::MAX)).unwrap();
        let b = MatQ::from_str(&format!("[[-{}, -1/{}],[-1, -2]]", u64::MAX, i64::MAX)).unwrap();

        assert_eq!(a, -(-&a));
        assert_eq!(b, -&a);
        assert_eq!(b, -a);
    }
}
