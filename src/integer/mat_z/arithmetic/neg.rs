// Copyright 2026 Jan Niklas Siemer
//
// This file is part of qFALL-math
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Neg`] trait for [`MatZ`] values.

use super::super::MatZ;
use crate::traits::MatrixDimensions;
use flint3_sys::fmpz_mat_neg;
use std::ops::Neg;

impl Neg for MatZ {
    type Output = MatZ;

    /// Implements the [`Neg`] trait for [`MatZ`] values.
    /// [`Neg`] is implemented for both borrowed and owned [`MatZ`].
    ///
    /// When called on owned [`MatZ`] it will reuse the memory of `self`.
    ///
    /// Returns the additive inverse of `self` as a [`MatZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let a: MatZ = MatZ::from_str("[[1, -2],[3, 42]]").unwrap();
    ///
    /// let b: MatZ = -&a;
    /// let c: MatZ = -a;
    /// ```
    fn neg(mut self) -> Self::Output {
        unsafe { fmpz_mat_neg(&mut self.matrix, &self.matrix) };
        self
    }
}

impl Neg for &MatZ {
    type Output = MatZ;

    /// Documentation at [`MatZ::neg`].
    fn neg(self) -> Self::Output {
        let mut out = MatZ::new(self.get_num_rows(), self.get_num_columns());
        unsafe { fmpz_mat_neg(&mut out.matrix, &self.matrix) };
        out
    }
}

#[cfg(test)]
mod test_neg {
    use super::MatZ;
    use std::str::FromStr;

    /// Ensure that `neg` works for small entries.
    #[test]
    fn correct_small() {
        let a = MatZ::from_str("[[1, -2, 0],[3, 4, -5]]").unwrap();
        let b = MatZ::from_str("[[-1, 2, 0],[-3, -4, 5]]").unwrap();
        let c = MatZ::new(2, 3);

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
        let a = MatZ::from_str(&format!("[[{}, {}],[1, 2]]", u64::MAX, i64::MIN)).unwrap();
        let b = MatZ::from_str(&format!(
            "[[-{}, {}],[-1, -2]]",
            u64::MAX,
            i64::MAX as u64 + 1
        ))
        .unwrap();

        assert_eq!(a, -(-&a));
        assert_eq!(b, -&a);
        assert_eq!(b, -a);
    }
}
