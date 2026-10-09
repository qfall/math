// Copyright 2026 Jan Niklas Siemer
//
// This file is part of qFALL-math
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Neg`] trait for [`MatPolyOverZ`] values.

use super::super::MatPolyOverZ;
use crate::traits::MatrixDimensions;
use flint3_sys::fmpz_poly_mat_neg;
use std::ops::Neg;

impl Neg for MatPolyOverZ {
    type Output = MatPolyOverZ;

    /// Implements the [`Neg`] trait for [`MatPolyOverZ`] values.
    /// [`Neg`] is implemented for both borrowed and owned [`MatPolyOverZ`].
    ///
    /// When called on owned [`MatPolyOverZ`] it will reuse the memory of `self`.
    ///
    /// Returns the additive inverse of `self` as a [`MatPolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a: MatPolyOverZ = MatPolyOverZ::from_str("[[2  1 -2, 0],[1  42, 3  1 2 3]]").unwrap();
    ///
    /// let b: MatPolyOverZ = -&a;
    /// let c: MatPolyOverZ = -a;
    /// ```
    fn neg(mut self) -> Self::Output {
        unsafe { fmpz_poly_mat_neg(&mut self.matrix, &self.matrix) };
        self
    }
}

impl Neg for &MatPolyOverZ {
    type Output = MatPolyOverZ;

    /// Documentation at [`MatPolyOverZ::neg`].
    fn neg(self) -> Self::Output {
        let mut out = MatPolyOverZ::new(self.get_num_rows(), self.get_num_columns());
        unsafe { fmpz_poly_mat_neg(&mut out.matrix, &self.matrix) };
        out
    }
}

#[cfg(test)]
mod test_neg {
    use super::MatPolyOverZ;
    use std::str::FromStr;

    /// Ensure that `neg` works for small coefficients.
    #[test]
    fn correct_small() {
        let a = MatPolyOverZ::from_str("[[2  1 -2, 0, 1  5],[1  -3, 3  1 0 4, 0]]").unwrap();
        let b = MatPolyOverZ::from_str("[[2  -1 2, 0, 1  -5],[1  3, 3  -1 0 -4, 0]]").unwrap();
        let c = MatPolyOverZ::new(2, 3);

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
        let a =
            MatPolyOverZ::from_str(&format!("[[2  {} {}],[1  1]]", u64::MAX, i64::MIN)).unwrap();
        let b = MatPolyOverZ::from_str(&format!(
            "[[2  -{} {}],[1  -1]]",
            u64::MAX,
            i64::MAX as u64 + 1
        ))
        .unwrap();

        assert_eq!(a, -(-&a));
        assert_eq!(b, -&a);
        assert_eq!(b, -a);
    }
}
