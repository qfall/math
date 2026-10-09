// Copyright 2026 Jan Niklas Siemer
//
// This file is part of qFALL-math
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Neg`] trait for [`MatZq`] values.

use super::super::MatZq;
use crate::traits::MatrixDimensions;
use flint3_sys::fmpz_mod_mat_neg;
use std::ops::Neg;

impl Neg for MatZq {
    type Output = MatZq;

    /// Implements the [`Neg`] trait for [`MatZq`] values.
    /// [`Neg`] is implemented for both borrowed and owned [`MatZq`].
    ///
    /// When called on owned [`MatZq`] it will reuse the memory of `self`.
    ///
    /// Returns the additive inverse of `self` as a [`MatZq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let a: MatZq = MatZq::from_str("[[1, 2],[3, 42]] mod 17").unwrap();
    ///
    /// let b: MatZq = -&a;
    /// let c: MatZq = -a;
    /// ```
    fn neg(mut self) -> Self::Output {
        unsafe {
            fmpz_mod_mat_neg(
                &mut self.matrix,
                &self.matrix,
                self.modulus.get_fmpz_mod_ctx_struct(),
            )
        };
        self
    }
}

impl Neg for &MatZq {
    type Output = MatZq;

    /// Documentation at [`MatZq::neg`].
    fn neg(self) -> Self::Output {
        let mut out = MatZq::new(self.get_num_rows(), self.get_num_columns(), self.get_mod());
        unsafe {
            fmpz_mod_mat_neg(
                &mut out.matrix,
                &self.matrix,
                self.modulus.get_fmpz_mod_ctx_struct(),
            )
        };
        out
    }
}

#[cfg(test)]
mod test_neg {
    use super::MatZq;
    use crate::integer::MatZ;
    use std::str::FromStr;

    /// Ensure that `neg` works for small entries.
    #[test]
    fn correct_small() {
        let a = MatZq::from_str("[[1, -2, 0],[3, 4, -5]] mod 17").unwrap();
        let b = MatZq::from_str("[[-1, 2, 0],[-3, -4, 5]] mod 17").unwrap();
        let c = MatZq::new(2, 3, 17);

        assert_eq!(a, -(-&a));
        assert_eq!(a, -&b);
        assert_eq!(b, -&a);
        assert_eq!(a, -b.clone());
        assert_eq!(b, -a);
        assert_eq!(c, -&c);
        assert_eq!(c.clone(), -c);
    }

    /// Ensure that `neg` works for large entries and moduli.
    #[test]
    fn correct_large() {
        let a = MatZq::from_str(&format!("[[{}, 1],[0, 2]] mod {}", i64::MAX, u64::MAX)).unwrap();
        let b =
            MatZq::from_str(&format!("[[-{}, -1],[0, -2]] mod {}", i64::MAX, u64::MAX)).unwrap();

        assert_eq!(a, -(-&a));
        assert_eq!(b, -&a);
        assert_eq!(b, -a);
    }

    /// Ensure that the result is reduced to the least non-negative residues
    /// and that the modulus is kept.
    #[test]
    fn reduced() {
        let a = MatZq::from_str("[[1, 16, 0],[3, 8, 9]] mod 17").unwrap();
        let cmp = MatZ::from_str("[[16, 1, 0],[14, 9, 8]]").unwrap();

        let neg_a = -&a;

        assert_eq!(cmp, neg_a.get_representative_least_nonnegative_residue());
        assert_eq!(cmp, (-a).get_representative_least_nonnegative_residue());
        assert_eq!(17, neg_a.get_mod());
    }
}
