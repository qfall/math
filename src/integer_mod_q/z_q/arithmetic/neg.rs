// Copyright 2026 Jan Niklas Siemer
//
// This file is part of qFALL-math
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Neg`] trait for [`Zq`] values.

use super::super::Zq;
use crate::integer::Z;
use flint3_sys::fmpz_mod_neg;
use std::ops::Neg;

impl Neg for Zq {
    type Output = Zq;

    /// Implements the [`Neg`] trait for [`Zq`] values.
    /// [`Neg`] is implemented for both borrowed and owned [`Zq`].
    ///
    /// When called on owned [`Zq`] it will reuse the memory of `self`.
    ///
    /// Returns the additive inverse of `self` as a [`Zq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    ///
    /// let a: Zq = Zq::from((42, 17));
    ///
    /// let b: Zq = -&a;
    /// let c: Zq = -a;
    /// ```
    fn neg(mut self) -> Self::Output {
        unsafe {
            fmpz_mod_neg(
                &mut self.value.value,
                &self.value.value,
                self.modulus.get_fmpz_mod_ctx_struct(),
            )
        };
        self
    }
}

impl Neg for &Zq {
    type Output = Zq;

    /// Documentation at [`Zq::neg`].
    fn neg(self) -> Self::Output {
        let mut out = Z::ZERO;
        unsafe {
            fmpz_mod_neg(
                &mut out.value,
                &self.value.value,
                self.modulus.get_fmpz_mod_ctx_struct(),
            )
        };
        Zq {
            value: out,
            modulus: self.modulus.clone(),
        }
    }
}

#[cfg(test)]
mod test_neg {
    use super::Zq;
    use crate::integer::Z;

    /// Ensure that `neg` works for small values.
    #[test]
    fn correct_small() {
        let a = Zq::from((1, 17));
        let b = Zq::from((-1, 17));
        let c = Zq::from((0, 17));

        assert_eq!(a, -(-&a));
        assert_eq!(a, -&b);
        assert_eq!(b, -&a);
        assert_eq!(a, -b.clone());
        assert_eq!(b, -a);
        assert_eq!(c, -&c);
        assert_eq!(c.clone(), -c);
    }

    /// Ensure that `neg` works for large values and moduli.
    #[test]
    fn correct_large() {
        let a = Zq::from((i64::MAX, u64::MAX));
        let b = Zq::from((u64::MAX - i64::MAX as u64, u64::MAX));

        assert_eq!(a, -(-&a));
        assert_eq!(b, -&a);
        assert_eq!(b, -a);
    }

    /// Ensure that the result is reduced to the least non-negative residue
    /// and that the modulus is kept.
    #[test]
    fn reduced() {
        let a = Zq::from((3, 17));
        let c = Zq::from((0, 17));

        let neg_a = -&a;
        let neg_c = -c;

        assert_eq!(
            Z::from(14),
            neg_a.get_representative_least_nonnegative_residue()
        );
        assert_eq!(
            Z::from(14),
            (-a).get_representative_least_nonnegative_residue()
        );
        assert_eq!(
            Z::ZERO,
            neg_c.get_representative_least_nonnegative_residue()
        );
        assert_eq!(Z::from(17), neg_a.get_mod());
    }
}
