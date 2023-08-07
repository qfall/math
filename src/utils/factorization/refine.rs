// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations for Factorizations of [`Z`](crate::integer::Z) values.

use super::Factorization;
use flint_sys::fmpz_factor::fmpz_factor_refine;

impl Factorization {
    /// Allows to refine a partial factorization of type [`Factorization`] to a more
    /// complete one whose bases are pairwise relatively prime.
    /// The bases of the factors are then in ascending order.
    ///
    /// For factorization `[(2, 2), (40, 1), (9, 2)]` the refinement looks like this
    /// `[(2, 5), (5, 1), (9, 2)]`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::utils::Factorization;
    /// use core::fmt;
    ///
    /// let mut fac = Factorization::from((1200, 20));
    /// fac.refine();
    ///
    /// println!("{}", fac);
    /// ```
    pub fn refine(&mut self) {
        unsafe { fmpz_factor_refine(&mut self.factors, &self.factors) }
    }
}

#[cfg(test)]
mod test_refine {
    use super::Factorization;

    /// Ensure that refinement works correctly.
    #[test]
    fn refine_correct() {
        let mut fac = Factorization::from((3, 6));

        fac.refine();

        assert_eq!("[(2, 1), (3, 2)]", fac.to_string());
    }

    /// Ensure that refinement works correctly.
    #[test]
    fn refine_correct_big() {
        let mut fac = Factorization::from((i64::MAX - 1, 2));

        fac.refine();

        assert_eq!(
            format!("[(2, 2), ({}, 1)]", (i64::MAX - 1) / 2),
            fac.to_string()
        );
    }

    /// Ensure that refinement works correctly with negative numbers.
    #[test]
    fn refine_correct_negative() {
        let mut fac = Factorization::from((-1200, 20));

        fac.refine();

        assert_eq!("[(-1, 1), (3, 1), (20, 3)]", fac.to_string());
    }

    /// Ensure that refinement orders the values correctly.
    #[test]
    fn refine_correct_order() {
        let mut fac1 = Factorization::from((8, 3));
        let mut fac2 = Factorization::from((i64::MAX - 1, 2));

        fac1.refine();
        fac2.refine();

        assert_eq!("[(3, 1), (8, 1)]", fac1.to_string());
        assert_eq!(
            format!("[(2, 2), ({}, 1)]", (i64::MAX - 1) / 2),
            fac2.to_string()
        );
    }

    /// Ensure that refinement works for value 1.
    #[test]
    fn refine_correct_one() {
        let mut fac = Factorization::from(1);

        fac.refine();

        assert_eq!("[(1, 1)]", fac.to_string());
    }

    /// Ensure that refinement works for value -1.
    #[test]
    fn refine_correct_minus_one() {
        let mut fac = Factorization::from(-1);

        fac.refine();

        assert_eq!("[(-1, 1)]", fac.to_string());
    }

    /// Ensure that refinement works for value 0.
    #[test]
    fn refine_correct_zero() {
        let mut fac = Factorization::from(0);

        fac.refine();

        assert_eq!("[]", fac.to_string());
    }
}
